def divides (n m : Nat) : Prop :=
  ∃ k : Nat, m = k * n

notation n " ∣ " m => divides n m
notation n " ∤ " m => ¬ (n ∣ m)

abbrev Reg (n : Nat) :=
  2 ≤ n 

abbrev pos_of_nz : x ≠ 0 → 0 < x :=
  Nat.zero_lt_of_ne_zero

abbrev nz_of_pos : 0 < x → x ≠ 0 :=
  Nat.not_eq_zero_of_lt

def Prime (k : Nat) :=
  Reg k ∧ ∀ n m : Nat, (k ∣ n * m) → (k ∣ n) ∨ (k ∣ m)

def NatPrime (k : Nat) :=
  Reg k ∧ ∀ m, 2 ≤ m ∧ m < k → (m ∤ k)

theorem double_neg_elim [Decidable p] : (¬ (¬ p)) → p :=
  if hp : p then fun _ => hp else (. hp |>.elim)

theorem or_of_left (or_pred: p ∨ q) (proof : p → q) : q :=
  Or.elim or_pred proof id

theorem or_of_right (or_pred: q ∨ p) (proof : p → q) : q :=
  Or.elim or_pred id proof

notation orp " >l " pr => or_of_left orp pr
notation orp " >r " pr => or_of_right orp pr

theorem eq_of_le_of_not_lt {a b : Nat}
    (a_le_b : a ≤ b) (not_a_lt_b : ¬ a < b) : a = b :=
  Nat.le_antisymm a_le_b (Nat.ge_of_not_lt not_a_lt_b)

def minSatRec
    [DecidablePred p] (r : Nat) (r_le_n : r ≤ n)
    (sat : p n) (sofar : ∀ k, k < r → ¬ p k) :
    ∃ m, p m ∧ ∀ k, k < m → ¬ p k :=
  if succ_r_le_n : r + 1 ≤ n then 
    if stop : p r then
      ⟨r, stop, sofar⟩
    else
      have rec_arg : (k : Nat) → k < (r + 1) → ¬ p k :=
        fun k k_lt_succ =>
        if already : k < r then
          sofar k already
        else
          have : k = r :=
            eq_of_le_of_not_lt (Nat.le_of_lt_succ k_lt_succ) already
          this ▸ stop
      minSatRec (r + 1) succ_r_le_n sat rec_arg
  else
    have : r = n :=
      eq_of_le_of_not_lt r_le_n succ_r_le_n
    ⟨n, sat, this ▸ sofar⟩
termination_by _ => n - r

theorem minimal_satisfies {n : Nat} [DecidablePred p] (sat : p n) :
    ∃ m, p m ∧ (∀ k, k < m → ¬ p k) := 
  minSatRec 0 (Nat.zero_le n) sat (Nat.not_lt_zero . . |>.elim)  

theorem pos_of_reg : Reg n → n > 0 :=
  (Nat.lt_trans (Nat.zero_lt_of_ne_zero Nat.one_ne_zero) .)

theorem nz_of_reg : Reg n → n ≠ 0 :=
  (Nat.not_eq_zero_of_lt .)

theorem pred_ge_one_of_reg (reg_d : Reg d) : 1 ≤ d - 1 :=
  Nat.pred_le_pred reg_d

theorem reg_monotone (reg_k : Reg k) (mono : k ≤ l) : Reg l :=
  Nat.le_trans reg_k mono

theorem pred_lt_of_reg (reg_d : Reg d) : d - 1 < d :=
  pos_of_reg reg_d |> Nat.not_eq_zero_of_lt |> Nat.pred_lt

theorem reg_pred_of_reg_ne_two (reg_d : Reg d) (ne : d ≠ 2) :
    Reg (d - 1) :=
  Nat.pred_le_pred <| Nat.lt_of_le_of_ne reg_d ne.symm

theorem reg_of_mul_regs (rx: Reg x) (ry :Reg y) : Reg (x * y) :=
  calc 2 ≤ 4     := by decide 
       _ ≤ x * y := Nat.mul_le_mul rx ry

theorem zero_one_of_not_reg (nreg_d : ¬ Reg d) : d = 0 ∨ d = 1 :=
  have : d < 2 := Nat.gt_of_not_le nreg_d
  match d with
  | 0 => .inl rfl
  | 1 => .inr rfl

def reg_by_match (k : Nat) :=
  Nat.add_comm 2 k ▸ Nat.le_add_right 2 k

def RegularRange (r n: Nat) :=
  2 ≤ r ∧ r < n

infix:50 " ⋖ " => RegularRange

theorem eq_of_sandwich {a x : Nat} (ax: a ≤ x) (xa : x ≤ a) : a = x :=
  calc a = (a - x) + x := Nat.sub_add_cancel xa |>.symm
       _ = x           := by rw [Nat.sub_eq_zero_of_le ax, Nat.zero_add]

theorem mod_cancel_prod (n d q : Nat) : (q * d + n) % d = n % d :=
  match q with
  | 0     => by rw [Nat.zero_mul, Nat.zero_add]
  | q + 1 => by
    rw [Nat.right_distrib, Nat.one_mul,
        Nat.add_assoc, Nat.add_comm d n, ← Nat.add_assoc]
    have : q * d + n + d ≥ d := Nat.le_add_left d _
    rw [Nat.mod_eq_sub_mod this, Nat.add_sub_assoc,
        Nat.sub_self, Nat.add_zero]
    exact mod_cancel_prod n d q
    exact Nat.le_refl d

theorem euclidean_data (d_pos : 0 < d) (n_pos : 0 < n) :
    (r < d ∧ n = q * d + r) ↔ (r = n % d ∧ q = n / d) :=
  have div_mod := Nat.div_add_mod n d
  ⟨ fun ⟨r_lt_d, ediv⟩ => 
      have rem_id : r = n % d := calc
        r = r % d           := Nat.mod_eq_of_lt r_lt_d |>.symm
        _ = (q * d + r) % d := mod_cancel_prod r d q   |>.symm
        _ = n % d           := ediv ▸ rfl
      ⟨ rem_id,
        have : d * (n / d) + r = n := rem_id.symm ▸ div_mod
        have : d * (n / d) = d * q := calc
          d * (n / d) = d * (n / d) + r - r := by rw [Nat.add_sub_cancel]
          _           = n - r               := by rw [this]
          _           = d * q               := by rw [ediv, Nat.add_sub_cancel,
                                                      Nat.mul_comm]
        Nat.eq_of_mul_eq_mul_left d_pos this.symm ⟩,
    fun ⟨r_eq_mod, q_eq_div⟩ =>
      ⟨ r_eq_mod ▸ Nat.mod_lt n d_pos,
        have := r_eq_mod.symm ▸ q_eq_div.symm ▸ div_mod
        by rw [Nat.mul_comm, this]⟩⟩

theorem euclidean_division (d_pos : 0 < d) (n_pos : 0 < n) :
    ∃ q r, r < d ∧ n = q*d + r :=
  ⟨n / d, n % d, by
    rw [euclidean_data d_pos n_pos]; apply And.intro <;> rfl⟩

theorem le_or_zero_of_dvd (k K : Nat) :
    (k ∣ K) → K = 0 ∨ k ≤ K :=
  fun ⟨m, kdiv⟩ =>
    if mz : m = 0 then
      .inl <| by rw [kdiv, mz, Nat.zero_mul]
    else
      .inr <| calc
        K = m * k := kdiv
        _ ≥ 1 * k := Nat.mul_le_mul_right k <| pos_of_nz mz
        _ = k     := by rw [Nat.mul_comm, Nat.mul_one]

theorem not_lt_of_dvd_pos (k_pos : 0 < K) :
    (k ∣ K) → ¬ K < k :=
  fun divs contra => le_or_zero_of_dvd k K divs |>.elim
    (fun kzr => Nat.ne_of_lt k_pos kzr.symm)
    (fun kle => Nat.not_le_of_gt contra kle)

theorem le_of_dvd_pos (k_pos : 0 < K) (dk : k ∣ K) : k ≤ K :=
  le_or_zero_of_dvd k K dk >l
    (. |> nz_of_pos k_pos |>.elim)

theorem one_of_dvd_one : (a ∣ 1) → a = 1 :=
  fun ⟨k, ka_eq_one⟩ =>
    have a_pos : a ≥ 1 :=
      Nat.eq_zero_or_pos _ >l
        fun _ => by simp only [*, Nat.mul_zero]
    have k_pos : k ≥ 1 :=
      Nat.eq_zero_or_pos _ >l
        fun _ => by simp only [*, Nat.zero_mul]
    have : a ≤ 1 := calc
      a = 1 * a := Nat.one_mul a |>.symm
      _ ≤ k * a := Nat.mul_le_mul_right a k_pos
      _ = 1     := ka_eq_one.symm
    Nat.le_antisymm this a_pos

theorem dvd_zero (a : Nat) : a ∣ 0 :=
  ⟨0, Nat.zero_mul a |>.symm⟩

theorem zero_of_dvd_by_zero : ∀ (a : Nat), (0 ∣ a) → a = 0 :=
  fun _ ⟨k, h⟩ => (Nat.mul_zero k) ▸ h

theorem dvd_transAux : (a ∣ b) ∧ (b ∣ c) → (a ∣ c) :=
  fun ⟨⟨m, adb⟩, ⟨n, bdc⟩⟩ =>
    ⟨n * m, by rw [bdc, adb, Nat.mul_assoc]⟩

theorem dvd_trans (h₁ : a ∣ b) (h₂ : b ∣ c) : (a ∣ c) :=
  dvd_transAux ⟨h₁, h₂⟩

instance : Trans divides divides divides where
  trans := dvd_trans

theorem dvd_diff_of_both : (a ∣ b) ∧ (a ∣ c) → (a ∣ b - c) :=
  fun ⟨⟨m, adb⟩, ⟨n, bdc⟩⟩ =>
    ⟨m - n, by rw [adb, bdc, Nat.mul_sub_right_distrib]⟩

theorem dvd_monotone (r : Nat) (div : p ∣ q) : p ∣ q * r :=
  have : q ∣ q * r := ⟨r, by rw [Nat.mul_comm]⟩
  dvd_trans div this

theorem dvd_of_eq : a = r → a ∣ r :=
  fun _ => ⟨1, by simp only [*, Nat.one_mul]⟩

theorem dvd_self : n ∣ n := ⟨1, by rw [Nat.one_mul]⟩

theorem dvd_antisymm : (a ∣ b) ∧ (b ∣ a) → a = b :=
  fun ⟨ab, ba⟩ =>
    le_or_zero_of_dvd a b ab |>.elim
      (fun bz => by rw [bz, zero_of_dvd_by_zero a (bz ▸ ba)])
      (fun bl => le_or_zero_of_dvd b a ba |>.elim
        fun az => by rw [zero_of_dvd_by_zero b (az ▸ ab), az]
        fun al => Nat.le_antisymm bl al)

theorem zmod_of_dvd (n m : Nat): (n ∣ m) → m % n = 0 :=
  if m_zero : m = 0 then
    fun _ => by rw [m_zero, Nat.zero_mod]
  else if n_zero : n = 0 then
    (n_zero ▸ . |> zero_of_dvd_by_zero m |> m_zero |>.elim)
  else if big_n : m < n then
    (le_or_zero_of_dvd n m . |>.elim
      (m_zero . |>.elim)
      (Nat.not_le_of_gt big_n . |>.elim))
  else if eq_n : n = m then
    fun _ => eq_n ▸ Nat.mod_self n
  else
    have small_n : n ≤ m := Nat.ge_of_not_lt big_n
    fun n_div_m =>
      have := zmod_of_dvd n (m - n) <|
              dvd_diff_of_both ⟨n_div_m, dvd_self⟩
      this ▸ Nat.mod_eq_sub_mod small_n
decreasing_by
  simp_wf; exact Nat.sub_lt
    (Nat.zero_lt_of_ne_zero m_zero)
    (Nat.zero_lt_of_ne_zero n_zero)

theorem dvd_of_zmod (n m : Nat) : m % n = 0 → (n ∣ m) :=
  fun mod_z =>
  have : n * (m / n) = m :=
    Nat.add_zero (n * (m / n)) ▸ mod_z ▸ Nat.div_add_mod m n
  ⟨m / n, by rw [Nat.mul_comm, this]⟩

theorem div_self_eq_one (nz : a ≠ 0) : a / a = 1 :=
  have : a * (a / a) = a :=
    Nat.add_zero (a * (a / a)) ▸ Nat.mod_self a ▸ Nat.div_add_mod a a
  have : a * (a / a) = a * 1 := by rw [Nat.mul_one, this]
  Nat.eq_of_mul_eq_mul_left (pos_of_nz nz) this

theorem expand_product {n m : Nat} (nx : n = a*x + p) (mx : m = a*y + q) :
  n * m = a*(x*a*y + x*q + p*y) + p*q := by
    rw [nx, mx]
    simp only [Nat.add_assoc, Nat.left_distrib,
               Nat.right_distrib, Nat.mul_assoc]
    simp only [← Nat.add_assoc]
    have : p * (a * y) = a * (p * y) := calc
      p * (a * y) = (p * a) * y := by rw [Nat.mul_assoc]
      _           = (a * p) * y := by rw [Nat.mul_comm a p]
      _           = a * (p * y) := by rw [Nat.mul_assoc]
    rw [this]
    simp only [Nat.add_comm, Nat.add_assoc]

def decDiv (n m : Nat) : Decidable (divides n m) :=
  if mod_zero : m % n = 0 then
    isTrue  <| dvd_of_zmod n m mod_zero
  else
    isFalse <| (zmod_of_dvd n m . |> mod_zero)

instance : Decidable (divides n m) :=
  decDiv n m

theorem mod_idemp (d_pos : 0 < d) :
    (n % d) % d = n % d :=
  Nat.mod_eq_of_lt <| Nat.mod_lt n d_pos

theorem prod_mod_eq_mod_prod_mod (d_pos : 0 < d) :
    (n * m) % d = (n % d)*(m % d) % d :=
  if nz : n = 0 then
    by rw [nz, Nat.zero_mul, Nat.zero_mod, Nat.zero_mul, Nat.zero_mod]
  else if mz : m = 0 then
    by rw [mz, Nat.mul_zero, Nat.zero_mod, Nat.mul_zero, Nat.zero_mod]
  else
    have np := pos_of_nz nz
    have mp := pos_of_nz mz
    have ⟨qn, rn, n_div⟩ := euclidean_division d_pos np
    have ⟨qm, rm, m_div⟩ := euclidean_division d_pos mp
    have div_n : n = d * qn + rn := by rw [Nat.mul_comm, n_div.2]
    have div_m : m = d * qm + rm := by rw [Nat.mul_comm, m_div.2]
    have mod_m_r := euclidean_data d_pos mp |>.mp m_div |>.left
    have mod_n_r := euclidean_data d_pos np |>.mp n_div |>.left
    have exp := expand_product div_n div_m
    let f := qn * d * qm + qn * rm + rn * qm
    calc
      (n * m) % d = (f * d + rn * rm) % d := by rw [exp, Nat.mul_comm]
      _           = rn * rm % d           := by rw [mod_cancel_prod]
      _           = (n % d) * (m % d) % d := by rw [mod_m_r, mod_n_r]

theorem not_dvd_prod_of_prime :
    Prime n → ∀ p q, 1 ≤ p ∧ p < n ∧ 1 ≤ q ∧ q < n → (n ∤ (p * q)) :=
  fun ⟨_, div⟩ p q ⟨pos_p, p_lt_n, pos_q, q_lt_n⟩ =>
    let contra_divs :=
      fun x dx pos_x x_lt_n => 
      le_or_zero_of_dvd n x dx |>.elim
        (Nat.not_eq_zero_of_lt pos_x .)
        (Nat.not_le_of_gt x_lt_n . |>.elim)
    (div p q . |>.elim
      (contra_divs p . pos_p p_lt_n)
      (contra_divs q . pos_q q_lt_n))

theorem prime_of_not_dvd_prod : Reg n →
    (∀ p q, 1 ≤ p ∧ p < n ∧ 1 ≤ q ∧ q < n → (n ∤ (p * q))) →
    Prime n :=
  fun reg_n not_dvd_prod =>
  ⟨reg_n,
    fun k l n_div_kl =>
    let p := k % n
    let q := l % n
    have n_pos  : 0 < n := pos_of_reg reg_n
    have p_lt_n : p < n := Nat.mod_lt k n_pos
    have q_lt_n : q < n := Nat.mod_lt l n_pos
    have n_div_pq : n ∣ (p * q) :=
      dvd_of_zmod n (p * q) <| Eq.symm <| calc
        0 = k * l % n           := zmod_of_dvd n (k * l) n_div_kl |>.symm
        _ = (k % n)*(l % n) % n := prod_mod_eq_mod_prod_mod n_pos
    if pos_p : 1 ≤ p then
      if pos_q : 1 ≤ q then
         not_dvd_prod p q ⟨pos_p, p_lt_n, pos_q, q_lt_n⟩ n_div_pq |>.elim
      else
        .inr <| dvd_of_zmod n l <| Nat.eq_zero_or_pos q >r (pos_q . |>.elim)
    else
      .inl <| dvd_of_zmod n k <| Nat.eq_zero_or_pos p >r (pos_p . |>.elim)⟩

theorem reduced_primality : Prime n →
    Reg n ∧ ∀ p q, p < n ∧ q < n → (n ∣ (p * q)) → (n ∣ p) ∨ (n ∣ q) :=
  fun ⟨reg_n, div⟩ => ⟨reg_n, fun p q _ => div p q⟩

def factors_of_dvd (dn : d ∣ n) : n = d * (n / d) :=
  calc n = d * (n / d) + n % d := Nat.div_add_mod n d |>.symm
       _ = d * (n / d)         := by rw [zmod_of_dvd d n dn, Nat.add_zero]

theorem descend_factors
    (d_pos : 0 < d) (div_p : d ∣ p) (div_c : d ∣ c)
    (factor : p * q = c * n) : (p / d) * q = (c / d) * n := by
  rw [factors_of_dvd div_p, factors_of_dvd div_c] at factor
  repeat rw [Nat.mul_assoc] at factor
  exact Nat.eq_of_mul_eq_mul_left d_pos factor

theorem pos_of_div : 0 < d ∧ d ≤ n → 1 ≤ n / d :=
  fun _ =>
  have : n / d = (n - d)/d + 1 := by
    rw [Nat.div_eq, if_pos]; assumption
  calc 1 ≤ (n - d) / d + 1 := Nat.succ_le_succ <| Nat.zero_le _
       _ = n / d           := this.symm

theorem reg_of_proper_div (reg_d : Reg d) (p_div_d : p ∣ d) (d_ne_p : d ≠ p) :
   Reg (d / p) :=
  have factor_d := factors_of_dvd p_div_d 
  let q := d / p
  if qz : q = 0 then
    have : d = 0 := Nat.mul_zero p ▸ qz ▸ factor_d
    nz_of_reg reg_d this |>.elim
  else if qo : q = 1 then
    have : d = p := Nat.mul_one p ▸ qo ▸ factor_d
    d_ne_p this |>.elim
  else
    show Reg (d / p) from Nat.lt_or_ge q 2 >l
      fun  _ => match q with
      | 0 => qz rfl |>.elim
      | 1 => qo rfl |>.elim

def PrimeTo (n q : Nat) : Prop :=
  if q ≥ 2 then
    (q ∤ n) ∧ (PrimeTo n (q-1))
  else
    True
notation n" ⊹ "m => PrimeTo n m
/- Note : The name PrimeTo is justified by the fact that
   PrimeTo n q implies (n, q) = 1. More descriptive, but verbose,
   would be PrimeUpTo. -/

def decPrimeTo (n q : Nat) : Decidable (n ⊹ q) :=
  if reg_q : q ≥ 2 then
    if ndiv_n : q ∤ n then
      match decPrimeTo n (q - 1) with
      | isTrue proof  => isTrue  <| by
        unfold PrimeTo; simp only [proof, if_pos, ndiv_n, reg_q]
      | isFalse proof => isFalse <| by
        unfold PrimeTo; simp only [proof, if_pos, ndiv_n, reg_q]
    else
      isFalse <| by unfold PrimeTo
                    simp only [if_pos, ndiv_n, reg_q]
                    intro ⟨_,_⟩; assumption
  else
    isTrue <| by unfold PrimeTo; simp only [if_neg, reg_q]

instance : Decidable (PrimeTo n q) :=
  decPrimeTo n q

theorem not_dvd_of_prime_to
    (reg_k : Reg k) (k_le_m : k ≤ m) (ndiv : n ⊹ m) : k ∤ n :=
  let ⟨ndiv_top, ndiv_rest⟩ : (m ∤ n) ∧ (n ⊹ (m - 1)) := by
    unfold PrimeTo at ndiv
    simp only [reg_monotone reg_k k_le_m, if_pos] at ndiv
    assumption
  if h : k = m then
    h ▸ ndiv_top
  else
    have k_lt_m := Nat.lt_of_le_of_ne k_le_m h
    have : (m - 1) + 1 = m :=
      Nat.succ_pred <| nz_of_pos <| pos_of_reg <| reg_monotone reg_k k_le_m 
    have : k ≤ m - 1 :=
      Nat.le_of_lt_succ <| this ▸ k_lt_m
    not_dvd_of_prime_to reg_k this ndiv_rest

theorem prime_to_monotone
    (reg_p : Reg p) (reg_q : Reg q) (n_ndiv_q : n ⊹ q) (p_div_n : p ∣ n) :
    p ⊹ q := by
  unfold PrimeTo at *
  simp only [if_pos, reg_p, reg_q]
  simp only [if_pos, reg_p, reg_q] at n_ndiv_q
  let ⟨not_q_div_n, n_ndiv_pred_q⟩ := n_ndiv_q
  have : q ∤ p := (dvd_trans . p_div_n |> not_q_div_n)
  exact
    if reg_pred_q : Reg (q - 1) then
      ⟨this,
        prime_to_monotone reg_p reg_pred_q n_ndiv_pred_q p_div_n⟩
    else
      have one_ge : 1 ≥ q - 1 := Nat.le_of_lt_succ <| Nat.gt_of_not_le reg_pred_q
      have one_le : 1 ≤ q - 1 := pred_ge_one_of_reg reg_q
      have q_eq_2 : q - 1 = 1 := eq_of_sandwich one_ge one_le 
      ⟨this, by unfold PrimeTo; simp only [q_eq_2, if_neg]⟩

theorem construct_prime_to
    (reg_m : Reg m) (reg_n : Reg n) (m_le_n : m ≤ n)
    (p : ∀ k, Reg k ∧ k < m → (k ∤ n)) : PrimeTo n (m - 1) :=
  match m with
  | 2 => by
    unfold PrimeTo
    rw [if_neg]
    repeat decide
  | k + 3 => by
    have reg_small : Reg (k + 2) := Nat.le_add_left 2 k
    have lt_pred : k + 2 < k + 3 := pred_lt_of_reg reg_m
    have p₁ : ∀ z, Reg z ∧ z < k + 2 → (z ∤ n) :=
      fun z ⟨reg_z, small_z⟩ =>
      p z ⟨reg_z, Nat.lt_trans small_z lt_pred⟩
    unfold PrimeTo
    rw [if_pos, Nat.add_sub_assoc, Nat.add_sub_assoc]
    have div_n : (k + 2) ∤ n := p (k + 2) ⟨reg_small, lt_pred⟩
    have leq_n : (k + 2) ≤ n := Nat.le_trans (Nat.le_succ _) m_le_n
    apply And.intro
    .  exact div_n
    .  exact construct_prime_to reg_small reg_n leq_n p₁
    repeat decide
    assumption

def MinDivisor (n d : Nat) : Prop :=
 Reg d ∧ (d ∣ n) ∧ (n ⊹ (d - 1))

def decMinDivisor (n d : Nat) : Decidable (MinDivisor n d) := by
  unfold MinDivisor
  exact instDecidableAnd

instance : Decidable (MinDivisor n d) :=
  decMinDivisor n d

def DivisorAccumulator
    (d : Nat) (reg_d : Reg d) (acc : n ⊹ (d - 1)) (n_geq_d : d ≤ n) :
    ∃ d, MinDivisor n d :=
  if h : d < n then
    if dvd_d : d ∣ n then
      ⟨d, ⟨reg_d, dvd_d, acc⟩⟩
    else
      have reg_succ_d : Reg (d + 1) :=
        reg_monotone reg_d (Nat.le_succ d)
      have acc_succ : n ⊹ d := by
        unfold PrimeTo
        simp only [if_pos, reg_d]
        exact ⟨dvd_d, acc⟩
      DivisorAccumulator (d + 1) reg_succ_d acc_succ h
  else
    have d_eq_n : d = n :=
      Nat.eq_or_lt_of_le n_geq_d >r (h . |>.elim)
    ⟨n, ⟨d_eq_n ▸ reg_d, dvd_self, d_eq_n ▸ acc⟩⟩
termination_by _ => n - d

def hasMinDivisor (n : Nat) (reg_n : Reg n) :
    ∃ d : Nat, MinDivisor n d :=
  DivisorAccumulator 2
    (by decide)
    (by unfold PrimeTo; simp only [if_neg, *])
    (by assumption)

def RecPrime (p : Nat) : Prop :=
  Reg p ∧ p ⊹ (p - 1)

instance : Decidable (RecPrime p) := by
  unfold RecPrime
  exact instDecidableAnd

theorem first_rec_prime : RecPrime 2 := by
  decide

theorem RecPrime_of_MinDivisor : MinDivisor n p → RecPrime p :=
  fun ⟨reg_p, p_div_n, p_ndiv_rest⟩ =>
    if h : p = 2 then
      by simp only [first_rec_prime, h]
    else
      have reg_pred : 2 ≤ (p - 1) := reg_pred_of_reg_ne_two reg_p h
      ⟨reg_p, prime_to_monotone reg_p reg_pred p_ndiv_rest p_div_n⟩

theorem rec_prime_divisor :
    ∀ n, Reg n → ∃ p, RecPrime p ∧ (p ∣ n) := fun n reg_n =>
  have ⟨d, minDiv⟩ := hasMinDivisor n reg_n
  ⟨d, ⟨RecPrime_of_MinDivisor minDiv, minDiv.2.1⟩⟩

theorem nat_of_prime : Prime n → NatPrime n :=
  fun prime_n =>
    let ⟨reg_n, red_prime⟩ := reduced_primality prime_n
    ⟨reg_n,
      fun d₁ ⟨reg₁, small₁⟩ small_div_n =>
        let d₂ := n / d₁
        have pos_d₁ : d₁ > 0 := pos_of_reg reg₁
        have pos_d₂ : d₂ > 0 := pos_of_div ⟨pos_d₁, Nat.le_of_lt small₁⟩
        have small₂ : d₂ < n := Nat.div_lt_self (pos_of_reg reg_n) reg₁
        have : n = d₁ * d₂ := factors_of_dvd small_div_n
        dvd_of_eq this |> red_prime d₁ d₂ ⟨small₁, small₂⟩ |>.elim
          (fun div₁ => not_lt_of_dvd_pos pos_d₁ div₁ small₁)
          (fun div₂ => not_lt_of_dvd_pos pos_d₂ div₂ small₂)⟩

theorem nat_of_rec : RecPrime n → NatPrime n :=
  fun ⟨reg_n, ndiv_n⟩ =>
  ⟨reg_n,
    fun _ ⟨reg_m, small_m⟩ =>
    not_dvd_of_prime_to reg_m
      (Nat.succ_pred (nz_of_reg reg_n) ▸ small_m |> Nat.le_of_lt_succ)
      ndiv_n⟩

theorem rec_of_nat : NatPrime n → RecPrime n :=
  fun ⟨reg_n, all_ndiv_n⟩ =>
  ⟨reg_n, construct_prime_to reg_n reg_n (Nat.le_refl n) all_ndiv_n⟩

instance : Decidable (NatPrime n) :=
  if rec_prime : RecPrime n then
    isTrue  <| nat_of_rec rec_prime
  else
    isFalse <| fun nat_prime =>
      rec_of_nat nat_prime |> rec_prime

theorem first_nat_prime : NatPrime 2 := by decide

theorem not_factor (factors : p = c * n) (small_p : p < n) (pos_c : 0 < c) :
    False := Nat.lt_irrefl n <| calc
  n ≤ c * n := by have := Nat.mul_le_mul_right n pos_c
                  rw [Nat.one_mul] at this; assumption
  _ = p     := factors.symm
  _ < n     := small_p

def ReducibleDividend (n m : Nat) :=
  (n ∣ m) ∧ ∃ p q, p ⋖ n ∧ q ⋖ n ∧ m = p * q

def decidable_exists (d : Nat → Nat → Prop) (n : Nat) [DecidablePred (d n)] :
    Decidable (∃ p, p ⋖ n ∧ (d n p)) :=
  if small_n : n ≤ 2 then
    isFalse <| fun ⟨p, p_regular_range, _⟩ =>
    Nat.lt_irrefl 2 <| calc
      2 ≤ p := p_regular_range.1
      _ < n := p_regular_range.2
      _ ≤ 2 := small_n
  else
    have big_n : 2 < n := Nat.gt_of_not_le small_n
    have : ¬ ∃ p, p ⋖ 2 ∧ d n p :=
      fun ⟨p, contra, _⟩ =>
      Nat.lt_irrefl 2 <| calc
        2 ≤ p := contra.1
        _ < 2 := contra.2 
    go 2 (by decide) (Nat.le_of_lt big_n) this where
    go (k : Nat) (reg_k : Reg k) (k_le_n : k ≤ n)
       (sofar : ¬ ∃ p, p ⋖ k ∧ (d n p)) :
        Decidable  (∃ p, p ⋖ n ∧ (d n p)) :=
      if k_eq_n : k = n then
        isFalse <| k_eq_n ▸ sofar
      else
        have k_lt_n      : k < n     := Nat.lt_of_le_of_ne k_le_n k_eq_n
        have succ_k_le_n : k + 1 ≤ n := Nat.succ_le_of_lt k_lt_n
        have reg_to      : k ⋖ n     := ⟨reg_k, k_lt_n⟩
        if contra : d n k then
          isTrue ⟨k, reg_to, contra⟩
        else
          have nextfar : ¬ ∃ p, p ⋖ (k + 1) ∧ (d n p) :=
            fun ⟨p, p_regular_range, p_sat⟩ =>
            if p_lt_k : p < k then
              have : p ⋖ k := ⟨p_regular_range.1, p_lt_k⟩
              sofar ⟨p, this, p_sat⟩
            else
              have : p = k := eq_of_le_of_not_lt 
                (Nat.le_of_lt_succ p_regular_range.2) p_lt_k
              contra (this ▸ p_sat)
          have _ : n - (k + 1) < n - k := Nat.sub_lt
            (Nat.sub_ne_zero_of_lt k_lt_n |> Nat.zero_lt_of_ne_zero)
            (Nat.zero_lt_succ 0)
          have : k ≤ k + 1 := Nat.le_succ k 
          go (k + 1) (reg_monotone reg_k this) succ_k_le_n nextfar 
termination_by
  go _ => n - k

def divisionEq (n p q c : Nat) := p * q = c * n

instance : Decidable (divisionEq n p q c) := by
  unfold divisionEq
  apply Nat.decEq

def decidable_divisionEq (n q c : Nat) :
    Decidable (∃ p, p ⋖ n ∧ divisionEq n p q c) :=
  decidable_exists (fun n x => divisionEq n x q c) n

abbrev divisionPred (n q c : Nat) :=
  ∃ p, p ⋖ n ∧ divisionEq n p q c

def decidable_div_pred : Decidable (divisionPred n q c) := by
  unfold divisionPred
  apply decidable_divisionEq

instance : Decidable (divisionPred n q c) :=
  decidable_div_pred

def dec_ref (n c : Nat) :
    Decidable (∃ q, q ⋖ n ∧ divisionPred n q c) :=
  decidable_exists (fun n x => divisionPred n x c) n

abbrev divPred (n c : Nat) :=
  ∃ q, q ⋖ n ∧ divisionPred n q c

instance : Decidable (divPred n c) := by
  unfold divPred
  apply dec_ref

def factorPredicate (n c : Nat) :=
  ∃ p q : Nat,
    2 ≤ p ∧ p < n ∧
    2 ≤ q ∧ q < n ∧
    p * q = c * n

theorem factorPredicate_iff_divPred :
    divPred n c ↔ factorPredicate n c :=
  ⟨fun h => by
    unfold divPred divisionPred divisionEq RegularRange at h
    have ⟨q, ⟨⟨reg_q, q_lt_n⟩, p, ⟨reg_p, p_lt_n⟩, eq⟩⟩ := h
    unfold factorPredicate
    exact ⟨p, q, reg_p, p_lt_n, reg_q, q_lt_n, eq⟩,
  fun h => by
    unfold factorPredicate at h
    have ⟨p, q, reg_p, p_lt_n, reg_q, q_lt_n, eq⟩ := h
    unfold divPred divisionPred divisionEq RegularRange
    exact ⟨q, ⟨⟨reg_q, q_lt_n⟩, p, ⟨reg_p, p_lt_n⟩, eq⟩⟩⟩

instance : Decidable (factorPredicate n c) :=
  if h : divPred n c then
    isTrue  <| factorPredicate_iff_divPred.mp h
  else
    isFalse <| fun contra => h <| factorPredicate_iff_divPred.mpr contra


abbrev Factors {n : Nat} (c : Nat) := factorPredicate n c

mutual
theorem reduced_predicate : NatPrime n → 
    ∀ p q, 1 ≤ p ∧ p < n ∧ 1 ≤ q ∧ q < n → (n ∤ (p * q)) :=
  fun nat_prime_n p q ⟨pos_p, p_lt_n, pos_q, q_lt_n⟩ =>
  have reg_n : Reg n := nat_prime_n.1
  if      pz : p = 0 then have := pz ▸ pos_p; by contradiction
  else if qz : q = 0 then have := qz ▸ pos_q; by contradiction
  else if po : p = 1 then fun n_div_pq =>
    have := Nat.one_mul q ▸ po ▸ n_div_pq
    have := le_of_dvd_pos pos_q <| this
    Nat.lt_irrefl q <| calc
      q < n := q_lt_n
      _ ≤ q := this
  else if qo : q = 1 then fun n_div_pq =>
    have := Nat.mul_one p ▸ qo ▸ n_div_pq
    have := le_of_dvd_pos pos_p <| this
    Nat.lt_irrefl p <| calc
      p < n := p_lt_n
      _ ≤ p := this
  else
    have reg_p : Reg p := match p with | k + 2 => reg_by_match k
    have reg_q : Reg q := match q with | k + 2 => reg_by_match k
    fun ⟨c, pq_eq_nc⟩ =>
      have some_sat : Factors c :=
        ⟨p, q, reg_p, p_lt_n, reg_q, q_lt_n, pq_eq_nc⟩
      have minimal : ∃ m, Factors m ∧ (∀ k, k < m → ¬ Factors k) :=
        minimal_satisfies some_sat
      let ⟨m, ⟨rs_eq_mn, no_smaller⟩⟩ := minimal
      if mz : m = 0 then by
        unfold Factors factorPredicate at rs_eq_mn
        let ⟨p, q, ⟨reg_p, _, reg_q, _, pq_eq_mn⟩⟩ := rs_eq_mn
        rw [mz, Nat.zero_mul] at pq_eq_mn
        have := reg_of_mul_regs reg_p reg_q
        exact nz_of_reg this pq_eq_mn
      else if mo : m = 1 then by
        unfold Factors factorPredicate at rs_eq_mn
        let ⟨p, q, ⟨reg_p, p_lt_n, _, _, pq_eq_mn⟩⟩ := rs_eq_mn
        rw [mo, Nat.one_mul] at pq_eq_mn
        have : p ∣ n := ⟨q, by rw [Nat.mul_comm, pq_eq_mn.symm]⟩
        have : p ∤ n := nat_prime_n.2 p ⟨reg_p, p_lt_n⟩
        contradiction
      else
        have reg_m : Reg m := match m with | k + 2 => reg_by_match k 
        let ⟨p, q, ⟨reg_p, p_lt_n, reg_q, q_lt_n, pq_eq_mn⟩⟩ := rs_eq_mn
        have : n * m < n * q := calc
          n * m = m * n := Nat.mul_comm n m
          _     = p * q := pq_eq_mn.symm
          _     < n * q := Nat.mul_lt_mul_of_pos_right p_lt_n (pos_of_reg reg_q)
        have m_lt_n : m < n := calc
          m ≤ q := Nat.le_of_mul_le_mul_left (Nat.le_of_lt this) (pos_of_reg reg_n)
          _ < n := q_lt_n
        let ⟨p₀, rec_prime_po, po_div_m⟩ := rec_prime_divisor m reg_m
        have : p₀ < n := calc
          p₀ ≤ m := le_of_dvd_pos (pos_of_reg reg_m) po_div_m
          _  < n := m_lt_n
        have pq_eq_nm : p * q = n * m := Nat.mul_comm n m ▸ pq_eq_mn
        have prime_o : Prime p₀ := prime_of_nat <| nat_of_rec rec_prime_po
        have : (p₀ ∣ p) ∨ (p₀ ∣ q) := prime_o.2 p q <|
          dvd_trans po_div_m ⟨n, pq_eq_nm⟩
        this.elim (
          fun po_div_p =>
          have descent : (p / p₀) * q = n * (m / p₀) :=
            have := descend_factors (pos_of_reg prime_o.1) po_div_p po_div_m  pq_eq_mn
            Nat.mul_comm n (m / p₀) ▸ this
          have po_lt_m : m / p₀ < m := Nat.div_lt_self (pos_of_reg reg_m) prime_o.1
          if  reg_po : Reg (p / p₀) then
            have po_lt_n : p / p₀ < n := Nat.lt_trans
              (Nat.div_lt_self (pos_of_reg reg_p) (prime_o.1))
              p_lt_n
            have : @Factors n (m / p₀) :=
              ⟨p / p₀, q, reg_po, po_lt_n, reg_q, q_lt_n,
               Nat.mul_comm (m / p₀) n ▸ descent⟩
            no_smaller (m / p₀) po_lt_m this |>.elim
          else
            zero_one_of_not_reg reg_po |>.elim
              (fun x => pos_of_div ⟨pos_of_reg prime_o.1,
                le_of_dvd_pos (pos_of_reg reg_p) po_div_p⟩ |>
                Nat.not_eq_zero_of_lt <| x)
              (fun po_one =>
                have : q = (m / p₀) * n :=
                  Nat.mul_comm (m / p₀) n ▸ Nat.one_mul q ▸ po_one ▸ descent
                not_factor this q_lt_n (pos_of_div
                  ⟨pos_of_reg prime_o.1,
                  le_of_dvd_pos (pos_of_reg reg_m) po_div_m⟩) |>.elim)
        ) (
          fun po_div_q =>
          have descent : (q / p₀) * p = n * (m / p₀) :=
            have : q * p = m * n := Nat.mul_comm p q ▸ pq_eq_mn
            have := descend_factors (pos_of_reg prime_o.1) po_div_q po_div_m  this
            Nat.mul_comm n (m / p₀) ▸ this
          have po_lt_m : m / p₀ < m := Nat.div_lt_self (pos_of_reg reg_m) prime_o.1
          if reg_po : Reg (q / p₀) then
            have po_lt_n : q / p₀ < n := Nat.lt_trans
              (Nat.div_lt_self (pos_of_reg reg_q) (prime_o.1))
              q_lt_n
            have : @Factors n (m / p₀) :=
              ⟨q / p₀, p, reg_po, po_lt_n, reg_p, p_lt_n,
               Nat.mul_comm (m / p₀) n ▸ descent⟩
            no_smaller (m / p₀) po_lt_m this |>.elim
          else
            zero_one_of_not_reg reg_po |>.elim
              (fun x => pos_of_div ⟨pos_of_reg prime_o.1,
                le_of_dvd_pos (pos_of_reg reg_q) po_div_q⟩ |>
                Nat.not_eq_zero_of_lt <| x
              )
              (fun po_one =>
                have : p = (m / p₀) * n :=
                  Nat.mul_comm (m / p₀) n ▸ Nat.one_mul p ▸ po_one ▸ descent
                not_factor this p_lt_n (pos_of_div
                  ⟨pos_of_reg prime_o.1,
                  le_of_dvd_pos (pos_of_reg reg_m) po_div_m⟩) |>.elim))

theorem prime_of_nat : NatPrime n → Prime n :=
  fun nat_prime_n =>
  let ⟨reg_n, _⟩ := nat_prime_n
  prime_of_not_dvd_prod reg_n <| reduced_predicate nat_prime_n
end

instance : Decidable (Prime n) :=
  if h : NatPrime n then
    isTrue  <| prime_of_nat h
  else
    isFalse <| (h <| nat_of_prime .)

theorem first_prime : Prime 2 :=
  by decide

def factorial : Nat → Nat
  | 0     => 1
  | k + 1 => (k + 1) * factorial k

theorem dvd_factorial (pos_k : 0 < k) (ineq : k ≤ n) :
    k ∣ factorial n :=
  have : 0 < n :=
    calc 0 < k := pos_k
         _ ≤ n := ineq
  match n with
  | r + 1 =>
    if h : k = r + 1 then by
      unfold factorial
      rw [h]
      have : (r + 1) ∣ (r + 1) * factorial r :=
        dvd_monotone (factorial r) dvd_self
      assumption
    else
      have : k ≤ r           := Nat.pred_le_pred <| Nat.lt_of_le_of_ne ineq h
      have : k ∣ factorial r := dvd_factorial pos_k this
      have                   := dvd_monotone (r + 1) this
      by rw [Nat.mul_comm] at this; assumption

theorem factorial_positive : ∀ n, factorial n > 0
  | 0     => by decide
  | k + 1 => Nat.mul_pos (Nat.succ_pos k) (factorial_positive k)

theorem greater_prime_of_any_nat :
    ∀ n, ∃ p, Prime p ∧ p > n :=
  fun n =>
  let Q := factorial n + 1
  have reg_q : Reg Q := 
    Nat.add_le_add (factorial_positive n) (Nat.le_refl 1)
  let ⟨p, rec_prime_p, p_div_q⟩ := rec_prime_divisor Q reg_q
  have prime_p : Prime p :=
    prime_of_nat <| nat_of_rec rec_prime_p
  if contra : p ≤ n then
    have p_div_fact : p ∣ factorial n :=
      dvd_factorial (pos_of_reg rec_prime_p.1) contra 
    have dvd_diff : p ∣ 1 := calc
      p ∣ (factorial n + 1) - factorial n := dvd_diff_of_both ⟨p_div_q, p_div_fact⟩
      _ = (1 + factorial n) - factorial n := by rw [Nat.add_comm]
      _ = 1 := by simp only [Nat.add_sub_assoc, Nat.le_refl, Nat.sub_self] 
    have : p = 1 := one_of_dvd_one dvd_diff
    have := this ▸ rec_prime_p.1
    by contradiction
  else
    ⟨p, prime_p, Nat.gt_of_not_le contra⟩