import Development.AutomorphicArithmetic.Foundations.IwahoriReduction.NormProducts.LUnH
import Development.AbelianVarietyTheory.Definitions.Foundations.HahnPowOrderLeadingCoeff
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective

open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.Kd.K4 Polynomial
open scoped Matrix MatrixGroups

private theorem one_eq_zero_of_products_vanish (N : ℕ) (γ : SL(2, ℤ)) :
    γ ∈ CongruenceSubgroup.Gamma N ↔
      ((N : ℤ) ∣ γ 0 0 - 1 ∧ (N : ℤ) ∣ γ 0 1 ∧ (N : ℤ) ∣ γ 1 0 ∧ (N : ℤ) ∣ γ 1 1 - 1) := by
  rw [CongruenceSubgroup.Gamma_mem]
  simp only [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, Int.cast_one, sub_eq_zero]

private theorem mem_gamma_of_dvd_of_mem_gamma {N P : ℕ} (h : N ∣ P) (γ : SL(2, ℤ)) (hγ : γ ∈ CongruenceSubgroup.Gamma P) :
    γ ∈ CongruenceSubgroup.Gamma N := by
  have h' : (N : ℤ) ∣ (P : ℤ) := Int.natCast_dvd_natCast.2 h
  rw [one_eq_zero_of_products_vanish] at hγ ⊢
  obtain ⟨h1, h2, h3, h4⟩ := hγ
  exact ⟨h'.trans h1, h'.trans h2, h'.trans h3, h'.trans h4⟩

private theorem exists_sl2_neg_mem_gamma_commutator_mem_gamma_mul (A R : ℕ) (hAR : Nat.Coprime A R) :
    ∃ z : SL(2, ℤ), -z ∈ CongruenceSubgroup.Gamma A ∧ z ∈ CongruenceSubgroup.Gamma R ∧
      ∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ CongruenceSubgroup.Gamma (A * R) := by
  obtain ⟨s, r, hsr⟩ := Nat.isCoprime_iff_coprime.2 hAR
  set P : ℤ := (A : ℤ) * R with hP
  set c : ℤ := s * A - r * R with hcdef
  set j : ℤ := -4 * s * r with hj
  have hc : c ^ 2 = 1 + P * j := by
    rw [hcdef, hP, hj]; linear_combination (s * A + r * R + 1) * hsr
  have hdet : Matrix.det !![c, P; -P * j ^ 2, c * (1 - P * j)] = 1 := by
    rw [Matrix.det_fin_two_of]; linear_combination (1 - P * j) * hc
  let z : SL(2, ℤ) := ⟨!![c, P; -P * j ^ 2, c * (1 - P * j)], hdet⟩
  refine ⟨z, ?_, ?_, ?_⟩
  · rw [one_eq_zero_of_products_vanish]
    refine ⟨⟨-2 * s, ?_⟩, ⟨-(R : ℤ), ?_⟩, ⟨R * j ^ 2, ?_⟩, ⟨-2 * s + c * R * j, ?_⟩⟩
    · show -c - 1 = (A : ℤ) * (-2 * s)
      linear_combination hsr - hcdef
    · show -P = (A : ℤ) * (-(R : ℤ))
      linear_combination -hP
    · show -(-P * j ^ 2) = (A : ℤ) * (R * j ^ 2)
      linear_combination j ^ 2 * hP
    · show -(c * (1 - P * j)) - 1 = (A : ℤ) * (-2 * s + c * R * j)
      linear_combination hsr - hcdef + c * j * hP
  · rw [one_eq_zero_of_products_vanish]
    refine ⟨⟨-2 * r, ?_⟩, ⟨(A : ℤ), ?_⟩, ⟨-(A : ℤ) * j ^ 2, ?_⟩, ⟨-2 * r - c * A * j, ?_⟩⟩
    · show c - 1 = (R : ℤ) * (-2 * r)
      linear_combination hcdef + hsr
    · show P = (R : ℤ) * A
      linear_combination hP
    · show -P * j ^ 2 = (R : ℤ) * (-(A : ℤ) * j ^ 2)
      linear_combination -j ^ 2 * hP
    · show c * (1 - P * j) - 1 = (R : ℤ) * (-2 * r - c * A * j)
      linear_combination hcdef + hsr - c * j * hP
  · intro γ
    set π : SL(2, ℤ) →* SL(2, ZMod (A * R)) :=
      Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod (A * R))) with hπ
    have hz : ((π z : SL(2, ZMod (A * R))) : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) =
        (c : ZMod (A * R)) • (1 : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) := by
      have hP0 : ((P : ℤ) : ZMod (A * R)) = 0 := by
        rw [hP]; push_cast; exact_mod_cast ZMod.natCast_self (A * R)
      have hentry : ∀ i k, ((π z : SL(2, ZMod (A * R))) : Matrix (Fin 2) (Fin 2) (ZMod (A * R))) i k =
          (((z : Matrix (Fin 2) (Fin 2) ℤ) i k : ℤ) : ZMod (A * R)) := fun _ _ => rfl
      ext i k
      rw [hentry]
      fin_cases i <;> fin_cases k <;> simp [z, hP0]
    have hcomm : ∀ g : SL(2, ZMod (A * R)), g * π z = π z * g := by
      intro g
      ext1
      simp only [Matrix.SpecialLinearGroup.coe_mul, hz, Matrix.mul_smul, Matrix.smul_mul, mul_one,
        one_mul]
    show γ * z * γ⁻¹ * z⁻¹ ∈ π.ker
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hcomm, mul_assoc (π z),
      mul_inv_cancel (π γ), mul_one, mul_inv_cancel]

private theorem exists_ne_zero_act_eq_mul_of_cocycle {K : Type} [Field K] {Q : Type} [Group Q] (E : Type) [Monoid E]
    (act : Q → K ≃+* K) (res : Q → (E →* K))
    (hres : ∀ p q x, res (p * q) x = act q (res p x))
    (hfin : (Set.range res).Finite)
    (t : Q → K) (ht0 : ∀ q, t q ≠ 0)
    (hcoc : ∀ p q, t (p * q) = t q * act q (t p))
    (hwd : ∀ p q, res p = res q → t p = t q) :
    ∃ β : K, β ≠ 0 ∧ ∀ q, act q β = t q * β := by
  classical
  set S := hfin.toFinset with hS
  have memS : ∀ s, s ∈ S ↔ ∃ p, res p = s := fun s => by
    rw [hS, Set.Finite.mem_toFinset, Set.mem_range]
  let tt : (E →* K) → K := fun s => if h : ∃ p, res p = s then t h.choose else 0
  have htt : ∀ q, tt (res q) = t q := fun q => by
    have h : ∃ p, res p = res q := ⟨q, rfl⟩
    simp only [tt, dif_pos h]
    exact hwd _ _ h.choose_spec
  obtain ⟨y, hy⟩ : ∃ y : E, ∑ s ∈ S, tt s * s y ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    have hli := linearIndependent_iff'.1 (linearIndependent_monoidHom E K) S (fun s => tt s) (by
      funext y
      simpa [Finset.sum_apply, smul_eq_mul] using hcon y)
    have h1 := hli (res 1) ((memS _).2 ⟨1, rfl⟩)
    rw [htt] at h1
    exact ht0 1 h1
  have hres' : ∀ p q, (act q).toMonoidHom.comp (res p) = res (p * q) := fun p q => by
    ext x; simp [hres]
  have key : ∀ q, act q (∑ s ∈ S, tt s * s y) = (t q)⁻¹ * ∑ s ∈ S, tt s * s y := by
    intro q
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_nbij' (fun s => (act q).toMonoidHom.comp s)
      (fun s => (act q⁻¹).toMonoidHom.comp s) ?_ ?_ ?_ ?_ ?_
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      exact (memS _).2 ⟨p * q, (hres' p q).symm⟩
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      exact (memS _).2 ⟨p * q⁻¹, (hres' p q⁻¹).symm⟩
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', hres', mul_inv_cancel_right]
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', hres', inv_mul_cancel_right]
    · intro s hs
      obtain ⟨p, rfl⟩ := (memS s).1 hs
      rw [hres', htt, htt, map_mul, hcoc]
      have : ((act q).toMonoidHom.comp (res p)) y = act q (res p y) := rfl
      rw [← hres] at this
      rw [← hres]
      field_simp [ht0 q]
  refine ⟨(∑ s ∈ S, tt s * s y)⁻¹, inv_ne_zero hy, fun q => ?_⟩
  rw [map_inv₀, key, mul_inv, inv_inv]

private theorem sl_apply_eq_of_pow_eq_one {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ}
    (X : Tower Ω ε) (g : GQ) (m : ℕ) (hm : 0 < m) (r : X.K) (hr : r ^ m = 1) :
    X.sl g r = r := by
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have hint : IsIntegral Ω r := IsIntegral.of_pow hm (by rw [hr]; exact isIntegral_one)
  have hdeg : (minpoly Ω r).natDegree = 1 :=
    Polynomial.natDegree_eq_of_degree_eq_some
      (IsAlgClosed.degree_eq_one_of_irreducible Ω (minpoly.irreducible hint))
  obtain ⟨c, hc⟩ := minpoly.natDegree_eq_one_iff.1 hdeg
  rw [← hc]
  exact (X.sl g).commutes c

theorem UpperTheory.Kd.K4.h90 :
    ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), ∀ (H : Subgroup SL(2, ℤ)) (M L m : ℕ) (a : X.Kˣ), 0 < M → 0 < m → L.Prime → CongruenceSubgroup.Gamma M ≤ H → -1 ∉ H → InvH X H m a → ∀ v N : ℕ, 0 < N → Nat.Coprime L N →
      ∃ z : SL(2, ℤ), -z ∈ CongruenceSubgroup.Gamma (L ^ v) ∧ z ∈ CongruenceSubgroup.Gamma N ∧ (∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ H) ∧
        (∀ γ : SL(2, ℤ), X.sl (ofSL (γ * z)) (a : X.K) = X.sl (ofSL (z * γ)) (a : X.K)) ∧
        ∃ f ∈ lev X H, ∃ h : X.K, h ≠ 0 ∧ (a : X.K) / X.sl (ofSL z) (a : X.K) = f * h ^ m := by
  intro Ω _ _ _ ε X H M L m a hM hm hL hMH _hneg hInv v N hN hLN
  classical
  have hmul : ∀ (γ δ : SL(2, ℤ)) (f : X.K),
      X.sl (ofSL (γ * δ)) f = X.sl (ofSL δ) (X.sl (ofSL γ) f) := by
    intro γ δ f; rw [map_mul]; exact X.sl_mul _ _ f
  have ha0 : (a : X.K) ≠ 0 := a.ne_zero
  obtain ⟨Ma, hMa, hfixa⟩ := X.level (a : X.K)
  set W0 := M * Ma with hW0
  have hW0pos : 0 < W0 := Nat.mul_pos hM hMa
  haveI : NeZero W0 := ⟨hW0pos.ne'⟩
  set π0 : SL(2, ℤ) →* SL(2, ZMod W0) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod W0)) with hπ0
  have hrep : ∀ w : SL(2, ZMod W0), ∃ g : SL(2, ℤ), (∃ γ ∈ H, π0 γ = w) → (g ∈ H ∧ π0 g = w) := by
    intro w
    by_cases h : ∃ γ ∈ H, π0 γ = w
    · obtain ⟨γ, hγ, hw⟩ := h
      exact ⟨γ, fun _ => ⟨hγ, hw⟩⟩
    · exact ⟨1, fun h' => absurd h' h⟩
  choose rep hrep using hrep
  have hu : ∀ w : SL(2, ZMod W0), ∃ u : X.K, u ≠ 0 ∧
      (rep w ∈ H → X.sl (ofSL (rep w)) (a : X.K) = (a : X.K) * u ^ m) := by
    intro w
    by_cases h : rep w ∈ H
    · obtain ⟨u, hu⟩ := hInv _ h
      exact ⟨u, u.ne_zero, fun _ => hu⟩
    · exact ⟨1, one_ne_zero, fun h' => absurd h' h⟩
  choose uq huq0 huq using hu
  have hlev : ∀ w : SL(2, ZMod W0), ∃ Lw : ℕ, 0 < Lw ∧
      ∀ γ ∈ CongruenceSubgroup.Gamma Lw, X.sl (ofSL γ) (uq w) = uq w := fun w => X.level (uq w)
  choose Lw hLw0 hLw using hlev
  set W := W0 * ∏ w, Lw w with hWdef
  have hWpos : 0 < W := Nat.mul_pos hW0pos (Finset.prod_pos fun w _ => hLw0 w)
  have hW0W : W0 ∣ W := Dvd.intro _ rfl
  have hLwW : ∀ w, Lw w ∣ W := fun w =>
    (Finset.dvd_prod_of_mem Lw (Finset.mem_univ w)).trans (Dvd.intro_left _ rfl)
  have hfixW : ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) (a : X.K) = a := fun c hc =>
    hfixa c (mem_gamma_of_dvd_of_mem_gamma ((Dvd.intro_left _ rfl : Ma ∣ W0).trans hW0W) c hc)
  have hWH : ∀ c ∈ CongruenceSubgroup.Gamma W, c ∈ H := fun c hc =>
    hMH (mem_gamma_of_dvd_of_mem_gamma ((Dvd.intro _ rfl : M ∣ W0).trans hW0W) c hc)
  have hUfix : ∀ w, ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) (uq w) = uq w := fun w c hc =>
    hLw w c (mem_gamma_of_dvd_of_mem_gamma (hLwW w) c hc)
  have hU : ∀ γ ∈ H, X.sl (ofSL γ) (a : X.K) = (a : X.K) * uq (π0 γ) ^ m := by
    intro γ hγ
    obtain ⟨hr1, hr2⟩ := hrep (π0 γ) ⟨γ, hγ, rfl⟩
    have hc : rep (π0 γ) * γ⁻¹ ∈ CongruenceSubgroup.Gamma W0 := by
      show rep (π0 γ) * γ⁻¹ ∈ π0.ker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hr2, mul_inv_cancel]
    rw [← huq _ hr1]
    have : rep (π0 γ) = (rep (π0 γ) * γ⁻¹) * γ := by group
    rw [this, hmul, hfixa _ (mem_gamma_of_dvd_of_mem_gamma (Dvd.intro_left _ rfl) _ hc)]
  set P := W * N * L ^ v with hPdef
  have hP0 : P ≠ 0 := by
    have : 0 < P := Nat.mul_pos (Nat.mul_pos hWpos hN) (pow_pos hL.pos v)
    exact this.ne'
  set A := L ^ P.factorization L with hAdef
  set R := P / A with hRdef
  have hAR : A * R = P := Nat.ordProj_mul_ordCompl_eq_self P L
  have hcop : Nat.Coprime A R := (Nat.coprime_ordCompl hL hP0).pow_left _
  obtain ⟨z, hz1, hz2, hz3⟩ := exists_sl2_neg_mem_gamma_commutator_mem_gamma_mul A R hcop
  have hLvA : L ^ v ∣ A := by
    apply pow_dvd_pow
    exact (hL.pow_dvd_iff_le_factorization hP0).1 (Dvd.intro_left _ rfl)
  have hNR : N ∣ R := by
    have hNA : Nat.Coprime N A := Nat.Coprime.pow_right _ hLN.symm
    have hNP : N ∣ A * R := by rw [hAR, hPdef]; exact ⟨W * L ^ v, by ring⟩
    exact (Nat.Coprime.dvd_mul_left hNA).1 hNP
  have hWP : W ∣ A * R := by rw [hAR, hPdef]; exact ⟨N * L ^ v, by ring⟩
  have hcomm : ∀ γ : SL(2, ℤ), γ * z * γ⁻¹ * z⁻¹ ∈ CongruenceSubgroup.Gamma W := fun γ =>
    mem_gamma_of_dvd_of_mem_gamma hWP _ (hz3 γ)
  have hcz : ∀ (γ : SL(2, ℤ)) (x : X.K), (∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) x = x) →
      X.sl (ofSL z) (X.sl (ofSL γ) x) = X.sl (ofSL γ) (X.sl (ofSL z) x) := by
    intro γ x hx
    rw [← hmul, ← hmul]
    have : γ * z = (γ * z * γ⁻¹ * z⁻¹) * (z * γ) := by group
    rw [this, hmul, hx _ (hcomm γ)]
  haveI : NeZero W := ⟨hWpos.ne'⟩
  set πW : SL(2, ℤ) →* SL(2, ZMod W) :=
    Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod W)) with hπW
  let E : Submonoid X.K :=
    { carrier := {x | ∀ c ∈ CongruenceSubgroup.Gamma W, X.sl (ofSL c) x = x}
      mul_mem' := by
        intro x y hx hy c hc
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        rw [map_mul, hx c hc, hy c hc]
      one_mem' := by
        intro c _
        simp }
  let act : H → X.K ≃+* X.K := fun q => (X.sl (ofSL (q : SL(2, ℤ)))).toRingEquiv
  let res : H → (E →* X.K) := fun q =>
    { toFun := fun x => X.sl (ofSL (q : SL(2, ℤ))) (x : X.K)
      map_one' := by simp
      map_mul' := by intro x y; simp }
  let U : H → X.K := fun q => uq (π0 q)
  let t : H → X.K := fun q => U q / X.sl (ofSL z) (U q)
  have hszne : ∀ x : X.K, x ≠ 0 → X.sl (ofSL z) x ≠ 0 := fun x hx => (_root_.map_ne_zero _).2 hx
  have hres : ∀ p q x, res (p * q) x = act q (res p x) := fun p q x => hmul _ _ _
  have hfin : (Set.range res).Finite := by
    let g : SL(2, ZMod W) → (E →* X.K) := fun w =>
      if h : ∃ q : H, πW q = w then res h.choose else 1
    have hg : ∀ q, res q = g (πW q) := by
      intro q
      have h : ∃ q' : H, πW q' = πW q := ⟨q, rfl⟩
      simp only [g, dif_pos h]
      ext x
      have hc : (h.choose : SL(2, ℤ)) * (q : SL(2, ℤ))⁻¹ ∈ CongruenceSubgroup.Gamma W := by
        show _ ∈ πW.ker
        rw [MonoidHom.mem_ker, map_mul, map_inv, h.choose_spec, mul_inv_cancel]
      show X.sl (ofSL q) x = X.sl (ofSL h.choose) x
      have e : (h.choose : SL(2, ℤ)) = ((h.choose : SL(2, ℤ)) * (q : SL(2, ℤ))⁻¹) * q := by group
      rw [e, hmul, x.2 _ hc]
    refine (Set.finite_range g).subset ?_
    rintro _ ⟨q, rfl⟩
    exact ⟨πW q, (hg q).symm⟩
  have ht0 : ∀ q, t q ≠ 0 := fun q => div_ne_zero (huq0 _) (hszne _ (huq0 _))
  have hcoc : ∀ p q, t (p * q) = t q * act q (t p) := by
    intro p q
    have e1 := hU _ (p * q).2
    have e2 : ((p * q : H) : SL(2, ℤ)) = (p : SL(2, ℤ)) * q := rfl
    rw [e2, hmul, hU _ p.2, map_mul, map_pow, hU _ q.2] at e1
    have hpq : U (p * q) ^ m = (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) ^ m := by
      apply mul_left_cancel₀ ha0
      show (a : X.K) * uq (π0 ((p * q : H) : SL(2, ℤ))) ^ m = _
      rw [e2, ← e1]
      ring
    have hden : U q * X.sl (ofSL (q : SL(2, ℤ))) (U p) ≠ 0 :=
      mul_ne_zero (huq0 _) ((_root_.map_ne_zero _).2 (huq0 _))
    set ζ := U (p * q) / (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) with hζdef
    have hζm : ζ ^ m = 1 := by rw [hζdef, div_pow, hpq, div_self (pow_ne_zero _ hden)]
    have hζ : X.sl (ofSL z) ζ = ζ := sl_apply_eq_of_pow_eq_one X _ m hm ζ hζm
    have hζ0 : ζ ≠ 0 := div_ne_zero (huq0 _) hden
    have hUpq : U (p * q) = ζ * (U q * X.sl (ofSL (q : SL(2, ℤ))) (U p)) := by
      rw [hζdef, div_mul_cancel₀ _ hden]
    show U (p * q) / X.sl (ofSL z) (U (p * q)) =
      U q / X.sl (ofSL z) (U q) * X.sl (ofSL (q : SL(2, ℤ))) (U p / X.sl (ofSL z) (U p))
    rw [hUpq, map_mul, map_mul, hζ, map_div₀, ← hcz q (U p) (hUfix _)]
    have h3 : X.sl (ofSL z) (X.sl (ofSL (q : SL(2, ℤ))) (U p)) ≠ 0 :=
      hszne _ ((_root_.map_ne_zero _).2 (huq0 _))
    have h4 := hszne _ (huq0 (π0 q))
    field_simp
  have hwd : ∀ p q, res p = res q → t p = t q := by
    intro p q h
    have e : X.sl (ofSL (p : SL(2, ℤ))) (a : X.K) = X.sl (ofSL (q : SL(2, ℤ))) (a : X.K) :=
      DFunLike.congr_fun h ⟨(a : X.K), hfixW⟩
    rw [hU _ p.2, hU _ q.2] at e
    have hpq : U p ^ m = U q ^ m := mul_left_cancel₀ ha0 e
    set ζ := U p / U q with hζdef
    have hζm : ζ ^ m = 1 := by rw [hζdef, div_pow, hpq, div_self (pow_ne_zero _ (huq0 _))]
    have hζ : X.sl (ofSL z) ζ = ζ := sl_apply_eq_of_pow_eq_one X _ m hm ζ hζm
    have hζ0 : ζ ≠ 0 := div_ne_zero (huq0 _) (huq0 _)
    have hUp : U p = ζ * U q := by rw [hζdef, div_mul_cancel₀ _ (huq0 _)]
    show U p / X.sl (ofSL z) (U p) = U q / X.sl (ofSL z) (U q)
    rw [hUp, map_mul, hζ, mul_div_mul_left _ _ hζ0]
  obtain ⟨β, hβ0, hβ⟩ := exists_ne_zero_act_eq_mul_of_cocycle (↥E) act res hres hfin t ht0 hcoc hwd
  have hinv : ∀ γ ∈ H, X.sl (ofSL γ) ((a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m) =
      (a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m := by
    intro γ hγ
    have hb : X.sl (ofSL γ) β = t ⟨γ, hγ⟩ * β := hβ ⟨γ, hγ⟩
    rw [map_div₀, map_div₀, map_pow, hb, ← hcz γ _ hfixW, hU γ hγ, map_mul, map_pow]
    have h1 := hszne _ ha0
    have h2 := hszne _ (huq0 (π0 γ))
    have h3 := huq0 (π0 γ)
    show (a : X.K) * uq (π0 γ) ^ m / (X.sl (ofSL z) (a : X.K) * X.sl (ofSL z) (uq (π0 γ)) ^ m) /
        (uq (π0 γ) / X.sl (ofSL z) (uq (π0 γ)) * β) ^ m = _
    rw [mul_pow, div_pow]
    field_simp
  refine ⟨z, mem_gamma_of_dvd_of_mem_gamma hLvA _ hz1, mem_gamma_of_dvd_of_mem_gamma hNR _ hz2, fun γ => hWH _ (hcomm γ), ?_,
    (a : X.K) / X.sl (ofSL z) (a : X.K) / β ^ m, ?_, β, hβ0, ?_⟩
  · intro γ
    rw [hmul, hmul]
    exact hcz γ _ hfixW
  · simp only [GlobalTheory.K4.lev, Subfield.mem_iInf]
    intro γ hγ
    exact hinv γ hγ
  · rw [div_mul_cancel₀ _ (pow_ne_zero _ hβ0)]
