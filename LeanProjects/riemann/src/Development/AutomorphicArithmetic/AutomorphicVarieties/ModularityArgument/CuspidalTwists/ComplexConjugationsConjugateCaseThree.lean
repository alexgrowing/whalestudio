import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CuspidalTwists.PromodularityCaseThree
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.MkTower
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.ExistsStrictHenselianAbsolutelyClosedLocalRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.RedOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.DirGPowOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.EltTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.EltOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.QuadEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixAb
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.FrobeniusFields.FixInf
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.SplittingFieldIsoQuadratic
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.ClassFieldRamification.ExistsQuadraticGaussSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.CyclotomicInertiaSpan.OnePrimeOfTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.ClsOnto
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.RootVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.CompIne
import Development.AutomorphicArithmetic.AutomorphicVarieties.PrimitiveFrobeniusFixed.PlaceBasic
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ClsIndep
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.DirichletGroupPowers.ImgRoots
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.UpperTriangularPlaces.BigOm

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem complex_conjugations_conjugate' {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {σ τ : G ℚ Ω} (hσ : IsCC σ) (hτ : IsCC τ) :
    ∃ g : G ℚ Ω, g * τ = σ * g := by
  obtain ⟨j, hj⟩ := hσ
  obtain ⟨j', hj'⟩ := hτ
  letI : Algebra Ω ℂ := j.toAlgebra
  haveI : IsScalarTower ℚ Ω ℂ := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  have key : ∀ x, j (AlgHom.restrictNormal' j'.toRatAlgHom Ω x) = j' x := fun x => AlgHom.restrictNormal_commutes j'.toRatAlgHom Ω x
  refine ⟨AlgHom.restrictNormal' j'.toRatAlgHom Ω, AlgEquiv.ext fun x => j.injective ?_⟩
  rw [AlgEquiv.mul_apply, AlgEquiv.mul_apply, key, hj, hj', key]

private theorem complex_conjugation_sq {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {σ : G ℚ Ω} (hσ : IsCC σ) : σ * σ = 1 := by
  obtain ⟨j, hj⟩ := hσ
  refine AlgEquiv.ext fun x => j.injective ?_
  exact (hj (σ x)).trans ((congrArg (starRingEnd ℂ) (hj x)).trans (Complex.conj_conj _))

private theorem exists_cm_and_real_fields {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω]
    (hpl : ∀ p : ℕ, p.Prime → ∃ A : ValuationSubring Ω, A.valuation (p : Ω) < 1) (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime)
    (H : Subgroup (G ℚ Ω)) (hH : IsOpen (H : Set (G ℚ Ω))) (hc : commutator (G ℚ Ω) ≤ H) (cc : G ℚ Ω) (hcc : IsCC cc) (hm : cc ∈ H) :
    ∃ (K F : IntermediateField ℚ Ω) (_ : NumberField K) (_ : NumberField F) (_ : IsCMField K) (_ : IsTotallyReal F) (_ : IsAbelianGalois ℚ F)
    (J : Subgroup (G ℚ Ω)), Module.finrank ℚ K = 2 ∧ Even (Module.finrank ℚ F) ∧
    (∀ p ∈ S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ J) ∧ (∀ g : G ℚ Ω, g ^ 2 ∈ J) ∧ J ≤ K.fixingSubgroup ∧
    F.fixingSubgroup ≤ H ∧ F.fixingSubgroup ⊓ K.fixingSubgroup = H ⊓ J ∧ ∀ A : ValuationSubring Ω, Ine (F := ℚ) A ⊓ F.fixingSubgroup ≤ K.fixingSubgroup := by
  obtain ⟨p, η, h⟩ := quadEx Ω (-1) S hS
  obtain ⟨p', η', h'⟩ := quadEx Ω (-1) (insert p S) fun q hq => (Finset.mem_insert.1 hq).elim (fun e => e ▸ h.prime) (hS q)
  have hk : ∀ g, g ∈ (η * η'⁻¹).ker ↔ η g = η' g := fun g => by
    rw [MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]
  have ho : IsOpen ((η * η'⁻¹).ker : Set (G ℚ Ω)) :=
    Subgroup.isOpen_mono (H₁ := η.ker ⊓ η'.ker) (fun g hg => (hk g).2 (Eq.trans hg.1 (Eq.symm hg.2))) (h.opn.inter h'.opn)
  obtain ⟨K, _, _, hK, dK⟩ := fixAb Ω η.ker h.opn (Abelianization.commutator_subset_ker _)
  obtain ⟨F, _, _, hF, dF⟩ := fixAb Ω (H ⊓ (η * η'⁻¹).ker) (hH.inter ho) (le_inf hc (Abelianization.commutator_subset_ker _))
  have hN : H.Normal := Subgroup.Normal.of_commutator_le _ hc
  refine ⟨K, F, inferInstance, inferInstance, (fixInf Ω K).2 (fun σ hσ e => ?_) (dK.trans h.idx), (fixInf Ω F).1 fun σ hσ => ?_, inferInstance,
    η.ker ⊓ η'.ker, dK.trans h.idx, ?_, fun q hq A hA => le_inf (h.split q hq A hA) (h'.split q (Finset.mem_insert_of_mem hq) A hA),
    fun g => ⟨?_, ?_⟩, hK ▸ inf_le_left, hF ▸ inf_le_left, ?_, fun A g hg => ?_⟩
  · rw [hK, MonoidHom.mem_ker, h.cc σ hσ] at e
    exact absurd e (by decide)
  · obtain ⟨g, hg⟩ := complex_conjugations_conjugate' hσ hcc
    have e : σ = g * cc * g⁻¹ := by rw [hg, mul_inv_cancel_right]
    rw [hF]
    exact ⟨e ▸ hN.conj_mem cc hm g, (hk σ).2 ((h.cc σ hσ).trans (h'.cc σ hσ).symm)⟩
  · obtain ⟨A, hA⟩ := hpl p h.prime
    obtain ⟨g, hg, e⟩ := h.ram A hA
    have e' : η' g = 1 := h'.split p (Finset.mem_insert_self _ _) A hA (Ine_le_Dec A hg)
    have h2 : (η * η'⁻¹).ker.index = 2 := by
      rw [Subgroup.index_ker]
      have ht : (η * η'⁻¹).range = ⊤ := eq_top_iff.2 fun u _ => by
        rcases Int.units_eq_one_or u with rfl | rfl
        exacts [one_mem _, ⟨g, by simp [e, e']⟩]
      rw [ht, Subgroup.card_top, Nat.card_eq_fintype_card]; rfl
    rw [dF, even_iff_two_dvd, ← h2]
    exact Subgroup.index_dvd_of_le inf_le_right
  · show η (g ^ 2) = 1
    rw [map_pow, Int.units_sq]
  · show η' (g ^ 2) = 1
    rw [map_pow, Int.units_sq]
  · rw [hF, hK]
    ext g
    exact ⟨fun ⟨⟨a, b⟩, d⟩ => ⟨a, d, ((hk g).1 b).symm.trans d⟩, fun ⟨a, b, d⟩ => ⟨⟨a, (hk g).2 (Eq.trans b (Eq.symm d))⟩, b⟩⟩
  · rw [hK]
    by_cases hA : A.valuation (p : Ω) < 1
    · have e := hg.2
      rw [hF] at e
      exact ((hk g).1 e.2).trans (h'.split p (Finset.mem_insert_self _ _) A hA (Ine_le_Dec A hg.1))
    · exact h.unr A hA hg.1

noncomputable section SlopeTestRemainingChoices

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l}

private theorem exists_lift_of_mem_fixing_case_three {F : IntermediateField ℚ Ω} {g : G ℚ Ω} (hg : g ∈ F.fixingSubgroup) : ∃ g' : G F Ω, resQ F g' = g :=
  ⟨AlgEquiv.ofRingEquiv (f := g.toRingEquiv) fun x => (F.mem_fixingSubgroup_iff g).1 hg x.1 x.2, rfl⟩

private theorem restrict_mem_fixing_subgroup_case_three {F : IntermediateField ℚ Ω} (g : G F Ω) : resQ F g ∈ F.fixingSubgroup :=
  (F.mem_fixingSubgroup_iff _).2 fun x hx => g.commutes ⟨x, hx⟩

private theorem restrict_inertia_mem_case_three {F : IntermediateField ℚ Ω} [NumberField F] {A : ValuationSubring Ω} {g : G F Ω}
    (hg : g ∈ Ine (F := F) A) : resQ F g ∈ Ine (F := ℚ) A := ⟨hg.1, hg.2⟩

private theorem neg_sq_pow_ne_one_case_three {R : Type} [CommRing R] {y : Rˣ} {m : ℕ} (hm : Odd m) (h : y ^ m = 1) (hy : y ≠ 1) (h2 : (-1 : Rˣ) ≠ 1)
    {n : ℕ} (h0 : 0 < n) (h4 : n ≤ 4) : (-y ^ 2) ^ n ≠ 1 := by
  intro e
  rcases Nat.even_or_odd n with hn | hn
  · rw [hn.neg_pow, ← pow_mul] at e
    have h8 : (2 * n).Coprime m := by
      have : 2 * n ∣ 2 ^ 3 := by
        obtain ⟨k, rfl⟩ := hn
        have : k = 1 ∨ k = 2 := by omega
        rcases this with rfl | rfl <;> norm_num
      exact Nat.Coprime.coprime_dvd_left this (Nat.Coprime.pow_left 3 ((Nat.coprime_two_left).2 hm))
    exact hy (orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes h8 (orderOf_dvd_of_pow_eq_one e) (orderOf_dvd_of_pow_eq_one h)))
  · have e2 : ((-y ^ 2) ^ n) ^ m = 1 := by rw [e, one_pow]
    rw [← pow_mul, (hn.mul hm).neg_pow, ← pow_mul, ← mul_assoc, mul_comm _ m, pow_mul, h, one_pow] at e2
    exact h2 e2

private theorem neg_pow_ne_one_of_odd_order {R : Type} [CommRing R] {z : Rˣ} {m : ℕ} (hm : Odd m) (h : z ^ m = 1) (hz : z ≠ 1) (h2 : (-1 : Rˣ) ≠ 1)
    {n : ℕ} (h0 : 0 < n) (h4 : n ≤ 4) : (-z) ^ n ≠ 1 := by
  obtain ⟨k, hk⟩ := hm
  have e : (z ^ (k + 1)) ^ 2 = z := by
    rw [← pow_mul, show (k + 1) * 2 = m + 1 by omega, pow_succ, h, one_mul]
  have e1 : (z ^ (k + 1)) ^ m = 1 := by rw [← pow_mul, mul_comm, pow_mul, h, one_pow]
  have e2 : z ^ (k + 1) ≠ 1 := fun h' => hz (by rw [← e, h', one_pow])
  have := neg_sq_pow_ne_one_case_three ⟨k, hk⟩ e1 e2 h2 h0 h4
  rwa [e] at this

private theorem odd_order_unit_ne_neg_one {R : Type} [CommRing R] {z : Rˣ} {m : ℕ} (hm : Odd m) (h : z ^ m = 1) (h2 : (-1 : Rˣ) ≠ 1) : z ≠ -1 := by
  rintro rfl
  exact h2 (by rw [← hm.neg_one_pow]; exact h)

private theorem root_character_ne_one {R : Type} [CommRing R] {z : Rˣ} (h2 : (-1 : Rˣ) ≠ 1) (h1 : z ≠ 1) (hn : z ≠ -1) :
    ∀ w ∈ roots, (-1 : Rˣ) ^ w.1 * z ^ w.2 ≠ 1 := by
  have hw : ∀ w ∈ roots, w = (1, 0) ∨ w = (-1, 0) ∨ w = (-1, 1) ∨ w = (1, -1) ∨ w = (1, 1) ∨ w = (-1, -1) ∨ w = (0, 1) ∨ w = (0, -1) := by
    decide
  have hneg : ((-1 : Rˣ))⁻¹ = -1 := inv_eq_of_mul_eq_one_right (by rw [neg_one_mul, neg_neg])
  have hi : z⁻¹ ≠ 1 := fun e => h1 (inv_eq_one.1 e)
  have hin : z⁻¹ ≠ -1 := fun e => hn (by rw [← inv_inv z, e, hneg])
  intro w hw'
  rcases hw w hw' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [zpow_one, zpow_zero, mul_one]; exact h2
  · rw [zpow_neg, zpow_one, zpow_zero, mul_one, hneg]; exact h2
  · intro e
    apply hn
    rw [zpow_neg, zpow_one, zpow_one, hneg, neg_one_mul] at e
    exact neg_eq_iff_eq_neg.1 e
  · intro e
    apply hin
    rw [zpow_one, zpow_neg, zpow_one, neg_one_mul] at e
    exact neg_eq_iff_eq_neg.1 e
  · intro e
    apply hn
    rw [zpow_one, zpow_one, neg_one_mul] at e
    exact neg_eq_iff_eq_neg.1 e
  · intro e
    apply hin
    rw [zpow_neg, zpow_neg, zpow_one, zpow_one, hneg, neg_one_mul] at e
    exact neg_eq_iff_eq_neg.1 e
  · rw [zpow_zero, zpow_one, one_mul]; exact h1
  · rw [zpow_zero, zpow_neg, zpow_one, one_mul]; exact hi

private theorem distinct_four_eigenvalues_injective {R : Type} [CommRing R] {z : Rˣ} (h2 : (-1 : Rˣ) ≠ 1) (h1 : z ≠ 1) (hn : z ≠ -1) (i j : Fin 4)
    (e : (![1, -1, z, -z] : Fin 4 → Rˣ) i = ![1, -1, z, -z] j) : i = j := by
  have hzz : z ≠ -z := fun e' => h2 (by
    have : z * (-1) = z * 1 := by rw [mul_neg_one, mul_one]; exact e'.symm
    exact mul_left_cancel this)
  fin_cases i <;> fin_cases j <;> (try simp at e) <;> (try rfl) <;> first
    | exact absurd e.symm h2
    | exact absurd e h2
    | exact absurd e.symm h1
    | exact absurd e h1
    | exact absurd e.symm hn
    | exact absurd e hn
    | exact absurd e hzz
    | exact absurd e.symm hzz
    | exact absurd (neg_eq_iff_eq_neg.1 e.symm) hn
    | exact absurd (neg_eq_iff_eq_neg.1 e) hn
    | exact absurd (neg_eq_iff_eq_neg.1 e).symm hn
    | exact absurd (neg_inj.1 e).symm h1
    | exact absurd (neg_inj.1 e) h1

private abbrev bU (c : Coef l) : c.Oˣ →* (ResidueField c.O)ˣ := Units.map (residue c.O : c.O →* ResidueField c.O)

private def sgnP (pr : Bool) : ℤ := if pr then -1 else 1

private theorem reduction_cyclotomic_char_eq_case_three (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (chiO ℚ Ω l c.O g) = bU c (D.om g) :=
  Units.ext (hD.om_bar g).symm

private theorem reduction_alpha_eq_xi_case_three (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (D.al g) = bU c (D.ξ g) := by
  simp only [Raw.al, MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, map_inv, reduction_cyclotomic_char_eq_case_three D hD, mul_inv_cancel, one_mul]

private theorem reduction_psi_eq_omega_pow_case_three (D : Raw Ω c) (hD : D.Good) (g : G ℚ Ω) : bU c (D.Psi g) = bU c (D.om g) ^ D.e * bU c (D.ψ g) := by
  simp only [Raw.Psi, UpperTheory.V.Chr.Psi, MonoidHom.mul_apply, zpow_natCast, MonoidHom.pow_apply, map_mul, map_pow, reduction_cyclotomic_char_eq_case_three D hD]

private theorem character_ratios_eq_case_three (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) :
    chi D pr 0 g * (chi D pr 1 g)⁻¹ = D.al g ∧ chi D pr 0 g * (chi D pr 2 g)⁻¹ = D.Psi g ^ sgnP pr ∧
      chi D pr 0 g * (chi D pr 3 g)⁻¹ = D.al g * D.Psi g ^ sgnP pr := by
  cases pr <;> simp [chi, lab, Raw.ps, Raw.th, sgnP, mul_comm]

private theorem residual_root_character_explicit {D : Raw Ω c} (T : Tower D) (w : ℤ × ℤ) (g : G T.F Ω) :
    T.rb w g = ((bU c (D.al (resQ T.F g)) ^ w.1 * (bU c (D.Psi (resQ T.F g)) ^ sgnP T.pr) ^ w.2 : (ResidueField c.O)ˣ) :
      ResidueField c.O) := by
  obtain ⟨h1, h2, -⟩ := character_ratios_eq_case_three D T.pr (resQ T.F g)
  have e : (T.fr ∅).rt w g = D.al (resQ T.F g) ^ w.1 * (D.Psi (resQ T.F g) ^ sgnP T.pr) ^ w.2 := by
    rw [← h1, ← h2]; rfl
  have e2 : bU c ((T.fr ∅).rt w g) = bU c (D.al (resQ T.F g)) ^ w.1 * (bU c (D.Psi (resQ T.F g)) ^ sgnP T.pr) ^ w.2 := by
    rw [e, map_mul, map_zpow, map_zpow, map_zpow]
  rw [← e2]; rfl

private theorem reduced_character_quotient_explicit (D : Raw Ω c) (pr : Bool) (g : G ℚ Ω) (i : Fin 4) :
    bU c (chi D pr i g) = bU c (chi D pr 0 g) *
      ((![1, bU c (D.al g), bU c (D.Psi g) ^ sgnP pr, bU c (D.al g) * bU c (D.Psi g) ^ sgnP pr] : Fin 4 → (ResidueField c.O)ˣ) i)⁻¹ := by
  obtain ⟨h1, h2, h3⟩ := character_ratios_eq_case_three D pr g
  have k1 := congrArg (bU c) h1
  have k2 := congrArg (bU c) h2
  have k3 := congrArg (bU c) h3
  simp only [map_mul, map_inv, map_zpow] at k1 k2 k3
  fin_cases i
  · simp
  · simp [← k1]
  · simp [← k2]
  · simp [← k3]

private theorem residual_rep_trivial_iff_case_three (D : Raw Ω c) (g : G ℚ Ω) : D.rbar g = 1 ↔ bU c (D.al g) = 1 ∧ bU c (D.Psi g) = 1 := by
  have key : ∀ i j, D.rbar g i j = residue c.O (Matrix.diagonal (fun i => (D.ps i g : c.O)) i j) := fun _ _ => rfl
  constructor
  · intro h
    have h1 := key 1 1
    have h2 := key 2 2
    rw [h, Matrix.one_apply_eq, Matrix.diagonal_apply_eq] at h1 h2
    exact ⟨Units.ext h2.symm, Units.ext h1.symm⟩
  · rintro ⟨h1, h2⟩
    have h3 : ∀ i, residue c.O (D.ps i g : c.O) = 1 := fun i => by
      have : bU c (D.ps i g) = 1 := by
        fin_cases i <;> simp [Raw.ps, Raw.th, h1, h2]
      exact congrArg Units.val this
    ext i j
    rw [key]
    by_cases hij : i = j
    · subst hij; rw [Matrix.diagonal_apply_eq, Matrix.one_apply_eq, h3]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij, map_zero]

end SlopeTestRemainingChoices

private theorem jacobi_symbol_eq_one_of_congr (p q : ℕ) (s : ℤˣ) (hq : q.Prime) (h8 : (p : ℤ) ≡ s [ZMOD 8]) (hpq : (p : ℤ) ≡ s [ZMOD q]) :
    jacobiSym q p = 1 := by
  have hp : Odd p := by
    rw [Nat.odd_iff]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 <;> omega
  rcases hq.eq_two_or_odd' with rfl | hq2
  · rw [Nat.cast_ofNat, jacobiSym.at_two hp, ZMod.χ₈_nat_eq_if_mod_eight]
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8
    · rw [if_neg (by omega), if_pos (by omega)]
    · rw [if_neg (by omega), if_pos (by omega)]
  · have e : jacobiSym p q = jacobiSym s q := jacobiSym.mod_left' hpq
    rcases Int.units_eq_one_or s with rfl | rfl <;> simp only [Int.ModEq, Units.val_one, Units.val_neg] at h8 e
    · rw [jacobiSym.quadratic_reciprocity_one_mod_four' hq2 (by omega), e, jacobiSym.one_left]
    · have hq' := Nat.odd_iff.1 hq2
      rcases (by omega : q % 4 = 1 ∨ q % 4 = 3) with h | h
      · rw [jacobiSym.quadratic_reciprocity_one_mod_four h hp, e, jacobiSym.at_neg_one hq2, ZMod.χ₄_nat_one_mod_four h]
      · rw [jacobiSym.quadratic_reciprocity_three_mod_four h (by omega), e, jacobiSym.at_neg_one hq2,
          ZMod.χ₄_nat_three_mod_four h, neg_neg]

private theorem exists_prime_quadratic_conditions (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (B : ℕ) :
    ∃ (p : ℕ) (_ : Fact p.Prime), p ∉ S ∧ p ≠ 2 ∧ quadraticChar (ZMod p) (-1) = -1 ∧
      (∀ q ∈ S, quadraticChar (ZMod p) (q : ZMod p) = 1) ∧ B < p ∧ p % 4 = 3 := by
  have h0 : 8 * ∏ q ∈ S, q ≠ 0 := mul_ne_zero (by norm_num) (Finset.prod_ne_zero_iff.2 fun q hq => (hS q hq).ne_zero)
  have hc : IsCoprime ((-1 : ℤˣ) : ℤ) ((8 * ∏ q ∈ S, q : ℕ) : ℤ) := ⟨((-1 : ℤˣ)⁻¹ : ℤˣ), 0, by simp⟩
  obtain ⟨p, hpn, hp, hps⟩ := Nat.forall_exists_prime_gt_and_zmodEq (max (S.sup id) B) h0 hc
  have h8 : (p : ℤ) ≡ ((-1 : ℤˣ) : ℤ) [ZMOD 8] :=
    hps.of_dvd (by exact_mod_cast Int.natCast_dvd_natCast.2 (dvd_mul_right 8 _))
  have : Fact p.Prime := ⟨hp⟩
  have h8' : (p : ℤ) % 8 = 7 := by
    simp only [Int.ModEq, Units.val_neg, Units.val_one] at h8
    omega
  have h2 : p ≠ 2 := by omega
  refine ⟨p, inferInstance, fun h => absurd (Finset.le_sup (f := id) h) (not_le.2 (lt_of_le_of_lt (le_max_left _ _) hpn)),
    h2, ?_, fun q hq => ?_, lt_of_le_of_lt (le_max_right _ _) hpn, by omega⟩
  · have e := legendreSym.at_neg_one h2
    rw [legendreSym, Int.cast_neg, Int.cast_one] at e
    rw [e]
    exact ZMod.χ₄_nat_three_mod_four (by omega)
  · have e := jacobi_symbol_eq_one_of_congr p q (-1) (hS q hq) h8
      (hps.of_dvd (Int.natCast_dvd_natCast.2 ((Finset.dvd_prod_of_mem _ hq).mul_left 8)))
    rwa [← jacobiSym.legendreSym.to_jacobiSym, legendreSym, Int.cast_natCast] at e

private theorem cyclotomic_class_eq_of_frobenius {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (p q : ℕ) [hp : Fact p.Prime] (γ : G ℚ Ω)
    (h : ((cycZ ℚ Ω p γ : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p])) (u : (ZMod p)ˣ) (hu : (u : ZMod p) = q) : UpperTheory.V.Chr.cls ℚ Ω p γ = u := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : NeZero ((p : ℕ) : Ω) := ⟨Nat.cast_ne_zero.mpr hp.out.ne_zero⟩
  refine (UpperTheory.V.Chr.clsFacts ℚ Ω p).2.2.1 γ u fun ζ hζ => ?_
  have hζ' : ζ ^ p ^ 1 = 1 := by rwa [pow_one]
  have h1 := cyclotomicCharacter.spec p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) ζ hζ'
  have h2 : ((cyclotomicCharacter Ω p (MulSemiringAction.toRingAut (Ω ≃ₐ[ℚ] Ω) Ω γ) : ℤ_[p]ˣ) : ℤ_[p]) = (q : ℤ_[p]) := h
  rw [h2, map_natCast, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ'] at h1
  rw [hu, ZMod.val_natCast, ← pow_eq_pow_mod _ hζ]
  exact h1

private theorem valuation_prime_lt_one_exclusive {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {p q : ℕ} (h : p.Coprime q)
    (hq : A.valuation (q : Ω) < 1) : ¬ A.valuation (p : Ω) < 1 := fun hp => by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 h
  have hv : ∀ n : ℤ, A.valuation (n : Ω) ≤ 1 := fun n => (A.valuation_le_one_iff _).mpr (intCast_mem A n)
  have h1 : A.valuation ((a : Ω) * (p : Ω) + (b : Ω) * (q : Ω)) < 1 := by
    refine Valuation.map_add_lt _ ?_ ?_
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv a)) hp
    · rw [map_mul]; exact lt_of_le_of_lt (mul_le_of_le_one_left' (hv b)) hq
  have h2 : (a : Ω) * (p : Ω) + (b : Ω) * (q : Ω) = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → Ω) hab
  rw [h2, map_one] at h1
  exact lt_irrefl _ h1

private theorem imag_quadratic_field_unique (p : ℕ) (hp : 0 < p) (K : Type) [Field K] [NumberField K] (hK : Module.finrank ℚ K = 2)
    (δ : K) (hδ : δ ^ 2 = -(p : K)) (L : Type) [Field L] [NumberField L]
    [hL : IsSplittingField ℚ L (X ^ 2 + C (p : ℚ) : ℚ[X])] : Nonempty (L ≃ₐ[ℚ] K) := by
  have hs : ((X ^ 2 + C (p : ℚ) : ℚ[X]).map (algebraMap ℚ K)).Splits := by
    have : (X ^ 2 + C (p : ℚ) : ℚ[X]).map (algebraMap ℚ K) = (X - C δ) * (X - C (-δ)) := by
      have h1 : (C (p : K) : K[X]) = -(C δ) ^ 2 := by rw [← C_pow, hδ, C_neg, neg_neg]
      simp only [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, map_natCast (algebraMap ℚ K), h1, C_neg]
      ring
    rw [this]
    exact (Splits.X_sub_C _).mul (Splits.X_sub_C _)
  let φ : L →ₐ[ℚ] K := IsSplittingField.lift L _ hs
  have hinj : Function.Injective φ := φ.toRingHom.injective
  have hle : Module.finrank ℚ L ≤ 2 := hK ▸ LinearMap.finrank_le_finrank_of_injective (f := φ.toLinearMap) hinj
  have hpos : 0 < Module.finrank ℚ L := Module.finrank_pos
  have hdeg : ((X ^ 2 + C (p : ℚ) : ℚ[X]).map (algebraMap ℚ L)).degree ≠ 0 := by
    rw [degree_map, degree_X_pow_add_C (by norm_num)]
    norm_num
  obtain ⟨s, hs'⟩ := (IsSplittingField.splits L (X ^ 2 + C (p : ℚ) : ℚ[X])).exists_eval_eq_zero hdeg
  have hne : Module.finrank ℚ L ≠ 1 := by
    intro h1
    obtain ⟨r, rfl⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.1 h1).2 s
    rw [eval_map, eval₂_at_apply, map_eq_zero] at hs'
    simp only [eval_add, eval_pow, eval_X, eval_C] at hs'
    have : (0 : ℚ) < p := by exact_mod_cast hp
    nlinarith [sq_nonneg r]
  have h2 : Module.finrank ℚ L = Module.finrank ℚ K := by omega
  have hsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (f := φ.toLinearMap) h2).1 hinj
  exact ⟨AlgEquiv.ofBijective φ ⟨hinj, hsurj⟩⟩

theorem UpperTheory.V.Cu.RankFourGaloisLemmas.quad {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] (S : Finset ℕ) (hS : ∀ q ∈ S, q.Prime) (B : ℕ) :
    ∃ (q : ℕ) (η : G ℚ Ω →* ℤˣ) (K' : IntermediateField ℚ Ω) (_ : NumberField K'), q.Prime ∧ B < q ∧ q ∉ S ∧
      IsOpen (η.ker : Set (G ℚ Ω)) ∧ K'.fixingSubgroup = η.ker ∧ Module.finrank ℚ K' = 2 ∧ IsTotallyComplex K' ∧
      discr K' = -(q : ℤ) ∧ (∀ σ : G ℚ Ω, IsCC σ → η σ = -1) ∧
      (∀ p ∈ S, ∀ A : ValuationSubring Ω, A.valuation (p : Ω) < 1 → Dec (F := ℚ) A ≤ η.ker) ∧
      (∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∃ g ∈ Ine (F := ℚ) A, η g = -1) := by
  obtain ⟨p, hp, hpS, h2, hs, hq, hB, h4⟩ := exists_prime_quadratic_conditions S hS B
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  have : IsGalois ℚ Ω := IsAlgClosure.isGalois ℚ Ω
  have : NeZero p := ⟨hp.out.ne_zero⟩
  obtain ⟨hopen, -, hspec, hcc, hine⟩ := Chr.clsFacts ℚ Ω p
  let χ : DirichletCharacter ℤ p := quadraticChar (ZMod p)
  have hval : ∀ g : G ℚ Ω, ((Chr.dirG ℚ Ω χ g : ℤˣ) : ℤ) = quadraticChar (ZMod p) (Chr.cls ℚ Ω p g : (ZMod p)ˣ) := fun g => rfl
  have hle : (Chr.cls ℚ Ω p).ker ≤ (Chr.dirG ℚ Ω χ).ker := fun g hg => by
    rw [MonoidHom.mem_ker] at hg ⊢
    rw [Chr.dirG, MonoidHom.comp_apply, hg, map_one]
  have hopn : IsOpen ((Chr.dirG ℚ Ω χ).ker : Set (G ℚ Ω)) := Subgroup.isOpen_mono hle hopen
  obtain ⟨u, hu⟩ : ∃ u : (ZMod p)ˣ, quadraticChar (ZMod p) u = -1 := by
    obtain ⟨a, ha⟩ := quadraticChar_exists_neg_one (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
    have h0 : a ≠ 0 := by
      rintro rfl
      simp at ha
    exact ⟨Units.mk0 a h0, ha⟩
  have hidx : (Chr.dirG ℚ Ω χ).ker.index = 2 := by
    obtain ⟨g, hg⟩ := (Chr.clsOnto Ω p).1 u
    have ht : (Chr.dirG ℚ Ω χ).range = ⊤ := by
      refine eq_top_iff.2 fun t _ => ?_
      rcases Int.units_eq_one_or t with rfl | rfl
      · exact one_mem _
      · exact ⟨g, Units.ext (by rw [hval, hg, hu]; rfl)⟩
    rw [Subgroup.index_ker, ht, Subgroup.card_top, Nat.card_eq_fintype_card, Fintype.card_units_int]
  have hccη : ∀ σ : G ℚ Ω, IsCC σ → Chr.dirG ℚ Ω χ σ = -1 := fun σ hσ =>
    Units.ext (by rw [hval, hcc σ hσ, Units.val_neg, Units.val_one, hs]; simp)
  obtain ⟨K', _, _, hK, dK⟩ := fixAb Ω (Chr.dirG ℚ Ω χ).ker hopn (Abelianization.commutator_subset_ker _)
  have hdeg : Module.finrank ℚ K' = 2 := dK.trans hidx
  have : IsCMField K' := (fixInf Ω K').2 (fun σ hσ e => by
    rw [hK, MonoidHom.mem_ker, hccη σ hσ] at e
    exact absurd e (by decide)) hdeg

  have hp2 : p ≠ 2 := h2
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω p
  have hst : CF.pStar p = -(p : ℤ) := by
    have : Odd (p / 2) := ⟨p / 4, by omega⟩
    rw [CF.pStar, this.neg_one_pow, neg_one_mul]
  obtain ⟨hex, hgs⟩ := CF.gauss Ω p ζ hp2 hζ
  obtain ⟨s, hs2⟩ := hex
  have hsq : s ^ 2 = -(p : Ω) := by rw [hs2, hst]; push_cast; rfl
  have hfix : ∀ σ ∈ (Chr.dirG ℚ Ω χ).ker, σ s = s := fun σ hσ => by
    have hc : Chr.cls ℚ Ω p σ = B1.cycN ℚ Ω p σ :=
      hspec σ _ fun z hz => B1.cycN_spec ℚ Ω p σ hz
    have h1 := (hgs s hs2).2 (σ : Ω →+* Ω) ((Chr.cls ℚ Ω p σ : (ZMod p)ˣ) : ZMod p).val (by
      rw [hc]; exact B1.cycN_spec ℚ Ω p σ hζ.pow_eq_one)
    have h3 : legendreSym p ((((Chr.cls ℚ Ω p σ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ℤ) = 1 := by
      rw [legendreSym, Int.cast_natCast, ZMod.natCast_zmod_val, ← hval, MonoidHom.mem_ker.1 hσ, Units.val_one]
    rw [h3] at h1
    simpa using h1
  have hsK : s ∈ K' := by
    rw [← InfiniteGalois.fixedField_fixingSubgroup K']
    exact (IntermediateField.mem_fixedField_iff _ _).2 fun σ hσ => hfix σ (hK ▸ hσ)
  let δ : K' := ⟨s, hsK⟩
  have hδ : δ ^ 2 = -(p : K') := Subtype.ext (by
    rw [IntermediateField.coe_pow]
    push_cast
    exact hsq)
  obtain ⟨hD, -, -, -⟩ := UpperTheory.V.HV.kstar p hp.out h4
  have hL : Polynomial.IsSplittingField ℚ (Kstar p) (Polynomial.X ^ 2 + Polynomial.C (p : ℚ)) := by
    convert Polynomial.IsSplittingField.splittingField (Polynomial.X ^ 2 + Polynomial.C (p : ℚ))
    · rfl
    · rfl
    · exact heq_of_eq (Subsingleton.elim (α := Algebra ℚ (Kstar p)) _ _)
  obtain ⟨e⟩ := imag_quadratic_field_unique p hp.out.pos K' hdeg δ hδ (Kstar p)
  refine ⟨p, Chr.dirG ℚ Ω χ, K', inferInstance, hp.out, hB, hpS, hopn, hK, hdeg, inferInstance,
    (discr_eq_discr_of_algEquiv _ e).symm.trans hD, hccη, fun q hqS A hA => ?_, fun A hA => ?_⟩
  · have hne : p ≠ q := fun h => hpS (h ▸ hqS)
    have hc : p.Coprime q := (Nat.coprime_primes hp.out (hS q hqS)).2 hne
    obtain ⟨-, -, γ, -, hDec, hγ⟩ := Chr.decCyc Ω q A (hS q hqS) hA
    refine hDec.trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ((hine A (valuation_prime_lt_one_exclusive A hc hA)).trans hle))
      (Subgroup.isClosed_of_isOpen _ hopn))
    rw [Subgroup.zpowers_le, MonoidHom.mem_ker]
    refine Units.ext ?_
    rw [hval, cyclotomic_class_eq_of_frobenius p q γ (hγ p hne) (ZMod.unitOfCoprime q hc.symm) rfl, ZMod.coe_unitOfCoprime, hq q hqS, Units.val_one]
  · have hm : u ∈ (proj p p).range := by
      rw [(projFacts p p hp.out).2.2.2.2.2.1, MonoidHom.mem_ker]
      have h1 : ordCompl[p] p = 1 := by
        rw [hp.out.factorization_self, pow_one, Nat.div_self hp.out.pos]
      have : Subsingleton (ZMod (ordCompl[p] p)) := by rw [h1]; infer_instance
      exact Units.ext (Subsingleton.elim _ _)
    rw [← (compIne Ω p p hp.out A hA).1] at hm
    obtain ⟨g, hg, hgu⟩ := hm
    exact ⟨g, hg, Units.ext (by rw [hval, hgu, hu]; rfl)⟩

private theorem unit_pow_two_pow_eq_one (n : ℕ) (u : (ZMod (2 ^ n))ˣ) : u ^ 2 ^ n = 1 := by
  have h : Nat.totient (2 ^ n) ∣ 2 ^ n := by
    rcases n with _ | n
    · simp
    · rw [Nat.totient_prime_pow_succ Nat.prime_two]
      simpa using pow_dvd_pow 2 (Nat.le_succ n)
  exact orderOf_dvd_iff_pow_eq_one.1 ((orderOf_dvd_of_pow_eq_one (ZMod.pow_totient u)).trans h)

private theorem dirichlet_unit_pow_order_eq_one {O : Type} [CommRing O] {N : ℕ} (ψ : DirichletCharacter O N) (a : (ZMod N)ˣ) :
    ψ.toUnitHom a ^ orderOf ψ = 1 := by
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, MulChar.coe_toUnitHom, ← MulChar.pow_apply_coe, pow_orderOf_eq_one,
    MulChar.one_apply_coe, Units.val_one]

private theorem dirichlet_galois_char_unramified {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {O : Type} [CommRing O] {N : ℕ} [NeZero N]
    (χ : DirichletCharacter O N) {A : ValuationSubring Ω} {v : ℕ} (hA : A.valuation (v : Ω) < 1) (hN : v.Coprime N)
    {g : G ℚ Ω} (hg : g ∈ Ine (F := ℚ) A) : UpperTheory.V.Chr.dirG ℚ Ω χ g = 1 := by
  have h1 : ¬ A.valuation (N : Ω) < 1 := (UpperTheory.V.ML.placeBasic Ω).2.2.2.1 A v N hN hA
  rw [UpperTheory.V.Chr.dirG, MonoidHom.comp_apply, MonoidHom.mem_ker.1 ((UpperTheory.V.Chr.clsFacts ℚ Ω N).2.2.2.2 A h1 hg), map_one]

theorem UpperTheory.V.Cu.RankFourGaloisLemmas.odd :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
      ∃ (g : G ℚ Ω) (m : ℕ), Odd m ∧ l.Coprime m ∧ D.om g = 1 ∧ D.ξ g = 1 ∧ D.ψ g ^ m = 1 ∧ D.ψ g ≠ 1 := by
  intro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, hB, he, het, hX, ⟨hlB, hle, hodd, hne⟩, hO⟩
  obtain ⟨-, hψ, -, _, ξ', ξ₀, -, -, hord, hξ⟩ := hO
  have lp : l.Prime := hl.out
  obtain ⟨-, -, -, hpN, hb⟩ := bchiFacts h t hB
  obtain ⟨-, hlo, -, -, -, hlp, -, hb⟩ := hb l lp hG.l_odd hlB
  obtain ⟨-, -, hlN⟩ := hb e he het hle
  obtain ⟨-, ⟨pp, -, pc⟩, -⟩ := UpperTheory.V.pK_pOne_prime_conditions h.chi
  have hdo : orderOf ψ ∣ h.o :=
    (((hostOdd h c.O ψ (h.mem_X.1 hX).1).1 hodd).1).trans (Nat.ordCompl_dvd _ _)
  have hlm : l.Coprime (orderOf ψ) := lp.coprime_iff_not_dvd.2 fun hd => hlo (hd.trans hdo)
  haveI : NeZero l := ⟨lp.ne_zero⟩
  generalize UpperTheory.V.pOne h.chi = p at *
  generalize h.nIII l ψ = n at *
  haveI : NeZero p := ⟨pp.ne_zero⟩
  have hom : ∀ g, Chr.cls ℚ Ω l g = 1 → D.om g = 1 := by
    have hT : IsOmT c D.om := ⟨hG.om_pow, fun σ => by
      have := hG.om_bar σ
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub]
      exact sub_eq_zero.2 this⟩
    intro g hg
    have hk := ((omT Ω l c).2 D.om hT).2.1
    rw [← MonoidHom.mem_ker, hk]
    exact hg
  obtain ⟨a, ha⟩ : ∃ a : (ZMod h.N)ˣ, ψ.toUnitHom a ≠ 1 := by
    by_contra hc
    push Not at hc
    apply hne
    ext a
    rw [MulChar.one_apply_coe, ← MulChar.coe_toUnitHom, hc a, Units.val_one]
  haveI : NeZero (l * p) := ⟨mul_ne_zero lp.ne_zero pp.ne_zero⟩
  have c1 : h.N.Coprime (l * p) :=
    Nat.Coprime.mul_right (lp.coprime_iff_not_dvd.2 hlN).symm (pp.coprime_iff_not_dvd.2 hpN).symm
  obtain ⟨u, hu, hu'⟩ := UpperTheory.V.Ws.large₂.clsIndep (Ω := Ω) h.N (l * p) c1 a
  have h1 : ψ.toUnitHom a ^ 2 ^ n ≠ 1 := by
    intro h2
    apply ha
    have hc : (2 ^ n).Coprime (orderOf ψ) := (Nat.coprime_two_left.2 hodd).pow_left _
    have := pow_gcd_eq_one.2 ⟨h2, dirichlet_unit_pow_order_eq_one ψ a⟩
    rwa [hc.gcd_eq_one, pow_one] at this
  have e1 : D.ξ (u ^ 2 ^ n) = 1 := by
    have f1 : Chr.cls ℚ Ω p (u ^ 2 ^ n) = 1 := by
      rw [map_pow, hu' p (dvd_mul_left _ _), one_pow]
    have f2 : Chr.cls ℚ Ω (2 ^ n) (u ^ 2 ^ n) = 1 := by
      rw [map_pow, unit_pow_two_pow_eq_one]
    rw [hξ, MonoidHom.mul_apply, Chr.dirG, Chr.dirG, MonoidHom.comp_apply, MonoidHom.comp_apply, f1, f2, map_one, map_one,
      mul_one]
  have e2 : D.ψ (u ^ 2 ^ n) = ψ.toUnitHom a ^ 2 ^ n := by
    rw [hψ, Chr.dirG, MonoidHom.comp_apply, map_pow, hu, map_pow]
  refine ⟨u ^ 2 ^ n, orderOf ψ, hodd, hlm, hom _ ?_, e1, ?_, ?_⟩
  · rw [map_pow, hu' l (dvd_mul_right _ _), one_pow]
  · rw [e2, ← pow_mul, mul_comm, pow_mul, dirichlet_unit_pow_order_eq_one, one_pow]
  · rw [e2]
    exact h1

theorem UpperTheory.V.Cu.RankFourGaloisLemmas.unr :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), Ctx3 D →
      ∃ B : ℕ, ∀ q : ℕ, q.Prime → B < q → ∀ A : ValuationSubring Ω, A.valuation (q : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A,
        D.ξ g = 1 ∧ D.ψ g = 1 ∧ D.om g = 1 := by
  rintro Ω _ _ _ l hl c D ⟨hG, h, t, e, ψ, hB, he0, het, hX, ⟨c1, c2, c3, c4⟩, he, hψ, hS, _, ξ', ξ₀, -, -, -, hξ⟩
  have hlp : l.Prime := hl.out
  obtain ⟨-, ⟨p1, -, -⟩, -⟩ := UpperTheory.V.pK_pOne_prime_conditions h.chi
  have hom : IsOmT c D.om := ⟨hG.om_pow, fun g => (Ideal.Quotient.eq).1 (hG.om_bar g)⟩
  obtain ⟨-, -, -, -, -, o6, -, -⟩ := (omT Ω l c).2 D.om hom
  have hpos : 0 < h.N * l * UpperTheory.V.pOne h.chi * 2 :=
    Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pos_of_ne_zero (NeZero.ne h.N)) hlp.pos) p1.pos) two_pos
  refine ⟨h.N * l * UpperTheory.V.pOne h.chi * 2, fun q hq hBq A hA g hg => ?_⟩
  have key : ∀ x : ℕ, x ∣ h.N * l * UpperTheory.V.pOne h.chi * 2 → q.Coprime x := fun x hx =>
    (Nat.Prime.coprime_iff_not_dvd hq).2 fun hd => absurd (Nat.le_of_dvd hpos (hd.trans hx)) (by omega)
  have kN : q.Coprime h.N := key _ (((dvd_mul_right _ _).mul_right _).mul_right _)
  have kl : q.Coprime l := key _ (((dvd_mul_left _ _).mul_right _).mul_right _)
  have kp : q.Coprime (UpperTheory.V.pOne h.chi) := key _ ((dvd_mul_left _ _).mul_right _)
  have k2 : q.Coprime 2 := key _ (dvd_mul_left _ _)
  refine ⟨?_, ?_, ?_⟩
  · rw [hξ, MonoidHom.mul_apply, dirichlet_galois_char_unramified ξ₀ hA kp hg, dirichlet_galois_char_unramified ξ' hA (k2.pow_right _) hg, mul_one]
  · rw [hψ]
    exact dirichlet_galois_char_unramified ψ hA kN hg
  · exact o6 A ((UpperTheory.V.ML.placeBasic Ω).2.2.2.1 A q l kl hA) hg

open UpperTheory.V.Cu in
theorem UpperTheory.V.Cu.existsTensorSeedTower_holds : ExistsTensorFactorTower := by
  intro Ω _ _ _ l hl c D hC pr hlab
  have hD := hC.1
  obtain ⟨h5, he, hSb, ⟨m, hmo, hlm, hm⟩, hIl⟩ := large₂.host3 D hC
  have hom : IsOmT c D.om := ⟨hD.om_pow, fun g => (Ideal.Quotient.eq).1 (hD.om_bar g)⟩
  obtain ⟨-, -, -, o4, -, o6, o7, -⟩ := (omT Ω l c).2 D.om hom
  have hl2 : l.Coprime 2 := (Nat.coprime_primes hl.out Nat.prime_two).2 hD.l_odd
  have hl1 : l.Coprime (l - 1) := (Nat.coprime_self_sub_right hl.out.one_le).2 (Nat.coprime_one_right _)
  have h2e : ∀ g, D.om (g ^ 2) ^ D.e = 1 := fun g => by
    obtain ⟨k, hk⟩ := he
    rw [map_pow, ← pow_mul, hk, pow_mul, ← MonoidHom.pow_apply, hD.om_pow, MonoidHom.one_apply, one_pow]
  have hm1 : (-1 : (ResidueField c.O)ˣ) ≠ 1 := by
    intro h
    have h' : ((-1 : (ResidueField c.O)ˣ) : ResidueField c.O) = 1 := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    have e1 := large₂.redOne c 2 hl2 (-1) (by simp) (by rw [Units.val_neg, Units.val_one, map_neg, map_one]; exact h')
    have h'' : ((-1 : c.O) : PadicAlgCl l) = ((1 : c.O) : PadicAlgCl l) := congrArg _ (congrArg Units.val e1)
    norm_num at h''

  obtain ⟨B, hB⟩ := RankFourGaloisLemmas.unr D hC
  obtain ⟨q, η, K', _, hq, hBq, hqS, hηo, hK'fix, hK'2, hK'c, hK'd, hηcc, hηS, hηram⟩ :=
    RankFourGaloisLemmas.quad (Ω := Ω) D.S hD.S_prime (B + l)
  let ηc : G ℚ Ω →* c.Oˣ := (Units.map (Int.castRingHom c.O).toMonoidHom).comp η
  have hηc : ∀ g, ηc g = 1 ∨ ηc g = -1 := fun g => by
    rcases Int.units_eq_one_or (η g) with h | h
    · left; simp [ηc, h]
    · right; ext; simp [ηc, h]
  let H : Subgroup (G ℚ Ω) := (D.ξ * ηc⁻¹).ker ⊓ ((bU c).comp (D.Psi * D.ψ⁻¹)).ker
  have memH : ∀ g, g ∈ H ↔ D.ξ g = ηc g ∧ bU c (D.Psi g) = bU c (D.ψ g) := fun g => by
    simp only [H, Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, map_mul,
      map_inv, mul_inv_eq_one]
  have hopen : IsOpen (H : Set (G ℚ Ω)) := by
    refine Subgroup.isOpen_mono (H₁ := D.ξ.ker ⊓ η.ker ⊓ D.ψ.ker ⊓ D.om.ker) ?_
      (((hD.xi_open.inter hηo).inter hD.psi_open).inter o4)
    rintro g ⟨⟨⟨a1, a2⟩, a3⟩, a4⟩
    refine (memH g).2 ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker.1 a1]
      simp [ηc, MonoidHom.mem_ker.1 a2]
    · rw [reduction_psi_eq_omega_pow_case_three D hD, MonoidHom.mem_ker.1 a4, MonoidHom.mem_ker.1 a3]
      simp
  have hcomm : commutator (G ℚ Ω) ≤ H :=
    le_inf (Abelianization.commutator_subset_ker _) (Abelianization.commutator_subset_ker _)
  have hψcc : D.ψ D.cc = 1 := by
    have h1 : D.ψ D.cc ^ 2 = 1 := by rw [← map_pow, pow_two, complex_conjugation_sq hD.isCC, map_one]
    have h2 : D.ψ D.cc ^ m = 1 := by rw [← MonoidHom.pow_apply, hm, MonoidHom.one_apply]
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rwa [((Nat.coprime_two_left).2 hmo).gcd_eq_one, pow_one] at this
  have hcc : D.cc ∈ H := (memH _).2 ⟨by
      rw [hD.xi_odd]
      ext
      simp [ηc, hηcc _ hD.isCC], by rw [hD.Psi_even, hψcc]⟩
  have hsq : ∀ A : ValuationSubring Ω, A.valuation (l : Ω) < 1 → ∀ g ∈ Ine (F := ℚ) A, g ^ 2 ∈ H := fun A hA g hg => by
    obtain ⟨a1, a2⟩ := hIl A hA (pow_mem hg 2)
    refine (memH _).2 ⟨?_, ?_⟩
    · rw [MonoidHom.mem_ker.1 a1]
      ext
      simp [ηc, Int.units_sq]
    · rw [reduction_psi_eq_omega_pow_case_three D hD, ← map_pow _ _ D.e, h2e, MonoidHom.mem_ker.1 a2]
      simp
  obtain ⟨K, F, _, _, _, _, _, J, hK, hev, hJS, hJ2, hJK, hFH, hFK, hunr⟩ :=
    exists_cm_and_real_fields (fun p hp => ⟨_, hD.pl_over p hp⟩) (insert q D.S)
      (fun p hp => (Finset.mem_insert.1 hp).elim (fun e => e ▸ hq) (hD.S_prime p)) H hopen hcomm D.cc hD.isCC hcc
  have hL : ∀ g, g ∈ H → g ∈ J → ∃ g' : G F Ω, resQ F g' = g ∧ resQ F g' ∈ K.fixingSubgroup := fun g a b => by
    have h : g ∈ F.fixingSubgroup ⊓ K.fixingSubgroup := hFK ▸ ⟨a, b⟩
    obtain ⟨g', rfl⟩ := exists_lift_of_mem_fixing_case_three h.1
    exact ⟨g', rfl, h.2⟩

  obtain ⟨g1, i1, x1, p1, w1⟩ := large₂.eltTwo D hC
  obtain ⟨g2, m', hm', hlm', w2, x2, y2, n2⟩ := RankFourGaloisLemmas.odd D hC
  obtain ⟨g5, i5, e5⟩ := hηram (D.pl q) (hD.pl_over q hq)
  obtain ⟨x5, p5, w5⟩ := hB q hq (by omega) (D.pl q) (hD.pl_over q hq) g5 i5
  have hη1 : η g1 = 1 :=
    hηS 2 hD.two_mem _ (hD.pl_over 2 Nat.prime_two) (Ine_le_Dec _ i1)
  have hx : D.ξ (g1 * g5 * g2 ^ 2) = -1 := by rw [map_mul, map_mul, map_pow, x1, x5, x2]; simp
  have hw : D.om (g1 * g5 * g2 ^ 2) = 1 := by rw [map_mul, map_mul, map_pow, w1, w5, w2]; simp
  have hp : D.ψ (g1 * g5 * g2 ^ 2) = D.ψ g2 ^ 2 := by rw [map_mul, map_mul, map_pow, p1, p5]; simp
  have hηx : ηc (g1 * g5 * g2 ^ 2) = -1 := by
    ext
    simp [ηc, map_mul, hη1, e5, Int.units_sq]
  obtain ⟨g0, hg0, hg0K⟩ := hL (g1 * g5 * g2 ^ 2) ((memH _).2 ⟨hx.trans hηx.symm, by rw [reduction_psi_eq_omega_pow_case_three D hD, hw]; simp⟩)
    (J.mul_mem (J.mul_mem (hJS 2 (Finset.mem_insert_of_mem hD.two_mem) _ (hD.pl_over 2 Nat.prime_two) (Ine_le_Dec _ i1))
      (hJS q (Finset.mem_insert_self _ _) _ (hD.pl_over q hq) (Ine_le_Dec _ i5))) (hJ2 g2))

  obtain ⟨g3, i3, w3⟩ : ∃ g ∈ D.Ip l, D.om (g ^ 2) ≠ 1 := by
    by_contra hc
    push Not at hc
    have := Nat.le_of_dvd two_pos (o7 _ (hD.pl_over l hl.out) 2 fun g hg => by
      rw [MonoidHom.mem_ker, MonoidHom.pow_apply, ← map_pow]; exact hc g hg)
    omega
  obtain ⟨g4, hg4, hg4K⟩ := hL (g3 ^ 2) (hsq _ (hD.pl_over l hl.out) g3 i3) (hJ2 g3)
  obtain ⟨T, rfl, rfl, rfl, hT0⟩ := mkTower D hD pr K F hK
    (fun A hA => (hJS l (Finset.mem_insert_of_mem hD.l_mem) A hA).trans hJK) g0

  have hrb : ∀ (w : ℤ × ℤ) (g : G T.F Ω), T.rb w g =
      ((bU c (D.ξ (resQ T.F g)) ^ w.1 * (bU c (D.ψ (resQ T.F g)) ^ sgnP T.pr) ^ w.2 : (ResidueField c.O)ˣ) : ResidueField c.O) := by
    intro w g
    rw [residual_root_character_explicit, reduction_alpha_eq_xi_case_three D hD, ((memH _).1 (hFH (restrict_mem_fixing_subgroup_case_three g))).2]
  set y : (ResidueField c.O)ˣ := bU c (D.ψ g2) ^ 2 with hy
  set z : (ResidueField c.O)ˣ := y ^ sgnP T.pr with hz
  have hξ0 : bU c (D.ξ (resQ T.F g0)) = -1 := by rw [hg0, hx]; ext; simp
  have hψ0 : bU c (D.ψ (resQ T.F g0)) = y := by rw [hg0, hp, map_pow]
  have hym : y ^ m' = 1 := by
    rw [hy, ← pow_mul, ← map_pow, mul_comm, pow_mul, y2, one_pow, map_one]
  have hy1 : y ≠ 1 := by
    intro e
    have e1 : D.ψ g2 ^ 2 = 1 := large₂.redOne c m' hlm' _ (by rw [← pow_mul, mul_comm, pow_mul, y2, one_pow])
      (by have := congrArg Units.val e; rw [hy, ← map_pow] at this; exact this)
    apply n2
    have := pow_gcd_eq_one.2 ⟨e1, y2⟩
    rwa [((Nat.coprime_two_left).2 hm').gcd_eq_one, pow_one] at this
  have hs : sgnP T.pr = 1 ∨ sgnP T.pr = -1 := by unfold sgnP; split_ifs <;> simp
  have hzm : z ^ m' = 1 := by rw [hz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hym, one_zpow]
  have hz1 : z ≠ 1 := by
    rcases hs with h | h <;> rw [hz, h] <;> simpa using hy1
  have hzn : z ≠ -1 := odd_order_unit_ne_neg_one hm' hzm hm1
  have hrb0 : ∀ w, T.rb w g0 = (((-1 : (ResidueField c.O)ˣ) ^ w.1 * z ^ w.2 : (ResidueField c.O)ˣ) : ResidueField c.O) := fun w => by
    rw [hrb, hξ0, hψ0]
  have hdist : ∀ i j : Fin 4, bU c (chi D T.pr i (resQ T.F g0)) = bU c (chi D T.pr j (resQ T.F g0)) → i = j := by
    intro i j e
    rw [reduced_character_quotient_explicit D T.pr _ i, reduced_character_quotient_explicit D T.pr _ j, mul_right_inj, inv_inj, reduction_alpha_eq_xi_case_three D hD, ((memH _).1 (hFH (restrict_mem_fixing_subgroup_case_three g0))).2, hξ0,
      hψ0] at e
    refine distinct_four_eigenvalues_injective hm1 hz1 hzn i j ?_
    have e' : (![1, -1, z, -1 * z] : Fin 4 → (ResidueField c.O)ˣ) i = ![1, -1, z, -1 * z] j := e
    simpa only [neg_one_mul] using e'
  have hxK : ∀ g : G T.F Ω, resQ T.F g ∈ K'.fixingSubgroup ↔ η (resQ T.F g) = 1 := fun g => by
    rw [hK'fix, MonoidHom.mem_ker]
  have hξF : ∀ g : G T.F Ω, D.ξ (resQ T.F g) = ηc (resQ T.F g) := fun g => ((memH _).1 (hFH (restrict_mem_fixing_subgroup_case_three g))).1
  refine ⟨T, rfl, ⟨hlab, hev, fun A g hg => hunr A ⟨restrict_inertia_mem_case_three hg, restrict_mem_fixing_subgroup_case_three g⟩,
    fun p hp A hA => (hJS p (Finset.mem_insert_of_mem hp) A hA).trans hJK, fun w => ⟨g4, hg4K, ?_⟩,
    fun w hw => ⟨g0, hg0K, ?_⟩, fun η' _ hη' h => ?_, ⟨wTh, by decide, fun n h0 h4 => ⟨g0, hg0K, ?_⟩⟩,
    fun A hA g hg hr => ?_, ⟨m, hlm, fun g _ => ?_⟩, fun A hA g hg => ?_, fun i j hij e => ?_,
    UpperTheory.V.Keep.loc3 D hD h5 T fun A hA g hg =>
      (show g ^ 2 ∈ T.F.fixingSubgroup ⊓ T.K.fixingSubgroup from hFK ▸ ⟨hsq A hA g hg, hJ2 g⟩).1⟩,
    ⟨h5, hSb, ⟨m, hlm, hm⟩, ⟨K', inferInstance, ⟨hK'2, hK'c, ?_, ?_, fun p hp A hA => (hηS p hp A hA).trans hK'fix.ge, ?_, ?_⟩⟩⟩, fun A hA g hg => ⟨2, hl2, ?_⟩⟩
  · obtain ⟨a1, a2⟩ := hIl _ (hD.pl_over l hl.out) (pow_mem i3 2)
    rw [hrb, hg4, MonoidHom.mem_ker.1 a1, MonoidHom.mem_ker.1 a2]
    simp only [map_one, one_zpow, one_mul]
    exact fun e => w3 (large₂.redOne c (l - 1) hl1 _ (by rw [← MonoidHom.pow_apply, hD.om_pow]; rfl) e.symm)
  · rw [hrb0, Ne, Units.val_eq_one]
    exact root_character_ne_one hm1 hz1 hzn w hw
  · obtain ⟨j, hj⟩ := h 0
    have h1 := hj ⟨g0, hg0K⟩
    rw [hη' ⟨g0, hg0K⟩ (by show D.om (resQ T.F g0) = 1; rw [hg0, hw]), Units.val_one, one_mul] at h1
    obtain rfl : 0 = j := hdist 0 j (Units.ext h1)
    ext g
    exact (mul_eq_right₀ (bU c (chi D T.pr 0 (resQ T.F g))).ne_zero).1 (hj g)
  · rw [hrb0, ← Units.val_pow_eq_pow_val, Ne, Units.val_eq_one]
    have := neg_pow_ne_one_of_odd_order hm' hzm hz1 hm1 h0 h4
    simpa [wTh, neg_one_mul] using this
  · have h1 := ((residual_rep_trivial_iff_case_three D _).1 hr).2
    rw [reduction_psi_eq_omega_pow_case_three D hD, MonoidHom.mem_ker.1 (o6 A (hA l (Finset.mem_singleton_self l)) (restrict_inertia_mem_case_three hg)), map_one, one_pow, one_mul] at h1
    exact large₂.redOne c m hlm _ (by rw [← MonoidHom.pow_apply, hm]; rfl) (congrArg Units.val h1)
  · rw [← MonoidHom.pow_apply, hm]; rfl
  · have a1 := MonoidHom.mem_ker.1 (hIl A hA (restrict_inertia_mem_case_three hg)).1
    have a2 := MonoidHom.mem_ker.1 (hIl A hA (restrict_inertia_mem_case_three hg)).2
    refine (residual_rep_trivial_iff_case_three D _).2 ⟨by rw [reduction_alpha_eq_xi_case_three D hD, a1, map_one], ?_⟩
    rw [((memH _).1 (hFH (restrict_mem_fixing_subgroup_case_three g))).2, a2, map_one]
  · rw [hT0] at e
    exact hij (hdist i j (Units.ext e))
  · rw [hK'd, Int.dvd_neg, Int.natCast_dvd_natCast]
    intro hd
    have := (Nat.prime_dvd_prime_iff_eq hl.out hq).1 hd
    omega
  · intro A hA
    rw [hK'fix]
    exact hηS l hD.l_mem A hA
  · intro g hg
    have h1 : ηc (resQ T.F g) = 1 := by
      show Units.map _ (η (resQ T.F g)) = 1
      rw [(hxK g).1 hg, map_one]
    rw [hrb, hξF g, h1]
    simp [wAl]
  · intro g hg
    have h1 : η (resQ T.F g) = -1 := (Int.units_eq_one_or _).resolve_left fun e => hg ((hxK g).2 e)
    have h1' : ηc (resQ T.F g) = -1 := by
      show Units.map _ (η (resQ T.F g)) = -1
      rw [h1]
      ext
      simp
    rw [hrb, hξF g, h1']
    simp [wAl]
  · have h : g ^ 2 ∈ T.F.fixingSubgroup ⊓ T.K.fixingSubgroup := hFK ▸ ⟨hsq A hA g hg, hJ2 g⟩
    exact h.1
