import Formalism.SharpRestriction.LevelLetterCocycles.FirstFrameStepImplication
import Formalism.SharpRestriction.LevelLetterCocycles.MapCompZero
import Formalism.SharpRestriction.LevelLetterCocycles.DvrLatticeRank.SumIocPadicValNatAddFactorial

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

theorem kapPiPf_natCast_le {a b : ℕ} (h : ((a : ℕ) : WithTop ℚ) ≤ ((b : ℕ) : WithTop ℚ)) : a ≤ b := by
  have h' : ((a : ℚ) : WithTop ℚ) ≤ ((b : ℚ) : WithTop ℚ) := by
    simpa only [WithTop.coe_natCast] using h
  exact_mod_cast WithTop.coe_le_coe.mp h'

theorem kapPiPf_sum_biUnion_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (t : ι → Finset ℤ)
    (f : ℤ → ℕ) : ∑ i ∈ s.biUnion t, f i ≤ ∑ τ ∈ s, ∑ i ∈ t τ, f i := by
  refine Finset.induction_on s (by simp) ?_
  intro a s ha ih
  rw [Finset.biUnion_insert, Finset.sum_insert ha]
  have h1 := Finset.sum_union_inter (s₁ := t a) (s₂ := s.biUnion t) (f := f)
  omega

private lemma sum_padicValNat_eq_padicValNat_descFactorial (p : ℕ) [Fact p.Prime] (m S : ℕ) :
    ∑ j ∈ Finset.range S, padicValNat p (m + 1 + j) = padicValNat p ((m + S).descFactorial S) := by
  induction S with
  | zero => simp
  | succ S ih =>
    rw [Finset.sum_range_succ, ih, show m + (S + 1) = (m + S) + 1 by omega,
      Nat.succ_descFactorial_succ,
      padicValNat.mul (by omega) (fun h => by rw [Nat.descFactorial_eq_zero_iff_lt] at h; omega),
      show m + 1 + S = m + S + 1 by omega]
    omega

private lemma padicValNat_descFactorial_le_factorial_add_log (p : ℕ) [hp : Fact p.Prime] (m S : ℕ) :
    padicValNat p ((m + S).descFactorial S) ≤ padicValNat p S.factorial + Nat.log p (m + S) := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    padicValNat.mul (Nat.factorial_ne_zero S) (Nat.choose_pos (by omega)).ne']
  have h := Nat.factorization_choose_le_log (p := p) (n := m + S) (k := S)
  rw [Nat.factorization_def _ hp.out] at h
  omega

private lemma sum_one_add_padicValNat_image_le (p : ℕ) [Fact p.Prime] (S h' m : ℕ) (e : ℕ → ℤ)
    (he : ∀ j, (e j).natAbs = m + 1 + j) (hm : m + S ≤ h') :
    ∑ i ∈ (Finset.range S).image e, (1 + padicValNat p i.natAbs) ≤
      S + padicValNat p S.factorial + Nat.log p h' := by
  rw [Finset.sum_image (by
    intro x _ y _ hxy
    have h1 := he x
    have h2 := he y
    rw [hxy] at h1
    omega)]
  simp only [he]
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul, mul_one,
    sum_padicValNat_eq_padicValNat_descFactorial]
  have h1 := padicValNat_descFactorial_le_factorial_add_log p m S
  have h2 : Nat.log p (m + S) ≤ Nat.log p h' := Nat.log_mono_right hm
  omega

theorem kapPiPf_sum {ι : Type*} [Fintype ι] (p : ℕ) [Fact p.Prime] (up : ι → Bool) (b : ι → ℕ)
    (S h' : ℕ) (hb : ∀ τ, 0 < b τ) (hbh : ∀ τ, b τ + S ≤ h') (Ω : Finset ℤ)
    (hΩ : ∀ i ∈ Ω, ∃ τ, (up τ = true ∧ -((b τ : ℤ) + S) ≤ i ∧ i < -(b τ : ℤ)) ∨
      (up τ = false ∧ (b τ : ℤ) ≤ i ∧ i < b τ + S)) :
    ∑ i ∈ Ω, (1 + padicValNat p i.natAbs) ≤
      Fintype.card ι * (S + padicValNat p S.factorial + Nat.log p h') := by
  classical
  let e : ι → ℕ → ℤ := fun τ j =>
    if up τ = true then -(((b τ + 1 + j : ℕ)) : ℤ) else ((b τ + j : ℕ) : ℤ)
  have hsub : Ω ⊆ (Finset.univ : Finset ι).biUnion (fun τ => (Finset.range S).image (e τ)) := by
    intro i hi
    obtain ⟨τ, hτ⟩ := hΩ i hi
    rw [Finset.mem_biUnion]
    refine ⟨τ, Finset.mem_univ _, ?_⟩
    rw [Finset.mem_image]
    rcases hτ with ⟨hu, h1, h2⟩ | ⟨hu, h1, h2⟩
    · refine ⟨(-i - (b τ : ℤ) - 1).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [e, hu, ↓reduceIte]
      push_cast
      omega
    · refine ⟨(i - (b τ : ℤ)).toNat, Finset.mem_range.mpr (by omega), ?_⟩
      simp only [e, hu, Bool.false_eq_true, ↓reduceIte]
      push_cast
      omega
  have hwin : ∀ τ, ∑ i ∈ (Finset.range S).image (e τ), (1 + padicValNat p i.natAbs) ≤
      S + padicValNat p S.factorial + Nat.log p h' := by
    intro τ
    have hb0 := hb τ
    have hbh0 := hbh τ
    refine sum_one_add_padicValNat_image_le p S h' (if up τ = true then b τ else b τ - 1) (e τ) ?_ ?_
    · intro j
      simp only [e]
      split_ifs <;> simp <;> omega
    · split_ifs <;> omega
  calc ∑ i ∈ Ω, (1 + padicValNat p i.natAbs)
      ≤ ∑ i ∈ (Finset.univ : Finset ι).biUnion (fun τ => (Finset.range S).image (e τ)),
          (1 + padicValNat p i.natAbs) := Finset.sum_le_sum_of_subset hsub
    _ ≤ ∑ τ : ι, ∑ i ∈ (Finset.range S).image (e τ), (1 + padicValNat p i.natAbs) :=
        kapPiPf_sum_biUnion_le _ _ _
    _ ≤ ∑ _τ : ι, (S + padicValNat p S.factorial + Nat.log p h') :=
        Finset.sum_le_sum (fun τ _ => hwin τ)
    _ = Fintype.card ι * (S + padicValNat p S.factorial + Nat.log p h') := by
        rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]

section KapPiPfLocal

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem kapPiPf_card (W : LocWach PD LL O v n) [FiniteDimensional K₀ K] (c : ZMod n) :
    Nat.card {τ : K →ₐ[Qp] LL // Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c} ≤ finrank K₀ K := by
  classical
  letI : Algebra K₀ LL := (W.emb c).toRingHom.toAlgebra
  let F : {τ : K →ₐ[Qp] LL // Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c} → (K →ₐ[K₀] LL) := fun τ =>
    { (τ.1 : K →+* LL) with
      commutes' := fun x => by
        have hx := congrArg (fun f : K₀ →ₐ[Qp] LL => f x) τ.2
        exact hx }
  have hF : Function.Injective F := by
    intro a b hab
    apply Subtype.ext
    apply AlgHom.ext
    intro x
    exact congrArg (fun f : K →ₐ[K₀] LL => f x) hab
  have hli := linearIndependent_toLinearMap K₀ K LL
  haveI : Finite (K →ₐ[K₀] LL) := hli.finite
  letI := Fintype.ofFinite (K →ₐ[K₀] LL)
  have h2 : Fintype.card (K →ₐ[K₀] LL) ≤ finrank K₀ K := by
    have h3 := hli.fintype_card_le_finrank
    rwa [Module.finrank_linearMap_self] at h3
  calc Nat.card {τ : K →ₐ[Qp] LL // Formalism.MainNotions.DeltaInvariantLattices.OverLetter W τ c}
      ≤ Nat.card (K →ₐ[K₀] LL) := Nat.card_le_card_of_injective F hF
    _ = Fintype.card (K →ₐ[K₀] LL) := Nat.card_eq_fintype_card
    _ ≤ finrank K₀ K := h2

end KapPiPfLocal

theorem kapPiPf_uU {l : ℕ} [Fact l.Prime] (P : LocPrime l) (H : LocHW l P) (K LL : FinExt l)
    (hg : Good K 1 LL) :
    ∃ χ : ℤ_[l]ˣ, ((χ : ℤ_[l]) - 1).valuation = 1 ∧ (χ : ℤ_[l]) - 1 ≠ 0 ∧
      ∀ k : ℤ, ((((Formalism.MainNotions.DeltaInvariantLattices.uU (H.W K 1 LL hg)) ^ k : (↥(OL LL))ˣ) : ↥(OL LL))) =
        algebraMap ℤ_[l] ↥(OL LL) ((χ ^ k : ℤ_[l]ˣ) : ℤ_[l]) := by
  have hs : (H.W K 1 LL hg).s = 1 := H.W_s K 1 LL hg
  have hvunit : ∀ u : ℤ_[l]ˣ, P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) = 0 := by
    intro u
    have h1 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) :=
      (P.v_O LL _).2 ((OL LL).algebraMap_mem _)
    have h2 : 0 ≤ P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) :=
      (P.v_O LL _).2 ((OL LL).algebraMap_mem _)
    have h3 : P.v LL (algebraMap ℤ_[l] ↥LL.1 (u : ℤ_[l])) +
        P.v LL (algebraMap ℤ_[l] ↥LL.1 ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l])) = 0 := by
      rw [← AddValuation.map_mul, ← map_mul, Units.mul_inv, map_one, AddValuation.map_one]
    exact ((add_eq_zero_iff_of_nonneg h1 h2).1 h3).1
  have hvint : ∀ x : ℤ_[l], x ≠ 0 →
      P.v LL (algebraMap ℤ_[l] ↥LL.1 x) = ((x.valuation : ℕ) : WithTop ℚ) := by
    intro x hx
    conv_lhs => rw [PadicInt.unitCoeff_spec hx]
    rw [map_mul, AddValuation.map_mul, hvunit, zero_add, map_pow, map_natCast,
      AddValuation.map_pow, P.v_l LL]
    simp
  obtain ⟨g, hgg⟩ := (H.W K 1 LL hg).resΓ_onto (H.W K 1 LL hg).gam
  have hχ := (H.W K 1 LL hg).χΓ_res g
  rw [hgg] at hχ
  have hint : IsIntegral ℤ_[l] (algebraMap ℚ_[l] ↥LL.1 ((P.PD K).χ g : ℚ_[l])) := by
    rw [← hχ]
    exact (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)).2
  have hint' : IsIntegral ℤ_[l] ((P.PD K).χ g : ℚ_[l]) :=
    (isIntegral_algebraMap_iff (algebraMap ℚ_[l] ↥LL.1).injective).1 hint
  obtain ⟨z, hz⟩ := IsIntegrallyClosed.isIntegral_iff.1 hint'
  have hzLL : algebraMap ℤ_[l] ↥LL.1 z = algebraMap ↥(OL LL) ↥LL.1
      (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam : (↥(OL LL))ˣ) : ↥(OL LL)) := by
    rw [hχ, ← hz, ← IsScalarTower.algebraMap_apply]
  have hgen := (H.W K 1 LL hg).gam_gen
  rw [hs, ← hzLL] at hgen
  have hz1 : z - 1 ≠ 0 := by
    intro h0
    have : algebraMap ℤ_[l] ↥LL.1 z - 1 = 0 := by
      rw [← map_one (algebraMap ℤ_[l] ↥LL.1), ← map_sub, h0, map_zero]
    rw [this, AddValuation.map_zero] at hgen
    exact WithTop.top_ne_natCast 1 hgen
  have hval : (z - 1).valuation = 1 := by
    have h1 := hvint (z - 1) hz1
    rw [map_sub, map_one, hgen] at h1
    exact le_antisymm (kapPiPf_natCast_le h1.ge) (kapPiPf_natCast_le h1.le)
  have hzu : IsUnit z := by
    rcases IsLocalRing.isUnit_or_isUnit_of_add_one (show z + (1 - z) = 1 by ring) with h | h
    · exact h
    · exfalso
      obtain ⟨u, hu⟩ := h
      have h1 := hvunit u
      have h2 : algebraMap ℤ_[l] ↥LL.1 (1 - z) = -(algebraMap ℤ_[l] ↥LL.1 z - 1) := by
        rw [map_sub, map_one]; ring
      rw [hu, h2, AddValuation.map_neg, hgen] at h1
      have h3 : (1 : ℕ) ≤ 0 := kapPiPf_natCast_le (by rw [h1]; simp)
      omega
  obtain ⟨χ, rfl⟩ := hzu
  refine ⟨χ, hval, hz1, fun k => ?_⟩
  have e1 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1)
      ((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) =
      Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) χ := Units.ext hzLL.symm
  have e2 : Units.map (algebraMap ↥(OL LL) ↥LL.1 : ↥(OL LL) →* ↥LL.1)
      (((H.W K 1 LL hg).χΓ (H.W K 1 LL hg).gam) ^ k) =
      Units.map (algebraMap ℤ_[l] ↥LL.1 : ℤ_[l] →* ↥LL.1) (χ ^ k) := by
    rw [map_zpow, map_zpow, e1]
  have e3 := congrArg Units.val e2
  have e4 : algebraMap ↥(OL LL) ↥LL.1
      (((Formalism.MainNotions.DeltaInvariantLattices.uU (H.W K 1 LL hg)) ^ k : (↥(OL LL))ˣ) : ↥(OL LL)) =
      algebraMap ↥(OL LL) ↥LL.1 (algebraMap ℤ_[l] ↥(OL LL) ((χ ^ k : ℤ_[l]ˣ) : ℤ_[l])) := by
    rw [← IsScalarTower.algebraMap_apply]
    exact e3
  exact Subtype.val_injective e4

theorem kapPiPf_main {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (P : LocPrime l) (H : LocHW l P)
    (K LL : FinExt l) (hg : Good K 1 LL) (h' S : ℕ) (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool)
    (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ) (c : ZMod (finrank ℚ_[l] ↥(K0 K)))
    (hb : ∀ τ, 0 < b τ) (hbh : ∀ τ, b τ + S ≤ h') :
    KapPi (H.W K 1 LL hg) c S h' (kapA l (eK K) h' S) up b := by
  obtain ⟨χ, hv1, hv0, hpow⟩ := kapPiPf_uU P H K LL hg
  have : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have : FiniteDimensional ↥(K0 K) ↥K.1 := FiniteDimensional.right ℚ_[l] ↥(K0 K) ↥K.1
  haveI : Fintype {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter (H.W K 1 LL hg) τ c} :=
    Fintype.ofFinite _
  have hΩ : ∀ i ∈ OmF (H.W K 1 LL hg) c S h' up b,
      ∃ τ : {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter (H.W K 1 LL hg) τ c},
        (up τ.1 = true ∧ -((b τ.1 : ℤ) + S) ≤ i ∧ i < -(b τ.1 : ℤ)) ∨
        (up τ.1 = false ∧ (b τ.1 : ℤ) ≤ i ∧ i < b τ.1 + S) := by
    intro i hi
    unfold OmF at hi
    simp only [Finset.mem_filter] at hi
    obtain ⟨-, τ, hτ, h⟩ := hi
    exact ⟨⟨τ, hτ⟩, h⟩
  have h0 : (0 : ℤ) ∉ OmF (H.W K 1 LL hg) c S h' up b := by
    intro hi
    obtain ⟨τ, h⟩ := hΩ 0 hi
    have := hb τ.1
    omega
  have hsum := kapPiPf_sum
    (ι := {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter (H.W K 1 LL hg) τ c}) l (fun τ => up τ.1) (fun τ => b τ.1) S h' (fun τ => hb τ.1)
    (fun τ => hbh τ.1) _ hΩ
  have hcard : Fintype.card
      {τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1 // Formalism.MainNotions.DeltaInvariantLattices.OverLetter (H.W K 1 LL hg) τ c} ≤ eK K := by
    rw [Fintype.card_eq_nat_card]
    exact kapPiPf_card (H.W K 1 LL hg) c
  obtain ⟨X, hXd⟩ : ∃ X : ℤ_[l],
      ∏ i ∈ OmF (H.W K 1 LL hg) c S h' up b, (1 - ((χ ^ i : ℤ_[l]ˣ) : ℤ_[l])) = X := ⟨_, rfl⟩
  have hXval : X.valuation = ∑ i ∈ OmF (H.W K 1 LL hg) c S h' up b, (1 + padicValNat l i.natAbs) := by
    rw [← hXd]
    exact DualFramesAlt.Val.val_prod_one_sub_zpow hl χ hv1 hv0 _ h0
  have hX0 : X ≠ 0 := by
    rw [← hXd, Finset.prod_ne_zero_iff]
    intro i hi h
    have hi0 : i ≠ 0 := fun h2 => h0 (h2 ▸ hi)
    have he := DualFramesAlt.Val.emult_zpow_sub_one hl χ (DualFramesAlt.Val.p_dvd_of_valuation_one hv0 hv1)
      (DualFramesAlt.Val.emult_of_valuation_one hv0 hv1) hi0
    rw [sub_eq_zero.2 (sub_eq_zero.1 h).symm, emultiplicity_zero] at he
    exact ENat.top_ne_natCast _ he
  obtain ⟨V, hV⟩ : ∃ V : ℕ, X.valuation = V := ⟨_, rfl⟩
  have hVκ : V ≤ kapA l (eK K) h' S := by
    rw [← hV, hXval]
    unfold kapA
    exact hsum.trans (Nat.mul_le_mul_right _ hcard)
  obtain ⟨w, hw⟩ : ∃ w : ℤ_[l]ˣ, X = (w : ℤ_[l]) * (l : ℤ_[l]) ^ V :=
    ⟨_, by rw [← hV]; exact PadicInt.unitCoeff_spec hX0⟩
  have key : (w⁻¹ : ℤ_[l]ˣ) * (l : ℤ_[l]) ^ (kapA l (eK K) h' S - V) * X =
      (l : ℤ_[l]) ^ kapA l (eK K) h' S := by
    conv_lhs => rw [hw]
    rw [show (w⁻¹ : ℤ_[l]ˣ) * (l : ℤ_[l]) ^ (kapA l (eK K) h' S - V) *
        (((w : ℤ_[l]ˣ) : ℤ_[l]) * (l : ℤ_[l]) ^ V) =
        (((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * ((w : ℤ_[l]ˣ) : ℤ_[l])) *
        ((l : ℤ_[l]) ^ (kapA l (eK K) h' S - V) * (l : ℤ_[l]) ^ V) by ring,
      Units.inv_mul, one_mul, ← pow_add, Nat.sub_add_cancel hVκ]
  have hpi : piOm1 (H.W K 1 LL hg) c S h' up b = algebraMap ℤ_[l] ↥(OL LL) X := by
    unfold piOm1
    rw [← hXd, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_sub, map_one, hpow i]
  refine ⟨algebraMap ℤ_[l] ↥(OL LL)
    (((w⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) * (l : ℤ_[l]) ^ (kapA l (eK K) h' S - V)), ?_⟩
  rw [hpi, ← map_mul, key, map_pow, map_natCast, P.PD_p K]

theorem kappi_pf : KapPiStep := by
  intro D HW F Cm CA CB CK _ l _ hl K LL hG π' E _ h' S up b c hb hbh
  exact kapPiPf_main hl _ (HW l) K LL hG h' S up b c hb hbh

end Formalism.MainNotions.N.Ln34

end
