import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImV
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdFundamentalDomainOfExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AddFundamentalDomainMeasureEqOfCountableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFundamentalDomainSndOfTwoSmulMemStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsMixedSpaceReImCoordsTotallyComplexStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FractionalIdealBasisTransportMeasurePreservingStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCmExtensionMixedSpaceRealCoordsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsDiscrEqSqOfUnramifiedCmExtensionStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AbsNormInverseDifferentIdealPowEqDiscrStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemInverseDifferentIdealPowRealIffUnramifiedCmStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddConjEqOneOfFormallyUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmExtensionConjMemInverseDifferentIdealPowStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ScaledSkewLatticeFundamentalDomainOfImaginaryParStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeQuotientOfRealIdentityStatement

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

noncomputable section

namespace GlobalTheory.SnMass.SkewVol
theorem dom_of_basis {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {ι : Type} [Finite ι]
    (b : Module.Basis ι ℝ W) (v : W) :
    ∃! l, l ∈ (Submodule.span ℤ (Set.range b) : Set W) ∧ v + l ∈ ZSpan.fundamentalDomain b := by
  obtain ⟨⟨l, hl⟩, h1, h2⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain b v
  refine ⟨l, ⟨hl, by simpa [Submodule.vadd_def, add_comm] using h1⟩, ?_⟩
  rintro l' ⟨hl', h'⟩
  have := h2 ⟨l', hl'⟩ (by simpa [Submodule.vadd_def, add_comm] using h')
  simpa using congrArg Subtype.val this

theorem dInv_ne_zero (K : Type) [Field K] [NumberField K] (j : ℕ) : dInv K j ≠ 0 := by
  unfold dInv
  refine pow_ne_zero _ (inv_ne_zero ?_)
  exact FractionalIdeal.coeIdeal_ne_zero.2 differentIdeal_ne_bot

theorem skew_covol_dInv : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.FormallyUnramified (𝓞 F) (𝓞 E) → ∀ (t : ℕ) (c : ℝ), 0 < c → HasDom volume (skewLat (σ : E →+* E) (dInv E (2 * t)) c : Set (InfinitePlace E → ℝ)) (ENNReal.ofReal (|(NumberField.discr F : ℝ)| ^ (1 / 2 - 2 * (t : ℝ)) * c ^ Fintype.card (InfinitePlace E))) := by
  intro F E _ _ _ _ _ σ hCM hU t c hc
  have hTC : IsTotallyComplex E := hCM.2.1
  have hTR : IsTotallyReal F := hCM.1
  have hσw : ∀ (w : InfinitePlace E) (x : E), w.embedding (σ x) = star (w.embedding x) :=
    fun w x => hCM.2.2.2 w.embedding x
  have hre : ∀ x : E, reV (σ x) = reV x := fun x => funext fun w => by simp [reV, hσw]
  have him : ∀ x : E, imV (σ x) = -imV x := fun x => funext fun w => by simp [imV, hσw]
  obtain ⟨e, he, hex⟩ := GlobalTheory.T.exists_mixedSpace_reIm_coords_totallyComplex E hTC
  obtain ⟨ι, _, b, hbs, hbv⟩ := GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving E volume e he (Units.mk0 (dInv E (2 * t)) (dInv_ne_zero E _))
  obtain ⟨e1, he1, he1x⟩ := GlobalTheory.T.exists_cmExtension_mixedSpace_realCoords F E σ hCM
  obtain ⟨ι1, _, b1, hb1s, hb1v⟩ :=
    GlobalTheory.T.fractionalIdeal_basis_transport_measurePreserving F volume e1 he1 (Units.mk0 (dInv F (2 * t)) (dInv_ne_zero F _))
  simp only [Units.val_mk0] at hbs hbv hb1s hb1v
  set Λ := Submodule.span ℤ (Set.range b) with hΛdef
  have hΛ : ∀ p, p ∈ Λ ↔ ∃ x ∈ dInv E (2 * t), (reV x, imV x) = p := by
    intro p
    rw [← SetLike.mem_coe, hbs]
    simp [hex]
  have hL1 : ∀ a, a ∈ (Submodule.span ℤ (Set.range b1) : Set (InfinitePlace E → ℝ)) ↔
      (a, (0 : InfinitePlace E → ℝ)) ∈ Λ := by
    intro a
    rw [hb1s, hΛ]
    simp only [Set.mem_image, Set.mem_setOf_eq, he1x, Prod.mk.injEq]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have h := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU (2 * t) (algebraMap F E y)).2 ⟨y, hy, rfl⟩
      exact ⟨_, h.1, rfl, h.2⟩
    · rintro ⟨x, hx, rfl, h0⟩
      obtain ⟨y, hy, rfl⟩ := (GlobalTheory.T.mem_inverseDifferentIdealPow_real_iff_unramified_cm F E σ hCM hU _ _).1 ⟨hx, h0⟩
      exact ⟨y, hy, rfl⟩
  have hD1 : ∀ a, ∃! l, l ∈ {a : InfinitePlace E → ℝ | (a, (0 : InfinitePlace E → ℝ)) ∈ Λ.toAddSubgroup} ∧
      a + l ∈ ZSpan.fundamentalDomain b1 := by
    intro a
    obtain ⟨l, hl, hu⟩ := dom_of_basis b1 a
    exact ⟨l, ⟨(hL1 l).1 hl.1, hl.2⟩, fun l' hl' => hu l' ⟨(hL1 l').2 hl'.1, hl'.2⟩⟩
  have h2 : ∀ a y, (a, y) ∈ Λ → ((0 : InfinitePlace E → ℝ), (2 : ℝ) • y) ∈ Λ := by
    intro a y hay
    obtain ⟨x, hx, hxe⟩ := (hΛ _).1 hay
    rw [Prod.mk.injEq] at hxe
    refine (hΛ _).2 ⟨x - σ x, Submodule.sub_mem (dInv E (2 * t) : Submodule (𝓞 E) E) hx (GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx), ?_⟩
    have h1 : reV (x - σ x) = reV x - reV (σ x) := funext fun w => by simp [reV]
    have h1' : imV (x - σ x) = imV x - imV (σ x) := funext fun w => by simp [imV]
    rw [h1, h1', hre, him, ← hxe.2]
    refine Prod.ext ?_ ?_
    · simp
    · funext w; simp; ring
  have hsp : Submodule.span ℝ (Λ : Set ((InfinitePlace E → ℝ) × (InfinitePlace E → ℝ))) = ⊤ := by
    rw [hΛdef, Submodule.span_span_of_tower, b.span_eq]
  obtain ⟨D2, hD2m, hD2⟩ := GlobalTheory.T.exists_fundamentalDomain_snd_of_two_smul_mem' Λ hsp h2
  have hprod := GlobalTheory.T.existsUnique_prod_fundamentalDomain_of_extension Λ.toAddSubgroup _ D2 hD1 hD2
  have heq := GlobalTheory.T.addFundamentalDomain_measure_eq_of_countable ((volume : Measure (InfinitePlace E → ℝ)).prod (volume : Measure (InfinitePlace E → ℝ))) Λ _ _ ((ZSpan.fundamentalDomain_measurableSet b1).prod hD2m)
    (ZSpan.fundamentalDomain_measurableSet b) hprod (dom_of_basis b)
  rw [Measure.prod_prod, ← Measure.volume_eq_prod, hbv, hb1v] at heq
  have hL2 : ∀ y, (∃ a, (a, y) ∈ Λ) ↔ ∃ x ∈ dInv E (2 * t), imV x = y := by
    intro y
    simp only [hΛ, Prod.mk.injEq]
    constructor
    · rintro ⟨a, x, hx, -, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨_, x, hx, rfl, rfl⟩
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_integer_add_conj_eq_one_of_formallyUnramified' F E σ hCM hU
  have hfin := GlobalTheory.T.scaledSkewLattice_fundamentalDomain_of_imaginaryParts F E σ hCM (dInv E (2 * t)) (fun x hx => GlobalTheory.T.cmExtension_conj_mem_inverseDifferentIdealPow F E σ hCM _ x hx) θ hθ c hc D2 _
    hD2m (fun y => by simpa only [Set.mem_setOf_eq, hL2] using hD2 y) rfl
  have hd : (1 : ℝ) ≤ |(discr F : ℝ)| := by
    have h := Int.one_le_abs (discr_ne_zero F)
    rw [← Int.cast_abs]
    exact_mod_cast h
  have hnc : InfinitePlace.nrComplexPlaces E = Fintype.card (InfinitePlace E) := by
    have h := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces E
    rw [IsTotallyComplex.nrRealPlaces_eq_zero E, zero_add] at h
    exact h.symm
  have hnr : InfinitePlace.nrComplexPlaces F = 0 := IsTotallyReal.nrComplexPlaces_eq_zero F
  rw [GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.absNorm_inverseDifferentIdealPow_eq_discr, GlobalTheory.T.abs_discr_eq_sq_of_unramified_cmExtension F E σ hCM hU, hnc, hnr] at heq
  rw [GlobalTheory.T.covolumeQuotient_ofReal_identity _ c _ t _ hd hc heq.symm] at hfin
  exact hfin

end GlobalTheory.SnMass.SkewVol
