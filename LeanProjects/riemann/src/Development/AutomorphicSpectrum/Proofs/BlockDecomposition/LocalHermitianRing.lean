import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsHermRingRat
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCyclicOfFiniteQuotient
open NumberField IsDedekindDomain Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet PositivityTheory.ThKR GlobalTheory.CompanionTheory.KFin
open Formalism.UG (cT)
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.KFin.RingHyp

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {v : HeightOneSpectrum (𝓞 F)}

theorem sigR_sigR (h : IsCMExt F E σ) (y : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ y) = y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul a e =>
    change a ⊗ₜ[F] σ (σ e) = _
    rw [cm_conj_conj h]

theorem finrank_loc (h : IsCMExt F E σ) : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_baseChange, h.2.2.1]

theorem noeth_intLoc : IsNoetherianRing (intLoc F E v) := by
  let _ := (GlobalTheory.Orb.intLocMap E v).toAlgebra
  have : Module.Finite (v.adicCompletionIntegers F) (intLoc F E v) := GlobalTheory.Orb.finite_intLocMap v
  exact IsNoetherianRing.of_finite (v.adicCompletionIntegers F) _

theorem isUnit_intCast {m : ℤ} (hm : m ≠ 0) : IsUnit ((m : ℤ) : Fv F v ⊗[F] E) := by
  have h1 : IsUnit ((m : ℤ) : E) := isUnit_iff_ne_zero.2 (by exact_mod_cast hm)
  simpa using h1.map (inclR (F := F) (Fv F v))

theorem denom_intLoc (a : Fv F v ⊗[F] E) :
    ∃ s ∈ intLoc F E v, IsUnit s ∧ s * a ∈ intLoc F E v := by
  obtain ⟨x, hx⟩ := exists_sub_mem_intLoc v a
  obtain ⟨m, hm, he⟩ := exists_integral_multiples ℤ ℚ ({x} : Finset E)
  have he' : IsIntegral ℤ (m • x) := he x (Finset.mem_singleton_self x)
  have hmem : ((m : ℤ) : Fv F v ⊗[F] E) ∈ intLoc F E v := intCast_mem _ m
  refine ⟨_, hmem, isUnit_intCast hm, ?_⟩
  have h2 := tmul_mem_intLoc (E := E) (one_mem (v.adicCompletionIntegers F)) ⟨m • x, he'⟩
  have e : ((m : ℤ) : Fv F v ⊗[F] E) * a =
      ((m : ℤ) : Fv F v ⊗[F] E) * (a - (1 : Fv F v) ⊗ₜ[F] x) + (1 : Fv F v) ⊗ₜ[F] (m • x) := by
    have e1 : ((m : ℤ) : Fv F v ⊗[F] E) * (1 : Fv F v) ⊗ₜ[F] x = (1 : Fv F v) ⊗ₜ[F] (m • x) := by
      rw [← zsmul_eq_mul, TensorProduct.tmul_smul]
    rw [mul_sub, e1, sub_add_cancel]
  rw [e]
  exact add_mem (mul_mem hmem hx) h2

theorem span_eq_of {R : Type} [CommRing R] {𝔬 : Subring R} {S : Set R} {u : R}
    (hu : u ∈ Submodule.span 𝔬 S) (h : ∀ s ∈ S, ∃ c ∈ 𝔬, s = c * u) :
    Submodule.span 𝔬 S = Submodule.span 𝔬 {u} := by
  refine le_antisymm (Submodule.span_le.2 fun s hs => ?_) ((Submodule.span_singleton_le_iff_mem _ _).2 hu)
  obtain ⟨c, hc, rfl⟩ := h s hs
  exact Submodule.mem_span_singleton.2 ⟨⟨c, hc⟩, rfl⟩

theorem finEmb_injective (hf : IsField (Fv F v ⊗[F] E)) (τ : E →ₐ[F] FvBar F v) :
    Function.Injective (finEmb F v τ) :=
  (injective_iff_map_eq_zero _).2 fun y hy => by
    by_contra h0
    obtain ⟨b, hb⟩ := hf.mul_inv_cancel h0
    have := congrArg (finEmb F v τ) hb
    simp [hy] at this

theorem absBar_finEmb_eq (hf : IsField (Fv F v ⊗[F] E)) (τ τ' : E →ₐ[F] FvBar F v) (y : Fv F v ⊗[F] E) :
    absBar F v (finEmb F v τ y) = absBar F v (finEmb F v τ' y) := by
  apply NNReal.eq
  change spectralNorm (Fv F v) (FvBar F v) _ = spectralNorm (Fv F v) (FvBar F v) _
  rw [spectralNorm, spectralNorm, minpoly.algHom_eq _ (finEmb_injective hf τ),
    minpoly.algHom_eq _ (finEmb_injective hf τ')]

theorem principal_field (hf : IsField (Fv F v ⊗[F] E)) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  have : Nontrivial (Fv F v ⊗[F] E) := ⟨hf.exists_pair_ne⟩
  let τ₀ : E →ₐ[F] FvBar F v := IsAlgClosed.lift
  let N : Fv F v ⊗[F] E → NNReal := fun y => absBar F v (finEmb F v τ₀ y)
  have hN0 : ∀ y, N y = 0 → y = 0 := fun y hy =>
    finEmb_injective hf τ₀ (by rw [map_zero]; exact (absBar_eq_zero F v).1 hy)
  have hS : S.Nonempty := by
    by_contra hc
    rw [Finset.not_nonempty_iff_eq_empty] at hc
    subst hc
    simp only [Finset.coe_empty, Submodule.span_empty, Submodule.mem_bot] at hw
    exact hwu.ne_zero hw
  obtain ⟨u, huS, hmax⟩ := S.exists_max_image N hS
  have hu0 : u ≠ 0 := by
    rintro rfl
    have h0 : (Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) ≤ ⊥ :=
      Submodule.span_le.2 fun s hs => by
        refine hN0 s (le_antisymm ?_ zero_le)
        have := hmax s hs
        rwa [show N 0 = 0 from by simp [N, (absBar_eq_zero F v).2 rfl]] at this
    exact hwu.ne_zero (by simpa using h0 hw)
  obtain ⟨b, hb⟩ := hf.mul_inv_cancel hu0
  have huU : IsUnit u := IsUnit.of_mul_eq_one b hb
  refine ⟨u, huU, span_eq_of (Submodule.subset_span huS) fun s hs => ⟨b * s, ?_, ?_⟩⟩
  · refine mem_intLoc_iff_absFin_le_one.2 ((absFin_le_iff F v).2 fun τ => ?_)
    rw [absBar_finEmb_eq hf τ τ₀, map_mul, absBar_mul]
    have h1 : absBar F v (finEmb F v τ₀ u) * absBar F v (finEmb F v τ₀ b) = 1 := by
      rw [← absBar_mul, ← map_mul, hb, map_one]
      simpa using absBar_algebraMap F v 1
    calc _ ≤ absBar F v (finEmb F v τ₀ b) * absBar F v (finEmb F v τ₀ u) := mul_le_mul' le_rfl (hmax s hs)
      _ = 1 := by rw [mul_comm, h1]
  · rw [mul_right_comm, mul_comm b, hb, one_mul]

theorem exists_dom (ρ : Fv F v ⊗[F] E →ₐ[Fv F v] Fv F v) (S : Finset (Fv F v ⊗[F] E)) {w : Fv F v ⊗[F] E}
    (hw : w ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E))) (hwu : IsUnit w) :
    ∃ j ∈ S, ρ j ≠ 0 ∧ ∀ s ∈ S, ‖ρ s‖₊ ≤ ‖ρ j‖₊ := by
  have hex : ∃ j ∈ S, ρ j ≠ 0 := by
    by_contra hc
    push Not at hc
    have h0 : ∀ y ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)), ρ y = 0 := fun y hy => by
      induction hy using Submodule.span_induction with
      | mem x hx => exact hc x hx
      | zero => simp
      | add x y _ _ hx hy => rw [map_add, hx, hy, add_zero]
      | smul a x _ hx => rw [Subring.smul_def, smul_eq_mul, map_mul, hx, mul_zero]
    exact (hwu.map ρ).ne_zero (h0 w hw)
  obtain ⟨j0, hj0, hj0'⟩ := hex
  obtain ⟨j, hj, hmax⟩ := S.exists_max_image (fun s => ‖ρ s‖₊) ⟨j0, hj0⟩
  refine ⟨j, hj, fun e => hj0' ?_, hmax⟩
  have := hmax j0 hj0
  rw [e, nnnorm_zero] at this
  exact nnnorm_eq_zero.1 (le_antisymm this zero_le)

theorem principal_split (h : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) (I : Submodule (intLoc F E v) (Fv F v ⊗[F] E))
    (hI : I.FG) (hu : ∃ u ∈ I, IsUnit u) : ∃ u : Fv F v ⊗[F] E, IsUnit u ∧ I = Submodule.span (intLoc F E v) {u} := by
  classical
  obtain ⟨S, rfl⟩ := hI
  obtain ⟨w, hw, hwu⟩ := hu
  obtain ⟨j1, hj1, h1, hm1⟩ := exists_dom (splitProj τ) S hw hwu
  obtain ⟨j2, hj2, h2, hm2⟩ := exists_dom (splitProj (τ.comp σ)) S hw hwu
  set e := splitIdem h τ with he
  have heI : e ∈ intLoc F E v := splitIdem_mem h τ
  set u : Fv F v ⊗[F] E := e * j1 + (1 - e) * j2 with hu
  have hup : splitProj τ u = splitProj τ j1 := by simp [hu, he]
  have huq : splitProj (τ.comp σ) u = splitProj (τ.comp σ) j2 := by simp [hu, he]
  have hmem : u ∈ Submodule.span (intLoc F E v) (S : Set (Fv F v ⊗[F] E)) :=
    add_mem (Submodule.smul_mem _ (⟨e, heI⟩ : intLoc F E v) (Submodule.subset_span hj1))
      (Submodule.smul_mem _ (⟨1 - e, sub_mem (one_mem _) heI⟩ : intLoc F E v) (Submodule.subset_span hj2))
  have hunit : IsUnit u := by
    refine IsUnit.of_mul_eq_one ((splitAlgEquiv h τ).symm ((splitProj τ j1)⁻¹, (splitProj (τ.comp σ) j2)⁻¹)) ?_
    refine split_ext h τ ?_ ?_
    · simp [hup, h1]
    · simp [huq, h2]
  refine ⟨u, hunit, span_eq_of hmem fun s hs => ?_⟩
  refine ⟨(splitAlgEquiv h τ).symm (splitProj τ s / splitProj τ j1, splitProj (τ.comp σ) s / splitProj (τ.comp σ) j2),
    (mem_intLoc_iff_split h τ).2 ⟨?_, ?_⟩, split_ext h τ ?_ ?_⟩
  · rw [splitProj_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm1 s hs) zero_le
  · rw [splitProj_comp_symm, ← nnnorm_le_one_iff_mem, nnnorm_div]
    exact div_le_one_of_le₀ (hm2 s hs) zero_le
  · simp [hup, h1]
  · simp [huq, h2]

theorem isHermRing_intLoc : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E}, IsCMExt F E σ → ∀ (v : HeightOneSpectrum (𝓞 F)),
      IsHermRing (sigR (Fv F v) σ) (intLoc F E v) := by
  intro F E _ _ _ _ _ σ h v
  have h2 : Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := finrank_loc h
  have hfin : Module.Finite (Fv F v) (Fv F v ⊗[F] E) := Module.finite_of_finrank_pos (by omega)
  refine
    { invol := sigR_sigR h
      conj_mem := fun a ha => sigR_mem_intLoc σ ha
      nontrivial := Module.nontrivial_of_finrank_pos (R := Fv F v) (by omega)
      artinian := IsArtinianRing.of_finite (Fv F v) _
      noeth := noeth_intLoc
      two := ?_
      denom := denom_intLoc
      principal := fun I hI hu => ?_ }
  · have h1 : IsUnit (2 : E) := isUnit_iff_ne_zero.2 two_ne_zero
    have h3 := h1.map (inclR (F := F) (Fv F v))
    rwa [map_ofNat] at h3
  · by_cases hf : IsField (Fv F v ⊗[F] E)
    · exact principal_field hf I hI hu
    · obtain ⟨φ⟩ := nonempty_algHom_of_not_isField (K := Fv F v) h2 hf
      exact principal_split h ((φ.restrictScalars F).comp Algebra.TensorProduct.includeRight) I hI hu

end GlobalTheory.CompanionTheory.KFin.RingHyp

end
