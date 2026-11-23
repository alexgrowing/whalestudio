import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmRepresentationEigenDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypePeriodNormIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCombinationInHodgeFiltrationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeProjectionFromLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeProjectionEigenvalueCompatStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLeFinrankSupEigenspacesStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FilCx

theorem fil_eq_iSup_eigenspace_bar : GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.AbelianDeRham →
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ →
    ∀ (c : Ideal (OF E)), c ≠ ⊥ → ∀ (𝔠 : FracId (FR E)) (L : Set E) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ L 0 X)
      (α : orderC c → (X.A ⟶ X.A)) [∀ a, IsMonHom (α a)],
      (∀ (a : orderC c) w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α a) →
      Fil X.A = ⨆ i, ⨅ a : orderC c,
        Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) := by
  intro hPC hADR E _ _ _ I _ φ hφ c hc 𝔠 L X U α _ hα
  obtain ⟨ε, hpc⟩ := hPC
  set g := Module.finrank ℚ (FR E) with hg
  have hLB : (X.diag U.c).IsLB := ReciprocityTheory.ChartRestriction.G.DVR.linComb_isLB _ (X.isLB U.c) _ _
  obtain ⟨P, hspan, hdim, hlie, hend, -⟩ := hpc X.A g X.ab X.dim (X.diag U.c) hLB U.u
  clear hpc
  have hLE : LieExact X.A := (hADR.2.1 ℂ X.A g X.ab X.dim).1
  obtain ⟨Q, hQker, hQP, hFdim⟩ :=
    GlobalTheory.T.hodge_projection_from_lattice (HdR X.A) g U.u.Λ P (Fil X.A) hspan hdim U.u.full (GlobalTheory.T.lattice_combination_in_hodge_filtration X.A X.ab _ g U.u P hLE hlie)
  let M : orderC c → (Fin g → ℂ) →ₗ[ℂ] (Fin g → ℂ) := fun a ↦
    LinearMap.pi fun j ↦ (φ (U.e j) (a : E)) • LinearMap.proj j
  have hM : ∀ a w, M a w = fun j ↦ φ (U.e j) (a : E) * w j := fun a w ↦ by ext j; simp [M]
  have hMΛ : ∀ (a : orderC c) (x : U.u.Λ), (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) ∈ U.u.Λ := by
    intro a x
    rw [← U.u.ker, hα a, (U.u.ker x).2 x.2]
    simp
  have hT : ∀ (a : orderC c) (x y : U.u.Λ), (y : Fin g → ℂ) = (fun j ↦ φ (U.e j) (a : E) * (x : Fin g → ℂ) j) →
      push (dp0 ℂ) (𝟙 _) (α a) (P x) = P y := by
    intro a x y hy
    exact hend (α a) (M a) (fun w ↦ by rw [hM]; exact hα a w) x y (by rw [hy, hM])
  have hbar : ∀ σ : E →+* ℂ, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar σ = ComplexEmbedding.conjugate σ := fun σ ↦ by
    ext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar, ComplexEmbedding.conjugate_coe_eq, IsCMField.complexEmbedding_complexConj]
  have hnreal : ∀ σ : E →+* ℂ, ¬ ComplexEmbedding.IsReal σ := fun σ h ↦
    (NumberField.InfinitePlace.isComplex_mk_iff (φ := σ)).1 (NumberField.IsTotallyComplex.isComplex _) h
  have hsep : ∀ (i : I) (j : Fin g), ∃ a : orderC c, φ (U.e j) (a : E) ≠ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i j
    by_contra h
    push_neg at h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ h
    rw [hbar] at h1
    obtain ⟨k, -, hk⟩ := hφ (φ (U.e j))
    have e1 := hk (U.e j) (Or.inl rfl)
    have e2 := hk i (Or.inr h1)
    rw [e1, ← e2] at h1
    exact hnreal _ h1.symm
  have hinj : Function.Injective fun (i : I) (a : orderC c) ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) (a : E) := by
    intro i i' h
    have h1 := GlobalTheory.CMExtend.ringHom_ext_orderC hc _ _ (fun a ↦ congrFun h a)
    rw [hbar, hbar] at h1
    have h2 : φ i = φ i' := by
      ext x
      simpa [ComplexEmbedding.conjugate_coe_eq] using congrArg (starRingEnd ℂ) (RingHom.congr_fun h1 x)
    obtain ⟨k, -, hk⟩ := hφ (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h2)).symm
  have hcomm : ∀ a b : orderC c, Commute (push (dp0 ℂ) (𝟙 _) (α a)) (push (dp0 ℂ) (𝟙 _) (α b)) := by
    intro a b
    refine LinearMap.ext_on_range hspan fun x ↦ ?_
    simp only [Module.End.mul_apply]
    rw [hT b x ⟨_, hMΛ b x⟩ rfl, hT a x ⟨_, hMΛ a x⟩ rfl, hT a _ ⟨_, hMΛ a ⟨_, hMΛ b x⟩⟩ rfl,
      hT b _ ⟨_, hMΛ b ⟨_, hMΛ a x⟩⟩ rfl]
    congr 1
    ext j
    simp only
    ring
  have hpos : 0 < g := Module.finrank_pos
  haveI : FiniteDimensional ℂ (HdR X.A) := Module.finite_of_finrank_pos (by rw [hdim]; omega)
  have hEdim : Module.finrank ℂ (HdR X.A) = Module.finrank ℚ E := by
    rw [hdim, ← Module.finrank_mul_finrank ℚ (maximalRealSubfield E) E,
      Algebra.IsQuadraticExtension.finrank_eq_two (maximalRealSubfield E) E, mul_comm]

  let Φ : E →+* (Fin g → ℂ) := Pi.ringHom fun j ↦ φ (U.e j)
  let L' : AddSubgroup E := AddSubgroup.comap Φ.toAddMonoidHom U.u.Λ.toAddSubgroup
  let jL : L' →+ U.u.Λ :=
    { toFun := fun x ↦ ⟨Φ x, x.2⟩
      map_zero' := by ext; simp
      map_add' := fun x y ↦ by ext; simp }
  have hone : ∀ i, 1 ≤ Module.finrank ℂ (⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) : Submodule ℂ (HdR X.A)) := by
    intro i
    refine le_of_eq (GlobalTheory.T.cm_representation_eigen_decomposition E (orderC c) (GlobalTheory.CMExtend.exists_natMul_mem_orderC hc) L' ?_ (HdR X.A)
      (P.comp jL) ?_ hEdim (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) ?_ (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i))).symm
    · intro a ha x hx
      show Φ (a * x) ∈ U.u.Λ
      have e : Φ (a * x) = fun j ↦ φ (U.e j) a * (Φ x) j := by rw [map_mul]; rfl
      rw [e]; exact hMΛ ⟨a, ha⟩ ⟨Φ x, hx⟩
    · refine eq_top_mono (Submodule.span_mono ?_) hspan
      rintro _ ⟨y, rfl⟩
      obtain ⟨x, -, hx⟩ := (U.lat y).1 y.2
      have hxy : Φ x = y := by
        rw [hx]; funext j; simp only [GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.defCoord, Pi.zero_apply, zero_mul, add_zero]; rfl
      have hmem : x ∈ L' := by
        show Φ x ∈ U.u.Λ
        rw [hxy]; exact y.2
      refine ⟨⟨x, hmem⟩, ?_⟩
      show P (jL ⟨x, hmem⟩) = P y
      congr 1
      exact Subtype.ext hxy
    · intro a x y hy
      refine hT a (jL x) (jL y) ?_
      show Φ y = fun j ↦ φ (U.e j) a * (Φ x) j
      rw [hy, map_mul]; rfl
  have hle : (⨆ i, ⨅ a : orderC c,
      Module.End.eigenspace (push (dp0 ℂ) (𝟙 _) (α a)) (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a)) ≤ Fil X.A := by
    refine iSup_le fun i ↦ ?_
    rw [← hQker]
    exact GlobalTheory.T.hodge_projection_eigenvalue_compat (HdR X.A) g U.u.Λ P hspan Q hQP (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a))
      (fun a j ↦ φ (U.e j) (a : E)) hMΛ hT (fun a ↦ GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.bar (φ i) a) (fun j ↦ hsep i j)
  have hge := GlobalTheory.T.card_le_finrank_sup_eigenspaces (HdR X.A) (orderC c) (fun a ↦ push (dp0 ℂ) (𝟙 _) (α a)) hcomm I _ hinj hone
  have hcard : Fintype.card I = g := by rw [Fintype.card_congr U.e.symm, Fintype.card_fin]
  exact (Submodule.eq_of_le_of_finrank_le hle (by rw [hFdim, ← hcard]; exact hge)).symm

end GlobalTheory.FilCx
