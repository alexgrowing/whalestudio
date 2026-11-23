import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OpenField
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineQuotientTensorDual
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriods
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

noncomputable section

namespace UpperTheory.V.Loc

section Generic

variable {G : Type} [Group G] {Q V V' W : Type} [Field Q] [AddCommGroup V] [Module Q V] [AddCommGroup V']
  [Module Q V'] [AddCommGroup W] [Module Q W] [FiniteDimensional Q V]

private theorem exists_inj_dual_tprod (ρ : Representation Q G V) (ρ' : Representation Q G V')
    (π : Representation Q G W) (b : W →ₗ[Q] V →ₗ[Q] V') (hb : ∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x))
    (hi : Function.Injective b) :
    ∃ f : W →ₗ[Q] Module.Dual Q V ⊗[Q] V', (∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) ∧
      Function.Injective f := by
  let e := dualTensorHomEquiv Q V V'
  refine ⟨e.symm.toLinearMap ∘ₗ b, fun g w => ?_, e.symm.injective.comp hi⟩
  have key : ∀ (t : Module.Dual Q V ⊗[Q] V') (x : V),
      e ((ρ.dual.tprod ρ') g t) (ρ g x) = ρ' g (e t x) := by
    intro t x
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add s t hs ht => simp only [map_add, LinearMap.add_apply, hs, ht]
    | tmul f y => simp [e, Module.Dual.transpose_apply]
  apply e.injective
  ext x
  obtain ⟨x, rfl⟩ : ∃ y, ρ g y = x := ⟨ρ g⁻¹ x, by simp⟩
  rw [key]
  simp [hb]

end Generic

section Transport

variable {l : ℕ} [Fact l.Prime] {G H A V : Type} [Group G] [Group H] [CommRing A] [Algebra ℚ_[l] A]
  [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V]

private theorem admissible_transport_equiv (ψ : H →* GQ l) (e : G ≃* H) (ρ : Representation A G V) :
    (IsCr (ψ.comp e.toMonoidHom) ρ ↔ IsCr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) ∧
    (IsDr (ψ.comp e.toMonoidHom) ρ ↔ IsDr ψ (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
  have hr : (ψ.comp e.toMonoidHom).range = ψ.range := by
    ext x
    exact ⟨fun ⟨g, hg⟩ => ⟨e g, hg⟩, fun ⟨h, hh⟩ => ⟨e.symm h, by simpa using hh⟩⟩
  have h1 : Dcr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Dcr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Dcr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actC, resCoef]
  have h2 : Ddr (ψ.comp e.toMonoidHom) (resCoef ℚ_[l] ρ) =
      Ddr ψ (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A H V)) := by
    unfold Ddr
    refine e.toEquiv.iInf_congr fun g => ?_
    simp [actD, resCoef]
  unfold IsCr IsDr
  rw [hr, h1, h2]
  exact ⟨Iff.rfl, Iff.rfl⟩

end Transport

section Field

variable {l : ℕ} [Fact l.Prime] (K : FinExt l) {V V' W : Type} [AddCommGroup V] [Module ℚ_[l] V]
  [AddCommGroup V'] [Module ℚ_[l] V'] [AddCommGroup W] [Module ℚ_[l] W] [FiniteDimensional ℚ_[l] V]
  [FiniteDimensional ℚ_[l] V'] [FiniteDimensional ℚ_[l] W]
  (ρ : Representation ℚ_[l] ↥(GK K) V) (ρ' : Representation ℚ_[l] ↥(GK K) V')
  (π : Representation ℚ_[l] ↥(GK K) W) (f : W →ₗ[ℚ_[l]] Module.Dual ℚ_[l] V ⊗[ℚ_[l]] V')
  (hf : ∀ g w, f (π g w) = (ρ.dual.tprod ρ') g (f w)) (hi : Function.Injective f)
include hf hi

private theorem crys_hom (h : IsCrys ((PP l).PD K) ρ) (h' : IsCrys ((PP l).PD K) ρ') :
    IsCrys ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  obtain ⟨C, hfit⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l _ _ T
  haveI := GlobalTheory.RegularRing.isDomain_of_tied T K
  have h1 := GlobalTheory.RegularRing.fracInv hfit (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C) K
  have h2 := GlobalTheory.RegularRing.lineUnit hfit (GlobalTheory.T.bcris_regular_of_tensorInj l C (GlobalTheory.T.algClosure_tensor_bcris_to_bdR_injective l C)) K
  exact GlobalTheory.RegularRing.subCrys _ ℚ_[l] h1 _ _ _ π f hf hi
    (GlobalTheory.RegularRing.tensorCrys _ ℚ_[l] h1 h2 _ _ _ _
      (GlobalTheory.RegularRing.dualCrys _ ℚ_[l] h1 h2 _ ρ h) h')

private theorem dR_hom (h : IsDR ((PP l).PD K) ρ) (h' : IsDR ((PP l).PD K) ρ') :
    IsDR ((PP l).PD K) π := by
  obtain ⟨T⟩ := tiedP l
  have := K.2
  have hF := GlobalTheory.DRFil.isField_dR T
  have s : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ hF h
  have s' : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ' := GlobalTheory.Per.DeRhamSpan.span_of_isField _ ρ' hF h'
  have sd : GlobalTheory.DRFil.Spans ((PP l).PD K) ρ.dual :=
    GlobalTheory.DRFil.spans_dual_of_spans _ ρ ρ.dual (Module.Dual.eval ℚ_[l] V) hF
      (fun g x y => by simp [Module.Dual.transpose_apply]) Function.bijective_id s
  have st : GlobalTheory.DRFil.Spans ((PP l).PD K) (ρ.dual.tprod ρ') :=
    GlobalTheory.DRFil.Spans.tensor _ (LinearEquiv.refl _ _) (fun g x y => by simp) sd s'
  have sw := GlobalTheory.DRSubQuot.spans_of_injective _ π _ f hf hF hi st
  obtain ⟨h1, h2⟩ := GlobalTheory.Per.FontaineBound.ddR_finite_le ((PP l).PD K) hF π
  exact le_antisymm h2 (GlobalTheory.DRFil.finrank_mul_le_finrank_DdR_of_spans _ π h1 sw)

end Field

end UpperTheory.V.Loc

theorem UpperTheory.V.Loc.isCrys_isDR_internalHom :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] {V' : Type} [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V'] [IsScalarTower ℚ_[l] A V'] [FiniteDimensional ℚ_[l] V'] [TopologicalSpace V'] [IsModuleTopology ℚ_[l] V'] [IsTopologicalAddGroup V'] [ContinuousConstSMul A V'] {W : Type} [AddCommGroup W] [Module A W] [Module ℚ_[l] W] [IsScalarTower ℚ_[l] A W] [FiniteDimensional ℚ_[l] W] [TopologicalSpace W] [IsModuleTopology ℚ_[l] W] [IsTopologicalAddGroup W] [ContinuousConstSMul A W] (ρ : Representation A G V) (ρ' : Representation A G V') (π : Representation A G W), ContAction ρ → ContAction ρ' → ContAction π → ∀ b : W →ₗ[ℚ_[l]] V →ₗ[ℚ_[l]] V', (∀ g w x, b (π g w) (ρ g x) = ρ' g (b w x)) → Function.Injective b → (IsCr φ ρ → IsCr φ ρ' → IsCr φ π) ∧ (IsDr φ ρ → IsDr φ ρ' → IsDr φ π) := by
  intro l _ G _ _ _ φ hφ A _ _ V _ _ _ _ _ _ _ _ _ V' _ _ _ _ _ _ _ _ _ W _ _ _ _ _ _ _ _ _ ρ ρ' π _ _ _ b hb hi
  obtain ⟨K, e, -, -, rfl, -⟩ := openField φ hφ
  obtain ⟨f, hf, hfi⟩ := exists_inj_dual_tprod
    (resCoef ℚ_[l] (ρ.comp e.symm.toMonoidHom : Representation A ↥(GK K) V))
    (resCoef ℚ_[l] (ρ'.comp e.symm.toMonoidHom : Representation A ↥(GK K) V'))
    (resCoef ℚ_[l] (π.comp e.symm.toMonoidHom : Representation A ↥(GK K) W)) b
    (fun g w x => hb (e.symm g) w x) hi
  rw [(admissible_transport_equiv _ e ρ).1, (admissible_transport_equiv _ e ρ').1, (admissible_transport_equiv _ e π).1, (admissible_transport_equiv _ e ρ).2,
    (admissible_transport_equiv _ e ρ').2, (admissible_transport_equiv _ e π).2, (isCrIff K _).1, (isCrIff K _).1, (isCrIff K _).1,
    (isCrIff K _).2, (isCrIff K _).2, (isCrIff K _).2]
  exact ⟨crys_hom K _ _ _ f hf hfi, dR_hom K _ _ _ f hf hfi⟩
