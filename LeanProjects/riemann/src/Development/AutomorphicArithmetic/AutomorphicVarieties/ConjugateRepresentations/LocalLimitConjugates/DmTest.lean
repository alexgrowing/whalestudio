import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.CasimirResolventProjection
import Development.AutomorphicArithmetic.AutomorphicVarieties.ConjugateRepresentations.LocalLimitConjugates.TestOps
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.ArchimedeanCompact.GrpEqMemArchCompact
import GroundTheory.AutomorphicForms.AdelicDixmierMalliavinProduct
open NumberField Matrix MeasureTheory Filter Topology Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.GKCoh GlobalTheory.UnitaryBC UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible
open UpperTheory.V.Lit UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Bor UpperTheory.V.Lit.Dr
open scoped TensorProduct GlobalTheory.CuspRep.CuspidalL2GL
open UpperTheory.V.Cj UpperTheory.V.Cj.H

section

open GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

variable (E a) in
private noncomputable def spl : GA E a ≃ₜ* archGroup E a × GL (Fin a) (Af E) where
  toMulEquiv := (AdelicGLn.prodEquiv E a).toMulEquiv.trans
    (MulEquiv.prodCongr (archEquiv E a).toMulEquiv (MulEquiv.refl _))
  continuous_toFun := ((archEquiv E a).continuous.prodMap continuous_id).comp (AdelicGLn.prodEquiv E a).continuous
  continuous_invFun := (AdelicGLn.prodEquiv E a).symm.continuous.comp
    ((archEquiv E a).symm.continuous.prodMap continuous_id)

private theorem spl_symm (x : archGroup E a) (b : GL (Fin a) (Af E)) :
    (spl E a).symm (x, b) = finEmb E a b * infEmb E a x := by
  refine (AdelicGLn.prodEquiv E a).injective ?_
  rw [map_mul, prodEquiv_infEmb, prodEquiv_finEmb, Prod.mk_mul_mk, one_mul, mul_one]
  exact (AdelicGLn.prodEquiv E a).apply_symm_apply _

private theorem spl_fin (b : GL (Fin a) (Af E)) : (spl E a).symm (1, b) = finGL E a b := by
  rw [spl_symm, map_one, mul_one, UpperTheory.V.Fb.finEmb_eq]

private theorem arch_iff (φ : GA E a → ℂ) :
    IsArchSmooth φ ↔ ∀ b, (isExpLieAlgebra E a).IsSmoothFun fun x => φ ((spl E a).symm (x, b)) := by
  simp only [spl_symm]
  refine ⟨fun h b => h (finEmb E a b), fun h g => ?_⟩
  rw [← infEmb_mul_finEmb g, infEmb_mul_finEmb_comm, archSlice_mul]
  exact ((isExpLieAlgebra E a).leftTranslateEnd _ ⟨_, h _⟩).2

variable [IsTotallyComplex E]

private def stab (φ : Sm E a) : Subgroup (GL (Fin a) (Af E)) where
  carrier := {k | ∀ g, φ.1 (g * finGL E a k) = φ.1 g}
  one_mem' := fun g => by rw [map_one, mul_one]
  mul_mem' := fun {k l} hk hl g => by rw [map_mul, ← mul_assoc, hl, hk]
  inv_mem' := fun {k} hk g => by
    rw [← hk (g * finGL E a k⁻¹), mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one]

private theorem lev_iff (φ : Sm E a) : HasLev φ ↔ IsOpen (stab φ : Set (GL (Fin a) (Af E))) := by
  have : {k | act (.fin k) φ = φ} = (stab φ : Set (GL (Fin a) (Af E))) := by
    ext k
    exact ⟨fun h g => congrFun (congrArg Subtype.val h) g, fun h => Subtype.ext (funext h)⟩
  rw [HasLev, this]

private theorem smooth_of (φ : Sm E a) (h : HasLev φ) :
    ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ.1 := by
  have ho : IsOpen ((stab φ ⊓ AdelicGLn.integralFiniteGL E a : Subgroup (GL (Fin a) (Af E))) :
      Set (GL (Fin a) (Af E))) := ((lev_iff φ).1 h).inter (AdelicGLn.isOpen_integralFiniteGL E a)
  refine ⟨(arch_iff φ.1).1 (UpperTheory.V.Cm.isArchSmooth_of_mem φ.2), _, ho,
    (AdelicGLn.isCompact_integralFiniteGL E a).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) fun _ h => h.2,
    fun x v hv => ?_⟩
  rw [spl_fin]
  exact hv.1 x

private theorem test_of (φ : CompactlySupportedContinuousMap (GA E a) ℂ)
    (h : ProdSmooth.IsSmooth (isExpLieAlgebra E a) (spl E a) φ) : ∃ u : Sm E a, IsTest u ∧ u.1 = φ := by
  obtain ⟨h1, V, hV, -, h2⟩ := h
  refine ⟨⟨φ, UpperTheory.V.Cm.mem_Sm_of ((arch_iff _).2 h1)⟩, ⟨φ.hasCompactSupport, ?_⟩, rfl⟩
  rw [lev_iff]
  refine Subgroup.isOpen_mono (H₁ := V) (fun v hv g => ?_) hV
  rw [← spl_fin]
  exact h2 g v hv

end

theorem UpperTheory.V.Cj.H.dmTest :
    UpperTheory.V.Cj.H.DmTest := by
  intro E _ _ _ a μ _ f hf
  let F : CompactlySupportedContinuousMap (GA E a) ℂ := ⟨⟨f.1, ((testOps E a f).1 hf.2).1⟩, hf.1⟩
  obtain ⟨n, φ, ψ, h, e⟩ := GroundTheory.Automorphic.ProdSmooth.exists_sum_conv _ (spl E a) μ F (smooth_of f hf.2)
  choose u hu eu using fun i => test_of (φ i) (h i).1
  choose v hv ev using fun i => test_of (ψ i) (h i).2
  refine ⟨n, u, v, fun i => ⟨hu i, hv i⟩, funext fun x => ?_⟩
  have := congrArg (fun G : CompactlySupportedContinuousMap (GA E a) ℂ => G x) e
  simp only [CompactlySupportedContinuousMap.sum_apply, GroundTheory.Automorphic.conv_apply] at this
  rw [Finset.sum_apply]
  simp only [eu, ev]
  exact this
