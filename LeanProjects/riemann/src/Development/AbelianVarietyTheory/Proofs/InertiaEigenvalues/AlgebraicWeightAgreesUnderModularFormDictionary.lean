import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecProdRecSatakeLL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DefiniteUnitaryAutFormEqZeroOfFinitePoints
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDictionaryCmFieldAutomorphic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdelicExtensionOfAlgebraicWeightDefiniteUn
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ArchimedeanUnitaryPointsEquivUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitaryGroupFiniteDimensionalRepContainsHighestW
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightEqOfFinitePartNeBot
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyRep
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolynomialRepGLComplexAlgebraicWeightEvalPointStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHighestWeightVectorDualWeylModuleUpperStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DualWeylModuleIntertwinesGLOfUnitaryGroupStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open Matrix Topology Pointwise

noncomputable section

namespace GlobalTheory.WeightDict

theorem exists_pair_ne_zero {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (hρ : ρ.IsIrreducible) (hσ : σ.IsIrreducible)
    (B : V →ₗ[ℂ] W →ₗ[ℂ] ℂ) (hB0 : B ≠ 0) (hB : ∀ γ x y, B (ρ γ x) (σ γ y) = B x y) {x : V} (hx : x ≠ 0)
    {y : W} (hy : y ≠ 0) : ∃ γ, B (ρ γ x) y ≠ 0 := by
  by_contra hc
  push Not at hc
  let K : Subrepresentation ρ :=
    { toSubmodule :=
        { carrier := {w | ∀ γ, B (ρ γ w) y = 0}
          add_mem' := fun {a b} ha hb γ => by rw [map_add, map_add, LinearMap.add_apply, ha γ, hb γ, add_zero]
          zero_mem' := fun γ => by simp
          smul_mem' := fun c a ha γ => by rw [map_smul, map_smul, LinearMap.smul_apply, ha γ, smul_zero] }
      apply_mem_toSubmodule := fun g w hw γ => by
        have := hw (γ * g)
        rwa [map_mul] at this }
  let K' : Subrepresentation σ :=
    { toSubmodule := LinearMap.ker B.flip
      apply_mem_toSubmodule := fun g z hz => by
        rw [LinearMap.mem_ker] at hz ⊢
        ext w
        have h1 := hB g (ρ g⁻¹ w) z
        rw [Representation.self_inv_apply] at h1
        exact h1.trans (LinearMap.congr_fun hz _) }
  rcases hρ.eq_bot_or_eq_top K with h | h
  · have h1 : K.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h
    have h2 : x ∈ K.toSubmodule := hc
    rw [h1] at h2
    exact hx h2
  · have h1 : K.toSubmodule = ⊤ := congrArg Subrepresentation.toSubmodule h
    have hyK : y ∈ K'.toSubmodule := by
      change B.flip y = 0
      ext w
      have h2 : w ∈ K.toSubmodule := by rw [h1]; exact Submodule.mem_top
      have h3 : B (ρ 1 w) y = 0 := h2 1
      rw [map_one] at h3
      exact h3
    rcases hσ.eq_bot_or_eq_top K' with h' | h'
    · have h3 : K'.toSubmodule = ⊥ := congrArg Subrepresentation.toSubmodule h'
      rw [h3] at hyK
      exact hy hyK
    · have h3 : LinearMap.ker B.flip = ⊤ := congrArg Subrepresentation.toSubmodule h'
      refine hB0 (LinearMap.ext fun w => LinearMap.ext fun z => ?_)
      have h4 : z ∈ LinearMap.ker B.flip := by rw [h3]; exact Submodule.mem_top
      exact LinearMap.congr_fun (LinearMap.mem_ker.1 h4) w

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem coord_conjugate (τ : L →+* ℂ) (z : Cinf L) :
    coord (ComplexEmbedding.conjugate τ) z = starRingEnd ℂ (coord τ z) := by
  have hm : InfinitePlace.mk (ComplexEmbedding.conjugate τ) = InfinitePlace.mk τ := InfinitePlace.mk_conjugate_eq τ
  have hne : ComplexEmbedding.conjugate τ ≠ τ := fun h =>
    IsTotallyComplex.complexEmbedding_not_isReal τ (ComplexEmbedding.isReal_iff.2 h)
  rw [GlobalTheory.EmbUnitary.coord_eq, GlobalTheory.EmbUnitary.coord_eq, hm]
  unfold GlobalTheory.EmbUnitary.twist
  rw [hm]
  rcases InfinitePlace.embedding_mk_eq τ with h | h
  · rw [if_pos h, if_neg (by rw [h]; exact hne.symm)]
    rfl
  · rw [if_pos h, if_neg (by rw [h]; exact hne)]
    simp

theorem polyMat_embU {ι : Type} (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (τ : L →+* ℂ)
    (x : embU n τ) : GlobalTheory.WeightRealExt.polyMat P (x : UA L n) = GlobalTheory.AlgWtHW.evM P (NG.evPt τ (cEmb τ (x : UA L n))) := by
  ext i j
  change MvPolynomial.eval _ _ = MvPolynomial.eval _ _
  congr 2
  funext p
  obtain ⟨σ, s, t⟩ := p
  change (cEmb σ (x : UA L n)).val s t = _
  unfold NG.evPt
  dsimp only
  split_ifs with h1 h2 h3
  · rw [h1]
  · rw [h2]
    have hu := Matrix.mem_unitaryGroup_iff.1 (GlobalTheory.EmbUnitary.cEmb_mem τ (x : UA L n))
    rw [Units.inv_eq_of_mul_eq_one_right hu]
    exact coord_conjugate τ _
  all_goals
    have hk : InfinitePlace.mk σ ≠ InfinitePlace.mk τ := fun h => by
      rcases InfinitePlace.mk_eq_iff.1 h with h | h
      · exact h1 h
      · exact h2 (by rw [← h]; ext z; simp)
    have h4 := MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 x.2).2 σ) hk)
    rw [h4]
    simp [Matrix.one_apply, h3]

theorem pair_ext {W : Type} [AddCommGroup W] [Module ℂ W] {ρ : Representation ℂ (GQ L n) W} (a : NG.AlgWt L n)
    (R : UA L n →* Module.End ℂ W) (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = ρ γQ)
    (hcont : ∀ (v : W) (μ : Module.Dual ℂ W), Continuous fun g : UA L n => μ (R g v))
    (B : W →ₗ[ℂ] a.W →ₗ[ℂ] ℂ) (hB : ∀ γ x y, B (ρ γ x) (a.ρ γ y) = B x y)
    {ι : Type} [Fintype ι] [DecidableEq ι] (b : Module.Basis ι ℂ a.W)
    (P : ι → ι → MvPolynomial ((L →+* ℂ) × Fin n × Fin n) ℂ) (hP : GlobalTheory.AlgWtHW.Agrees a b P)
    (w : W) (c : ι → ℂ) (g : UA L n) :
    B (R g⁻¹ w) (b.equivFun.symm c) = B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) := by
  have h1 : Continuous fun g : UA L n => B (R g⁻¹ w) (b.equivFun.symm c) :=
    (hcont w (B.flip (b.equivFun.symm c))).comp continuous_inv
  have h2 : Continuous fun g : UA L n => B w (b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P g *ᵥ c)) :=
    (LinearMap.continuous_of_finiteDimensional (B w ∘ₗ b.equivFun.symm.toLinearMap)).comp
      ((GlobalTheory.WeightRealExt.continuous_polyMat P).matrix_mulVec continuous_const)
  refine congrFun (Continuous.ext_on GlobalTheory.WeightRealExt.dense_rat_fin h1 h2 fun z hz => ?_) g
  obtain ⟨γ, hγ, k, hk, rfl⟩ := Set.mem_mul.1 hz
  obtain ⟨γ₀, hγ₀⟩ := GlobalTheory.WeightRealExt.exists_unitaryRationalMatrix_of_mem_definiteUnitaryRational hγ
  have hR : R γ = ρ (GlobalTheory.WeightRealExt.ratPt γ₀) := hrat γ _ γ₀.1 hγ₀ rfl
  have hM : GlobalTheory.WeightRealExt.polyMat P (γ * k) = LinearMap.toMatrix b b (a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀)) := by
    have hk' : cInf k = 1 := hk
    rw [GlobalTheory.WeightRealExt.polyMat_congr P (g := γ * k) (h := γ) (by rw [map_mul, hk', mul_one]),
      GlobalTheory.WeightRealExt.polyMat_rat P γ γ₀.1 hγ₀]
    exact (hP _ γ₀.1 rfl).symm
  have e1 : b.equivFun.symm (GlobalTheory.WeightRealExt.polyMat P (γ * k) *ᵥ c) =
      a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀) (b.equivFun.symm c) := by
    rw [hM, LinearEquiv.symm_apply_eq]
    have := LinearMap.toMatrix_mulVec_repr b b (a.ρ (GlobalTheory.WeightRealExt.ratPt γ₀)) (b.equivFun.symm c)
    rw [← b.equivFun_apply, ← b.equivFun_apply, LinearEquiv.apply_symm_apply] at this
    exact this
  have e2 : ρ (GlobalTheory.WeightRealExt.ratPt γ₀) (R (γ * k)⁻¹ w) = w := by
    rw [_root_.mul_inv_rev, map_mul, hfin _ ((finU L n).inv_mem hk), one_mul, ← hR, ← Module.End.mul_apply, ← map_mul,
      mul_inv_cancel, map_one, Module.End.one_apply]
  change B (R (γ * k)⁻¹ w) _ = B w _
  rw [e1, ← hB (GlobalTheory.WeightRealExt.ratPt γ₀), e2]

theorem phi_mem {F : FinIso L n} {π : NG.AutRep L n} {U : Submodule ℂ (UA L n → ℂ)} (hU : Dict F π U)
    (R : UA L n →* Module.End ℂ π.W) (hfin : ∀ k ∈ finU L n, R k = 1)
    (hrat : ∀ (γ : UA L n) (γQ : GQ L n) (γ₀ : GL (Fin n) L), γ.1 = ratGL L n γ₀ →
      (((γQ : GAf L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
        (γ₀ : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom → R γ = π.ρ γQ)
    (hcont : ∀ (v : π.W) (μ : Module.Dual ℂ π.W), Continuous fun g : UA L n => μ (R g v))
    {f : GAf L n → π.W} (hf : f ∈ π.S) (μ : Module.Dual ℂ π.W) : GlobalTheory.FormDictEx.phi F R f μ ∈ U := by
  haveI : FiniteDimensional ℂ π.W := π.alg.1
  have hmem : (fun x => μ (f x)) ∈ U.map (LinearMap.funLeft ℂ ℂ F.j) := by
    rw [hU.2]
    exact Submodule.subset_span ⟨f, hf, μ, rfl⟩
  obtain ⟨u, hu, hue⟩ := hmem
  have ha : GlobalTheory.FormDictEx.phi F R f μ ∈ GlobalTheory.DefU.autU L n :=
    GlobalTheory.FormDictEx.isAutFormU_phi F π.ρ R hfin hrat hcont (π.irrS.1.le hf) μ
  have hu' : u ∈ GlobalTheory.DefU.autU L n := hU.1.aut u hu
  have h0 := GlobalTheory.DefiniteDense.eq_zero_of_finU L n _ ((GlobalTheory.DefU.autU L n).sub_mem ha hu') fun y hy => by
    obtain ⟨x, rfl⟩ := F.onto y hy
    rw [Pi.sub_apply, GlobalTheory.FormDictEx.phi_j F R hfin, sub_eq_zero]
    exact (congrFun hue x).symm
  rw [sub_eq_zero.1 h0]
  exact hu

theorem weight_agree : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (F : FinIso L n) (π : NG.AutRep L n)
    (U : Submodule ℂ (UA L n → ℂ)), Dict F π U → ∀ (a : NG.AlgWt L n), π.toAlgWt.IsDual a → ∀ τ : L →+* ℂ,
      ∃ lam, HasWeightAt U τ lam ∧ a.HWAt τ lam.w := by
  intro L _ _ _ n F π U hU a hdual τ
  obtain ⟨B, hB0, hB⟩ := hdual
  obtain ⟨R, hfin, hrat, hcont⟩ := GlobalTheory.WeightRealExt.exists_extension L n π.toAlgWt
  obtain ⟨_, ι, _, _, b, P, hP⟩ := a.alg
  obtain ⟨e, he⟩ := GlobalTheory.EmbUnitary.exists_equiv_unitaryGroup L n τ
  have hΦ := GlobalTheory.T.isPolynomialRepGLComplex_algebraicWeight_evalPoint L n a ι b P hP τ
  set Φ : GL (Fin n) ℂ → Matrix ι ι ℂ := fun A => GlobalTheory.AlgWtHW.evM P (NG.evPt τ A) with hΦd
  have hΦx : ∀ x : embU n τ, Φ (cEmb τ (x : UA L n)) = GlobalTheory.WeightRealExt.polyMat P (x : UA L n) := fun x =>
    (polyMat_embU P τ x).symm
  let σ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) (ι → ℂ) :=
    { toFun := fun u => Matrix.mulVecLin (Φ (GlobalTheory.Branching.unitaryIncl n u))
      map_one' := by
        rw [map_one, hΦ.one, Matrix.mulVecLin_one]
        rfl
      map_mul' := fun u u' => by
        rw [map_mul, hΦ.mul, Matrix.mulVecLin_mul]
        rfl }
  have hσc : ∀ (l : Module.Dual ℂ (ι → ℂ)) (v : ι → ℂ), Continuous fun u => l (σ u v) := by
    intro l v
    have h1 : ∀ u, σ u v = GlobalTheory.WeightRealExt.polyMat P (e.symm u : UA L n) *ᵥ v := fun u => by
      rw [← hΦx, ← he, e.apply_symm_apply]
      rfl
    simp only [h1]
    exact (LinearMap.continuous_of_finiteDimensional l).comp
      (((GlobalTheory.WeightRealExt.continuous_polyMat P).comp (continuous_subtype_val.comp e.symm.continuous)).matrix_mulVec
        continuous_const)
  haveI : Nontrivial a.W := by
    by_contra hs
    rw [not_nontrivial_iff_subsingleton] at hs
    exact hB0 (LinearMap.ext fun w => LinearMap.ext fun z => by rw [Subsingleton.elim z 0, map_zero, map_zero])
  haveI : Nontrivial (ι → ℂ) := b.equivFun.symm.toEquiv.nontrivial
  obtain ⟨lam, M₀, hM₀⟩ := GlobalTheory.UnitaryContainsType.exists_smallRep_intertwining n (ι → ℂ) σ hσc
  let M : nablaSq ℂ n lam →ₗ[ℂ] (ι → ℂ) := M₀.toLinearMap
  have hM := GlobalTheory.T.dualWeylModule_intertwines_GL_of_unitaryGroup n lam ι Φ hΦ M fun u v => Representation.IntertwiningMap.isIntertwining _ _ M₀ u v
  have hirr := GlobalTheory.DefU.isIrreducible_sqRep n lam
  have hinj : ∀ v, v ≠ 0 → M v ≠ 0 := by
    intro v hv hMv
    let K : Subrepresentation (GlobalTheory.Branching.sqRep ℂ n lam) :=
      { toSubmodule := LinearMap.ker M
        apply_mem_toSubmodule := fun g z hz => by
          rw [LinearMap.mem_ker] at hz ⊢
          rw [hM, hz, Matrix.mulVec_zero] }
    rcases hirr.eq_bot_or_eq_top K with h | h
    · have h1 : LinearMap.ker M = ⊥ := congrArg Subrepresentation.toSubmodule h
      exact hv (by rw [← Submodule.mem_bot ℂ, ← h1]; exact hMv)
    · have h1 : LinearMap.ker M = ⊤ := congrArg Subrepresentation.toSubmodule h
      exact hM₀ (Representation.IntertwiningMap.ext (LinearMap.ker_eq_top.1 h1))
  obtain ⟨v₀, hv₀, hw⟩ := GlobalTheory.T.exists_highest_weight_vector_dualWeylModule_upper n lam
  refine ⟨lam, ?_, ι, inferInstance, inferInstance, b, P, hP, M v₀, hinj v₀ hv₀, fun A hA => ?_⟩
  · obtain ⟨f, hf, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.irrS.2.1
    obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hf0 (funext h)
    refine ⟨hirr, GlobalTheory.FormDictEx.phiR F R f ∘ₗ B.flip ∘ₗ b.equivFun.symm.toLinearMap ∘ₗ M, fun h0 => ?_,
      fun v => phi_mem hU R hfin hrat hcont hf (B.flip (b.equivFun.symm (M v))), fun x v => ?_⟩
    · obtain ⟨γ, hγ⟩ := exists_pair_ne_zero π.irr a.irr B hB0 hB hx₀
        ((LinearEquiv.map_ne_zero_iff b.equivFun.symm).2 (hinj v₀ hv₀))
      apply hγ
      have h1 := congrFun (LinearMap.congr_fun h0 v₀) (F.j ((γ : GAf L n) * x₀))
      change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v₀))) _ = 0 at h1
      rw [GlobalTheory.FormDictEx.phi_j F R hfin, (π.irrS.1.le hf).1] at h1
      exact h1
    · change GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M (GlobalTheory.Branching.sqRep ℂ n lam (cEmb τ (x : UA L n)) v)))) =
        RU L n (x : UA L n) (GlobalTheory.FormDictEx.phi F R f (B.flip (b.equivFun.symm (M v))))
      rw [GlobalTheory.FormDictEx.RU_phi, GlobalTheory.FormDictEx.fy_inf F (Subgroup.mem_inf.1 x.2).1, GlobalTheory.FormDictEx.rt_one, hM, hΦx]
      congr 1
      exact LinearMap.ext fun w => (pair_ext a R hfin hrat hcont B hB b P hP w (M v) x).symm
  · have h1 := hM A v₀
    rw [hw A hA, map_smul] at h1
    exact h1.symm

end GlobalTheory.WeightDict

end
