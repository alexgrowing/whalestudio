import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentVectorsLocalizationLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationIndependentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameLocalizationSpansStatement

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
  TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult GlobalTheory.RealMult.Obj

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RealMult.Obj
open GlobalTheory.Serre GlobalTheory.FlatRow.EigLocal

theorem lieBaseChange_equiv : ∀ {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R R' : Type} [CommRing R]
    [CommRing R'] [Algebra R R'] {X : Obj F 𝔠 (Sp R)} {X' : Obj F 𝔠 (Sp R')}
    {φ : X'.A.left ⟶ X.A.left}, X'.IsPullBy X (spMap (algebraMap R R')) φ →
    ∃ e : R' ⊗[R] X.Lie ≃ₗ[R'] X'.Lie, ∀ v v', LieCorr (algebraMap R R') φ v v' ↔ v' = e (1 ⊗ₜ v) := by
  intro F _ _ 𝔠 R R' _ _ _ X X' φ h
  set f := algebraMap R R' with hf
  obtain ⟨ρ, hρ, -⟩ := exists_res h.grp X.rm X'.rm h.act
  letI : Module R X'.Lie := Module.compHom X'.Lie f
  haveI : IsScalarTower R R' X'.Lie := ⟨fun r s v => by
    show (r • s) • v = f r • (s • v)
    rw [Algebra.smul_def, mul_smul]⟩
  let ρR : X.Lie →ₗ[R] X'.Lie :=
    { toFun := ρ, map_add' := ρ.map_add, map_smul' := fun r v => ρ.map_smulₛₗ r v }
  let e₀ : R' ⊗[R] X.Lie →ₗ[R'] X'.Lie := LinearMap.liftBaseChange R' ρR
  have he₀ : ∀ (c : R') v, e₀ (c ⊗ₜ v) = c • ρ v := fun c v => by
    simp [e₀, ρR, LinearMap.liftBaseChange_tmul]
  have corr : ∀ v v', LieCorr f φ v v' ↔ v' = ρ v := fun v v' =>
    ⟨fun e => Serre.Lie.ext ((existsUnique_isVecOver h.grp.1 v.hom).unique e (hρ v)), fun e => e ▸ hρ v⟩
  have hsm := X.dim.smooth
  have hsm' := X'.dim.smooth

  have loc : ∀ (q : Ideal R') [q.IsPrime], (∀ z, e₀ z = 0 → ∃ u ∉ q, u • z = 0) ∧
      ∀ y, ∃ u ∉ q, u • y ∈ LinearMap.range e₀ := by
    intro q _
    let T := Localization.AtPrime q
    let gT := algebraMap R' T
    letI : GrpObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.grpObjObj
    haveI : IsCommMonObj ((Over.pullback (spMap gT)).obj X'.A) := Functor.isCommMonObj_obj
    have hq := isGrpPullback_pullback X'.A (spMap gT)
    obtain ⟨aq, haq⟩ := GlobalTheory.OActPull.exists_oAct_of_isGrpPullback X'.rm hq
    obtain ⟨ρq, hρq, -⟩ := exists_res hq X'.rm aq haq
    have hc : IsGrpPullback ((Over.pullback (spMap gT)).obj X'.A) X.A (spMap (gT.comp f))
        (pullback.fst X'.A.hom (spMap gT) ≫ φ) := by
      have := hq.comp h.grp
      rwa [spMap_comp_spMap] at this
    set p := q.comap f with hp
    obtain ⟨n, w₀, hw₀, hw⟩ := GlobalTheory.T.tangent_vectors_localization_lift X.A hsm p
    let w : Fin n → X.Lie := fun i => Serre.Lie.mk X.rm (w₀ i) (hw₀ i)
    have hmax : (IsLocalRing.maximalIdeal T).comap (gT.comp f) = p := by
      rw [← Ideal.comap_comap]
      exact congrArg (Ideal.comap f) (Localization.AtPrime.comap_maximalIdeal (I := q))
    have hB := GlobalTheory.T.tangent_frame_localization_spans hsm p w₀ hw T (gT.comp f) hmax _ _ hc
      (fun i => (ρq (ρ (w i))).hom) fun i => by
        have e1 := hρq (ρ (w i))
        have e2 := hρ (w i)
        unfold IsVecOver at e1 e2 ⊢
        rw [← Category.assoc, e1, Category.assoc, e2, ← Category.assoc, spMap_comp_spMap,
          ← Chart.dualMapR_comp]
        rfl
    rw [Serre.Lie.isLieBasis_iff] at hB
    refine ⟨fun z hz => ?_, fun y => ?_⟩
    ·
      have span : ∀ z : R' ⊗[R] X.Lie, ∃ s ∉ p, ∃ c : Fin n → R', f s • z = ∑ i, c i ⊗ₜ w i := by
        intro z
        induction z using TensorProduct.induction_on with
        | zero => exact ⟨1, p.primeCompl.one_mem, 0, by simp⟩
        | tmul r l =>
          obtain ⟨s, hs, hl⟩ := GlobalTheory.T.tangent_frame_localization_independent hsm X.rm p w (fun G' _ ψ hψ v hv => hw G' ψ hψ v hv) l
          obtain ⟨b, hb⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 hl
          refine ⟨s, hs, fun i => f (b i) * r, ?_⟩
          calc f s • (r ⊗ₜ[R] l) = (s • r) ⊗ₜ[R] l := by
                rw [TensorProduct.smul_tmul', smul_eq_mul, Algebra.smul_def]
            _ = r ⊗ₜ[R] (s • l) := TensorProduct.smul_tmul _ _ _
            _ = _ := by
                rw [← hb, TensorProduct.tmul_sum]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def]
        | add z₁ z₂ h₁ h₂ =>
          obtain ⟨s₁, hs₁, c₁, e₁⟩ := h₁
          obtain ⟨s₂, hs₂, c₂, e₂⟩ := h₂
          refine ⟨s₁ * s₂, p.primeCompl.mul_mem hs₁ hs₂, fun i => f s₂ * c₁ i + f s₁ * c₂ i, ?_⟩
          have e₃ : f (s₁ * s₂) • (z₁ + z₂) = f s₂ • (f s₁ • z₁) + f s₁ • (f s₂ • z₂) := by
            rw [map_mul, smul_add, smul_smul, smul_smul, mul_comm (f s₂)]
          rw [e₃, e₁, e₂]
          simp only [Finset.smul_sum, TensorProduct.smul_tmul', smul_eq_mul, TensorProduct.add_tmul,
            Finset.sum_add_distrib]
      obtain ⟨s, hs, c, hc⟩ := span z
      have h0 : ∑ i, c i • ρ (w i) = 0 := by
        have := congrArg e₀ hc
        rw [map_smul, hz, smul_zero, map_sum] at this
        simpa [he₀] using this.symm
      have h1 : Fintype.linearCombination T (fun i => ρq (ρ (w i))) (fun i => gT (c i)) = 0 := by
        have := congrArg ρq h0
        rw [map_sum, map_zero] at this
        simpa [Fintype.linearCombination_apply] using this
      have h2 : ∀ i, gT (c i) = 0 := fun i => by
        have := hB.1 (h1.trans (map_zero _).symm)
        exact congrFun this i
      choose u hu using fun i => (IsLocalization.map_eq_zero_iff q.primeCompl T (c i)).1 (h2 i)
      refine ⟨(∏ i, (u i : R')) * f s, q.primeCompl.mul_mem (q.primeCompl.prod_mem fun i _ => (u i).2) hs, ?_⟩
      rw [mul_smul, hc, Finset.smul_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [TensorProduct.smul_tmul', smul_eq_mul,
        ← Finset.mul_prod_erase _ _ (Finset.mem_univ i), mul_right_comm, hu i, zero_mul, TensorProduct.zero_tmul]
    ·
      obtain ⟨c, hcy⟩ := hB.2 (ρq y)
      obtain ⟨⟨t, ht⟩, hta⟩ := IsLocalization.exist_integer_multiples q.primeCompl (Finset.univ : Finset (Fin n)) c
      choose a ha using fun i => hta i (Finset.mem_univ i)
      have hx0 : ρq (t • y - ∑ i, a i • ρ (w i)) = 0 := by
        rw [map_sub, map_smulₛₗ, map_sum, ← hcy, Fintype.linearCombination_apply, Finset.smul_sum,
          ← Finset.sum_sub_distrib]
        refine Finset.sum_eq_zero fun i _ => ?_
        rw [map_smulₛₗ, smul_smul, ha i, Algebra.smul_def, sub_self]
      haveI := hsm'
      obtain ⟨r, hr, hrx⟩ := exists_smul_eq_zero X'.rm q (t • y - ∑ i, a i • ρ (w i)) (by
        have e1 := hρq (t • y - ∑ i, a i • ρ (w i))
        have e0 := hρq 0
        rw [hx0] at e1
        rw [map_zero] at e0
        unfold IsVecOver at e1 e0
        exact e1.symm.trans e0)
      refine ⟨r * t, q.primeCompl.mul_mem hr ht, ∑ i, (r * a i) ⊗ₜ w i, ?_⟩
      rw [smul_sub, sub_eq_zero, Finset.smul_sum] at hrx
      rw [map_sum]
      simp only [he₀]
      rw [mul_smul, hrx]
      simp only [smul_smul]
  refine ⟨LinearEquiv.ofBijective e₀ ⟨?_, ?_⟩, fun v v' => (corr v v').trans ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    exact eq_zero_of_loc fun q _ => (loc q).1 z hz
  · intro y
    have : Submodule.Quotient.mk (p := LinearMap.range e₀) y = 0 := eq_zero_of_loc fun q _ => by
      obtain ⟨u, hu, hm⟩ := (loc q).2 y
      exact ⟨u, hu, by rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]; exact hm⟩
    exact (Submodule.Quotient.mk_eq_zero _).1 this
  · show v' = ρ v ↔ v' = e₀ (1 ⊗ₜ v)
    rw [he₀, one_smul]
end GlobalTheory.RealMult.Obj
