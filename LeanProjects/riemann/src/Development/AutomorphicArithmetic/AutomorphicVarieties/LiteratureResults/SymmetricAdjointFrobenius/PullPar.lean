import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.ArthurClozelDescent
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.InfinitesimalCharacterPullback.HasInfCharPullSub
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.AutomorphicForms.StrongApproximationSLDense

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 Formalism.L2.Host Formalism.L2.Host.CT GlobalTheory.CuspRep
open scoped ContDiff

namespace UpperTheory.V.Lit

section Comp

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E]

omit [IsTotallyReal E] in

private def zf (y : Af E) : Ad E := ((0, y) : InfiniteAdeleRing E × Af E)

omit [IsTotallyReal E] in
private theorem continuous_zf : Continuous (zf (E := E)) :=
  (continuous_const.prodMk continuous_id : Continuous fun y : Af E => ((0, y) : InfiniteAdeleRing E × Af E))

private theorem continuous_sInf : Continuous (TR.sInf E) :=
  ((TR.continuous_infEq E).prodMk continuous_const :
    Continuous fun x : TR.Rinf E => ((TR.infEq E x, 0) : InfiniteAdeleRing E × Af E))

private theorem continuous_pInf : Continuous (TR.pInf E) := by
  have h : Continuous (TR.infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

private theorem split (x : Ad E) : x = TR.sInf E (TR.pInf E x) + zf (pFin E x) :=
  Prod.ext (((TR.infEq E).apply_symm_apply _).symm.trans (add_zero _).symm) (zero_add _).symm

private theorem fin_kill (f : Ad E →+* Af E) (hf : Continuous f) (t : TR.Rinf E) : f (TR.sInf E t) = 0 := by
  refine FiniteAdeleRing.ext _ fun u => ?_
  have hc : Continuous fun t : TR.Rinf E => (f (TR.sInf E t)) u :=
    (RestrictedProduct.continuous_eval u).comp (hf.comp continuous_sInf)
  have h := (isPreconnected_range hc).subsingleton ⟨t, rfl⟩ ⟨0, rfl⟩
  simpa using h

omit [IsTotallyReal E] in

private theorem inf_kill (f : Ad E →+* ℝ) (hf : Continuous f) (y : Af E) : f (zf y) = 0 := by
  have h1 : f (zf 1) = 0 := by
    obtain ⟨C, hC⟩ := ((GroundTheory.Global.isCompact_integralFiniteAdeles E).image (hf.comp continuous_zf)).isBounded.exists_norm_le
    by_contra h0
    have hp : 0 < ‖f (zf 1)‖ := norm_pos_iff.2 h0
    obtain ⟨n, hn⟩ := exists_nat_gt (C / ‖f (zf 1)‖)
    have h2 := hC _ ⟨(n : Af E), natCast_mem _ n, rfl⟩
    have e : zf (n : Af E) = (n : Ad E) * zf 1 := Prod.ext (mul_zero _).symm (mul_one _).symm
    rw [Function.comp_apply, e, map_mul, map_natCast, norm_mul, Real.norm_natCast] at h2
    rw [div_lt_iff₀ hp] at hn
    linarith
  have e : zf y = zf y * zf 1 := Prod.ext (mul_zero _).symm (mul_one _).symm
  rw [e, map_mul, h1, mul_zero]

private theorem abs_pInf (x : E) (v : InfinitePlace E) : ‖TR.pInf E (algebraMap E (Ad E) x) v‖ = v x := by
  have : TR.pInf E (algebraMap E (Ad E) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
    change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap E (InfiniteAdeleRing E) x v) = _
    simp
  rw [this]
  exact InfinitePlace.norm_embedding_of_isReal _ _

private theorem ringHom_pi {ι : Type} [Finite ι] (g : (ι → ℝ) →+* ℝ) : ∃ v, ∀ t, g t = t v := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨v, hv⟩ : ∃ v, g (Pi.single v 1) ≠ 0 := by
    by_contra! h
    have h1 := map_sum g (fun v => Pi.single v (1 : ℝ)) Finset.univ
    rw [show ∑ v, Pi.single v (1 : ℝ) = (1 : ι → ℝ) from Finset.univ_sum_single (1 : ι → ℝ)] at h1
    simp [h] at h1
  refine ⟨v, fun t => mul_right_cancel₀ hv ?_⟩
  have e : t * Pi.single v 1 = algebraMap ℝ (ι → ℝ) (t v) * Pi.single v 1 := by
    funext u
    by_cases h : u = v <;> simp [h]
  have e2 : g (algebraMap ℝ (ι → ℝ) (t v)) = t v :=
    DFunLike.congr_fun (Subsingleton.elim (g.comp (algebraMap ℝ (ι → ℝ))) (RingHom.id ℝ)) (t v)
  rw [← map_mul, e, map_mul, e2]

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

private theorem pFin_ext (x : Ad E) : pFin E (s x) = finMap σ (pFin E x) := by
  have hf : Continuous ((pFin E).comp s) := continuous_snd.comp hs.1
  have h1 : ∀ x, pFin E (s x) = pFin E (s (zf (pFin E x))) := fun x => by
    conv_lhs => rw [split x, map_add, map_add]
    rw [show pFin E (s (TR.sInf E _)) = 0 from fin_kill _ hf _, zero_add]
  rw [h1]
  refine congrFun ((GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing E).equalizer
    (hf.comp continuous_zf) (continuous_finMap σ) (funext fun k => ?_)) _
  exact (h1 (algebraMap E (Ad E) k)).symm.trans ((congrArg (pFin E) (hs.2 k)).trans
    (FieldIso.finMap_algebraMap σ k).symm)

private theorem pInf_ext (x : Ad E) (w : InfinitePlace E) :
    TR.pInf E (s x) w = TR.pInf E x (w.comap (σ : E →+* E)) := by
  let f : Ad E →+* ℝ := (Pi.evalRingHom (fun _ => ℝ) w).comp ((TR.pInf E).comp s)
  have hf : Continuous f := (continuous_apply w).comp (continuous_pInf.comp hs.1)
  have h1 : ∀ x, f x = f (TR.sInf E (TR.pInf E x)) := fun x => by
    conv_lhs => rw [split x, map_add, inf_kill f hf, add_zero]
  let g : TR.Rinf E →+* ℝ :=
    { toFun := fun t => f (TR.sInf E t)
      map_one' := by
        have := h1 1
        rw [map_one, map_one] at this
        exact this.symm
      map_mul' := fun a b => by rw [map_mul, map_mul]
      map_zero' := by rw [map_zero, map_zero]
      map_add' := fun a b => by rw [map_add, map_add] }
  obtain ⟨v, hv⟩ := ringHom_pi g
  have h2 : ∀ x, TR.pInf E (s x) w = TR.pInf E x v := fun x => (h1 x).trans (hv _)
  have h3 : v = w.comap (σ : E →+* E) := by
    ext k
    have := h2 (algebraMap E (Ad E) k)
    rw [hs.2] at this
    rw [InfinitePlace.comap_apply, ← abs_pInf, ← abs_pInf, this]
  rw [h2, h3]

end Comp

section Pull

variable {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {a : ℕ}

omit [NumberField E] [IsTotallyReal E] in

private def rinf (σ : E ≃+* E) : TR.Rinf E →+* TR.Rinf E :=
  RingHom.pi fun u => Pi.evalRingHom (fun _ => ℝ) (u.comap (σ : E →+* E))

omit [IsTotallyReal E] in
variable (a) in

private def lieMap (σ : E ≃+* E) : TR.Lie E a →L[ℝ] TR.Lie E a :=
  LinearMap.toContinuousLinearMap
    { toFun := fun X i k => rinf σ (X i k)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }

variable {σ : E ≃+* E} {s : Ad E →+* Ad E} (hs : IsAdExt (σ : E →+* E) s)
include hs

private theorem pInf_map (g : GA E a) : GeneralLinearGroup.map (TR.pInf E) (GeneralLinearGroup.map s g) =
    GeneralLinearGroup.map (rinf σ) (GeneralLinearGroup.map (TR.pInf E) g) :=
  Units.ext (Matrix.ext fun _ _ => funext fun w => pInf_ext hs _ w)

private theorem pFin_map (g : GA E a) : GeneralLinearGroup.map (pFin E) (GeneralLinearGroup.map s g) =
    GeneralLinearGroup.map (finMap σ) (GeneralLinearGroup.map (pFin E) g) :=
  Units.ext (Matrix.ext fun _ _ => pFin_ext hs _)

private theorem map_infGL (y : GL (Fin a) (TR.Rinf E)) :
    GeneralLinearGroup.map s (TR.infGL E a y) = TR.infGL E a (GeneralLinearGroup.map (rinf σ) y) :=
  TR.ga_ext (by rw [pInf_map hs, TR.pInf_infGL, TR.pInf_infGL])
    (by rw [pFin_map hs, TR.pFin_infGL, TR.pFin_infGL, map_one])

private theorem chart_map (φ : GA E a → ℂ) (g : GA E a) {x : TR.Lie E a} (hx : x ∈ TR.invSet E a) :
    TR.chart (fun g => φ (GeneralLinearGroup.map s g)) g x = TR.chart φ (GeneralLinearGroup.map s g) (lieMap a σ x) ∧
      lieMap a σ x ∈ TR.invSet E a := by
  obtain ⟨u, hu⟩ := id hx
  obtain rfl : x = TR.toL u.val := hu.symm
  have e : lieMap a σ (TR.toL u.val) = TR.toL (GeneralLinearGroup.map (rinf σ) u).val := rfl
  rw [e, TR.chart_val, TR.chart_val, map_mul, map_infGL hs]
  exact ⟨rfl, TR.val_mem_invSet _⟩

variable (a) in

private def pl : TR.Sm E a →ₗ[ℂ] TR.Sm E a where
  toFun φ := ⟨fun g => φ.1 (GeneralLinearGroup.map s g), fun g =>
    ((φ.2 (GeneralLinearGroup.map s g)).comp (lieMap a σ).contDiff.contDiffOn
      fun _ hx => (chart_map hs φ.1 g hx).2).congr fun _ hx => (chart_map hs φ.1 g hx).1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

end Pull

end UpperTheory.V.Lit
