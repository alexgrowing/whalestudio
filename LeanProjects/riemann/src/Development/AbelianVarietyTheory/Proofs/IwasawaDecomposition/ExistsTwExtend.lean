import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksChar

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 800000

namespace GlobalTheory.Mem.SJ.Place

theorem exists_tw_extend {H K X : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup K]
    [InnerProductSpace ℂ K] [AddCommGroup X] [Module ℂ X] (e : H →ₗ[ℂ] X) (V : Submodule ℂ X) (φ : V →ₗ⋆[ℂ] K) (z : ℂ) (s : Bool) :
    ∃ sE : Tw s H →ₗ⋆[ℂ] Tw s K, ∀ (x : Tw s H) (hx : e (Tw.out x) ∈ V), sE x = Tw.mk s (z • φ ⟨e (Tw.out x), hx⟩) := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend (p := V.comap e) (e.restrict (p := V.comap e) (q := V) fun _ h => h)
  refine ⟨{ toFun := fun x => Tw.mk s (z • φ (g (Tw.out x))), map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y
    show z • φ (g (Tw.out x + Tw.out y)) = z • φ (g (Tw.out x)) + z • φ (g (Tw.out y))
    rw [map_add, map_add, smul_add]
  · intro a x
    show z • φ (g (cj s a • Tw.out x)) = cj s (starRingEnd ℂ a) • z • φ (g (Tw.out x))
    rw [map_smul, map_smulₛₗ, cj_conj, smul_comm]
  · intro x hx
    have := LinearMap.congr_fun hg ⟨Tw.out x, hx⟩
    show Tw.mk s (z • φ (g (Tw.out x))) = _
    rw [show g (Tw.out x) = ⟨e (Tw.out x), hx⟩ from this]

theorem scale_norm {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℂ K] {c n a : ℝ} (hc : 0 < c) (hn : 0 < n) (y : K)
    (h : ‖y‖ ^ 2 = c * a) : n * ‖((1 : ℂ) * (((Real.sqrt (c * n))⁻¹ : ℝ) : ℂ)) • y‖ ^ 2 = a := by
  have hcn : 0 < c * n := mul_pos hc hn
  rw [one_mul, norm_smul, Complex.norm_real, mul_pow, h, Real.norm_eq_abs, sq_abs, inv_pow, Real.sq_sqrt hcn.le]
  field_simp

theorem sEEofTT_spec {D : D7} {S : D.what₂.Tau → Formalism.BasicNotions.TH.SPar} (M : DSModel (D.sp.Y 0) S) (μ : Measure (GA D (D.sp.Y 0)))
    (𝓕 : Set (GA D (D.sp.Y 0))) (E : Submodule ℂ (MMap M)) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (G : GoodOp X)
    (ι : GA D (D.sp.Y 0) ≃* X.B.I.GA) (t : GA D (D.sp.Y 0)) (c : ℝ) (h : EvalTieT M μ 𝓕 E X G ι t c) (T : E) :
    ‖sEEofTT M μ 𝓕 E X G ι t c T‖ ^ 2 = c * (ipM M μ 𝓕 (T : MMap M) (T : MMap M)).re ∧
      ((sEEofTT M μ 𝓕 E X G ι t c T : HHX X) : L2X X) ∈ goodSub X G := by
  have e : sEEofTT M μ 𝓕 E X G ι t c = (conjHH X G).toLinearMap.comp h.choose_spec.2.choose.toLinearMap := by
    unfold sEEofTT
    exact dif_pos h
  have e' : sEEofTT M μ 𝓕 E X G ι t c T = conjHH X G (h.choose_spec.2.choose T) := by
    rw [e]
    rfl
  rw [e']
  refine ⟨?_, (mem_EEC X G _).1 (h.choose_spec.2.choose T).2⟩
  rw [(conjHH X G).norm_map]
  exact (h.choose_spec.2.choose_spec T).2

theorem exists_placement : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (St : Formalism.L2.SG.HidaSetting.HidaSetting D) (Gd : GoodOp St) (ι : GA D (Yc D 0) ≃* St.B.I.GA) (t : GA D (Yc D 0)) (c : ℝ) (s : Bool), R.models_HE → 0 < c → EvalTieT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c → ∃ (κ : ℝ) (sE : Tw s R.HE.H →ₗ⋆[ℂ] Tw s (HHX St)), 0 < κ ∧ ∀ (x : Tw s R.HE.H) (hx : R.HE.e (Tw.out x) ∈ R.EEat (R.levR F true)), sE x = Tw.mk s (((1 : ℂ) * (κ : ℂ)) • sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) ∧ RealDat.nP F true * ‖sE x‖ ^ 2 = ‖x‖ ^ 2 ∧ ((Tw.out (sE x) : HHX St) : L2X St) ∈ goodSub St Gd := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F St Gd ι t c s hE hc h
  have hn : 0 < RealDat.nP F true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  obtain ⟨sE, hs⟩ := exists_tw_extend R.HE.e (R.EEat (R.levR F true))
    (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c)
    ((1 : ℂ) * (((Real.sqrt (c * RealDat.nP F true))⁻¹ : ℝ) : ℂ)) s
  refine ⟨(Real.sqrt (c * RealDat.nP F true))⁻¹, sE, inv_pos.2 (Real.sqrt_pos.2 (mul_pos hc hn)), fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := sEEofTT_spec (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c h ⟨R.HE.e (Tw.out x), hx⟩
  refine ⟨hs x hx, ?_, ?_⟩
  · rw [hs x hx]
    have hip : (ipM (R.MY 0) R.ν0 R.fd0 (R.HE.e (Tw.out x)) (R.HE.e (Tw.out x))).re = ‖Tw.out x‖ ^ 2 := by
      rw [← hE.2.2]
      exact (InnerProductSpace.norm_sq_eq_re_inner (𝕜 := ℂ) (Tw.out x)).symm
    have key := scale_norm (K := HHX St) hc hn
      (sEEofTT (R.MY 0) R.ν0 R.fd0 (R.EEat (R.levR F true)) St Gd ι t c ⟨R.HE.e (Tw.out x), hx⟩) (h1.trans (congrArg (c * ·) hip))
    exact key
  · rw [hs x hx]
    exact (goodSub St Gd).smul_mem _ h2

end GlobalTheory.Mem.SJ.Place
