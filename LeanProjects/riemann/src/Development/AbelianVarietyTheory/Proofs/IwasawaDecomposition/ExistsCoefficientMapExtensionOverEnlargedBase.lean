import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOmPinsLev
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteFamilyCoefficientMapsMulRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CoefficientMapEnlargedBaseEqComplexMultipleStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCoefficientMapsAgreeRootOfUnityEnlargedStatement

set_option autoImplicit false

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.R3.Rw.OmCoef

theorem smul_eq_of_heq {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ a b : ℂ}
    (h1 : HEq x' (μ • y)) (h2 : HEq (a • x') (b • y)) : (a * μ) • y = b • y := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]
  exact eq_of_heq h2

theorem heq_smul {W W' : Type} [nW : NormedAddCommGroup W] [iW : InnerProductSpace ℂ W] [nW' : NormedAddCommGroup W']
    [iW' : InnerProductSpace ℂ W'] (hW : W' = W) (hn : HEq nW' nW) (hi : HEq iW' iW) {x' : W'} {y : W} {μ : ℂ}
    (h1 : HEq x' (μ • y)) (a : ℂ) : HEq (a • x') ((a * μ) • y) := by
  subst hW
  cases hn
  cases hi
  cases h1
  rw [mul_smul]

end GlobalTheory.Mem.R3.Rw.OmCoef

set_option maxHeartbeats 4000000 in

theorem GlobalTheory.Mem.R3.Rw.OmCoef.exists_coefFam_ext : ∀ {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'}
  {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl}
  (z : Dat (w.st Z) w.I hX T Wt), Enl0 B B' → HEq f' f → HEq w'.px w.px → z.Std →
  ∀ {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks (w'.st Z').toD7.what₂.LL] {Xg : Finset (Gc B' w'.px → B'.LL)} {tr : TrI B' w'.px}
    (R' : RealDat3 (w'.st Z').toD7 (famR (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) Ks)
    (cG' : G0 R'.Pg (w'.st Z').toD7.R.r ≃* G0g (w'.st Z').toD7.nd),
    Pins R' (face0 (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr) cG' → LevOf (w'.st Z') w'.I (usedOf w'.I T' Wt') R'.toLevCh →
    BrgStd (w'.st Z') w'.I hX' (usedOf w'.I T' Wt') Xg tr R'.toRealDat → RSideW z Wt' R' →
    ∀ (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m), (i : ℕ) = i' →
    ∀ c0L, GlobalTheory.Mem.R3.Rw.OmExt.CoefFam z.R.toRealDat c0L →
      (∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0) ∨
      ∃ c0L', GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L' ∧
        ∀ (v : Formalism.IndefR.FWT.VsV (w.st Z).toD7 i (w.st Z).toD7.what₂.LL) (v' : Formalism.IndefR.FWT.VsV (w'.st Z').toD7 i' (w'.st Z').toD7.what₂.LL),
          HEq (MvPolynomial.map (w'.st Z').toD7.what₂.embLL v'.1) (MvPolynomial.map (w.st Z).toD7.what₂.embLL v.1) → HEq (c0L' i' v') (c0L i v) := by
  intro B B' f f' T T' w w' Z Z' hX hX' Wt Wt' z hE hf hpx hstd Ks _ _ _ Xg tr R' cG' hP hL hB hR i i' hii c0L hc
  obtain ⟨g'', c0R'', c0L'', hT''⟩ := hP.char.base.fam.tie
  have hc'' : GlobalTheory.Mem.R3.Rw.OmExt.CoefFam R'.toRealDat c0L'' := ⟨g'', c0R'', hT''⟩
  by_cases h0 : ∀ x : (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.fam.amb.FL i
      (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0, x = 0
  · exact Or.inl h0
  right
  push_neg at h0
  obtain ⟨x, hx⟩ := h0
  obtain ⟨μ, hμ⟩ := GlobalTheory.T.coefficientMap_enlargedBase_eq_complexMultiple z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc''
  obtain ⟨v, v', u, u', n, n', hn, hun, hn', hun', hvv, hv0, hrel⟩ :=
    GlobalTheory.T.exists_coefficientMaps_agree_rootOfUnity_enlarged z hE hf hpx hstd R' cG' hP hL hB hR i i' hii c0L hc c0L'' hc'' x hx
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, hcv, -⟩ := hR
  obtain ⟨hW, -, hnW, hiW, -⟩ := hcv i i' hii
  have key := GlobalTheory.Mem.R3.Rw.OmCoef.smul_eq_of_heq (eq_of_heq hW) hnW hiW (hμ v v' hvv) hrel
  have hμe : (w'.st Z').toD7.what₂.embLL u' * μ = (w.st Z).toD7.what₂.embLL u := smul_left_injective ℂ hv0 key
  have hu0 : (w.st Z).toD7.what₂.embLL u ≠ 0 := (map_ne_zero _).2 fun h => by
    rw [h, zero_pow hn] at hun
    exact zero_ne_one hun
  obtain ⟨b, hb⟩ : (w.st Z).toD7.what₂.embLL u ∈ Set.range (w'.st Z').toD7.what₂.embLL := hE.2.2.2 ⟨u, rfl⟩
  have hb1 : b ^ n = 1 := (w'.st Z').toD7.what₂.embLL.injective (by rw [map_pow, hb, ← map_pow, hun, map_one, map_one])
  have ha : (u' * b⁻¹) ^ (n * n') = 1 := by
    have e1 : u' ^ (n * n') = 1 := by rw [mul_comm, pow_mul, hun', one_pow]
    have e2 : b ^ (n * n') = 1 := by rw [pow_mul, hb1, one_pow]
    rw [mul_pow, inv_pow, e1, e2, inv_one, mul_one]
  refine ⟨Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i'),
    GlobalTheory.T.definiteFamilyCoefficientMaps_mul_rootOfUnity R'.toRealDat c0L'' hc'' i' (u' * b⁻¹) (n * n') (mul_ne_zero hn hn') ha, fun v1 v1' h => ?_⟩
  have eu : Function.update c0L'' i' ((w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i') i' =
      (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) • c0L'' i' := Function.update_self _ _ _
  refine (heq_of_eq ((congrArg (fun g => g v1') eu).trans (LinearMap.smul_apply _ _ _))).trans ?_
  refine (GlobalTheory.Mem.R3.Rw.OmCoef.heq_smul (eq_of_heq hW) hnW hiW (hμ v1 v1' h) _).trans (heq_of_eq ?_)
  have e1 : (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = 1 := by
    calc (w'.st Z').toD7.what₂.embLL (u' * b⁻¹) * μ = ((w'.st Z').toD7.what₂.embLL u' * μ) * ((w.st Z).toD7.what₂.embLL u)⁻¹ := by
          rw [map_mul, map_inv₀, hb]; ring
      _ = 1 := by rw [hμe, mul_inv_cancel₀ hu0]
  rw [e1, one_smul]

end
