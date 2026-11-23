import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedVectorEqOfStandardData
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTwIffCanonEq
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.InterlaceAll
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.JetsInIffStepField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermitianChartComplexRationalIntegralFormsStatement
import Formalism.LocalToGlobal.KernelLattices.ColumnData.DiagramFitsSourceRank
import Formalism.UnipotentAdelicQuotients.WeylLatDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolFunApply
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalTwSubK
import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.TiedRec
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IntegralityCompare

namespace GlobalTheory.Mem.SrcFunRead

open MvPolynomial

theorem map_twSubK_field {E K K' ι : Type} [Field E] [Field K] [Field K'] [Fintype ι] {n : ℕ} (t : ι → E →+* K)
    (M : GL (Fin n) E) (s : ι → ℤ) (P : MvPolynomial (ι × Fin n × Fin n) K) (φ : K →+* K') :
    map φ (twSubK t M s P) = twSubK (fun τ => φ.comp (t τ)) M s (map φ P) := by
  simp only [twSubK, map_mul, map_C, map_prod, map_zpow₀, RingHom.comp_apply]
  congr 1
  induction P using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p k hp => simp [hp]

theorem eq_of_eval_invertible {LL ι : Type} [Field LL] [Fintype ι] {n : ℕ} (e : LL →+* ℂ)
    {A B : MvPolynomial (ι × Fin n × Fin n) LL}
    (h : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ, (∀ τ, (y τ).det ≠ 0) →
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e A) =
        eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) (map e B)) : A = B := by
  classical
  let d : MvPolynomial (ι × Fin n × Fin n) ℂ :=
    ∏ τ, (Matrix.of fun a b : Fin n => (X (τ, a, b) : MvPolynomial (ι × Fin n × Fin n) ℂ)).det
  have hd : ∀ y : ι → Matrix (Fin n) (Fin n) ℂ,
      eval (fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2) d = ∏ τ, (y τ).det := by
    intro y
    simp only [d, map_prod]
    refine Finset.prod_congr rfl fun τ _ => ?_
    rw [RingHom.map_det]
    congr 1
    ext a b
    simp
  have hd0 : d ≠ 0 := by
    intro h0
    have h1 := hd (fun _ => 1)
    rw [h0] at h1
    simp at h1
  have hm : d * map e A = d * map e B := by
    apply MvPolynomial.funext
    intro x
    obtain ⟨y, rfl⟩ : ∃ y : ι → Matrix (Fin n) (Fin n) ℂ, x = fun k : ι × Fin n × Fin n => y k.1 k.2.1 k.2.2 :=
      ⟨fun τ a b => x (τ, a, b), rfl⟩
    rw [eval_mul, eval_mul, hd]
    by_cases hy : ∀ τ, (y τ).det ≠ 0
    · rw [h _ hy]
    · push_neg at hy
      obtain ⟨τ, hτ⟩ := hy
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) hτ, zero_mul, zero_mul]
  exact MvPolynomial.map_injective e e.injective (mul_left_cancel₀ hd0 hm)

end GlobalTheory.Mem.SrcFunRead

namespace GlobalTheory.Mem.SrcFunRead
open MvPolynomial

theorem srcFun_secC_read : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)),
    ∀ (Y : DivX (I.rec7 l Z)) (O : ∀ u a, GL3Theta.LiftObj (I.rec7 l Z) ((I.rec7 l Z).chTw u a)) (Pl : Examples₂.EntPl (I.rec7 l Z))
    (Bs : PlaceMatrixFamily (I.rec7 l Z)), I.QpIs Y.Qp → I.StdO l Z Y.Qp O → BasOk Pl O Bs →
    (∀ u a w, LevFree Y u a w → ∀ i, i ≤ B.R.m → ∀ c τ j k, ∃ x : (I.rec7 l Z).what₂.LL, Bs u a w i c τ j k = Pl.iL w x) →
    ∀ (u : B.Word) (μ : I.ι) (w : (I.rec7 l Z).what₂.places.Pl), LevFree Y u μ w → ∀ (i : ℕ) (hi : i < B.R.m)
    (eY : (I.chain l u μ).Y i ≃ Formalism.L2.Forms.Fr (I.rec7 l Z) i hi.le), I.IdY l Z u μ i hi.le eY →
    ∀ (c : (I.stp u μ i).Cl) (f : (I.chain l u μ).Y i → ℂ)
    (P0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) ℂ),
    (∀ z, f z = fnOf (gramC (gramN (I.rec7 l Z) i hi.le) (embT (I.rec7 l Z))) (shiftOf (lamTG (I.fm l u μ) i)) 1 P0 (eY z)) →
    ∀ (R0 : MvPolynomial ((I.rec7 l Z).what₂.Tau × Fin ((I.rec7 l Z).R.N i) × Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL),
    MvPolynomial.map (I.rec7 l Z).what₂.embLL R0 = P0 →
    ∀ (k : (I.rec7 l Z).what₂.Tau → ℕ),
    (∀ τ, (k τ : ℤ) = shiftOf (lamTG (I.fm l u μ) i) τ + ((I.rec7 l Z).chTw u μ).sSharp i τ) →
    ∀ (Bm : GL (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E)
    (g : (I.rec7 l Z).what₂.Tau → Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) ℂ_[(I.rec7 l Z).what₂.places.resChar w]),
    (∀ τ, Bs u μ w i c τ = (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) * g τ) →
    ∀ v : ValQ O u μ i, evC O u μ i v = f →
    srcFun Pl Bs u μ w i c (secC O u μ i v) = fun y =>
      (∏ τ, (g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ)) * ((∏ τ, (g τ * y τ).det ^ k τ) *
        polFun (MvPolynomial.map (Pl.iL w) (twSubK (Formalism.L2.G.Cmp.tEL (I.rec7 l Z)) Bm (shiftOf (lamTG (I.fm l u μ) i)) R0))
          (fun τ => g τ * y τ)) := by
  intro B X I hOk hPins l Z Y O Pl Bs hQp hStd hBas hEnt u μ w hLev i hi eY hId c f P0 hf R0 hR0 k hk Bm g hBs v hv

  have hPI : (secC O u μ i v : MvPolynomial (GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i)) (I.rec7 l Z).what₂.LL) *
      ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
      R0 * ∏ τ, frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ ^ k τ := by
    apply eq_of_eval_invertible (I.rec7 l Z).what₂.embLL
    intro y hy
    obtain ⟨z, hz⟩ : ∃ z : (I.chain l u μ).Y i, z.1 = y := by
      refine ⟨eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩, ?_⟩
      have h2 := hId (eY.symm ⟨y, fun τ => isUnit_iff_ne_zero.2 (hy τ)⟩)
      exact h2.symm.trans (congrArg Subtype.val (eY.apply_symm_apply _))
    have h1 : evP O u μ i (secC O u μ i v) z = f z :=
      (congrFun (evC_sec O u μ i v) z).symm.trans (congrFun hv z)
    rw [hf z] at h1
    have hfr : (O u μ).frm i z = y := (hStd.frm u μ i z).trans hz
    have hde : ∀ τ, ((I.rec7 l Z).chTw u μ).de i z τ = (y τ).det := fun τ =>
      ((O u μ).frm_de i hi.le z τ).trans (congrArg (fun M => (M τ).det) hfr)
    have hez : (eY z).1 = y := (hId z).trans hz
    simp only [evP, LinearMap.coe_mk, AddHom.coe_mk, fnOf, GL3Theta.evFr, hfr, hde, hez, Matrix.one_mul, Pi.one_apply] at h1
    rw [← hR0] at h1
    simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z)]
    have e1 : ∀ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ - twB (I.rec7 l Z) u μ i τ).toNat =
        (y τ).det ^ (-twB (I.rec7 l Z) u μ i τ) * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, Int.toNat_of_nonneg (sub_nonneg.2 (twLe (I.rec7 l Z) u μ i hi τ)), ← zpow_add₀ (hy τ)]
      congr 1
      ring
    have e2 : ∀ τ, (y τ).det ^ k τ =
        (y τ).det ^ shiftOf (lamTG (I.fm l u μ) i) τ * (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ) := by
      intro τ
      rw [← zpow_natCast, hk τ, zpow_add₀ (hy τ)]
    simp only [e1, e2, Finset.prod_mul_distrib]
    linear_combination (∏ τ, (y τ).det ^ (((I.rec7 l Z).chTw u μ).sSharp i τ)) * h1
  funext y
  simp only [srcFun, atBas, LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    LinearMap.mulRight_apply, Submodule.coe_subtype, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [hPI]
  have hφ : ∀ τ x, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) x = TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ x := by
    intro τ x
    have hx : (I.rec7 l Z).what₂.embLL (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ x) ∈ algebraicClosure ℚ ℂ := embLL_alg w _
    have he := Formalism.L2.G.Cmp.tEL_emb (I.rec7 l Z) τ x
    rw [RingHom.comp_apply, Pl.iL_lam' w _ hx]
    unfold TaylorLogMetric.tauEmb TaylorLogMetric.lamC
    rw [dif_pos (he ▸ hx)]
    exact congrArg (Pl.lam w) (Subtype.ext he)
  have hA : ∀ τ, (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      (TaylorLogMetric.tauEmb (I.rec7 l Z) (Pl.lam w) τ) =
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) := fun τ => by
    ext a b
    exact (hφ τ _).symm
  have hdetA : ∀ τ, ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))).det =
      ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det :=
    fun τ => (RingHom.map_det _ _).symm
  have ha : ∀ τ, ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ≠ 0 :=
    fun τ => ((Matrix.isUnits_det_units Bm).map _).ne_zero
  simp only [hBs, hA]
  rw [map_twSubK_field, polFun_apply, eval_twSubK _ _ _ _ (fun τ => g τ * y τ)]
  simp only [map_mul, map_prod, map_pow, eval_mul, eval_prod, eval_pow, eval_detP (D := I.rec7 l Z),
    Matrix.mul_assoc, Matrix.det_mul, hdetA]
  have hev : ∀ τ, eval (fun k : GL3Theta.FrV (I.rec7 l Z) ((I.rec7 l Z).R.N i) =>
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) k.1)) * (g k.1 * y k.1)) k.2.1 k.2.2)
      (MvPolynomial.map (Pl.iL w) (frDet (I.rec7 l Z).what₂.LL ((I.rec7 l Z).R.N i) τ)) =
      ((Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ)) * (g τ * y τ)).det :=
    fun τ => eval_detP (D := I.rec7 l Z) (Pl.iL w) (fun t =>
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).map
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) t)) * (g t * y t)) τ
  simp only [hev, Matrix.det_mul, hdetA]
  have hper : ∀ τ, (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det * (g τ).det) ^
          (-((I.rec7 l Z).chTw u μ).sSharp i τ) *
      (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
        (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det *
          ((g τ).det * (y τ).det)) ^ k τ =
      ((g τ).det ^ (-((I.rec7 l Z).chTw u μ).sSharp i τ) * ((g τ).det * (y τ).det) ^ k τ) *
        ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
          (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
            shiftOf (lamTG (I.fm l u μ) i) τ := by
    intro τ
    have h0 := ha τ
    rw [mul_zpow, mul_pow, ← zpow_natCast (((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det), hk τ,
      zpow_add₀ h0, _root_.zpow_neg]
    have h1 : ((Pl.iL w).comp (Formalism.L2.G.Cmp.tEL (I.rec7 l Z) τ))
      (Bm : Matrix (Fin ((I.rec7 l Z).R.N i)) (Fin ((I.rec7 l Z).R.N i)) (I.rec7 l Z).host.E).det ^
        (((I.rec7 l Z).chTw u μ).sSharp i τ) ≠ 0 := zpow_ne_zero _ h0
    field_simp
  rw [mul_left_comm, ← mul_assoc, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_congr rfl fun τ _ => hper τ,
    Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  ring

end GlobalTheory.Mem.SrcFunRead
