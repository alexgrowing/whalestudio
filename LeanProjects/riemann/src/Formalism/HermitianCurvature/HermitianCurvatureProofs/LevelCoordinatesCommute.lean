import Formalism.HermitianCurvature.StatementNF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.ActualAdjointnessFromHermitian
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SumDualVectorEqZeta
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WeylCellConjTransposeMulApply
import Formalism.FormalDegreeBessel.FinalWR

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFx1.APL

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section Pair

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem mkPair_mul_mkPair (a b c d : Module.End ℂ V) : mkP a b * mkP c d = mkP (a * c) (d * b) := rfl
theorem mkPair_add_mkPair (a b c d : Module.End ℂ V) : mkP a b + mkP c d = mkP (a + c) (b + d) := rfl
theorem mkPair_sub_mkPair (a b c d : Module.End ℂ V) : mkP a b - mkP c d = mkP (a - c) (b - d) := rfl
theorem one_eq_mkPair : (1 : Pr V) = mkP 1 1 := rfl
theorem mkPair_inj (a b c d : Module.End ℂ V) : mkP a b = mkP c d ↔ a = c ∧ b = d := by
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg (fun p : Module.End ℂ V × (Module.End ℂ V)ᵐᵒᵖ => MulOpposite.unop p.2) h⟩
  · rintro ⟨rfl, rfl⟩
    rfl
theorem algebraMap_Pr (s : ℂ) :
    algebraMap ℂ (Pr V) s = mkP (algebraMap ℂ (Module.End ℂ V) s) (algebraMap ℂ (Module.End ℂ V) (starRingEnd ℂ s)) := rfl

end Pair

section Ops

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem slice_wsm {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') (g : Mx k r) :
    (fun c' => Φ c' g) ∈ WSm r (Wq →L[ℂ] Wp) := by
  by_cases hg : g ∈ Glev k r (Fin.last r) ∧ 0 < GGl k r z z' g
  · show ContDiffOn ℝ ∞ (fun c' => Φ c' g) (OmX r) ∧ ∀ x, x ∉ OmX r → Φ x g = 0
    refine ⟨fun c hc => ?_, fun c hc => hΦ.1 (c, g) (fun h => hc h.1)⟩
    obtain ⟨U, F, hU, hxU, hF, hΦF⟩ := hΦ.2.1 (c, g) ⟨hc, hg.1, hg.2⟩
    have hcd : ContDiffAt ℝ ∞ (fun c' : Fin r → ℂ => F (c', g)) c :=
      (hF.contDiffAt (hU.mem_nhds hxU)).comp c (contDiffAt_id.prodMk contDiffAt_const)
    have hev : (fun c' => Φ c' g) =ᶠ[𝓝 c] fun c' => F (c', g) := by
      filter_upwards [Qx5.eventually_slice (x := (c, g)) hU hxU] with c' hc'
      exact hΦF (c', g) hc' hg.1
    exact (hcd.congr_of_eventuallyEq hev).contDiffWithinAt
  · rw [Qx5.slice_zero hΦ hg]
    exact (WSm r _).zero_mem

theorem end_ext {A B : Module.End ℂ (RadSp k r z z' π π')}
    (h : ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) = (B Φ : Fn k r (Wq →L[ℂ] Wp))) :
    A = B := LinearMap.ext fun Φ => Subtype.ext (h Φ)

variable (X : ActualOps k r z z' π π')

theorem op_coe (l : Fin r) (i : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.op l i Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => opL l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c := X.op_apply l i Φ

theorem opop_coe (l m : Fin r) (i j : Fin 6) (Φ : RadSp k r z z' π π') :
    (((X.op l i * X.op m j) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => opL l i (opL m j (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g)) c := (op_coe X l i (X.op m j Φ)).trans (by rw [op_coe X m j])

theorem fn_coe (j : Fin 6) (Φ : RadSp k r z z' π π') :
    ((X.fn j Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => fnVal k r z z' j g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g := by
  funext c g
  show _ = fnVal k r z z' j g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · exact X.fn_apply j Φ (c, g) hx
  · obtain ⟨h1, -, -⟩ := (X.fn j Φ).2
    obtain ⟨h2, -, -⟩ := Φ.2
    have e1 : (X.fn j Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h1 (c, g) hx
    have e2 : (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h2 (c, g) hx
    rw [e1, e2, smul_zero]

end Ops

section Ids

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable (X : ActualOps k r z z' π π')

theorem end_of_slices {A B : Module.End ℂ (RadSp k r z z' π π')}
    (RA RB : ((Fin r → ℂ) → (Wq →L[ℂ] Wp)) → (Fin r → ℂ) → (Wq →L[ℂ] Wp))
    (hA : ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => RA (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c)
    (hB : ∀ Φ : RadSp k r z z' π π', ((B Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => RB (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) c)
    (h : ∀ f ∈ WSm r (Wq →L[ℂ] Wp), RA f = RB f) : A = B := by
  refine end_ext fun Φ => ?_
  rw [hA Φ, hB Φ]
  funext c g
  exact congrFun (h _ (slice_wsm Φ.2 g)) c

theorem coe_add (A B : Module.End ℂ (RadSp k r z z' π π')) (Φ : RadSp k r z z' π π') :
    (((A + B) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (A Φ : Fn k r (Wq →L[ℂ] Wp)) c g + (B Φ : Fn k r (Wq →L[ℂ] Wp)) c g := rfl

theorem coe_sub (A B : Module.End ℂ (RadSp k r z z' π π')) (Φ : RadSp k r z z' π π') :
    (((A - B) Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
      fun c g => (A Φ : Fn k r (Wq →L[ℂ] Wp)) c g - (B Φ : Fn k r (Wq →L[ℂ] Wp)) c g := rfl

theorem weyl_pc (l : Fin r) : X.op l 0 * X.op l 1 = X.op l 1 * X.op l 0 + X.op l 1 := by
  refine end_of_slices (fun f => opL l 0 (opL l 1 f)) (fun f => opL l 1 (opL l 0 f) + opL l 1 f) (fun Φ => opop_coe X l l 0 1 Φ) (fun Φ => ?_) (fun f hf => (weylFun r _ l f hf).2.2.1)
  rw [coe_add, opop_coe X l l 1 0 Φ, op_coe X l 1 Φ] <;> rfl

theorem weyl_pbcb (l : Fin r) : X.op l 3 * X.op l 4 = X.op l 4 * X.op l 3 + X.op l 4 := by
  refine end_of_slices (fun f => opL l 3 (opL l 4 f)) (fun f => opL l 4 (opL l 3 f) + opL l 4 f) (fun Φ => opop_coe X l l 3 4 Φ) (fun Φ => ?_) (fun f hf => (weylFun r _ l f hf).2.2.2.2.2)
  rw [coe_add, opop_coe X l l 4 3 Φ, op_coe X l 4 Φ] <;> rfl

theorem fun_pci (l : Fin r) {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (hf : f ∈ WSm r (Wq →L[ℂ] Wp)) :
    pOp l (ciOp l f) = ciOp l (pOp l f) - ciOp l f := by
  have hg : ciOp l f ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 2 f hf
  have hpg : pOp l (ciOp l f) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 0 _ hg
  have hcpg : cOp l (pOp l (ciOp l f)) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 1 _ hpg
  have w1 := (weylFun r _ l _ hg).2.2.1
  have w2 := (weylFun r _ l f hf).1
  have w3 : ciOp l (cOp l (pOp l (ciOp l f))) = pOp l (ciOp l f) := (weylFun r _ l _ hpg).2.1
  have hadd : ciOp l (cOp l (pOp l (ciOp l f)) + f) = ciOp l (cOp l (pOp l (ciOp l f))) + ciOp l f :=
    (linOps r _ l 2 _ f 1 hcpg hf).1
  rw [w2] at w1
  rw [w1, hadd, w3, add_sub_cancel_right]

theorem weyl_pci (l : Fin r) : X.op l 0 * X.op l 2 = X.op l 2 * X.op l 0 - X.op l 2 := by
  refine end_of_slices (fun f => opL l 0 (opL l 2 f)) (fun f => opL l 2 (opL l 0 f) - opL l 2 f) (fun Φ => opop_coe X l l 0 2 Φ) (fun Φ => ?_) (fun f hf => fun_pci l hf)
  rw [coe_sub, opop_coe X l l 2 0 Φ, op_coe X l 2 Φ] <;> rfl

private theorem pbOp_cbiOp_eq_cbiOp_pbOp_sub (l : Fin r) {f : (Fin r → ℂ) → (Wq →L[ℂ] Wp)} (hf : f ∈ WSm r (Wq →L[ℂ] Wp)) :
    pbOp l (cbiOp l f) = cbiOp l (pbOp l f) - cbiOp l f := by
  have hg : cbiOp l f ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 5 f hf
  have hpg : pbOp l (cbiOp l f) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 3 _ hg
  have hcpg : cbOp l (pbOp l (cbiOp l f)) ∈ WSm r (Wq →L[ℂ] Wp) := presOps r _ l 4 _ hpg
  have w1 := (weylFun r _ l _ hg).2.2.2.2.2
  have w2 := (weylFun r _ l f hf).2.2.2.1
  have w3 : cbiOp l (cbOp l (pbOp l (cbiOp l f))) = pbOp l (cbiOp l f) := (weylFun r _ l _ hpg).2.2.2.2.1
  have hadd : cbiOp l (cbOp l (pbOp l (cbiOp l f)) + f) = cbiOp l (cbOp l (pbOp l (cbiOp l f))) + cbiOp l f :=
    (linOps r _ l 5 _ f 1 hcpg hf).1
  rw [w2] at w1
  rw [w1, hadd, w3, add_sub_cancel_right]

theorem weyl_pbcbi (l : Fin r) : X.op l 3 * X.op l 5 = X.op l 5 * X.op l 3 - X.op l 5 := by
  refine end_of_slices (fun f => opL l 3 (opL l 5 f)) (fun f => opL l 5 (opL l 3 f) - opL l 5 f) (fun Φ => opop_coe X l l 3 5 Φ) (fun Φ => ?_) (fun f hf => pbOp_cbiOp_eq_cbiOp_pbOp_sub l hf)
  rw [coe_sub, opop_coe X l l 5 3 Φ, op_coe X l 5 Φ] <;> rfl

theorem comm_ops (l m : Fin r) (i j : Fin 6) (h : l ≠ m ∨ (holoIdx i ↔ ¬ holoIdx j)) :
    X.op l i * X.op m j = X.op m j * X.op l i := end_of_slices (fun f => opL l i (opL m j f)) (fun f => opL m j (opL l i f))
    (fun Φ => opop_coe X l m i j Φ) (fun Φ => opop_coe X m l j i Φ) (fun f hf => commFun r _ l m i j f hf h)

theorem inv_ops (l : Fin r) : X.op l 1 * X.op l 2 = 1 ∧ X.op l 2 * X.op l 1 = 1 ∧
    X.op l 4 * X.op l 5 = 1 ∧ X.op l 5 * X.op l 4 = 1 := ⟨end_of_slices (A := X.op l 1 * X.op l 2) (B := 1) (fun f => opL l 1 (opL l 2 f)) (fun f => f)
      (fun Φ => opop_coe X l l 1 2 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).1),
    end_of_slices (A := X.op l 2 * X.op l 1) (B := 1) (fun f => opL l 2 (opL l 1 f)) (fun f => f)
      (fun Φ => opop_coe X l l 2 1 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.1),
    end_of_slices (A := X.op l 4 * X.op l 5) (B := 1) (fun f => opL l 4 (opL l 5 f)) (fun f => f)
      (fun Φ => opop_coe X l l 4 5 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.2.2.1),
    end_of_slices (A := X.op l 5 * X.op l 4) (B := 1) (fun f => opL l 5 (opL l 4 f)) (fun f => f)
      (fun Φ => opop_coe X l l 5 4 Φ) (fun Φ => rfl) (fun f hf => (weylFun r _ l f hf).2.2.2.2.1)⟩

theorem op_fn (l : Fin r) (i j : Fin 6) : X.op l i * X.fn j = X.fn j * X.op l i := by
  refine end_ext fun Φ => ?_
  have e1 := op_coe X l i (X.fn j Φ)
  have e2 := fn_coe X j (X.op l i Φ)
  rw [fn_coe X j Φ] at e1
  rw [op_coe X l i Φ] at e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  funext c g
  have := (linOps r _ l i (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g) 0 (fnVal k r z z' j g) (slice_wsm Φ.2 g)
    (WSm r _).zero_mem).2
  exact congrFun this c

def multiplicationOperator (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ) : Prop :=
  ∀ Φ : RadSp k r z z' π π', ((A Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) =
    fun c g => a c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g

theorem multiplicationOperator.comm {A B : Module.End ℂ (RadSp k r z z' π π')} {a b : (Fin r → ℂ) → Mx k r → ℂ}
    (hA : multiplicationOperator A a) (hB : multiplicationOperator B b) : A * B = B * A := by
  refine end_ext fun Φ => ?_
  have e1 := hA (B Φ)
  have e2 := hB (A Φ)
  rw [hB Φ] at e1
  rw [hA Φ] at e2
  refine e1.trans (Eq.trans ?_ e2.symm)
  funext c g
  exact smul_comm (a c g) (b c g) _

theorem multiplicationOperator.one {A B : Module.End ℂ (RadSp k r z z' π π')} {a b : (Fin r → ℂ) → Mx k r → ℂ}
    (hA : multiplicationOperator A a) (hB : multiplicationOperator B b) (h : ∀ c g, (c, g) ∈ DomR k r z z' → a c g * b c g = 1) : A * B = 1 := by
  refine end_ext fun Φ => ?_
  have e1 := hA (B Φ)
  rw [hB Φ] at e1
  refine e1.trans ?_
  funext c g
  show a c g • b c g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · rw [smul_smul, h c g hx, one_smul]
  · obtain ⟨h0, -, -⟩ := Φ.2
    have e : (Φ : Fn k r (Wq →L[ℂ] Wp)) c g = 0 := h0 (c, g) hx
    rw [e, smul_zero, smul_zero]

theorem mul_fn (j : Fin 6) : multiplicationOperator (X.fn j) (fun _ g => fnVal k r z z' j g) := fun Φ => fn_coe X j Φ
theorem mul_c (l : Fin r) : multiplicationOperator (X.op l 1) (fun c _ => c l) := fun Φ => op_coe X l 1 Φ
theorem mul_ci (l : Fin r) : multiplicationOperator (X.op l 2) (fun c _ => (c l)⁻¹) := fun Φ => op_coe X l 2 Φ
theorem mul_cb (l : Fin r) : multiplicationOperator (X.op l 4) (fun c _ => star (c l)) := fun Φ => op_coe X l 4 Φ
theorem mul_cbi (l : Fin r) : multiplicationOperator (X.op l 5) (fun c _ => (star (c l))⁻¹) := fun Φ => op_coe X l 5 Φ

theorem fn_inv (hT : 0 ≤ Tz k r z * Tz k r z') :
    X.fn 0 * X.fn 1 = 1 ∧ X.fn 1 * X.fn 0 = 1 ∧ X.fn 2 * X.fn 3 = 1 ∧ X.fn 3 * X.fn 2 = 1 ∧
    X.fn 4 * X.fn 5 = 1 ∧ X.fn 5 * X.fn 4 = 1 := by
  have hz : ∀ g, 0 < GGl k r z z' g → zetaL k r z z' (Fin.last r) g ≠ 0 := fun g hg => Qx5.zeta_ne hT hg
  have hzb : ∀ g, 0 < GGl k r z z' g → star (zetaL k r z z' (Fin.last r) g) ≠ 0 :=
    fun g hg => star_ne_zero.2 (hz g hg)
  have hG : ∀ g, 0 < GGl k r z z' g → ((GGl k r z z' g : ℝ) : ℂ) ≠ 0 :=
    fun g hg => Complex.ofReal_ne_zero.2 hg.ne'
  refine ⟨(mul_fn X 0).one (mul_fn X 1) fun c g hx => ?_, (mul_fn X 1).one (mul_fn X 0) fun c g hx => ?_,
    (mul_fn X 2).one (mul_fn X 3) fun c g hx => ?_, (mul_fn X 3).one (mul_fn X 2) fun c g hx => ?_,
    (mul_fn X 4).one (mul_fn X 5) fun c g hx => ?_, (mul_fn X 5).one (mul_fn X 4) fun c g hx => ?_⟩
  · exact mul_inv_cancel₀ (hz g hx.2.2)
  · exact inv_mul_cancel₀ (hz g hx.2.2)
  · exact mul_inv_cancel₀ (hzb g hx.2.2)
  · exact inv_mul_cancel₀ (hzb g hx.2.2)
  · exact mul_inv_cancel₀ (hG g hx.2.2)
  · exact inv_mul_cancel₀ (hG g hx.2.2)

theorem fn_GG : X.fn 4 = X.fn 0 * X.fn 2 - algebraMap ℂ (Module.End ℂ (RadSp k r z z' π π'))
    ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  refine end_ext fun Φ => ?_
  rw [coe_sub, Module.End.mul_apply, fn_coe, fn_coe, fn_coe, Module.algebraMap_end_apply]
  funext c g
  show fnVal k r z z' 4 g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g =
    fnVal k r z z' 0 g • fnVal k r z z' 2 g • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g -
      ((Tz k r z * Tz k r z' : ℝ) : ℂ) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g
  rw [smul_smul, ← sub_smul]
  congr 1
  simp only [fnVal, GGl, Complex.mul_conj, Complex.ofReal_sub, Complex.ofReal_mul, Complex.star_def]

end Ids

section Pre

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}
variable (X : ActualOps k r z z' π π')

theorem hol_03 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_04 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (4 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_05 : holoIdx (0 : Fin 6) ↔ ¬ holoIdx (5 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_31 : holoIdx (3 : Fin 6) ↔ ¬ holoIdx (1 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_32 : holoIdx (3 : Fin 6) ↔ ¬ holoIdx (2 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_13 : holoIdx (1 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_23 : holoIdx (2 : Fin 6) ↔ ¬ holoIdx (3 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_40 : holoIdx (4 : Fin 6) ↔ ¬ holoIdx (0 : Fin 6) := by
  unfold holoIdx
  decide
theorem hol_50 : holoIdx (5 : Fin 6) ↔ ¬ holoIdx (0 : Fin 6) := by
  unfold holoIdx
  decide

theorem pair_comm {x y : Pr (RadSp k r z z' π π')}
    (hx : ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ x = mkP A B)
    (hy : ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ y = mkP A B) : x * y = y * x := by
  obtain ⟨A, a, B, b, hA, hB, rfl⟩ := hx
  obtain ⟨C, c, D, d, hC, hD, rfl⟩ := hy
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, multiplicationOperator.comm hA hC, multiplicationOperator.comm hD hB]

theorem mulPair_of_mem (w : Pr (RadSp k r z z' π π'))
    (hw : w ∈ Set.range (fun l => mkP (X.op l 1) (X.op l 4)) ∪ Set.range (fun l => mkP (X.op l 2) (X.op l 5)) ∪
      Set.range (fun l => mkP (X.op l 4) (X.op l 1)) ∪ Set.range (fun l => mkP (X.op l 5) (X.op l 2)) ∪
      {mkP (X.fn 0) (X.fn 2), mkP (X.fn 1) (X.fn 3), mkP (X.fn 2) (X.fn 0), mkP (X.fn 3) (X.fn 1),
        mkP (X.fn 4) (X.fn 4), mkP (X.fn 5) (X.fn 5)}) :
    ∃ (A : Module.End ℂ (RadSp k r z z' π π')) (a : (Fin r → ℂ) → Mx k r → ℂ)
      (B : Module.End ℂ (RadSp k r z z' π π')) (b : (Fin r → ℂ) → Mx k r → ℂ),
      multiplicationOperator A a ∧ multiplicationOperator B b ∧ w = mkP A B := by
  rcases hw with ((((⟨l, rfl⟩ | ⟨l, rfl⟩) | ⟨l, rfl⟩) | ⟨l, rfl⟩) | hw)
  · exact ⟨_, _, _, _, mul_c X l, mul_cb X l, rfl⟩
  · exact ⟨_, _, _, _, mul_ci X l, mul_cbi X l, rfl⟩
  · exact ⟨_, _, _, _, mul_cb X l, mul_c X l, rfl⟩
  · exact ⟨_, _, _, _, mul_cbi X l, mul_ci X l, rfl⟩
  · rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨_, _, _, _, mul_fn X 0, mul_fn X 2, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 1, mul_fn X 3, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 2, mul_fn X 0, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 3, mul_fn X 1, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 4, mul_fn X 4, rfl⟩
    · exact ⟨_, _, _, _, mul_fn X 5, mul_fn X 5, rfl⟩

theorem f_p_c (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 1) (X.op m 4) =
    mkP (X.op m 1) (X.op m 4) * mkP (X.op l 0) (-X.op l 3) + (if l = m then mkP (X.op m 1) (X.op m 4) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_add_mkPair, mkPair_inj]
    refine ⟨weyl_pc X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pbcb X l]
    abel
  · rw [add_zero, mkPair_inj]
    exact ⟨comm_ops X l m 0 1 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 4 3 (Or.inl (Ne.symm h))]⟩

theorem f_p_ci (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 2) (X.op m 5) =
    mkP (X.op m 2) (X.op m 5) * mkP (X.op l 0) (-X.op l 3) - (if l = m then mkP (X.op m 2) (X.op m 5) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_sub_mkPair, mkPair_inj]
    refine ⟨weyl_pci X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pbcbi X l]
    abel
  · rw [sub_zero, mkPair_inj]
    exact ⟨comm_ops X l m 0 2 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 5 3 (Or.inl (Ne.symm h))]⟩

theorem f_pb_cb (l m : Fin r) : mkP (X.op l 3) (-X.op l 0) * mkP (X.op m 4) (X.op m 1) =
    mkP (X.op m 4) (X.op m 1) * mkP (X.op l 3) (-X.op l 0) + (if l = m then mkP (X.op m 4) (X.op m 1) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_add_mkPair, mkPair_inj]
    refine ⟨weyl_pbcb X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pc X l]
    abel
  · rw [add_zero, mkPair_inj]
    exact ⟨comm_ops X l m 3 4 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 1 0 (Or.inl (Ne.symm h))]⟩

theorem f_pb_cbi (l m : Fin r) : mkP (X.op l 3) (-X.op l 0) * mkP (X.op m 5) (X.op m 2) =
    mkP (X.op m 5) (X.op m 2) * mkP (X.op l 3) (-X.op l 0) - (if l = m then mkP (X.op m 5) (X.op m 2) else 0) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair]
  split_ifs with h
  · subst h
    rw [mkPair_sub_mkPair, mkPair_inj]
    refine ⟨weyl_pbcbi X l, ?_⟩
    rw [mul_neg, neg_mul, weyl_pci X l]
    abel
  · rw [sub_zero, mkPair_inj]
    exact ⟨comm_ops X l m 3 5 (Or.inl h), by rw [mul_neg, neg_mul, comm_ops X m l 2 0 (Or.inl (Ne.symm h))]⟩

theorem f_comm (l m : Fin r) (i i' j j' : Fin 6) (h1 : X.op l i * X.op m j = X.op m j * X.op l i)
    (h2 : X.op m j' * X.op l i' = X.op l i' * X.op m j') :
    mkP (X.op l i) (-X.op l i') * mkP (X.op m j) (X.op m j') = mkP (X.op m j) (X.op m j') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨h1, by rw [mul_neg, neg_mul, h2]⟩

theorem f_fn (l : Fin r) (i i' j j' : Fin 6) :
    mkP (X.op l i) (-X.op l i') * mkP (X.fn j) (X.fn j') = mkP (X.fn j) (X.fn j') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨op_fn X l i j, by rw [mul_neg, neg_mul, op_fn X l i' j']⟩

theorem f_pp (l m : Fin r) (i i' : Fin 6) (h1 : ∀ l m : Fin r, l ≠ m → X.op l i * X.op m i = X.op m i * X.op l i)
    (h2 : ∀ l m : Fin r, l ≠ m → X.op l i' * X.op m i' = X.op m i' * X.op l i') :
    mkP (X.op l i) (-X.op l i') * mkP (X.op m i) (-X.op m i') = mkP (X.op m i) (-X.op m i') * mkP (X.op l i) (-X.op l i') := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  by_cases h : l = m
  · subst h
    exact ⟨rfl, rfl⟩
  · exact ⟨h1 l m h, by rw [neg_mul_neg, neg_mul_neg, h2 m l (Ne.symm h)]⟩

theorem f_ppb (l m : Fin r) : mkP (X.op l 0) (-X.op l 3) * mkP (X.op m 3) (-X.op m 0) =
    mkP (X.op m 3) (-X.op m 0) * mkP (X.op l 0) (-X.op l 3) := by
  rw [mkPair_mul_mkPair, mkPair_mul_mkPair, mkPair_inj]
  exact ⟨comm_ops X l m 0 3 (Or.inr hol_03), by rw [neg_mul_neg, neg_mul_neg, comm_ops X m l 0 3 (Or.inr hol_03)]⟩

theorem f_GG : mkP (X.fn 4) (X.fn 4) = mkP (X.fn 0) (X.fn 2) * mkP (X.fn 2) (X.fn 0) -
    algebraMap ℂ (Pr (RadSp k r z z' π π')) ((Tz k r z * Tz k r z' : ℝ) : ℂ) := by
  rw [mkPair_mul_mkPair, algebraMap_Pr, mkPair_sub_mkPair, Complex.conj_ofReal, ← fn_GG X]

def preOf (X : ActualOps k r z z' π π') (hT : 0 ≤ Tz k r z * Tz k r z') : PreLevel (Pr (RadSp k r z z' π π')) r where
  p := fun l => mkP (X.op l 0) (-X.op l 3)
  pb := fun l => mkP (X.op l 3) (-X.op l 0)
  c := fun l => mkP (X.op l 1) (X.op l 4)
  ci := fun l => mkP (X.op l 2) (X.op l 5)
  cb := fun l => mkP (X.op l 4) (X.op l 1)
  cbi := fun l => mkP (X.op l 5) (X.op l 2)
  ζ := mkP (X.fn 0) (X.fn 2)
  ζi := mkP (X.fn 1) (X.fn 3)
  ζb := mkP (X.fn 2) (X.fn 0)
  ζbi := mkP (X.fn 3) (X.fn 1)
  GG := mkP (X.fn 4) (X.fn 4)
  GGi := mkP (X.fn 5) (X.fn 5)
  TT := ((Tz k r z * Tz k r z' : ℝ) : ℂ)
  fns_comm := fun x hx y hy => pair_comm (mulPair_of_mem X x hx) (mulPair_of_mem X y hy)
  c_ci := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).1, (inv_ops X l).2.2.2⟩
  ci_c := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.1, (inv_ops X l).2.2.1⟩
  cb_cbi := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.2.1, (inv_ops X l).2.1⟩
  cbi_cb := fun l => by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(inv_ops X l).2.2.2, (inv_ops X l).1⟩
  ζ_ζi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).1, (fn_inv X hT).2.2.2.1⟩
  ζi_ζ := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.1, (fn_inv X hT).2.2.1⟩
  ζb_ζbi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.1, (fn_inv X hT).2.1⟩
  ζbi_ζb := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.1, (fn_inv X hT).1⟩
  GG_GGi := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.2.1, (fn_inv X hT).2.2.2.2.2⟩
  GGi_GG := by rw [mkPair_mul_mkPair, one_eq_mkPair, mkPair_inj]; exact ⟨(fn_inv X hT).2.2.2.2.2, (fn_inv X hT).2.2.2.2.1⟩
  GG_def := f_GG X
  p_c := f_p_c X
  p_ci := f_p_ci X
  p_cb := fun l m => f_comm X l m 0 3 4 1 (comm_ops X l m 0 4 (Or.inr hol_04)) (comm_ops X m l 1 3 (Or.inr hol_13))
  p_cbi := fun l m => f_comm X l m 0 3 5 2 (comm_ops X l m 0 5 (Or.inr hol_05)) (comm_ops X m l 2 3 (Or.inr hol_23))
  p_ζ := fun l => f_fn X l 0 3 0 2
  p_ζi := fun l => f_fn X l 0 3 1 3
  p_ζb := fun l => f_fn X l 0 3 2 0
  p_ζbi := fun l => f_fn X l 0 3 3 1
  p_GG := fun l => f_fn X l 0 3 4 4
  p_GGi := fun l => f_fn X l 0 3 5 5
  pb_cb := f_pb_cb X
  pb_cbi := f_pb_cbi X
  pb_c := fun l m => f_comm X l m 3 0 1 4 (comm_ops X l m 3 1 (Or.inr hol_31)) (comm_ops X m l 4 0 (Or.inr hol_40))
  pb_ci := fun l m => f_comm X l m 3 0 2 5 (comm_ops X l m 3 2 (Or.inr hol_32)) (comm_ops X m l 5 0 (Or.inr hol_50))
  pb_ζ := fun l => f_fn X l 3 0 0 2
  pb_ζi := fun l => f_fn X l 3 0 1 3
  pb_ζb := fun l => f_fn X l 3 0 2 0
  pb_ζbi := fun l => f_fn X l 3 0 3 1
  pb_GG := fun l => f_fn X l 3 0 4 4
  pb_GGi := fun l => f_fn X l 3 0 5 5
  p_p := fun l m => f_pp X l m 0 3 (fun a b h => comm_ops X a b 0 0 (Or.inl h)) (fun a b h => comm_ops X a b 3 3 (Or.inl h))
  p_pb := f_ppb X
  pb_pb := fun l m => f_pp X l m 3 0 (fun a b h => comm_ops X a b 3 3 (Or.inl h)) (fun a b h => comm_ops X a b 0 0 (Or.inl h))

theorem preOf_actual (X : ActualOps k r z z' π π') (hT : 0 ≤ Tz k r z * Tz k r z') : IsActualPre X (preOf X hT) := ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Pre

end Formalism.FourierDecayAlt.P.NFx1.APL

theorem Formalism.FourierDecayAlt.P.actual_pre_level : Formalism.FourierDecayAlt.NF.ActualPreLevel := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' hpl X
  exact ⟨Formalism.FourierDecayAlt.P.NFx1.APL.preOf X (Formalism.FourierDecayAlt.P.Qx5.place_alt_alt hpl), Formalism.FourierDecayAlt.P.NFx1.APL.preOf_actual X _⟩

open Matrix Finset Filter Topology
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.NFx1.TC

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.NF

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

section CD

variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {i : Fin (r + 1)}

structure CD (k r : ℕ) (i : Fin (r + 1)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  pres : ∀ (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E), SmoothFam k r i U₀ Φ →
    SmoothFam k r i U₀ (fun c => T (Φ c))
  loc : ∀ D : Set (Mx k r), IsOpen D → ∀ f f₂ : Mx k r → E, (∀ x ∈ Glev k r i ∩ D, f x = f₂ x) →
    ∀ x ∈ Glev k r i ∩ D, T f x = T f₂ x
  comm : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → ∀ v : Fin r → ℂ,
      fderiv ℝ (fun c' => T (Φ c') x.2) x.1 v = T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2

theorem slice_open {U₀ : Set ((Fin r → ℂ) × Mx k r)} (hU₀ : IsOpen U₀) (c : Fin r → ℂ) :
    IsOpen {g : Mx k r | (c, g) ∈ U₀} := IsOpen.preimage (f := fun g : Mx k r => (c, g)) (by fun_prop) hU₀

theorem diff_of_pres {T : (Mx k r → E) → Mx k r → E}
    (hp : ∀ (U₀ : Set ((Fin r → ℂ) × Mx k r)) (Φ : Fn k r E), SmoothFam k r i U₀ Φ →
      SmoothFam k r i U₀ (fun c => T (Φ c)))
    {U₀ : Set ((Fin r → ℂ) × Mx k r)} {Φ : Fn k r E} (h : SmoothFam k r i U₀ Φ) {x : (Fin r → ℂ) × Mx k r}
    (hx : x ∈ U₀) (hg : x.2 ∈ Glev k r i) : DifferentiableAt ℝ (fun c' => T (Φ c') x.2) x.1 :=
  Qx3.fam_differentiableAt (hp U₀ Φ h) hx hg

theorem cd_id : CD k r i (fun f : Mx k r → E => f) := ⟨fun _ _ h => h, fun _ _ _ _ h x hx => h x hx, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem cd_zero : CD k r i (fun _ : Mx k r → E => fun _ => (0 : E)) := by
  refine ⟨fun U₀ Φ _ x₀ _ _ => ⟨Set.univ, fun _ => (0 : E), isOpen_univ, trivial, contDiffOn_const, fun _ _ _ => rfl⟩,
    fun _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U₀ _ Φ _ x _ _ v
  show fderiv ℝ (fun _ : Fin r → ℂ => (0 : E)) x.1 v = 0
  simp

theorem CD.comp {T S : (Mx k r → E) → Mx k r → E} (hT : CD k r i T) (hS : CD k r i S) :
    CD k r i (fun f => T (S f)) := by
  refine ⟨fun U₀ Φ h => hT.pres U₀ _ (hS.pres U₀ Φ h),
    fun D hD f f₂ h x hx => hT.loc D hD _ _ (hS.loc D hD f f₂ h) x hx, ?_⟩
  intro U₀ hU Φ hΦ x hx hg v
  refine (hT.comm U₀ hU (fun c => S (Φ c)) (hS.pres U₀ Φ hΦ) x hx hg v).trans ?_
  refine hT.loc {g | (x.1, g) ∈ U₀} (slice_open hU x.1) _ _ ?_ x.2 (Set.mem_inter hg hx)
  intro y hy
  exact hS.comm U₀ hU Φ hΦ (x.1, y) hy.2 hy.1 v

theorem CD.add {T S : (Mx k r → E) → Mx k r → E} (hT : CD k r i T) (hS : CD k r i S) :
    CD k r i (fun f x => T f x + S f x) := by
  refine ⟨fun U₀ Φ h => Qx3.sf_add (hT.pres U₀ Φ h) (hS.pres U₀ Φ h), ?_, ?_⟩
  · intro D hD f f₂ h x hx
    show T f x + S f x = T f₂ x + S f₂ x
    rw [hT.loc D hD f f₂ h x hx, hS.loc D hD f f₂ h x hx]
  · intro U₀ hU₀ Φ h x hx hg v
    have h1 := diff_of_pres hT.pres h hx hg
    have h2 := diff_of_pres hS.pres h hx hg
    show fderiv ℝ (fun c' => T (Φ c') x.2 + S (Φ c') x.2) x.1 v = _
    rw [show (fun c' => T (Φ c') x.2 + S (Φ c') x.2) = (fun c' => T (Φ c') x.2) + (fun c' => S (Φ c') x.2) from rfl,
      fderiv_add h1 h2, _root_.add_apply, hT.comm U₀ hU₀ Φ h x hx hg v,
      hS.comm U₀ hU₀ Φ h x hx hg v]

theorem CD.smul {T : (Mx k r → E) → Mx k r → E} (hT : CD k r i T) (s : ℂ) :
    CD k r i (fun f x => s • T f x) := by
  refine ⟨fun U₀ Φ h => Qx3.sf_csmul s (hT.pres U₀ Φ h), ?_, ?_⟩
  · intro D hD f f₂ h x hx
    show s • T f x = s • T f₂ x
    rw [hT.loc D hD f f₂ h x hx]
  · intro U₀ hU₀ Φ h x hx hg v
    have h1 := diff_of_pres hT.pres h hx hg
    show fderiv ℝ (fun c' => s • T (Φ c') x.2) x.1 v = s • T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
    rw [show (fun c' => s • T (Φ c') x.2) = s • (fun c' => T (Φ c') x.2) from rfl,
      (h1.hasFDerivAt.const_smul s).fderiv, _root_.smul_apply, hT.comm U₀ hU₀ Φ h x hx hg v]

theorem rd_rep {Φ : Fn k r E} {U : Set ((Fin r → ℂ) × Mx k r)} {F : (Fin r → ℂ) × Mx k r → E}
    (hU : IsOpen U) (hF : ContDiffOn ℝ ∞ F U) (hΦ : ∀ y ∈ U, y.2 ∈ Glev k r i → Φ y.1 y.2 = F y)
    {X : Mx k r} (hX : inLieLev k r i X) {y : (Fin r → ℂ) × Mx k r} (hy : y ∈ U) (hyG : y.2 ∈ Glev k r i) :
    RdV X (Φ y.1) y.2 = fderiv ℝ F y ((0 : Fin r → ℂ), y.2 * X) := by
  have hγ : HasDerivAt (fun t : ℝ => ((y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)) : (Fin r → ℂ) × Mx k r))
      ((0 : Fin r → ℂ), y.2 * X) 0 :=
    (hasDerivAt_const (0 : ℝ) y.1).prodMk (hasDerivAt_mul_exp_smul_zero y.2 X)
  have hγ0 : ((y.1, y.2 * NormedSpace.exp (((0 : ℝ) : ℂ) • X)) : (Fin r → ℂ) × Mx k r) = y := by
    simp [NormedSpace.exp_zero]
  have hFd : DifferentiableAt ℝ F y := (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hy)
  have hcomp : HasDerivAt (fun t : ℝ => F (y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)))
      (fderiv ℝ F y ((0 : Fin r → ℂ), y.2 * X)) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have hev : (fun t : ℝ => Φ y.1 (y.2 * NormedSpace.exp ((t : ℂ) • X))) =ᶠ[𝓝 0]
      (fun t : ℝ => F (y.1, y.2 * NormedSpace.exp ((t : ℂ) • X))) := by
    have hmem : ∀ᶠ t : ℝ in 𝓝 0, ((y.1, y.2 * NormedSpace.exp ((t : ℂ) • X)) : (Fin r → ℂ) × Mx k r) ∈ U :=
      hγ.continuousAt.preimage_mem_nhds (by rw [hγ0]; exact hU.mem_nhds hy)
    filter_upwards [hmem] with t ht
    exact hΦ _ ht (Qx2.curve_lev hyG hX t)
  show deriv (fun t : ℝ => Φ y.1 (y.2 * NormedSpace.exp ((t : ℂ) • X))) 0 = _
  rw [hev.deriv_eq]
  exact hcomp.deriv

theorem cd_rd {X : Mx k r} (hX : inLieLev k r i X) : CD (E := E) k r i (fun f => RdV X f) := by
  refine ⟨fun U₀ Φ h => Qx3.sf_rdV (Qx3.lieLev_of hX) h, fun D hD f f₂ h x hx => Qx2.rd_loc hD h hx hX, ?_⟩
  intro U₀ hU₀ Φ h x hx hg v
  obtain ⟨U, F, hU, hxU, hF, hΦ⟩ := h x hx hg
  have hF1 := hF.fderiv_of_isOpen (m := ∞) hU withTop_enat_infty_add_one_le_infty
  have hFx := hF.contDiffAt (hU.mem_nhds hxU)
  have hF1d := (hF1.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hxU)
  have hL : (fun c' => RdV X (Φ c') x.2) =ᶠ[𝓝 x.1]
      (fun c' => fderiv ℝ F (c', x.2) ((0 : Fin r → ℂ), x.2 * X)) := by
    have hmem : ∀ᶠ c' in 𝓝 x.1, ((c', x.2) : (Fin r → ℂ) × Mx k r) ∈ U :=
      (continuous_id.prodMk continuous_const).continuousAt.preimage_mem_nhds (hU.mem_nhds hxU)
    filter_upwards [hmem] with c' hc'
    exact rd_rep hU hF hΦ hX (y := (c', x.2)) hc' hg
  have hA := (ContinuousLinearMap.apply ℝ E (((0 : Fin r → ℂ), x.2 * X) : (Fin r → ℂ) × Mx k r)).hasFDerivAt.comp
    x hF1d.hasFDerivAt
  have hL2 := HasFDerivAt.comp x.1 (f := fun c' : Fin r → ℂ => ((c', x.2) : (Fin r → ℂ) × Mx k r)) hA
    (hasFDerivAt_prodMk_left x.1 x.2)
  have e1 : fderiv ℝ (fun c' => RdV X (Φ c') x.2) x.1 v =
      fderiv ℝ (fderiv ℝ F) x ((v, 0) : (Fin r → ℂ) × Mx k r) ((0 : Fin r → ℂ), x.2 * X) :=
    (congrArg (fun L => L v) (hL.fderiv_eq.trans hL2.fderiv) :)
  have hH := hF1.clm_apply (contDiffOn_const (c := ((v, 0) : (Fin r → ℂ) × Mx k r)))
  have hrep : ∀ y ∈ U, y.2 ∈ Glev k r i →
      (fun c g => fderiv ℝ (fun c' => Φ c' g) c v) y.1 y.2 = fderiv ℝ F y ((v, 0) : (Fin r → ℂ) × Mx k r) := by
    intro y hy hyG
    show fderiv ℝ (fun c' => Φ c' y.2) y.1 v = _
    rw [(Qx3.fam_hasFDerivAt hU hF hΦ hy hyG).fderiv]
    rfl
  have hR := rd_rep (Φ := fun c g => fderiv ℝ (fun c' => Φ c' g) c v) hU hH hrep hX hxU hg
  have hH1 := (ContinuousLinearMap.apply ℝ E ((v, 0) : (Fin r → ℂ) × Mx k r)).hasFDerivAt.comp
    x hF1d.hasFDerivAt
  have e2 : RdV X (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2 =
      fderiv ℝ (fderiv ℝ F) x ((0 : Fin r → ℂ), x.2 * X) ((v, 0) : (Fin r → ℂ) × Mx k r) :=
    hR.trans (congrArg (fun L => L ((0 : Fin r → ℂ), x.2 * X)) hH1.fderiv :)
  have hsym : IsSymmSndFDerivAt ℝ F x := hFx.isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]; exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))
  exact e1.trans ((hsym _ _).trans e2.symm)

theorem cd_eh (a b : Fin (mdim k r i)) :
    CD (E := E) k r i (fun f => EH k r (posL k r i a) (posL k r i b) f) :=
  (cd_rd (Qx2.hpart_lev i a b).1).add ((cd_rd (Qx2.hpart_lev i a b).2).smul Complex.I)

theorem cd_top (u : ℂ) (a b : Fin (mdim k r i)) :
    CD (E := E) k r i (fun f => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) := by
  by_cases h : posL k r i a = posL k r i b
  · have := ((cd_id (E := E) (k := k) (r := r) (i := i)).smul u).add (cd_eh a b)
    have e : (fun f : Mx k r → E => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) =
        fun f x => u • f x + EH k r (posL k r i a) (posL k r i b) f x := by
      funext f x
      simp only [QuantumDeterminants.Top, if_pos h]
    rw [e]
    exact this
  · have := (cd_zero (E := E) (k := k) (r := r) (i := i)).add (cd_eh a b)
    have e : (fun f : Mx k r → E => QuantumDeterminants.Top (EH k r) u (posL k r i a) (posL k r i b) f) =
        fun f x => 0 + EH k r (posL k r i a) (posL k r i b) f x := by
      funext f x
      simp only [QuantumDeterminants.Top, if_neg h]
    rw [e]
    exact this

theorem cd_foldr (L : List ((Mx k r → E) → Mx k r → E)) (hL : ∀ T ∈ L, CD k r i T) :
    CD k r i (fun f => L.foldr (fun T h => T h) f) := by
  induction L with
  | nil => exact cd_id
  | cons T L ih =>
    exact (hL T (by simp)).comp (ih fun S hS => hL S (by simp [hS]))

theorem cd_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, CD k r i (T j)) : CD k r i (fun f x => ∑ j ∈ s, c j • T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cd_zero
  | insert j s hj ih =>
    have := ((hT j (by simp)).smul (c j)).add (ih fun l hl => hT l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this

theorem cd_qminor {t : ℕ} (a b : Fin t → Fin (mdim k r i)) (u : ℂ) :
    CD k r i (fun f : Mx k r → E => qminorOp (EH k r) (posL k r i ∘ a) (posL k r i ∘ b) u f) := by
  have := cd_sum (E := E) (k := k) (r := r) (i := i) Finset.univ
    (fun σ : Equiv.Perm (Fin t) => ((Equiv.Perm.sign σ : ℤ) : ℂ))
    (fun σ f => (List.ofFn fun l : Fin t => QuantumDeterminants.Top (EH k r) (u - ((l : ℕ) : ℂ)) ((posL k r i ∘ a) (σ l))
      ((posL k r i ∘ b) l)).foldr (fun T h => T h) f)
    (fun σ _ => cd_foldr _ (by
      intro T hT
      rw [List.mem_ofFn] at hT
      obtain ⟨l, rfl⟩ := hT
      exact cd_top _ _ _))
  refine Eq.mp (congrArg (CD k r i) ?_) this
  funext f x
  simp only [qminorOp, Finset.sum_apply, Pi.smul_apply]

structure CW (k r : ℕ) (i : Fin (r + 1)) (T : (Mx k r → E) → Mx k r → E) : Prop where
  diff : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → DifferentiableAt ℝ (fun c' => T (Φ c') x.2) x.1
  comm : ∀ U₀ : Set ((Fin r → ℂ) × Mx k r), IsOpen U₀ → ∀ Φ : Fn k r E, SmoothFam k r i U₀ Φ →
    ∀ x ∈ U₀, x.2 ∈ Glev k r i → ∀ v : Fin r → ℂ,
      fderiv ℝ (fun c' => T (Φ c') x.2) x.1 v = T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2

theorem CD.cw {T : (Mx k r → E) → Mx k r → E} (h : CD k r i T) : CW k r i T :=
  ⟨fun _ _ _ hΦ _ hx hg => diff_of_pres h.pres hΦ hx hg, h.comm⟩

theorem cw_zero : CW k r i (fun _ : Mx k r → E => fun _ => (0 : E)) := (cd_zero).cw

theorem CW.coef {T : (Mx k r → E) → Mx k r → E} (h : CW k r i T) (a : Mx k r → ℂ) :
    CW k r i (fun f x => a x • T f x) := by
  refine ⟨fun U₀ hU₀ Φ hΦ x hx hg => (h.diff U₀ hU₀ Φ hΦ x hx hg).const_smul (a x.2), ?_⟩
  intro U₀ hU₀ Φ hΦ x hx hg v
  have h1 := h.diff U₀ hU₀ Φ hΦ x hx hg
  show fderiv ℝ (fun c' => a x.2 • T (Φ c') x.2) x.1 v = a x.2 • T (fun g => fderiv ℝ (fun c' => Φ c' g) x.1 v) x.2
  rw [show (fun c' => a x.2 • T (Φ c') x.2) = a x.2 • (fun c' => T (Φ c') x.2) from rfl,
    (h1.hasFDerivAt.const_smul (a x.2)).fderiv, _root_.smul_apply, h.comm U₀ hU₀ Φ hΦ x hx hg v]

theorem CW.add {T S : (Mx k r → E) → Mx k r → E} (hT : CW k r i T) (hS : CW k r i S) :
    CW k r i (fun f x => T f x + S f x) := by
  refine ⟨fun U₀ hU₀ Φ hΦ x hx hg => (hT.diff U₀ hU₀ Φ hΦ x hx hg).add (hS.diff U₀ hU₀ Φ hΦ x hx hg), ?_⟩
  intro U₀ hU₀ Φ hΦ x hx hg v
  have h1 := hT.diff U₀ hU₀ Φ hΦ x hx hg
  have h2 := hS.diff U₀ hU₀ Φ hΦ x hx hg
  show fderiv ℝ (fun c' => T (Φ c') x.2 + S (Φ c') x.2) x.1 v = _
  rw [show (fun c' => T (Φ c') x.2 + S (Φ c') x.2) = (fun c' => T (Φ c') x.2) + (fun c' => S (Φ c') x.2) from rfl,
    fderiv_add h1 h2, _root_.add_apply, hT.comm U₀ hU₀ Φ hΦ x hx hg v,
    hS.comm U₀ hU₀ Φ hΦ x hx hg v]

theorem CW.neg {T : (Mx k r → E) → Mx k r → E} (h : CW k r i T) : CW k r i (fun f => -(T f)) := by
  have := h.coef (fun _ => (-1 : ℂ))
  refine Eq.mp (congrArg (CW k r i) ?_) this
  funext f x
  simp

theorem CW.ite {T : (Mx k r → E) → Mx k r → E} (h : CW k r i T) (p : Prop) [Decidable p] :
    CW k r i (fun f x => if p then T f x else 0) := by
  by_cases hp : p
  · simpa only [if_pos hp] using h
  · simpa only [if_neg hp] using (cw_zero (E := E) (k := k) (r := r) (i := i))

theorem cw_sum {ι : Type*} (s : Finset ι) (T : ι → (Mx k r → E) → Mx k r → E)
    (hT : ∀ j ∈ s, CW k r i (T j)) : CW k r i (fun f x => ∑ j ∈ s, T j f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cw_zero
  | insert j s hj ih =>
    have := (hT j (by simp)).add (ih fun l hl => hT l (by simp [hl]))
    simpa only [Finset.sum_insert hj] using this

theorem cw_chat (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ) :
    CW k r i (fun f : Mx k r → E => chatL (EH k r) (posL k r i) u a β f) :=
  cw_sum _ _ fun i' _ => cw_sum _ _ fun j' _ => (cd_qminor (skip1 i') (skip1 j') u).cw.coef _

theorem cw_chat2 (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ) :
    CW k r i (fun f : Mx k r → E => chat2L (EH k r) (posL k r i) u a a' β β' f) :=
  cw_sum _ _ fun i₁ _ => cw_sum _ _ fun i₂ _ => cw_sum _ _ fun j₁ _ => cw_sum _ _ fun j₂ _ =>
    ((cd_qminor (skip2 i₁ i₂) (skip2 j₁ j₂) u).cw.coef _).ite _

theorem cw_tL (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    CW k r i (fun f : Mx k r → E => tL k r z z' i Y p q f) := by
  fin_cases p <;> fin_cases q
  · exact (cd_qminor id id _).cw
  · exact (cw_chat _ _ _).neg
  · exact (cw_chat _ _ _).neg
  · exact (cw_chat2 _ _ _ _ _).neg

end CD

section Rad

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp] [NormedSpace ℂ Wp]
  [NormedAddCommGroup Wq] [NormedSpace ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)}

theorem radSp_fam {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') :
    SmoothFam k r (Fin.last r) (Qx5.OpR k r z z') Φ :=
  fun x₀ hx₀ hg₀ => hΦ.2.1 x₀ (Qx5.mem_DomR_of_OpR hx₀ hg₀)

theorem transfer_operator_fderiv {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} {g : Mx k r}
    (hx : (c, g) ∈ DomR k r z z') (Y : ℂ) (a b : Fin 2) (v : Fin r → ℂ) :
    fderiv ℝ (fun c' => tL k r z z' (Fin.last r) Y a b (Φ c') g) c v =
      tL k r z z' (Fin.last r) Y a b (fun g' => fderiv ℝ (fun c' => Φ c' g') c v) g :=
  (cw_tL (E := Wq →L[ℂ] Wp) z z' Y a b).comm _ (Qx5.isOpen_OpR k r z z') Φ (radSp_fam hΦ) (c, g)
    (Qx5.DomR_sub_OpR hx) hx.2.1 v

theorem transfer_operator_linear {f₁ f₂ : Mx k r → (Wq →L[ℂ] Wp)} (h₁ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₁)
    (h₂ : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f₂) (Y : ℂ) (a b : Fin 2) (s₁ s₂ : ℂ) {g : Mx k r}
    (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    tL k r z z' (Fin.last r) Y a b (fun y => s₁ • f₁ y + s₂ • f₂ y) g =
      s₁ • tL k r z z' (Fin.last r) Y a b f₁ g + s₂ • tL k r z z' (Fin.last r) Y a b f₂ g := by
  have hll := Qx2.ll_tL (E := Wq →L[ℂ] Wp) (i := Fin.last r) (Qx5.Dp_open k r z z') z z' Y a b
  have h0 := hll.lin (fun _ => 0) (fun _ => 0) 1 Qx2.smooth_zero Qx2.smooth_zero g hg
  have hs := hll.lin (fun _ => 0) f₁ s₁ Qx2.smooth_zero h₁ g hg
  have hm := hll.lin (fun y => s₁ • f₁ y) f₂ s₂ (Qx2.smooth_smul h₁ s₁) h₂ g hg
  simp only [one_smul, add_zero, zero_add, smul_zero] at h0 hs hm
  have h0' : tL k r z z' (Fin.last r) Y a b (fun _ => (0 : Wq →L[ℂ] Wp)) g = 0 :=
    add_left_cancel (h0.symm.trans (add_zero _).symm)
  rw [h0', zero_add] at hs
  rw [hm, hs]

theorem tl_smul {f : Mx k r → (Wq →L[ℂ] Wp)} (h : SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') f)
    (Y : ℂ) (a b : Fin 2) (s : ℂ) {g : Mx k r} (hg : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z') :
    tL k r z z' (Fin.last r) Y a b (fun y => s • f y) g = s • tL k r z z' (Fin.last r) Y a b f g := by
  have := transfer_operator_linear h h Y a b s 0 hg
  simp only [zero_smul, add_zero] at this
  exact this

theorem dir_smooth {Φ : Fn k r (Wq →L[ℂ] Wp)} (hΦ : Φ ∈ RadSp k r z z' π π') {c : Fin r → ℂ} (hc : c ∈ OmX r)
    (v : Fin r → ℂ) :
    SmoothLev k r (Fin.last r) (Qx5.Dp k r z z') (fun g' => fderiv ℝ (fun c' => Φ c' g') c v) := by
  have h := Qx5.slice_smooth (Qx5.dirD_mem v hΦ) hc
  have e : Qx5.dirD v Φ c = fun g' => fderiv ℝ (fun c' => Φ c' g') c v := by
    funext g'
    simp [Qx5.dirD, hc]
  rw [e] at h
  exact h

variable (X : ActualOps k r z z' π π')

theorem t_op_comm (Y : ℂ) (a b : Fin 2) (l : Fin r) (i : Fin 6) :
    X.t Y a b * X.op l i = X.op l i * X.t Y a b := by
  refine APL.end_ext fun Φ => ?_
  funext c g
  show ((X.t Y a b (X.op l i Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
    ((X.op l i (X.t Y a b Φ) : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
  by_cases hx : (c, g) ∈ DomR k r z z'
  · have et : ∀ Ψ : RadSp k r z z' π π', ((X.t Y a b Ψ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g =
        tL k r z z' (Fin.last r) Y a b ((Ψ : Fn k r (Wq →L[ℂ] Wp)) c) g := fun Ψ => X.t_apply Y a b Ψ (c, g) hx
    have hc : c ∈ OmX r := hx.1
    have hgD : g ∈ Glev k r (Fin.last r) ∩ Qx5.Dp k r z z' := ⟨hx.2.1, hx.2.2⟩
    have hsl := Qx5.slice_smooth Φ.2 hc
    have hev : (fun c' => ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c' g) =ᶠ[𝓝 c]
        (fun c' => tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c') g) := by
      filter_upwards [(Qx3.isOpen_OmX r).mem_nhds hc] with c' hc'
      exact X.t_apply Y a b Φ (c', g) ⟨hc', hx.2⟩
    rw [et, APL.op_coe X l i Φ, APL.op_coe X l i (X.t Y a b Φ)]
    simp only []
    fin_cases i
    · show tL k r z z' (Fin.last r) Y a b (fun g' => pOp l (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c) g =
        pOp l (fun c' => ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c' g) c
      have hf : (fun g' => pOp l (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c) = fun g' =>
          (c l * (1 / 2)) • fderiv ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c (Pi.single l 1) +
          (-(c l * (1 / 2) * Complex.I)) •
            fderiv ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c (Pi.single l Complex.I) := by
        funext g'
        simp only [pOp, if_pos hc, wirt]
        module
      have hr : pOp l (fun c' => ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c' g) c =
          (c l * (1 / 2)) • fderiv ℝ (fun c' => tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c') g)
            c (Pi.single l 1) +
          (-(c l * (1 / 2) * Complex.I)) • fderiv ℝ
            (fun c' => tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c') g) c (Pi.single l Complex.I) := by
        simp only [pOp, if_pos hc, wirt, hev.fderiv_eq]
        module
      rw [hf, hr, transfer_operator_linear (dir_smooth Φ.2 hc _) (dir_smooth Φ.2 hc _) Y a b _ _ hgD, transfer_operator_fderiv Φ.2 hx, transfer_operator_fderiv Φ.2 hx]
    · show tL k r z z' (Fin.last r) Y a b (fun g' => c l • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g') g =
        c l • ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
      rw [tl_smul hsl Y a b _ hgD, et]
    · show tL k r z z' (Fin.last r) Y a b (fun g' => (c l)⁻¹ • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g') g =
        (c l)⁻¹ • ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
      rw [tl_smul hsl Y a b _ hgD, et]
    · show tL k r z z' (Fin.last r) Y a b (fun g' => pbOp l (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c) g =
        pbOp l (fun c' => ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c' g) c
      have hf : (fun g' => pbOp l (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c) = fun g' =>
          (star (c l) * (1 / 2)) • fderiv ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c (Pi.single l 1) +
          (star (c l) * (1 / 2) * Complex.I) •
            fderiv ℝ (fun c' => (Φ : Fn k r (Wq →L[ℂ] Wp)) c' g') c (Pi.single l Complex.I) := by
        funext g'
        simp only [pbOp, if_pos hc, wirtBar]
        module
      have hr : pbOp l (fun c' => ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c' g) c =
          (star (c l) * (1 / 2)) • fderiv ℝ
            (fun c' => tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c') g) c (Pi.single l 1) +
          (star (c l) * (1 / 2) * Complex.I) • fderiv ℝ
            (fun c' => tL k r z z' (Fin.last r) Y a b ((Φ : Fn k r (Wq →L[ℂ] Wp)) c') g) c (Pi.single l Complex.I) := by
        simp only [pbOp, if_pos hc, wirtBar, hev.fderiv_eq]
        module
      rw [hf, hr, transfer_operator_linear (dir_smooth Φ.2 hc _) (dir_smooth Φ.2 hc _) Y a b _ _ hgD, transfer_operator_fderiv Φ.2 hx, transfer_operator_fderiv Φ.2 hx]
    · show tL k r z z' (Fin.last r) Y a b (fun g' => star (c l) • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g') g =
        star (c l) • ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
      rw [tl_smul hsl Y a b _ hgD, et]
    · show tL k r z z' (Fin.last r) Y a b (fun g' => (star (c l))⁻¹ • (Φ : Fn k r (Wq →L[ℂ] Wp)) c g') g =
        (star (c l))⁻¹ • ((X.t Y a b Φ : RadSp k r z z' π π') : Fn k r (Wq →L[ℂ] Wp)) c g
      rw [tl_smul hsl Y a b _ hgD, et]
  · rw [(X.t Y a b (X.op l i Φ)).2.1 (c, g) hx, (X.op l i (X.t Y a b Φ)).2.1 (c, g) hx]

end Rad

end Formalism.FourierDecayAlt.P.NFx1.TC

theorem Formalism.FourierDecayAlt.P.level_coordinates_commute : Formalism.FourierDecayAlt.NF.TCoordComm := by
  intro Wp Wq _ _ _ _ _ _ P z z' π π' _ X l i
  exact ⟨fun Y a b => Formalism.FourierDecayAlt.P.NFx1.TC.t_op_comm X Y a b l i,
    fun j => (Formalism.FourierDecayAlt.P.NFx1.APL.op_fn X l i j).symm⟩

theorem Formalism.FourierDecayAlt.P.relations_core_and_norms : Formalism.FourierDecayAlt.NF.RelIsCoreNorm := by
  intro P A _ _ _ d
  unfold Formalism.FourierDecayAlt.Q.NFData.Rel Formalism.FourierDecayAlt.NF.RelCore Formalism.FourierDecayAlt.NF.RelNorm
  constructor
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
  · rintro ⟨⟨h1, h2, h3, h4, h5⟩, h6⟩
    exact ⟨h1, h2, h3, h4, h5, h6⟩
