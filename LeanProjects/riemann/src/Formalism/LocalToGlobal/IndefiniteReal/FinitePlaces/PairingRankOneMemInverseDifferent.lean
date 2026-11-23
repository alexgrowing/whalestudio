import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.LatMod
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharDual
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import Formalism.SharpRestriction.CuspSpanNormBounds.NonemptyParameterModels.TermTiesEmptyOfLargeIndex

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Polynomial
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Datum

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ}

theorem star_gram (S : HSp D) (k b : Fin S.rank) : star (S.gram k b) = S.gram b k := by
  have := congrFun (congrFun (Brg.gram_herm S) b) k
  rw [Matrix.conjTranspose_apply] at this
  exact this

theorem inv_contract (S : HSp D) (a : Fin S.rank) (v : Fin S.rank → D.host.E) :
    ∑ b, S.gram⁻¹ a b * ∑ k, v k * S.gram b k = v a := by
  have h1 : S.gram⁻¹ * S.gram = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (Formalism.MainNotions.S.Inh.tie_gram_det_ne S))
  calc ∑ b, S.gram⁻¹ a b * ∑ k, v k * S.gram b k = ∑ k, (∑ b, S.gram⁻¹ a b * S.gram b k) * v k := by
        simp only [Finset.mul_sum, Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ k, (S.gram⁻¹ * S.gram) a k * v k := by simp only [Matrix.mul_apply]
    _ = v a := by
        rw [h1]
        simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

def rk1 (S T : HSp D) (c : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    Matrix (Fin T.rank) (Fin S.rank) D.host.E :=
  Matrix.of fun i j => c * t i * ∑ k, star (s k) * S.gram k j

def hF (S : HSp D) (x y : Fin S.rank → D.host.E) : D.host.E := ∑ i, ∑ j, star (x i) * S.gram i j * y j

theorem hermitian_rank_one_right (S T : HSp D) (X : Matrix (Fin T.rank) (Fin S.rank) D.host.E) (c' : D.host.E)
    (s' : Fin S.rank → D.host.E) (t' : Fin T.rank → D.host.E) :
    hE S T X (rk1 S T c' s' t') = star c' * ∑ cc, ∑ d, star (t' cc) * T.gram cc d * ∑ a, X d a * s' a := by
  unfold hE rk1
  have hst : ∀ cc b, star (c' * t' cc * ∑ k, star (s' k) * S.gram k b) =
      star c' * star (t' cc) * ∑ k, s' k * S.gram b k := by
    intro cc b
    rw [star_mul', star_mul', star_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [star_mul', star_star, star_gram]
  simp only [Matrix.of_apply, hst]
  calc ∑ a, ∑ b, ∑ cc, ∑ d, S.gram⁻¹ a b * (star c' * star (t' cc) * ∑ k, s' k * S.gram b k) * T.gram cc d * X d a
      = ∑ a, ∑ cc, ∑ d, star c' * star (t' cc) * T.gram cc d * X d a *
          (∑ b, S.gram⁻¹ a b * ∑ k, s' k * S.gram b k) := by
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun cc _ => ?_
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun b _ => by ring
    _ = ∑ a, ∑ cc, ∑ d, star c' * star (t' cc) * T.gram cc d * X d a * s' a := by
        simp only [inv_contract]
    _ = _ := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun cc _ => ?_
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun d _ => ?_
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun a _ => by ring

theorem hermitian_rank_one_rank_one (S T : HSp D) (c c' : D.host.E) (s s' : Fin S.rank → D.host.E) (t t' : Fin T.rank → D.host.E) :
    hE S T (rk1 S T c s t) (rk1 S T c' s' t') = c * star c' * hF S s s' * hF T t' t := by
  rw [hermitian_rank_one_right]
  unfold hF
  simp only [rk1, Matrix.of_apply]
  have h1 : ∀ d, ∑ a, c * t d * (∑ k, star (s k) * S.gram k a) * s' a = c * t d * ∑ i, ∑ j, star (s i) * S.gram i j * s' j := by
    intro d
    simp only [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [h1]
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun cc _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun d _ => by ring

open scoped Pointwise

theorem bb_ne_bot : D.host.𝔟 ≠ ⊥ := by
  intro h
  have h1 := D.host.𝔟_spec.1
  rw [h] at h1
  simp only [Submodule.bot_mul] at h1
  exact differentIdeal_ne_bot h1

theorem conj_bb_ne_bot : D.host.conj • D.host.𝔟 ≠ ⊥ := by
  intro h
  apply bb_ne_bot (D := D)
  have := congrArg (fun I : Ideal (𝓞 D.host.E) => D.host.conj⁻¹ • I) h
  simpa using this

theorem conj_inv_eq : D.host.conj⁻¹ = D.host.conj := by
  rw [inv_eq_iff_mul_eq_one]
  exact AlgEquiv.ext fun y => Formalism.MainNotions.UnusedSlot33.HK.conj_conj D.host y

theorem conj_inv_smul (x : 𝓞 D.host.E) : D.host.conj⁻¹ • x = D.host.conj • x := by
  rw [conj_inv_eq]

set_option maxHeartbeats 800000 in

theorem star_mem_AAbar {c : D.host.E} (hc : c ∈ D.host.AA) : star c ∈ D.host.AAbar := by
  have hJ : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 bb_ne_bot
  have hJc : ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 conj_bb_ne_bot

  have h1 : ∀ y ∈ D.host.𝔟, c * (y : D.host.E) ∈
      ((D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    intro y hy
    have hyJ : (y : D.host.E) ∈ ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :=
      (FractionalIdeal.mem_coeIdeal _).2 ⟨y, hy, rfl⟩
    have := FractionalIdeal.mul_mem_mul hc hyJ
    unfold Host.AA Host.AA0 at this
    rwa [mul_assoc, inv_mul_cancel₀ hJ, mul_one] at this

  have h2 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
      ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≤
      ((D.host.conj • D.host.ccE : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [FractionalIdeal.mul_le]
    intro i hi j hj
    obtain ⟨z, rfl⟩ := (FractionalIdeal.mem_spanSingleton _).1 hi
    obtain ⟨j', hj', rfl⟩ := (FractionalIdeal.mem_coeIdeal _).1 hj
    have hy : D.host.conj • j' ∈ D.host.𝔟 := by
      have := (Ideal.mem_pointwise_smul_iff_inv_smul_mem).1 hj'
      rwa [conj_inv_smul] at this
    obtain ⟨x, hx, hxe⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 _ hy)
    have hxs : D.host.conj • x ∈ D.host.conj • D.host.ccE := Ideal.smul_mem_pointwise_smul _ _ _ hx
    have key : star c * algebraMap (𝓞 D.host.E) D.host.E j' = algebraMap (𝓞 D.host.E) D.host.E (D.host.conj • x) := by
      show star c * (j' : D.host.E) = ((D.host.conj • x : 𝓞 D.host.E) : D.host.E)
      rw [Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, show ((x : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E x from rfl, hxe,
        map_mul, Formalism.TwoAdicCyclotomicDecomposition.odd_coe_smul, Formalism.MainNotions.UnusedSlot33.HK.conj_conj, Formalism.BasicNotions.Examples₂.star_eq_conj]
    rw [smul_mul_assoc, key]
    exact Submodule.smul_mem _ _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨_, hxs, rfl⟩)
  have h3 : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) ≤ D.host.AAbar := by
    unfold Host.AAbar
    calc FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c)
        = FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (star c) *
          ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
          ((D.host.conj • D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ := by
          rw [mul_assoc, mul_inv_cancel₀ hJc, mul_one]
      _ ≤ _ := by gcongr
  exact h3 (FractionalIdeal.mem_spanSingleton_self _ _)

set_option maxHeartbeats 800000 in

theorem xi_dual {c c' : D.host.E} (hc : c ∈ D.host.AA) (hc' : c' ∈ D.host.AA) (o : 𝓞 D.host.E) :
    ∃ z : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * c * star c' * o) = z := by
  have hfp := factPrincipalDatum D.R D.host
  have hdd := coeIdeal_differentIdeal ℤ ℚ D.host.E (𝓞 D.host.E)
  have hX : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) D.host.xi0 * D.host.AA * D.host.AAbar =
      FractionalIdeal.dual ℤ ℚ 1 := by
    have := eq_inv_of_mul_eq_one_left hfp
    rw [this]
    show (((differentIdeal ℤ (𝓞 D.host.E)) : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E)⁻¹ = _
    rw [hdd, inv_inv]
  have hz : D.host.xi0 * c * star c' ∈ FractionalIdeal.dual ℤ ℚ (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) := by
    rw [← hX]
    exact FractionalIdeal.mul_mem_mul (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _) hc)
      (star_mem_AAbar hc')
  have h10 : (1 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 := by
    rw [← FractionalIdeal.coeIdeal_top]; exact FractionalIdeal.coeIdeal_ne_zero.2 top_ne_bot
  have h1 := (FractionalIdeal.mem_dual (A := ℤ) (K := ℚ) h10).1 hz (o : D.host.E)
    ((FractionalIdeal.mem_one_iff _).2 ⟨o, rfl⟩)
  obtain ⟨z, hz'⟩ := h1
  rw [Algebra.traceForm_apply] at hz'
  exact ⟨z, by rw [← hz']; simp⟩

theorem symplO_smul_right (S T : HSp D) (c : AF D.host.F) (x y : WO S T) :
    symplO S T x (c • y) = c * symplO S T x y := by
  have h : hO S T x (c • y) = algebraMap (AF D.host.F) (AE D) c * hO S T x y := by
    unfold hO
    simp only [Matrix.smul_apply, Algebra.smul_def, map_mul, cA_alg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ =>
      Finset.sum_congr rfl fun c' _ => Finset.sum_congr rfl fun d _ => by ring
  unfold symplO
  rw [h, mul_left_comm, ← Algebra.smul_def, map_smul, smul_eq_mul]

theorem gen_eq (S T : HSp D) (α : Af D.host.F) (c : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (c * t i * ∑ k, star (s k) * S.gram k j) : WO S T) =
      pairA D.host.F 0 α • ratW T S (rk1 S T c s t) := by
  ext i j
  rw [Matrix.of_apply, Matrix.smul_apply, Algebra.smul_def, Algebra.TensorProduct.algebraMap_apply,
    Algebra.algebraMap_self, RingHom.id_apply]
  show _ = (pairA D.host.F 0 α ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] rk1 S T c s t i j)
  rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  rfl

theorem trace_mul_alg (w : D.host.E) (y : D.host.F) :
    Algebra.trace D.host.F D.host.E (w * algebraMap D.host.F D.host.E y) = Algebra.trace D.host.F D.host.E w * y := by
  rw [mul_comm, ← Algebra.smul_def, map_smul, smul_eq_mul, mul_comm]

theorem pairing_rank_one_mem_inverse_different (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {c c' : D.host.E} (hc : c ∈ D.host.AA) (hc' : c' ∈ D.host.AA) {s s' : Fin S.rank → D.host.E} (hs : s ∈ ΛS)
    (hs' : s' ∈ ΛS) {t t' : Fin T.rank → D.host.E} (ht : t ∈ ΛT) (ht' : t' ∈ ΛT) :
    betaO S T (rk1 S T c s t) (rk1 S T c' s' t') ∈ invDiff D.host.F := by
  obtain ⟨b1, hb1⟩ := (hS.2 s').1 hs' s hs
  obtain ⟨b2, hb2⟩ := (hT.2 t).1 ht t' ht'
  intro y
  obtain ⟨z, hz⟩ := xi_dual hc hc' (b1 * b2 * algebraMap (𝓞 D.host.F) (𝓞 D.host.E) y)
  refine ⟨z, ?_⟩
  unfold betaO
  rw [hermitian_rank_one_rank_one, ← trace_mul_alg, Algebra.trace_trace]
  rw [← hz]
  congr 1
  have e1 : hF S s s' = (b1 : D.host.E) := by rw [hb1]; rfl
  have e2 : hF T t' t = (b2 : D.host.E) := by rw [hb2]; rfl
  rw [e1, e2]
  show _ = D.host.xi0 * c * star c' * ((b1 : D.host.E) * (b2 : D.host.E) * algebraMap D.host.F D.host.E (y : D.host.F))
  ring

theorem psi_gen (hψ : IsStdChar D ψ (-1)) (S T : HSp D) {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)} (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    {α α' : Af D.host.F} (hα : α ∈ intAf D.host.F) (hα' : α' ∈ intAf D.host.F)
    {c c' : D.host.E} (hc : c ∈ D.host.AA) (hc' : c' ∈ D.host.AA) {s s' : Fin S.rank → D.host.E} (hs : s ∈ ΛS)
    (hs' : s' ∈ ΛS) {t t' : Fin T.rank → D.host.E} (ht : t ∈ ΛT) (ht' : t' ∈ ΛT) :
    ψ (symplO S T (pairA D.host.F 0 α • ratW T S (rk1 S T c s t)) (pairA D.host.F 0 α' • ratW T S (rk1 S T c' s' t'))) = 1 := by
  rw [symplO_smul_left, symplO_smul_right, symplO_ratW_ratW]
  have e : pairA D.host.F 0 α * (pairA D.host.F 0 α' *
      algebraMap D.host.F (AF D.host.F) (betaO S T (rk1 S T c s t) (rk1 S T c' s' t'))) =
      pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (betaO S T (rk1 S T c s t) (rk1 S T c' s' t')) * (α * α')) := by
    refine Prod.ext (by show (0 : Ainf D.host.F) * (0 * _) = 0; rw [zero_mul]) ?_
    change α * (α' * algebraMap D.host.F (Af D.host.F) (betaO S T (rk1 S T c s t) (rk1 S T c' s' t'))) =
      algebraMap D.host.F (Af D.host.F) (betaO S T (rk1 S T c s t) (rk1 S T c' s' t')) * (α * α')
    ring
  rw [e]
  exact psi_invDiff hψ _ (pairing_rank_one_mem_inverse_different S T hS hT hc hc' hs hs' ht ht') _ (intAf_mul hα hα')

end Formalism.IndefR.Fin

end
