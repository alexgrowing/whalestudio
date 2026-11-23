import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitChart

open GlobalTheory.IdemModTwo GlobalTheory.SplitIdem

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)} {e : AE D}

def sc (he : SplitAt D v e) (z : AE D) : Fv D.host.F v := (he.exists_scalar z).choose

theorem sc_spec (he : SplitAt D v e) (z : AE D) : e * z = fj D (singleV D.host.F v (sc he z)) * e :=
  (he.exists_scalar z).choose_spec

theorem sc_eq (he : SplitAt D v e) {z : AE D} {α : Af D.host.F} (h : e * z = fj D α * e) :
    sc he z = evalV D.host.F v α := by
  rw [sc_spec he] at h
  rw [← he.scalar_inj h, evalV_singleV_same]

def comp (he : SplitAt D v e) : AE D →+* Fv D.host.F v where
  toFun := sc he
  map_one' := by rw [sc_eq he (α := 1) (by rw [he.one_mul', mul_one]), map_one]
  map_zero' := by rw [sc_eq he (α := 0) (by rw [map_zero, mul_zero, zero_mul]), map_zero]
  map_mul' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) * singleV D.host.F v (sc he y)), map_mul,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_mul]
    linear_combination y * sc_spec he x + fj D (singleV D.host.F v (sc he x)) * sc_spec he y
  map_add' x y := by
    rw [sc_eq he (α := singleV D.host.F v (sc he x) + singleV D.host.F v (sc he y)), map_add,
      evalV_singleV_same, evalV_singleV_same]
    rw [map_add]
    linear_combination sc_spec he x + sc_spec he y

theorem comp_apply (he : SplitAt D v e) (z : AE D) : comp he z = sc he z := rfl

theorem comp_fj (he : SplitAt D v e) (α : Af D.host.F) : comp he (fj D α) = evalV D.host.F v α :=
  sc_eq he (mul_comm _ _)

theorem comp_self (he : SplitAt D v e) : comp he e = 1 := by
  rw [comp_apply, sc_eq he (α := 1) (by rw [he.one_mul', he.1]), map_one]

theorem comp_algebraMap (he : SplitAt D v e) (y : AF D.host.F) :
    comp he (algebraMap (AF D.host.F) (AE D) y) = evalV D.host.F v y.2 := by
  rw [comp_apply, sc_eq he (α := y.2 * 1), mul_one]
  rw [← algebraMap_mul_fj, mul_assoc, he.one_mul', mul_comm]

theorem isIntegral_of_int (O : Type) {K L : Type} [CommRing O] [CommRing K] [CommRing L] [Algebra O K]
    (f : L →+* K) {x : L} (hx : IsIntegral ℤ x) : IsIntegral O (f x) :=
  (map_isIntegral_int f hx).tower_top

theorem comp_mem (he : SplitAt D v e) {z : AE D} (hz : z ∈ intL D) :
    comp he z ∈ v.adicCompletionIntegers D.host.F := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    have h1 : (pairA D.host.F 0 α ⊗ₜ[D.host.F] (o : D.host.E) : AE D) =
        fj D α * (1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E) := by
      show _ = (_ ⊗ₜ _) * _
      rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, mul_one]
    rw [h1, map_mul, comp_fj]
    refine mul_mem (hα v) ?_
    have h3 : IsIntegral (v.adicCompletionIntegers D.host.F)
        (comp he ((1 : AF D.host.F) ⊗ₜ[D.host.F] (o : D.host.E))) :=
      isIntegral_of_int _ ((comp he).comp
        (Algebra.TensorProduct.includeRight (R := D.host.F) (A := AF D.host.F) (B := D.host.E)).toRingHom) o.2
    obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    rw [← hy]
    exact y.2
  | zero => rw [map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg]; exact neg_mem hx

theorem finPart_mem {z : AE D} (hz : z ∈ intL D) : finPart D z ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hα, o, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩
  | zero => rw [RingHom.map_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [RingHom.map_add]; exact add_mem hx hy
  | neg x _ hx => rw [RingHom.map_neg]; exact neg_mem hx

theorem chart_comp (he : SplitAt D v e) : Chart e v (comp he) := by
  refine ⟨fun a => ⟨fj D (singleV D.host.F v a), by rw [comp_fj, evalV_singleV_same]⟩, fun a => ⟨fun h => ?_, fun h => ?_⟩,
    comp_algebraMap he, fun a => ⟨fun h => ?_, fun h => ?_⟩⟩
  · have h0 : singleV D.host.F v 0 = 0 := by
      rw [← sub_self (0 : Fv D.host.F v), singleV_sub, sub_self]
    rw [sc_spec he, ← comp_apply, h, h0, map_zero, zero_mul]
  · rw [← one_mul (comp he a), ← comp_self he, ← map_mul, h, map_zero]
  · have h1 := comp_mem he (inF_mem h)
    rw [inF_finPart, ← mul_assoc, he.one_mul', map_mul, comp_self, one_mul] at h1
    exact isInt_Ov.2 h1
  · rw [sc_spec he]
    exact finPart_mem (fj_mul_mem (singleV_mem_intAf D.host.F v ⟨_, isInt_Ov.1 h⟩) he.mem)

theorem exists_chart : ∀ {D : D7} (e : AE D), IsSplitIdem D e →
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (π : AE D →+* Fv D.host.F v), Chart e v π := by
  intro D e h
  obtain ⟨v, he⟩ := (isSplitIdem_iff e).1 h
  exact ⟨v, comp he, chart_comp he⟩

end GlobalTheory.SplitChart

end
