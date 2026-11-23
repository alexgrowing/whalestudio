import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.BesselLevi
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact

noncomputable section

open Matrix MeasureTheory NumberField Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.CayleySignature
open Formalism.L2.SG.SplitPrimeNormLemmas
open scoped InnerProductSpace

namespace Formalism.L2.SG.Pf.WFL

variable {k r : ℕ}

section Blocks

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem hform_crdA (A : UnitaryGroupInstance D) (v w : (VS D).V) :
    A.ιE (Formalism.UG.hform (starRingEnd A.I.E) A.I.J (crdOf A.I A.ιE A.bas v) (crdOf A.I A.ιE A.bas w)) =
      (VS D).hT v w := by
  conv_rhs => rw [← A.bas.sum_repr v, ← A.bas.sum_repr w]
  simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
    Formalism.UG.hform, map_mul, crdOf, starRingEnd_apply, A.ιE_conj, RingEquiv.apply_symm_apply,
    A.J_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [← Formalism.BasicNotions.bridge_star_holds D.R D.host, RingHom.id_apply]
  ring

theorem hJ_crdA (A : UnitaryGroupInstance D) (v : InfinitePlace A.I.F) (p q : (VS D).V) :
    hJ (A.I.ε v) (rv A.I v (crdOf A.I A.ιE A.bas p)) (rv A.I v (crdOf A.I A.ιE A.bas q)) =
      A.I.φ v (A.ιE.symm ((VS D).hT p q)) := by
  rw [Formalism.L2.SG.Pf.hJ_rv_sc, ← hform_crdA A p q, RingEquiv.symm_apply_apply]

end Blocks

section FrameOf
variable {ε : Fin (2 * r + k + 1) → Bool}

theorem hJ_smul_right {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) : hJ ε x (c • y) = c * hJ ε x y := by
  unfold hJ; rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_smul_left {n : ℕ} (ε : Fin n → Bool) (x y : Fin n → ℂ) (c : ℂ) :
    hJ ε (c • x) y = star c * hJ ε x y := by
  unfold hJ; rw [star_smul, smul_dotProduct, smul_eq_mul]

theorem isFrameJ_of (e f : Fin r → Fin (2 * r + k + 1) → ℂ) (z : Fin (2 * r + k + 1) → ℂ)
    (wf : Fin k → Fin (2 * r + k + 1) → ℂ) {T : ℝ} (hT : 0 < T)
    (hee : ∀ a b, hJ ε (e a) (e b) = 0) (hff : ∀ a b, hJ ε (f a) (f b) = 0)
    (hef : ∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0)
    (hez : ∀ a, hJ ε (e a) z = 0) (hfz : ∀ a, hJ ε (f a) z = 0) (hzz : hJ ε z z = -(T : ℂ))
    (hww : ∀ a b, hJ ε (wf a) (wf b) = if a = b then 1 else 0)
    (hew : ∀ c a, hJ ε (e c) (wf a) = 0) (hfw : ∀ c a, hJ ε (f c) (wf a) = 0) (hzw : ∀ a, hJ ε z (wf a) = 0) :
    IsFrameJ ε e f wf (z0v T z) := by
  have hs : Real.sqrt T ≠ 0 := (Real.sqrt_pos.mpr hT).ne'
  refine ⟨hee, hff, hef, fun a => ?_, fun a => ?_, ?_, hww, hew, hfw, fun a => ?_⟩
  · rw [z0v, hJ_smul_right, hez, mul_zero]
  · rw [z0v, hJ_smul_right, hfz, mul_zero]
  · rw [z0v, hJ_smul_right, hJ_smul_left, hzz, Complex.star_def, Complex.conj_ofReal]
    have h1 : ((Real.sqrt T)⁻¹ : ℝ) * (Real.sqrt T)⁻¹ * T = 1 := by
      rw [← mul_inv, Real.mul_self_sqrt hT.le, inv_mul_cancel₀ hT.ne']
    have h2 : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) * (((Real.sqrt T)⁻¹ : ℝ) * -(T : ℂ)) =
        -((((Real.sqrt T)⁻¹ * (Real.sqrt T)⁻¹ * T : ℝ)) : ℂ) := by push_cast; ring
    rw [h2, h1]; simp
  · rw [z0v, hJ_smul_left, hzw, mul_zero]

end FrameOf

section QuotRaw

theorem fix_one {n : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} :
    (∀ a, uMat (1 : Formalism.REAL.UJ ε) *ᵥ e a = e a) ∧ (∀ a, uMat (1 : Formalism.REAL.UJ ε) *ᵥ f a = f a) ∧
      uMat (1 : Formalism.REAL.UJ ε) *ᵥ z = z := by
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩ <;> simp [uMat]

theorem fix_mul {n : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {a b : Formalism.REAL.UJ ε}
    (ha : (∀ c, uMat a *ᵥ e c = e c) ∧ (∀ c, uMat a *ᵥ f c = f c) ∧ uMat a *ᵥ z = z)
    (hb : (∀ c, uMat b *ᵥ e c = e c) ∧ (∀ c, uMat b *ᵥ f c = f c) ∧ uMat b *ᵥ z = z) :
    (∀ c, uMat (a * b) *ᵥ e c = e c) ∧ (∀ c, uMat (a * b) *ᵥ f c = f c) ∧ uMat (a * b) *ᵥ z = z := by
  refine ⟨fun c => ?_, fun c => ?_, ?_⟩
  · rw [show uMat (a * b) = uMat a * uMat b from rfl, ← Matrix.mulVec_mulVec, hb.1 c, ha.1 c]
  · rw [show uMat (a * b) = uMat a * uMat b from rfl, ← Matrix.mulVec_mulVec, hb.2.1 c, ha.2.1 c]
  · rw [show uMat (a * b) = uMat a * uMat b from rfl, ← Matrix.mulVec_mulVec, hb.2.2, ha.2.2]

theorem fix_inv {n : ℕ} {ε : Fin n → Bool} {e f : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {a : Formalism.REAL.UJ ε}
    (ha : (∀ c, uMat a *ᵥ e c = e c) ∧ (∀ c, uMat a *ᵥ f c = f c) ∧ uMat a *ᵥ z = z) :
    (∀ c, uMat a⁻¹ *ᵥ e c = e c) ∧ (∀ c, uMat a⁻¹ *ᵥ f c = f c) ∧ uMat a⁻¹ *ᵥ z = z := by
  have hinv : uMat a⁻¹ * uMat a = 1 := by
    show ((a⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ).val * (a : (Matrix (Fin n) (Fin n) ℂ)ˣ).val = 1
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]; rfl
  have key : ∀ y, uMat a *ᵥ y = y → uMat a⁻¹ *ᵥ y = y := fun y hy => by
    conv_lhs => rw [← hy]
    rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  exact ⟨fun c => key _ (ha.1 c), fun c => key _ (ha.2.1 c), key _ ha.2.2⟩

variable {ε : Fin (2 * r + k + 1) → Bool} {e f : Fin r → Fin (2 * r + k + 1) → ℂ}
  {wf : Fin k → Fin (2 * r + k + 1) → ℂ}

theorem HNset_eq_NH (hHN : LocHNProps) {T : ℝ} (hT : 0 < T) {z : Fin (2 * r + k + 1) → ℂ}
    (hF : IsFrameJ ε e f wf (z0v T z)) (s : Formalism.REAL.UJ ε) :
    s ∈ HNset ε e f wf (z0v T z) (zBv k r T) ↔
      ∃ m ∈ {g : Formalism.REAL.UJ ε | InN ε e z (uMat g)},
        ∃ h ∈ {g : Formalism.REAL.UJ ε | (∀ a, uMat g *ᵥ e a = e a) ∧ (∀ a, uMat g *ᵥ f a = f a) ∧ uMat g *ᵥ z = z},
          s = m * h := by
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  obtain ⟨-, -, -, hnorm⟩ := hHN k r ε e f wf (z0v T z) z _ hF hc rfl
  have hz := Qm_zB (e := e) (f := f) (wf := wf) hT z
  have hzB : ∀ i : Fin (2 * r + k + 1), i.val < r ∨ r + k < i.val → zBv k r T i = 0 := inWb_zB T
  have hz0 : ∃ t : ℂ, z0v T z = t • z := ⟨_, rfl⟩
  rw [HNset_iff hF hz hzB hz0]
  constructor
  · rintro ⟨h, n, rfl, he, hf, hzz, hn⟩
    refine ⟨h * n * h⁻¹, hnorm h ⟨he, hf, hzz⟩ n hn, h, ⟨he, hf, hzz⟩, by group⟩
  · rintro ⟨m, hm, h, hh, rfl⟩
    refine ⟨h, h⁻¹ * m * h, by group, hh.1, hh.2.1, hh.2.2, ?_⟩
    have := hnorm h⁻¹ (fix_inv hh) m hm
    simpa using this

end QuotRaw

section QuotRaw2

theorem quotRaw (hQK : QuotProdK) (hHN : LocHNProps) (hNU : NUnimodLoc) {ι : Type} [Fintype ι]
    {ε : ι → Fin (2 * r + k + 1) → Bool} (e f : ι → Fin r → Fin (2 * r + k + 1) → ℂ)
    (z : ι → Fin (2 * r + k + 1) → ℂ) (wf : ι → Fin k → Fin (2 * r + k + 1) → ℂ) {T : ℝ} (hT : 0 < T)
    (hF : ∀ v, IsFrameJ (ε v) (e v) (f v) (wf v) (z0v T (z v)))
    (muN muH nuQ : Measure (∀ v, Formalism.REAL.UJ (ε v)))
    (hN : SigmaFinite muN ∧ muN ≠ 0 ∧ muN {s | ∀ v, InN (ε v) (e v) (z v) (uMat (s v))}ᶜ = 0 ∧
      ∀ s ∈ {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, InN (ε v) (e v) (z v) (uMat (s v))}, muN.map (fun x => s * x) = muN)
    (hH : SigmaFinite muH ∧ muH ≠ 0 ∧ muH {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, (∀ a, uMat (s v) *ᵥ e v a = e v a) ∧
        (∀ a, uMat (s v) *ᵥ f v a = f v a) ∧ uMat (s v) *ᵥ z v = z v}ᶜ = 0 ∧
      ∀ s ∈ {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, (∀ a, uMat (s v) *ᵥ e v a = e v a) ∧
        (∀ a, uMat (s v) *ᵥ f v a = f v a) ∧ uMat (s v) *ᵥ z v = z v}, muH.map (fun x => s * x) = muH)
    (hW : ∀ F : (∀ v, Formalism.REAL.UJ (ε v)) → ENNReal, Measurable F →
      ∫⁻ x, F x ∂(Measure.pi fun v => Formalism.REAL.muG (ε v)) =
        ∫⁻ x, (∫⁻ s, F (s * x) ∂((muN.prod muH).map (fun p => p.1 * p.2))) ∂nuQ) :
    ∃ (μS νl : ∀ v, Measure (Formalism.REAL.UJ (ε v))) (C : ENNReal), C ≠ 0 ∧ C ≠ ⊤ ∧
      (∀ v, IsLocHaar (HNset (ε v) (e v) (f v) (wf v) (z0v T (z v)) (zBv k r T)) (μS v) ∧ IsLocQuot (μS v) (νl v)) ∧
      ∀ F : ∀ v, Formalism.REAL.UJ (ε v) → ENNReal, (∀ v, Measurable (F v)) →
        (∀ v, ∀ s ∈ HNset (ε v) (e v) (f v) (wf v) (z0v T (z v)) (zBv k r T), ∀ x, F v (s * x) = F v x) →
        ∫⁻ x, ∏ v, F v (x v) ∂nuQ = C * ∏ v, ∫⁻ y, F v y ∂(νl v) := by
  have hc : (((Real.sqrt T)⁻¹ : ℝ) : ℂ) ≠ 0 := by
    have : (Real.sqrt T)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.mpr hT).ne'
    exact_mod_cast this
  set N : ∀ v, Set (Formalism.REAL.UJ (ε v)) := fun v => {g | InN (ε v) (e v) (z v) (uMat g)} with hNdef
  set H : ∀ v, Set (Formalism.REAL.UJ (ε v)) := fun v => {g | (∀ a, uMat g *ᵥ e v a = e v a) ∧
    (∀ a, uMat g *ᵥ f v a = f v a) ∧ uMat g *ᵥ z v = z v} with hHdef
  have hP := fun v => hHN k r (ε v) (e v) (f v) (wf v) (z0v T (z v)) (z v) _ (hF v) hc rfl
  have hpiN : Set.pi Set.univ N = {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, InN (ε v) (e v) (z v) (uMat (s v))} := by
    ext s; simp [Set.mem_pi, hNdef]
  have hpiH : Set.pi Set.univ H = {s : ∀ v, Formalism.REAL.UJ (ε v) | ∀ v, (∀ a, uMat (s v) *ᵥ e v a = e v a) ∧
      (∀ a, uMat (s v) *ᵥ f v a = f v a) ∧ uMat (s v) *ᵥ z v = z v} := by
    ext s; simp [Set.mem_pi, hHdef]
  have hN' := hN; rw [← hpiN] at hN'
  have hH' := hH; rw [← hpiH] at hH'
  obtain ⟨μS, νl, C, hC0, hCt, hloc, hK⟩ := hQK ι (fun _ => 2 * r + k + 1) ε N H
    (fun v => (hP v).1) (fun v => (hP v).2.1) (fun v => (hP v).2.2.1)
    (fun v => ⟨fix_one, fun a ha b hb => fix_mul ha hb, fun a ha => fix_inv ha⟩)
    (fun v h hh m hm => (hP v).2.2.2 h hh m hm)
    (fun v μ h1 h2 h3 h4 => hNU k r (ε v) (e v) (f v) (wf v) (z0v T (z v)) (z v) _ (hF v) hc rfl μ h1 h2 h3 h4)
    muN muH nuQ hN' hH' hW
  have hset : ∀ v, {s : Formalism.REAL.UJ (ε v) | ∃ m ∈ N v, ∃ h ∈ H v, s = m * h} =
      HNset (ε v) (e v) (f v) (wf v) (z0v T (z v)) (zBv k r T) := by
    intro v; ext s; exact (HNset_eq_NH hHN hT (hF v) s).symm
  refine ⟨μS, νl, C, hC0, hCt, fun v => ?_, fun F hFm hFi => hK F hFm fun v m hm h hh x => ?_⟩
  · obtain ⟨⟨h1, h2, h3, h4⟩, hq⟩ := hloc v
    rw [hset v] at h3 h4
    exact ⟨⟨h1, h2, h3, h4⟩, hq⟩
  · refine hFi v (m * h) ?_ x
    rw [← hset v]; exact ⟨m, hm, h, hh, rfl⟩

end QuotRaw2

end Formalism.L2.SG.Pf.WFL
