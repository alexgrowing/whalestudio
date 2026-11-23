import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRedKerA

noncomputable section

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct

namespace Formalism.L2.SG.Pf.KppRedW

open Formalism.MainNotions.S Formalism.L2.SG.Pf.RowDictPf PIW.AdelClassFin Formalism.L2.SG.Pf.RedBasicsPf Formalism.L2.SG.Pf.unitaryCongruence
  Formalism.L2.SG.Pf.AllRowsRedKerA

variable (I : AutInst)

abbrev sg : I.E ⊗[I.F] Af I.F →+* I.E ⊗[I.F] Af I.F := Formalism.UG.sigR I.cm.sig (Af I.F)

theorem sg_sg (x : I.E ⊗[I.F] Af I.F) : sg I (sg I x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul e b =>
    show (I.cm.sig (I.cm.sig e)) ⊗ₜ[I.F] b = e ⊗ₜ[I.F] b
    have : I.cm.sig (I.cm.sig e) = e := star_star e
    rw [this]

theorem sg_natCast (m : ℕ) : sg I (m : I.E ⊗[I.F] Af I.F) = m := map_natCast _ m

theorem sg_intCast (m : ℤ) : sg I (m : I.E ⊗[I.F] Af I.F) = m := map_intCast _ m

theorem hhat_conj (x y : Fin I.n → I.E ⊗[I.F] Af I.F) : sg I (hhat I x y) = hhat I y x := by
  have hJ : ∀ i j, sg I ((I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) i j) =
      (I.J.map (Formalism.UG.inclE (F := I.F) (Af I.F))) j i := by
    intro i j
    simp only [Matrix.map_apply]
    rw [DictLat.sigR_inclE]
    congr 1
    have := congrFun (congrFun I.J_herm j) i
    rw [← starRingEnd_apply]
    simpa [Formalism.UG.cT] using this
  unfold hhat Formalism.UG.hform
  simp only [map_sum, map_mul, sg_sg, hJ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

variable (w : HeightOneSpectrum (𝓞 I.E))

def Wq : Submodule (IntAf I.F I.E) (I.E ⊗[I.F] Af I.F) :=
  Submodule.span (IntAf I.F I.E) (iE I '' (w.asIdeal : Set (𝓞 I.E)))

variable {I w}

theorem iE_mem {a : 𝓞 I.E} (ha : a ∈ w.asIdeal) : iE I a ∈ Wq I w := Submodule.subset_span ⟨a, ha, rfl⟩

theorem Wq_int {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ Wq I w) : t ∈ IntAf I.F I.E := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, -, rfl⟩ := hx
    exact iE_int I a
  | zero => exact zero_mem _
  | add x y _ _ hx hy => exact add_mem hx hy
  | smul r x _ hx => exact mul_mem r.2 hx

theorem Wq_mul {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ Wq I w) {s : I.E ⊗[I.F] Af I.F} (hs : s ∈ IntAf I.F I.E) :
    s * t ∈ Wq I w :=
  (Wq I w).smul_mem ⟨s, hs⟩ ht

theorem Wq_mul' {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ Wq I w) {s : I.E ⊗[I.F] Af I.F} (hs : s ∈ IntAf I.F I.E) :
    t * s ∈ Wq I w := by
  rw [mul_comm]; exact Wq_mul ht hs

theorem Wq_smul {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ Wq I w) {y : Fin I.n → I.E ⊗[I.F] Af I.F} (hy : y ∈ I.Lf) :
    t • y ∈ Lq I w := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    exact smul_mem I w ha hy
  | zero => rw [zero_smul]; exact zero_mem _
  | add x z _ _ hx hz => rw [add_smul]; exact add_mem hx hz
  | smul r x _ hx =>
    have e : (r • x) • y = r • (x • y) := by
      show ((r : I.E ⊗[I.F] Af I.F) * x) • y = (r : I.E ⊗[I.F] Af I.F) • (x • y)
      rw [mul_smul]
    rw [e]
    exact (Lq I w).smul_mem r hx

theorem hhat_Lq_right {u : Fin I.n → I.E ⊗[I.F] Af I.F} (hu : u ∈ I.Lf) {v : Fin I.n → I.E ⊗[I.F] Af I.F}
    (hv : v ∈ Lq I w) : hhat I u v ∈ Wq I w := by
  have hgen : ∀ l ∈ wLat0 I w, hhat I u (iv I l) ∈ Wq I w := by
    intro l hl
    unfold wLat0 at hl
    induction hl using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨a, ha, y, hy, rfl⟩ := hz
      rw [DictLat.iv_smulE, DictLat.hhat_smul_right]
      exact Wq_mul' (iE_mem ha) (dual_hat_integral I u hu _ (DictLat.iv_mem I hy))
    | zero => rw [DictLat.iv_zero, DictLat.hhat_zero_right]; exact zero_mem _
    | add z z' _ _ hz hz' => rw [DictLat.iv_add, DictLat.hhat_add_right]; exact add_mem hz hz'
    | smul o z _ hz =>
      rw [DictLat.iv_smulO, DictLat.hhat_smul_right]
      exact Wq_mul hz (iE_int I o)
  unfold Lq lamAf at hv
  induction hv using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨⟨l, hl⟩, rfl⟩ := hz
    exact hgen l hl
  | zero => rw [DictLat.hhat_zero_right]; exact zero_mem _
  | add z z' _ _ hz hz' => rw [DictLat.hhat_add_right]; exact add_mem hz hz'
  | smul r z _ hz =>
    show hhat I u ((r : I.E ⊗[I.F] Af I.F) • z) ∈ Wq I w
    rw [DictLat.hhat_smul_right]
    exact Wq_mul hz r.2

theorem sg_Wq {t : I.E ⊗[I.F] Af I.F} (ht : t ∈ Wq I w) : sg I t ∈ Wq I (wc I w) := by
  induction ht using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨a, ha, rfl⟩ := hx
    have e : sg I (iE I a) = iE I (sigO I a) := by
      show Formalism.UG.sigR I.cm.sig (Af I.F) (Formalism.UG.inclE (F := I.F) (Af I.F) ((a : 𝓞 I.E) : I.E)) = _
      rw [DictLat.sigR_inclE]; rfl
    rw [e]
    exact iE_mem (sig_mem_wc I ha)
  | zero => rw [map_zero]; exact zero_mem _
  | add x z _ _ hx hz => rw [map_add]; exact add_mem hx hz
  | smul r x _ hx =>
    show sg I ((r : I.E ⊗[I.F] Af I.F) * x) ∈ Wq I (wc I w)
    rw [map_mul]
    exact Wq_mul hx (DictLat.sigR_int I r.2)

theorem wc_wc (w : HeightOneSpectrum (𝓞 I.E)) : wc I (wc I w) = w := by
  refine HeightOneSpectrum.ext ?_
  ext a
  rw [mem_wc, mem_wc, sigO_sigO]

theorem sg_Wq_iff {t : I.E ⊗[I.F] Af I.F} : sg I t ∈ Wq I (wc I w) ↔ t ∈ Wq I w := by
  refine ⟨fun h => ?_, sg_Wq⟩
  have := sg_Wq h
  rwa [sg_sg, wc_wc] at this

variable {p : ℕ}

theorem natCast_Wq (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) :
    (p : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
  have := iE_mem (I := I) (natCast_mem I w hp hcard)
  simpa [iE] using this

theorem intCast_int (c : ℤ) : (c : I.E ⊗[I.F] Af I.F) ∈ IntAf I.F I.E := intCast_mem _ c

theorem dvd_of_Wq (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hn : 0 < I.n) {c : ℤ}
    (hc : (c : I.E ⊗[I.F] Af I.F) ∈ Wq I w) : (p : ℤ) ∣ c := by
  obtain ⟨b, hb⟩ := exists_redBasis I w hp hcard
  let i0 : Fin I.n := ⟨0, hn⟩
  have h1 : (c : I.E ⊗[I.F] Af I.F) • iv I (b i0) ∈ Lq I w := Wq_smul hc (DictLat.iv_mem I (hb.1 i0))
  have h2 : iv I ((c : I.E) • b i0) ∈ Lq I w := by
    rw [DictLat.iv_smulE]
    simpa using h1
  have h3 : (c : I.E) • b i0 ∈ wLat0 I w := inter I w h2
  have hs : ∑ i, (((Pi.single i0 c : Fin I.n → ℤ) i : ℤ) : I.E) • b i = (c : I.E) • b i0 := by
    rw [Fintype.sum_eq_single i0 (fun j hj => by simp [hj])]
    simp
  have h4 := redBasis_indep I w hp hcard hb (Pi.single i0 c) (by rw [hs]; exact h3) i0
  simpa using h4

theorem int_of_Wq (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hn : 0 < I.n) {a : 𝓞 I.E}
    (ha : iE I a ∈ Wq I w) : a ∈ w.asIdeal := by
  obtain ⟨c, hc⟩ := int_surj I w hp hcard (Ideal.Quotient.mk _ a)
  have hac : a - (c : 𝓞 I.E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
  have hcW : ((c : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    have e : iE I a - iE I (a - (c : 𝓞 I.E)) = (c : I.E ⊗[I.F] Af I.F) := by simp [iE]
    rw [← e]; exact sub_mem ha (iE_mem hac)
  have h2 : (c : 𝓞 I.E) ∈ w.asIdeal := (int_mem_iff I w hp hcard c).2 (dvd_of_Wq hp hcard hn hcW)
  have := add_mem hac h2
  simpa using this

def CongW (p : ℕ) (t : I.E ⊗[I.F] Af I.F) (m : ZMod p) : Prop :=
  ∃ c : ℤ, (c : ZMod p) = m ∧ t - (c : I.E ⊗[I.F] Af I.F) ∈ Wq I w

theorem congW_unique (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) (hn : 0 < I.n)
    {t : I.E ⊗[I.F] Af I.F} {m m' : ZMod p} (h : CongW (w := w) p t m) (h' : CongW (w := w) p t m') : m = m' := by
  obtain ⟨c, rfl, hc⟩ := h
  obtain ⟨c', rfl, hc'⟩ := h'
  have h3 : ((c' - c : ℤ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w := by
    have := sub_mem hc hc'
    push_cast
    convert this using 1
    ring
  rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
  exact dvd_of_Wq hp hcard hn h3

theorem congW_exists (hp : p.Prime) (hcard : Nat.card (𝓞 I.E ⧸ w.asIdeal) = p) {t : I.E ⊗[I.F] Af I.F}
    (ht : t ∈ IntAf I.F I.E) : ∃ m, CongW (w := w) p t m := by
  obtain ⟨a, r', hr', hr⟩ := dual_dense I.F I.E p hp.pos t ht
  obtain ⟨c, hc⟩ := int_surj I w hp hcard (Ideal.Quotient.mk _ a)
  have hac : a - (c : 𝓞 I.E) ∈ w.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_intCast, hc, sub_self]
  refine ⟨c, c, rfl, ?_⟩
  have e : t - (c : I.E ⊗[I.F] Af I.F) = iE I (a - (c : 𝓞 I.E)) + (p : I.E ⊗[I.F] Af I.F) * r' := by
    rw [hr]; simp [iE]; ring
  rw [e]
  exact add_mem (iE_mem hac) (Wq_mul' (natCast_Wq hp hcard) hr')

theorem congW_of_sub {t t' : I.E ⊗[I.F] Af I.F} {m : ZMod p} (h : CongW (w := w) p t m) (h' : t' - t ∈ Wq I w) :
    CongW (w := w) p t' m := by
  obtain ⟨c, hc, ht⟩ := h
  refine ⟨c, hc, ?_⟩
  have := add_mem h' ht
  convert this using 1
  ring

theorem congW_zero_of {t : I.E ⊗[I.F] Af I.F} (h : t ∈ Wq I w) : CongW (w := w) p t 0 :=
  ⟨0, by simp, by simpa using h⟩

theorem congW_intCast (c : ℤ) : CongW (w := w) p (c : I.E ⊗[I.F] Af I.F) (c : ZMod p) :=
  ⟨c, rfl, by simp⟩

theorem congW_natCast (c : ℕ) : CongW (w := w) p (c : I.E ⊗[I.F] Af I.F) (c : ZMod p) :=
  ⟨c, by simp, by simp⟩

theorem congW_val [NeZero p] {t : I.E ⊗[I.F] Af I.F} {m : ZMod p}
    (h : t - ((m.val : ℕ) : I.E ⊗[I.F] Af I.F) ∈ Wq I w) : CongW (w := w) p t m :=
  ⟨m.val, by simp, by simpa using h⟩

theorem congW_add {t t' : I.E ⊗[I.F] Af I.F} {m m' : ZMod p} (h : CongW (w := w) p t m)
    (h' : CongW (w := w) p t' m') : CongW (w := w) p (t + t') (m + m') := by
  obtain ⟨c, rfl, hc⟩ := h
  obtain ⟨c', rfl, hc'⟩ := h'
  refine ⟨c + c', by push_cast; ring, ?_⟩
  have := add_mem hc hc'
  push_cast
  convert this using 1
  ring

theorem congW_neg {t : I.E ⊗[I.F] Af I.F} {m : ZMod p} (h : CongW (w := w) p t m) :
    CongW (w := w) p (-t) (-m) := by
  obtain ⟨c, rfl, hc⟩ := h
  refine ⟨-c, by push_cast; ring, ?_⟩
  have := neg_mem hc
  push_cast
  convert this using 1
  ring

theorem congW_sub {t t' : I.E ⊗[I.F] Af I.F} {m m' : ZMod p} (h : CongW (w := w) p t m)
    (h' : CongW (w := w) p t' m') : CongW (w := w) p (t - t') (m - m') := by
  rw [sub_eq_add_neg, sub_eq_add_neg]
  exact congW_add h (congW_neg h')

theorem congW_mul {t t' : I.E ⊗[I.F] Af I.F} {m m' : ZMod p} (ht' : t' ∈ IntAf I.F I.E)
    (h : CongW (w := w) p t m) (h' : CongW (w := w) p t' m') : CongW (w := w) p (t * t') (m * m') := by
  obtain ⟨c, rfl, hc⟩ := h
  obtain ⟨c', rfl, hc'⟩ := h'
  refine ⟨c * c', by push_cast; ring, ?_⟩
  have e : t * t' - ((c * c' : ℤ) : I.E ⊗[I.F] Af I.F) =
      (t - (c : I.E ⊗[I.F] Af I.F)) * t' + (c : I.E ⊗[I.F] Af I.F) * (t' - (c' : I.E ⊗[I.F] Af I.F)) := by
    push_cast; ring
  rw [e]
  exact add_mem (Wq_mul' hc ht') (Wq_mul hc' (intCast_int c))

theorem congW_sum {ι : Type*} (s : Finset ι) {t : ι → I.E ⊗[I.F] Af I.F} {m : ι → ZMod p}
    (h : ∀ i ∈ s, CongW (w := w) p (t i) (m i)) : CongW (w := w) p (∑ i ∈ s, t i) (∑ i ∈ s, m i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using congW_intCast (w := w) (p := p) (I := I) 0
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact congW_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem congW_sg {t : I.E ⊗[I.F] Af I.F} {m : ZMod p} :
    CongW (w := wc I w) p (sg I t) m ↔ CongW (w := w) p t m := by
  constructor
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    rw [← sg_Wq_iff, map_sub, sg_intCast]
    exact h
  · rintro ⟨c, hc, h⟩
    refine ⟨c, hc, ?_⟩
    have := sg_Wq h
    rwa [map_sub, sg_intCast] at this

end Formalism.L2.SG.Pf.KppRedW
