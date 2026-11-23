import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd

open MeasureTheory NumberField Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.Count.Test

open Formalism.MainNotions.S GlobalTheory.Count

theorem dHS_rank_one (z : ℂ) : dHS (!![z] : Matrix (Fin 1) (Fin 1) ℂ) = |Real.log ‖z‖| := by
  have hev : (Matrix.isHermitian_conjTranspose_mul_self
      (!![z] : Matrix (Fin 1) (Fin 1) ℂ)).eigenvalues 0 = ‖z‖ ^ 2 := by
    have htr := (Matrix.isHermitian_conjTranspose_mul_self
      (!![z] : Matrix (Fin 1) (Fin 1) ℂ)).trace_eq_sum_eigenvalues
    rw [Fin.sum_univ_one] at htr
    have h2 : ((!![z] : Matrix (Fin 1) (Fin 1) ℂ)ᴴ * !![z]).trace = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
      simp [Matrix.trace_fin_one, Matrix.mul_apply, Complex.conj_mul']
    exact Complex.ofReal_injective (htr.symm.trans h2)
  unfold dHS
  rw [Fin.sum_univ_one, hev, Real.log_pow]
  rw [show ((2 : ℕ) : ℝ) * Real.log ‖z‖ / 2 = Real.log ‖z‖ by push_cast; ring, Real.sqrt_sq_eq_abs]

theorem layerProd_const (f : ℕ) (τ : Fin 2 → ℝ) (c : ℝ) :
    layerProd 10 f ![1, 2] τ (fun _ => c) = c ^ ((2 * 3 * 10 - 2 * 3 ^ 2 - (1 + 4)) * f) := by
  simp [layerProd, Finset.prod_filter, Fin.prod_univ_two, Fin.sum_univ_two]
  ring

theorem gap_const : (16 : ℝ) * ((1 / 10 ^ 6)⁻¹) ^ 2 * (4 * 11 + 6) = 8 * 10 ^ 14 := by norm_num

variable (I : AutInst)

theorem mem_lamX (x : I.GA) (y : Fin I.n → I.E) : y ∈ lamX I x ↔
    I.fmat x.2⁻¹ *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) ∈ I.Lf := by
  constructor
  · intro hy
    unfold lamX at hy
    induction hy using Submodule.span_induction with
    | mem z hz => exact hz
    | zero =>
      have e0 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((0 : Fin I.n → I.E) i)) = 0 := by
        ext i; simp
      rw [e0, Matrix.mulVec_zero]
      exact zero_mem _
    | add z₁ z₂ _ _ h₁ h₂ =>
      have e2 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((z₁ + z₂) i)) =
          (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₁ i)) +
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z₂ i)) := by
        ext i; simp
      rw [e2, Matrix.mulVec_add]
      exact add_mem h₁ h₂
    | smul a z _ hz =>
      have hc : Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) ∈ IntAf I.F I.E :=
        Subring.subset_closure (Or.inl ⟨⟨_, a, rfl⟩, rfl⟩)
      have e1 : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) ((a • z) i)) =
          Formalism.UG.inclE (F := I.F) (Af I.F) (algebraMap (𝓞 I.E) I.E a) •
            (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (z i)) := by
        ext i; simp [Algebra.smul_def]
      rw [e1, Matrix.mulVec_smul]
      exact I.Lf.smul_mem ⟨_, hc⟩ hz
  · intro hy
    exact Submodule.subset_span hy

theorem le_lamX_one : I.L ≤ lamX I 1 := by
  intro y hy
  rw [mem_lamX]
  have h1 : I.fmat (1 : I.GA).2⁻¹ = 1 := by simp [AutInst.fmat]
  rw [h1, Matrix.one_mulVec]
  exact Submodule.subset_span ⟨⟨y, hy⟩, rfl⟩

theorem one_mem_GF : (1 : I.GA) ∈ I.GFset := by
  simp only [AutInst.GFset, Set.mem_ofPred_eq]
  refine ⟨1, one_mem _, fun v => ?_, ?_⟩
  · have hdet : IsUnit (I.P v).det := (Matrix.isUnit_iff_isUnit_det _).mp (I.P_unit v)
    simp [uMat, Matrix.nonsing_inv_mul _ hdet]
  · simp [AutInst.fmat]

theorem lamX_equivariant (g x : I.GA) (γ : GL (Fin I.n) I.E)
    (h : I.fmat g.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (y : Fin I.n → I.E) :
    (γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y ∈ lamX I (g * x) ↔ y ∈ lamX I x := by
  have hm : ∀ a b : I.Gf, I.fmat (a * b) = I.fmat a * I.fmat b := fun a b => by
    simp [AutInst.fmat]
  have h1 : I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hinc : (fun i => Formalism.UG.inclE (F := I.F) (Af I.F)
      (((γ : Matrix (Fin I.n) (Fin I.n) I.E) *ᵥ y) i)) =
      I.fmat g.2 *ᵥ (fun i => Formalism.UG.inclE (F := I.F) (Af I.F) (y i)) := by
    ext i
    rw [h, RingHom.map_mulVec]
    rfl
  rw [mem_lamX, mem_lamX, hinc, Prod.snd_mul, _root_.mul_inv_rev, hm, Matrix.mulVec_mulVec, mul_assoc,
    ← hm g.2⁻¹ g.2, inv_mul_cancel, h1, mul_one]

theorem embedding_cases (w : InfinitePlace I.E) :
    w.embedding = I.φ (w.comap (algebraMap I.F I.E)) ∨
      w.embedding = ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E))) := by
  have hcm := I.cm.cmUnram.2.1
  have hF : ∀ a : I.F, w.embedding (algebraMap I.F I.E a) =
      I.φ (w.comap (algebraMap I.F I.E)) (algebraMap I.F I.E a) := by
    have := I.cm.totReal
    have hv : w.comap (algebraMap I.F I.E) =
        InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) := by
      rw [← InfinitePlace.comap_mk, InfinitePlace.mk_embedding]
    have hψ : (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) =
        (w.comap (algebraMap I.F I.E)).embedding := RingHom.ext (I.φ_over _)
    have hreal : ComplexEmbedding.conjugate (w.embedding.comp (algebraMap I.F I.E)) =
        w.embedding.comp (algebraMap I.F I.E) :=
      ComplexEmbedding.isReal_iff.mp (InfinitePlace.isReal_mk_iff.mp (IsTotallyReal.isReal _))
    have hmk : InfinitePlace.mk (w.embedding.comp (algebraMap I.F I.E)) =
        InfinitePlace.mk ((I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E)) := by
      rw [hψ, InfinitePlace.mk_embedding, hv]
    have key : w.embedding.comp (algebraMap I.F I.E) =
        (I.φ (w.comap (algebraMap I.F I.E))).comp (algebraMap I.F I.E) := by
      rcases InfinitePlace.mk_eq_iff.mp hmk with h | h
      · exact h
      · rwa [hreal] at h
    intro a
    exact RingHom.congr_fun key a
  set ψ := I.φ (w.comap (algebraMap I.F I.E)) with hψdef
  have hpt : ∀ e : I.E, w.embedding e = ψ e ∨ w.embedding e = starRingEnd ℂ (ψ e) := by
    intro e
    obtain ⟨s, hs⟩ := (I.cm.fixed (e + star e)).1 (by rw [star_add, star_star, add_comm])
    obtain ⟨t, ht⟩ := (I.cm.fixed (e * star e)).1 (by rw [star_mul, star_star])
    have h1 : w.embedding e + starRingEnd ℂ (w.embedding e) = ψ e + starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_add, ← map_add, ← hs, hF]
    have h2 : w.embedding e * starRingEnd ℂ (w.embedding e) = ψ e * starRingEnd ℂ (ψ e) := by
      rw [← hcm w.embedding, ← hcm ψ, ← map_mul, ← map_mul, ← ht, hF]
    have h3 : (w.embedding e - ψ e) * (w.embedding e - starRingEnd ℂ (ψ e)) = 0 := by
      linear_combination (w.embedding e) * h1 - h2
    rcases mul_eq_zero.mp h3 with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (sub_eq_zero.mp h)
  by_contra hne
  push Not at hne
  obtain ⟨hne1, hne2⟩ := hne
  obtain ⟨a, ha⟩ : ∃ a, w.embedding a ≠ ψ a := by
    by_contra hc
    push Not at hc
    exact hne1 (RingHom.ext hc)
  obtain ⟨b, hb⟩ : ∃ b, w.embedding b ≠ starRingEnd ℂ (ψ b) := by
    by_contra hc
    push Not at hc
    exact hne2 (RingHom.ext fun x => (hc x).trans (ComplexEmbedding.conjugate_coe_eq ψ x).symm)
  have ha' := (hpt a).resolve_left ha
  have hb' := (hpt b).resolve_right hb
  rcases hpt (a + b) with h | h
  · apply ha
    rw [map_add, map_add] at h
    linear_combination h - hb'
  · apply hb
    rw [map_add, map_add, map_add] at h
    linear_combination h - ha'

theorem frm_frame (x : I.GA) (w : InfinitePlace I.E) :
    (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
  have hU : (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ * Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) *
      uMat (x.1 (w.comap (algebraMap I.F I.E))) = Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) :=
    (x.1 (w.comap (algebraMap I.F I.E))).2
  have key : (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
      I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
      (I.P (w.comap (algebraMap I.F I.E)) * uMat (x.1 (w.comap (algebraMap I.F I.E)))) =
      Formalism.REAL.Jm (I.ε (w.comap (algebraMap I.F I.E))) := by
    rw [Matrix.conjTranspose_mul]
    calc _ = (uMat (x.1 (w.comap (algebraMap I.F I.E))))ᴴ *
          ((I.P (w.comap (algebraMap I.F I.E)))ᴴ * I.J.map (I.φ (w.comap (algebraMap I.F I.E))) *
            I.P (w.comap (algebraMap I.F I.E))) * uMat (x.1 (w.comap (algebraMap I.F I.E))) := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [I.P_spec]; exact hU
  have hc : ∀ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      (A.map (starRingEnd ℂ))ᴴ = Aᴴ.map (starRingEnd ℂ) := by
    intro A; ext i j; simp [Matrix.conjTranspose_apply]
  simp only [frm]
  split_ifs with h
  · rw [h]; exact key
  · rw [(embedding_cases I w).resolve_left h]
    have hJ : I.J.map (ComplexEmbedding.conjugate (I.φ (w.comap (algebraMap I.F I.E)))) =
        (I.J.map (I.φ (w.comap (algebraMap I.F I.E)))).map (starRingEnd ℂ) := by
      ext i j; simp [ComplexEmbedding.conjugate_coe_eq]
    rw [hJ, hc, ← Matrix.map_mul, ← Matrix.map_mul, key]
    ext i j
    simp [Formalism.REAL.Jm, Matrix.diagonal_apply, apply_ite (starRingEnd ℂ)]

theorem one_mem_nearSet (x : I.GA) {δ : ℝ} (hδ : 0 ≤ δ) : (1 : I.GA) ∈ nearSet I x δ := by
  simp only [nearSet, Set.mem_ofPred_eq]
  refine ⟨one_mem_GF I, ?_, fun v => ?_⟩
  · rw [mul_one, inv_mul_cancel]
    exact one_mem (Formalism.UG.stabGL I.Lf)
  · simp [uMat, Formalism.REAL.hs, hδ]

theorem hasType_zero (x : I.GA) (j : Fin 0 → ℕ) (τ : Fin 0 → ℝ) :
    HasType I x j τ ↔ stepLt I x (1 / 2) = ⊥ := by
  unfold HasType HasFlag
  constructor
  · rintro ⟨S, ⟨h0, -, hlast, -, -, -⟩, -⟩
    rw [← hlast, show (Fin.last 0 : Fin (0 + 1)) = 0 from rfl]
    exact h0
  · intro h
    refine ⟨fun _ => ⊥, ⟨rfl, ?_, h.symm, fun a => a.elim0, fun i => i.elim0, ?_⟩, fun i => i.elim0⟩
    · intro a b hab
      rw [show a = b from Fin.ext (by have := a.2; have := b.2; omega)] at hab
      exact absurd hab (lt_irrefl b)
    · intro t ht
      refine ⟨0, ?_⟩
      show ⊥ = stepLe I x t
      refine (eq_bot_iff.mpr ?_).symm
      rw [← h]
      unfold stepLe stepLt
      apply sSup_le_sSup
      rintro N ⟨h1, h2, h3⟩
      exact ⟨h1, h2, lt_of_le_of_lt h3 ht⟩

theorem ph_one (B : RowsAut) (d : InfinitePlace B.I.F → ℝ) (h : IsDSData B d) :
    ph B d 1 = ((∏ v, d v : ℝ) : ℂ) := by
  have hv : ∀ v, ⟪B.w v, B.σ v (uMat ((1 : B.I.Ginf) v)) (B.w v)⟫_ℂ = 1 := by
    intro v
    have h1 : B.σ v 1 = 1 := (h v).2.1.2.2.1.1.1
    have h2 : ‖B.w v‖ = 1 := (h v).2.2.1.1
    have hu : uMat ((1 : B.I.Ginf) v) = 1 := by simp [uMat]
    rw [hu, h1, one_apply_eq_self, inner_self_eq_norm_sq_to_K, h2]
    simp
  unfold ph
  rw [Finset.prod_eq_one (fun v _ => hv v), star_one, mul_one]

end GlobalTheory.Count.Test
