import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LamXEquivariant
import Formalism.HarderNarasimhan.ShiftInvariance

open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

namespace GlobalTheory.Count.FrameMajorant

theorem signed_cs {n : ℕ} (ε : Fin n → Bool) (a b : Fin n → ℂ) :
    ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ Formalism.HermitianLatticesTheory.cnorm a * Formalism.HermitianLatticesTheory.cnorm b := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  have h1 : ‖star a ⬝ᵥ (Jm ε *ᵥ b)‖ ≤ ∑ i, ‖a i‖ * ‖b i‖ := by
    unfold dotProduct
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => le_of_eq ?_)
    simp only [Jm, Matrix.mulVec_diagonal, norm_mul, Pi.star_apply, norm_star]
    split_ifs <;> simp
  exact h1.trans (Real.sum_mul_le_sqrt_mul_sqrt _ _ _)

theorem cnorm_unitary {n : ℕ} (u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (u *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm a := by
  have key : ∀ c : Fin n → ℂ, ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) = star c ⬝ᵥ c := by
    intro c
    unfold dotProduct
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  unfold Formalism.HermitianLatticesTheory.cnorm
  congr 1
  have : star (u *ᵥ a) ⬝ᵥ (u *ᵥ a) = star a ⬝ᵥ a := by
    rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hu, Matrix.one_mulVec]
  exact_mod_cast (key _).trans (this.trans (key _).symm)

theorem cnorm_inv_mul_unitary {n : ℕ} (X u : Matrix (Fin n) (Fin n) ℂ) (hu : uᴴ * u = 1) (a : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((X * u)⁻¹ *ᵥ a) = Formalism.HermitianLatticesTheory.cnorm (X⁻¹ *ᵥ a) := by
  rw [Matrix.mul_inv_rev, Matrix.inv_eq_left_inv hu, ← Matrix.mulVec_mulVec]
  apply cnorm_unitary
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hu

variable (I : AutInst)

theorem comap_bijective :
    Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) := by
  refine ⟨fun w w' h => ?_, ?_⟩
  · have hw : ∀ w : InfinitePlace I.E, w = InfinitePlace.mk (I.φ (w.comap (algebraMap I.F I.E))) := by
      intro w
      rcases Test.embedding_cases I w with h | h
      · rw [← h, InfinitePlace.mk_embedding]
      · rw [← InfinitePlace.mk_conjugate_eq, ← h, InfinitePlace.mk_embedding]
    have h' : w.comap (algebraMap I.F I.E) = w'.comap (algebraMap I.F I.E) := h
    rw [hw w, hw w', h']
  · intro v
    refine ⟨InfinitePlace.mk (I.φ v), ?_⟩
    have h2 : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
    show (InfinitePlace.mk (I.φ v)).comap _ = v
    rw [InfinitePlace.comap_mk, h2, InfinitePlace.mk_embedding]

theorem card_places : Fintype.card (InfinitePlace I.F) = I.f := by
  have hR := I.cm.totReal
  rw [AutInst.f, IsTotallyReal.finrank, InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]

theorem frm_unit (x : I.GA) (w : InfinitePlace I.E) : IsUnit (frm I x w).det := by
  have h := congrArg (fun M => (Jm (I.ε (w.comap (algebraMap I.F I.E))) * M).det) (Test.frm_frame I x w)
  simp only [Jm_mul_self, Matrix.det_mul, Matrix.det_one] at h
  refine isUnit_iff_ne_zero.2 fun h0 => ?_
  simp [h0] at h

theorem hform_le (x : I.GA) (w : InfinitePlace I.E) (y z : Fin I.n → I.E) :
    ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤
      Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z := by
  have hc := I.cm.cmUnram.2.1
  have hX := frm_unit I x w
  have hback : ∀ y, frm I x w *ᵥ Formalism.HermitianLatticesTheory.fcoord (bas I) (frm I x) w y = fun i => w.embedding (y i) := by
    intro y
    unfold Formalism.HermitianLatticesTheory.fcoord
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec]
    funext i
    simp [Formalism.HermitianLatticesTheory.vecAt]
  have h1 : w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z) =
      star (fun i => w.embedding (y i)) ⬝ᵥ (I.J.map w.embedding *ᵥ fun i => w.embedding (z i)) := by
    simp only [Formalism.UG.hform, map_sum, map_mul, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
      Finset.mul_sum, starRingEnd_apply, hc, mul_assoc]
  rw [h1, ← hback y, ← hback z, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
    Matrix.mulVec_mulVec, Test.frm_frame I x w]
  exact signed_cs _ _ _

theorem normAt_mul (x : I.GA) (w : InfinitePlace I.E) (k : I.GA) (hk : ∀ v, uMat (k.1 v) ∈ Kset (I.ε v))
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  set v := w.comap (algebraMap I.F I.E) with hv
  have hu : (uMat (k.1 v))ᴴ * uMat (k.1 v) = 1 := (hk v).1.1
  have hm : uMat ((x * k).1 v) = uMat (x.1 v) * uMat (k.1 v) := rfl
  unfold Formalism.HermitianLatticesTheory.normAt Formalism.HermitianLatticesTheory.fcoord frm
  simp only [← hv]
  split_ifs with h
  · rw [hm, ← Matrix.mul_assoc]
    exact cnorm_inv_mul_unitary _ _ hu _
  · rw [hm, ← Matrix.mul_assoc, Matrix.map_mul]
    apply cnorm_inv_mul_unitary
    have hT : ∀ M : Matrix (Fin I.n) (Fin I.n) ℂ, (M.map (starRingEnd ℂ))ᴴ = Mᴴ.map (starRingEnd ℂ) := by
      intro M; ext i j; simp
    rw [hT, ← Matrix.map_mul, hu]
    simp

theorem frames_give_majorants : ∀ (I : AutInst) (x : I.GA), IsTotallyComplex I.E ∧ nPl I.E = I.f ∧ Fintype.card (InfinitePlace I.F) = I.f ∧ Function.Bijective (fun w : InfinitePlace I.E => w.comap (algebraMap I.F I.E)) ∧ ∀ w : InfinitePlace I.E, IsUnit (frm I x w).det ∧ (frm I x w)ᴴ * I.J.map w.embedding * frm I x w = Jm (I.ε (w.comap (algebraMap I.F I.E))) ∧ (∀ y z : (Fin I.n → I.E), ‖w.embedding (Formalism.UG.hform (starRingEnd I.E) I.J y z)‖ ≤ Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w z) ∧ ∀ k : I.GA, (∀ v, uMat (k.1 v) ∈ Kset (I.ε v)) → ∀ y, Formalism.HermitianLatticesTheory.normAt (bas I) (frm I (x * k)) w y = Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  intro I x
  refine ⟨I.cm.cmUnram.1, ?_, card_places I, comap_bijective I, fun w =>
    ⟨frm_unit I x w, Test.frm_frame I x w, hform_le I x w, normAt_mul I x w⟩⟩
  rw [nPl, Fintype.card_of_bijective (comap_bijective I), card_places]

end GlobalTheory.Count.FrameMajorant
