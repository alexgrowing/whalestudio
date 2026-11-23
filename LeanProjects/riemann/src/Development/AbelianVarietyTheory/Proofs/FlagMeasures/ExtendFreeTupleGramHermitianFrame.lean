import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.Measures
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensVSec
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.DensInfSS
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StandardFrameGramDetNeZero
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures
open scoped TensorProduct ENNReal

noncomputable section

namespace GlobalTheory.FrameExtend

section Alg

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem hR_sub_sum_right {m : ℕ} (x w : Fin n → R ⊗[F] E) (c : Fin m → R ⊗[F] E)
    (u : Fin m → Fin n → R ⊗[F] E) :
    hR R σ J x (w - ∑ a, c a • u a) = hR R σ J x w - ∑ a, c a * hR R σ J x (u a) := by
  simp only [hR, Formalism.UG.hform, Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end Alg

open GlobalTheory.FrameGram in

theorem extend_frame : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ (r : ℕ) (P : Frame E n r) (T : F), P.IsStd σ J T → ∀ y : Fin (r + 1) → Fin n → Fv F v ⊗[F] E, LinearIndependent (Fv F v ⊗[F] E) y → gramR (Fv F v) σ J y = (gramE σ J (F0 P)).map (inclR (Fv F v)) → ∃ f : Fin r → Fin n → Fv F v ⊗[F] E, gramR (Fv F v) σ J (Fin.append y f) = (gramE σ J (tupH P)).map (inclR (Fv F v)) := by
  intro F E _ _ _ _ _ σ hσ n J hJ v r P T hP y hy hgram
  have hinv : ∀ x, σ (σ x) = x := conj_invol hσ
  obtain ⟨_, hGh, _, hG0, _⟩ := std_frame_gram F E σ hσ n J hJ r P T hP
  have hPs := hP
  obtain ⟨_, hff0, hef, _, hfz, _, _⟩ := hPs
  have : FiniteDimensional F E := Module.Finite.of_restrictScalars_finite ℚ F E
  have : IsArtinianRing (Fv F v ⊗[F] E) := IsArtinianRing.of_finite (Fv F v) (Fv F v ⊗[F] E)
  have : IsReduced (Fv F v ⊗[F] E) := PI.VolStabS.isReduced_tens_field F E (Fv F v)
  have : IsSemisimpleRing (Fv F v ⊗[F] E) := IsArtinianRing.isSemisimpleRing_of_isReduced _
  let s := sigR (Fv F v) σ
  have hsw : ∀ x w, s (hR (Fv F v) σ J x w) = hR (Fv F v) σ J w x :=
    PI.VolStabS.hR_herm (Fv F v) σ hinv J hJ.1
  have hss : ∀ x, s (s x) = x := PI.VolStabS.sigR_invol (Fv F v) σ hinv

  let Z : Fin (r + 1) → Fin n → Fv F v ⊗[F] E := fun i => Matrix.vecMul (fun l => s (y i l)) (JR (F := F) (Fv F v) J)
  have hZh : ∀ i w, hR (Fv F v) σ J (y i) w = ∑ k, Z i k * w k := by
    intro i w
    simp only [hR, Formalism.UG.hform, Z, Matrix.vecMul, dotProduct, Finset.sum_mul]
    rw [Finset.sum_comm]
  have hZ : LinearIndependent (Fv F v ⊗[F] E) Z := by
    have hJu : IsUnit (JR (F := F) (Fv F v) J).det := by
      have e := RingHom.map_det (inclR (F := F) (E := E) (Fv F v)) J
      rw [RingHom.mapMatrix_apply] at e
      show IsUnit (J.map (inclR (Fv F v))).det
      rw [← e]
      exact (isUnit_iff_ne_zero.2 hJ.2).map _
    refine Fintype.linearIndependent_iff.2 fun g hg i => ?_
    let w : Fin n → Fv F v ⊗[F] E := fun l => ∑ i, g i * s (y i l)
    have hv0 : Matrix.vecMul w (JR (F := F) (Fv F v) J) = 0 := by
      funext j
      have := congrFun hg j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Z, Matrix.vecMul, dotProduct,
        Finset.mul_sum, Pi.zero_apply] at this
      simp only [Matrix.vecMul, dotProduct, w, Finset.sum_mul, Pi.zero_apply]
      rw [Finset.sum_comm]
      rw [← this]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
    have hv : w = 0 := by
      have := congrArg (fun u => Matrix.vecMul u (JR (F := F) (Fv F v) J)⁻¹) hv0
      simp only [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hJu, Matrix.vecMul_one,
        Matrix.zero_vecMul] at this
      exact this
    have hX0 : ∑ i, s (g i) • y i = 0 := by
      funext l
      have := congrArg s (congrFun hv l)
      simp only [w, map_sum, map_mul, hss, Pi.zero_apply, map_zero] at this
      simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using this
    have := Fintype.linearIndependent_iff.1 hy _ hX0 i
    have e2 := congrArg s this
    simp only [hss, map_zero] at e2
    exact e2
  obtain ⟨q, hq⟩ := PI.VolStabS.exists_leftInv_of_linIndep Z hZ

  let f' : Fin r → Fin n → Fv F v ⊗[F] E := fun b k => q k b.castSucc
  have hyf' : ∀ i b, hR (Fv F v) σ J (y i) (f' b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    rw [hZh]
    exact hq i b.castSucc
  have hyy : ∀ i j, hR (Fv F v) σ J (y i) (y j) =
      inclR (Fv F v) (if i = Fin.last r ∧ j = Fin.last r then algebraMap F E (-T) else 0) := by
    intro i j
    have := congrFun (congrFun hgram i) j
    simp only [Matrix.map_apply, hG0] at this
    exact this
  have hyy0 : ∀ i (a : Fin r), hR (Fv F v) σ J (y i) (y a.castSucc) = 0 := by
    intro i a
    rw [hyy]
    simp [Fin.castSucc_ne_last]
  let h2 : Fv F v ⊗[F] E := algebraMap F (Fv F v ⊗[F] E) (1 / 2)
  have hh : h2 + h2 = 1 := by
    rw [← map_add, show (1 / 2 : F) + 1 / 2 = 1 by norm_num, map_one]
  have hsh : s h2 = h2 := (Algebra.TensorProduct.map (AlgHom.id F (Fv F v)) σ).commutes _
  let c : Fin r → Fin r → Fv F v ⊗[F] E := fun a b => h2 * hR (Fv F v) σ J (f' a) (f' b)
  let f : Fin r → Fin n → Fv F v ⊗[F] E := fun b => f' b - ∑ a, c a b • y a.castSucc
  have hyf : ∀ i b, hR (Fv F v) σ J (y i) (f b) = if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [f]
    rw [GlobalTheory.FrameExtend.hR_sub_sum_right, hyf']
    simp [hyy0]
  have hfy : ∀ b i, hR (Fv F v) σ J (f b) (y i) = if i = b.castSucc then 1 else 0 := by
    intro b i
    rw [← hsw, hyf]
    split_ifs <;> simp
  have hf'y : ∀ b (d : Fin r), hR (Fv F v) σ J (f' b) (y d.castSucc) = if d = b then 1 else 0 := by
    intro b d
    rw [← hsw, hyf']
    split_ifs with h1 h2 h2 <;> simp_all [Fin.castSucc_inj]
  have hff : ∀ a b, hR (Fv F v) σ J (f a) (f b) = 0 := by
    intro a b
    have e1 : hR (Fv F v) σ J (f a) (f b) = hR (Fv F v) σ J (f a) (f' b) - c a b := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      have := fun d => hfy a (Fin.castSucc d)
      simp only [f] at this
      simp [this, Fin.castSucc_inj]
    have e2 : hR (Fv F v) σ J (f' b) (f a) = hR (Fv F v) σ J (f' b) (f' a) - c b a := by
      simp only [f]
      rw [GlobalTheory.FrameExtend.hR_sub_sum_right]
      congr 1
      simp [hf'y]
    have e3 : hR (Fv F v) σ J (f a) (f' b) = hR (Fv F v) σ J (f' a) (f' b) - h2 * hR (Fv F v) σ J (f' a) (f' b) := by
      rw [← hsw, e2, map_sub, hsw]
      simp only [c, map_mul, hsh, hsw]
    rw [e1, e3]
    simp only [c]
    linear_combination (-(hR (Fv F v) σ J (f' a) (f' b))) * hh
  refine ⟨f, ?_⟩
  have hTL : ∀ i (b : Fin r), gramE σ J (tupH P) (Fin.castAdd r i) (Fin.natAdd (r + 1) b) =
      if i = b.castSucc then 1 else 0 := by
    intro i b
    simp only [gramE, tupH, Fin.append_left, Fin.append_right, F0]
    refine Fin.lastCases ?_ (fun a => ?_) i
    · rw [Fin.snoc_last, ← hE_swap hinv hJ.1 P.z (P.f b), hfz, map_zero]
      exact (if_neg (Fin.castSucc_ne_last b).symm).symm
    · rw [Fin.snoc_castSucc, hef]
      simp only [Fin.castSucc_inj]
  funext i j
  simp only [Matrix.map_apply]
  show hR (Fv F v) σ J (Fin.append y f i) (Fin.append y f j) = _
  refine Fin.addCases (fun i => ?_) (fun a => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun b => ?_) j
  · rw [Fin.append_left, Fin.append_left, hyy, ← hG0]
    simp [gramE, tupH, Fin.append_left]
  · rw [Fin.append_left, Fin.append_right, hyf, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_left, hfy, ← hGh, hTL]
    split_ifs <;> simp
  · rw [Fin.append_right, Fin.append_right, hff]
    simp [gramE, tupH, Fin.append_right, hff0]

end GlobalTheory.FrameExtend
