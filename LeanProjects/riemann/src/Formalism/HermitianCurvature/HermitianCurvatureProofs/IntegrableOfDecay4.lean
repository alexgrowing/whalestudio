import Formalism.HermitianCurvature.RealInputsClosedAdmissibleSettings
import Formalism.HermitianCurvature.HermitianCurvatureProofs.VectorIsomorphismLevels
import Formalism.HermitianCurvature.HermitianCurvatureProofs.PBFVstep
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SliceCompactSupportCoefficient
import Formalism.HermitianCurvature.HermitianCurvatureProofs.JfBetaAdjCOfLemmaBNorm

open Matrix MeasureTheory

noncomputable section

namespace Formalism.FourierDecayAlt.P.PBO

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.YangianSpanCharacter.T Formalism.FourierDecayAlt.P5

def FormOne : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (P0 : M.Par)
    (T : D.LevTower P0.k P0.r Wp Wq) (j : Fin (P0.r + 1))
    (X : Q.ActualOps (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π')
    (μ : Measure (Formalism.QuantumDeterminants.Mt (JC.parLev P0 j).k (JC.parLev P0 j).r))
    (L : R.LevelData (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π')) (JC.parLev P0 j).r)
    (st : Fr.Start (Q.Pr (Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π
      (T.bs j).π'))) (l0 : ℕ),
    P5.IsData (JC.parLev P0 j) (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π' X μ L st l0 →
    KB.ZetaNorm (T.bs j) μ →
    ∀ (w : List C.Letter) (F F' : Wd.Ix (Fin w.length) → B.Mat P0.k (P0.r - j) → (Wq →L[ℂ] Wp))
      (Φ Φ' : Wd.Ix (Fin w.length) →
        Q.RadSp (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z' (T.bs j).π (T.bs j).π') (ε : ℝ),
      0 < ε → (∀ a, JC.NiceCoef (T.bs j) ε (F a)) → (∀ a, JC.NiceCoef (T.bs j) ε (F' a)) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F a)) y.1 y.2) →
      (∀ a, ∀ y ∈ Q.DomR (JC.parLev P0 j).k (JC.parLev P0 j).r (T.bs j).z (T.bs j).z',
        (Φ' a : Q.Fn (JC.parLev P0 j).k (JC.parLev P0 j).r (Wq →L[ℂ] Wp)) y.1 y.2 =
          Q.resG (JC.parLev P0 j).k (JC.parLev P0 j).r (Fin.last _) (B.JF (T.bs j) (F' a)) y.1 y.2) →
      D.formLev T (M.sgn P0 l0) j w F F' = P5.form μ 0 (P5.act (P5.RRi L st 0 (D.positionted w)) Φ) Φ' 0

def ZetaNormExists : Prop :=
  ∀ (k r : ℕ) (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] (Bs : B.RealPlaceData k r Wp Wq), ∃ μ : Measure (Mt k r), KB.ZetaNorm Bs μ

theorem integrable_of_decay4 {φ : ℂ → ℂ} (hφ : Continuous φ) {C : ℝ}
    (hC : ∀ t, ‖φ t‖ ≤ C * (1 + ‖t‖) ^ (-4 : ℤ)) : Integrable φ := by
  have hd : Integrable (fun t : ℂ => (1 + ‖t‖) ^ (-(4 : ℝ))) volume := by
    refine integrable_one_add_norm ?_
    rw [Complex.finrank_real_complex]; norm_num
  refine Integrable.mono' (hd.const_mul C) hφ.aestronglyMeasurable (Filter.Eventually.of_forall fun t => ?_)
  have e : (1 + ‖t‖) ^ (-4 : ℤ) = (1 + ‖t‖) ^ (-(4 : ℝ)) := by
    rw [← Real.rpow_intCast]; norm_num
  rw [← e]; exact hC t

theorem nice_common {k ρ : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
    [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {S : Type} [Fintype S] (Bs : B.RealPlaceData k ρ Wp Wq)
    {x : S → B.Mat k ρ → (Wq →L[ℂ] Wp)} (h : ∀ a, KB.CptCoef Bs (x a)) :
    ∃ ε, 0 < ε ∧ ∀ a, JC.NiceCoef Bs ε (x a) := by
  classical
  choose R hR using fun a => (h a).2.1
  choose εf hεf0 hεf using fun a => (h a).2.2
  let Sε : Finset ℝ := insert 1 (Finset.univ.image εf)
  have hne : Sε.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨Sε.min' hne, ?_, fun a => ⟨(h a).1, fun A m => ?_, fun g hg hg0 => ?_⟩⟩
  · rw [Finset.lt_min'_iff]
    intro y hy
    rcases Finset.mem_insert.1 hy with rfl | hy
    · exact one_pos
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
      exact hεf0 a
  · refine Formalism.FourierDecayAlt.P.JFxG.cptInCC_G (h a).1 (Formalism.FourierDecayAlt.P.PBE.isCompact_gN_le k ρ (R a)) (fun g hg hgC => ?_) A m
    by_contra h0
    exact hgC (hR a g hg h0)
  · exact le_trans (Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ a))))
      (hεf a g hg hg0)

end Formalism.FourierDecayAlt.P.PBO
