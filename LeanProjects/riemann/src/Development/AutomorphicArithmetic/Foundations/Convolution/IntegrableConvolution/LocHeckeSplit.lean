import Mathlib
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.ThickFrames
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.MatchProd
import Development.AutomorphicArithmetic.Foundations.Convolution.IntegrableConvolution.SphLaws
import GroundTheory.GlobalFields.KummerTheory.Splitting

noncomputable section

open MeasureTheory NumberField IsDedekindDomain
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm GroundTheory.Global GroundTheory.Global.SemiLocal
open PositivityTheory.Rg.Tf.Geo

namespace UpperTheory.ConvolutionTheory.L1

private theorem isSph_cvAll {K : Type} [Field K] [NumberField K] {n : ℕ} {v : Pl K}
    [MeasurableSpace (GL (Fin n) (v.adicCompletion K))] [BorelSpace (GL (Fin n) (v.adicCompletion K))]
    (mF : Measure (GL (Fin n) (v.adicCompletion K))) (hH : mF.IsHaarMeasure)
    (h1 : mF (GLnLocal.integralGL (v.adicCompletion K) n) = 1) :
    ∀ (m : ℕ) (p : Fin (m + 1) → MvPolynomial (Fin n) ℂ) (φ : Fin (m + 1) → GL (Fin n) (v.adicCompletion K) → ℂ),
      (∀ i, GM.IsSph v (p i) (φ i)) → GM.IsSph v (∏ i, p i) (cvAll mF m φ)
  | 0, p, φ, h => by simpa [cvAll] using h 0
  | m + 1, p, φ, h => by
    rw [Fin.prod_univ_succ]
    exact (sphLaws.2 K n v).2.2 mF hH h1 _ _ _ _ (h 0)
      (isSph_cvAll mF hH h1 m (Fin.tail p) (Fin.tail φ) fun i => h i.succ)

end UpperTheory.ConvolutionTheory.L1

open GroundTheory.Global.SemiLocal in
theorem UpperTheory.ConvolutionTheory.L1.locHeckeSplit :
    UpperTheory.ConvolutionTheory.GM.LocHeckeSplit := by
  intro F E _ _ _ _ _ _ σ hσ hp n hn v hv p h f hh hf
  obtain ⟨m, hm⟩ : ∃ m, Module.finrank F E = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  obtain ⟨w₀⟩ := nonempty_placesOver E v
  obtain ⟨w, -, hM⟩ := UpperTheory.ConvolutionTheory.L1.matchProd F E σ hσ m hm n v w₀ hv
  intro _ _ _ _ mE mF hE hF h1E h1F
  have hc : ∀ u : PlacesOver E v, Continuous (h u) ∧ HasCompactSupport (h u) :=
    fun u => (UpperTheory.ConvolutionTheory.L1.sphLaws.2 E n u.1).1 _ _ (hh u)
  have hm' := hM h hc mF hF h1F
  have hs := UpperTheory.ConvolutionTheory.L1.isSph_cvAll mF hF h1F m (fun i => p (w i))
    (fun i g => h (w i) (mapGL n (completionMap v (w i).1) g))
    (fun i => UpperTheory.ConvolutionTheory.L1.sphLaws.1 F E v (w i) (hv (w i)) n _ _ (hh (w i)))
  have hprod : (∏ i, p (w i)) = ∏ᶠ u, p u := by
    rw [finprod_eq_prod_of_fintype]
    exact Equiv.prod_comp w p
  rw [hprod] at hs
  have key := (UpperTheory.ConvolutionTheory.L1.sphLaws.2 F n v).2.1 _ _ _ hs hf
  rw [key] at hm'
  exact hm' mE mF hE hF h1E h1F
