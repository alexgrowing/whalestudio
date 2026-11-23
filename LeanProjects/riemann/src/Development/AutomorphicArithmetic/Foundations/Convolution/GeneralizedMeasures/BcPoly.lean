import Development.AutomorphicArithmetic.Foundations.Convolution.GeneralizedMeasures.HeckeFinAlt

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.RightCosetSpace
open GroundTheory.Automorphic.AutomorphicForm GroundTheory.Automorphic.CuspidalSpectrum UpperTheory.ConvolutionTheory.C PositivityTheory.Rg.Tf.Core PositivityTheory.Rg.Tf.Geo
open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Automorphic.Spherical
open UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.GM

private theorem bc_at {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (w : Pl E) (p : MvPolynomial (Fin n) ℂ) :
    bcPR F (map C (atPl w p) : PR E n) = map C (atPl (w.under (𝓞 F)) (aeval (powE (resDeg F w)) p)) := by
  unfold atPl
  induction p using MvPolynomial.induction_on with
  | C a => simp [bcPR]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp =>
    simp only [map_mul, hp]
    simp [bcPR]

private theorem bc_mono {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (wd : List (Option (Ix E n))) : bcPR F (C (mono wd) : PR E n) = C (mono (wd.map (resIx F))) := by
  unfold mono
  induction wd with
  | nil => simp
  | cons a l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, ih]
    simp [bcPR, resIx]

theorem UpperTheory.ConvolutionTheory.GM.bcPoly :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (κ : Finset (Pl E)) (κF : Finset (Pl F)), (∀ w ∈ κ, w.under (𝓞 F) ∈ κF) →
    ∀ (p : Pl E → MvPolynomial (Fin n) ℂ) (wd : List (Option (Ix E n))) [DecidableEq (Pl F)],
      bcPR F (C (mono wd) * map C (∏ w ∈ κ, atPl w (p w))) = C (mono (wd.map (resIx F))) *
        map C (∏ v ∈ κF, atPl v (∏ w ∈ κ.filter fun w => w.under (𝓞 F) = v, aeval (powE (resDeg F w)) (p w))) := by
  intro F E _ _ _ _ _ n κ κF hκ p wd _
  rw [map_mul, bc_mono, map_prod, map_prod]
  congr 1
  simp only [bc_at]
  rw [← map_prod, ← Finset.prod_fiberwise_of_maps_to hκ]
  congr 1
  refine Finset.prod_congr rfl fun v _ => ?_
  unfold atPl
  rw [map_prod]
  refine Finset.prod_congr rfl fun w hw => ?_
  rw [(Finset.mem_filter.1 hw).2]
