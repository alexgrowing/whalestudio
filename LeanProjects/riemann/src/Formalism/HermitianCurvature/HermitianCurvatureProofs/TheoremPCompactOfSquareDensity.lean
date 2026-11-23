import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheoremPCompactOfStepDensity

open MeasureTheory Filter Topology
open scoped Matrix

noncomputable section

namespace Formalism.FourierDecayAlt.P5.HerD

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Wd Formalism.FourierDecayAlt.P5 Formalism.FourierDecayAlt.P5.HerA Formalism.FourierDecayAlt.P5.HerB Formalism.FourierDecayAlt.P5.HerC

section Dens

variable {k r : ℕ} {z z' : Fin (2 * r + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp]
  [FiniteDimensional ℂ Wq] {π : Mx k r → (Wp →L[ℂ] Wp)} {π' : Mx k r → (Wq →L[ℂ] Wq)} {S : Type} [Fintype S]
  [DecidableEq S]

def Dens (μ : Measure (Mt k r)) (l : Fin r) (u v : Ix S → RadSp k r z z' π π') (c : Fin r → ℂ) (t : ℂ) : ℂ :=
  ((‖t‖ ^ (-2 : ℤ) : ℝ) : ℂ) * form μ l.succ u v (Function.update c l t)

theorem dens_int (μ : Measure (Mt k r)) [SFinite μ] (hμ : B.IsHaarOn (Glev k r (Fin.last r)) μ) (l : Fin r)
    (u v : Ix S → RadSp k r z z' π π') (hu : ∀ a, u a ∈ lcSub k r z z' π π') (hv : ∀ a, v a ∈ lcSub k r z z' π π')
    (c : Fin r → ℂ) (Iu : ∀ a, LevelSquareIntegrable μ l.castSucc (u a) c) (Iv : ∀ a, LevelSquareIntegrable μ l.castSucc (v a) c) :
    Integrable (Dens μ l u v c) ∧ ∫ t, Dens μ l u v c t = form μ l.castSucc u v c := by
  have hint := formIntOuter_of_l2I μ hμ l.castSucc u v hu hv c Iu Iv
  set f : Cf r l.castSucc → ℂ := fun c' =>
    ((∏ j, ‖c' j‖ ^ (-2 : ℤ) : ℝ) : ℂ) * ∑ a, pairAt μ (u a) (v a) (glue l.castSucc c c') with hf
  have hmp := coordinate_split_measurePreserving (r := r) l
  have hval : ∀ p : ℂ × Cf r l.succ, f ((coordinateSplit (r := r) l).symm p) = ((‖p.1‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
      (((∏ j, ‖p.2 j‖ ^ (-2 : ℤ) : ℝ) : ℂ) *
        ∑ a, pairAt μ (u a) (v a) (glue l.succ (Function.update c l p.1) p.2)) := by
    intro p
    have hw := weight_coordinate_split (r := r) l ((coordinateSplit (r := r) l).symm p)
    have hg := glue_coordinate_split (r := r) l c ((coordinateSplit (r := r) l).symm p)
    simp only [MeasurableEquiv.apply_symm_apply] at hw hg
    simp only [hf]
    rw [hw, hg, Complex.ofReal_mul, mul_assoc]
  have hF : Integrable (fun p : ℂ × Cf r l.succ => f ((coordinateSplit (r := r) l).symm p)) (volume.prod volume) :=
    (hmp.symm.integrable_comp_emb (coordinateSplit (r := r) l).symm.measurableEmbedding (g := f)).mpr hint
  have h2 := hF.integral_prod_left
  refine ⟨h2.congr (Filter.Eventually.of_forall fun t => ?_), (form_split μ l u v c hint).symm⟩
  show ∫ c'', f ((coordinateSplit (r := r) l).symm (t, c'')) = Dens μ l u v c t
  simp only [hval, Dens, form]
  rw [integral_const_mul]

end Dens

def DecayRest (n : ℕ) (C : ℝ) (D : ℂ → ℂ) : Prop :=
  Integrable (fun t : ℂ => ((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t) ∧ (∀ t, t ≠ 0 → ContinuousAt D t) ∧
    (∀ s, ‖∫ t, fsv s t * D t‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))) ∧
    ∀ s, ‖∫ t, fsv s t * (((1 + ‖t‖ ^ 2) ^ 2 : ℝ) • D t)‖ ≤ C * (1 + ‖s‖) ^ (-((n : ℝ) + 3))

def LevelDensitySquareIntegrable : Prop :=
  ∀ (Wp Wq : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq] (S : Type) [Fintype S] [DecidableEq S]
    (P : M.Par) (z z' : Fin (2 * P.r + P.k + 1) → ℂ) (π : Mx P.k P.r → (Wp →L[ℂ] Wp))
    (π' : Mx P.k P.r → (Wq →L[ℂ] Wq)) (X : ActualOps P.k P.r z z' π π') (μ : Measure (Mt P.k P.r))
    (L : R.LevelData (Pr (RadSp P.k P.r z z' π π')) P.r) (st : Fr.Start (Pr (RadSp P.k P.r z z' π π'))) (l0 : ℕ)
    (D : B.RealPlaceData P.k P.r Wp Wq),
    IsData P z z' π π' X μ L st l0 → 1 ≤ l0 → l0 ≤ P.k → D.z = z → D.z' = z' → D.π = π → D.π' = π' →
    ∀ w : List (Letter ℂ S), WordOK P z z' π π' st l0 w → ∀ (l : Fin P.r), l.val = 0 →
    ∀ (x y : Ix S → RadSp P.k P.r z z' π π'),
      InK (herKc S P z z' π π' L st l0 D l.castSucc) x → InK (herKc S P z z' π π' L st l0 D l.castSucc) y →
      ∀ c ∈ OmX P.r,
      ∃ (n K : ℕ) (C : ℝ) (u v : Fin K → Ix S → RadSp P.k P.r z z' π π') (j : Fin K → ℕ)
        (vv : ∀ i, Fin (j i) → ℂ) (a : Fin K → ℂ),
        (∀ i b, u i b ∈ lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (u i b) c ∧
          v i b ∈ lcSub P.k P.r z z' π π' ∧ LevelSquareIntegrable μ l.castSucc (v i b) c) ∧
        (∀ i, j i ≤ n) ∧ (∀ i, DecayRest n C (Dens μ l (u i) (v i) c)) ∧
        (∀ t, t ≠ 0 → ph L st μ l w x y c t = ∑ i, a i * iteratedFDeriv ℝ (j i) (Dens μ l (u i) (v i) c) t (vv i)) ∧
        ∑ i, a i * (if j i = 0 then form μ l.castSucc (u i) (v i) c else 0) = RRform L st μ l.castSucc w x y c

theorem step_density_of_square (h : LevelDensitySquareIntegrable) : StepExp0 := by
  intro Wp Wq _ _ _ _ _ _ S _ _ P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have : SFinite μ := sfinite_of_isHaarOn _ μ hD.2.1
  obtain ⟨n, K, C, u, v, j, vv, a, hL2, hjn, hrest, hexp, hI⟩ :=
    h Wp Wq S P z z' π π' X μ L st l0 D hD h1 h2 hz hz' hπ hπ' w hw l hl x y hx hy c hc
  have hdi := fun i => dens_int μ hD.2.1 l (u i) (v i) (fun b => (hL2 i b).1) (fun b => (hL2 i b).2.2.1) c
    (fun b => (hL2 i b).2.1) (fun b => (hL2 i b).2.2.2)
  refine ⟨n, K, C, fun i => Dens μ l (u i) (v i) c, j, vv, a, hjn, fun i => ⟨(hdi i).1, hrest i⟩, hexp, ?_⟩
  rw [← hI]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs
  · rw [(hdi i).2]
  · rfl

end Formalism.FourierDecayAlt.P5.HerD
