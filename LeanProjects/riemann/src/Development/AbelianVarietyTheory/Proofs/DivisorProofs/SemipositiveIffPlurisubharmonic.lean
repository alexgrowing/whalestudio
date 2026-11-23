import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffAtOfIsPotential
import ReciprocityTheory.AnalyticForms.PotentialTheory.PshShiftA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MetricSmoothPshIffPotentialPshStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CombinedMetricLocalPotentialExistsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.ShFam

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.SemiposObj

section Levi

variable {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}

theorem isPsh_iff_leviAt {P : LocPot X} (hP : IsPotential A P) :
    IsPsh A P ↔ ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, 0 ≤ leviAt A P j y w := by
  refine ⟨fun hp j y hy w => hp _ j y ⟨hy, P.mem_U _⟩ w, fun h x j y hy w => ?_⟩
  rw [GlobalTheory.LeviOnly.levi_base hP x j hy.1 hy.2]
  exact h j y hy.1 w

theorem leviAt_add {P Q : LocPot X} (hP : IsPotential A P) (hQ : IsPotential A Q) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : leviAt A (P + Q) j y w = leviAt A P j y w + leviAt A Q j y w := by
  have h := levi_add_smul 1 (GlobalTheory.LeviOnly.pot_two hP ((A.chart j).symm y) j hy (P.mem_U _))
    (GlobalTheory.LeviOnly.pot_two hQ ((A.chart j).symm y) j hy (Q.mem_U _)) w
  simp only [one_mul] at h
  exact h

theorem leviAt_rsmul {P : LocPot X} (hP : IsPotential A P) (c : ℝ) (j : Fin A.n) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target) (w : Fin e → ℂ) : leviAt A (P.rsmul c) j y w = c * leviAt A P j y w := by
  have h := levi_add_smul c (f := fun _ => (0 : ℝ)) contDiffAt_const
    (GlobalTheory.LeviOnly.pot_two hP ((A.chart j).symm y) j hy (P.mem_U _)) w
  have h0 : levi (fun _ : Fin e → ℂ => (0 : ℝ)) y w = 0 := levi_clm 0 y w
  simp only [zero_add] at h
  rw [h0, zero_add] at h
  exact h

end Levi

theorem semiPos_iff_isPsh {F : Type} [Field F] [NumberField F] {Y : Var F} {e : ℕ} {M : Man e} (I : ManIs M Y)
    (he : e = Y.dim) {ι : Type} [Fintype ι] (Mb : Adl (cxSt F) Y) (ρ : ι → Adl (cxSt F) Y) (t : ι → ℝ)
    (g : ∀ σ, Pts Y σ → ℝ) (P : M.Pot) (hc : IsComb Mb ρ t g) (hP : ∀ a, IsPotential (M.A a) (P a))
    (hg : ∀ a, (M.A a).Smooth fun z => g (I.ε a) (I.pt a z))
    (hQ : ∀ a, ∃ Q : ι → LocPot (M.X a), (∀ i, IsPot (I.pt a) ((ρ i).m (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) ∧
      ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (P a) j y w =
        ∑ i, t i / (((ρ i).n : ℕ) : ℝ) * leviAt (M.A a) (Q i) j y w +
          leviAt (M.A a) (LocPot.ofFun fun z => g (I.ε a) (I.pt a z)) j y w) :
    Mb.SemiPos ↔ ∀ a, IsPsh (M.A a) (P a) := by
  have step : ∀ a, (cxSt F).mSmooth Y (I.ε a) Mb.D (Mb.m (I.ε a)) ∧
      ((cxSt F).mPsh Y (I.ε a) Mb.D (Mb.m (I.ε a)) 0 ↔ IsPsh (M.A a) (P a)) := by
    intro a
    obtain ⟨Q, hQp, hQl⟩ := hQ a
    obtain ⟨QM, h1, h2, h3⟩ := GlobalTheory.T.combined_metric_local_potential_exists F Y e M I ι Mb ρ t g a Q hc hQp (hg a)
    obtain ⟨hs, hiff⟩ := GlobalTheory.T.metric_smooth_psh_iff_potential_psh F Y e M I he Mb.D a (Mb.m (I.ε a)) QM h1 h2
    refine ⟨hs, hiff.trans ?_⟩
    rw [isPsh_iff_leviAt h2, isPsh_iff_leviAt (hP a)]
    have hn : (0 : ℝ) < ((Mb.n : ℕ) : ℝ) := Nat.cast_pos.2 Mb.n.pos
    refine forall_congr' fun j => forall₂_congr fun y hy => forall_congr' fun w => ?_
    rw [h3 j y hy w, ← hQl j y hy w]
    exact mul_nonneg_iff_of_pos_left hn
  constructor
  · intro h a
    exact (step a).2.1 (h (I.ε a)).2
  · intro h σ
    obtain ⟨a, rfl⟩ := I.ε.surjective σ
    exact ⟨(step a).1, (step a).2.2 (h a)⟩

theorem isPot_h0_congr {D : D7} (O : Setup D) (c : O.s.Comp) {X : Type} [TopologicalSpace X] (σ : D.what₂.LL →+* ℂ)
    (h : X → Pts (O.var c) σ) (Q : LocPot X) {n n' : Pad.Letter O.S.Dw → ℤ} (e : n = n')
    (hQ : IsPot h (O.met.h0 c σ n) Q) : IsPot h (O.met.h0 c σ n') Q := by
  subst e
  exact hQ

theorem semipos_onObj : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s → Dominant O.Y (A.sh u s) → (∀ c, (T.M c).Smooth ((T.F c).phS (A.sh u s) s)) → (O.Y.semipos (O.Y.Mbar B u s) ↔ ∀ c σ, IsPsh ((T.M c).A σ) ((T.F c).form (A.sh u s) s ((T.F c).phS (A.sh u s) s) σ)) := by
  intro _ _ D O hC _ A T H h B hB u s hu hs hd hsm
  show (∀ k, Adl.SemiPos (O.Mb B u s k)) ↔ _
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  have e1 : A.sh u s = fun τ i => u τ i - (s : ℝ) * O.met.dir τ i := by
    funext τ i
    simp [SlopeTestRemainingChoices.sh, h.aux.dir]
  have hmb := hC.mbIs B hB u s hu hs _ e1 (e1 ▸ hd)
  refine forall_congr' fun c => ?_
  have hsmc := hsm c
  have hphS : ∀ a, (fun z => O.met.reg c ((h.man c).ε a) (A.sh u s) (Real.exp (-((s : ℝ) ^ 2)⁻¹)) ((h.man c).pt a z) / 2) =
      (T.F c).phS (A.sh u s) s a := fun a => funext fun z => ((h.an c).phS _ _ hs' a z).symm
  refine semiPos_iff_isPsh (h.man c) ?_ (O.Mb B u s c) _ _ _ ((T.F c).form (A.sh u s) s ((T.F c).phS (A.sh u s) s))
    (hmb c) (fun a => ?_) (fun a => ?_) (fun a => ?_)
  · show dimY O.Y = (O.var c).dim
    rw [O.dim_eq c]
    rfl
  · exact isPotentialAdd _ _ _ (isPotentialAdd _ _ _ (T.th_pot c _ a) (isPotentialRsmul _ _ _ (T.a_pot c a)))
      (isPotential_ofFun _ _ (hsmc a))
  · simp only [hphS a]
    exact hsmc a
  · obtain ⟨Qt, hQt, hlt⟩ := (h.an c).th (A.sh u s) a
    obtain ⟨Qa, hQa, hla⟩ := (h.an c).a a
    refine ⟨fun o => o.elim (Qa ()) Qt, fun o => ?_, fun j y hy w => ?_⟩
    · cases o with
      | none => exact hQa ()
      | some x => exact ⟨isPot_h0_congr O c _ _ _ (expo_rootSym _ _ _ _ _).symm (hQt x).1, (hQt x).2⟩
    · have p1 := T.th_pot c (A.sh u s) a
      have p2 := isPotentialRsmul _ (s : ℝ) _ (T.a_pot c a)
      have p3 := isPotential_ofFun _ _ (hsmc a)
      rw [show (T.F c).form (A.sh u s) s ((T.F c).phS (A.sh u s) s) a =
          (T.F c).th (A.sh u s) a + ((T.F c).a a).rsmul s + LocPot.ofFun ((T.F c).phS (A.sh u s) s a) from rfl,
        leviAt_add (isPotentialAdd _ _ _ p1 p2) p3 j hy, leviAt_add p1 p2 j hy, leviAt_rsmul (T.a_pot c a) _ j hy,
        hlt j y hy w, hla j y hy w, Fintype.sum_option, hphS a]
      have hn1 : ∀ x, (((O.root0 c (setB O.Y B) x).n : ℕ) : ℝ) = 1 := fun x => by
        rw [show (O.root0 c (setB O.Y B) x).n = 1 from rfl]
        simp
      simp only [Option.elim, hn1, div_one, Fintype.univ_punit, Finset.sum_singleton]
      ring

end GlobalTheory.SemiposObj
