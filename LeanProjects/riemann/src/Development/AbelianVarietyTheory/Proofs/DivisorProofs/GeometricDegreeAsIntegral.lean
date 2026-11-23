import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MIntEqOfLeviEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialChartContDiffAtTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviAtLinearCombinationPotential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FamilyMetricsSmooth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedIntegralOfCombinedMetricsStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.DegreeFormula Formalism.BasicNotions.DV Formalism.MainNotions.WeightThresholdDefs Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.FlagPoly GlobalTheory.FlagAr
open GlobalTheory.ShFam GlobalTheory.TrueGeo GlobalTheory.CxPts

noncomputable section
namespace GlobalTheory.GeoCObj

theorem mInt_scale (e : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P R : LocPot X) (c : ℝ) (g : X → ℝ) (hP : IsPotential A P) (hR : IsPotential A R)
    (h : ∀ j, ∀ y ∈ (A.chart j).target, ∀ w, leviAt A P j y w = c * leviAt A R j y w) :
    mInt A (fun _ => P) g = c ^ e * mInt A (fun _ => R) g := by
  have hcR : IsPotential A (R.rsmul c) := isPotentialRsmul A c R hR
  have h1 : mInt A (fun _ => P) g = mInt A (fun _ => R.rsmul c) g :=
    (LeviOnly.mInt_eq_of_leviEq e X A _ _ g (fun _ => hP) (fun _ => hcR) fun _ j y hy w => by
      rw [h j y hy w, Deg.leviAt_rsmul]).1
  rw [h1]
  have key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then R.rsmul c else R) g =
      c ^ k * mInt A (fun _ => R) g := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      have hF : ∀ i : Fin e, IsPotential A (if (i : ℕ) < k then R.rsmul c else R) := fun i => by
        split_ifs
        exacts [hcR, hR]
      have e1 : (fun i : Fin e => if (i : ℕ) < k + 1 then R.rsmul c else R) =
          Function.update (fun i : Fin e => if (i : ℕ) < k then R.rsmul c else R) ⟨k, hk⟩ (R.rsmul c) := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp
        · have hi' : (i : ℕ) ≠ k := fun h' => hi (Fin.ext h')
          rw [Function.update_of_ne hi]
          by_cases h2 : (i : ℕ) < k
          · rw [if_pos h2, if_pos (by omega)]
          · rw [if_neg h2, if_neg (by omega)]
      have e2 : (fun i : Fin e => if (i : ℕ) < k then R.rsmul c else R) =
          Function.update (fun i : Fin e => if (i : ℕ) < k then R.rsmul c else R) ⟨k, hk⟩ R := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp
        · rw [Function.update_of_ne hi]
      rw [e1, InhabCalc.mInt_update_rsmul A _ ⟨k, hk⟩ c R hF hR g, ← e2, ih (Nat.le_of_succ_le hk), pow_succ]
      ring
  have e3 : (fun i : Fin e => if (i : ℕ) < e then R.rsmul c else R) = fun _ => R.rsmul c :=
    funext fun i => if_pos i.2
  rw [← key e le_rfl, e3]

theorem mInt_combPot_eq_inter : GlobalTheory.Published.ChernDegree → ∀ (F : Type) [Field F] [NumberField F] (Y : GlobalTheory.ProjVar.Var F)
    (e : ℕ) (M : Man e) (I : ManIs M Y) (a : Fin (M.n + 1)) (ι : Type) [Fintype ι] (Δ : ι → Y.Dv)
    (m : ∀ i (σ : F →+* ℂ), (cxSt F).Met Y σ (Δ i)) (b : ι → ℤ) (Q : ι → LocPot (M.X a)), Y.dim = e →
    (∀ i σ, (cxSt F).mSmooth Y σ (Δ i) (m i σ)) →
    (∀ i, IsPot (I.pt a) (m i (I.ε a)) (Q i) ∧ IsPotential (M.A a) (Q i)) →
    mInt (M.A a) (fun _ => InhabCalc.combPot Q (fun i => (b i : ℝ)) (fun _ => 0)) (fun _ => 1) =
      (Y.inter (fun _ => ∑ i, b i • Δ i) : ℝ) := GlobalTheory.T.mixed_integral_of_combined_metrics

theorem geoC_onObj : Hypotheses2 → HypothesesH → OnObj fun _ O A T _ _ => ∀ B : ℝ, 2 ≤ B → ∀ (u : Wt O.Y) (s : ℚ), IsRat O.Y u → 0 < s →
    ∀ c, O.Y.geoC (O.Y.Mbar B u s) c = (T.M c).int (fun _ => (T.F c).form (A.sh u s) s 0) (fun _ _ => 1) := by
  intro _ hH D O hO _ A T H h B _ u s hu hs c
  obtain ⟨x, P, hc⟩ := hO
  have hChern : GlobalTheory.Published.ChernDegree := hH.deg.2
  set u' : D.what₂.Tau → Fin O.N → ℚ := fun τ i => ratOf (u τ i) with hu'
  have hu'c : ∀ τ i, ((u' τ i : ℚ) : ℝ) = u τ i := fun τ i => by
    obtain ⟨q, hq⟩ := hu τ i
    simp [hu', hq]
  set ρ := P.gens c B with hρ
  set t : Option (DV.Rt D.what₂.Tau O.N) → ℚ := fun o => o.elim s fun x => -(u' x.1 x.2 - s * P.dirQ x.1 x.2) with ht

  have hL : O.Y.geoC (O.Y.Mbar B u s) c = (((O.var c).inter fun _ => ∑ o, combNum ρ t o • (ρ o).D : ℤ) : ℝ) /
      ((combDen ρ t : ℕ) : ℝ) ^ (O.var c).dim := by
    change Adl.deg (O.Mb B u s c) = _
    rw [hc.Mb]
    unfold mbarOf
    rw [if_pos ⟨hu, hs⟩]
    rfl
  have hR : (T.M c).int (fun _ => (T.F c).form (A.sh u s) s 0) (fun _ _ => 1) =
      (T.M c).κ * ∑ a, mInt ((T.M c).A a) (fun _ => (T.F c).form (A.sh u s) s 0 a) (fun _ => 1) := rfl
  have hdim : (O.var c).dim = dimY O.Y := O.dim_eq c

  have key : ∀ a, mInt ((T.M c).A a) (fun _ => (T.F c).form (A.sh u s) s 0 a) (fun _ => 1) =
      (((combDen ρ t : ℕ) : ℝ)⁻¹) ^ (O.var c).dim * (((O.var c).inter fun _ => ∑ o, combNum ρ t o • (ρ o).D : ℤ) : ℝ) := by
    intro a
    obtain ⟨Qt, hQt, hLt⟩ := (h.an c).th (A.sh u s) a
    obtain ⟨Qa, hQa, hLa⟩ := (h.an c).a a
    let Q : Option (DV.Rt D.what₂.Tau O.N) → LocPot ((T.M c).X a) := fun o => o.elim (Qa ()) Qt
    have hmove : ∀ {n n' : Pad.Letter O.S.Dw → ℤ} {R : LocPot ((T.M c).X a)}, n = n' →
        (IsPot ((h.man c).pt a) (refMet x O.Φ c ((h.man c).ε a) n) R ∧ IsPotential ((T.M c).A a) R) →
        (IsPot ((h.man c).pt a) (refMet x O.Φ c ((h.man c).ε a) n') R ∧ IsPotential ((T.M c).A a) R) := by
      rintro _ _ _ rfl hh; exact hh
    have hQ : ∀ o, IsPot ((h.man c).pt a) ((ρ o).m ((h.man c).ε a)) (Q o) ∧ IsPotential ((T.M c).A a) (Q o) := by
      rintro (_ | r)
      · have hh := hQa ()
        rw [hc.ab_eq] at hh
        exact hh
      · have hh := hQt r
        rw [hc.h0_eq] at hh
        exact hmove (expo_rootSym _ _ _ _ _).symm hh
    have hsm : ∀ o σ, (cxSt D.what₂.LL).mSmooth _ σ ((ρ o).D) ((ρ o).m σ) := by
      rintro (_ | r) σ
      · exact P.ab_smooth c σ
      · exact (GlobalTheory.metsOf_smooth D O.A O.N O.j O.S O.κ O.s x O.Φ c σ _).2.1
    set q : ℝ := ((combDen ρ t : ℕ) : ℝ) with hq
    have hq0 : q ≠ 0 := Nat.cast_ne_zero.2 (combDen ρ t).ne_zero
    have hb : ∀ o, ((combNum ρ t o : ℤ) : ℝ) = q * (t o : ℝ) / (((ρ o).n : ℕ) : ℝ) := fun o => by
      have e := congrArg (fun r : ℚ => (r : ℝ)) (combNum_mul ρ t o)
      push_cast at e
      have hn : (((ρ o).n : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (ρ o).n.ne_zero
      rw [eq_div_iff hn, e]
    have hz : ((T.M c).A a).Smooth (fun _ => (0 : ℝ)) := Deg.smooth_const _ 0
    have hthp := T.th_pot c (A.sh u s) a
    have hap := T.a_pot c a
    have h12 : IsPotential ((T.M c).A a) ((T.F c).th (A.sh u s) a + ((T.F c).a a).rsmul s) :=
      isPotentialAdd _ _ _ hthp (isPotentialRsmul _ _ _ hap)
    have hpot : IsPotential ((T.M c).A a) ((T.F c).form (A.sh u s) s 0 a) :=
      isPotentialAdd _ _ _ h12 (isPotential_ofFun _ _ hz)
    have hcp : IsPotential ((T.M c).A a) (InhabCalc.combPot Q (fun o => (combNum ρ t o : ℝ)) fun _ => 0) :=
      InhabCalc.isPotential_combPot _ Q (fun o => (hQ o).2) _ _ hz
    rw [mInt_scale _ _ _ _ _ q⁻¹ _ hpot hcp ?_, mInt_combPot_eq_inter hChern _ _ _ _ (h.man c) a _ (fun o => (ρ o).D)
      (fun o σ => (ρ o).m σ) (combNum ρ t) Q hdim hsm hQ, ← hdim]
    intro j y hy w
    rw [LeviFormCombination.GlobalTheory.CompanionTheory.LeviComb.leviAt_combPot _ _ _ _ Q _ _ (fun o => (hQ o).2) hz j y hy w, Deg.leviAt_const]
    show leviAt _ ((T.F c).th (A.sh u s) a + ((T.F c).a a).rsmul s + LocPot.ofFun fun _ => 0) j y w = _
    rw [Deg.leviAt_add _ h12 (isPotential_ofFun _ _ hz) j hy w, Deg.leviAt_const,
      Deg.leviAt_add _ hthp (isPotentialRsmul _ _ _ hap) j hy w, Deg.leviAt_rsmul, hLt j y hy w, hLa j y hy w,
      Fintype.sum_option]

    have tn : q⁻¹ * (q * (t none : ℝ) / (((ρ none).n : ℕ) : ℝ)) = (s : ℝ) * ((((O.met.ab c).n : ℕ) : ℝ))⁻¹ := by
      rw [hc.ab_eq]
      show q⁻¹ * (q * (s : ℝ) / (((P.ab c).n : ℕ) : ℝ)) = _
      field_simp
    have ts : ∀ r : DV.Rt D.what₂.Tau O.N, q⁻¹ * (q * (t (some r) : ℝ) / (((ρ (some r)).n : ℕ) : ℝ)) = -A.sh u s r.1 r.2 := by
      intro r
      show q⁻¹ * (q * ((-(u' r.1 r.2 - s * P.dirQ r.1 r.2) : ℚ) : ℝ) / ((1 : ℕ) : ℝ)) = -(u r.1 r.2 - s * A.dir r.1 r.2)
      rw [h.aux.dir, hc.dir_eq]
      push_cast
      rw [hu'c]
      field_simp
      rfl
    simp only [Q, Option.elim, Fintype.sum_unique, add_zero, hb]
    rw [mul_add, Finset.mul_sum]
    simp only [← mul_assoc, tn, ts]
    ring

  rw [hL, hR, Finset.sum_congr rfl fun a _ => key a, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    (T.M c).κ_eq]
  have : ((T.M c).n : ℝ) + 1 ≠ 0 := by positivity
  push_cast
  rw [← mul_assoc, inv_mul_cancel₀ this, one_mul, inv_pow, div_eq_inv_mul]

end GlobalTheory.GeoCObj
