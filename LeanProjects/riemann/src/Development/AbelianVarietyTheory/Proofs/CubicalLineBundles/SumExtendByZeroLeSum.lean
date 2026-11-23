import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.LogQdLeRd
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.LocalToGlobal.ProjectiveLattices.RosatiLatticeNorms.CmFrameOfEq
import Formalism.LocalToGlobal.ProjectiveLattices.ArchimedeanQuadraticData.ArcWitnessExistence.DataXOfModel
import Formalism.LocalToGlobal.ProjectiveLattices.ExtendedPointBaseChange
import Formalism.LocalToGlobal.ProjectiveLattices.HostInt
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FactPrincipalDatum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLam
import Formalism.LocalToGlobal.ProjectiveLattices.HostSize
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.QuadraticCoefficientForms

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.MainNotions Formalism.BasicNotions
open GlobalTheory GlobalTheory.RunIn

noncomputable section

namespace GlobalTheory.WtSizes

theorem extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (i : ℕ) : Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  unfold Formalism.L2.Pj.ext0
  split_ifs with hi
  · exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, hi⟩ : Fin p))
  · exact Nat.zero_le _

theorem sum_extendByZero_le_sum {p : ℕ} (f : Fin p → ℕ) (m : ℕ) : ∑ i : Fin m, Formalism.L2.Pj.ext0 f i ≤ ∑ k, f k := by
  have h1 : ∑ k, f k = ∑ i : Fin p, Formalism.L2.Pj.ext0 f i :=
    Finset.sum_congr rfl fun i _ => by simp [Formalism.L2.Pj.ext0, i.isLt]
  rw [h1, Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) m,
    Fin.sum_univ_eq_sum_range (fun i => Formalism.L2.Pj.ext0 f i) p]
  refine Finset.sum_le_sum_of_ne_zero fun i _ hi => ?_
  rw [Finset.mem_range]
  by_contra hp
  exact hi (by simp [Formalism.L2.Pj.ext0, hp])

variable {D : D7} {j : ℕ}

open Classical in

def tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) : ℕ :=
  ∑ t : D.what₂.Tau, ((if b = DV.tauEmb D t then ∑ i, w.aP t i else 0) +
    if b = conjEmb (DV.tauEmb D t) then ∑ i, w.aM t i else 0)

theorem wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (i : ℕ) : wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  refine Finset.sum_le_sum fun t _ => add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl
  · dsimp only
    split_ifs
    · exact extendByZero_le_sum _ _
    · exact le_rfl

theorem sum_wtA_le_tot (w : WeightFamilies.Wt D j) (b : D.host.E →+* ℂ) (m : ℕ) :
    ∑ i : Fin m, wtA w (b, i) ≤ tot w b := by
  unfold wtA tot
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun t _ => ?_
  rw [Finset.sum_add_distrib]
  refine add_le_add ?_ ?_
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp
  · dsimp only
    split_ifs
    · exact sum_extendByZero_le_sum _ _
    · simp

theorem sum_tot (w : WeightFamilies.Wt D j) :
    ∑ b, tot w b = ∑ t, ((∑ i, w.aP t i) + ∑ i, w.aM t i) := by
  classical
  unfold tot
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

theorem tot_le_size (w : WeightFamilies.Wt D j) :
    ((∑ b, tot w b : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  rw [sum_tot]
  unfold WeightFamilies.Wt.size
  push_cast
  have h1 : (1 : ℝ) ≤ max ((D.R.sigW j).2 : ℝ) 1 := le_max_right _ _
  have h2 : (0 : ℝ) ≤ (D.R.f : ℝ) * D.R.r * w.n := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 h2]

theorem spread_le {r : ℕ} (hr : 0 < r) (x : Fin r → ℝ) (A B : ℝ) (h1 : ∀ i, x i ≤ A) (h2 : ∀ i, -B ≤ x i) :
    (⨆ i, x i) - ⨅ i, x i ≤ A + B := by
  haveI : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have := ciSup_le h1
  have := le_ciInf h2
  linarith

theorem invFun_relab (T : Core D) (τ : D.host.E →+* ℂ) : Function.invFun (relab T.Q.c T.σ₀) τ = τ := by
  have h : ∀ τ : D.host.E →+* ℂ, relab T.Q.c T.σ₀ τ = τ := fun τ => RingHom.ext fun _ => rfl
  have h2 : relab T.Q.c T.σ₀ (Function.invFun (relab T.Q.c T.σ₀) τ) = τ := Function.invFun_eq ⟨τ, h τ⟩
  rwa [h] at h2

theorem spread_laU_le (T : Core D) (hr : 0 < D.R.r) (w : WeightFamilies.Wt D j) (k : (T.U j T.σ₀).Comp)
    (τ : ((T.U j T.σ₀).X k).Ψ) :
    ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ ≤
      (tot w τ.1 : ℝ) + tot w (conjEmb τ.1) + w.n := by
  have hn : ((w.n / 2 : ℕ) : ℝ) + ((w.n / 2 : ℕ) : ℝ) ≤ w.n := by
    have : w.n / 2 + w.n / 2 ≤ w.n := by omega
    exact_mod_cast this
  have key : ∀ i, -((tot w (conjEmb τ.1) : ℤ) + ((w.n / 2 : ℕ) : ℤ)) ≤ laU (T.U j T.σ₀) (wtA w) w.n k τ i ∧
      laU (T.U j T.σ₀) (wtA w) w.n k τ i ≤ (tot w τ.1 : ℤ) + ((w.n / 2 : ℕ) : ℤ) := by
    intro i
    unfold laU
    rw [invFun_relab, invFun_relab]
    have a1 := wtA_le_tot w τ.1 ((i : ℕ) - ((T.U j T.σ₀).X k).p0)
    have a2 := wtA_le_tot w (conjEmb τ.1) (((T.U j T.σ₀).X k).p0 - 1 - (i : ℕ))
    split_ifs <;> constructor <;> omega
  refine (spread_le hr _ ((tot w τ.1 : ℝ) + ((w.n / 2 : ℕ) : ℝ))
    ((tot w (conjEmb τ.1) : ℝ) + ((w.n / 2 : ℕ) : ℝ)) (fun i => ?_) (fun i => ?_)).trans (by linarith)
  · have h1 := (Int.cast_le (R := ℝ)).2 (key i).2
    rwa [Int.cast_add, Int.cast_natCast, Int.cast_natCast] at h1
  · exact_mod_cast (key i).1

theorem sum_cm_le {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (B : (E →+* ℂ) → ℕ) : ∑ τ : X.Ψ, (B τ.1 + B (conjEmb τ.1)) ≤ ∑ b, B b := by
  classical
  have hcc : ∀ τ : E →+* ℂ, conjEmb (conjEmb τ) = τ := fun τ => RingHom.ext fun x => by simp [conjEmb]
  have hinj : Function.Injective (conjEmb : (E →+* ℂ) → (E →+* ℂ)) := Function.LeftInverse.injective hcc
  rw [Finset.sum_add_distrib, Finset.sum_coe_sort X.Ψ B, Finset.sum_coe_sort X.Ψ (fun τ => B (conjEmb τ)),
    ← Finset.sum_image (f := B) (g := conjEmb) (s := X.Ψ) hinj.injOn, ← Finset.sum_add_sum_compl X.Ψ B]
  refine Nat.add_le_add_left (Finset.sum_le_sum_of_subset fun b hb => ?_) _
  obtain ⟨τ, hτ, rfl⟩ := Finset.mem_image.1 hb
  rw [Finset.mem_compl]
  exact (X.cmType τ).1 hτ

theorem fdeg_eq (D : D7) : fdeg D.host.E = D.R.f := by
  unfold fdeg
  rw [hostSize_finrank]
  omega

theorem one_le_dE (D : D7) : 1 ≤ dE D.host.E := by
  unfold dE
  have h : (1 : ℤ) ≤ |NumberField.discr D.host.E| := Int.one_le_abs (NumberField.discr_ne_zero _)
  exact_mod_cast h

theorem sqrt_le_dE (D : D7) : Real.sqrt D.host.d ≤ dE D.host.E := by
  have h1 : Real.sqrt ((D.host.q : ℝ) * D.host.d) ≤ D.host.rdE :=
    (UpperTheory.KR.log_qd_le_rd D.host.toHostAx D.host.flPS).2.2.1
  have hq : (1 : ℝ) ≤ D.host.q := by exact_mod_cast D.host.hyp.1.one_lt.le
  have h2 : Real.sqrt D.host.d ≤ Real.sqrt ((D.host.q : ℝ) * D.host.d) :=
    Real.sqrt_le_sqrt (le_mul_of_one_le_left (Nat.cast_nonneg _) hq)
  have h4 : D.host.rdE ≤ dE D.host.E := by
    have h5 : (1 : ℝ) ≤ (Module.finrank ℚ D.host.E : ℝ) := by
      have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
      exact_mod_cast this
    exact Real.rpow_le_self_of_one_le (one_le_dE D) ((div_le_one (by linarith)).2 h5)
  linarith

theorem sizes : ∀ (D : D7) (T : Core D) (h : LawsCore T) (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, 0 < D.R.r ∧ (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r ∧ fdeg D.host.E = D.R.f ∧ Real.sqrt D.host.d ≤ dE D.host.E ∧ 1 ≤ dE D.host.E ∧ Real.log (dE D.host.E) = logdE D ∧ (∀ k, (∑ τ, ((T.U j T.σ₀).X k).spread (laU (T.U j T.σ₀) (wtA w) w.n k) τ) ≤ w.size) ∧ ((∑ b : D.host.E →+* ℂ, ∑ i : Fin ((T.Q.Dw j).mult b), wtA w (b, i) : ℕ) : ℝ) + ((D.R.f * D.R.r : ℕ) : ℝ) * w.n ≤ w.size := by
  intro D T h j hj w
  have hr : 0 < D.R.r := by
    have := D.R.m_add_three_le_k
    unfold Ranks.r
    omega
  have hts := tot_le_size w
  refine ⟨hr, (h.unf j hj T.σ₀ T.good_σ₀).1.symm, fdeg_eq D, sqrt_le_dE D, one_le_dE D, rfl, fun k => ?_, ?_⟩
  · refine (Finset.sum_le_sum fun τ _ => spread_laU_le T hr w k τ).trans (le_trans ?_ hts)
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact_mod_cast sum_cm_le ((T.U j T.σ₀).X k) (tot w)
    · rw [Finset.sum_const, Finset.card_univ, QuadraticCoefficientForms.card_Psi (X := (T.U j T.σ₀).X k), fdeg_eq, nsmul_eq_mul]
      refine mul_le_mul_of_nonneg_right ?_ (Nat.cast_nonneg _)
      exact_mod_cast Nat.le_mul_of_pos_right _ hr
  · refine le_trans (add_le_add ?_ le_rfl) hts
    exact_mod_cast Finset.sum_le_sum fun b _ => sum_wtA_le_tot w b _

end GlobalTheory.WtSizes
