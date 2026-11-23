import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.PowerSeriesHasSumAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstHasSumAndBoundsStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosureStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConvergentSubstOneVariableAndFormalAgreementStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstIsRingHomOnBoundedStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesConvergentSubstAssocStatement

open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer

theorem ev_algebra : ∀ (K : Type) [NormedField K] [IsUltrametricDist K] [CompleteSpace K] (σ : Type) [Fintype σ] (x : σ → K), (∀ i, ‖x i‖ < 1) → (∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x)) ∧ (∀ S T : MvPowerSeries σ K, Bdd S → Bdd T → ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧ ev (S * T) x = ev S x * ev T x) ∧ (∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a) ∧ (∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i) ∧ (∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1)) ∧ (∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x)) ∧ (∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K), (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S → ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x)) ∧ (∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a → MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x)) := by
  intro K _ _ _ σ _ x hx
  have Cinj : ∀ a b : K, (MvPowerSeries.C a : MvPowerSeries Unit K) = MvPowerSeries.C b → a = b := by
    intro a b h
    simpa using congrArg MvPowerSeries.constantCoeff h
  have E : ∀ (ρ : Type) [Fintype ρ] (S : MvPowerSeries ρ K) (y : ρ → K),
      csub (fun i => (MvPowerSeries.C (y i) : MvPowerSeries Unit K)) S = MvPowerSeries.C (ev S y) := by
    intro ρ _ S y
    exact (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.1 ρ Unit S y
  obtain ⟨c, hc⟩ : ∃ c : σ → MvPowerSeries Unit K, c = fun i => MvPowerSeries.C (x i) := ⟨_, rfl⟩
  have E' : ∀ S : MvPowerSeries σ K, csub c S = MvPowerSeries.C (ev S x) := by
    intro S
    subst hc
    exact E σ S x
  have B := GlobalTheory.T.mvPowerSeries_integral_bounded_closure K σ
  have hcs : ∀ i, Small (c i) := by
    intro i
    subst hc
    exact ((GlobalTheory.T.mvPowerSeries_integral_bounded_closure K Unit).2.2.2.1 (x i)).2.2 (hx i)
  have R := GlobalTheory.T.mvPowerSeriesConvergentSubst_isRingHom_on_bounded K σ Unit c hcs

  have p1 : ∀ S : MvPowerSeries σ K, Bdd S → HS S x (ev S x) := by
    intro S hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hS).1 0
    rw [E' S] at h
    have hm : ∀ ν : σ →₀ ℕ, MvPowerSeries.coeff 0 (∏ i, c i ^ ν i) = ∏ i, x i ^ ν i := by
      intro ν
      subst hc
      simp [map_prod, map_pow]
    simp only [hm] at h
    unfold HS
    simpa using h
  have p2 : ∀ S T : MvPowerSeries σ K, Bdd S → Bdd T →
      ev (S + T) x = ev S x + ev T x ∧ ev (S - T) x = ev S x - ev T x ∧
        ev (S * T) x = ev S x * ev T x := by
    intro S T hS hT
    obtain ⟨h1, h2, h3⟩ := R.1 S T hS hT
    simp only [E'] at h1 h2 h3
    exact ⟨by simpa using congrArg MvPowerSeries.constantCoeff h1,
      by simpa using congrArg MvPowerSeries.constantCoeff h2,
      by simpa using congrArg MvPowerSeries.constantCoeff h3⟩
  have p3 : ∀ a : K, ev (MvPowerSeries.C a : MvPowerSeries σ K) x = a := by
    intro a
    have h := R.2.1 a
    rw [E'] at h
    exact Cinj _ _ h
  have p4 : ∀ i, ev (MvPowerSeries.X i : MvPowerSeries σ K) x = x i := by
    intro i
    have h := R.2.2.1 i
    rw [E'] at h
    exact Cinj _ _ (h.trans (by rw [hc]))
  have p5 : ∀ S : MvPowerSeries σ K, Intg S → ‖ev S x‖ ≤ 1 ∧ (Small S → ‖ev S x‖ < 1) := by
    intro S hS
    have hSB : Bdd S := (B.2.2.1 S 0).2.2 hS
    have hI := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c S hcs hSB).2.2.1 hS
    rw [E'] at hI
    refine ⟨by simpa using hI 0, fun hSm => ?_⟩

    set c0 := MvPowerSeries.constantCoeff S with hc0d
    have hc0 : ‖c0‖ ≤ 1 := by simpa [hc0d] using hS 0
    have hCI : Intg (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).2.1 hc0
    have hCB : Bdd (MvPowerSeries.C c0 : MvPowerSeries σ K) := (B.2.2.2.1 c0).1
    have hT : Intg (S - MvPowerSeries.C c0) := (B.1 S _ hS hCI).2.1
    have hT0 : MvPowerSeries.constantCoeff (S - MvPowerSeries.C c0) = 0 := by simp [hc0d]
    have hTB : Bdd (S - MvPowerSeries.C c0) := (B.2.2.1 _ 0).2.2 hT
    have hsm := (GlobalTheory.T.mvPowerSeriesConvergentSubst_hasSum_and_bounds K σ Unit c _ hcs hTB).2.2.2 hT hT0
    rw [E'] at hsm
    have hlt : ‖ev (S - MvPowerSeries.C c0) x‖ < 1 := by simpa using hsm.2
    have hadd : ev S x = ev (S - MvPowerSeries.C c0) x + c0 := by
      have h := (p2 (S - MvPowerSeries.C c0) _ hTB hCB).1
      rw [sub_add_cancel, p3] at h
      exact h
    have hlt0 : ‖c0‖ < 1 := hSm.2
    calc ‖ev S x‖ = ‖ev (S - MvPowerSeries.C c0) x + c0‖ := by rw [← hadd]
      _ ≤ max ‖ev (S - MvPowerSeries.C c0) x‖ ‖c0‖ := IsUltrametricDist.norm_add_le_max _ _
      _ < 1 := max_lt hlt hlt0
  have p6 : ∀ (ρ : Type) [Fintype ρ] (s : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Small (s j)) → Bdd S → ev (csub s S) x = ev S (fun j => ev (s j) x) := by
    intro ρ _ s S hs hS
    have h := (GlobalTheory.T.mvPowerSeriesConvergentSubst_assoc K ρ σ Unit s c S hs hcs hS).2
    have hf : (fun j => csub c (s j)) = fun j => (MvPowerSeries.C (ev (s j) x) : MvPowerSeries Unit K) :=
      funext fun j => E' (s j)
    rw [hf, E'] at h
    exact Cinj _ _ (h.trans (E ρ S (fun j => ev (s j) x)))
  have small0 : ∀ a : MvPowerSeries σ K, Intg a → MvPowerSeries.constantCoeff a = 0 → Small a := by
    intro a ha ha0
    show Intg a ∧ ‖MvPowerSeries.constantCoeff a‖ < 1
    exact ⟨ha, by rw [ha0]; simp⟩
  have p7 : ∀ (ρ : Type) [Fintype ρ] (a : ρ → MvPowerSeries σ K) (S : MvPowerSeries ρ K),
      (∀ j, Intg (a j)) → (∀ j, MvPowerSeries.constantCoeff (a j) = 0) → Bdd S →
        ev (MvPowerSeries.subst a S) x = ev S (fun j => ev (a j) x) := by
    intro ρ _ a S ha ha0 hS
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.1 ρ σ a S ha0]
    exact p6 ρ a S (fun j => small0 _ (ha j) (ha0 j)) hS
  have p8 : ∀ (a : MvPowerSeries σ K) (f : PowerSeries K), Intg a →
      MvPowerSeries.constantCoeff a = 0 → Bdd f → ev (f.subst a) x = ev1 f (ev a x) := by
    intro a f ha ha0 hf
    rw [← (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.2.2.2.2.2 σ a f ha0, (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).1 σ a f,
      (GlobalTheory.T.convergentSubst_oneVariable_and_formal_agreement K).2.1 f (ev a x)]
    exact p6 Unit (fun _ => a) f (fun _ => small0 a ha ha0) hf
  exact ⟨p1, p2, p3, p4, p5, p6, p7, p8⟩

end GlobalTheory.ConvSer
