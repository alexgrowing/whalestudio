import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedOfIsAnalyticSubset
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LogResolutionProjectiveLine

namespace GlobalTheory

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology

noncomputable section

namespace AnDim

variable {d : ℕ} {X : Type} [TopologicalSpace X]

def singularLocus (A : FinHolAtlas d X) (T : Set X) : Set X :=
  T \ ⋃ n, regularLocus A T n

def analyticDim (A : FinHolAtlas d X) (T : Set X) : WithBot ℕ∞ :=
  ⨆ (n : ℕ) (_ : (regularLocus A T n).Nonempty), (n : WithBot ℕ∞)

end AnDim

namespace Published

open AnDim

def AnalyticSetDimension : Prop :=
  ∀ (d : ℕ) (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas d X),
    (∀ T : Set X, A.IsAnalyticSubset T →
      A.IsAnalyticSubset (singularLocus A T) ∧
        (T.Nonempty → analyticDim A (singularLocus A T) < analyticDim A T)) ∧
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      analyticDim A Z = n) ∧
    (∀ C S : Set X, IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      analyticDim A (C ∩ S) < analyticDim A C) ∧
    (∀ T : Set X, A.IsAnalyticSubset T →
      {C | IsIrreducibleComponent A T C}.Finite ∧ T = ⋃₀ {C | IsIrreducibleComponent A T C})

end Published

namespace AnDim

variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem le_analyticDim {A : FinHolAtlas d X} {T : Set X} {n : ℕ}
    (h : (regularLocus A T n).Nonempty) : (n : WithBot ℕ∞) ≤ analyticDim A T :=
  le_iSup₂ (f := fun (n : ℕ) (_ : (regularLocus A T n).Nonempty) => (n : WithBot ℕ∞)) n h

theorem le_analyticDim_iff {A : FinHolAtlas d X} {T : Set X} {k : ℕ} :
    (k : WithBot ℕ∞) ≤ analyticDim A T ↔ ∃ n, k ≤ n ∧ (regularLocus A T n).Nonempty := by
  refine ⟨fun h => ?_, fun ⟨n, hk, hn⟩ => le_trans (by exact_mod_cast hk) (le_analyticDim hn)⟩
  by_contra hcon
  push_neg at hcon
  have hlt : ∀ n, (regularLocus A T n).Nonempty → n < k := fun n hn =>
    lt_of_not_ge fun hk => hn.ne_empty (hcon n hk)
  cases k with
  | zero =>
    have : analyticDim A T ≤ ⊥ := iSup₂_le fun n hn => absurd (hlt n hn) (Nat.not_lt_zero n)
    exact absurd (h.trans this) (by simp)
  | succ k =>
    have : analyticDim A T ≤ (k : WithBot ℕ∞) :=
      iSup₂_le fun n hn => by exact_mod_cast Nat.lt_succ_iff.1 (hlt n hn)
    have h2 : k + 1 ≤ k := by exact_mod_cast h.trans this
    omega

theorem analyticDim_le (A : FinHolAtlas d X) (T : Set X) : analyticDim A T ≤ (d : WithBot ℕ∞) :=
  iSup₂_le fun n ⟨_, _, _, hψ, _⟩ => by exact_mod_cast hψ.1

theorem analyticDim_empty (A : FinHolAtlas d X) : analyticDim A ∅ = ⊥ :=
  le_bot_iff.1 (iSup₂_le fun _ ⟨_, hx⟩ => absurd hx.1 (Set.notMem_empty _))

theorem analyticDim_univ [Nonempty X] (A : FinHolAtlas d X) : analyticDim A Set.univ = d :=
  le_antisymm (analyticDim_le A _)
    (le_analyticDim (by rw [regularLocus_univ]; exact Set.univ_nonempty))

theorem singularLocus_univ (A : FinHolAtlas d X) : singularLocus A Set.univ = ∅ :=
  Set.diff_eq_empty.2 fun x _ => Set.mem_iUnion.2 ⟨d, by rw [regularLocus_univ]; trivial⟩

theorem injective_fderiv_of_comp {a b c : ℕ} {F : (Fin a → ℂ) → Fin b → ℂ}
    {G : (Fin b → ℂ) → Fin c → ℂ} {H : (Fin a → ℂ) → Fin c → ℂ} {z : Fin a → ℂ}
    (hF : DifferentiableAt ℂ F z) (hG : DifferentiableAt ℂ G (F z)) (h : G ∘ F =ᶠ[𝓝 z] H)
    (hH : Function.Injective (fderiv ℂ H z)) : Function.Injective (fderiv ℂ F z) := by
  rw [← h.fderiv_eq, fderiv_comp z hG hF] at hH
  exact Function.Injective.of_comp (f := fderiv ℂ G (F z)) hH

def padL (k d : ℕ) : (Fin k → ℂ) →L[ℂ] (Fin d → ℂ) :=
  ContinuousLinearMap.pi fun i => if h : (i : ℕ) < k then ContinuousLinearMap.proj ⟨i, h⟩ else 0

theorem padL_apply_of_le {k d : ℕ} (z : Fin k → ℂ) {i : Fin d} (h : k ≤ (i : ℕ)) :
    padL k d z i = 0 := by
  simp [padL, not_lt.2 h]

theorem padL_injective {k d : ℕ} (h : k ≤ d) : Function.Injective (padL k d) := by
  intro z w hzw
  funext i
  simpa [padL] using congrFun hzw (Fin.castLE h i)

theorem hasHoloImm_of_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ} (hk : k ≤ n)
    (h : (regularLocus A T n).Nonempty) : HasHoloImm A T k := by
  obtain ⟨x, hxT, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := h
  obtain ⟨j, hj⟩ := A.cover x
  have hp : ∀ i : Fin d, n ≤ (i : ℕ) → ψ x i = 0 := (hT.le ⟨hxT, hx⟩).2
  set a : (Fin k → ℂ) → Fin d → ℂ := fun z => ψ x + padL k d z with ha
  have han : ∀ z, AnalyticAt ℂ a z := fun z => analyticAt_const.add ((padL k d).analyticAt z)
  have hac : Continuous a := continuous_const.add (padL k d).continuous
  have hV : IsOpen (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source) :=
    ψ.symm.isOpen_inter_preimage (A.chart j).open_source
  have hF : ∀ z ∈ a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source),
      AnalyticAt ℂ (A.chart j ∘ ψ.symm ∘ a) z := fun z hz =>
    ((hψ j).2 (a z) hz).comp (han z)
  refine ⟨a ⁻¹' (ψ.target ∩ ψ.symm ⁻¹' (A.chart j).source), ψ.symm ∘ a, j, hV.preimage hac,
    ⟨0, ?_⟩, fun z hz => ⟨?_, hz.2⟩, hF, fun z hz => ?_⟩
  · simp [ha, ψ.map_source hx, ψ.left_inv hx, hj]
  · refine (hT.ge ⟨ψ.map_target hz.1, fun i hi => ?_⟩).1
    rw [ψ.right_inv hz.1]
    simp [ha, hp i hi, padL_apply_of_le z (hk.trans hi)]
  · refine injective_fderiv_of_comp (G := ψ ∘ (A.chart j).symm) (H := a) (hF z hz).differentiableAt
      ((hψ j).1 _ ⟨(A.chart j).map_source hz.2, ?_⟩).differentiableAt ?_ ?_
    · simpa [(A.chart j).left_inv hz.2] using ψ.map_target hz.1
    · filter_upwards [(hV.preimage hac).mem_nhds hz] with w hw
      simp [(A.chart j).left_inv hw.2, ψ.right_inv hw.1]
    · have : fderiv ℂ a z = padL k d := ((padL k d).hasFDerivAt.const_add (ψ x)).fderiv
      rw [this]
      exact padL_injective (hk.trans hnd)

theorem le_of_mem_regularLocus {A : FinHolAtlas d X} {T : Set X} {n k : ℕ}
    {U : Set (Fin k → ℂ)} {g : (Fin k → ℂ) → X} {j : Fin A.n} (hU : IsOpen U)
    (hmaps : Set.MapsTo g U (T ∩ (A.chart j).source)) (han : AnalyticOnNhd ℂ (A.chart j ∘ g) U)
    {z : Fin k → ℂ} (hz : z ∈ U) (hinj : Function.Injective (fderiv ℂ (A.chart j ∘ g) z))
    (hreg : g z ∈ regularLocus A T n) : k ≤ n := by
  obtain ⟨-, ψ, ⟨hnd, hψ, hT⟩, hx⟩ := hreg
  have hj := (hmaps hz).2
  have hV : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source) :=
    (A.chart j).symm.isOpen_inter_preimage ψ.open_source
  have hzV : (A.chart j ∘ g) z ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' ψ.source :=
    ⟨(A.chart j).map_source hj, by simpa [(A.chart j).left_inv hj] using hx⟩
  have hev : ∀ᶠ w in 𝓝 z, w ∈ U ∧ g w ∈ ψ.source := by
    filter_upwards [hU.mem_nhds hz, (han z hz).continuousAt.preimage_mem_nhds (hV.mem_nhds hzV)]
      with w hw hw'
    exact ⟨hw, by simpa [(A.chart j).left_inv (hmaps hw).2] using hw'.2⟩
  have hH : AnalyticAt ℂ (ψ ∘ g) z := by
    refine (((hψ j).1 _ hzV).comp (han z hz)).congr ?_
    filter_upwards [hev] with w hw
    simp [(A.chart j).left_inv (hmaps hw.1).2]
  have hHinj : Function.Injective (fderiv ℂ (ψ ∘ g) z) := by
    refine injective_fderiv_of_comp (G := A.chart j ∘ ψ.symm) hH.differentiableAt
      ((hψ j).2 _ ⟨ψ.map_source hx, by simpa [ψ.left_inv hx] using hj⟩).differentiableAt ?_ hinj
    filter_upwards [hev] with w hw
    simp [ψ.left_inv hw.2]
  have hzero : ∀ (v : Fin k → ℂ) (i : Fin d), n ≤ (i : ℕ) → fderiv ℂ (ψ ∘ g) z v i = 0 := by
    intro v i hi
    have h1 : (fun w => (ψ ∘ g) w i) =ᶠ[𝓝 z] fun _ => 0 := by
      filter_upwards [hev] with w hw
      exact (hT.le ⟨(hmaps hw.1).1, hw.2⟩).2 i hi
    have h2 := h1.fderiv_eq (𝕜 := ℂ)
    rw [fderiv_pi (differentiableAt_pi.1 hH.differentiableAt)]
    simp only [ContinuousLinearMap.pi_apply]
    rw [h2]
    simp
  let M : (Fin k → ℂ) →ₗ[ℂ] (Fin n → ℂ) :=
    (LinearMap.funLeft ℂ ℂ (Fin.castLE hnd)).comp (fderiv ℂ (ψ ∘ g) z).toLinearMap
  have hM : Function.Injective M := by
    intro v w hvw
    refine hHinj (funext fun i => ?_)
    by_cases hi : (i : ℕ) < n
    · exact congrFun hvw ⟨i, hi⟩
    · rw [hzero v i (not_lt.1 hi), hzero w i (not_lt.1 hi)]
  simpa using LinearMap.finrank_le_finrank_of_injective hM

theorem hasHoloImm_iff (h : Published.AnalyticSetDimension) [CompactSpace X] [T2Space X]
    {A : FinHolAtlas d X} {T : Set X} (hT : A.IsAnalyticSubset T) {k : ℕ} :
    HasHoloImm A T k ↔ (k : WithBot ℕ∞) ≤ analyticDim A T := by
  refine ⟨fun hk => ?_, fun hk => ?_⟩
  · induction hm : analyticDim A T using WellFoundedLT.induction generalizing T with
    | ind m ih =>
      subst hm
      obtain ⟨U, g, j, hU, hne, hmaps, han, hinj⟩ := hk
      by_cases hreg : ∃ z ∈ U, ∃ n, g z ∈ regularLocus A T n
      · obtain ⟨z, hz, n, hn⟩ := hreg
        exact le_analyticDim_iff.2
          ⟨n, le_of_mem_regularLocus hU hmaps han hz (hinj z hz) hn, _, hn⟩
      · push_neg at hreg
        obtain ⟨hs, hlt⟩ := (h d X A).1 T hT
        obtain ⟨z, hz⟩ := hne
        have hlt' := hlt ⟨g z, (hmaps hz).1⟩
        refine (ih _ hlt' hs ⟨U, g, j, hU, ⟨z, hz⟩, fun w hw => ⟨⟨(hmaps hw).1, ?_⟩, (hmaps hw).2⟩,
          han, hinj⟩ rfl).trans hlt'.le
        simpa using hreg w hw
  · obtain ⟨n, hkn, hn⟩ := le_analyticDim_iff.1 hk
    exact hasHoloImm_of_regularLocus hkn hn

theorem immersedPieces (h : Published.AnalyticSetDimension) (d : ℕ) (X : Type) [TopologicalSpace X]
    [CompactSpace X] [T2Space X] (A : FinHolAtlas d X) :
    (∀ (Z : Set X) (n : ℕ), IsIrreducibleAnalytic A Z → (regularLocus A Z n).Nonempty →
      ¬ HasHoloImm A Z (n + 1)) ∧
    (∀ (C S : Set X) (k : ℕ), IsIrreducibleAnalytic A C → A.IsAnalyticSubset S → ¬ C ⊆ S →
      HasHoloImm A (C ∩ S) k → HasHoloImm A C (k + 1)) ∧
    (∀ S : Set X, A.IsAnalyticSubset S →
      {C | IsIrreducibleComponent A S C}.Finite ∧ S = ⋃₀ {C | IsIrreducibleComponent A S C}) := by
  obtain ⟨-, h2, h3, h4⟩ := h d X A
  refine ⟨fun Z n hZ hn hc => ?_, fun C S k hC hS hCS hk => ?_, h4⟩
  · have h5 := (hasHoloImm_iff h hZ.1).1 hc
    rw [h2 Z n hZ hn] at h5
    have : n + 1 ≤ n := by exact_mod_cast h5
    omega
  · have h5 := ((hasHoloImm_iff h (isAnalyticSubset_inter hC.1 hS)).1 hk).trans_lt (h3 C S hC hS hCS)
    obtain ⟨n, hn, hlt⟩ : ∃ n : ℕ, (regularLocus A C n).Nonempty ∧ (k : WithBot ℕ∞) < n := by
      obtain ⟨n, hn⟩ := lt_iSup_iff.1 h5
      obtain ⟨hn', hn⟩ := lt_iSup_iff.1 hn
      exact ⟨n, hn', hn⟩
    exact hasHoloImm_of_regularLocus (by exact_mod_cast hlt) hn

theorem analyticDim_singleton_le (A : FinHolAtlas d X) (x : X) : analyticDim A {x} ≤ 0 := by
  refine iSup₂_le fun n hn => ?_
  obtain ⟨U, g, j, hU, ⟨z, hz⟩, hmaps, -, hinj⟩ := hasHoloImm_of_regularLocus le_rfl hn
  have h1 : (A.chart j ∘ g) =ᶠ[𝓝 z] fun _ => A.chart j x := by
    filter_upwards [hU.mem_nhds hz] with w hw
    rw [Function.comp_apply, (hmaps hw).1]
  have h2 := hinj z hz
  rw [h1.fderiv_eq, fderiv_fun_const] at h2
  cases n with
  | zero => simp
  | succ n =>
    have := congrFun (h2 (a₁ := 0) (a₂ := 1) rfl) 0
    simp at this

theorem point_dimension_lt_projective_line (x : OnePoint ℂ) :
    analyticDim p1 (Set.univ ∩ {x}) < analyticDim p1 Set.univ := by
  rw [Set.univ_inter, analyticDim_univ]
  exact (analyticDim_singleton_le p1 x).trans_lt (by exact_mod_cast Nat.zero_lt_one)

theorem projective_line_dimension : IsIrreducibleAnalytic p1 Set.univ ∧ analyticDim p1 Set.univ = 1 ∧
    analyticDim p1 (singularLocus p1 Set.univ) < analyticDim p1 Set.univ := by
  refine ⟨AnLogRes.isIrreducibleAnalytic_univ p1, by simpa using analyticDim_univ p1, ?_⟩
  rw [singularLocus_univ, analyticDim_empty, analyticDim_univ]
  exact WithBot.bot_lt_coe _

end AnDim

end

end GlobalTheory
