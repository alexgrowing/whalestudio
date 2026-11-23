import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankPosOfLeaves

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace GlobalTheory.CompanionTheory.EGlue

section LimLists

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem limL_allLeaves_strip (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) :
    ∀ {N : ℕ} (t : Tr E N), t.strip.AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_shift (P : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop) (z : ℂ) :
    ∀ {N : ℕ} (t : Tr E N), (t.shift z).AllLeaves P ↔ t.AllLeaves P := by
  intro N t
  induction t with
  | leaf V z' => exact Iff.rfl
  | node t₁ t₂ i₁ i₂ => exact and_congr i₁ i₂

theorem limL_allLeaves_mono {P Q : ∀ M : ℕ, Submodule ℂ (Sm E M) → Prop} (h : ∀ M V, P M V → Q M V) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves P → t.AllLeaves Q := by
  intro N t
  induction t with
  | leaf V z => exact h _ _
  | node t₁ t₂ i₁ i₂ => exact fun a => ⟨i₁ a.1, i₂ a.2⟩

theorem limL_disc_shift (z : ℂ) : ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Disc → (t.shift z).Disc := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr h
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

theorem limL_good_shift {z : ℂ} (hz : z.re = 0) :
    ∀ {N : ℕ} {t : Tr E N}, t.AllLeaves (fun M _ => 0 < M) → t.Good → (t.shift z).Good := by
  intro N t
  induction t with
  | leaf V z' =>
    intro hp h
    rcases h with h | h
    · exact absurd h.1 (Nat.ne_of_gt (show 0 < _ from hp))
    · exact Or.inr ⟨h.1, h.2.1, by simp [h.2.2, hz]⟩
  | node t₁ t₂ i₁ i₂ => exact fun hp h => ⟨i₁ hp.1 h.1, i₂ hp.2 h.2⟩

def LimDiscBody (E : Type) [Field E] [NumberField E] [IsCMField E] (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ))
    (K : Subgroup (GL (Fin M) (Af E))) (Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ)))
    (Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))) : Prop :=
  ∀ [MeasurableSpace (GA E M)] [BorelSpace (GA E M)] (μ : Measure (GA E M)) [μ.IsHaarMeasure] (R : ℝ), 0 < M →
  ReproAll E →
  ∀ V : ℕ → Submodule ℂ (Sm E M), (∀ k, IsDiscrete (V k)) → (∀ k, HasType K W (V k)) → (∀ k, InfBdd R (V k)) →
  ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (t₀ : Tr E M), StrictMono φ ∧ t₀.Good ∧ (∀ k, (t k).Disc) ∧
    (∀ k, (t k).strip = t₀.strip) ∧
    t₀.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧
    (∀ i, Tendsto (fun k => ((t k).twists.getD i 0)) atTop (𝓝 (t₀.twists.getD i 0))) ∧
    ∀ k, Emb (V (φ k)) (· ∈ (t k).space)

theorem limL_exists_haar (M : ℕ) : ∃ (_ : MeasurableSpace (GA E M)) (_ : BorelSpace (GA E M)) (μ : Measure (GA E M)),
    μ.IsHaarMeasure := by
  letI : MeasurableSpace (GA E M) := borel _
  haveI : BorelSpace (GA E M) := ⟨rfl⟩
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E M
  exact ⟨_, inferInstance, Measure.haar, inferInstance⟩

theorem limL_lim_one (hS : ConvStrip) (hSh : ConvShift) (hC : ConvComp) (hT : TwShift) {M : ℕ} (hM : 0 < M)
    {W : Submodule ℂ (Kinf E M → ℂ)} {K : Subgroup (GL (Fin M) (Af E))}
    {Ω : ∀ M : ℕ, Set (Submodule ℂ (Kinf E M → ℂ))} {Θ : ∀ M : ℕ, Set (Subgroup (GL (Fin M) (Af E)))}
    (hB : LimDiscBody E M W K Ω Θ) (V : ℕ → Submodule ℂ (Sm E M)) (z : ℕ → ℂ) (R : ℝ) (hR : ReproAll E)
    (hD : ∀ k, IsDiscrete (V k)) (hz : ∀ k, (z k).re = 0) (hTy : ∀ k, HasType K W (V k))
    (hI : ∀ k, InfBdd R (V k)) (hzR : ∀ k, ‖z k‖ ≤ R) :
    ∃ (φ : ℕ → ℕ) (t : ℕ → Tr E M) (s : Tr E M), StrictMono φ ∧ Conv t s ∧ Red s ∧ s.Good ∧
      s.AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) ∧ (∀ k, (t k).Disc) ∧
      ∀ k, Emb (tw (V (φ k)) (z (φ k))) (· ∈ (t k).space) := by
  obtain ⟨_, _, μ, _⟩ := limL_exists_haar (E := E) M
  obtain ⟨φ, tt, t₀, hφ, hG, hDt, hst, hL, htw, hE⟩ := hB μ R hM hR V hD hTy hI
  obtain ⟨z₀, hz₀, ψ, hψ, hlim⟩ := tendsto_subseq_of_bounded (x := fun k => z (φ k))
    (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := R)) (fun k => by simpa using hzR (φ k))
  have hre : z₀.re = 0 := by
    have h1 : Tendsto (fun k => (z (φ (ψ k))).re) atTop (𝓝 z₀.re) :=
      (Complex.continuous_re.tendsto z₀).comp hlim
    simp only [hz, ] at h1
    exact (tendsto_nhds_unique h1 tendsto_const_nhds)
  have hpos : t₀.AllLeaves (fun M _ => 0 < M) := limL_allLeaves_mono (fun _ _ h => h.1) hL
  have hposk : ∀ k, (tt k).AllLeaves (fun M _ => 0 < M) := fun k => by
    rw [← limL_allLeaves_strip, hst k, limL_allLeaves_strip]
    exact hpos
  have hconv : Conv tt t₀ := (hS E M tt t₀).2 ⟨hst, htw⟩
  have hconv' : Conv (fun k => (tt (ψ k)).shift (z (φ (ψ k)))) (t₀.shift z₀) :=
    hSh E M _ t₀ _ z₀ (hC E M tt t₀ ψ hconv hψ) hlim
  have hL' : (t₀.shift z₀).AllLeaves (fun M V => 0 < M ∧ ∃ K' ∈ Θ M, ∃ W' ∈ Ω M, HasType K' W' V) :=
    (limL_allLeaves_shift _ _ _).2 hL
  exact ⟨fun k => φ (ψ k), fun k => (tt (ψ k)).shift (z (φ (ψ k))), t₀.shift z₀, hφ.comp hψ, hconv',
    red_of_leaves hL', limL_good_shift hre hpos hG, hL', fun k => limL_disc_shift _ (hposk _) (hDt _),
    fun k => hT E M _ _ _ (hD _).stable (hE _)⟩

end LimLists

theorem limLists : ConvStrip → ConvShift → ConvComp → LimLists := by
  intro hS hSh hC h5 hT E _ _ _ N Ωs hΩs
  have h1 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)),
      ∃ Ω : ∀ M' : ℕ, Set (Submodule ℂ (Kinf E M' → ℂ)), KTypes E Ω ∧
        (FiniteDimensional ℂ W → ∀ K : Subgroup (GL (Fin M) (Af E)), IsOpen (K : Set (GL (Fin M) (Af E))) →
          ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧ LimDiscBody E M W K Ω Θ) := by
    intro M W
    by_cases hW : FiniteDimensional ℂ W
    · obtain ⟨Ω, hΩ, h⟩ := h5 E M W hW
      exact ⟨Ω, hΩ, fun _ K hK => h K hK⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun h => absurd h hW⟩
  choose Om hOm hOm' using h1
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, Om M W M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ => (hOm M W M').1, ?_⟩
    intro W' hW'
    simp only [Set.mem_iUnion] at hW'
    obtain ⟨M, _, W, _, h⟩ := hW'
    exact (hOm M W M').2 W' h
  intro Θs hΘs
  have h2 : ∀ (M : ℕ) (W : Submodule ℂ (Kinf E M → ℂ)) (K : Subgroup (GL (Fin M) (Af E))),
      ∃ Θ : ∀ M' : ℕ, Set (Subgroup (GL (Fin M') (Af E))), Levels E Θ ∧
        (FiniteDimensional ℂ W → IsOpen (K : Set (GL (Fin M) (Af E))) → LimDiscBody E M W K (Om M W) Θ) := by
    intro M W K
    by_cases h : FiniteDimensional ℂ W ∧ IsOpen (K : Set (GL (Fin M) (Af E)))
    · obtain ⟨Θ, hΘ, hb⟩ := hOm' M W h.1 K h.2
      exact ⟨Θ, hΘ, fun _ _ => hb⟩
    · exact ⟨fun _ => ∅, fun _ => ⟨Set.finite_empty, by simp⟩, fun a b => absurd ⟨a, b⟩ h⟩
  choose Th hTh hTh' using h2
  refine ⟨fun M' => ⋃ M ∈ Set.Icc 1 N, ⋃ W ∈ Ωs M, ⋃ K ∈ Θs M, Th M W K M', ?_, ?_⟩
  · intro M'
    refine ⟨(Set.finite_Icc 1 N).biUnion fun M _ => (hΩs M).1.biUnion fun W _ =>
      (hΘs M).1.biUnion fun K _ => (hTh M W K M').1, ?_⟩
    intro K' hK'
    simp only [Set.mem_iUnion] at hK'
    obtain ⟨M, _, W, _, K, _, h⟩ := hK'
    exact (hTh M W K M').2 K' h
  intro M hM hMN V z R hR hD hz hTy hI hzR
  choose Kk hKk Wk hWk hty using hTy
  have hfin : (Θs M ×ˢ Ωs M).Finite := (hΘs M).1.prod (hΩs M).1
  haveI := hfin.to_subtype
  obtain ⟨⟨⟨K, W⟩, hKW⟩, hinf⟩ := Finite.exists_infinite_fiber
    (fun k : ℕ => (⟨(Kk k, Wk k), hKk k, hWk k⟩ : ↥(Θs M ×ˢ Ωs M)))
  have hfr : ∃ᶠ k in atTop, Kk k = K ∧ Wk k = W := by
    refine Nat.frequently_atTop_iff_infinite.2 ((Set.infinite_coe_iff.1 hinf).mono ?_)
    intro k hk
    have h := congrArg Subtype.val (Set.mem_singleton_iff.1 (Set.mem_preimage.1 hk))
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  obtain ⟨a, ha, hak⟩ := extraction_of_frequently_atTop hfr
  have hK : K ∈ Θs M := hKW.1
  have hW : W ∈ Ωs M := hKW.2
  have hbody : LimDiscBody E M W K (Om M W) (Th M W K) := hTh' M W K ((hΩs M).2 W hW) ((hΘs M).2 K hK)
  have htyp : ∀ k, HasType K W (V (a k)) := fun k => by
    have h := hty (a k)
    rwa [(hak k).1, (hak k).2] at h
  obtain ⟨φ, t, s, hφ, hc, hr, hg, hl, hd, he⟩ := limL_lim_one hS hSh hC hT hM hbody (fun k => V (a k))
    (fun k => z (a k)) R hR (fun k => hD _) (fun k => hz _) htyp (fun k => hI _) (fun k => hzR _)
  refine ⟨fun k => a (φ k), t, s, ha.comp hφ, hc, hr, hg, limL_allLeaves_mono ?_ hl, hd, he⟩
  rintro M' V' ⟨-, K'', hK'', W'', hW'', h⟩
  refine Or.inr ⟨K'', ?_, W'', ?_, h⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, K, hK, hK''⟩
  · simp only [Set.mem_iUnion]
    exact ⟨M, ⟨hM, hMN⟩, W, hW, hW''⟩

end GlobalTheory.CompanionTheory.EGlue

end
