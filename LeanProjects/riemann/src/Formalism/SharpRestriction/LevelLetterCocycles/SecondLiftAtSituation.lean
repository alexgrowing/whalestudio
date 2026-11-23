import Formalism.SharpRestriction.LevelLetterCocycles.LevelMembershipPackage
import Formalism.SharpRestriction.LevelLetterCocycles.CoboundaryMemInvariantCocycles
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsLinearLiftOfFree
import Formalism.SharpRestriction.LevelLetterCocycles.FiltrationQuotientFiniteDimensional

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains TensorProduct Formalism.MainNotions.N.Pv.LocalLengthBound
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX InI)
open Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2I

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem second_lift_at_situation [NeZero n] (W : LocWach PD LL O v n) (hZ : TTool2Z W)
    (hF : Formalism.MainNotions.CrystallineLiftingInputs.FTool W) (hB : Sh.BasTool W) (hK : Sh.LemK W) (hD : Sh.FilDim W)
    (hR : Sh.ExpRing W) (hE : Sh.ExpRules W)
    (h2a : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → Formalism.MainNotions.DeltaInvariantLattices.p2aK W T)
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hEx : DcrisExactStrict PD LL)
    (hCs : CrysSubQuot PD LL) (hDq : DdREqDcris PD LL) {d : ℕ} {T₁ T₂ : LocLat G Qp LL O}
    {F : LatHom T₁.L T₂.L} {b : ZMod n → ℕ} {S η m : ℕ} (hS : SetCS W d T₁ T₂ F b S η m)
    [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O LL] (s₁ : ℕ) {FF : Type}
    [AddCommGroup FF] [Module O FF] [Module.Free O FF] [Module.Finite O FF]
    (g : FF →ₗ[O] ↥(latticeFiniteCocycles PD T₂.L)) (N : ℕ) (y z : FF →ₗ[O] W.DD T₂)
    (μ ν : ZMod n → FF →ₗ[O] W.DD T₂)
    (hX : Sh.ExtData W T₂ (MiW d b S η) (hiW d b S η) ⌈aR PD.p (hpar n b S + η)⌉₊ N g y z μ ν)
    (F₁ : Submodule O FF) (ms : ZMod n → FF →ₗ[O] W.DD T₂)
    (hO : Step1Out W T₂ d ⌈aR PD.p (hpar n b S + η)⌉₊ N s₁ z μ F₁ ms) :
    ∃ (F₂ : Submodule O FF) (w : ZMod n → ↥F₂ →ₗ[O] W.DD T₂),
      PChain (lenOl PD (O := O)) m (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S) F₁ F₂
        (evens n d).card 0 ∧
      (m = 0 → F₂ = F₁) ∧
      (∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (w c f)) ∧
      ∀ f : ↥F₂, ∃ κ : ZMod n → G → T₂.V,
        (∀ c ∈ evens n d, RhoCoc W T₂ c (Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S)) η
          (sigC PD.p (hpar n b S) η) (w c f) (κ c)) ∧
        (((PD.p : O) ^ (s₁ + 2 * sigC PD.p (hpar n b S) η)) • (g (f : FF) : G → T₂.V) -
            (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L ∨
          ((PD.p : O) ^ (s₁ + 2 * sigC PD.p (hpar n b S) η)) • (g (f : FF) : G → T₂.V) +
            (∑ c ∈ evens n d, κ c) ∈ latticeCoboundaries T₂.L) := by
  have hA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hp11 : 11 ≤ PD.p := hS.2.1
  have hn : Even n := hS.2.2.1
  obtain ⟨hc1, hc2, -⟩ := hS.2.2.2.2.2.1
  set M := Formalism.MainNotions.CrystallineLiftingInputs.Mpar PD.p (hpar n b S) with hMdef
  set σ := sigC PD.p (hpar n b S) η with hσdef
  have hM1 : 1 ≤ M := Nat.le_add_left _ _
  have hTC : Formalism.MainNotions.CrystallineLiftingInputs.TCase PD.p 1 M η σ := Or.inl ⟨rfl, hM1, rfl⟩
  have hηM : η ≤ (PD.p - 1) * M := by
    have hb0 : b 0 ≤ Finset.univ.sup b := Finset.le_sup (Finset.mem_univ 0)
    have := rk_eta_lt W hS 0
    exact Step2A.eta_le_parameter _ _ _ (by omega) (by unfold hpar; omega)

  have hfin : Module.finrank K₀ K = 1 := by
    rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) hA.1).toLinearEquiv.finrank_eq,
      Module.finrank_self]
  obtain ⟨hring, hmod⟩ := ((h9 T₂ hc2) hA.2.1 hA.2.2).2.2 hfin
  have hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀ := hring.1
  have hπ : W.π₀ ∈ W.AΔ := hring.1
  have hu0 : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1) := hring.2.2.1
  have hqpΔ : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ := qp_mem_AΔ W hring
  have hgam : W.gamK = W.gam := W.gamK_eq_one hA.2.1 hA.2.2

  obtain ⟨hJ2, hJ2U⟩ := Step2A.jumps_bounds_of_set W hEx hCs hDq hS
  have F2 := hF d T₁ T₂ F b S η m hS T₂ hc2 hJ2 hJ2U
  dsimp only at F2
  obtain ⟨F2c1, F2c2, F2c3, F2c4, F2c5⟩ := F2

  have Z2 := fun i => hZ hA hp11 1 M η σ hTC T₂ hc2 i

  have h5T := h5 T₂ (boxM d b S η) (boxH d b S η) hc2 (rk_jumpsLet₂ W hEx hCs hDq hS)
  have hev : ∀ c : ZMod n, c ∈ evens n d → (c.val + d) % 2 = 0 := fun c hc => mem_evens_iff.1 hc
  have hm2 : ∀ c : ZMod n, c ∈ evens n d → c - 2 ∈ evens n d := fun c hc => sub_two_mem_evens hn hc
  have h5D : ∀ c ∈ evens n d, ∀ x ∈ W.N T₂, DL W T₂ c x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ pullJ W T₂ (c - 1) 1 := by
    intro c hc x hx hd
    have := q_pow_smul_mem_pullback W T₂ hA.2.1 hring hmod _ _ h5T c hx hd
    rwa [show boxH d b S η c = η by simp [boxH, hev c hc]] at this
  have hpol : ∀ c ∈ evens n d, ∀ x ∈ W.N T₂, DL W T₂ (c - 1) x →
      Formalism.MainNotions.LiftingTheory.qp W ^ (b c + S) • W.φD T₂ x ∈ W.N T₂ := by
    intro c hc x hx hd
    obtain ⟨u, hu, -⟩ := qp_unit W hA.2.1 hring
    have := h5T.1 c x (mem_Nl W T₂ hx hd.1)
    rw [show boxM d b S η c = b c + S by simp [boxM, hev c hc]] at this
    rw [hu, mul_pow, mul_smul]
    exact (W.N T₂).smul_mem _ this
  have hMi : ∀ c ∈ evens n d, MiW d b S η c = b c + S := fun c hc => by simp [MiW, hev c hc]
  have hMiU : ∀ c ∈ evens n d, MiW d b S η (c + 1) = η := fun c hc => by
    simp only [MiW]; rw [if_neg (succ_not_mem_evens hn hc)]
  have hhi : ∀ c ∈ evens n d, hiW d b S η c = η := fun c hc => by simp [hiW, hev c hc]

  obtain ⟨hX1, hX2⟩ := hX
  have hyz : ∀ f : FF, W.γ T₂ (y f) - y f = W.φD T₂ (z f) - z f ∧
      ∀ δ ∈ W.DelF, W.γD T₂ δ (y f) = y f ∧ W.γD T₂ δ (z f) = z f := by
    intro f
    obtain ⟨x0, -, hx0, -⟩ := hX1 f
    have hm := (RL.mem_Z1DΔ_iff W T₂ _).1 x0.2
    rw [hx0] at hm
    refine ⟨?_, hm.2⟩
    have h1 := hm.1
    rw [hgam] at h1
    exact h1

  let ζL : ZMod n → FF →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ s₁ • (Step2A.letterIdempotentMap W T₂ c).comp z + (W.γ T₂ - LinearMap.id).comp (ms c)
  have hζL : ∀ c f, ζL c f = gammaDefectOfLetterLift W T₂ s₁ (z f) (fun c' => ms c' f) c := fun c f => rfl
  have hζ : ∀ c ∈ evens n d, ∀ f, DL W T₂ c (ζL c f) ∧ InPN W T₂ 1 (ζL c f) := by
    intro c hc f
    obtain ⟨hms, hPN, -⟩ := hO c hc f
    exact ⟨Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _
      (invariantLetter_idempotent_of_fixed W T₂ (fun δ hδ => ((hyz f).2 δ hδ).2))) (invariantLetter_sub' W T₂ (invariantLetter_gamma W T₂ hms) hms), hPN⟩
  have htex : ∀ c, ∃ tL : ↥F₁ →ₗ[O] W.DD T₂, c ∈ evens n d → ∀ f : ↥F₁,
      tL f ∈ pullJ W T₂ c 1 ∧ DL W T₂ (c + 1) (tL f) ∧
      (∃ p ∈ pullJ W T₂ c 1, ((PD.p : ℕ) : O) ^ σ • W.φD T₂ (ζL c f) - (W.γ T₂ (tL f) - tL f) =
        fMX W M η • p) ∧
      ∃ t', IsTrZ W T₂ c 1 M η σ (ζL c f) t' ∧ ∃ p ∈ pullJ W T₂ c 1, tL f - t' = fMX W M η • p := by
    intro c
    by_cases hc : c ∈ evens n d
    · obtain ⟨tL, htL⟩ := Step2T.exists_linear_lift_of_free W T₂ hZ hA hp11 hTC hc2 c F₁ (ζL c) (hζ c hc)
      exact ⟨tL, fun _ => htL⟩
    · exact ⟨0, fun h => (hc h).elim⟩
  choose tL htL using htex

  let mhL : ZMod n → ↥F₁ →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ σ • (W.φD T₂).comp ((ms c).comp F₁.subtype) +
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • (Step2A.letterIdempotentMap W T₂ (c + 1)).comp (y.comp F₁.subtype) - tL c
  have hmh : ∀ c (f : ↥F₁), mhL c f =
      liftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f) c := fun c f => rfl
  let uhL : ZMod n → ↥F₁ →ₗ[O] W.DD T₂ := fun c =>
    ((PD.p : ℕ) : O) ^ N • mhL c - ((PD.p : ℕ) : O) ^ (s₁ + σ) • (μ (c + 1)).comp F₁.subtype
  have huh : ∀ c (f : ↥F₁), uhL c f = ((PD.p : ℕ) : O) ^ N •
      liftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f) c -
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • μ (c + 1) f := fun c f => rfl
  have hu : ∀ c ∈ evens n d, ∀ f : ↥F₁, ((PD.p : ℕ) : O) ^ N • ms c f -
      ((PD.p : ℕ) : O) ^ s₁ • μ c f ∈ W.N T₂ ∧
      DL W T₂ c (((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f) := by
    intro c hc f
    obtain ⟨hms, -, -, -, hin⟩ := hO c hc f
    exact ⟨hin f.2, invariantLetter_sub' W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ hms)
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ (hX2 c f).1)⟩
  have hmhDL : ∀ c ∈ evens n d, ∀ f : ↥F₁,
      DL W T₂ (c + 1) (liftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f) c) := by
    intro c hc f
    obtain ⟨hms, -⟩ := hO c hc f
    exact invariantLetter_sub' W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ (invariantLetter_frobenius_succ W T₂ hms))
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ (invariantLetter_idempotent_of_fixed W T₂ (fun δ hδ => ((hyz f).2 δ hδ).1))))
      (htL c hc f).2.1

  have hxi : ∀ c ∈ evens n d, ∀ f : ↥F₁,
      (∃ p ∈ pullJ W T₂ c 1, gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f) c =
        fMX W M η • p) ∧
      InPN W T₂ M (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f) c) ∧
      DL W T₂ (c + 1) (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f) c) := by
    intro c hc f
    obtain ⟨-, ht2, ⟨p, hp, ep⟩, -⟩ := htL c hc f
    have hx := cocycleXi_eq (W := W) (T := T₂) (s₁ := s₁) (σ := σ) (fun c' => ms c' f)
      (fun c' => tL c' f) (hyz f).1 c
    rw [← hζL] at hx
    rw [ep] at hx
    have hΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ
        (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f) c) =
        gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f) c := by
      intro δ hδ
      rw [hx, ← ep]
      simp only [map_sub, map_smul, gammaD_frobenius_comm, gammaD_gamma_comm', ((hζ c hc f).1).2 δ hδ, ht2.2 δ hδ]
    refine ⟨⟨p, hp, hx⟩, frobeniusPoly_smul_mem_lattice W T₂ hu0 hΔπ c M η (fun x h1 h2 => F2c4 c x (hev c hc) h1 h2)
      hp hx hΔ, ⟨?_, hΔ⟩⟩
    rw [hx, smul_comm, RL.pullJ_letter W T₂ c hp]

  have hq : ∀ c ∈ evens n d, ∀ f, Formalism.MainNotions.LiftingTheory.qp W ^ η • uhL c f ∈ W.N T₂ := by
    intro c hc f
    obtain ⟨ht1, -, -⟩ := htL c hc f
    have e := Step2A.frobenius_lift_identity N s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f) (fun c' => μ c' f) c
    beta_reduce at e
    rw [huh, e]
    have h1 : Formalism.MainNotions.LiftingTheory.qp W ^ η • W.φD T₂ (((PD.p : ℕ) : O) ^ N • ms c f -
        ((PD.p : ℕ) : O) ^ s₁ • μ c f) ∈ W.N T₂ :=
      F2c4 c _ (hev c hc) (Submodule.subset_span ⟨_, (hu c hc f).1, rfl⟩)
        (letter_phi W T₂ (c + 1) (by rw [add_sub_cancel_right]; exact (hu c hc f).2.1))
    have h2 := (hX2 (c + 1) f).2.2.2.1
    rw [hMiU c hc, add_sub_cancel_right] at h2
    have h3 : Formalism.MainNotions.LiftingTheory.qp W ^ η • tL c f ∈ W.N T₂ :=
      F2c4 c _ (hev c hc) (RL.pullJ_le_φpull W T₂ c ht1) (RL.pullJ_letter W T₂ c ht1)
    rw [smul_sub, smul_add, smul_comm _ (((PD.p : ℕ) : O) ^ σ), smul_comm _ (((PD.p : ℕ) : O) ^ (s₁ + σ)),
      smul_comm _ (((PD.p : ℕ) : O) ^ N)]
    exact Submodule.sub_mem _ (Submodule.add_mem _ (Submodule.smul_of_tower_mem _ _ h1)
      (Submodule.smul_of_tower_mem _ _ h2)) (Submodule.smul_of_tower_mem _ _ h3)
  have hdl : ∀ c ∈ evens n d, ∀ f, DL W T₂ (c + 1) (uhL c f) := by
    intro c hc f
    rw [huh]
    exact invariantLetter_sub' W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ (hmhDL c hc f))
      (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ (hX2 (c + 1) f).1)
  have hg : ∀ c ∈ evens n d, ∀ f, W.γ T₂ (uhL c f) - uhL c f ∈ W.N T₂ := by
    intro c hc f
    have e := Step2A.gamma_difference_identity N s₁ σ (y f) (z f) (fun c' => ms c' f) (fun c' => tL c' f)
      (fun c' => μ c' f) c
    beta_reduce at e
    rw [huh, e]
    exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ (mem_of_mem_uniformizerLattice W T₂ (hxi c hc f).2.1))
      (Submodule.smul_of_tower_mem _ _ (mem_of_mem_uniformizerLattice W T₂ (hX2 (c + 1) f).2.2.1))
  obtain ⟨F₂, hle, hch, hm0, hPass⟩ := Step2E.passage_to_quotient W hK hD hR hE hDq hS F₁ uhL hq hdl hg
    (lenOl PD (O := O)) (lenC (finrank LL T₂.V) m PD.p (hpar n b S + η) S)

  let wL : ZMod n → ↥F₂ →ₗ[O] W.DD T₂ := fun c =>
    ((W.φD T₂).comp (mhL (c - 2)) +
      ((PD.p : ℕ) : O) ^ (s₁ + σ) • (Step2A.letterIdempotentMap W T₂ c).comp (y.comp F₁.subtype) -
      ((PD.p : ℕ) : O) ^ σ • (ms c).comp F₁.subtype).comp (Submodule.inclusion hle)
  have hw : ∀ c (f : ↥F₂), wL c f = frobeniusShiftDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f)
      (fun c' => tL c' (Submodule.inclusion hle f)) c := fun c f => rfl
  have hcm1 : ∀ c : ZMod n, c - 2 + 1 = c - 1 := fun c => by ring
  have hcm2 : ∀ c : ZMod n, c - 2 + 1 + 1 = c := fun c => by ring

  have hfacts : ∀ c ∈ evens n d, ∀ f : ↥F₂,
      uhL (c - 2) (Submodule.inclusion hle f) ∈ W.N T₂ ∧
      DL W T₂ (c - 1) (uhL (c - 2) (Submodule.inclusion hle f)) ∧
      DL W T₂ c (wL c f) := by
    intro c hc f
    have hc2' := hm2 c hc
    refine ⟨hPass (c - 2) hc2' _ f.2, by
      have := hdl (c - 2) hc2' (Submodule.inclusion hle f); rwa [hcm1] at this, ?_⟩
    rw [hw]
    obtain ⟨hms, -⟩ := hO c hc f
    have h1 := invariantLetter_frobenius_succ W T₂ (hmhDL (c - 2) hc2' (Submodule.inclusion hle f))
    rw [hcm2] at h1
    exact invariantLetter_sub' W T₂ (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T₂ h1 (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _
      (invariantLetter_idempotent_of_fixed W T₂ (fun δ hδ => ((hyz f).2 δ hδ).1)))) (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T₂ _ hms)
  have hNw : ∀ c ∈ evens n d, ∀ f : ↥F₂, ((PD.p : ℕ) : O) ^ N • wL c f =
      W.φD T₂ (uhL (c - 2) (Submodule.inclusion hle f)) -
        ((PD.p : ℕ) : O) ^ σ • (((PD.p : ℕ) : O) ^ N • ms c f - ((PD.p : ℕ) : O) ^ s₁ • μ c f) +
        ((PD.p : ℕ) : O) ^ (s₁ + σ) • (((PD.p : ℕ) : O) ^ N • ((letE c : LetA O n) • y f) +
          W.φD T₂ (μ (c - 1) f) - μ c f) := by
    intro c hc f
    have e := Step2A.frobenius_difference_identity N s₁ σ (y f) (fun c' => ms c' f)
      (fun c' => tL c' (Submodule.inclusion hle f)) (fun c' => μ c' f) c
    beta_reduce at e
    rw [hw, e, huh, hcm1]
    rfl

  have hφxi : ∀ c ∈ evens n d, ∀ f : ↥F₁,
      InPN W T₂ M (W.φD T₂ (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f)
        (fun c' => tL c' f) (c - 2))) ∧
      DL W T₂ c (W.φD T₂ (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f) (z f) (fun c' => ms c' f)
        (fun c' => tL c' f) (c - 2))) := by
    intro c hc f
    obtain ⟨-, hPN, hDL⟩ := hxi (c - 2) (hm2 c hc) f
    rw [hcm1] at hDL
    have hDL2 := invariantLetter_frobenius_succ W T₂ hDL
    rw [sub_add_cancel] at hDL2
    exact ⟨uniformizerLattice_frobenius W T₂ hu0 hΔπ M c (F2c1 c) hPN hDL, hDL2⟩
  have hdist1 : ∀ (q : LetA O n) (A B' C : W.DD T₂), q • (A - B' + C) = q • A - q • B' + q • C :=
    fun q A B' C => by rw [smul_add, smul_sub]
  have hdist2 : ∀ (a : O) (q : LetA O n) (A B' C : W.DD T₂),
      a • q • (A - B' + C) = a • q • A - a • q • B' + a • q • C :=
    fun a q A B' C => by rw [smul_add, smul_sub, smul_add, smul_sub]

  have h36 : ∀ c ∈ evens n d, ∀ f : ↥F₂, QPowSmulMemPullback W T₂ c η (wL c f) := by
    intro c hc f
    obtain ⟨huhN, huhD, hwD⟩ := hfacts c hc f
    obtain ⟨huN, huD⟩ := hu c hc (Submodule.inclusion hle f)
    have hE4 := (hX2 c f).2.2.2.1
    rw [hMi c hc] at hE4
    refine ⟨?_, hwD, ?_, ?_⟩
    ·
      obtain ⟨s', hs'⟩ := (hX2 c f).2.2.2.2.1
      rw [hhi c hc] at hs'
      refine mem_pullJ_of_p_pow_smul_mem_pullJ W T₂ hB hA hc2 (s' + N) ?_
      rw [pow_add, mul_smul, smul_comm (((PD.p : ℕ) : O) ^ N) (Formalism.MainNotions.LiftingTheory.qp W ^ η), hNw c hc f,
        hdist2]
      refine Submodule.add_mem _ (Submodule.sub_mem _ ?_ ?_) ?_
      · exact Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ s') (Submodule.smul_mem _
          (Formalism.MainNotions.LiftingTheory.qp W ^ η) (frobenius_mem_pullback_one W T₂ huhN huhD))
      · rw [smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ η) (((PD.p : ℕ) : O) ^ σ)]
        exact Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ s')
          (Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ σ) (h5D c hc _ huN huD))
      · rw [smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ η) (((PD.p : ℕ) : O) ^ (s₁ + σ)),
          smul_comm (((PD.p : ℕ) : O) ^ s') (((PD.p : ℕ) : O) ^ (s₁ + σ))]
        exact Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ (s₁ + σ)) hs'
    ·
      refine ⟨1, b c + S, ?_⟩
      have hpk : (∏ j ∈ Finset.range 1, Formalism.MainNotions.LiftingTheory.pk W j) = Formalism.MainNotions.LiftingTheory.qp W := by
        simp [Formalism.MainNotions.LiftingTheory.pk]
      rw [hpk]
      have hdq : DL W T₂ c (Formalism.MainNotions.LiftingTheory.qp W ^ (b c + S) • wL c f) :=
        ⟨by rw [smul_comm, hwD.1], fun δ hδ => by
          rw [RL.γD_smulA, map_pow, hqpΔ δ hδ, hwD.2 δ hδ]⟩
      refine mem_of_natCast_pow_smul_mem' W T₂ hB hA hc2 N hdq ?_
      rw [smul_comm (((PD.p : ℕ) : O) ^ N) (Formalism.MainNotions.LiftingTheory.qp W ^ (b c + S)), hNw c hc f, hdist1]
      refine Submodule.add_mem _ (Submodule.sub_mem _ (hpol c hc _ huhN huhD) ?_) ?_
      · rw [smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ (b c + S)) (((PD.p : ℕ) : O) ^ σ)]
        exact Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ σ) ((W.N T₂).smul_mem _ huN)
      · rw [smul_comm (Formalism.MainNotions.LiftingTheory.qp W ^ (b c + S)) (((PD.p : ℕ) : O) ^ (s₁ + σ))]
        exact Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ (s₁ + σ)) hE4
    ·
      rw [hw, gamma_sub_cocycleW _ _ (hyz f).1 c, ← hζL]
      exact uniformizerLattice_sub W T₂ (uniformizerLattice_antitone W T₂ hM1 hπ (hφxi c hc (Submodule.inclusion hle f)).1)
        (Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T₂ _ (hζ c hc f).2)

  have hcob : ∀ x : ↥(W.wachCocyclesDelta T₂), (∃ m0 : W.DD T₂, (∀ δ ∈ W.DelF, W.γD T₂ δ m0 = m0) ∧
      (x : W.DD T₂ × W.DD T₂) = (W.φD T₂ m0 - m0, W.γD T₂ W.gamK m0 - m0)) → W.clK T₂ x = 0 :=
    fun x hx => ((h2a T₂ hc2 hA.2.1 hA.2.2).2 x).2 hx
  have hYΔ : ∀ c ∈ evens n d, ∀ f : ↥F₂, ∀ δ ∈ W.DelF,
      W.γD T₂ δ (frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f)
        (fun c' => tL c' (Submodule.inclusion hle f)) c) =
      frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' (Submodule.inclusion hle f)) c := by
    intro c hc f δ hδ
    rw [cocycleY_eq_frobenius_add, ← hw, map_add, gammaD_frobenius_comm, (hfacts c hc f).2.2.2 δ hδ,
      (htL c hc (Submodule.inclusion hle f)).2.1.2 δ hδ]
  have hpack : ∀ f : ↥F₂, ∀ c, ∃ (xc : ↥(W.wachCocyclesDelta T₂)) (κc : G → T₂.V) (hκc : κc ∈ latticeCocycles T₂.L),
      c ∈ evens n d → (RhoCoc W T₂ c M η σ (wL c f) κc ∧
        W.clK T₂ xc = Submodule.Quotient.mk ⟨κc, hκc⟩ ∧
        DL W T₂ (c + 1) ((xc : W.DD T₂ × W.DD T₂).1 - ((PD.p : ℕ) : O) ^ σ •
          frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' (Submodule.inclusion hle f)) c) ∧
        InPN W T₂ M ((xc : W.DD T₂ × W.DD T₂).1 - ((PD.p : ℕ) : O) ^ σ •
          frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' (Submodule.inclusion hle f)) c) ∧
        InPN W T₂ M (xc : W.DD T₂ × W.DD T₂).2) := by
    intro f c
    by_cases hc : c ∈ evens n d
    swap; exact ⟨0, 0, (latticeCocycles T₂.L).zero_mem, fun h => (hc h).elim⟩
    set f₁ := Submodule.inclusion hle f with hf₁
    have hgw : W.γ T₂ (wL c f) - wL c f = (1 : O) • W.φD T₂ (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f₁) (z f₁)
        (fun c' => ms c' f₁) (fun c' => tL c' f₁) (c - 2)) + (-(((PD.p : ℕ) : O) ^ σ)) • ζL c f₁ := by
      rw [hw, gamma_sub_cocycleW _ _ (hyz f).1 c, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    obtain ⟨xc, κc, hκc, H⟩ := Step2K.level_membership_package W T₂ c M η σ hu0 hΔπ hπ hM1 hηM hZ hA hp11 hTC hc2
      (fun x h1 h2 => F2c4 c x (hev c hc) h1 h2)
      (fun w' z' hw' htr => (F2c5 c w' z' (hev c hc) hw' htr).1) (wL c f) _ (ζL c f₁) (tL c f₁) _
      (h36 c hc f).2 hgw (by rw [cocycleY_eq_frobenius_add, ← hw]) (hYΔ c hc f) ⟨(hφxi c hc f₁).2, (hφxi c hc f₁).1⟩ (hζ c hc f₁)
      (htL c hc f₁).2.2.2
    exact ⟨xc, κc, hκc, fun _ => H⟩
  refine ⟨F₂, wL, hch, hm0, h36, ?_⟩
  intro f
  choose xc κ hκ hP using hpack f
  refine ⟨κ, fun c hc => (hP c hc).1, Or.inl ?_⟩
  obtain ⟨x0, hκg, hx0, hcl0⟩ := hX1 (f : FF)
  set f₁ := Submodule.inclusion hle f with hf₁
  have hmE : ∀ δ ∈ W.DelF, W.γD T₂ δ (liftCorrectionSum W T₂ s₁ σ (y f) (fun c' => ms c' f)
      (fun c' => tL c' f₁) d) = liftCorrectionSum W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) d := by
    intro δ hδ
    unfold liftCorrectionSum
    rw [map_sum]
    refine Finset.sum_congr rfl fun c hc => ?_
    have h1 : W.γD T₂ δ (liftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) c) =
        liftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) c := (hmhDL c hc f₁).2 δ hδ
    rw [map_add, map_add, map_smul, gammaD_letter_smul, ((hyz f).2 δ hδ).1, gammaD_frobenius_comm, h1]
  have hcls := Step2C.sum_clK_eq_pow_smul_clK_of_level_decomposition W T₂ M (s₁ + σ) σ (evens n d) hgam hπ F2c2
    (fun i x h1 h2 h3 => ((F2c3 i x h1 h2).1 h3)) hcob x0 _ hmE
    (fun c => frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) c) xc
    (by rw [hx0]; exact first_component_sum_eq (fun c' => ms c' f) (fun c' => tL c' f₁) hn d)
    (by
      rw [hx0]
      show InPN W T₂ M (((PD.p : ℕ) : O) ^ (s₁ + σ) • z f + _)
      rw [second_component_sum_eq (fun c' => ms c' f) (fun c' => tL c' f₁) hn d (hyz f).1]
      refine Finset.sum_induction _ _ (fun a b ha hb => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ ha hb)
        (uniformizerLattice_zero W T₂ M) (fun c hc => Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T₂ (hxi c hc f₁).2.1 ?_)
      have hd0 := (hxi c hc f₁).2.2
      have hd : DL W T₂ (c + 2 - 1) (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f₁) (z f₁)
          (fun c' => ms c' f₁) (fun c' => tL c' f₁) c) := by
        rw [show c + 2 - 1 = c + 1 by ring]; exact hd0
      exact uniformizerLattice_frobenius W T₂ hu0 hΔπ M (c + 2) (F2c1 (c + 2)) (hxi c hc f₁).2.1 hd)
    (fun c hc => by
      show InPN W T₂ M (W.γ T₂ (frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) c) -
        frobeniusSquareDefectOfLiftCorrection W T₂ s₁ σ (y f) (fun c' => ms c' f) (fun c' => tL c' f₁) c)
      rw [gamma_sub_cocycle_component (fun c' => ms c' f) (fun c' => tL c' f₁) (hyz f).1 c]
      obtain ⟨hφPN, hφDL0⟩ := hφxi c hc f₁
      have hφDL : DL W T₂ (c + 1 - 1) (W.φD T₂ (gammaDefectOfLiftCorrection W T₂ s₁ σ (y f₁) (z f₁)
          (fun c' => ms c' f₁) (fun c' => tL c' f₁) (c - 2))) := by
        rw [add_sub_cancel_right]; exact hφDL0
      exact uniformizerLattice_sub W T₂ (uniformizerLattice_frobenius W T₂ hu0 hΔπ M (c + 1) (F2c1 (c + 1)) hφPN hφDL)
        (hxi c hc f₁).2.1)
    (fun c hc => hYΔ c hc f) (fun c hc => ⟨(hP c hc).2.2.1, (hP c hc).2.2.2.1⟩)
    (fun c hc => (hP c hc).2.2.2.2)
  exact Step2A.pow_smul_cocycle_sub_sum_mem_latticeCoboundaries W T₂ _ xc κ hκ (fun c hc => (hP c hc).2.1) x0 _ hκg hcl0 _
    (by rw [show s₁ + 2 * σ = s₁ + σ + σ by ring]; exact hcls)

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt

end
