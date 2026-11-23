import Formalism.SharpRestriction.LevelLetterCocycles.IsTruncIff
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.Pi0PowSmulInjective
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.ExistsInIInPNPowSmulSubMap
import Formalism.SharpRestriction.LevelLetterCocycles.KillerLevCoreOf
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX)
open Formalism.MainNotions.N.Pv.LocalLengthBound

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Alg

variable (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem gammaD_letter_smul (g : W.Gam) (i : ZMod n) (x : W.DD T) :
    W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [RL.γD_smulA, Formalism.MainNotions.UnusedSlot80.KL.γA_letE]

theorem gamma_letter_smul (i : ZMod n) (x : W.DD T) :
    W.γ T ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γ T x :=
  gammaD_letter_smul W T W.gam i x

theorem frobenius_letter_shift (i : ZMod n) (x : W.DD T) :
    W.φD T ((letE i : LetA O n) • x) = (letE (i + 1) : LetA O n) • W.φD T x := by
  rw [Formalism.MainNotions.WachCoordinates.Br.φD_smulA]
  have := Formalism.MainNotions.WachCoordinates.Br.φA_letE W (i + 1)
  rw [add_sub_cancel_right] at this
  rw [this]

theorem gamma_frobenius_comm (x : W.DD T) : W.γ T (W.φD T x) = W.φD T (W.γ T x) := (W.φγ_comm T W.gam x).symm

theorem gammaD_frobenius_comm (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.φD T x) = W.φD T (W.γD T δ x) :=
  (W.φγ_comm T δ x).symm

theorem gammaD_gamma_comm' (δ : W.Gam) (x : W.DD T) : W.γD T δ (W.γ T x) = W.γ T (W.γD T δ x) := by
  show W.γD T δ (W.γD T W.gam x) = W.γD T W.gam (W.γD T δ x)
  rw [← W.γD_mul, ← W.γD_mul, mul_comm]

theorem invariantLetter_frobenius_succ {i : ZMod n} {x : W.DD T} (h : DL W T i x) : DL W T (i + 1) (W.φD T x) :=
  ⟨by rw [← frobenius_letter_shift, h.1], fun δ hδ => by rw [gammaD_frobenius_comm, h.2 δ hδ]⟩

theorem invariantLetter_gamma {i : ZMod n} {x : W.DD T} (h : DL W T i x) : DL W T i (W.γ T x) :=
  ⟨by rw [← gamma_letter_smul, h.1], fun δ hδ => by rw [gammaD_gamma_comm', h.2 δ hδ]⟩

theorem invariantLetter_idempotent_of_fixed {i : ZMod n} {x : W.DD T} (h : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    DL W T i ((letE i : LetA O n) • x) :=
  ⟨by rw [smul_smul, RL.letE_mul_self'], fun δ hδ => by rw [gammaD_letter_smul, h δ hδ]⟩

theorem invariantLetter_neg {i : ZMod n} {x : W.DD T} (h : DL W T i x) : DL W T i (-x) :=
  ⟨by rw [smul_neg, h.1], fun δ hδ => by rw [map_neg, h.2 δ hδ]⟩

theorem invariantLetter_sub' {i : ZMod n} {x x' : W.DD T} (h : DL W T i x) (h' : DL W T i x') :
    DL W T i (x - x') := by
  rw [sub_eq_add_neg]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_add W T h (invariantLetter_neg W T h')

theorem invariantLetter_zero (i : ZMod n) : DL W T i (0 : W.DD T) :=
  ⟨smul_zero _, fun δ _ => map_zero _⟩

theorem uniformizerLattice_neg {k : ℕ} {x : W.DD T} (h : InPN W T k x) : InPN W T k (-x) := by
  have := Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_smul W T (-1 : O) h
  rwa [neg_one_smul] at this

theorem uniformizerLattice_sub {k : ℕ} {x x' : W.DD T} (h : InPN W T k x) (h' : InPN W T k x') :
    InPN W T k (x - x') := by
  rw [sub_eq_add_neg]; exact Formalism.MainNotions.RamifiedCoefficientChains.S9.inPN_add W T h (uniformizerLattice_neg W T h')

theorem uniformizerLattice_zero (k : ℕ) : InPN W T k (0 : W.DD T) :=
  ⟨0, (W.N T).zero_mem, fun δ _ => map_zero _, (smul_zero _).symm⟩

theorem uniformizerLattice_antitone {k K : ℕ} (hk : k ≤ K) (hπ : W.π₀ ∈ W.AΔ) {x : W.DD T} (h : InPN W T K x) :
    InPN W T k x := by
  obtain ⟨y, hy, hΔ, rfl⟩ := h
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hk
  refine ⟨W.π₀ ^ t • y, (W.N T).smul_mem _ hy, fun δ hδ => ?_, ?_⟩
  · rw [RL.γD_smulA, map_pow, hπ δ hδ, hΔ δ hδ]
  · rw [smul_smul, ← pow_add]

theorem mem_of_mem_uniformizerLattice {k : ℕ} {x : W.DD T} (h : InPN W T k x) : x ∈ W.N T := by
  obtain ⟨y, hy, -, rfl⟩ := h
  exact (W.N T).smul_mem _ hy

theorem uniformizerLattice_delta_fixed {k : ℕ} (hπ : W.π₀ ∈ W.AΔ) {x : W.DD T} (h : InPN W T k x) :
    ∀ δ ∈ W.DelF, W.γD T δ x = x := by
  obtain ⟨y, -, hΔ, rfl⟩ := h
  intro δ hδ
  rw [RL.γD_smulA, map_pow, hπ δ hδ, hΔ δ hδ]

theorem mem_pullback_zero {i : ZMod n} {x : W.DD T} (hx : x ∈ W.N T) (hd : DL W T i x) :
    x ∈ pullJ W T i 0 :=
  Submodule.subset_span ⟨x, ⟨hx, hd⟩, by simp⟩

theorem pullback_zero_le (i : ZMod n) : pullJ W T i 0 ≤ W.N T := by
  unfold pullJ
  rw [Submodule.span_le]
  rintro _ ⟨y, ⟨hy, -⟩, rfl⟩
  simpa using hy

theorem frobenius_mem_pullback_one {i : ZMod n} {x : W.DD T} (hx : x ∈ W.N T) (hd : DL W T i x) :
    W.φD T x ∈ pullJ W T i 1 :=
  Submodule.subset_span ⟨x, ⟨hx, hd⟩, by simp⟩

theorem frobeniusPoly_smul_mem_lattice (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1))
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) (c : ZMod n) (M η : ℕ)
    (h4 : ∀ x : W.DD T, x ∈ W.φpull T → (letE (c + 1) : LetA O n) • x = x →
      Formalism.MainNotions.LiftingTheory.qp W ^ η • x ∈ W.N T)
    {p x : W.DD T} (hp : p ∈ pullJ W T c 1) (hx : x = fMX W M η • p)
    (hxΔ : ∀ δ ∈ W.DelF, W.γD T δ x = x) : InPN W T M x :=
  RL.inPN_of_inv W T hu hΔπ M (h4 p (RL.pullJ_le_φpull W T c hp) (RL.pullJ_letter W T c hp))
    (by rw [hx, fMX, mul_smul]) hxΔ

theorem uniformizerLattice_frobenius (hu : ∃ u : (LetA O n)ˣ, W.π₀ = (u : LetA O n) * letπ ^ (PD.p - 1))
    (hΔπ : ∀ δ ∈ W.DelF, W.γA δ W.π₀ = W.π₀) (M : ℕ) (i : ZMod n)
    (h1 : ∀ x : W.DD T, x ∈ W.N T → DL W T (i - 1) x →
      ∃ y ∈ W.N T, W.φD T (W.π₀ ^ M • x) = (W.π₀ ^ M * Formalism.MainNotions.LiftingTheory.qp W) • y)
    {x : W.DD T} (hx : InPN W T M x) (hd : DL W T (i - 1) x) : InPN W T M (W.φD T x) := by
  obtain ⟨y, hy, hyΔ, rfl⟩ := hx
  have hyl : (letE (i - 1) : LetA O n) • y = y := by
    apply RL.pi0_pow_smul_injective W T hu M
    rw [smul_comm, hd.1]
  obtain ⟨y', hy', e⟩ := h1 y hy ⟨hyl, hyΔ⟩
  refine RL.inPN_of_inv W T hu hΔπ M ((W.N T).smul_mem (Formalism.MainNotions.LiftingTheory.qp W) hy') (by rw [e, mul_smul]) ?_
  intro δ hδ
  rw [gammaD_frobenius_comm, RL.γD_smulA, map_pow, hΔπ δ hδ, hyΔ δ hδ]

theorem mem_of_natCast_pow_smul_mem' [NeZero n] (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hc : IsCrys PD T.ρ) {i : ZMod n} {x : W.DD T} (s : ℕ) (hd : DL W T i x)
    (h : ((PD.p : ℕ) : O) ^ s • x ∈ W.N T) : x ∈ W.N T := by
  obtain ⟨⟨e, he⟩, h2⟩ := hB hA T hc i
  have hsat := ((h2 _ e he 0).2 x s)
  exact pullback_zero_le W T i (hsat (mem_pullback_zero W T h (Formalism.MainNotions.RamifiedCoefficientChains.S9.dl_smul W T _ hd)))

theorem mem_pullJ_of_p_pow_smul_mem_pullJ [NeZero n] (hB : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BasTool W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (hc : IsCrys PD T.ρ) {i : ZMod n} {x : W.DD T} (s : ℕ)
    (h : ((PD.p : ℕ) : O) ^ s • x ∈ pullJ W T i 1) : x ∈ pullJ W T i 1 := by
  obtain ⟨⟨e, he⟩, h2⟩ := hB hA T hc i
  exact (h2 _ e he 1).2 x s h

theorem frobeniusSpan_le_pullback (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (i : ZMod n) :
    Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤ (pullJ W T (i - 1) 1) := by
  obtain ⟨⟨r, b, hb, hbN, -⟩, -⟩ := hmod
  unfold Formalism.MainNotions.DeltaInvariantLattices.φspan
  rw [Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨a, ha, -⟩ := hbN x' hx'
  simp only [LinearMap.smul_apply, LinearMap.id_apply, SetLike.mem_coe]
  rw [ha, Finset.smul_sum, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [smul_comm, Formalism.MainNotions.WachCoordinates.Br.φD_smulA]
  refine Submodule.smul_mem _ _ (frobenius_mem_pullback_one W T ((W.N T).smul_mem _ (hb j).1)
    (invariantLetter_idempotent_of_fixed W T (hb j).2))

theorem q_pow_smul_mem_pullback [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (Mi hi : ZMod n → ℕ) (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T Mi hi)
    (c : ZMod n) {y : W.DD T} (hy : y ∈ W.N T) (hd : DL W T c y) :
    Formalism.MainNotions.LiftingTheory.qp W ^ hi c • y ∈ pullJ W T (c - 1) 1 := by
  obtain ⟨u, hu, -⟩ := Formalism.MainNotions.N.Pv.LocalLengthBound.qp_unit W hs hR
  have h2 := h5.2.1 c y (Formalism.MainNotions.N.Pv.LocalLengthBound.mem_Nl W T hy hd.1)
  rw [hu, mul_pow, mul_smul]
  exact Submodule.smul_mem _ _ (frobeniusSpan_le_pullback W T hmod c h2)

theorem sum_letter_idempotents_smul [NeZero n] (x : W.DD T) : ∑ i : ZMod n, (letE i : LetA O n) • x = x := by
  rw [← Finset.sum_smul]
  have : ∑ i : ZMod n, (letE i : LetA O n) = 1 := by
    unfold letE
    exact Finset.univ_sum_single (fun _ => (1 : PowerSeries O))
  rw [this, one_smul]

end Alg

section Sums

variable {M : Type} [AddCommMonoid M]

theorem parity_add_two [NeZero n] (hn : Even n) (d : ℕ) (c : ZMod n) :
    ((c + 2).val + d) % 2 = (c.val + d) % 2 := by
  have h1 := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c
  have h2 := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c + 1)
  rw [show c + 1 + 1 = c + 2 by ring] at h2
  omega

theorem mem_evens_iff [NeZero n] {d : ℕ} {c : ZMod n} :
    c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d ↔ (c.val + d) % 2 = 0 := by
  unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.evens
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem sum_evens_shift_add_two [NeZero n] (hn : Even n) (d : ℕ) (g : ZMod n → M) :
    ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, g (c + 2) = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, g c := by
  refine Finset.sum_nbij' (fun c => c + 2) (fun c => c - 2) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    try simp only [Finset.mem_coe] at hc ⊢
    rw [mem_evens_iff] at hc ⊢
    rw [parity_add_two hn d]; exact hc
  · intro c hc
    try simp only [Finset.mem_coe] at hc ⊢
    rw [mem_evens_iff] at hc ⊢
    rw [← parity_add_two hn d (c - 2), sub_add_cancel]; exact hc
  · intro c _; simp
  · intro c _; simp
  · intro c _; rfl

theorem sum_evens_shift_sub_two [NeZero n] (hn : Even n) (d : ℕ) (g : ZMod n → M) :
    ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, g (c - 2) = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, g c := by
  rw [← sum_evens_shift_add_two hn d (fun c => g (c - 2))]
  simp

theorem sum_eq_sum_evens_pairs [NeZero n] (hn : Even n) (d : ℕ) (g : ZMod n → M) :
    ∑ i : ZMod n, g i = ∑ c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d, (g (c + 1) + g (c + 2)) := by
  rw [Finset.sum_add_distrib, sum_evens_shift_add_two hn d,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun c : ZMod n => (c.val + d) % 2 = 0)]
  rw [add_comm]
  congr 1
  refine Finset.sum_nbij' (fun c => c - 1) (fun c => c + 1) ?_ ?_ ?_ ?_ ?_
  · intro c hc
    try simp only [Finset.mem_coe] at hc ⊢
    rw [Finset.mem_filter] at hc
    rw [mem_evens_iff]
    have hc2 := hc.2
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d (c - 1)
    rw [sub_add_cancel] at this
    omega
  · intro c hc
    try simp only [Finset.mem_coe] at hc ⊢
    rw [mem_evens_iff] at hc
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c
    omega
  · intro c _; simp
  · intro c _; simp
  · intro c _; simp

theorem sub_two_mem_evens [NeZero n] (hn : Even n) {d : ℕ} {c : ZMod n} (hc : c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d) :
    c - 2 ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d := by
  rw [mem_evens_iff, ← parity_add_two hn d (c - 2), sub_add_cancel]; exact mem_evens_iff.1 hc

theorem succ_not_mem_evens [NeZero n] (hn : Even n) {d : ℕ} {c : ZMod n} (hc : c ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.evens n d) :
    ¬ (((c + 1).val + d) % 2 = 0) := by
  have h1 := Formalism.MainNotions.RamifiedCoefficientChains.S9.parity_succ hn d c; have h2 := mem_evens_iff.1 hc; omega

end Sums

end Formalism.MainNotions.RamifiedCoefficientChains.S9.ExtensionLemmaAlt.Step2L

end
