import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.QPowMemOfGenerator
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.InFNcOfInFPOfArcSigmaLe
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeMapLattice
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeInFPSmulPhiLambda
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ArcLengthThreeRepresentation
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.AlgebraMapMemInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.Pi0MemADelta

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17 TypesA

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem frobenius_relation_combination {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (L q g₁ g₂ t B' aX : R)
    (κ₂ κ₁' κ₀ κ b₁ σ σ₁ E w S : ℕ) (V FY Φ y₂ y₃ : M)
    (h₂ : L ^ κ₂ • g₂ • (L ^ (κ₀ + κ) • V - L ^ σ • aX • Φ) = q • y₂)
    (h₃ : L ^ κ₁' • g₁ • (L ^ (b₁ + κ) • FY - L ^ (σ₁ + E + σ + w + S) • Φ) = q • y₃)
    (hrel : t * aX * L ^ b₁ = B' * L ^ (κ₀ + σ₁ + E + w + S)) :
    L ^ (κ₂ + κ₁' + κ₀ + κ + b₁) • (g₁ * g₂) • (t • V - B' • FY) =
      q • ((g₁ * t * L ^ (κ₁' + b₁)) • y₂ - (g₂ * B' * L ^ (κ₂ + κ₀)) • y₃) := by
  have hrelV : (t * aX * L ^ b₁) • Φ = (B' * L ^ (κ₀ + σ₁ + E + w + S)) • Φ := by rw [hrel]
  linear_combination (norm := module) (g₁ * t * L ^ (κ₁' + b₁)) • h₂ - (g₂ * B' * L ^ (κ₂ + κ₀)) • h₃ +
    (g₁ * g₂ * L ^ (κ₁' + κ₂) * L ^ σ) • hrelV

theorem arc_length_three_final_bound [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR)
    (hW₁ : Win W (arcOf b w S η up size) T₁) (hW₂ : Win W (arcOf b w S η up size) T₂) (hH : Formalism.MainNotions.LiftingTheory.coreH W) (hTr : Formalism.MainNotions.LiftingTheory.coreTr W)
    (hRelay : RelayCore W) (hArc : ArcCore W) (hArcL : ArcLCore W) (hNN : UnivNNCore W)
    (hSat : SATcore W) (hSatP : Formalism.MainNotions.ArcLiftingSetup.SATPcore W) (hKill : KillerLevCore W) (hR2 : R2)
    (hO : ∀ x : O, 0 ≤ v (algebraMap O LL x)) (hOv : ∀ x : LL, 0 ≤ v x → ∃ y : O, algebraMap O LL y = x)
    (hinj : Function.Injective (algebraMap O LL))
    (hP2 : Formalism.MainNotions.DeltaInvariantLattices.P2W W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hpi0 : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hSec : ArcSecMapCore W) (hGL : ArcGamLiftCore W) (hHF : HorFrameCore W) (hFL : ArcFilLowCore W)
    (rr : ℕ) (hrr : (rr : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hkill : ∀ c ∈ (arcOf b w S η up size).cuts, Formalism.MainNotions.LiftingTheory.KillsΔ W F c (Formalism.MainNotions.LiftingTheory.lp W rr))
    (c : ZMod n) (hc : c ∈ (arcOf b w S η up size).cuts) {d : ℕ} (bb : Fin d → W.DD T₂)
    (sol : Fin d → ℕ → Fin d → LL)
    (hbb : IsHor W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) bb sol) (k₀ : Fin d)
    (hk₀ : InLpp W (arcOf b w S η up size) T₂ c bb k₀) (f : W.EE) (hf : InFF W (arcOf b w S η up size) c f) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (hP3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (hP4 : Formalism.MainNotions.DeltaInvariantLattices.P4W W Pt)
    (hPtEx : ∀ (i : ZMod n) (τ : K →ₐ[Qp] LL), Formalism.MainNotions.LiftingTheory.Over W τ i →
      ∃ ζ : LL, ζ ^ PD.p = 1 ∧ ζ ≠ 1 ∧ Pt i ζ τ)
    (hC4 : Formalism.MainNotions.N.LetterConditionLocal W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (f₂ : W.EE) (hf₂ : InFr W c (ps W 2 ^ (size (c - 2) + S)) (ps W 1 ^ size (c - 1)) f₂) (κ₀ : ℕ) (X₀ : O) (hX₀ : InFr W c (ps W 0 ^ (size c + S)) (ps W 1 ^ size (c - 1))
      (lE W κ₀ * f₂ - algebraMap (LetA O n) W.EE (letE c) * algebraMap O W.EE X₀))
    (hx0 : ∀ r : ℚ, v (algebraMap O LL X₀) = ((r : ℚ) : WithTop ℚ) →
      ((size (c - 2) : ℝ) + S - size (c - 1) + ((size c + S : ℕ) : ℝ) / PD.p - ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 -
        Real.logb PD.p (2 * (((arcOf b w S η up size).h : ℕ) : ℝ))) + κ₀ ≤ (r : ℝ))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam)) (hE : (E : ℝ) ≤ 8 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (y₁ : W.DD T₁) (σ₁ : ℕ) (hy₁ : ((σ₁ : ℝ) ≤ ((size c + S : ℕ) : ℝ) / ((PD.p : ℝ) - 1) + 1) ∧
      InFP W T₁ (c - 1) 1 1 y₁ ∧ InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) ∧
      ∃ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, ∃ κ' : ℕ,
        InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ κ' • g • (lA W ^ (size (c - 1) + κ) • W.map F y₁ -
          lA W ^ (σ₁ + E + (arcOf b w S η up size).σ PD.p + size (c - 2) + S) • ((W.φD T₂) ^ 3) Hh))) :
    ∃ (e : ℕ) (t₃ : O), (e : ℝ) ≤ 6 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ∧
      (∃ r : ℚ, v (algebraMap O LL t₃) = ((r : ℚ) : WithTop ℚ) ∧ (r : ℝ) ≤ 14 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size) ∧
      LiftsAt W (arcOf b w S η up size) F c bb sol k₀ (algebraMap O W.EE t₃ * f₂) e := by
  classical
  obtain ⟨hσ₁, hy₁P, hy₁I, hy₁N, g₁, hg₁, κ₁', hY⟩ := hy₁
  have hn₂ : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) :=
    fun s h => (hmap s h).1
  obtain ⟨hv₂P, g₂, hg₂, κ₂, hV⟩ := arc_length_three_inFP_smul_phi_lambda W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ κ₀ X₀ hX₀ lam hlam hlamγ κ Hh hHh h4a hn₂
  obtain ⟨⟨a₀, ha₀, hΛf⟩, hφl, hrep⟩ := arc_length_three_representation W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy f₂ hf₂ lam hlam hlamγ κ Hh hHh h4a

  have hB' := hB
  obtain ⟨hl11, hSet, -, hη20, hS20, -⟩ := hB'
  have hthick : ∀ d : ℕ, 1 ≤ d → d < 3 → Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1) := by
    intro d hd1 hd3
    by_contra hnt
    have hmem : d ∈ {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := ⟨hd1, hnt⟩
    have hle := Nat.sInf_le hmem
    have hlen' : (arcOf b w S η up size).len c =
        sInf {d : ℕ | 1 ≤ d ∧ ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - (d : ZMod n) + 1)} := rfl
    rw [hlen'] at hlen
    omega
  have ht1 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c - 1) := by
    have h := hthick 2 (by norm_num) (by norm_num)
    have e2 : c - ((2 : ℕ) : ZMod n) + 1 = c - 1 := by push_cast; ring
    rwa [e2] at h
  have ht0 : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c := by
    have h := hthick 1 le_rfl (by norm_num)
    have e1 : c - ((1 : ℕ) : ZMod n) + 1 = c := by push_cast; ring
    rwa [e1] at h
  have hhB : Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size = b + η + S := by
    unfold Formalism.MainNotions.TruncatedSeriesCountingBounds.hB
    rw [if_pos ⟨c - 1, ht1⟩]
  have hSgEq : Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size = Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
    unfold Formalism.MainNotions.N.Ln17.Sg Formalism.MainNotions.N.FrobeniusPowerSeries.Sg
    rw [hhB]
  have hp : (11 : ℝ) ≤ (PD.p : ℝ) := by exact_mod_cast hl11

  set σ := (arcOf b w S η up size).σ PD.p with hσdef
  set D₁ : ℕ := κ₀ + σ₁ + E + size (c - 2) + S with hD₁
  have hvp : v ((PD.p : ℕ) : LL) = 1 := by exact_mod_cast W.v_l
  have hp0 : ((PD.p : ℕ) : LL) ≠ 0 := by
    intro h0; rw [h0, AddValuation.map_zero] at hvp; exact WithTop.top_ne_coe hvp
  obtain ⟨t₃, B', hrel, r₃, hr₃, hr₃b⟩ : ∃ t₃ B' : O,
      t₃ * X₀ * ((PD.p : ℕ) : O) ^ size (c - 1) = B' * ((PD.p : ℕ) : O) ^ D₁ ∧
      ∃ r : ℚ, v (algebraMap O LL t₃) = ((r : ℚ) : WithTop ℚ) ∧ (r : ℝ) ≤ 14 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
    have hvcalc : ∀ (k : ℕ) (x : LL) (r : ℚ), v x = ((r : ℚ) : WithTop ℚ) →
        v (((PD.p : ℕ) : LL) ^ k * x⁻¹) = ((((k : ℚ) - r) : ℚ) : WithTop ℚ) := by
      intro k x r hr
      rw [AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv, hvp, hr]
      rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg, ← WithTop.coe_add,
        nsmul_one, sub_eq_add_neg]
    have hσ0 : (0 : ℝ) ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
      have : (0 : ℝ) ≤ (σ : ℝ) := Nat.cast_nonneg _
      linarith [hσ]
    by_cases hX : X₀ = 0
    · refine ⟨1, 0, by rw [hX]; ring, 0, ?_, ?_⟩
      · rw [map_one, AddValuation.map_one, WithTop.coe_zero]
      · push_cast; linarith
    have hXLL : algebraMap O LL X₀ ≠ 0 := fun h => hX (hinj (by rw [h, map_zero]))
    have hne : v (algebraMap O LL X₀) ≠ ⊤ := by
      intro h; exact hXLL ((AddValuation.top_iff v).1 h)
    obtain ⟨rX, hrX⟩ := WithTop.ne_top_iff_exists.1 hne
    have hrX0 : (0 : ℚ) ≤ rX := by
      have h0 := hO X₀; rw [← hrX] at h0; exact_mod_cast h0
    have hx0' := hx0 rX hrX.symm
    by_cases hlt : rX < ((D₁ + σ : ℕ) : ℚ) - (size (c - 1) : ℚ)
    · have hk : size (c - 1) ≤ D₁ + σ := by
        have : ((size (c - 1) : ℕ) : ℚ) ≤ ((D₁ + σ : ℕ) : ℚ) := by linarith
        exact_mod_cast this
      have hv1 := hvcalc (D₁ + σ - size (c - 1)) (algebraMap O LL X₀) rX hrX.symm
      obtain ⟨t₃, ht₃⟩ := hOv (((PD.p : ℕ) : LL) ^ (D₁ + σ - size (c - 1)) * (algebraMap O LL X₀)⁻¹) (by
        rw [hv1]
        have : (0 : ℚ) ≤ ((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX := by
          rw [Nat.cast_sub hk]; push_cast at hlt ⊢; linarith
        exact_mod_cast this)
      refine ⟨t₃, ((PD.p : ℕ) : O) ^ σ, ?_, ((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX, by rw [ht₃, hv1], ?_⟩
      · apply hinj
        simp only [map_mul, map_pow, map_natCast, ht₃]
        field_simp
        rw [← pow_add, ← pow_add, Nat.sub_add_cancel hk, add_comm]
      · have hb1 : 1 ≤ b := by
          have hh1 : 1 ≤ Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size := hOK.2.2.2.2.2.2.1
          have hlog : 0 ≤ Real.logb PD.p (2 * ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ)) :=
            Real.logb_nonneg (by linarith) (by
              have : (1 : ℝ) ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ) := by exact_mod_cast hh1
              linarith)
          have hSg1 : 1 ≤ Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size := by
            unfold Formalism.MainNotions.N.Ln17.Sg
            have h1 : (0 : ℝ) ≤ ((Formalism.MainNotions.TruncatedSeriesCountingBounds.hB b w S η size : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 := by positivity
            have h2 : (0 : ℝ) ≤ ((w : ℝ) + S + η) / PD.p := by positivity
            linarith
          have : (160 : ℝ) ≤ b := by linarith [hsm]
          exact_mod_cast (by linarith : (1 : ℝ) ≤ b)
        have hAh : ((arcOf b w S η up size).h : ℕ) = b + η + S := hhB
        have hBle : ((size c + S : ℕ) : ℝ) ≤ ((b + η + S : ℕ) : ℝ) := by
          have := ht0.2
          exact_mod_cast (by omega : size c + S ≤ b + η + S)
        have hv' : ((size (c - 2) : ℝ) + S - size (c - 1)) + ((size c + S : ℕ) : ℝ) / PD.p -
            ((size c + S : ℕ) : ℝ) / (PD.p : ℝ) ^ 2 - 2 - Real.logb PD.p (2 * ((b + η + S : ℕ) : ℝ)) ≤
            (rX : ℝ) - κ₀ := by
          rw [hAh] at hx0'; linarith
        have hE' : (E : ℝ) ≤ 8 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by rw [← hSgEq]; exact hE
        have hσ' : (σ : ℝ) ≤ 3 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by rw [← hSgEq]; exact hσ
        have h10 := Formalism.MainNotions.N.FrobeniusPowerSeries.sub_le_fourteen_mul_errorScale PD.p hl11 b w S η hb1 (σ₁ : ℝ) (E : ℝ) (σ : ℝ)
          ((size c + S : ℕ) : ℝ) (size (c - 2) : ℝ) (size (c - 1) : ℝ) ((rX : ℝ) - κ₀) (Nat.cast_nonneg _) hBle hσ₁
          hE' hσ' hv'
        rw [hSgEq]
        have hcast : ((D₁ + σ - size (c - 1) : ℕ) : ℝ) =
            (κ₀ : ℝ) + σ₁ + E + size (c - 2) + S + σ - size (c - 1) := by
          rw [Nat.cast_sub hk, hD₁]; push_cast; ring
        have hq : ((((D₁ + σ - size (c - 1) : ℕ) : ℚ) - rX : ℚ) : ℝ) =
            ((D₁ + σ - size (c - 1) : ℕ) : ℝ) - (rX : ℝ) := by push_cast; ring
        rw [hq, hcast]
        linarith
    · have hv2 : v (algebraMap O LL X₀ * ((PD.p : ℕ) : LL) ^ size (c - 1) * (((PD.p : ℕ) : LL) ^ D₁)⁻¹) =
          (((rX + size (c - 1) - D₁ : ℚ)) : WithTop ℚ) := by
        rw [AddValuation.map_mul, AddValuation.map_mul, AddValuation.map_pow, AddValuation.map_inv,
          AddValuation.map_pow, hvp, ← hrX]
        rw [← WithTop.coe_one, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul, ← WithTop.LinearOrderedAddCommGroup.coe_neg,
          ← WithTop.coe_add, ← WithTop.coe_add, nsmul_one, nsmul_one]
        congr 1; ring
      obtain ⟨B', hB'⟩ := hOv (algebraMap O LL X₀ * ((PD.p : ℕ) : LL) ^ size (c - 1) * (((PD.p : ℕ) : LL) ^ D₁)⁻¹) (by
        rw [hv2]
        have : (0 : ℚ) ≤ rX + size (c - 1) - D₁ := by
          push_cast at hlt; push Not at hlt
          have : (0 : ℚ) ≤ (σ : ℚ) := Nat.cast_nonneg _
          linarith
        exact_mod_cast this)
      refine ⟨1, B', ?_, 0, ?_, ?_⟩
      · apply hinj
        simp only [map_mul, map_pow, map_natCast, map_one, hB']
        field_simp
      · rw [map_one, AddValuation.map_one, WithTop.coe_zero]
      · push_cast; linarith

  set V : W.DD T₂ := f₂ • W.φD T₂ lam with hVdef
  set Φ : W.DD T₂ := ((W.φD T₂) ^ 3) Hh with hΦdef
  set De : W.DD T₂ := algebraMap O (LetA O n) t₃ • V - algebraMap O (LetA O n) B' • W.map F y₁ with hDedef
  have hDeP : InFP W T₂ (c - 1) 1 1 De :=
    inMultiple_sub W (inMultiple_smul W (algebraMap_mem_invariants W t₃) hv₂P)
      (inMultiple_smul W (algebraMap_mem_invariants W B') (arc_length_three_map_lattice W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy y₁ hy₁P))
  have hPsA : ∀ g ∈ Submonoid.closure {x : LetA O n | ∃ k ≥ 1, x = ps W k}, g ∈ W.AΔ := by
    intro g hg
    refine (Submonoid.closure_le (S := W.AΔ.toSubmonoid)).2 ?_ hg
    rintro _ ⟨k, -, rfl⟩
    exact ps_mem W k
  have hDe0 : ∃ k : ℕ, InFP W T₂ (c - 1) 1 (qA W ^ (size c + S)) (lA W ^ k • (g₁ * g₂) • De) := by
    obtain ⟨y₂, hy₂, hy₂e⟩ := hV
    obtain ⟨y₃, hy₃, hy₃e⟩ := hY
    have hrelL : algebraMap O (LetA O n) t₃ * algebraMap O (LetA O n) X₀ * lA W ^ size (c - 1) =
        algebraMap O (LetA O n) B' * lA W ^ D₁ := by
      have := congrArg (algebraMap O (LetA O n)) hrel
      simpa only [map_mul, map_pow, map_natCast, lA] using this
    have hrelL' : algebraMap O (LetA O n) t₃ * algebraMap O (LetA O n) X₀ * lA W ^ size (c - 1) =
        algebraMap O (LetA O n) B' * lA W ^ (κ₀ + σ₁ + E + size (c - 2) + S) := by
      rw [hrelL, hD₁]
    rw [← algebraMap_smul_eq_smul W X₀ Φ] at hy₂e
    refine ⟨κ₂ + κ₁' + κ₀ + κ + size (c - 1),
      (g₁ * algebraMap O (LetA O n) t₃ * lA W ^ (κ₁' + size (c - 1))) • y₂ -
        (g₂ * algebraMap O (LetA O n) B' * lA W ^ (κ₂ + κ₀)) • y₃, ?_, ?_⟩
    · exact sub_mem
        (Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem (hPsA g₁ hg₁) (algebraMap_mem_invariants W t₃)) (lA_pow_mem W _)) hy₂)
        (Pp_smul W (W.AΔ.mul_mem (W.AΔ.mul_mem (hPsA g₂ hg₂) (algebraMap_mem_invariants W B')) (lA_pow_mem W _)) hy₃)
    · rw [hDedef]
      exact frobenius_relation_combination (lA W) (qA W ^ (size c + S)) g₁ g₂ (algebraMap O (LetA O n) t₃) (algebraMap O (LetA O n) B')
        (algebraMap O (LetA O n) X₀) κ₂ κ₁' κ₀ κ (size (c - 1)) σ σ₁ E (size (c - 2)) S V (W.map F y₁) Φ y₂ y₃
        hy₂e hy₃e hrelL'
  have hDeq := q_pow_mem_of_generator W hcase hP9 hSatP hO hOv hinj hW₂.1 (c - 1) (size c + S) (g₁ * g₂)
    (Submonoid.mul_mem _ hg₁ hg₂) De hDeP hDe0
  have hDeN := inFNc_of_inFP_of_arc_sigma_le W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy De hDeq
  obtain ⟨De₁, hDe₁N, hDe₁I, hFDe₁⟩ := arc_length_three_annihilate W hcase F hB CR hWR hW₁ hW₂ hH hTr hRelay hArc hArcL hNN hSat hSatP hKill hR2 hO hOv hinj hP2 hP9 hpi0 hSec hGL hHF hFL rr hrr hkill c hc bb sol hbb k₀ hk₀ f hf Pt hP3 hP4 hPtEx hC4 hP5 Cb hCb halt hsm hlen hD hOK hσ hy De hDeN
  set tt : O := ((PD.p : ℕ) : O) ^ rr * B' with htt
  have hFw : W.map F (De₁ + algebraMap O (LetA O n) tt • y₁) =
      algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ rr * t₃) • V := by
    have hlA : lA W = algebraMap O (LetA O n) ((PD.p : ℕ) : O) := by simp [lA]
    rw [map_add, map_smulA W F, hFDe₁, hDedef, htt, map_mul, map_mul, map_pow, ← hlA]
    simp only [smul_sub, mul_smul]
    abel
  refine ⟨rr + σ, t₃, ?_, ⟨r₃, hr₃, hr₃b⟩, ?_⟩
  · push_cast; linarith [hrr, hσ]
  · have h0 : ps W 0 = qA W := by simp [ps]
    have hqA : qA W ∈ W.AΔ := h0 ▸ ps_mem W 0
    have hΛV : abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c) • V = a₀ • W.φD T₂ lam := by
      rw [hVdef, ← algebraMap_smul W.EE (abelian₂ W (arcOf b w S η up size) c ((arcOf b w S η up size).len c)) (f₂ • W.φD T₂ lam), smul_smul, hΛf,
        algebraMap_smul]
    unfold LiftsAt
    refine ⟨De₁ + algebraMap O (LetA O n) tt • y₁, 0, InI_add W hDe₁I (inI_algebraMap_smul W tt hy₁I),
      ⟨qA W ^ (size c + S), ?_, ?_⟩, ?_, ?_, ?_⟩
    · rw [← h0]; exact Submonoid.pow_mem _ (Submonoid.subset_closure (Set.mem_range_self (f := ps W) 0)) _
    · rw [smul_add]
      refine InFNc_add W (InFNc_smul W (W.AΔ.pow_mem hqA _) hDe₁N) ?_
      rw [smul_comm]
      exact InFNc_smul W (algebraMap_mem_invariants W tt) hy₁N
    · rw [hFw, smul_comm, hΛV]
      exact inMultiple_smul W (algebraMap_mem_invariants W _) (inMultiple_smul W ha₀ hφl)
    · exact ⟨0, zero_mem _, smul_zero _, (smul_zero _).symm⟩
    · rw [sub_zero, hFw]
      have h6 := repVV_smul_invariant W (algebraMap O (LetA O n) (((PD.p : ℕ) : O) ^ rr * t₃)) (algebraMap_mem_invariants W _) hrep
      refine RepVV_congr W h6 rfl fun k => ?_
      split_ifs
      · simp only [lE, ← IsScalarTower.algebraMap_apply, map_mul, map_pow, map_natCast]; ring
      · rw [mul_zero]

end Formalism.MainNotions.N.FrobeniusPowerSeries
