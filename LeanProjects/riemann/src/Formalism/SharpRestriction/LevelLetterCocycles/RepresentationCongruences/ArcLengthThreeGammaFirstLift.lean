import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.DivAddLogbLeEightMulErrorScale
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TruncatedCoefficientPoly
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.PpLeHLD

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_gamma_first_lift [NeZero n] [Fintype (K →ₐ[Qp] LL)] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (IsLocalRing.maximalIdeal O) O] (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W)
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
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (Cb : ℝ) (hCb : 2 ≤ Cb) (halt : Alt b η up size)
    (hsm : 40 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size ≤ (b : ℝ) / 4)
    (hlen : (arcOf b w S η up size).len c = 3) (hD : up (c - 2) = false)
    (hOK : (arcOf b w S η up size).OK) (hσ : (((arcOf b w S η up size).σ PD.p : ℕ) : ℝ) ≤ 3 * Formalism.MainNotions.N.Ln17.Sg PD.p b w S η size)
    (hy : size (c - 1) < PD.p * (size (c - 2) + S + η))
    (lam : W.DD T₂) (hlam : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 1 lam)
    (hlamγ : InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (W.γ T₂ lam - lam)) (κ : ℕ) (Hh : W.DD T₂)
    (hHh : IsHorTr W T₂ bb sol ((arcOf b w S η up size).M PD.p) κ k₀ Hh)
    (h4a : ∃ κ' : ℕ, InFP W T₂ (c - (((arcOf b w S η up size).len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * (arcOf b w S η up size).G₀) ((arcOf b w S η up size).M PD.p))) (lA W ^ κ' • (lA W ^ κ • lam - lA W ^ ((arcOf b w S η up size).σ PD.p) • ((W.φD T₂) ^ 2) Hh)))
    (n₁ : W.DD T₁) (E : ℕ) (hn₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) n₁)
    (hmap : ∀ s : W.EE, algebraMap (LetA O n) W.EE (qA W ^ size (c - 1)) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (size (c - 2) + S)) → Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) (s • lam) ∧ W.map F n₁ = (((PD.p : ℕ) : LetA O n) ^ E) • (s • lam))
    (R₀ σ₁ κ₁ : ℕ) (X₁ x₁ y₁ Z : W.DD T₁) (hR₀ : size c + S ≤ (PD.p - 1) * R₀) (hR₁ : 1 ≤ R₀)
    (hX₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) X₁) (hx₁ : Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x₁)
    (hγX : W.γ T₁ X₁ - X₁ = W.π₀ ^ R₀ • x₁) (hy₁ : InFP W T₁ (c - 1) 1 1 y₁) (hZ : InFP W T₁ (c - 1) 1 1 Z)
    (hrel : lA W ^ κ₁ • y₁ + (W.π₀ * qA W ^ (size c + S)) • Z = lA W ^ σ₁ • W.φD T₁ X₁) :
    InI W T₁ c y₁ ∧ InFNc W T₁ c 1 (qA W ^ (size c + S) • y₁) := by
  have hT : IsCrys PD T₁.ρ := hW₁.1
  have hR : GS.RD W := NTB.ringData_of_crystalline W hcase hP9 T₁ hT
  obtain ⟨y, hyP, hyy⟩ := hy₁
  rw [one_smul] at hyy
  subst hyy
  obtain ⟨Zp, hZP, hZZ⟩ := hZ
  rw [one_smul] at hZZ
  subst hZZ
  have hLD := DYB.Pp_le_HLD W T₁ (c - 1) hyP
  rw [sub_add_cancel] at hLD

  have hup : up c = false := by
    have h1 := (halt (c - 2)).1
    have h2 := (halt (c - 1)).1
    have e1 : c - 2 + 1 = c - 1 := by ring
    rw [e1, hD] at h1
    rw [sub_add_cancel] at h2
    cases hc1 : up (c - 1) <;> simp_all

  have hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₁ (fun i => if up i then η else size i + S)
      (fun i => if up i then size i + S else η) := by
    intro τ i hτ a ha
    have h := hW₁.2 i τ hτ a ha
    have hok := hOK.2.2.2.2.1 i
    simp only [arcOf] at h hok
    cases hi : up i <;> simp [hi, Formalism.MainNotions.LocalTheoryWindows.LT.win, Formalism.MainNotions.LocalTheoryWindows.LT.ok] at h hok ⊢ <;> omega
  have h5 := (hP5 T₁ _ _ hT hJL).1 c
  simp only [hup, Bool.false_eq_true, ↓reduceIte] at h5
  have hring := ((hP9 T₁ hT hcase.2.1 hcase.2.2).2.2 (NTB.finrank_one W hcase)).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    have hQq : W.Q = W.q := by
      unfold LocWach.Q
      rw [hcase.2.1]
      simp
    rw [hQq, hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hq : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₁ (c - 1) x → qA W ^ (size c + S) • W.φD T₁ x ∈ W.N T₁ := by
    intro x hx
    have h := h5 x hx.2
    rw [hQ, mul_pow, mul_smul] at h
    have h' := (W.N T₁).smul_mem (((wq⁻¹ : (LetA O n)ˣ) : LetA O n) ^ (size c + S)) h
    rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h'

  have hγP : W.γ T₁ y₁ - y₁ ∈ Pp W T₁ (c - 1) 1 := sub_mem (DYB.Pp_γ W T₁ (c - 1) hyP) hyP
  obtain ⟨w, hwΔ, hwφ⟩ := NTB.w_mem hR
  obtain ⟨u, huΔ, hγπ⟩ := GS.gamma_pi0_eq_pi0_mul_unit hR
  obtain ⟨r, rfl⟩ : ∃ r, R₀ = r + 1 := ⟨R₀ - 1, by omega⟩
  obtain ⟨t, ht⟩ : ∃ t, (PD.p - 1) * (r + 1) = (size c + S) + t := ⟨_, (Nat.add_sub_of_le hR₀).symm⟩
  have hπΔ := GS.π₀_mem W
  have hqΔ := GS.qA_mem W
  have hlΔ : lA W ∈ W.AΔ := NTB.lA_mem'
  have ha₁ : lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hlΔ _) (W.AΔ.pow_mem hwΔ _))
      (W.AΔ.pow_mem hπΔ _)) (W.AΔ.pow_mem hqΔ _)
  have hu' : (1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S) ∈ W.AΔ :=
    W.AΔ.mul_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hqΔ))
      (W.AΔ.pow_mem (W.AΔ.add_mem (W.AΔ.one_mem) (W.AΔ.mul_mem huΔ hπΔ)) _)
  have hbrP : (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
      (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z - Z) ∈
      Pp W T₁ (c - 1) 1 := by
    refine sub_mem (AddSubgroup.subset_closure ⟨_, ha₁, x₁, hx₁, by rw [pow_one]⟩)
      (sub_mem (DYB.Pp_smul W T₁ (c - 1) hu' (DYB.Pp_γ W T₁ (c - 1) hZP)) hZP)
  have e1 : W.γ T₁ (lA W ^ κ₁ • y₁) = lA W ^ κ₁ • W.γ T₁ y₁ := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have e2 : lA W ^ κ₁ • y₁ = lA W ^ σ₁ • W.φD T₁ X₁ - (W.π₀ * qA W ^ (size c + S)) • Z :=
    eq_sub_of_add_eq hrel
  have e3 : W.γ T₁ (W.φD T₁ X₁) =
      W.φD T₁ X₁ + ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) • W.φD T₁ x₁ := by
    have h1 : W.γ T₁ (W.φD T₁ X₁) = W.φD T₁ (W.γ T₁ X₁) := (W.φγ_comm T₁ W.gam X₁).symm
    rw [h1, ← hwφ, ← map_pow, ← DYB.φD_smulA, ← map_add, ← hγX, add_sub_cancel]
  have e4 : W.γ T₁ ((W.π₀ * qA W ^ (size c + S)) • Z) =
      ((W.π₀ * qA W ^ (size c + S)) * ((1 + (u : LetA O n) * qA W) *
        (1 + (u : LetA O n) * W.π₀) ^ (size c + S))) • W.γ T₁ Z := by
    rw [DYB.γ_smulA, map_mul, map_pow, hγπ, GS.γqA hγπ, mul_pow]
    congr 1
    ring
  have e5 : W.γ T₁ (lA W ^ σ₁ • W.φD T₁ X₁) = lA W ^ σ₁ • W.γ T₁ (W.φD T₁ X₁) := by
    rw [DYB.γ_smulA, DYB.γA_lA_pow]
  have hscal : ((w : LetA O n) * W.π₀ * qA W ^ (PD.p - 1)) ^ (r + 1) =
      W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) := by
    rw [mul_pow, mul_pow, ← pow_mul, ht, pow_add]
    ring
  have hkey : lA W ^ κ₁ • (W.γ T₁ y₁ - y₁) = (W.π₀ * qA W ^ (size c + S)) •
      ((lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) * W.π₀ ^ r * qA W ^ t) • W.φD T₁ x₁ -
        (((1 + (u : LetA O n) * qA W) * (1 + (u : LetA O n) * W.π₀) ^ (size c + S)) • W.γ T₁ Z -
          Z)) := by
    rw [smul_sub, ← e1, e2, map_sub, e5, e3, e4, hscal]
    simp only [smul_add, smul_sub, smul_smul]
    rw [show lA W ^ σ₁ * (W.π₀ * qA W ^ (size c + S) * ((w : LetA O n) ^ (r + 1) * W.π₀ ^ r *
        qA W ^ t)) = W.π₀ * qA W ^ (size c + S) * (lA W ^ σ₁ * (w : LetA O n) ^ (r + 1) *
        W.π₀ ^ r * qA W ^ t) by ring]
    abel
  have hfP : W.π₀ * qA W ^ (size c + S) ∈ PiPs W := by
    have h0 : ps W 0 = qA W := by simp [ps]
    exact (PiPs W).mul_mem (Submonoid.subset_closure (Set.mem_insert _ _))
      ((PiPs W).pow_mem (Submonoid.subset_closure (Set.mem_insert_of_mem _ ⟨0, h0⟩)) _)
  obtain ⟨tt, httP, htt⟩ := hSatP hcase T₁ (c - 1) 1 (W.π₀ * qA W ^ (size c + S)) 1 hT hfP
    (PiPs W).one_mem (W.γ T₁ y₁ - y₁) ⟨_, hγP, rfl⟩ ⟨κ₁, _, hbrP, hkey⟩
  have httq := DYB.Pp_qpow W T₁ (c - 1) _ hq httP
  have httL := DYB.Pp_le_HLD W T₁ (c - 1) httP
  rw [sub_add_cancel] at httL
  refine ⟨⟨hLD.1, hLD.2, qA W ^ (size c + S) • tt, httq, ?_, ?_⟩,
    qA W ^ (size c + S) • y₁, DYB.Pp_qpow W T₁ (c - 1) _ hq hyP, ?_, (one_smul _ _).symm⟩
  · rw [smul_smul, mul_comm, ← smul_smul, httL.1]
  · rw [htt, smul_smul]
  · rw [smul_smul, mul_comm, ← smul_smul, hLD.1]

end Formalism.MainNotions.N.FrobeniusPowerSeries
