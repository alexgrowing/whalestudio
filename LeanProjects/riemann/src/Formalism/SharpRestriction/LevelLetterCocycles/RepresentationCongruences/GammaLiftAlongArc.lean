import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction

noncomputable section

open Classical

namespace Formalism.MainNotions.N.Ln17

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module TensorProduct Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.UnusedSlot80 Formalism.MainNotions.UnusedSlot80.UnivF

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} (W : LocWach PD LL O v n)

theorem gamma_lift_along_arc [IsDomain O] (hinj : Function.Injective (algebraMap O LL))
    (hArc : ArcCore W)
    (hR : Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀
      (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)))
    (hS : Formalism.MainNotions.UnusedSlot80.KL.PsStable W)
    (hP : ∃ u ∈ W.AΔ, W.γA W.gam W.π₀ = W.π₀ * u)
    (hCA : Formalism.MainNotions.LiftingTheory.CaseA W) (h5 : 5 ≤ PD.p) (A : ArcP n) (hA : A.OK) (c : ZMod n) (hc : c ∈ A.cuts)
    (e : ℕ) (hje : A.j ≤ e) (hel : e ≤ A.len c) (T : LocLat G Qp LL O) (hT : Win W A T)
    (d : ℕ) (b : Fin d → W.DD T) (sol : Fin d → ℕ → Fin d → LL)
    (hhor : IsHor W T (c - ((A.len c : ℕ) : ZMod n)) b sol)
    (f : Fin d → W.EE)
    (hf : ∀ k, InFr W (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) 1
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) (f k))
    (hinv : InvNL W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e
      (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b f) :
    ∃ u, InI W T (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) u ∧
      InFP W T (c - ((A.len c : ℕ) : ZMod n)) e 1
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e • u) ∧
      RepVV W T (c - ((A.len c : ℕ) : ZMod n)) e (A.M PD.p)
        (abelian₂ W A (c - ((A.len c : ℕ) : ZMod n) + (e : ZMod n)) e) b sol u
        (fun k => lE W (A.σ PD.p) * f k) := by
  have hπ := Formalism.MainNotions.UnusedSlot80.UnivC.uniformizer_mem_delta_invariants W
  have hAC := (hArc hCA h5 A hA c hc e hje hel).2 T hT
  set c' := c - ((A.len c : ℕ) : ZMod n) with hc'
  set a := c' + (e : ZMod n) with ha
  set Λ := abelian₂ W A a e with hΛdef
  obtain ⟨hP1, hP2, -, hF⟩ := hAC
  obtain ⟨-, -, hlift, -, hNL, hzero, -⟩ := hF d b sol hhor
  have hΛmem : Λ ∈ W.AΔ := lam_mem W A a e
  obtain ⟨u, huP, huR⟩ := hlift f hf
  obtain ⟨p0, hp0, hup0⟩ := huP
  rw [one_smul] at hup0
  have hlet : InLet W T a u := by
    show (letE a : LetA O n) • u = u
    refine lam_cancel W hR A a e T ?_
    rw [smul_comm, hup0]
    exact Relay2.Pp_letter W T c' e p0 hp0
  have hΔ : IsΔ W T u := by
    intro δ hδ
    refine lam_cancel W hR A a e T ?_
    have h1 : W.γD T δ (Λ • u) = Λ • W.γD T δ u := by
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hΛmem δ hδ]
    rw [← h1, hup0, Relay2.Pp_Δ W T c' e p0 hp0 δ hδ]
  obtain ⟨w, hw, w', hw', hww, hγΛ⟩ := lam_γ W hS A a e
  obtain ⟨u0, hu0, hγπ⟩ := hP
  have hπΛ : ∃ t, W.γA W.gam (W.π₀ * Λ ^ 2) = t * (W.π₀ * Λ ^ 2) ∧ t ∈ W.AΔ :=
    ⟨u0 * w ^ 2, by rw [map_mul, map_pow, hγπ, hγΛ]; ring, W.AΔ.mul_mem hu0 (W.AΔ.pow_mem hw _)⟩
  have hJJ : ∀ x', Formalism.MainNotions.LiftingTheory.InNΔi W T c' x' →
      InFP W T c' e (W.π₀ * Λ ^ 2) (((W.φD T) ^ e) (W.π₀ ^ A.M PD.p • x')) :=
    fun x' hx' => jj_lam W hR h5 A hA a e T c' hx'
  have hsol : ∀ k, Formalism.MainNotions.LiftingTheory.IsSol W T c' b 0 (sol k) := fun k => (hhor.2 k).1
  have hγu := repVV_γ W hsol hJJ hw hw' hww hγΛ hπΛ huR
  obtain ⟨g, hgNL, hg⟩ := hinv
  obtain ⟨y, hyN, hyR⟩ := hNL g hgNL
  have hπy := repVV_smul W hyR hπ
  have hz := repVV_sub W hinj (repVV_sub W hinj hγu huR) hπy
  have hz0 : (((fun k => W.γE W.gam (lE W (A.σ PD.p) * f k)) - fun k => lE W (A.σ PD.p) * f k) -
      fun k => algebraMap (LetA O n) W.EE W.π₀ * (lE W (A.σ PD.p) * g k)) = 0 := by
    funext k
    simp only [Pi.sub_apply, Pi.zero_apply, map_mul]
    have hl : W.γE W.gam (lE W (A.σ PD.p)) = lE W (A.σ PD.p) := by
      unfold lE; rw [map_pow, map_natCast]
    rw [hl, ← mul_sub, hg k]
    ring
  rw [hz0] at hz
  have hγΛu : InFP W T c' e 1 (Λ • W.γ T u) := by
    have h1 : Λ • W.γ T u = w' • W.γ T (Λ • u) := by
      show _ = w' • W.γD T W.gam (Λ • u)
      rw [Formalism.MainNotions.LiftingTheory.frame_γD_smul, hγΛ, smul_smul, ← mul_assoc, hww, one_mul]
      rfl
    refine ⟨w' • W.γ T p0, Relay2.Pp_smul W T c' _ hw' _ (Relay2.Pp_γ W T c' _ p0 hp0), ?_⟩
    rw [one_smul, h1, hup0]
  have hΛu : InFP W T c' e 1 (Λ • u) := ⟨p0, hp0, by rw [one_smul, hup0]⟩
  have hΛy : InFP W T c' e 1 (Λ • (W.π₀ • y)) := by
    rw [smul_comm]
    exact Relay2.inMultiple_smul W T c' _ _ hπ (hP2 y hyN)
  have hΛz : InFP W T c' e 1 (Λ • (W.γ T u - u - W.π₀ • y)) := by
    rw [smul_sub, smul_sub]
    exact Relay2.inMultiple_sub W T c' _ _ (Relay2.inMultiple_sub W T c' _ _ hγΛu hΛu) hΛy
  obtain ⟨p1, hp1, hzp⟩ := hzero _ hΛz hz
  obtain ⟨y2, hy2, hy2c, hy2e⟩ := hP1 p1 hp1
  obtain ⟨y1, hy1, hy1c, hy1e⟩ := hyN
  rw [one_smul] at hy2e hy1e
  refine ⟨u, ⟨hlet, hΔ, y1 + y2, (W.NΔ T).add_mem hy1 hy2, ?_, ?_⟩, ⟨p0, hp0, by rw [one_smul, hup0]⟩,
    huR⟩
  · rw [smul_add, hy1c, hy2c]
  · have : W.γ T u - u = (W.γ T u - u - W.π₀ • y) + W.π₀ • y := by abel
    rw [this, hzp, mul_smul, hy2e, hy1e, smul_add, add_comm]

end Core

end Formalism.MainNotions.N.Ln17
