import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.ImportsAlt
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RepVVSmulA
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.CmpDSmulLetter
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.RingDataOfCaseAOfP9
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.LemGBInImgIff

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

variable [FiniteDimensional Qp LL]

theorem arc_length_three_hyp_second (W : LocWach PD LL O v n) (hcase : Formalism.MainNotions.LiftingTheory.CaseA W) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W)
    (hP5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W) (A : ArcP n) (c : ZMod n) (hlen : A.len c = 3) {T₂ : LocLat G Qp LL O}
    (hT₂ : IsCrys PD T₂.ρ) (Mi' hi' : ZMod n → ℕ) (hJL : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T₂ Mi' hi') {b₁ w' A₀ : ℕ}
    (hM1 : Mi' (c - 2) = w' + A.S) (hM2 : Mi' (c - 1) = A.η)
    (hN : b₁ + A₀ + A.η ≤ (PD.p - 1) * A.M PD.p) (hM : 1 ≤ A.M PD.p) (lam : W.DD T₂)
    (hlamγ : InFP W T₂ (c - ((A.len c : ℕ) : ZMod n)) 2 (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)))
      (W.γ T₂ lam - lam))
    (s : W.EE) (hs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * s =
      algebraMap (LetA O n) W.EE (ps W 1 ^ (w' + A.S))) :
    ∃ y, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) y ∧
      W.γE W.gam s • (W.γ T₂ lam - lam) = (W.π₀ * qA W ^ A₀) • y := by
  classical
  have hR := GS.ringData_of_caseA_of_p9 W hcase hP9
  set c' : ZMod n := c - ((A.len c : ℕ) : ZMod n) with hc'
  have e1 : c - 2 - 1 = c' := by rw [hc', hlen]; push_cast; ring
  have e2 : c - 1 - 1 = c - 2 := by ring
  have e3 : c' + ((2 : ℕ) : ZMod n) = c - 1 := by rw [hc', hlen]; push_cast; ring
  have e4 : c' + ((1 : ℕ) : ZMod n) = c - 2 := by rw [hc', hlen]; push_cast; ring

  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hcase.1).finrank_eq, Module.finrank_self]
  have h9 := hP9 T₂ hT₂ hcase.2.1 hcase.2.2
  have hring := (h9.2.2 hK).1
  obtain ⟨wq, hwq⟩ := hring.2.2.2.2.1
  have hq : W.q = (wq : LetA O n) * qA W := by
    rw [hwq]
    congr 1
    funext j
    simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qA, lA]
  have hQ : W.Q = (wq : LetA O n) * qA W := by
    unfold LocWach.Q
    rw [hcase.2.1]
    simp [hq]
  have h5 := hP5 T₂ Mi' hi' hT₂ hJL
  have hφs : ∀ (a : LetA O n) (y : W.DD T₂), W.φD T₂ (a • y) = W.φA a • W.φD T₂ y := by
    intro a y
    rw [← algebraMap_smul W.EE a y, W.φD_smul, ← algebraMap_smul W.EE (W.φA a)]
    congr 1
    exact W.φE_ext a
  have hps1 : ps W 1 = W.φA (qA W) := by simp [ps]
  have hqmem : qA W ∈ W.AΔ := GS.qA_mem W
  have hp1mem : ps W 1 ∈ W.AΔ := GS.ps_mem W 1

  have hgen : ∀ x, Formalism.MainNotions.LiftingTheory.InNΔi W T₂ c' x →
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) := by
    intro x hx
    obtain ⟨hxΔ, hxl⟩ := hx
    have hxlet := TypesD.nl_letter W hxl
    have h1 := h5.1 (c - 2) x (by rw [e1]; exact hxl)
    rw [hM1] at h1
    have hl1 : (letE (c - 2) : LetA O n) • (W.Q ^ (w' + A.S) • W.φD T₂ x) = W.Q ^ (w' + A.S) • W.φD T₂ x := by
      rw [smul_comm]
      congr 1
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hletφ : (letE (c - 2) : LetA O n) • W.φD T₂ x = W.φD T₂ x := by
      have := TypesD.φD_letter W hxlet
      rwa [show c' + 1 = c - 2 by rw [← e4]; push_cast; ring] at this
    have hz1 : W.Q ^ (w' + A.S) • W.φD T₂ x ∈ W.Nl T₂ (c - 2) := ⟨_, h1, by simp [hletφ]⟩
    have h2 := h5.1 (c - 1) _ (by rw [e2]; exact hz1)
    rw [hM2, hφs] at h2
    set u : (LetA O n)ˣ := wq ^ A.η * (Units.map (W.φA : LetA O n →* LetA O n) wq) ^ (w' + A.S) with hu
    have hE : ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        ((u⁻¹ : (LetA O n)ˣ) : LetA O n) • (W.Q ^ A.η • (W.φA (W.Q ^ (w' + A.S)) • W.φD T₂ (W.φD T₂ x))) := by
      rw [smul_smul, smul_smul, pow_two, Module.End.mul_apply]
      congr 1
      rw [hQ, map_pow, map_mul, hps1, hu]
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe, mul_pow]
      have h1' : ((u⁻¹ : (LetA O n)ˣ) : LetA O n) * (u : LetA O n) = 1 := Units.inv_mul u
      rw [hu] at h1'
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe] at h1'
      linear_combination (-(qA W ^ A.η * W.φA (qA W) ^ (w' + A.S))) * h1'
    have hEN : (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x ∈ W.N T₂ := by
      rw [hE]; exact (W.N T₂).smul_mem _ h2
    have hlet2 := TypesD.φDpow_letter W hxlet 2
    rw [e3] at hlet2
    have hEl : (letE (c - 1) : LetA O n) • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x) =
        (qA W ^ A.η * ps W 1 ^ (w' + A.S)) • ((W.φD T₂) ^ 2) x := by
      rw [smul_comm, hlet2]
    have hamem : qA W ^ A.η * ps W 1 ^ (w' + A.S) ∈ W.AΔ :=
      W.AΔ.mul_mem (W.AΔ.pow_mem hqmem _) (W.AΔ.pow_mem hp1mem _)
    have hΔ : ∀ δ ∈ W.DelF, W.γD T₂ δ (((W.φD T₂) ^ 2) x) = ((W.φD T₂) ^ 2) x := by
      intro δ hδ
      rw [pow_two, Module.End.mul_apply, ← W.φγ_comm, ← W.φγ_comm, hxΔ.2 δ hδ]
    refine ⟨⟨hEN, fun δ hδ => ?_⟩, ⟨_, hEN, by simp [hlet2]⟩⟩
    rw [ArcLengthTwo.γD_smulA W T₂ δ, hΔ δ hδ]
    have ha' : W.γA δ (qA W ^ A.η * ps W 1 ^ (w' + A.S)) = qA W ^ A.η * ps W 1 ^ (w' + A.S) := hamem δ hδ
    rw [ha']

  obtain ⟨z₀, hz₀, hz₀eq⟩ := hlamγ
  have hPall : ∀ z ∈ Pp W T₂ c' 2,
      Formalism.MainNotions.LiftingTheory.InNΔi W T₂ (c - 1) ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z) := by
    intro z hz
    unfold Pp at hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨α, hα, x, hx, rfl⟩ := hz
      rw [smul_comm]
      exact inNΔi_smulA W T₂ (c - 1) hα (hgen x hx)
    | zero => rw [smul_zero]; exact ⟨(W.NΔ T₂).zero_mem, (W.Nl T₂ (c - 1)).zero_mem⟩
    | add z z' _ _ h h' => rw [smul_add]; exact inNΔi_add W T₂ (c - 1) h h'
    | neg z _ h => rw [smul_neg]; exact ⟨(W.NΔ T₂).neg_mem h.1, (W.Nl T₂ (c - 1)).neg_mem h.2⟩
  have hPz := hPall z₀ hz₀

  obtain ⟨r₀, -, r₀', hr₀', hrr₀, hγ₀⟩ := GS.psγ hR 0
  obtain ⟨r₁, hr₁, -, -, -, hγ₁⟩ := GS.psγ hR 1
  have hps0 : ps W 0 = qA W := by simp [ps]
  rw [hps0] at hγ₀
  have hγs : algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s =
      algebraMap (LetA O n) W.EE (r₀' ^ b₁ * (r₁ * ps W 1) ^ (w' + A.S)) := by
    have h := congrArg (W.γE W.gam) hs
    rw [map_mul, GS.γE_ι, GS.γE_ι, map_pow (W.γA W.gam), map_pow (W.γA W.gam), hγ₀, hγ₁] at h
    have hq' : qA W ^ b₁ = r₀' ^ b₁ * (r₀ * qA W) ^ b₁ := by
      rw [mul_pow, ← mul_assoc, ← mul_pow, mul_comm r₀' r₀, hrr₀, one_pow, one_mul]
    rw [hq', map_mul, mul_assoc, h, ← map_mul]

  obtain ⟨w₁, hw₁⟩ := hR.2.1
  have hJJ : W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) (A.M PD.p)) =
      (w₁ : LetA O n) ^ A.M PD.p * W.π₀ ^ A.M PD.p * qA W ^ ((PD.p - 1) * A.M PD.p) * ps W 1 ^ (2 * A.G₀) := by
    have hpk : Formalism.MainNotions.LiftingTheory.pk W 0 = qA W := by simp [Formalism.MainNotions.LiftingTheory.pk, Formalism.MainNotions.LiftingTheory.qp, qA, lA]
    simp only [Formalism.MainNotions.LiftingTheory.JJ, Finset.prod_range_one, hpk, map_mul, map_pow, hw₁, hps1]
    rw [pow_mul]
    try ring
  have hw₁mem : (w₁ : LetA O n) ∈ W.AΔ := by
    refine GS.quot_mem W (W.AΔ.mul_mem (GS.π₀_mem W) (W.AΔ.pow_mem hqmem _))
      (by rw [map_mul, map_pow]; exact (GS.isUnit_π₀ hR).mul ((GS.isUnit_qA hR).pow (PD.p - 1))) ?_
    have : W.π₀ * qA W ^ (PD.p - 1) * (w₁ : LetA O n) = W.φA W.π₀ := by rw [hw₁]; ring
    rw [this]
    exact GS.φpow_mem W 1 (GS.π₀_mem W)
  set N := (PD.p - 1) * A.M PD.p with hNdef
  set M := A.M PD.p with hMdef
  set V : LetA O n := (w₁ : LetA O n) ^ M * r₀' ^ b₁ * r₁ ^ (w' + A.S) with hV
  have hVmem : V ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem hw₁mem _)
    (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₀') _)) (W.AΔ.pow_mem (GS.mem_invariants_of_mem_S1 W hr₁) _)
  set C : LetA O n := W.π₀ ^ (M - 1) * qA W ^ (N - b₁ - A₀ - A.η) * ps W 1 ^ (2 * A.G₀) * V with hC
  have hCmem : C ∈ W.AΔ := W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.mul_mem (W.AΔ.pow_mem (GS.π₀_mem W) _)
    (W.AΔ.pow_mem hqmem _)) (W.AΔ.pow_mem hp1mem _)) hVmem
  refine ⟨C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀), inNΔi_smulA W T₂ (c - 1) hCmem hPz, ?_⟩
  have hL : W.γE W.gam s • (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M) • z₀) =
      (W.γE W.gam s * algebraMap (LetA O n) W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M))) • z₀ := by
    rw [← algebraMap_smul W.EE (W.φA (Formalism.MainNotions.LiftingTheory.JJ W 1 (2 * A.G₀) M)) z₀, smul_smul]
  have hRt : (W.π₀ * qA W ^ A₀) • (C • ((qA W ^ A.η * ps W 1 ^ (w' + A.S)) • z₀)) =
      algebraMap (LetA O n) W.EE (W.π₀ * qA W ^ A₀ * (C * (qA W ^ A.η * ps W 1 ^ (w' + A.S)))) • z₀ := by
    rw [smul_smul, smul_smul, algebraMap_smul, mul_assoc]
  rw [hz₀eq, hL, hRt, hJJ]
  congr 1
  have hπ : W.π₀ ^ M = W.π₀ * W.π₀ ^ (M - 1) := by
    rw [← pow_succ']; (try congr 1); (try omega)
  have hqN : qA W ^ N = qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁ := by
    rw [← pow_add, ← pow_add, ← pow_add]; (try congr 1); (try omega)
  rw [hπ, hqN]
  have : W.γE W.gam s * algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η * qA W ^ b₁) * ps W 1 ^ (2 * A.G₀)) =
      algebraMap (LetA O n) W.EE ((w₁ : LetA O n) ^ M * (W.π₀ * W.π₀ ^ (M - 1)) *
      (qA W ^ A₀ * qA W ^ (N - b₁ - A₀ - A.η) * qA W ^ A.η) * ps W 1 ^ (2 * A.G₀)) *
      (algebraMap (LetA O n) W.EE (qA W ^ b₁) * W.γE W.gam s) := by
    simp only [map_mul]; ring
  rw [this, hγs, ← map_mul]
  congr 1
  rw [hC, hV]
  ring

end Formalism.MainNotions.N.FrobeniusPowerSeries
