import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.PchainDNAlt

noncomputable section
open Classical

namespace Formalism.MainNotions.N.Pv.LocalLengthBound

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc PowerSeries TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

section Core

variable (W : LocWach PD LL O v n)

theorem qp_mem_AΔ (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W) : Formalism.MainNotions.LiftingTheory.qp W ∈ W.AΔ :=
  W.AΔ.add_mem hR.1 (W.AΔ.natCast_mem _)

theorem inI_qpphi [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    (T : LocLat G Qp LL O) (h3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    {c : ZMod n} {kB : ℕ} (hM : ∀ z ∈ W.Nl T (c - 1), W.Q ^ kB • W.φD T z ∈ W.N T)
    {x : W.DD T} (hxN : x ∈ W.N T) (hxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T (c - 1) x) (pad : ℕ) :
    Formalism.MainNotions.CrystallineLiftingInputs.InI W T c (((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x)) := by
  obtain ⟨hN, -⟩ := cmp_qpphi W T hs hR h3 hM hxN hxD.1
  set z := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T x) with hz
  have hzN : z ∈ W.N T := by
    rw [hz, ← algebraMap_smul (LetA O n)]; exact (W.N T).smul_mem _ hN
  have hzΔ : ∀ δ ∈ W.DelF, W.γD T δ z = z := by
    intro δ hδ
    rw [hz, map_smul, Formalism.MainNotions.UnusedSlot80.SatW.γD_smulA', ← W.φγ_comm, hxD.2 δ hδ,
      (W.AΔ.pow_mem (qp_mem_AΔ W hR) kB) δ hδ]
  have hzl : (letE c : LetA O n) • z = z := by
    rw [hz, osmul_comm W T, aself_comm W T, letter_phi W T c hxD.1]
  refine ⟨⟨hzl, hzΔ⟩, ⟨0, 0, by simpa using hzN⟩, ?_⟩
  obtain ⟨x', hx', he⟩ := hmod.2 z ⟨hzN, hzΔ⟩
  exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact he⟩

theorem exists_inI_inPN_pow_smul_sub_map [IsDomain O] (hs : W.s = 1) (hR : Formalism.MainNotions.UnusedSlot80.ToolsR.RingP W)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L)
    (h3₁ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₁) (h3₂ : Formalism.MainNotions.DeltaInvariantLattices.p3 W T₂)
    (hmod₁ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₁ W.π₀) (hmod₂ : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T₂ W.π₀)
    {c : ZMod n} {kB : ℕ}
    (hM₁ : ∀ z ∈ W.Nl T₁ (c - 1), W.Q ^ kB • W.φD T₁ z ∈ W.N T₁)
    (hM₂ : ∀ z ∈ W.Nl T₂ (c - 1), W.Q ^ kB • W.φD T₂ z ∈ W.N T₂)
    {y : W.DD T₂} (hy : y ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c) {d1 d2 d3 : T₂.V ⊗[Qp] B}
    {s₁ s₂ bb hh e pad : ℕ} {k : ℤ}
    (h1 : (PD.p : LL) ^ s₁ • Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ y =
      (PD.p : LL) ^ kB • φVB PD (LL := LL) (V := T₂.V) d1)
    (h2 : (PD.p : LL) ^ bb • d1 = φVB PD (LL := LL) (V := T₂.V) d2)
    (h3 : (PD.p : LL) ^ s₂ • d2 = (PD.p : LL) ^ hh • φVB PD (LL := LL) (V := T₂.V) d3)
    (hG : (PD.p : LL) ^ k • φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) ∈
      Formalism.MainNotions.CrystallineLiftingInputs.DlatImg W F (c - 1))
    (hexp : (e : ℤ) + hh = pad + k + bb) :
    ∃ x : W.DD T₁, Formalism.MainNotions.CrystallineLiftingInputs.InI W T₁ c x ∧
      Formalism.MainNotions.CrystallineLiftingInputs.InPN W T₂ 1 (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) := by
  have hp : (PD.p : LL) ≠ 0 := Formalism.MainNotions.UnusedSlot80.ArcF.p_ne_zero W
  obtain ⟨n', hn'N, hmN, hn'D, hcmp⟩ := hG
  set x := ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₁ n') with hxdef
  refine ⟨x, inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad, ?_⟩
  have hyN : y ∈ W.N T₂ := NDl_N W T₂ hy
  have hyl : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c y := NDl_DL W T₂ hy

  have hml : (letE (c - 1) : LetA O n) • W.map F n' = W.map F n' := by
    rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hn'D.1]
  obtain ⟨hqN, hqc⟩ := cmp_qpphi W T₂ hs hR h3₂ hM₂ hmN hml
  have hFx : W.map F x = ((PD.p : O) ^ pad) • (Formalism.MainNotions.LiftingTheory.qp W ^ kB • W.φD T₂ (W.map F n')) := by
    rw [hxdef, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulO, Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, W.map_φ]
  have hFxN : W.map F x ∈ W.N T₂ := by
    rw [hFx, ← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hqN
  have hxI := inI_qpphi W hs hR T₁ h3₁ hmod₁ hM₁ hn'N hn'D pad
  have hFxD : Formalism.MainNotions.CrystallineLiftingInputs.DL W T₂ c (W.map F x) := by
    refine ⟨by rw [← Formalism.MainNotions.UnusedSlot80.ArcC.map_smulA, hxI.1.1], fun δ hδ => ?_⟩
    rw [← W.map_γ, hxI.1.2 δ hδ]
  have hpyN : ((PD.p : O) ^ (e + s₁ + s₂)) • y ∈ W.N T₂ := by
    rw [← algebraMap_smul (LetA O n)]; exact (W.N T₂).smul_mem _ hyN
  have hzmem : ((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x ∈ Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c :=
    (Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).sub_mem ((Formalism.MainNotions.RamifiedCoefficientChains.S9.NDl W T₂ c).smul_mem _ hy) ⟨hFxN, hFxD⟩
  refine ker_NDl W T₂ c h3₂ hmod₂ hR hzmem ?_

  have hsub : Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y - W.map F x) =
      Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (((PD.p : O) ^ (e + s₁ + s₂)) • y) - Formalism.MainNotions.ArcLiftingSetup.cmpD W T₂ (W.map F x) := by
    have := cmpD_add W T₂ ((W.N T₂).sub_mem hpyN hFxN) hFxN
    rw [sub_add_cancel] at this
    rw [this, add_sub_cancel_right]
  rw [hsub, sub_eq_zero, cmpD_osmul W T₂ _ hyN, hFx, cmpD_osmul W T₂ _ hqN, hqc,
    Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hmN, ← hcmp, map_pow, map_pow, map_natCast]

  have hsc : (PD.p : LL) ^ e * (PD.p : LL) ^ hh = (PD.p : LL) ^ bb * ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) := by
    rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ hp,
      ← zpow_add₀ hp, ← zpow_add₀ hp]
    congr 1
    omega
  have key : (PD.p : LL) ^ (e + s₂) • d1 = ((PD.p : LL) ^ pad * (PD.p : LL) ^ k) •
      φVB PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) d3) := by
    apply smul_right_injective _ (pow_ne_zero bb hp)
    simp only
    rw [smul_comm, h2, pow_add, mul_smul, ← map_smul, h3, map_smul, smul_smul, smul_smul, hsc]
  rw [pow_add, pow_add, mul_smul, mul_smul, smul_comm ((PD.p : LL) ^ s₁), h1, ← mul_smul,
    ← pow_add, smul_comm, ← map_smul, key, map_smul, map_smul, smul_smul]
  simp only [smul_smul]
  congr 1
  ring

end Core

end Formalism.MainNotions.N.Pv.LocalLengthBound
