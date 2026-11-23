import Formalism.CoboundaryTransfers.StatementAPI
import Formalism.CoboundaryTransfers.GammaStableTransfers.MemCoboundariesOfIsOneCoboundary
import Formalism.FrobeniusContraction.FrobeniusContractionProofs.LenBound

noncomputable section

namespace Formalism.CoboundaryTransfers

section SlopeTestRemainingChoices

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {B : Base O A} {M : ℕ}
  {D : Type} [AddCommGroup D] [Module A D] [Module O D] [IsScalarTower O A D]

private theorem WachMod.mem_cocycles_units_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.Z1 ↔ W.d1 pr.1 pr.2 = 0 := by
  simp [WachMod.Z1, WachMod.d1, sub_eq_add_neg]

private theorem WachMod.WachMod_mem_B1_iff (W : WachMod B M D) (pr : D × D) :
    pr ∈ W.B1 ↔ ∃ x, (W.φ x - x, W.γ x - x) = pr := by
  simp [WachMod.B1]

end SlopeTestRemainingChoices

theorem homPreservesCochains_holds : HomMaps := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F
  have hQ : ∀ y, W.QInv y → W'.QInv (F.f y) := fun y hy => by
    show B.Q ^ M • F.f y ∈ W'.N
    rw [← map_smul]
    exact F.N_le _ hy
  have hX : ∀ z, W.XN z → W'.XN (F.f z) := by
    rintro z ⟨n, hn, rfl⟩
    exact ⟨F.f n, F.N_le n hn, map_smul _ _ _⟩
  have hC1 : ∀ y z, W.C1 y z → W'.C1 (F.f y) (F.f z) := fun y z h => ⟨hQ y h.1, hX z h.2⟩
  have hd : ∀ y z, F.f (W.d1 y z) = W'.d1 (F.f y) (F.f z) := fun y z => by
    simp only [WachMod.d1, map_sub, F.φ_comm, F.γ_comm]
  have hZ1 : W.Z1.map F.f2 ≤ W'.Z1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    refine (WachMod.mem_cocycles_units_iff W' _).mpr ?_
    show W'.d1 (F.f pr.1) (F.f pr.2) = 0
    rw [← hd, (WachMod.mem_cocycles_units_iff W pr).mp hpr, map_zero]
  have hB1 : W.B1.map F.f2 ≤ W'.B1 := by
    rintro _ ⟨pr, hpr, rfl⟩
    obtain ⟨x, rfl⟩ := (WachMod.WachMod_mem_B1_iff W pr).mp hpr
    exact (WachMod.WachMod_mem_B1_iff W' _).mpr ⟨F.f x, by simp [Hom.f2, F.φ_comm, F.γ_comm]⟩
  have hZf : W.Zf.map F.f2 ≤ W'.Zf := by
    refine Submodule.map_le_iff_le_comap.mpr ?_
    rw [WachMod.Zf]
    refine sup_le ?_ ?_
    · rw [Submodule.span_le]
      rintro pr ⟨hz, a, b, hb, hint⟩
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      apply Submodule.mem_sup_left
      apply Submodule.subset_span
      refine ⟨hZ1 ⟨pr, hz, rfl⟩, a, F.f2 b, hB1 ⟨b, hb, rfl⟩, ?_⟩
      obtain ⟨⟨k, hk⟩, hxn⟩ := hint
      have e : (B.p ^ a : ℕ) • F.f2 pr + F.f2 b = F.f2 ((B.p ^ a : ℕ) • pr + b) := by
        rw [map_add, map_nsmul]
      rw [e]
      refine ⟨⟨k, ?_⟩, hX _ hxn⟩
      show B.Q ^ k • F.f (((B.p ^ a : ℕ) • pr + b).1) ∈ W'.N
      rw [← map_smul]
      exact F.N_le _ hk
    · intro pr hpr
      refine Submodule.mem_comap.mpr ?_
      rw [WachMod.Zf]
      exact Submodule.mem_sup_right (hB1 ⟨pr, hpr, rfl⟩)
  refine ⟨hQ, hX, ?_, hd, ?_, ?_, ?_, hZ1, hB1, hZf⟩
  · rintro ω ⟨y, hy, rfl⟩
    exact ⟨F.f y, hQ y hy, map_smul _ _ _⟩
  · rintro y z ⟨h1, h2⟩
    exact ⟨hC1 y z h1, by rw [← hd, h2, map_zero]⟩
  · rintro y z ⟨x, hx, rfl, rfl⟩
    exact ⟨F.f x, F.N_le x hx, by rw [map_sub, F.φ_comm], by rw [map_sub, F.γ_comm]⟩
  · rintro ω ⟨y, z, h, rfl⟩
    exact ⟨F.f y, F.f z, hC1 y z h, hd y z⟩

theorem gammaStableOfGammaQUnit_holds : GammaQNOf := by
  intro O A _ _ _ B M D _ _ _ _ N γ hG hQ hγ hN y hy
  obtain ⟨v, hvu, ⟨t, hvt⟩, hγQ⟩ := hG
  have hit : ∀ (k : ℕ) (x : D), (fun x : D => B.Q • x)^[k] x = B.Q ^ k • x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih => intro x; rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]
  have hQM : Function.Bijective (fun x : D => B.Q ^ M • x) := by
    have h := hQ.iterate M
    rwa [show (fun x : D => B.Q • x)^[M] = fun x => B.Q ^ M • x from funext (hit M)] at h
  have hvk : ∀ k : ℕ, ∃ s : A, v ^ k = 1 + B.X * s := by
    intro k
    induction k with
    | zero => exact ⟨0, by simp⟩
    | succ k ih =>
      obtain ⟨s, hs⟩ := ih
      exact ⟨s + t + B.X * s * t, by rw [pow_succ, hs, hvt]; ring⟩
  obtain ⟨s, hs⟩ := hvk M
  have hγn : γ (B.Q ^ M • y) = v ^ M • B.Q ^ M • γ y := by
    rw [hγ, map_pow, hγQ, mul_pow, mul_smul]
  obtain ⟨n', hn'N, hn'⟩ := hN _ hy
  obtain ⟨u, hu⟩ := hvu.pow M
  have hQγ : B.Q ^ M • γ y ∈ N := by
    have h1 : γ (B.Q ^ M • y) ∈ N := by
      have e : γ (B.Q ^ M • y) = B.Q ^ M • y + B.X • n' := by rw [← hn']; abel
      rw [e]
      exact N.add_mem hy (N.smul_mem _ hn'N)
    have h2 : B.Q ^ M • γ y = ((u⁻¹ : Aˣ) : A) • γ (B.Q ^ M • y) := by
      rw [hγn, ← hu, smul_smul, Units.inv_mul, one_smul]
    rw [h2]
    exact N.smul_mem _ h1
  have hmN : n' - s • B.Q ^ M • γ y ∈ N := N.sub_mem hn'N (N.smul_mem _ hQγ)
  have hkey : B.Q ^ M • (γ y - y) = B.X • (n' - s • B.Q ^ M • γ y) := by
    have e : (1 + B.X * s) • B.Q ^ M • γ y - B.Q ^ M • y = B.X • n' := by
      rw [← hs, ← hγn]
      exact hn'
    rw [smul_sub, smul_sub, ← e, add_smul, one_smul, mul_smul]
    abel
  obtain ⟨y', hy'⟩ := hQM.2 (n' - s • B.Q ^ M • γ y)
  simp only at hy'
  refine ⟨y', by rw [hy']; exact hmN, ?_⟩
  apply hQM.1
  show B.Q ^ M • (γ y - y) = B.Q ^ M • (B.X • y')
  rw [hkey, smul_comm (B.Q ^ M) B.X y', hy']

theorem cokernelLengthBound_holds : ColBound := by
  intro O A _ _ _ B M D D' _ _ _ _ _ _ _ _ W W' F g e hfin hlift
  obtain ⟨s, hs, hspan⟩ := hfin
  show Module.length O (↥W'.Zf ⧸ F.ImF.comap W'.Zf.subtype) ≤ _
  first
    | exact Formalism.WachCohomologyFacts.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact Formalism.WachCohomologyFacts.PLenBound.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift
    | exact _root_.quotientLengthBound_holds O (D' × D') B.p g e W'.Zf W'.B1 F.ImF s hs hspan le_sup_right hlift

theorem finiteClassesLift_holds : LiftHf := by
  intro O A _ _ _ B M D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ S H₁ H₂ _ _ _ _ cl₁ cl₂ Hf₁ Hf₂ g eW c
    hnat hcl₁ hint hlifts κ hκ
  obtain ⟨pr, hcoc, hpr⟩ := hint.2 κ hκ
  obtain ⟨y₁, z₁, hcoc₁, hy, hz⟩ := hlifts _ _ hcoc
  have hmem : ((y₁, z₁) : D₁ × D₁) ∈ W₁.Z1 := (WachMod.mem_cocycles_units_iff W₁ _).mpr hcoc₁.2
  refine ⟨cl₁ ⟨(y₁, z₁), hmem⟩, hcl₁ _ hcoc₁, ?_⟩
  have hpr' : ((c • pr : W₂.Z1) : D₂ × D₂) = S.π.f2 (⟨(y₁, z₁), hmem⟩ : W₁.Z1) := by
    show c • (pr : D₂ × D₂) = (S.π.f y₁, S.π.f z₁)
    rw [hy, hz]
    rfl
  rw [hnat _ _ hpr', map_smul, hpr, smul_smul, mul_comm]

end Formalism.CoboundaryTransfers
