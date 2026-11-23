import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolMulPosLeConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntSmulLe
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ImportsBisTer
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.DegCnt.Unimod

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem exists_mul_mem {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤) (x : V) :
    ∃ N : ℤ, N ≠ 0 ∧ N • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.IntMulIntegral.main
  | exact _root_.GlobalTheory.IntMulIntegral.main
  | (apply _root_.GlobalTheory.IntMulIntegral.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntMulIntegral.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntMulIntegral.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntMulIntegral.main ..)

theorem exists_mul_le {A : Submodule (𝓞 K) V} (hA : Submodule.span K (A : Set V) = ⊤)
    {B : Submodule (𝓞 K) V} (hB : B.FG) : ∃ N : ℤ, N ≠ 0 ∧ ∀ x ∈ B, N • x ∈ A := by
  first
  | exact @_root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le
  | exact _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le
  | (apply _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerMultipleIntegral.exists_int_smul_le ..)

theorem finite_between {Λ : Submodule (𝓞 K) V} (hΛ : Λ.FG) {a b : ℤ} (ha : a ≠ 0) (hb : b ≠ 0) :
    {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ}.Finite := by
  haveI : Module.Finite (𝓞 K) Λ := Module.Finite.iff_fg.2 hΛ
  haveI : Module.Finite ℤ Λ := Module.Finite.trans (𝓞 K) Λ
  let P : Submodule ℤ Λ := LinearMap.range (LinearMap.lsmul ℤ Λ (b * a))
  haveI : Finite (Λ ⧸ P) := by
    refine Module.finite_of_fg_torsion _ ?_
    intro q
    obtain ⟨x, rfl⟩ := P.mkQ_surjective q
    refine ⟨⟨b * a, mem_nonZeroDivisors_of_ne_zero (mul_ne_zero hb ha)⟩, ?_⟩
    change (b * a) • P.mkQ x = 0
    rw [← map_smul]
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  let f : Submodule (𝓞 K) V → Set (Λ ⧸ P) := fun M =>
    {q | ∃ x ∈ M, ∃ h : b • x ∈ Λ, P.mkQ ⟨b • x, h⟩ = q}
  have key : ∀ M M' : Submodule (𝓞 K) V, (∀ x ∈ M, b • x ∈ Λ) → (∀ x ∈ Λ, a • x ∈ M') →
      f M = f M' → M ≤ M' := by
    intro M M' hM hM' e x hx
    have : P.mkQ ⟨b • x, hM x hx⟩ ∈ f M' := e ▸ ⟨x, hx, hM x hx, rfl⟩
    obtain ⟨y, hy, hy', h⟩ := this
    obtain ⟨z, hz⟩ := (Submodule.Quotient.eq _).1 h
    have hz' : (b * a) • (z : V) = b • y - b • x := congrArg Subtype.val hz
    have h2 : (b : K) • (a • (z : V)) = (b : K) • (y - x) := by
      rw [Int.cast_smul_eq_zsmul, Int.cast_smul_eq_zsmul, ← mul_smul, hz', smul_sub]
    have h3 := smul_right_injective V (by exact_mod_cast hb : (b : K) ≠ 0) h2
    have h4 : x = y - a • (z : V) := by
      have h3' : a • (z : V) = y - x := h3
      rw [h3']; abel
    rw [h4]
    exact M'.sub_mem hy (hM' _ z.2)
  refine Set.Finite.of_finite_image (f := f) (Set.toFinite _) ?_
  intro M hM M' hM' e
  exact le_antisymm (key M M' hM.2 hM'.1 e) (key M' M hM'.2 hM.1 e.symm)

theorem mem_smul_iff (g : V ≃ₗ[K] V) (Λ : Submodule (𝓞 K) V) (x : V) :
    x ∈ g • Λ ↔ g⁻¹ x ∈ Λ := by
  rw [Submodule.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · intro h
    exact ⟨_, h, by simp⟩

theorem isLattice_smul (g : V ≃ₗ[K] V) {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) :
    Submodule.IsLattice K (g • Λ) := by
  refine ⟨?_, ?_⟩
  · exact hΛ.fg.map _
  · rw [eq_top_iff]
    intro x _
    obtain ⟨N, hN, h⟩ := exists_mul_mem hΛ.span_eq_top (g⁻¹ x)
    have h1 : N • x ∈ g • Λ := by rw [mem_smul_iff, map_zsmul]; exact h
    have h2 : x = (N : K)⁻¹ • (N • x) := by
      rw [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hN), one_smul]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem relIndex_ne_zero (G : Subgroup (V ≃ₗ[K] V)) {Λ Λ' : Submodule (𝓞 K) V}
    (hΛ : Submodule.IsLattice K Λ) (hΛ' : Submodule.IsLattice K Λ') :
    (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex
      (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 := by
  obtain ⟨a, ha, h₁⟩ := exists_mul_le hΛ.span_eq_top hΛ'.fg
  obtain ⟨b, hb, h₂⟩ := exists_mul_le hΛ'.span_eq_top hΛ.fg
  set H := G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ' with hH
  have e : (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex H = (MulAction.stabilizer H Λ).index := by
    rw [Subgroup.relIndex]
    congr 1
    ext g
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨g.2.1, h⟩⟩
  rw [e, MulAction.index_stabilizer]
  refine Set.ncard_ne_zero_of_mem (MulAction.mem_orbit_self Λ) ?_
  refine (finite_between hΛ'.fg ha hb).subset ?_
  rintro _ ⟨g, rfl⟩
  have hg : (g : V ≃ₗ[K] V) • Λ' = Λ' := g.2.2
  have hg' : ∀ x, (g : V ≃ₗ[K] V)⁻¹ x ∈ Λ' ↔ x ∈ Λ' := fun x => by rw [← mem_smul_iff, hg]
  refine ⟨fun x hx => ?_, fun x hx => ?_⟩
  · change a • x ∈ (g : V ≃ₗ[K] V) • Λ
    rw [mem_smul_iff, map_zsmul]
    exact h₁ _ ((hg' x).2 hx)
  · have hx' : x ∈ (g : V ≃ₗ[K] V) • Λ := hx
    rw [mem_smul_iff] at hx'
    rw [← hg', map_zsmul]
    exact h₂ _ hx'

theorem exists_den {s : V ≃ₗ[K] V} {n : ℕ} (hs : ((s : V →ₗ[K] V) - 1) ^ n = 0)
    {Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) :
    ∃ N : ℤ, N ≠ 0 ∧ ∀ m : ℕ, ∀ x ∈ Λ, N • (s ^ m) x ∈ Λ := by
  let u : V →ₗ[K] V := (s : V →ₗ[K] V) - 1
  let B : Submodule (𝓞 K) V := ⨆ i : Fin (n + 1), Λ.map ((u ^ (i : ℕ)).restrictScalars (𝓞 K))
  have hB : B.FG := Submodule.fg_iSup _ fun i => hΛ.fg.map _
  have hm : ∀ i : ℕ, ∀ x ∈ Λ, (u ^ i) x ∈ B := by
    intro i x hx
    by_cases hi : i < n + 1
    · exact Submodule.mem_iSup_of_mem (⟨i, hi⟩ : Fin (n + 1)) ⟨x, hx, rfl⟩
    · rw [pow_eq_zero_of_le (by omega : n ≤ i) hs]
      exact B.zero_mem
  have hu : B ≤ B.comap (u.restrictScalars (𝓞 K)) := by
    refine iSup_le fun i => ?_
    rintro _ ⟨x, hx, rfl⟩
    have := hm (i + 1) x hx
    rw [pow_succ'] at this
    exact this
  have hsB : ∀ x ∈ B, s x ∈ B := by
    intro x hx
    have h1 : u x ∈ B := hu hx
    have : s x = u x + x := by simp [u]
    rw [this]
    exact B.add_mem h1 hx
  have hp : ∀ m : ℕ, ∀ x ∈ Λ, (s ^ m) x ∈ B := by
    intro m x hx
    induction m with
    | zero => simpa using hm 0 x hx
    | succ m ih => rw [pow_succ']; exact hsB _ ih
  obtain ⟨N, hN, h⟩ := exists_mul_le hΛ.span_eq_top hB
  exact ⟨N, hN, fun m x hx => h _ (hp m x hx)⟩

theorem inf_stab_smul {Γ X : Type} [Group Γ] [MulAction Γ X] (G : Subgroup Γ) {s : Γ} (hs : s ∈ G) (x : X) :
    G ⊓ MulAction.stabilizer Γ (s • x) = MulAut.conj s • (G ⊓ MulAction.stabilizer Γ x) := by
  ext g
  rw [Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp only [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_inv_apply]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨G.mul_mem (G.mul_mem (G.inv_mem hs) h1) hs, ?_⟩
    rw [mul_smul, mul_smul, h2, inv_smul_smul]
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have := G.mul_mem (G.mul_mem hs h1) (G.inv_mem hs)
      simpa [mul_assoc] using this
    · rw [mul_smul, mul_smul, inv_smul_eq_iff] at h2
      exact h2

theorem invVol_smul : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (G : Subgroup (V ≃ₗ[K] V)) (n : ℕ), (∀ s ∈ G, ((s : V →ₗ[K] V) - 1) ^ n = 0) → ∀ Λ Λ' : Submodule (𝓞 K) V, Submodule.IsLattice K Λ → Submodule.IsLattice K Λ' → (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ).relIndex (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') ≠ 0 ∧ ∀ s ∈ G, GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) (s • Λ)) = GlobalTheory.HL.invVol (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ') (G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ) := by
  intro K V _ _ _ _ _ _ _ G n hG Λ Λ' hΛ hΛ'
  refine ⟨relIndex_ne_zero G hΛ hΛ', fun s hs => ?_⟩
  let S : Submodule (𝓞 K) V → Subgroup (V ≃ₗ[K] V) := fun M =>
    G ⊓ MulAction.stabilizer (V ≃ₗ[K] V) M
  have main : ∀ A B C : Submodule (𝓞 K) V, Submodule.IsLattice K A → Submodule.IsLattice K B →
      Submodule.IsLattice K C → _ := fun A B C hA hB hC =>
    GlobalTheory.HL.invVol_mul_pos_le_conj (S A) (S B) (S C) (relIndex_ne_zero G hA hB)
      (relIndex_ne_zero G hB hA) (relIndex_ne_zero G hA hC) (relIndex_ne_zero G hC hA)
  set d : ℝ := GlobalTheory.HL.invVol (S Λ) (S (s • Λ)) with hd
  have hdpos : 0 < d := (main Λ Λ (s • Λ) hΛ hΛ (isLattice_smul s hΛ)).2.1
  have hpow : ∀ m : ℕ, GlobalTheory.HL.invVol (S Λ) (S (s ^ m • Λ)) = d ^ m := by
    intro m
    induction m with
    | zero => simp [GlobalTheory.HL.invVol]
    | succ m ih =>
      have h1 := (main Λ (s • Λ) (s ^ (m + 1) • Λ) hΛ (isLattice_smul _ hΛ) (isLattice_smul _ hΛ)).1
      have h2 := (main Λ Λ (s ^ m • Λ) hΛ hΛ (isLattice_smul _ hΛ)).2.2.2 s
      have e1 : MulAut.conj s • S Λ = S (s • Λ) := (inf_stab_smul G hs Λ).symm
      have e2 : MulAut.conj s • S (s ^ m • Λ) = S (s ^ (m + 1) • Λ) := by
        rw [pow_succ', mul_smul]
        exact (inf_stab_smul G hs _).symm
      rw [e1, e2, ih] at h2
      rw [h1, h2, pow_succ']
  obtain ⟨b, hb, h₂⟩ := exists_den (hG s hs) hΛ
  obtain ⟨a, ha, h₁⟩ := exists_den (hG s⁻¹ (G.inv_mem hs)) hΛ
  have hfin := finite_between hΛ.fg ha hb
  have hmaps : ∀ m : ℕ, s ^ m • Λ ∈
      {M : Submodule (𝓞 K) V | (∀ x ∈ Λ, a • x ∈ M) ∧ ∀ x ∈ M, b • x ∈ Λ} := by
    intro m
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [mem_smul_iff, map_zsmul, ← inv_pow]
      exact h₁ m x hx
    · rw [mem_smul_iff] at hx
      simpa using h₂ m _ hx
  obtain ⟨i, j, hij, e⟩ := hfin.exists_lt_map_eq_of_forall_mem hmaps
  have hd1 : d = 1 := by
    have h : d ^ i = d ^ j := by rw [← hpow, ← hpow, e]
    by_contra hne
    exact hij.ne (pow_right_injective₀ hdpos hne h)
  have h := (main Λ' Λ (s • Λ) hΛ' hΛ (isLattice_smul s hΛ)).1
  rw [← hd, hd1, mul_one] at h
  exact h

end GlobalTheory.DegCnt.Unimod
