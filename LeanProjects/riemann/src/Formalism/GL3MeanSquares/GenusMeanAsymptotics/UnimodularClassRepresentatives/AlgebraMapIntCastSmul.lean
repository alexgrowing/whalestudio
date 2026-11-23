import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.LocalDensityRatio
import Formalism.HermitianLattices.HermitianLatticesProofs.LocBasic
import Formalism.HermitianLattices.HermitianLatticesProofs.TraceReal

open NumberField Module

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.LocF

variable {K F : Type} [Field K] [NumberField K] [Field F] [NumberField F] [Algebra F K]

section Gen

variable {W : Type} [AddCommGroup W] [Module (𝓞 K) W]

theorem mem_closure_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (s : 𝓞 K) :
    s ∈ Submonoid.closure {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s} ↔
      ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s := by
  constructor
  · intro hs
    induction hs using Submonoid.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨1, (Ideal.ne_top_iff_one 𝔭).mp hp.ne_top, map_one _⟩
    | mul a b _ _ iha ihb =>
      obtain ⟨t, ht, rfl⟩ := iha
      obtain ⟨u, hu, rfl⟩ := ihb
      exact ⟨t * u, fun h => (hp.mem_or_mem h).elim ht hu, map_mul _ _ _⟩
  · intro hs
    exact Submonoid.subset_closure hs

theorem mem_locF_iff {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsPrime) (L : Submodule (𝓞 K) W) (x : W) :
    x ∈ locF 𝔭 L ↔ ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t • x ∈ L := by
  unfold locF
  rw [Formalism.HermitianLatticesTheory.locBasic_mem_locS]
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨t, ht, rfl⟩ := (mem_closure_iff hp s).mp hs
    exact ⟨t, ht, hx⟩
  · rintro ⟨t, ht, hx⟩
    exact ⟨_, (mem_closure_iff hp _).mpr ⟨t, ht, rfl⟩, hx⟩

theorem le_locF (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) : L ≤ locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_le_locS _ L

theorem locF_mono (𝔭 : Ideal (𝓞 F)) {L M : Submodule (𝓞 K) W} (h : L ≤ M) :
    locF 𝔭 L ≤ locF 𝔭 M :=
  Formalism.HermitianLatticesTheory.locBasic_locS_mono _ h

theorem locF_idem (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) W) :
    locF 𝔭 (locF 𝔭 L) = locF 𝔭 L :=
  Formalism.HermitianLatticesTheory.locBasic_locS_idem _ L

theorem iInf_locF (L : Submodule (𝓞 K) W) :
    (⨅ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 L) = L := by
  apply le_antisymm
  · intro x hx
    by_contra hxL
    let I : Ideal (𝓞 F) := Ideal.comap (algebraMap (𝓞 F) (𝓞 K))
      (Submodule.comap (LinearMap.toSpanSingleton (𝓞 K) W x) L)
    have hmem : ∀ r : 𝓞 F, r ∈ I ↔ algebraMap (𝓞 F) (𝓞 K) r • x ∈ L := by
      intro r
      simp [I]
    have hI : I ≠ ⊤ := by
      intro h
      apply hxL
      have h1 : (1 : 𝓞 F) ∈ I := h ▸ Submodule.mem_top
      simpa using (hmem 1).mp h1
    obtain ⟨p, hp, hIp⟩ := Ideal.exists_le_maximal I hI
    have h2 := (Submodule.mem_iInf _).mp hx ⟨p, hp⟩
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff hp.isPrime L x).mp h2
    exact ht (hIp ((hmem t).mpr htx))
  · exact le_iInf fun 𝔭 => le_locF 𝔭.1 L

end Gen

theorem exists_prime_to_part {c : 𝓞 F} (hc : c ≠ 0) {𝔭 : Ideal (𝓞 F)} (hp : 𝔭.IsMaximal) :
    ∃ t : 𝓞 F, t ∉ 𝔭 ∧ ∀ 𝔮 : Ideal (𝓞 F), 𝔮.IsMaximal → 𝔮 ≠ 𝔭 → ∃ u : 𝓞 F, u ∉ 𝔮 ∧ c ∣ u * t := by
  have hc' : Ideal.span {c} ≠ (0 : Ideal (𝓞 F)) := by
    simpa using hc
  have hu : ¬ IsUnit 𝔭 := by
    rw [Ideal.isUnit_iff]
    exact hp.ne_top
  obtain ⟨𝔟, hb, hnd⟩ := (FiniteMultiplicity.of_not_isUnit hu hc').exists_eq_pow_mul_and_not_dvd
  rw [Ideal.dvd_iff_le] at hnd
  obtain ⟨t, htb, htp⟩ := SetLike.not_le_iff_exists.mp hnd
  refine ⟨t, htp, fun 𝔮 hq hne => ?_⟩
  have h1 : ¬ 𝔭 ^ multiplicity 𝔭 (Ideal.span {c}) ≤ 𝔮 := by
    intro hle
    exact hne (hp.eq_of_le hq.ne_top (hq.isPrime.le_of_pow_le hle)).symm
  obtain ⟨u, hu1, hu2⟩ := SetLike.not_le_iff_exists.mp h1
  refine ⟨u, hu2, ?_⟩
  rw [← Ideal.mem_span_singleton, hb]
  exact Ideal.mul_mem_mul hu1 htb

section Lat

variable [StarRing K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem exists_zsmul_le {A B : Submodule (𝓞 K) V} (hA : Submodule.IsLattice K A)
    (hB : Submodule.IsLattice K B) : ∃ n : ℤ, n ≠ 0 ∧ ∀ x ∈ A, n • x ∈ B := by
  obtain ⟨S, hS⟩ := hA.fg
  choose n hn hnx using fun x : V => Formalism.HermitianLatticesTheory.traceReal_mult B hB x
  refine ⟨∏ x ∈ S, n x, Finset.prod_ne_zero_iff.mpr fun x _ => hn x, fun x hx => ?_⟩
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem n hy
    rw [hm, mul_comm, mul_smul]
    exact zsmul_mem (hnx y) m
  | zero => rw [smul_zero]; exact B.zero_mem
  | add y z _ _ hy hz => rw [smul_add]; exact B.add_mem hy hz
  | smul a y _ hy => rw [smul_comm]; exact B.smul_mem a hy

theorem algebraMap_intCast_smul (n : ℤ) (x : V) :
    algebraMap (𝓞 F) (𝓞 K) (n : 𝓞 F) • x = n • x := by
  rw [map_intCast, Int.cast_smul_eq_zsmul]

theorem patch {L₀ : Submodule (𝓞 K) V} (hL₀ : Submodule.IsLattice K L₀)
    (s : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (B : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Submodule (𝓞 K) V)
    (hB : ∀ 𝔭, Submodule.IsLattice K (B 𝔭)) (hBs : ∀ 𝔭 ∉ s, B 𝔭 = L₀) :
    Submodule.IsLattice K (⨅ 𝔭, locF 𝔭.1 (B 𝔭)) ∧
      ∀ 𝔭, locF 𝔭.1 (⨅ 𝔮, locF 𝔮.1 (B 𝔮)) = locF 𝔭.1 (B 𝔭) := by
  classical
  choose n₁ hn₁ hn₁x using fun 𝔭 => exists_zsmul_le (hB 𝔭) hL₀
  choose n₂ hn₂ hn₂x using fun 𝔭 => exists_zsmul_le hL₀ (hB 𝔭)
  obtain ⟨N, hN, hN1, hN2⟩ : ∃ N : ℤ, N ≠ 0 ∧ (∀ 𝔭, ∀ x ∈ B 𝔭, N • x ∈ L₀) ∧
      ∀ 𝔭, ∀ x ∈ L₀, N • x ∈ B 𝔭 := by
    refine ⟨∏ 𝔭 ∈ s, (n₁ 𝔭 * n₂ 𝔭),
      Finset.prod_ne_zero_iff.mpr fun 𝔭 _ => mul_ne_zero (hn₁ 𝔭) (hn₂ 𝔭), ?_, ?_⟩
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₂ 𝔭 * m) * n₁ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₁x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭] at hx
        exact zsmul_mem hx _
    · intro 𝔭 x hx
      by_cases h𝔭 : 𝔭 ∈ s
      · obtain ⟨m, hm⟩ := Finset.dvd_prod_of_mem (fun 𝔭 => n₁ 𝔭 * n₂ 𝔭) h𝔭
        rw [hm, show n₁ 𝔭 * n₂ 𝔭 * m = (n₁ 𝔭 * m) * n₂ 𝔭 by ring, mul_smul]
        exact zsmul_mem (hn₂x 𝔭 x hx) _
      · rw [hBs 𝔭 h𝔭]
        exact zsmul_mem hx _
  set Λ : Submodule (𝓞 K) V := ⨅ 𝔭, locF 𝔭.1 (B 𝔭) with hΛ
  have hΛle : ∀ 𝔭, Λ ≤ locF 𝔭.1 (B 𝔭) := fun 𝔭 => iInf_le _ 𝔭
  have h2 : ∀ x ∈ L₀, N • x ∈ Λ := by
    intro x hx
    rw [hΛ, Submodule.mem_iInf]
    exact fun 𝔭 => le_locF 𝔭.1 _ (hN2 𝔭 x hx)
  have h3 : ∀ x ∈ Λ, N • x ∈ L₀ := by
    intro x hx
    rw [← iInf_locF (F := F) L₀, Submodule.mem_iInf]
    intro 𝔭
    obtain ⟨t, ht, htx⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp (hΛle 𝔭 hx)
    refine (mem_locF_iff 𝔭.2.isPrime _ _).mpr ⟨t, ht, ?_⟩
    rw [smul_comm]
    exact hN1 𝔭 _ htx
  have hNK : (N : K) ≠ 0 := by exact_mod_cast hN
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · let φ : V →ₗ[𝓞 K] V := N • LinearMap.id
    have hφ : Function.Injective φ := by
      intro x y hxy
      have : N • x = N • y := hxy
      rw [← Int.cast_smul_eq_zsmul K, ← Int.cast_smul_eq_zsmul K] at this
      exact smul_right_injective V hNK this
    apply Submodule.fg_of_fg_map_injective φ hφ
    have hle : Λ.map φ ≤ L₀ := by
      rintro _ ⟨x, hx, rfl⟩
      exact h3 x hx
    exact hL₀.fg.of_le hle
  · rw [eq_top_iff, ← hL₀.span_eq_top, Submodule.span_le]
    intro x hx
    have h4 : (N : K)⁻¹ • (N • x) ∈ Submodule.span K (Λ : Set V) :=
      Submodule.smul_mem _ _ (Submodule.subset_span (h2 x hx))
    rwa [← Int.cast_smul_eq_zsmul K, smul_smul, inv_mul_cancel₀ hNK, one_smul] at h4
  · intro 𝔭
    apply le_antisymm
    · calc locF 𝔭.1 Λ ≤ locF 𝔭.1 (locF 𝔭.1 (B 𝔭)) := locF_mono _ (hΛle 𝔭)
        _ = _ := locF_idem _ _
    · intro x hx
      obtain ⟨t₀, ht₀, hy⟩ := (mem_locF_iff 𝔭.2.isPrime _ x).mp hx
      have hc : ((N * N : ℤ) : 𝓞 F) ≠ 0 := by
        exact_mod_cast mul_ne_zero hN hN
      obtain ⟨t, ht, hq⟩ := exists_prime_to_part hc 𝔭.2
      refine (mem_locF_iff 𝔭.2.isPrime _ x).mpr
        ⟨t * t₀, fun h => (𝔭.2.isPrime.mem_or_mem h).elim ht ht₀, ?_⟩
      rw [map_mul, mul_smul]
      generalize algebraMap (𝓞 F) (𝓞 K) t₀ • x = y at hy
      have hcy : (N * N) • y ∈ Λ := by
        rw [mul_smul]
        exact h2 _ (hN1 𝔭 y hy)
      rw [hΛ, Submodule.mem_iInf]
      intro 𝔮
      by_cases hqp : 𝔮 = 𝔭
      · rw [hqp]
        exact Submodule.smul_mem _ _ (le_locF _ _ hy)
      · obtain ⟨u, hu, d, hd⟩ := hq 𝔮.1 𝔮.2 (fun h => hqp (Subtype.ext h))
        rw [← locF_idem]
        refine (mem_locF_iff 𝔮.2.isPrime _ _).mpr ⟨u, hu, ?_⟩
        rw [← mul_smul, ← map_mul, hd, mul_comm, map_mul, mul_smul, algebraMap_intCast_smul]
        exact Submodule.smul_mem _ _ (hΛle 𝔮 hcy)

end Lat

end Formalism.HermitianLattices.Ext.L3.LocF
