import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.ExistsLocFEq
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.GmapEqSelfOfFix

open NumberField Module

noncomputable section

namespace Formalism.L2.SG.Pf.G8

open Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

variable {K F V : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

private lemma mem_locF_lemma (𝔭 : Ideal (𝓞 F)) (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ locF 𝔭 L ↔ ∃ s ∈ Submonoid.closure
      {s : 𝓞 K | ∃ t : 𝓞 F, t ∉ 𝔭 ∧ algebraMap (𝓞 F) (𝓞 K) t = s}, s • x ∈ L := Iff.rfl

private lemma locF_inf_restrictScalars (X : Submodule K V) (Λ : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (hp : 𝔭.IsPrime) :
    locF 𝔭 (Λ ⊓ X.restrictScalars (𝓞 K)) = locF 𝔭 Λ ⊓ X.restrictScalars (𝓞 K) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
    refine Submodule.mem_inf.mpr ⟨(mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.1⟩, ?_⟩
    rw [← Formalism.L2.SG.Pf.G7.locF_subspace X hp]
    exact (mem_locF_lemma 𝔭 _ x).mpr ⟨s, hs, hsx.2⟩
  · intro x hx
    obtain ⟨hx1, hx2⟩ := Submodule.mem_inf.mp hx
    obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx1
    exact (mem_locF_lemma 𝔭 _ x).mpr
      ⟨s, hs, Submodule.mem_inf.mpr ⟨hsx, (X.restrictScalars (𝓞 K)).smul_mem s hx2⟩⟩

theorem locF_mem_fibS (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    {M T Λ : Submodule (𝓞 K) V} (hΛ : Submodule.IsLattice K Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ)
    (hM : Λ ⊓ U.restrictScalars (𝓞 K) = M) (hT : Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) : locF 𝔭 Λ ∈ fibS h U 𝔭 M T := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ = Λ := hu
  simp only [fibS, Set.mem_setOf_eq]
  refine ⟨⟨Λ, hΛ, rfl⟩, ?_, ?_, ?_⟩
  · rw [← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ.fg h𝔭.isPrime, hu']
  · rw [← hM, locF_inf_restrictScalars U Λ h𝔭.isPrime]
  · rw [← hT, locF_inf_restrictScalars (orthK h U) Λ h𝔭.isPrime]

theorem fibS_eq_singleton (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {U : Submodule K V}
    (hUc : IsCompl U (orthK h U)) {M T Λ₀ : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    (hT : IsLatIn (orthK h U) T) (hΛ₀ : Submodule.IsLattice K Λ₀) (hu : Formalism.HermitianLatticesTheory.IsUnimodular h Λ₀)
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) (he : locF 𝔭 (M ⊔ T) = locF 𝔭 Λ₀) :
    fibS h U 𝔭 M T = {locF 𝔭 (M ⊔ T)} := by
  have hu' : Formalism.HermitianLatticesTheory.dual h Λ₀ = Λ₀ := hu
  have hN : dualF h 𝔭 (locF 𝔭 (M ⊔ T)) = locF 𝔭 (M ⊔ T) := by
    rw [he, ← Formalism.L2.SG.Pf.G7.locF_dual hF h hΛ₀.fg h𝔭.isPrime, hu']
  have hMU : ∀ x ∈ M, x ∈ U := fun x hx => hM.2 ▸ Submodule.subset_span hx
  have hTW : ∀ x ∈ T, x ∈ orthK h U := fun x hx => hT.2 ▸ Submodule.subset_span hx
  have hcapU : locF 𝔭 (M ⊔ T) ⊓ U.restrictScalars (𝓞 K) = locF 𝔭 M :=
    locF_sup_inf hUc hMU hTW h𝔭.isPrime
  have hcapW : locF 𝔭 (M ⊔ T) ⊓ (orthK h U).restrictScalars (𝓞 K) = locF 𝔭 T := by
    rw [sup_comm]; exact locF_sup_inf hUc.symm hTW hMU h𝔭.isPrime
  ext Λ
  simp only [fibS, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨⟨Λ₁, hΛ₁, rfl⟩, hd, hcU, hcW⟩
    have hle : locF 𝔭 (M ⊔ T) ≤ locF 𝔭 Λ₁ := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (mem_locF_lemma 𝔭 _ x).mp hx
      obtain ⟨m, hm, t, ht, hmt⟩ := Submodule.mem_sup.mp hsx
      have hm' : m ∈ locF 𝔭 Λ₁ := by
        have hm1 : m ∈ locF 𝔭 M :=
          (mem_locF_lemma 𝔭 _ m).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcU] at hm1
        exact (Submodule.mem_inf.mp hm1).1
      have ht' : t ∈ locF 𝔭 Λ₁ := by
        have ht1 : t ∈ locF 𝔭 T :=
          (mem_locF_lemma 𝔭 _ t).mpr ⟨1, Submonoid.one_mem _, by rwa [one_smul]⟩
        rw [← hcW] at ht1
        exact (Submodule.mem_inf.mp ht1).1
      have hsx' : s • x ∈ locF 𝔭 Λ₁ := by rw [← hmt]; exact add_mem hm' ht'
      obtain ⟨s', hs', h'⟩ := (mem_locF_lemma 𝔭 _ _).mp hsx'
      exact (mem_locF_lemma 𝔭 _ x).mpr
        ⟨s' * s, Submonoid.mul_mem _ hs' hs, by rw [mul_smul]; exact h'⟩
    refine le_antisymm ?_ hle
    calc locF 𝔭 Λ₁ = dualF h 𝔭 (locF 𝔭 Λ₁) := hd.symm
      _ ≤ dualF h 𝔭 (locF 𝔭 (M ⊔ T)) := dualF_anti h 𝔭 hle
      _ = locF 𝔭 (M ⊔ T) := hN
  · rintro rfl
    exact ⟨⟨Λ₀, hΛ₀, he.symm⟩, hN, hcapU, hcapW⟩

theorem card_glue (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K}
    {U : Submodule K V} (hUc : IsCompl U (orthK h U)) {M : Submodule (𝓞 K) V} (hM : IsLatIn U M)
    {Λ₀ : Submodule (𝓞 K) V} (hΛ₀ : Λ₀ ∈ GlueSet h U M) {T : Submodule (𝓞 K) V}
    (hT : IsLatIn (orthK h U) T) :
    Nat.card {Λ : Submodule (𝓞 K) V // Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T} =
      ∏' 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, fibP h U 𝔭.1 M T := by
  classical
  have hN := isLattice_sup hUc hM hT
  obtain ⟨s, hs⟩ := exists_locF_eq (F := F) hN hΛ₀.1
  have hsing : ∀ 𝔭 ∉ s, fibS h U 𝔭.1 M T = {locF 𝔭.1 (M ⊔ T)} := fun 𝔭 h𝔭 =>
    fibS_eq_singleton hF hUc hM hT hΛ₀.1 hΛ₀.2.1 𝔭.2 (hs 𝔭 h𝔭)
  have hone : ∀ 𝔭 ∉ s, fibP h U 𝔭.1 M T = 1 := by
    intro 𝔭 h𝔭
    rw [fibP_eq, hsing 𝔭 h𝔭]
    simp
  rw [tprod_eq_prod hone, ← Finset.prod_coe_sort s]
  simp only [fibP_eq]
  rw [← Nat.card_pi]
  refine Nat.card_congr (Equiv.ofBijective
    (fun Λ 𝔭 => ⟨locF 𝔭.1.1 Λ.1, locF_mem_fibS hF Λ.2.1.1 Λ.2.1.2.1 Λ.2.1.2.2 Λ.2.2 𝔭.1.2⟩) ⟨?_, ?_⟩)
  · rintro ⟨Λ₁, h1⟩ ⟨Λ₂, h2⟩ he
    apply Subtype.ext
    show Λ₁ = Λ₂
    refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
    by_cases hps : (⟨𝔭, h𝔭⟩ : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}) ∈ s
    · exact congrArg Subtype.val (congrFun he ⟨_, hps⟩)
    · have a1 := locF_mem_fibS hF h1.1.1 h1.1.2.1 h1.1.2.2 h1.2 h𝔭
      have a2 := locF_mem_fibS hF h2.1.1 h2.1.2.1 h2.1.2.2 h2.2 h𝔭
      rw [hsing _ hps, Set.mem_singleton_iff] at a1 a2
      exact a1.trans a2.symm
  · intro τ
    obtain ⟨Λ, ⟨hΛ, hin, hout⟩, -⟩ := exists_unique_patch hK hF hN s
      (fun 𝔭 => if hp : 𝔭 ∈ s then (τ ⟨𝔭, hp⟩).1 else ⊥) (by
        intro 𝔭 hp
        simp only [dif_pos hp]
        obtain ⟨⟨A, hA, e⟩, -, -, -⟩ := (τ ⟨𝔭, hp⟩).2
        exact ⟨by rw [← e, LocF.locF_idem], A, hA, e⟩)
    have hfib : ∀ 𝔭 : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal}, locF 𝔭.1 Λ ∈ fibS h U 𝔭.1 M T := by
      intro 𝔭
      by_cases hp : 𝔭 ∈ s
      · rw [hin 𝔭 hp, dif_pos hp]
        exact (τ ⟨𝔭, hp⟩).2
      · rw [hout 𝔭 hp, hsing 𝔭 hp]
        exact Set.mem_singleton _
    have hmem : Λ ∈ GlueSet h U M ∧ Λ ⊓ (orthK h U).restrictScalars (𝓞 K) = T := by
      refine ⟨⟨hΛ, ?_, ?_⟩, ?_⟩
      · show Formalism.HermitianLatticesTheory.dual h Λ = Λ
        refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [G7.locF_dual hF h hΛ.fg h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace U h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.1
      · refine G7.eq_of_locF (F := F) _ _ fun 𝔭 h𝔭 => ?_
        rw [LIOrb.locF_inf_locF h𝔭, G7.locF_subspace (orthK h U) h𝔭.isPrime]
        exact (hfib ⟨𝔭, h𝔭⟩).2.2.2
    refine ⟨⟨Λ, hmem⟩, ?_⟩
    funext 𝔭
    apply Subtype.ext
    show locF 𝔭.1.1 Λ = (τ 𝔭).1
    rw [hin 𝔭.1 𝔭.2, dif_pos 𝔭.2]

end Formalism.L2.SG.Pf.G8
