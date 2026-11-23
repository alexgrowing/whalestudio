import Mathlib
import Formalism.UnipotentAdelicQuotients.ThmBInSatake
import GroundTheory.IdeleRoots.TorusPowers.SatakeBoundGroup
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.BlockD

namespace SatakeBound

open HeckeCharacterZeroLocus.ThmBIn

section Group

variable {G : Type} [Group G] {K : Subgroup G} {α : G} {R : Finset G}

theorem isCosetRep_congr (h : IsCosetRep (K : Set G) α R) {k₁ k₂ : G} (h₁ : k₁ ∈ K) (h₂ : k₂ ∈ K) :
    IsCosetRep (K : Set G) (k₁ * α * k₂) R := by
  obtain ⟨hR, hx⟩ := h
  refine ⟨fun γ hγ => ?_, fun x hx' => hx x ?_⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hR γ hγ
    exact ⟨a * k₁⁻¹, K.mul_mem ha (K.inv_mem h₁), k₂⁻¹ * b, K.mul_mem (K.inv_mem h₂) hb, by group⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    exact ⟨a * k₁, K.mul_mem ha h₁, k₂ * b, K.mul_mem h₂ hb, by group⟩

theorem isCosetRep_map (h : IsCosetRep (K : Set G) α R) (φ : G ≃* G) (hφ : ∀ g, φ g ∈ K ↔ g ∈ K) :
    IsCosetRep (K : Set G) (φ α) (R.map φ.toEquiv.toEmbedding) := by
  classical
  have hφs : ∀ g, φ.symm g ∈ K ↔ g ∈ K := fun g => by
    rw [← hφ (φ.symm g), MulEquiv.apply_symm_apply]
  obtain ⟨hR, hx⟩ := h
  refine ⟨fun γ hγ => ?_, fun x hx' => ?_⟩
  · obtain ⟨γ₀, hγ₀, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := hR γ₀ hγ₀
    exact ⟨φ a, (hφ a).2 ha, φ b, (hφ b).2 hb, by simp [map_mul]⟩
  · obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hy : ∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), φ.symm (a * φ α * b) = k₁ * α * k₂ :=
      ⟨φ.symm a, (hφs a).2 ha, φ.symm b, (hφs b).2 hb, by simp [map_mul]⟩
    obtain ⟨γ₀, ⟨hγ₀, hγK⟩, huniq⟩ := hx _ hy
    refine ⟨φ γ₀, ⟨Finset.mem_map_of_mem _ hγ₀, ?_⟩, ?_⟩
    · have := (hφ (γ₀⁻¹ * φ.symm (a * φ α * b))).2 hγK
      simpa [map_mul, map_inv] using this
    · rintro γ ⟨hγ, hγK'⟩
      obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_map.1 hγ
      have h1 : γ₁⁻¹ * φ.symm (a * φ α * b) ∈ K := by
        rw [← hφ]
        simpa [map_mul, map_inv] using hγK'
      have : γ₁ = γ₀ := huniq γ₁ ⟨hγ₁, h1⟩
      rw [this]
      rfl

theorem isCosetRep_mul_central (h : IsCosetRep (K : Set G) α R) {z : G} (hz : ∀ g, z * g = g * z) :
    IsCosetRep (K : Set G) (z * α) (R.map (Equiv.mulLeft z).toEmbedding) := by
  classical
  obtain ⟨hR, hx⟩ := h
  refine ⟨fun γ hγ => ?_, fun x hx' => ?_⟩
  · obtain ⟨γ₀, hγ₀, rfl⟩ := Finset.mem_map.1 hγ
    obtain ⟨a, ha, b, hb, rfl⟩ := hR γ₀ hγ₀
    refine ⟨a, ha, b, hb, ?_⟩
    simp only [Equiv.coe_toEmbedding, Equiv.coe_mulLeft]
    rw [← mul_assoc, ← mul_assoc, hz a, mul_assoc a z α]
  · obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have hy : ∃ k₁ ∈ (K : Set G), ∃ k₂ ∈ (K : Set G), z⁻¹ * (a * (z * α) * b) = k₁ * α * k₂ := by
      refine ⟨a, ha, b, hb, ?_⟩
      rw [← mul_assoc a z α, ← hz a, mul_assoc z a α, mul_assoc z (a * α) b, inv_mul_cancel_left]
    obtain ⟨γ₀, ⟨hγ₀, hγK⟩, huniq⟩ := hx _ hy
    refine ⟨z * γ₀, ⟨Finset.mem_map_of_mem (Equiv.mulLeft z).toEmbedding hγ₀, ?_⟩, ?_⟩
    · rw [mul_inv_rev, mul_assoc]
      exact hγK
    · rintro γ ⟨hγ, hγK'⟩
      obtain ⟨γ₁, hγ₁, rfl⟩ := Finset.mem_map.1 hγ
      simp only [Equiv.coe_toEmbedding, Equiv.coe_mulLeft] at hγK' ⊢
      rw [mul_inv_rev, mul_assoc] at hγK'
      rw [huniq γ₁ ⟨hγ₁, hγK'⟩]

end Group

open GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GLnLocal Iwasawa Finset Matrix
open scoped ValuativeRel

attribute [local instance] GroundTheory.Automorphic.Spherical.fintypeResidue

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
theorem one_apply_mem_integer (i j : Fin n) : (1 : Matrix (Fin n) (Fin n) F) i j ∈ 𝒪[F] := by
  rw [Matrix.one_apply]
  split_ifs
  · exact (𝒪[F]).one_mem
  · exact (𝒪[F]).zero_mem

theorem unipC_mem_integralGL (S : Finset (Fin n)) (c : Pairs S → 𝓀[F]) : unipC S c ∈ integralGL F n := by
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · change (1 + cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.add_apply]
    exact (𝒪[F]).add_mem (one_apply_mem_integer i j) (cMat_mem c i j)
  · change (1 - cMat S c) i j ∈ 𝒪[F]
    rw [Matrix.sub_apply]
    exact (𝒪[F]).sub_mem (one_apply_mem_integer i j) (cMat_mem c i j)

theorem exists_torusPow_lamS_eq {A B : Finset (Fin n)} (h : A.card = B.card) :
    ∃ P ∈ integralGL F n, torusPow F n (lamS A) = P⁻¹ * torusPow F n (lamS B) * P := by
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff h
  refine ⟨permGL F σ, GLnLocal.permGL_mem_integralGL F n σ, ?_⟩
  rw [permGL_conj_torusPow, lamS_comp_of_mem_iff hσ]

def reps (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (n r : ℕ) : Finset (GL (Fin n) F) :=
  open Classical in (powersetCard r (univ : Finset (Fin n))).biUnion fun S => univ.image (gMat S)

theorem mk_gMat_eq {S S' : Finset (Fin n)} {c : Pairs S → 𝓀[F]} {c' : Pairs S' → 𝓀[F]}
    (h : (QuotientGroup.mk (gMat S c) : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk (gMat S' c')) :
    S = S' := by
  have hk : (gMat S c)⁻¹ * gMat S' c' ∈ integralGL F n := QuotientGroup.eq.1 h
  have e : gMat S' c' = unipC S c * torusPow F n (lamS S) * ((gMat S c)⁻¹ * gMat S' c') := by
    simp only [gMat]
    group
  have := iwasawaExponent_eq F n (unipC_mem_unipotent S c) hk (l := lamS S)
  rw [← e, iwasawaExponent_gMat] at this
  exact lamS_injective this.symm

theorem gMat_injective' (S : Finset (Fin n)) : Function.Injective (gMat (F := F) S) :=
  fun _ _ h => gMat_injective S (congrArg QuotientGroup.mk h)

theorem mem_reps {r : ℕ} {γ : GL (Fin n) F} :
    γ ∈ reps F n r ↔ ∃ S ∈ powersetCard r (univ : Finset (Fin n)), ∃ c, gMat S c = γ := by
  classical
  simp only [reps, mem_biUnion, mem_image, mem_univ, true_and]

theorem sum_reps {M : Type*} [AddCommMonoid M] (r : ℕ) (f : GL (Fin n) F → M) :
    ∑ γ ∈ reps F n r, f γ = ∑ S ∈ powersetCard r (univ : Finset (Fin n)), ∑ c : Pairs S → 𝓀[F], f (gMat S c) := by
  classical
  rw [reps, sum_biUnion]
  · refine sum_congr rfl fun S _ => ?_
    rw [sum_image fun c _ c' _ h => gMat_injective' S h]
  · intro S _ S' _ hne
    rw [Function.onFun, disjoint_left]
    intro x hx hx'
    obtain ⟨c, -, rfl⟩ := mem_image.1 hx
    obtain ⟨c', -, hc'⟩ := mem_image.1 hx'
    exact hne (mk_gMat_eq (congrArg QuotientGroup.mk hc'.symm))

theorem isCosetRep_reps {r : ℕ} (hr : r ≤ n) :
    IsCosetRep (integralGL F n : Set (GL (Fin n) F)) (torusPow F n (lamS (initSeg hr))) (reps F n r) := by
  classical
  have hI : (initSeg hr).card = r := card_initSeg hr
  refine ⟨fun γ hγ => ?_, fun x hx => ?_⟩
  · obtain ⟨S, hS, c, rfl⟩ := mem_reps.1 hγ
    obtain ⟨P, hP, hPe⟩ := exists_torusPow_lamS_eq (F := F) (A := S) (B := initSeg hr)
      (by rw [(mem_powersetCard.1 hS).2, hI])
    refine ⟨unipC S c * P⁻¹, (integralGL F n).mul_mem (unipC_mem_integralGL S c)
      ((integralGL F n).inv_mem hP), P, hP, ?_⟩
    rw [gMat, hPe]
    group
  · obtain ⟨a, ha, b, hb, rfl⟩ := hx
    let c₀ : Pairs (initSeg hr) → 𝓀[F] := fun _ => 0
    have hα : torusPow F n (lamS (initSeg hr)) = (unipC (initSeg hr) c₀)⁻¹ * gMat (initSeg hr) c₀ := by
      rw [gMat, inv_mul_cancel_left]
    have hm : a * torusPow F n (lamS (initSeg hr)) * b ∈ minusculeSet F n r := by
      have h := mul_mem_minusculeSet (gMat_mem_minusculeSet _ c₀)
        ((integralGL F n).mul_mem ha ((integralGL F n).inv_mem (unipC_mem_integralGL _ c₀))) hb
      rw [hI] at h
      rw [hα, ← mul_assoc]
      exact h
    obtain ⟨S, hS, c, hc⟩ := exists_gMat hm
    refine ⟨gMat S c, ⟨mem_reps.2 ⟨S, mem_powersetCard.2 ⟨subset_univ _, hS⟩, c, rfl⟩,
      QuotientGroup.eq.1 hc⟩, ?_⟩
    rintro γ ⟨hγ, hγK⟩
    obtain ⟨S', -, c', rfl⟩ := mem_reps.1 hγ
    have h' : (QuotientGroup.mk (gMat S' c') : GL (Fin n) F ⧸ integralGL F n) = QuotientGroup.mk (gMat S c) := by
      rw [hc]
      exact QuotientGroup.eq.2 hγK
    have hSS := mk_gMat_eq h'
    subst hSS
    rw [gMat_injective _ h']

end SatakeBound

end GroundTheory.BlockD
