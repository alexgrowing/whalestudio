import Formalism.SharpRestriction.CuspSpanNormBounds.CayleyDegreeNondegeneracy.MemSupIsotropicOfDualPairing

noncomputable section

namespace Formalism.MainNotions.BridgeLemma₂

open NumberField Module Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Formalism.MainNotions.LatticeGluingRadicals
open scoped nonZeroDivisors

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {D : D7} {u : D.what₂.Word} (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E))
  (he : F0.e = D.sp.hypE) (hz : F0.z = D.zmOf u) (Λ : LatV D)
  (hΛ : Submodule.IsLattice D.host.E Λ) (hu : Formalism.HermitianLatticesTheory.IsUnimodular (hS D).hT Λ) (hzΛ : F0.z ∈ Λ)
  (hprim : ∀ c : D.host.E, c • F0.z ∈ Lsub Λ (lf D F0) → ∃ o : 𝓞 D.host.E, (o : D.host.E) = c)
  (hT : Tu D u ≠ 0)

local notation "t" => ((Tu D u : ℕ) : D.host.E)

theorem z_mem_orth_isotropic : F0.z ∈ orth (hS D) (Xsp (lf D F0)) := a_orth_of_frame F0.e F0.z F0.z_orth

include he hΛ hu hzΛ hprim hT in

theorem exists_lattice_vector_inner_z_one : ∃ m ∈ Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))), (hS D).hT F0.z m = 1 := by
  set M : LatV D := Λ ⊓ toO (hS D) (orth (hS D) (Xsp (lf D F0))) with hM
  set I : Ideal (𝓞 D.host.E) :=
    (M.map (((hS D).hT F0.z).restrictScalars (𝓞 D.host.E))).comap (Algebra.linearMap (𝓞 D.host.E) D.host.E) with hI
  have memI : ∀ o : 𝓞 D.host.E, o ∈ I ↔ ∃ m ∈ M, (hS D).hT F0.z m = algebraMap (𝓞 D.host.E) D.host.E o := by
    intro o
    rw [hI, Submodule.mem_comap, Submodule.mem_map]
    rfl
  have hzM : F0.z ∈ M := ⟨hzΛ, z_mem_orth_isotropic F0⟩
  have hI0 : I ≠ ⊥ := by
    intro h0
    have h1 : (-(Tu D u : 𝓞 D.host.E)) ∈ I := (memI _).2 ⟨F0.z, hzM, by rw [F0.z_norm]; simp⟩
    rw [h0, Ideal.mem_bot, neg_eq_zero] at h1
    exact hT (by exact_mod_cast h1)
  have hFI0 : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 hI0
  have hinv : (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ ≤ 1 := by
    intro c hc
    rw [FractionalIdeal.mem_inv_iff hFI0] at hc
    have hy : star c • F0.z ∈ Λ ⊔ toO (hS D) (Xsp (lf D F0)) := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hΛ hu _ fun m hm => ?_
      obtain ⟨i, hi⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have hiI : i ∈ I := (memI i).2 ⟨m, hm, hi.symm⟩
      obtain ⟨o, ho⟩ := (FractionalIdeal.mem_one_iff _).1
        (hc _ ((FractionalIdeal.mem_coeIdeal _).2 ⟨i, hiI, rfl⟩))
      rw [map_smul, smul_eq_mul, ← c_herm F0.z m, ← star_mul', ← hi, ← ho]
      exact star_mem_one_submodule (Submodule.mem_one.2 ⟨o, rfl⟩)
    obtain ⟨o, ho⟩ := hprim (star c) ((mem_Lsub_iff_sup_and_orth F0 Λ).2
      ⟨hy, (orth (hS D) (Xsp (lf D F0))).smul_mem _ (z_mem_orth_isotropic F0)⟩)
    obtain ⟨o', ho'⟩ := i_star_int o
    refine (FractionalIdeal.mem_one_iff _).2 ⟨o', ?_⟩
    rw [ho']
    show star (o : D.host.E) = c
    rw [ho, star_star]
  have h1 : (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) ≤ I := by
    calc (1 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) = I * (I : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)⁻¹ :=
          (mul_inv_cancel₀ hFI0).symm
      _ ≤ I * 1 := by gcongr
      _ = I := mul_one _
  obtain ⟨x, hx, hx1⟩ := (FractionalIdeal.mem_coeIdeal _).1 (h1 (FractionalIdeal.one_mem_one _))
  obtain ⟨m, hm, e⟩ := (memI x).1 hx
  exact ⟨m, hm, by rw [e, hx1]⟩

include he hz hT in

theorem exists_decomp_orth_plus {v : (hS D).V} (hv : v ∈ orth (hS D) (Xsp (lf D F0))) (hvz : (hS D).hT F0.z v = 0) :
    ∃ w : (D.sp.X 0).V, ∃ ξ ∈ Xsp (lf D F0), v = D.sp.iXY 0 w + ξ := by
  have hW := (Formalism.MainNotions.WHyp_Wsp D u hT (lf D F0) he hz).1
  have hv' : v ∈ orth (hS D) (Xplus (lf D F0)) := by
    have h : Xplus (lf D F0) ≤ LinearMap.ker ((hS D).hT.flip v) := by
      refine sup_le (fun x hx => c_mem_orth.1 hv x hx) (Submodule.span_le.2 ?_)
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hvz
    exact c_mem_orth.2 fun x hx => h hx
  rw [← hW] at hv'
  obtain ⟨a, ⟨w, rfl⟩, ξ, hξ, e⟩ := Submodule.mem_sup.1 hv'
  exact ⟨w, ξ, hξ, e.symm⟩

include he hz hT in

theorem inner_mem_one_of_mem_dual_orthLattice {m : (hS D).V} (hmΛ : m ∈ Λ) (hm : m ∈ orth (hS D) (Xsp (lf D F0)))
    (hmz : (hS D).hT F0.z m = 0) {w : (D.sp.X 0).V}
    (hw : w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0))) :
    (hS D).hT m (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨x, ξ, hξ, e⟩ := exists_decomp_orth_plus F0 he hz hT hm hmz
  have hx : x ∈ L0X D Λ (lf D F0) := by
    refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
    have : D.sp.iXY 0 x = m + (-ξ) := by rw [e]; abel
    rw [this]
    exact Submodule.add_mem_sup hmΛ ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ)
  rw [e, map_add, LinearMap.add_apply, orth_embedding_isometry, c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz w) ξ hξ, add_zero]
  exact (i_mem_dual _ _).1 hw x hx

include he hz hΛ hu hzΛ hprim hT in

theorem dual_orthLattice_quotient_cyclic : ∃ w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)),
    (∀ w ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)), ∃ a : 𝓞 D.host.E, w + a • w₁ ∈ L0X D Λ (lf D F0)) ∧
    ∀ a : 𝓞 D.host.E, a • w₁ ∈ L0X D Λ (lf D F0) ↔ ((Tu D u : ℕ) : 𝓞 D.host.E) ∣ a := by
  obtain ⟨m₁, hm₁, hzm⟩ := exists_lattice_vector_inner_z_one F0 he Λ hΛ hu hzΛ hprim hT
  have hTE : ((Tu D u : ℕ) : D.host.E) ≠ 0 := Nat.cast_ne_zero.2 hT
  set B : LatV D := Λ ⊔ toO (hS D) (Xsp (lf D F0)) with hB
  have hstar : star t = t := by simp
  have hzo := z_mem_orth_isotropic F0

  have hv1 : m₁ + t⁻¹ • F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
    (orth (hS D) (Xsp (lf D F0))).add_mem hm₁.2 ((orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo)
  have hv2 : (hS D).hT F0.z (m₁ + t⁻¹ • F0.z) = 0 := by
    rw [map_add, map_smul, hzm, F0.z_norm, smul_eq_mul]
    field_simp
    ring
  obtain ⟨w₁, ξ₁, hξ₁, e₁⟩ := exists_decomp_orth_plus F0 he hz hT hv1 hv2
  have hK1 : D.sp.iXY 0 w₁ - t⁻¹ • F0.z ∈ B := by
    have : D.sp.iXY 0 w₁ - t⁻¹ • F0.z = m₁ + (-ξ₁) := by
      have : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
      rw [this]; abel
    rw [this]
    exact Submodule.add_mem_sup hm₁.1 ((toO (hS D) (Xsp (lf D F0))).neg_mem hξ₁)
  have hmz : (hS D).hT m₁ F0.z = 1 := by rw [← c_herm, hzm, star_one]
  have hw₁ : w₁ ∈ Formalism.HermitianLatticesTheory.dual (D.sp.X 0).hT (L0X D Λ (lf D F0)) := by
    refine (i_mem_dual _ _).2 fun x hx => ?_
    have e2 : D.sp.iXY 0 w₁ = m₁ + t⁻¹ • F0.z - ξ₁ := by rw [e₁]; abel
    rw [← orth_embedding_isometry, e2, map_sub, map_add, map_smul, c_symm0 (inner_z_orth_embedding_eq_zero F0 he hz x), smul_zero, add_zero,
      c_symm0 (c_mem_orth.1 (orth_embedding_mem_orth_isotropic F0 he hz x) ξ₁ hξ₁), sub_zero]
    obtain ⟨l, hl, ξ, hξ, e⟩ := Submodule.mem_sup.1 ((mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 hx)
    rw [← e, map_add, LinearMap.add_apply, c_mem_orth.1 hm₁.2 ξ hξ, add_zero]
    exact i_int Λ hu hl hm₁.1
  refine ⟨w₁, hw₁, ?_, ?_⟩
  · intro w hw

    have hα : t * (hS D).hT m₁ (D.sp.iXY 0 w) ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
      have h1 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ Λ := Λ.add_mem (Λ.smul_mem _ hm₁.1) hzΛ
      have h2 : ((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).add_mem
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2) hzo
      have h3 : (hS D).hT F0.z (((Tu D u : ℕ) : 𝓞 D.host.E) • m₁ + F0.z) = 0 := by
        rw [map_add, ← algebraMap_smul D.host.E, map_smul, hzm, F0.z_norm]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      rw [map_add, LinearMap.add_apply, inner_z_orth_embedding_eq_zero F0 he hz w, add_zero, ← algebraMap_smul D.host.E,
        map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply] at h4
      have h5 : star (algebraMap (𝓞 D.host.E) D.host.E ((Tu D u : ℕ) : 𝓞 D.host.E)) = t := by
        rw [map_natCast]; exact hstar
      rwa [h5] at h4
    obtain ⟨α₀, hα₀⟩ := Submodule.mem_one.1 hα
    refine ⟨-α₀, (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_⟩
    have hy : D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z ∈ B := by
      refine mem_sup_isotropic_of_dual_pairing F0 he Λ hΛ hu _ fun m hm => ?_
      obtain ⟨γ, hγ⟩ := Submodule.mem_one.1 (i_int Λ hu hzΛ hm.1)
      have h1 : m - γ • m₁ ∈ Λ := Λ.sub_mem hm.1 (Λ.smul_mem _ hm₁.1)
      have h2 : m - γ • m₁ ∈ orth (hS D) (Xsp (lf D F0)) :=
        (toO (hS D) (orth (hS D) (Xsp (lf D F0)))).sub_mem hm.2
          ((toO (hS D) (orth (hS D) (Xsp (lf D F0)))).smul_mem _ hm₁.2)
      have h3 : (hS D).hT F0.z (m - γ • m₁) = 0 := by
        rw [map_sub, ← algebraMap_smul D.host.E, map_smul, hzm, hγ]
        simp
      have h4 := inner_mem_one_of_mem_dual_orthLattice F0 he hz Λ hT h1 h2 h3 hw
      have h5 : (hS D).hT m (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) =
          (hS D).hT (m - γ • m₁) (D.sp.iXY 0 w) := by
        rw [map_add, map_smul, map_sub, LinearMap.sub_apply, ← algebraMap_smul D.host.E γ, map_smulₛₗ,
          LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, starRingEnd_apply, hγ, c_herm, map_neg, hα₀]
        field_simp
        ring
      rw [h5]
      exact h4
    have e3 : D.sp.iXY 0 (w + (-α₀) • w₁) =
        (D.sp.iXY 0 w + (algebraMap (𝓞 D.host.E) D.host.E (-α₀) * t⁻¹) • F0.z) +
          (-α₀) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
      rw [map_add, LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E (-α₀) (t⁻¹ • F0.z), smul_smul]
      abel
    rw [e3]
    exact B.add_mem hy (B.smul_mem _ hK1)
  · intro a
    constructor
    · intro ha
      have h1 := (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).1 ha
      have h2 : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z ∈ B := by
        have : (algebraMap (𝓞 D.host.E) D.host.E a * t⁻¹) • F0.z =
            D.sp.iXY 0 (a • w₁) - a • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) := by
          rw [LinearMap.map_smul_of_tower, smul_sub, ← algebraMap_smul D.host.E a (t⁻¹ • F0.z), smul_smul]
          abel
        rw [this]
        exact B.sub_mem h1 (B.smul_mem _ hK1)
      obtain ⟨o, ho⟩ := hprim _ ((mem_Lsub_iff_sup_and_orth F0 Λ).2
        ⟨h2, (orth (hS D) (Xsp (lf D F0))).smul_mem _ hzo⟩)
      refine ⟨o, ?_⟩
      apply RingOfIntegers.ext
      show algebraMap (𝓞 D.host.E) D.host.E a = algebraMap (𝓞 D.host.E) D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o)
      rw [map_mul, map_natCast]
      show algebraMap (𝓞 D.host.E) D.host.E a = t * (o : D.host.E)
      rw [ho]
      field_simp
    · rintro ⟨o, rfl⟩
      refine (mem_orthLattice_iff_image_mem_sup F0 he hz Λ).2 ?_
      have : D.sp.iXY 0 ((((Tu D u : ℕ) : 𝓞 D.host.E) * o) • w₁) =
          (((Tu D u : ℕ) : 𝓞 D.host.E) * o) • (D.sp.iXY 0 w₁ - t⁻¹ • F0.z) + o • F0.z := by
        rw [LinearMap.map_smul_of_tower, smul_sub,
          ← algebraMap_smul D.host.E (((Tu D u : ℕ) : 𝓞 D.host.E) * o) (t⁻¹ • F0.z), smul_smul, map_mul, map_natCast,
          ← algebraMap_smul D.host.E o F0.z]
        have : (t * algebraMap (𝓞 D.host.E) D.host.E o * t⁻¹) = algebraMap (𝓞 D.host.E) D.host.E o := by
          field_simp
        rw [this]
        abel
      rw [this]
      exact B.add_mem (B.smul_mem _ hK1) (Submodule.mem_sup_left (Λ.smul_mem _ hzΛ))

end Lat

end Formalism.MainNotions.BridgeLemma₂

end
