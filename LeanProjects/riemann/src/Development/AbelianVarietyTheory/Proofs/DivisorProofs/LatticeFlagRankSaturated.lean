import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LnStepFalse
open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.PullbackSections ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj
open GlobalTheory.TrueGeo GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.Toroidal GlobalTheory.LocM.Frm GlobalTheory.HeightParts
open GlobalTheory.GradedNorm GlobalTheory.LieHt
open Formalism.MainNotions.DIV.Cons (intO)
open GlobalTheory.LieSmooth

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LieSmooth

theorem exists_ne_zero_smul_mem_of_mem_kspan_lat {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (E : Submodule (𝓞 K) V) {x : V}
    (hx : x ∈ Submodule.span K (E : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ E := by
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_ne_zero, by simpa using hy⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨d₁, hd₁, h₁⟩ := hy
    obtain ⟨d₂, hd₂, h₂⟩ := hz
    refine ⟨d₁ * d₂, mul_ne_zero hd₁ hd₂, ?_⟩
    have e1 : (d₁ * d₂) • y = d₂ • (d₁ • y) := by rw [mul_comm, mul_smul]
    have e2 : (d₁ * d₂) • z = d₁ • (d₂ • z) := by rw [mul_smul]
    rw [smul_add, e1, e2]
    exact E.add_mem (E.smul_mem _ h₁) (E.smul_mem _ h₂)
  | smul c y _ hy =>
    obtain ⟨d, hd, h⟩ := hy
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := 𝓞 K) c
    have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
    have hbK : (algebraMap (𝓞 K) K b) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
    refine ⟨b * d, mul_ne_zero hb0 hd, ?_⟩
    have key : (b * d) • ((algebraMap (𝓞 K) K a / algebraMap (𝓞 K) K b) • y) = a • (d • y) := by
      rw [← algebraMap_smul K (b * d), ← algebraMap_smul K a, ← algebraMap_smul K d,
        smul_smul, smul_smul]
      congr 1
      rw [map_mul]
      field_simp
    rw [key]
    exact E.smul_mem _ h

theorem sum_smul_castLE_of_vanish {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {r : ℕ}
    (v : Fin r → V) {k : ℕ} (hk : k ≤ r) (c : Fin r → K) (hc : ∀ j : Fin r, k ≤ j.val → c j = 0) :
    ∑ j, c j • v j = ∑ j : Fin k, c (Fin.castLE hk j) • v (Fin.castLE hk j) := by
  classical
  have hm := Finset.sum_map Finset.univ (Fin.castLEEmb hk) (fun j => c j • v j)
  simp only [Fin.castLEEmb_apply] at hm
  rw [← hm]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro j _ hj
  have : k ≤ j.val := by
    by_contra hlt
    exact hj (Finset.mem_map.2 ⟨⟨j.val, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
  simp [hc j this]

theorem grIdeal_castLE {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (E : Submodule (𝓞 K) V) {r : ℕ} (v : Fin r → V) {k : ℕ}
    (hk : k ≤ r) (i : Fin k) :
    grIdeal (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)) (v ∘ Fin.castLE hk) i
      = grIdeal E v (Fin.castLE hk i) := by
  ext a
  constructor
  · rintro ⟨c, rfl, hc1, hc2⟩
    let c' : Fin r → K := fun j => if h : j.val < k then c ⟨j.val, h⟩ else 0
    refine ⟨c', by simp [c'], fun j hj => ?_, ?_⟩
    · simp only [c']
      split_ifs with h
      · exact hc1 _ (by simpa [Fin.lt_def] using hj)
      · rfl
    · have hs := sum_smul_castLE_of_vanish v hk c' (fun j hj => by simp [c', not_lt.2 hj])
      rw [hs]
      have : ∀ j : Fin k, c' (Fin.castLE hk j) = c j := fun j => by simp [c']
      simp only [this]
      exact (Submodule.mem_inf.1 hc2).1
  · rintro ⟨c, rfl, hc1, hc2⟩
    refine ⟨c ∘ Fin.castLE hk, rfl, fun j hj => hc1 _ (by rw [Fin.lt_def, Fin.coe_castLE, Fin.coe_castLE]; exact hj), ?_⟩
    have hs := sum_smul_castLE_of_vanish v hk c (fun j hj => hc1 j (by have := i.isLt; rw [Fin.lt_def, Fin.coe_castLE]; omega))
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · simpa [hs] using hc2
    · rw [Submodule.restrictScalars_mem]
      exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem inf_span_castLE_lineHt : ∀ (K : Type) [Field K] [NumberField K] (V : Type) [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : HermFam K V) (E : Submodule (𝓞 K) V) (r : ℕ) (v : Fin r → V) (k : ℕ) (hk : k ≤ r), E.FG → LinearIndependent K v → Submodule.span K (Set.range v) ≤ Submodule.span K (E : Set V) → latRank K (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)) = k ∧ (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)).FG ∧ Submodule.span K ((E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = Submodule.span K (Set.range (v ∘ Fin.castLE hk)) ∧ ∀ i, lineHt h (E ⊓ (Submodule.span K (Set.range (v ∘ Fin.castLE hk))).restrictScalars (𝓞 K)) (v ∘ Fin.castLE hk) i = lineHt h E v (Fin.castLE hk i) := by
  intro K _ _ V _ _ _ _ h E r v k hk hE hv hvE
  set S := Submodule.span K (Set.range (v ∘ Fin.castLE hk)) with hS
  have hspan : Submodule.span K ((E ⊓ S.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) : Set V) = S := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro x hx
      exact (Submodule.mem_inf.1 hx).2
    · rw [hS, Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      obtain ⟨d, hd, hdE⟩ := exists_ne_zero_smul_mem_of_mem_kspan_lat E
        (hvE (Submodule.subset_span ⟨Fin.castLE hk j, rfl⟩))
      have hdK : (algebraMap (𝓞 K) K d) ≠ 0 := by
        simpa using (FaithfulSMul.algebraMap_injective (𝓞 K) K).ne hd
      have hmem : d • (v ∘ Fin.castLE hk) j ∈ (E ⊓ S.restrictScalars (𝓞 K) : Submodule (𝓞 K) V) :=
        Submodule.mem_inf.2 ⟨hdE, (Submodule.restrictScalars_mem _ _ _).2
          (Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨j, rfl⟩))⟩
      have e : (v ∘ Fin.castLE hk) j = (algebraMap (𝓞 K) K d)⁻¹ • (d • (v ∘ Fin.castLE hk) j) := by
        rw [← algebraMap_smul K d, smul_smul, inv_mul_cancel₀ hdK, one_smul]
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  refine ⟨?_, ?_, hspan, ?_⟩
  · unfold latRank
    rw [hspan, hS, finrank_span_eq_card (hv.comp _ (Fin.castLE_injective hk))]
    simp
  · haveI := isNoetherian_of_fg_of_noetherian E hE
    have := (IsNoetherian.noetherian (Submodule.comap E.subtype (S.restrictScalars (𝓞 K)))).map E.subtype
    rwa [Submodule.map_comap_subtype] at this
  · intro i
    rw [hS]
    simp only [lineHt, grIdeal_castLE]
    rfl

end GlobalTheory.LieSmooth
