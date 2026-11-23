import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwLeviSum
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwFactTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHkApply
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwHeckePairIwC
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem domSum_reps {G : Type} [Group G] {N I : Subgroup G} (hN : N ≤ I) (d : G) (h : FinOrb I I d) :
    ∃ s : Finset G, (∀ u ∈ s, u ∈ N) ∧ ∀ y ∈ N, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
  obtain ⟨S, hS, hb⟩ := Set.exists_subset_bijOn (N : Set G) (fun y => ((y * d : G) : G ⧸ I))
  have hq : ((fun y => ((y * d : G) : G ⧸ I)) '' (N : Set G)).Finite := by
    refine h.subset ?_
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨⟨y, hN hy⟩, rfl⟩
  have hf : S.Finite := Set.Finite.of_finite_image (hb.image_eq ▸ hq) hb.injOn
  have key : ∀ u y : G, ((u * d : G) : G ⧸ I) = ((y * d : G) : G ⧸ I) ↔ d⁻¹ * (u⁻¹ * y) * d ∈ I := by
    intro u y
    rw [QuotientGroup.eq]
    have : (u * d)⁻¹ * (y * d) = d⁻¹ * (u⁻¹ * y) * d := by group
    rw [this]
  refine ⟨hf.toFinset, fun u hu => hS (hf.mem_toFinset.1 hu), fun y hy => ?_⟩
  obtain ⟨u, hu, e⟩ := hb.surjOn ⟨y, hy, rfl⟩
  refine ⟨u, ⟨hf.mem_toFinset.2 hu, (key u y).1 e⟩, ?_⟩
  rintro u' ⟨hu', e'⟩
  exact hb.injOn (hf.mem_toFinset.1 hu') hu (((key u' y).2 e').trans e.symm)

private theorem domSum_gen {G : Type} [Group G] {I : Subgroup G} (F : LeviFact I) (d : G) (hI : HeckePair I)
    (hp : F.Pos d) (hn : F.NormJ d) (s : Finset G) (hs : ∀ u ∈ s, u ∈ F.Uf ⊓ I)
    (hs' : ∀ x ∈ F.Uf ⊓ I, ∃! u, u ∈ s ∧ d⁻¹ * (u⁻¹ * x) * d ∈ I)
    (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A G M) (v : fixd ρ I) :
    (hk ρ I d v : M) = ∑ u ∈ s, ρ (u * d) v := by
  classical
  have H := leviSum G I F d hI hp {d}
    (fun a ha => ⟨1, one_mem _, 1, one_mem _, by simpa using ha⟩)
    (fun j hj => ⟨d, ⟨Finset.mem_singleton_self d, by simpa [mul_assoc] using (hn j hj).2⟩,
      fun a ha => Finset.mem_singleton.1 ha.1⟩)
    (fun _ => s) (fun a ha => by
      rw [Finset.mem_singleton.1 ha]
      exact ⟨hs, hs'⟩)
  have h2 := (hkApply A G M ρ I I d (hI d)).2.1 (s.image (· * d)) ?_ ?_ v
  · rw [hk, h2, Finset.sum_image (fun a _ b _ h => mul_right_cancel h)]
  · intro y hy
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hy
    exact ⟨⟨u, (hs u hu).2⟩, rfl⟩
  · intro q hq
    obtain ⟨⟨a, u⟩, ⟨ha, hu, e⟩, huniq⟩ := (H q).1 hq
    have had : a = d := Finset.mem_singleton.1 ha
    subst had
    refine ⟨u * a, ⟨Finset.mem_image.2 ⟨u, hu, rfl⟩, e⟩, ?_⟩
    rintro y ⟨hy, e'⟩
    obtain ⟨u', hu', rfl⟩ := Finset.mem_image.1 hy
    have := huniq (a, u') ha hu' e'
    rw [show u' = u from (Prod.ext_iff.1 this).2]

theorem UpperTheory.V.AlgebraTools.domSum :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (t : Fin n → kˣ), Dom t → ∃ s : Finset (GL (Fin n) k), (∀ u ∈ s, u ∈ unipO k n) ∧ (∀ y ∈ unipO k n, ∃! u, u ∈ s ∧ (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n) ∧ ∀ (C : Subgroup 𝓀[k]ˣ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (v : fixd ρ (iwC k n C)), (hk ρ (iwC k n C) (diagT k (Fin n) t) v : M) = ∑ u ∈ s, ρ (u * diagT k (Fin n) t) v := by
  intro k _ _ _ _ n t ht
  have key : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ u ∈ unipO k n, ∀ y ∈ unipO k n,
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C ↔
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ unipO k n := by
    intro C u hu y hy
    obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    rw [← hU] at hu hy ⊢
    have := F.M_U _ (inv_mem ((hF t).2 ht).1) _ (mul_mem (inv_mem hu.1) hy.1)
    rw [inv_inv] at this
    exact ⟨fun h => ⟨this, h⟩, fun h => h.2⟩
  have hle : unipO k n ≤ iwC k n ⊤ := le_sup_right.trans le_sup_left
  obtain ⟨s, hs, hs'⟩ := domSum_reps hle (diagT k (Fin n) t) ((heckePairIwC k n ⊤).1 _)
  have hs2 : ∀ (C : Subgroup 𝓀[k]ˣ), ∀ y ∈ unipO k n, ∃! u, u ∈ s ∧
      (diagT k (Fin n) t)⁻¹ * (u⁻¹ * y) * diagT k (Fin n) t ∈ iwC k n C := by
    intro C y hy
    refine (existsUnique_congr fun u => and_congr_right fun hu => ?_).1 (hs' y hy)
    rw [key ⊤ u (hs u hu) y hy, key C u (hs u hu) y hy]
  refine ⟨s, hs, fun y hy => ?_, fun C A M _ _ _ ρ v => ?_⟩
  · exact (existsUnique_congr fun u => and_congr_right fun hu => key ⊤ u (hs u hu) y hy).1 (hs' y hy)
  · obtain ⟨F, -, -, -, hU, -, hF⟩ := factTorus k n C
    exact domSum_gen F _ (heckePairIwC k n C).1 ((hF t).2 ht) (hF t).1 s (hU ▸ hs) (hU ▸ hs2 C) A M ρ v
