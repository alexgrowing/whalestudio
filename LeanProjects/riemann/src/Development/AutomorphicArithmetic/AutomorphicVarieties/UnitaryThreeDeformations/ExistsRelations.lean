import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsCharZeroPt
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.RelAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ExistsUnobstructed
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.ConjPushMat

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia

namespace UpperTheory.V.UnitaryThreeInertia.Rel

private theorem C_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (c : O) (hc : c ∈ maximalIdeal O) :
    (MvPowerSeries.C c : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := fun h =>
  hc (by simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 h)

private theorem X_mem_max {O σ : Type} [CommRing O] [IsLocalRing O] (i : σ) :
    (MvPowerSeries.X i : MvPowerSeries σ O) ∈ maximalIdeal (MvPowerSeries σ O) := fun h => by
  simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 h

private theorem map_eq_of_linear {O σ B : Type} [CommRing O] [IsLocalRing O] [Fintype σ] [CommRing B] [IsLocalRing B]
    [Algebra O B] (a b : MvPowerSeries σ O →ₐ[O] B) (N : Ideal B) (hN : N ≤ maximalIdeal B)
    (hk : ∀ x ∈ maximalIdeal B, ∀ y ∈ N, x * y = 0) (hab : ∀ f, a f - b f ∈ N)
    (ha : ∀ f ∈ maximalIdeal (MvPowerSeries σ O), a f ∈ maximalIdeal B) (f : MvPowerSeries σ O)
    (hf : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) f ∈ maximalIdeal O) : a f = b f := by
  classical
  have h2 : f - MvPowerSeries.C (MvPowerSeries.coeff 0 f) ∈ maximalIdeal (MvPowerSeries σ O) ^ 2 := by
    refine mem_pow_of_coeff (maximalIdeal O) _ C_mem_max X_mem_max 2 _ fun n => ?_
    rw [map_sub, MvPowerSeries.coeff_C]
    split_ifs with h0
    · subst h0
      simp
    · rw [sub_zero]
      by_cases h1 : Finsupp.degree n = 1
      · obtain ⟨i, rfl⟩ : n ∈ Set.range fun i : σ => Finsupp.single i 1 := by
          rw [Finsupp.range_single_one]; exact h1
        rw [h1]
        simpa using hf i
      · have : Finsupp.degree n ≠ 0 := fun h => h0 ((Finsupp.degree_eq_zero_iff n).1 h)
        rw [show 2 - Finsupp.degree n = 0 by omega]
        simp
  have h3 : ∀ g ∈ maximalIdeal (MvPowerSeries σ O) ^ 2, a g = b g := fun g hg => by
    rw [pow_two] at hg
    refine Submodule.mul_induction_on hg (fun x hx y hy => ?_) fun x y hx hy => by rw [map_add, map_add, hx, hy]
    have hb : b y ∈ maximalIdeal B := by simpa using sub_mem (ha y hy) (hN (hab y))
    have e1 := hk _ (ha x hx) _ (hab y)
    have e2 := hk _ hb _ (hab x)
    rw [map_mul, map_mul]
    linear_combination e1 + e2
  have h4 := h3 _ h2
  have h5 : ∀ c : O, (MvPowerSeries.C c : MvPowerSeries σ O) = algebraMap O _ c := fun c => by
    simp [MvPowerSeries.algebraMap_apply]
  rw [map_sub, map_sub, h5, AlgHom.commutes, AlgHom.commutes] at h4
  exact sub_left_injective h4

private theorem card_ker_le
    {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
    {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι) (hF : F.Ok)
    (hv : F.LocVan) (hc : F.Count) (g₁ : Γ) (hg : F.Marked g₁) {R : Type} [CommRing R] [Algebra O R] [IsCO O R]
    (u : Γ →* GG 3 R) (hu : F.IsUniv g₁ u) (W : WPres O ℤ R) (hW : F.Adapted u W) (hm : Frame.Minimal W)
    {A A' : Type} [CommRing A] [Algebra O A] [IsCO O A] [CommRing A'] [Algebra O A'] [IsCO O A']
    (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (p : A →ₐ[O] A') (j : ℤ) (hp : Function.Surjective p)
    (hs : SmallExt O 𝒜 (RingHom.ker p) j) (φ : MvPowerSeries W.σ O →ₐ[O] A) (hφ : Function.Surjective φ)
    (hw : ∀ i, ∀ f ∈ wtPart O W.wt i, φ f ∈ 𝒜 i) (hker : RingHom.ker p = (RingHom.ker W.π).map φ) :
    Nat.card (RingHom.ker p) ≤ Nat.card (ResidueField O) ^ Module.finrank (ResidueField O) (F.Ob j) := by
  by_contra hlt
  rw [not_le] at hlt
  let ψ : R →ₐ[O] A' := AlgHom.liftOfSurjective W.π W.surj (p.comp φ) fun f hf => by
    have : φ f ∈ RingHom.ker p := hker ▸ Ideal.mem_map_of_mem _ hf
    exact this
  have hψ : ∀ f, ψ (W.π f) = p (φ f) := fun f => AlgHom.liftOfSurjective_apply _ _ _ _ f
  haveI : IsLocalHom ψ := ⟨fun x hx => by
    by_contra hn
    have h1 : x ∈ maximalIdeal R := hn
    rw [← res_eq_zero_iff O, ← res_map ψ, res_eq_zero_iff] at h1
    exact h1 hx⟩
  obtain ⟨R'', _, _, _, p₁, q, r, hp₁, hq, hinj, hr, hqr⟩ :=
    exists_unobstructed F hF hv g₁ hg 𝒜 p j hp hs (hc j).2.1 hlt (push ψ u) (isPt_push F ψ g₁ u hu.pt) fun g => by
      have h1 : ∀ a b, ∃ f ∈ wtPart O W.wt (wt a b), W.π f = (u g).mat a b := fun a b => by
        have := entry_mem (O := O) u g a b
        rw [← hW.part] at this
        exact this
      choose f hf hf' using h1
      refine ⟨fun a b => φ (f a b), fun a b => hw _ _ (hf a b), ?_⟩
      ext a b
      show p (φ (f a b)) = ψ ((u g).mat a b)
      rw [← hf', hψ]
  obtain ⟨s, hs1, -⟩ := hu.univ R'' r hr
  have hqs : q.comp s = ψ := by
    refine (hu.univ A' (push ψ u) (isPt_push F ψ g₁ u hu.pt)).unique ?_ rfl
    rw [← hqr, ← hs1]
    refine MonoidHom.ext fun g => SemidirectProduct.ext ?_ rfl
    exact Units.ext (Matrix.ext fun a b => rfl)
  have hq' : ∀ x, q (p₁ x) = p x := fun x => AlgHom.congr_fun hq x
  have key : ∀ f, W.π f = 0 → p₁ (φ f) = 0 := fun f hf => by
    have := map_eq_of_linear (p₁.comp φ) (s.comp W.π) (RingHom.ker q)
      (le_maximalIdeal (RingHom.ker_ne_top _)) (fun x hx y hy => ?_) (fun f => ?_) (fun f hf => ?_) f (hm f hf)
    · simpa [hf] using this
    · obtain ⟨w, rfl⟩ := hp₁ x
      obtain ⟨z, rfl⟩ := hp₁ y
      have hw : w ∈ maximalIdeal A := fun h => hx (h.map p₁)
      have hz : z ∈ RingHom.ker p := by
        rw [RingHom.mem_ker, ← hq']; exact hy
      have := Ideal.mul_mem_mul hw hz
      rw [hs.kill, Ideal.mem_bot] at this
      rw [← map_mul, this, map_zero]
    · have e : q (s (W.π f)) = ψ (W.π f) := AlgHom.congr_fun hqs _
      rw [RingHom.mem_ker, map_sub, AlgHom.comp_apply, AlgHom.comp_apply, e, hq', hψ, sub_self]
    · haveI := IsLocalHom.of_surjective ((p₁.comp φ : MvPowerSeries W.σ O →ₐ[O] R'') : MvPowerSeries W.σ O →+* R'')
        (hp₁.comp hφ)
      exact map_nonunit ((p₁.comp φ : MvPowerSeries W.σ O →ₐ[O] R'') : MvPowerSeries W.σ O →+* R'') f hf
  refine hinj ((injective_iff_map_eq_zero q).2 fun y hy => ?_)
  obtain ⟨z, rfl⟩ := hp₁ y
  have hz : z ∈ RingHom.ker p := by
    rw [RingHom.mem_ker, ← hq']; exact hy
  rw [hker] at hz
  obtain ⟨f, hf, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hz
  exact key f hf

end UpperTheory.V.UnitaryThreeInertia.Rel

open UpperTheory.V.UnitaryThreeInertia.Rel in
theorem UpperTheory.V.UnitaryThreeInertia.exists_relations :
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O] [Finite (ResidueField O)]
      {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
      [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [T2Space Γ] [TotallyDisconnectedSpace Γ] [Finite ι] (F : Frame O G Γ ι), F.Ok →
    F.LocVan → F.Count → ∀ (g₁ : Γ), F.Marked g₁ → ∀ {R : Type} [CommRing R] [Algebra O R] [IsCO O R] (u : Γ →* GG 3 R), F.IsUniv g₁ u →
    ∀ (W : WPres O ℤ R), F.Adapted u W → Frame.Minimal W →
    ∃ f : (j : ℤ) → Fin (Module.finrank (ResidueField O) (F.Ob j)) → MvPowerSeries W.σ O, (∀ j i, f j i ∈ wtPart O W.wt j) ∧ RingHom.ker W.π = Ideal.span (⋃ j, Set.range (f j)) := by
  intro O _ _ _ _ _ _ G Γ ι _ _ _ _ _ _ _ _ _ _ _ _ _ F hF hv hc g₁ hg R _ _ _ u hu W hW hm
  classical
  set P := MvPowerSeries W.σ O
  set J : Ideal P := RingHom.ker W.π with hJ
  obtain ⟨N, hN0, hN⟩ : ∃ N, N ≠ 0 ∧ maximalIdeal P ^ N ⊓ J ≤ maximalIdeal P * J := by
    obtain ⟨k, hk⟩ := (maximalIdeal P).exists_pow_inf_eq_pow_smul (M := P) J
    refine ⟨k + 1, by omega, ?_⟩
    have := hk (k + 1) (by omega)
    simp only [smul_eq_mul, Ideal.mul_top, Nat.add_sub_cancel_left, pow_one] at this
    rw [this]
    exact Ideal.mul_mono_right inf_le_right
  have hT : Tr W.σ (maximalIdeal O) N ≤ maximalIdeal P ^ N := fun f hf =>
    mem_pow_of_coeff _ _ C_mem_max X_mem_max N f hf
  have hTm : Tr W.σ (maximalIdeal O) N ≤ maximalIdeal P := hT.trans (Ideal.pow_le_self hN0)
  have hJm : J ≤ maximalIdeal P := le_maximalIdeal (RingHom.ker_ne_top _)
  haveI : Finite (O ⧸ maximalIdeal O) := inferInstanceAs (Finite (ResidueField O))
  haveI : Finite (O ⧸ maximalIdeal O ^ N) := Ideal.finite_quotient_pow (IsNoetherian.noetherian _) N
  set T := Tr W.σ (maximalIdeal O) N with hTdef
  haveI : Finite (P ⧸ T) := finite_quot_Tr _ N
  haveI : Nontrivial (P ⧸ T) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top (maximalIdeal.isMaximal P).ne_top hTm)
  have h5 : ∀ c : O, (MvPowerSeries.C c : P) = algebraMap O _ c := fun c => by
    simp [P, MvPowerSeries.algebraMap_apply]
  haveI : IsLocalHom (algebraMap O P) := ⟨fun c h => by
    by_contra hn
    exact C_mem_max c hn (h5 c ▸ h)⟩
  have hres : ∀ x : P, ∃ a : O, x - algebraMap O P a ∈ maximalIdeal P := fun x =>
    ⟨MvPowerSeries.constantCoeff x, fun h => by
      rw [← h5] at h
      simpa using MvPowerSeries.isUnit_iff_constantCoeff.1 h⟩
  let φ : P →ₐ[O] P ⧸ T := Ideal.Quotient.mkₐ O T
  have hφ : Function.Surjective φ := Ideal.Quotient.mk_surjective
  have hφ0 : ∀ x, φ x = 0 ↔ x ∈ T := fun x => Ideal.Quotient.eq_zero_iff_mem
  haveI : IsCO O (P ⧸ T) := isCO_of_surj hres φ hφ
  let 𝒜 : ℤ → Submodule O (P ⧸ T) := fun j => (wtPart O W.wt j).map φ.toLinearMap
  have hsum : ∀ x : P, ∃ S : Finset ℤ, φ x = ∑ j ∈ S, φ (wcomp O W.wt j x) := fun x => by
    obtain ⟨S, hS⟩ := exists_sub_sum_mem_Tr (maximalIdeal O) N W.wt x
    exact ⟨S, by rw [← map_sum, ← sub_eq_zero, ← map_sub, hφ0]; exact hS⟩
  obtain ⟨gr⟩ : Nonempty (GradedAlgebra 𝒜) :=
    nonempty_gradedAlgebra_map (wtPart O W.wt) (wcomp O W.wt) (fun j x hx => wcomp_of_mem _ hx)
      (fun i j h x hx => wcomp_of_ne _ h hx) φ
      (fun j x hx => (hφ0 _).2 (isHomog_Tr _ N W.wt x ((hφ0 _).1 hx) j)) (by
        rw [eq_top_iff]
        intro y _
        obtain ⟨x, rfl⟩ := hφ y
        obtain ⟨S, hS⟩ := hsum x
        rw [hS]
        exact Submodule.sum_mem _ fun j _ => Submodule.mem_iSup_of_mem j ⟨_, wcomp_mem O W.wt j x, rfl⟩)
  have hJb : (J.map φ).IsHomogeneous 𝒜 := by
    refine Ideal.IsHomogeneous.iff_exists 𝒜 _ |>.2 ⟨{x | x.1 ∈ J.map φ}, le_antisymm (fun y hy => ?_) ?_⟩
    · obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 hy
      obtain ⟨S, hS⟩ := hsum x
      rw [hS]
      exact Ideal.sum_mem _ fun j _ => Ideal.subset_span
        ⟨⟨_, j, ⟨_, wcomp_mem O W.wt j x, rfl⟩⟩, Ideal.mem_map_of_mem φ (W.homog x hx j), rfl⟩
    · exact Ideal.span_le.2 (by rintro _ ⟨x, hx, rfl⟩; exact hx)
  haveI hφl : IsLocalHom (φ : P →+* P ⧸ T) := IsLocalHom.of_surjective _ hφ
  have hJbm : J.map φ ≤ maximalIdeal (P ⧸ T) :=
    Ideal.map_le_iff_le_comap.2 fun x hx => map_nonunit (φ : P →+* P ⧸ T) x (hJm hx)
  obtain ⟨f, hf, hle⟩ := exists_gens 𝒜 hJb (fun j => Module.finrank (ResidueField O) (F.Ob j)) fun j => by
    set K := Kj 𝒜 (J.map φ) j with hK
    have hKJ : K ≤ J.map φ := Kj_le 𝒜 _ j
    have hne : J.map φ ≠ ⊤ := ne_top_of_le_ne_top (maximalIdeal.isMaximal _).ne_top hJbm
    haveI : Finite ((P ⧸ T) ⧸ K) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    haveI : Finite ((P ⧸ T) ⧸ J.map φ) := Finite.of_surjective _ Ideal.Quotient.mk_surjective
    haveI : Nontrivial ((P ⧸ T) ⧸ K) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_le_ne_top hne hKJ)
    haveI : Nontrivial ((P ⧸ T) ⧸ J.map φ) := Ideal.Quotient.nontrivial_iff.2 hne
    haveI : IsCO O ((P ⧸ T) ⧸ K) :=
      isCO_of_surj IsCO.res_surj (Ideal.Quotient.mkₐ O K) Ideal.Quotient.mk_surjective
    haveI : IsCO O ((P ⧸ T) ⧸ J.map φ) :=
      isCO_of_surj IsCO.res_surj (Ideal.Quotient.mkₐ O (J.map φ)) Ideal.Quotient.mk_surjective
    obtain ⟨gr'⟩ := nonempty_gradedAlgebra_quot 𝒜 (Ideal.Quotient.mkₐ O K) Ideal.Quotient.mk_surjective
      (by
        rw [show RingHom.ker (Ideal.Quotient.mkₐ O K) = K from Ideal.mk_ker]
        exact Kj_isHomogeneous 𝒜 hJb j)
    let p : ((P ⧸ T) ⧸ K) →ₐ[O] ((P ⧸ T) ⧸ J.map φ) := Ideal.Quotient.factorₐ O hKJ
    have hp : Function.Surjective p := Ideal.Quotient.factor_surjective hKJ
    have hker : RingHom.ker p = (J.map φ).map (Ideal.Quotient.mk K) := by
      ext y
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [Ideal.mem_quotient_iff_mem hKJ]
      exact Ideal.Quotient.eq_zero_iff_mem
    rw [← hker]
    refine card_ker_le F hF hv hc g₁ hg u hu W hW hm
      (fun i => (𝒜 i).map (Ideal.Quotient.mkₐ O K).toLinearMap) p j hp
      ⟨inferInstance, ?_, le_maximalIdeal (RingHom.ker_ne_top _), fun y hy => ?_⟩
      ((Ideal.Quotient.mkₐ O K).comp φ) (Ideal.Quotient.mk_surjective.comp hφ)
      (fun i g hg => ⟨_, ⟨g, hg, rfl⟩, rfl⟩) ?_
    · rw [eq_bot_iff, Ideal.mul_le]
      intro x hx y hy
      obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective x
      obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hker, Ideal.mem_quotient_iff_mem hKJ] at hy
      have hw : w ∈ maximalIdeal (P ⧸ T) := fun h => hx (h.map _)
      rw [Ideal.mem_bot, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_sup_left (Ideal.mul_mem_mul hw hy)
    · obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective y
      rw [hker, Ideal.mem_quotient_iff_mem hKJ] at hy
      exact ⟨_, SetLike.coe_mem _, (Ideal.Quotient.eq.2 (sub_decompose_mem_Kj 𝒜 hJb j hy)).symm⟩
    · rw [hker]
      exact Ideal.map_map (φ : P →+* P ⧸ T) (Ideal.Quotient.mk K)
  have hl : ∀ j i, ∃ g : P, (g ∈ J ∧ g ∈ wtPart O W.wt j) ∧ φ g = f j i := fun j i => by
    obtain ⟨x, hx, e⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 (hf j i).1
    obtain ⟨y, hy, e'⟩ := (hf j i).2
    have e'' : φ y = f j i := e'
    refine ⟨wcomp O W.wt j x, ⟨W.homog x hx j, wcomp_mem O W.wt j x⟩, ?_⟩
    have h1 : x - y ∈ T := (hφ0 _).1 (by rw [map_sub, e, e'', sub_self])
    have h2 := (hφ0 _).2 (isHomog_Tr _ N W.wt _ h1 j)
    rw [map_sub, map_sub, wcomp_of_mem _ hy, sub_eq_zero] at h2
    rw [h2, e'']
  choose g hgm hgf using hl
  refine ⟨g, fun j i => (hgm j i).2, ?_⟩
  set S := Ideal.span (⋃ j, Set.range (g j)) with hS
  have hSJ : S ≤ J := Ideal.span_le.2 (Set.iUnion_subset fun j => by rintro _ ⟨i, rfl⟩; exact (hgm j i).1)
  refine le_antisymm ?_ hSJ
  refine Submodule.le_of_le_smul_of_le_jacobson_bot (I := maximalIdeal P) (IsNoetherian.noetherian _)
    (maximalIdeal_le_jacobson _) fun x hx => ?_
  have h1 : Ideal.span (⋃ j, Set.range (f j)) ⊔ maximalIdeal (P ⧸ T) * J.map φ ≤
      (S ⊔ maximalIdeal P * J).map φ := by
    rw [Ideal.map_sup, Ideal.map_mul]
    refine sup_le_sup (Ideal.span_le.2 (Set.iUnion_subset fun j => ?_)) (Ideal.mul_mono_left fun y hy => ?_)
    · rintro _ ⟨i, rfl⟩
      rw [← hgf]
      exact Ideal.mem_map_of_mem φ (Ideal.subset_span (Set.mem_iUnion.2 ⟨j, i, rfl⟩))
    · obtain ⟨w, rfl⟩ := hφ y
      exact Ideal.mem_map_of_mem φ (show w ∈ maximalIdeal P from fun h => hy (h.map φ))
  obtain ⟨y, hy, e⟩ := (Ideal.mem_map_iff_of_surjective φ hφ).1 (h1 (hle (Ideal.mem_map_of_mem φ hx)))
  have h2 : x - y ∈ T := (hφ0 _).1 (by rw [map_sub, e, sub_self])
  have h3 : x - y ∈ maximalIdeal P * J := hN ⟨hT h2, sub_mem hx (sup_le hSJ Ideal.mul_le_right hy)⟩
  rw [← add_sub_cancel y x]
  exact add_mem hy (Ideal.mem_sup_right h3)
