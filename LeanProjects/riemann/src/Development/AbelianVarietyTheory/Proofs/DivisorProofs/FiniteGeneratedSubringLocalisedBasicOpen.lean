import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinSubRange
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem closure_pow_lift {L L' : Type*} [CommRing L] [CommRing L'] (ρ : L →+* L') (C : Subring L) (u : L)
    (hu : u ∈ C) (G : Set L') (hG : ∀ g ∈ G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * g) :
    ∀ z ∈ Subring.closure G, ∃ k : ℕ, ∃ w ∈ C, ρ w = ρ u ^ k * z := by
  intro z hz
  induction hz using Subring.closure_induction with
  | mem g hg => exact hG g hg
  | zero => exact ⟨0, 0, C.zero_mem, by simp⟩
  | one => exact ⟨0, 1, C.one_mem, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, u ^ l * w + u ^ k * v,
      C.add_mem (C.mul_mem (C.pow_mem hu _) hw) (C.mul_mem (C.pow_mem hu _) hv), ?_⟩
    rw [map_add, map_mul, map_mul, map_pow, map_pow, e, e']
    ring
  | neg a _ ha =>
    obtain ⟨k, w, hw, e⟩ := ha
    exact ⟨k, -w, C.neg_mem hw, by rw [map_neg, e]; ring⟩
  | mul a b _ _ ha hb =>
    obtain ⟨k, w, hw, e⟩ := ha
    obtain ⟨l, v, hv, e'⟩ := hb
    refine ⟨k + l, w * v, C.mul_mem hw hv, ?_⟩
    rw [map_mul, e, e']
    ring

theorem exists_pow_mul_res {S : Scheme.{0}} {U : S.Opens} (hc : IsCompact (U : Set S))
    (hq : IsQuasiSeparated (U : Set S)) (g : Γ(S, U)) (U' : S.Opens) (hle : U' ≤ U) (hU' : U' = S.basicOpen g)
    (a : Γ(S, U')) : ∃ (k : ℕ) (b : Γ(S, U)), (S.presheaf.map (homOfLE hle).op).hom b =
      (S.presheaf.map (homOfLE hle).op).hom g ^ k * a := by
  subst hU'
  letI := (S.presheaf.map (homOfLE (S.basicOpen_le g)).op).hom.toAlgebra
  have := isLocalization_basicOpen_of_qcqs hc hq g
  obtain ⟨⟨y, ⟨_, k, rfl⟩⟩, hy⟩ := IsLocalization.surj (Submonoid.powers g) a
  refine ⟨k, y, ?_⟩
  rw [← map_pow, mul_comm]
  simpa [RingHom.algebraMap_toAlgebra] using hy.symm

theorem presheaf_map_bijective_of_eq {X : Scheme.{0}} {A B : X.Opens} (h : B ≤ A) (e : A = B) :
    Function.Bijective (X.presheaf.map (homOfLE h).op).hom := by
  subst e
  have : homOfLE h = 𝟙 A := Subsingleton.elim _ _
  simpa [this] using Function.bijective_id

end GlobalTheory.Mum

namespace GlobalTheory.Mum

theorem finFam_basicOpen_loc : ∀ {S : Scheme.{0}} {K : Type} [Field K] (gp : Sp K ⟶ S) [IsLocallyNoetherian S] {r : ℕ} (V : Fin r → S.Opens)
    (t : ∀ i, Finset Γ(Sp K, gp ⁻¹ᵁ V i)) (W : S.Opens), IsAffineOpen W → ∀ (f : Γ(S, W))
    (x : Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f)), x ∈ finFam gp V t (S.basicOpen f) →
    ∃ (k : ℕ) (y : Γ(Sp K, gp ⁻¹ᵁ W)), y ∈ finFam gp V t W ∧
      resK gp (S.basicOpen_le f) y = resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ k * x := by
  intro S K _ gp _ r V t W hW f x hx
  haveI : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  let p : Sp K := (IsLocalRing.closedPoint K : PrimeSpectrum K)
  have pre : ∀ U U' : S.Opens, (gp.base p ∈ U ↔ gp.base p ∈ U') → gp ⁻¹ᵁ U = gp ⁻¹ᵁ U' := by
    intro U U' h
    ext q
    rw [Subsingleton.elim q p]
    exact h
  have bij : ∀ {U U' : S.Opens} (h : U' ≤ U), (gp.base p ∈ U ↔ gp.base p ∈ U') →
      Function.Bijective (resK gp h) := fun h e => presheaf_map_bijective_of_eq _ (pre _ _ e)
  by_cases hs : gp.base p ∈ S.basicOpen f
  swap
  · have e : gp ⁻¹ᵁ S.basicOpen f = ⊥ := by
      ext q
      rw [Subsingleton.elim q p]
      exact ⟨fun h => (hs h).elim, fun h => by simp at h⟩
    haveI : Subsingleton Γ(Sp K, gp ⁻¹ᵁ S.basicOpen f) := by rw [e]; infer_instance
    exact ⟨0, 0, Subring.zero_mem _, Subsingleton.elim _ _⟩
  have hsW : gp.base p ∈ W := S.basicOpen_le f hs
  haveI : IsNoetherianRing Γ(S, W) := IsLocallyNoetherian.component_noetherian ⟨W, hW⟩
  have hNW : TopologicalSpace.NoetherianSpace (W : Set S) := noetherianSpace_of_isAffineOpen W hW
  have hcpt : ∀ T ⊆ (W : Set S), IsCompact T := (TopologicalSpace.noetherianSpace_set_iff _).mp hNW
  have hle : ∀ i, S.basicOpen f ⊓ V i ≤ W ⊓ V i := fun i => inf_le_inf_right _ (S.basicOpen_le f)
  rw [mem_finFam] at hx
  have step : ∀ i, ∃ k : ℕ, ∃ w ∈ Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
      resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)),
      resK gp (hle i) w = resK gp (hle i) (resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f)) ^ k *
        resK gp (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f) x := by
    intro i
    refine closure_pow_lift _ _ _ ?_ _ ?_ _ (hx i)
    · rw [resK_app]
      exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
    rintro _ (⟨a, rfl⟩ | ⟨c, hc, rfl⟩)
    · have hU' : S.basicOpen f ⊓ V i =
          S.basicOpen ((S.presheaf.map (homOfLE (inf_le_left : W ⊓ V i ≤ W)).op).hom f) := by
        rw [Scheme.basicOpen_res]
        exact le_antisymm (le_inf (le_inf (inf_le_left.trans (S.basicOpen_le f)) inf_le_right) inf_le_left)
          (le_inf inf_le_right (inf_le_left.trans inf_le_right))
      have hWi : (↑(W ⊓ V i) : Set S) ⊆ W := fun z hz => hz.1
      obtain ⟨k, b, e⟩ := exists_pow_mul_res (hcpt _ hWi)
        (fun A B hA _ _ hB _ _ => hcpt _ ((Set.inter_subset_left.trans hA).trans hWi)) _ _ (hle i) hU' a
      refine ⟨k, (gp.app (W ⊓ V i)).hom b, Subring.subset_closure (Or.inl ⟨_, rfl⟩), ?_⟩
      rw [resK_app, resK_app, resK_app, e, map_mul, map_pow, ← CommRingCat.comp_apply]
    · refine ⟨0, resK gp (inf_le_right : W ⊓ V i ≤ V i) c, Subring.subset_closure (Or.inr ⟨c, hc, rfl⟩), ?_⟩
      rw [pow_zero, _root_.one_mul, resK_resK]
  choose k w hw e using step
  let N := Finset.univ.sup k
  obtain ⟨y, hy⟩ := (bij (S.basicOpen_le f) ⟨fun _ => hs, fun _ => hsW⟩).2
    (resK gp (S.basicOpen_le f) ((gp.app W).hom f) ^ N * x)
  refine ⟨N, y, ?_, hy⟩
  rw [mem_finFam]
  intro i
  have hki : k i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have hmem : resK gp (inf_le_left : W ⊓ V i ≤ W) ((gp.app W).hom f) ^ (N - k i) * w i ∈
      Subring.closure (Set.range (gp.app (W ⊓ V i)).hom ∪
        resK gp (inf_le_right : W ⊓ V i ≤ V i) '' (t i : Set _)) := by
    refine Subring.mul_mem _ (Subring.pow_mem _ ?_ _) (hw i)
    rw [resK_app]
    exact Subring.subset_closure (Or.inl ⟨_, rfl⟩)
  have inj := (bij (hle i) (by simp [hs, hsW])).1
  convert hmem using 1
  apply inj
  rw [map_mul, map_pow, e i, ← _root_.mul_assoc, ← pow_add, Nat.sub_add_cancel hki, resK_resK, resK_resK,
    ← resK_resK gp (S.basicOpen_le f) (inf_le_left : S.basicOpen f ⊓ V i ≤ S.basicOpen f), hy, map_mul, map_pow,
    resK_resK]

end GlobalTheory.Mum
