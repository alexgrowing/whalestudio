import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsNormalSchemeSp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.KbIsAlgClosedAndConj
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AlgHomEqOfReductionEqOfCoordsEq
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZJ

noncomputable section
namespace GlobalTheory.ZJ

theorem sub_const_mem_span {S L k : Type} [CommRing S] [IsLocalRing S] [CommRing L] [_root_.IsReduced L]
    [Field k] (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (κ : k →+* L) (ε : L →+* k) (hεκ : ∀ x, ε (κ x) = x) (hu : ∀ x, ε x ≠ 0 → IsUnit x)
    (ψ : S →+* L) {g : ℕ} (v : Fin g → S) (J : Ideal S) (hJ : ∀ x ∈ J, ψ x = 0)
    (hm : IsLocalRing.maximalIdeal S = Ideal.span (Set.range v) ⊔ J.radical) (a : S) :
    ψ a - κ (ε (ψ a)) ∈ Ideal.span (Set.range fun i => ψ (v i)) := by
  have h0 : ∀ b : S, ε (ψ b) = 0 → ψ b ∈ Ideal.span (Set.range fun i => ψ (v i)) := by
    intro b hb
    have hbm : b ∈ IsLocalRing.maximalIdeal S := by
      intro hub
      exact ((hub.map ψ).map ε).ne_zero hb
    have hle : IsLocalRing.maximalIdeal S ≤ (Ideal.span (Set.range fun i => ψ (v i))).comap ψ := by
      rw [hm]
      refine sup_le (Ideal.span_le.2 ?_) ?_
      · rintro _ ⟨i, rfl⟩
        exact Ideal.subset_span ⟨i, rfl⟩
      · rintro x ⟨n, hn⟩
        have : IsNilpotent (ψ x) := ⟨n, by rw [← map_pow]; exact hJ _ hn⟩
        rw [Ideal.mem_comap, this.eq_zero]
        exact Ideal.zero_mem _
    exact hle hbm
  by_cases ha : ε (ψ a) = 0
  · rw [ha, map_zero, sub_zero]
    exact h0 a ha
  obtain ⟨n, hn, hn'⟩ := hk _ ha
  have hfin : IsOfFinOrder (ε (ψ a)) := isOfFinOrder_iff_pow_eq_one.2 ⟨n, hn, hn'⟩
  have hpos := hfin.orderOf_pos
  have hprim := IsPrimitiveRoot.orderOf (ε (ψ a))
  have h1 := pow_orderOf_eq_one (ε (ψ a))
  generalize orderOf (ε (ψ a)) = m at hpos hprim h1
  have : NeZero m := ⟨hpos.ne'⟩
  have hm0 : (m : k) ≠ 0 := hprim.neZero'.ne
  have h2 := h0 (a ^ m - 1) (by simp [h1])
  have h3 := Commute.mul_geom_sum₂ (Commute.all (ψ a) (κ (ε (ψ a)))) m
  have h4 : IsUnit (∑ i ∈ Finset.range m, ψ a ^ i * κ (ε (ψ a)) ^ (m - 1 - i)) := by
    apply hu
    simp only [map_sum, map_mul, map_pow, hεκ]
    rw [geom_sum₂_self]
    exact mul_ne_zero hm0 (pow_ne_zero _ ha)
  rw [← Ideal.mul_unit_mem_iff_mem _ h4, h3, ← map_pow κ, h1]
  simpa using h2

theorem exists_reduced_fibre_localRing {O B : Type} [CommRing O] [IsLocalRing O] [CommRing B] [Algebra O B]
    [Algebra.Smooth O B] (s : B →ₐ[O] O) :
    ∃ (L : Type) (_ : CommRing L) (_ : IsLocalRing L) (_ : _root_.IsReduced L) (π : B →+* L)
      (κ : IsLocalRing.ResidueField O →+* L) (ε : L →+* IsLocalRing.ResidueField O),
      π.comp (algebraMap O B) = κ.comp (IsLocalRing.residue O) ∧
      ε.comp π = (IsLocalRing.residue O).comp s ∧ (∀ x, ε (κ x) = x) ∧ (∀ x, ε x ≠ 0 → IsUnit x) ∧
      ∀ (I : Ideal B) (b : B), π b ∈ I.map π → ∃ t : B, IsUnit (s t) ∧
        t * b ∈ I ⊔ (IsLocalRing.maximalIdeal O).map (algebraMap O B) := by
  let M : Ideal B := (IsLocalRing.maximalIdeal O).map (algebraMap O B)
  let D := B ⧸ M
  have hD : _root_.IsReduced D := by
    have : _root_.IsReduced (TensorProduct O (IsLocalRing.ResidueField O) B) :=
      GlobalTheory.isReduced_algebra_of_smooth_of_isReduced (IsLocalRing.ResidueField O) _
    have e := Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (IsLocalRing.maximalIdeal O)
    have e' := Algebra.TensorProduct.comm O B (IsLocalRing.ResidueField O)
    exact isReduced_of_injective (e.toRingEquiv.trans e'.toRingEquiv) (RingEquiv.injective _)
  let ε₀ : D →+* IsLocalRing.ResidueField O :=
    Ideal.Quotient.lift M ((IsLocalRing.residue O).comp s) (by
      intro b hb
      have : M ≤ RingHom.ker ((IsLocalRing.residue O).comp (s : B →+* O)) := by
        rw [Ideal.map_le_iff_le_comap]
        intro x hx
        simpa [RingHom.mem_ker, IsLocalRing.residue_eq_zero_iff] using hx
      exact this hb)
  let q : Ideal D := RingHom.ker ε₀
  have hq : q.IsPrime := RingHom.ker_isPrime _
  let L := Localization.AtPrime q
  have hε : ∀ y : q.primeCompl, IsUnit (ε₀ y) := fun y => Ne.isUnit y.2
  let ε : L →+* IsLocalRing.ResidueField O := IsLocalization.lift hε
  let κ₀ : IsLocalRing.ResidueField O →+* D :=
    Ideal.quotientMap M (algebraMap O B) Ideal.le_comap_map
  refine ⟨L, inferInstance, inferInstance, inferInstance, (algebraMap D L).comp (Ideal.Quotient.mk M),
    (algebraMap D L).comp κ₀, ε, rfl, ?_, ?_, ?_, ?_⟩
  · ext b
    simp only [ε, RingHom.comp_apply, IsLocalization.lift_eq]
    rfl
  · intro x
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective x
    have : κ₀ (IsLocalRing.residue O x) = Ideal.Quotient.mk M (algebraMap O B x) := rfl
    simp only [ε, RingHom.comp_apply, IsLocalization.lift_eq, this]
    exact congrArg (IsLocalRing.residue O) (s.commutes x)
  · intro x hx
    obtain ⟨⟨d, t⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl x
    rw [IsLocalization.AtPrime.isUnit_mk'_iff L q]
    intro hd
    apply hx
    simp only [ε]
    rw [IsLocalization.lift_mk'_spec]
    rw [mul_zero]
    exact hd
  · intro I b hb
    rw [← Ideal.map_map, RingHom.comp_apply,
      IsLocalization.algebraMap_mem_map_algebraMap_iff q.primeCompl] at hb
    obtain ⟨t, ht, hb⟩ := hb
    obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective t
    refine ⟨t, ?_, ?_⟩
    · rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      exact ht
    · rw [← map_mul, ← Ideal.mem_comap, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective] at hb
      simpa [← RingHom.ker_eq_comap_bot] using hb

def ptVal {X : Scheme.{0}} (W : X.Opens) {L : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme) : Γ(X, W) ⟶ L :=
  W.topIso.inv ≫ m.appTop ≫ (Scheme.ΓSpecIso L).hom

theorem ptVal_comp {X : Scheme.{0}} (W : X.Opens) {L L' : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme)
    (φ : L ⟶ L') : ptVal W (Spec.map φ ≫ m) = ptVal W m ≫ φ := by
  simp only [ptVal, Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality]

theorem comp_toSpecΓ_eq {X : Scheme.{0}} (W : X.Opens) {L : CommRingCat.{0}} (m : Spec L ⟶ W.toScheme) :
    m ≫ W.toSpecΓ = Spec.map (ptVal W m) := by
  rw [Scheme.Opens.toSpecΓ, Scheme.toSpecΓ_naturality_assoc, ← SpecMap_ΓSpecIso_hom, ptVal,
    Spec.map_comp, Spec.map_comp, Category.assoc]

theorem exists_stalk_hom {X : Scheme.{0}} (W : X.Opens) (w : X) (hw : w ∈ W) {L : CommRingCat.{0}}
    [IsLocalRing L] (m : Spec L ⟶ W.toScheme) (hm : (m ≫ W.ι) (IsLocalRing.closedPoint L) = w) :
    ∃ ψ : X.presheaf.stalk w ⟶ L, IsLocalHom ψ.hom ∧ Spec.map ψ ≫ X.fromSpecStalk w = m ≫ W.ι ∧
      X.presheaf.germ W w hw ≫ ψ = ptVal W m := by
  subst hm
  have h := Scheme.Spec_stalkClosedPointTo_fromSpecStalk (m ≫ W.ι)
  refine ⟨Scheme.stalkClosedPointTo (m ≫ W.ι), inferInstance, h, ?_⟩
  apply Spec.map_injective
  rw [← comp_toSpecΓ_eq, Spec.map_comp, ← Scheme.Opens.fromSpecStalkOfMem_toSpecΓ, ← Category.assoc]
  congr 1
  rw [← cancel_mono W.ι, Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι, h]

theorem const_mod_coord {G Z : Scheme.{0}} (q : G ⟶ Z) (W : G.Opens) (w : G) (hw : w ∈ W) {g : ℕ}
    (u : Fin g → Γ(G, W))
    (hc : IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom).radical)
    {L k : Type} [CommRing L] [IsLocalRing L] [_root_.IsReduced L]
    [Field k] (hk : ∀ x : k, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (κ : k →+* L) (ε : L →+* k) (hεκ : ∀ x, ε (κ x) = x) (hu : ∀ x, ε x ≠ 0 → IsUnit x)
    (m : Sp L ⟶ W.toScheme) (hm : (m ≫ W.ι) (IsLocalRing.closedPoint L) = w)
    (t : Sp k ⟶ Z) (ht : m ≫ W.ι ≫ q = spMap κ ≫ t) (I : Ideal L)
    (hI : I = Ideal.span (Set.range fun i => (ptVal W m).hom (u i))) :
    spMap (Ideal.Quotient.mk I) ≫ m ≫ W.ι =
      spMap (Ideal.Quotient.mk I) ≫ spMap κ ≫ spMap ε ≫ m ≫ W.ι := by
  obtain ⟨ψ, hψ, h1, h2⟩ := exists_stalk_hom W w hw (L := .of L) m hm
  have hκε : spMap ε ≫ spMap κ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact hεκ x
  have h3 : q.stalkMap w ≫ ψ =
      q.stalkMap w ≫ ψ ≫ CommRingCat.ofHom ε ≫ CommRingCat.ofHom κ := by
    apply Spec.map_injective
    rw [← cancel_mono (Z.fromSpecStalk (q w))]
    simp only [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk]
    rw [reassoc_of% h1, ht, reassoc_of% hκε]
  have h4 : ∀ x ∈ (IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom,
      ψ.hom x = 0 := by
    intro x hx
    have : (IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom ≤ RingHom.ker ψ.hom := by
      rw [Ideal.map_le_iff_le_comap]
      intro r hr
      have e : ψ.hom ((q.stalkMap w).hom r) = κ (ε (ψ.hom ((q.stalkMap w).hom r))) :=
        congr(($h3).hom r)
      change ψ.hom ((q.stalkMap w).hom r) = 0
      by_cases h0 : ε (ψ.hom ((q.stalkMap w).hom r)) = 0
      · rw [e, h0, map_zero]
      · exact absurd (IsUnit.of_map _ _ (IsUnit.of_map _ _ (hu _ h0))) hr
    exact this hx
  have h5 := sub_const_mem_span hk κ ε hεκ hu ψ.hom _ _ h4 hc
  rw [← h1]
  simp only [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext a
  change Ideal.Quotient.mk I (ψ.hom a) = Ideal.Quotient.mk I (κ (ε (ψ.hom a)))
  rw [Ideal.Quotient.eq, hI, ← h2]
  exact h5 a

theorem spMap_comp_closedPoint {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (φ : R →+* S) [IsLocalHom φ] {X : Scheme.{0}} (d : Sp R ⟶ X) :
    (spMap φ ≫ d) (IsLocalRing.closedPoint S) = d (IsLocalRing.closedPoint R) :=
  (Scheme.Hom.comp_apply _ _ _).trans
    (congrArg d (Spec_closedPoint (R := .of R) (S := .of S) (f := CommRingCat.ofHom φ)))

theorem section_eq_of_coord {G Z X : Scheme.{0}} (q : G ⟶ Z) (W : G.Opens) (w : G) (hw : w ∈ W) {g : ℕ}
    (u : Fin g → Γ(G, W))
    (hc : IsLocalRing.maximalIdeal (G.presheaf.stalk w) =
      Ideal.span (Set.range fun i => (G.presheaf.germ W w hw).hom (u i)) ⊔
      ((IsLocalRing.maximalIdeal (Z.presheaf.stalk (q w))).map (q.stalkMap w).hom).radical)
    {O : Type} [CommRing O] [IsLocalRing O]
    (hk : ∀ x : IsLocalRing.ResidueField O, x ≠ 0 → ∃ n : ℕ, 1 ≤ n ∧ x ^ n = 1)
    (x : X ⟶ Sp O) [Smooth x] (F : X ⟶ G) (y : Sp O ⟶ Z) (hF : F ≫ q = x ≫ y)
    (hmono : ∀ (T : Scheme.{0}) (α β : T ⟶ X) (r : T ⟶ Sp (IsLocalRing.ResidueField O)),
      α ≫ x = r ≫ spMap (IsLocalRing.residue O) → β ≫ x = r ≫ spMap (IsLocalRing.residue O) →
      α ≫ F = β ≫ F → α = β)
    (c c' : Sp O ⟶ X) (hcx : c ≫ x = 𝟙 _) (hcx' : c' ≫ x = 𝟙 _) (a a' : Sp O ⟶ W.toScheme)
    (ha : c ≫ F = a ≫ W.ι) (ha' : c' ≫ F = a' ≫ W.ι)
    (hw' : (a ≫ W.ι) (IsLocalRing.closedPoint O) = w)
    (hr : spMap (IsLocalRing.residue O) ≫ a = spMap (IsLocalRing.residue O) ≫ a')
    (hu : ∀ i, (ptVal W a).hom (u i) = (ptVal W a').hom (u i)) : c = c' := by
  have hcr : spMap (IsLocalRing.residue O) ≫ c = spMap (IsLocalRing.residue O) ≫ c' :=
    hmono _ _ _ (𝟙 _) (by simp [hcx]) (by simp [hcx']) (by simp only [Category.assoc, ha, ha', reassoc_of% hr])
  have hpt : ∀ d : Sp O ⟶ X, d (IsLocalRing.closedPoint O) =
      (spMap (IsLocalRing.residue O) ≫ d) (IsLocalRing.closedPoint (IsLocalRing.ResidueField O)) :=
    fun d => (spMap_comp_closedPoint _ d).symm
  have hcc : c' (IsLocalRing.closedPoint O) = c (IsLocalRing.closedPoint O) := by
    rw [hpt, hpt, hcr]
  obtain ⟨B, jj, _, hjj, hjjW⟩ := Scheme.exists_affine_mem_range_and_range_subset
    (x := c (IsLocalRing.closedPoint O)) (U := F ⁻¹ᵁ W) (by
      change F (c _) ∈ W
      have e : F (c (IsLocalRing.closedPoint O)) = w :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans (by rw [ha]; exact hw')
      exact e ▸ hw)
  have hrange : ∀ d : Sp O ⟶ X, d (IsLocalRing.closedPoint O) ∈ Set.range jj → Set.range d ⊆ Set.range jj := by
    rintro d hd _ ⟨z, rfl⟩
    have := Scheme.preimage_eq_top_of_closedPoint_mem (R := .of O) d (U := jj.opensRange) hd
    have hz : z ∈ d ⁻¹ᵁ jj.opensRange := by rw [this]; trivial
    exact hz
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (jj ≫ x)
  obtain ⟨σ, hσ⟩ := Spec.map_surjective (IsOpenImmersion.lift jj c (hrange c hjj))
  obtain ⟨σ', hσ'⟩ := Spec.map_surjective (IsOpenImmersion.lift jj c' (hrange c' (hcc ▸ hjj)))
  replace hσ : Spec.map σ ≫ jj = c := by rw [hσ, IsOpenImmersion.lift_fac]
  replace hσ' : Spec.map σ' ≫ jj = c' := by rw [hσ', IsOpenImmersion.lift_fac]
  let n : Spec B ⟶ W.toScheme := IsOpenImmersion.lift W.ι (jj ≫ F) (by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hjjW ⟨z, rfl⟩)
  have hn : n ≫ W.ι = jj ≫ F := IsOpenImmersion.lift_fac _ _ _
  have hna : Spec.map σ ≫ n = a := by
    rw [← cancel_mono W.ι, Category.assoc, hn, reassoc_of% hσ, ha]
  have hna' : Spec.map σ' ≫ n = a' := by
    rw [← cancel_mono W.ι, Category.assoc, hn, reassoc_of% hσ', ha']
  let _ : Algebra O B := φ.hom.toAlgebra
  have hsm : Algebra.Smooth O B := by
    have : Smooth (Spec.map φ) := by rw [hφ]; infer_instance
    exact (HasRingHomProperty.Spec_iff (P := @Smooth)).1 this
  have hsec : ∀ (τ : B ⟶ CommRingCat.of O) (d : Sp O ⟶ X), Spec.map τ ≫ jj = d → d ≫ x = 𝟙 _ →
      ∀ r : O, τ.hom (φ.hom r) = r := by
    intro τ d h1 h2 r
    have : φ ≫ τ = 𝟙 _ := by
      apply Spec.map_injective
      rw [Spec.map_comp, hφ, reassoc_of% h1, h2, Spec.map_id]
    exact congr(($this).hom r)
  let s : B →ₐ[O] O := ⟨σ.hom, hsec σ c hσ hcx⟩
  let s' : B →ₐ[O] O := ⟨σ'.hom, hsec σ' c' hσ' hcx'⟩
  obtain ⟨L, _, _, _, π, κ, ε, h1, h2, h3, h4, h5⟩ := exists_reduced_fibre_localRing s
  have e1 : Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ Spec.map φ =
      spMap κ ≫ spMap (IsLocalRing.residue O) := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) h1
  have e2 : spMap ε ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) =
      spMap (IsLocalRing.residue O) ≫ Spec.map σ := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg (fun t => Spec.map (CommRingCat.ofHom t)) h2
  have e3 : spMap ε ≫ spMap κ = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext x
    exact h3 x
  have hεloc : IsLocalHom ε := ⟨fun z hz => h4 z hz.ne_zero⟩
  have hm : ((Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ n) ≫ W.ι) (IsLocalRing.closedPoint L) = w := by
    refine (spMap_comp_closedPoint ε _).symm.trans ?_
    rw [Category.assoc, reassoc_of% e2, reassoc_of% hna]
    exact (spMap_comp_closedPoint _ _).trans hw'
  let uB : Fin g → B := fun i => (ptVal W n).hom (u i)
  have hI : (Ideal.span (Set.range uB)).map π = Ideal.span (Set.range fun i =>
      (ptVal W (Spec.map (CommRingCat.ofHom π : B ⟶ .of L) ≫ n)).hom (u i)) := by
    rw [Ideal.map_span, ← Set.range_comp, ptVal_comp]
    rfl
  have key := const_mod_coord q W w hw u hc hk κ ε h3 h4 _ hm (spMap (IsLocalRing.residue O) ≫ y)
    (by rw [Category.assoc, reassoc_of% hn, hF, reassoc_of% hφ.symm, reassoc_of% e1]) _ hI
  generalize hI' : (Ideal.span (Set.range uB)).map π = I at key
  have key2 : spMap (Ideal.Quotient.mk I) ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) =
      spMap (Ideal.Quotient.mk I) ≫ spMap κ ≫ spMap ε ≫ Spec.map (CommRingCat.ofHom π : B ⟶ .of L) := by
    rw [← cancel_mono jj]
    refine hmono _ _ _ (spMap (Ideal.Quotient.mk I) ≫ spMap κ) ?_ ?_ ?_
    · simp only [Category.assoc, ← hφ, e1]
    · simp only [Category.assoc, ← hφ, e1, reassoc_of% e3]
    · simpa only [Category.assoc, hn] using key
  have key3 : ∀ b : B, π b - κ (ε (π b)) ∈ I := by
    intro b
    simp only [← Spec.map_comp] at key2
    rw [← Ideal.Quotient.eq]
    exact congr(($(Spec.map_injective key2)).hom b)
  have hsu : ∀ i, s (uB i) ∈ IsLocalRing.maximalIdeal O := by
    intro i
    obtain ⟨ψ, hψ, -, h⟩ := exists_stalk_hom W w hw (L := .of O) a hw'
    have e : s (uB i) = ψ.hom ((G.presheaf.germ W w hw).hom (u i)) := by
      have := ptVal_comp W n σ
      rw [hna, ← h] at this
      exact (congr(($this).hom (u i))).symm
    rw [e]
    refine map_nonunit ψ.hom _ ?_
    rw [hc]
    exact Ideal.mem_sup_left (Ideal.subset_span ⟨i, rfl⟩)
  have hss : s = s' := by
    refine GlobalTheory.algHom_eq_of_reduction_eq_of_coords_eq O B s s' g uB ?_ ?_ ?_
    · intro b
      have : σ ≫ CommRingCat.ofHom (IsLocalRing.residue O) = σ' ≫ CommRingCat.ofHom (IsLocalRing.residue O) := by
        apply Spec.map_injective
        rw [← cancel_mono jj]
        simp only [Spec.map_comp, Category.assoc, hσ, hσ', hcr]
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, sub_eq_zero]
      exact congr(($this).hom b)
    · intro i
      have := hu i
      rw [← hna, ← hna', ptVal_comp, ptVal_comp] at this
      exact this
    · intro b hb
      have hb' : ε (π b) = 0 := by
        have : ε (π b) = IsLocalRing.residue O (s b) := congr($h2 b)
        rw [this, hb, map_zero]
      have := key3 b
      rw [hb', map_zero, sub_zero, ← hI'] at this
      obtain ⟨t, ht, htb⟩ := h5 _ _ this
      refine ⟨t, ht, SetLike.le_def.1 ?_ htb⟩
      refine sup_le (Ideal.span_le.2 ?_) le_sup_right
      rintro _ ⟨i, rfl⟩
      have : uB i = (uB i - algebraMap O B (s (uB i))) + algebraMap O B (s (uB i)) := by ring
      rw [SetLike.mem_coe, this]
      refine Ideal.add_mem _ (Ideal.mem_sup_left (Ideal.subset_span ⟨i, ?_⟩))
        (Ideal.mem_sup_right (Ideal.mem_map_of_mem _ ?_))
      · simp
      · simpa using hsu i
  have : σ = σ' := by
    ext b
    exact congr($hss b)
  rw [← hσ, ← hσ', this]

theorem classical_eq_of_coord : ∀ C : Core, C.HasTests → C.Fib → ∀ (w : C.G.toScheme) (W : C.G.toScheme.Opens) (hw : w ∈ W) (u : Fin C.g → Γ(C.G.toScheme, W)), C.Coord w W hw u → ∀ (p : ℕ) [Fact p.Prime] (a a' : Sp (OO p) ⟶ W.toScheme), C.Cl (a ≫ W.ι ≫ C.GG.hom) → a ≫ W.ι ≫ C.GG.hom = a' ≫ W.ι ≫ C.GG.hom → a (cPt p) = ⟨w, hw⟩ → rPt p ≫ a = rPt p ≫ a' → (∀ i, a.appTop.hom (W.topIso.inv.hom (u i)) = a'.appTop.hom (W.topIso.inv.hom (u i))) → a = a' := by
  intro C hT _ w W hw u hC p _ a a' hcl hy hx hr hu
  obtain ⟨τ⟩ := hT p _ hcl
  obtain ⟨c, hc1, hc2⟩ := τ.lift (a ≫ W.ι) (Category.assoc _ _ _)
  obtain ⟨c', hc1', hc2'⟩ := τ.lift (a' ≫ W.ι) ((Category.assoc _ _ _).trans hy.symm)
  have := τ.smooth
  have : Smooth τ.H.hom := SmoothOfRelativeDimension.smooth C.g _
  have hfac := τ.fac
  have hfo := τ.f_over
  have himm := τ.imm
  have key := section_eq_of_coord C.GG.hom W w hw u hC (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).2.1
    (pullback.snd τ.H.hom (spMap τ.j)) (pullback.fst _ _ ≫ τ.f) (a ≫ W.ι ≫ C.GG.hom)
    (by rw [Category.assoc, hfo, pullback.condition_assoc, hfac]) ?_
    (pullback.lift c (𝟙 _) (by simp [hc1])) (pullback.lift c' (𝟙 _) (by simp [hc1']))
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) a a'
    (by rw [pullback.lift_fst_assoc, hc2]) (by rw [pullback.lift_fst_assoc, hc2'])
    ((Scheme.Hom.comp_apply _ _ _).trans (congrArg Subtype.val hx)) hr
    (fun i => congrArg (Scheme.ΓSpecIso (.of (OO p))).hom.hom (hu i))
  · have : c = c' := by simpa only [pullback.lift_fst] using congr($key ≫ pullback.fst _ _)
    rw [← cancel_mono W.ι, ← hc2, ← hc2', this]
  · intro T α β r hα hβ hF
    let h : pullback τ.H.hom (rPt p ≫ spMap τ.j) ⟶ pullback C.GG.hom (rPt p ≫ a ≫ W.ι ≫ C.GG.hom) :=
      pullback.lift (pullback.fst _ _ ≫ τ.f) (pullback.snd _ _) (by
        rw [Category.assoc, hfo, pullback.condition_assoc, Category.assoc, hfac])
    have h1 : h ≫ pullback.fst _ _ = pullback.fst _ _ ≫ τ.f := pullback.lift_fst _ _ _
    have h2 : h ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _
    have := himm h h1 h2
    have e : pullback.lift (f := τ.H.hom) (g := rPt p ≫ spMap τ.j) (α ≫ pullback.fst _ _) r
          (by rw [Category.assoc, pullback.condition, reassoc_of% hα]) =
        pullback.lift (β ≫ pullback.fst _ _) r
          (by rw [Category.assoc, pullback.condition, reassoc_of% hβ]) := by
      rw [← cancel_mono h]
      apply pullback.hom_ext
      · simp only [Category.assoc, h1, pullback.lift_fst_assoc, hF]
      · simp only [Category.assoc, h2, pullback.lift_snd]
    apply pullback.hom_ext
    · simpa only [pullback.lift_fst] using congr($e ≫ pullback.fst _ _)
    · rw [hα, hβ]

end GlobalTheory.ZJ
end
