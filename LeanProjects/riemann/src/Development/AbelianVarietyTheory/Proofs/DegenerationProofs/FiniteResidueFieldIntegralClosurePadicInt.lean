import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.MemPadicAlgClValuationSubringIffNormLeOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FiniteOfIsClosedOfFiniteInterClosedPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SemiAbelianTorsionFiniteAndClosedPointFiniteOrde

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
local notation "OO" p:max => (Valuation.valuationSubring (Valued.v : Valuation (PadicAlgCl p) NNReal))
local notation "cPt" p:max => (IsLocalRing.closedPoint (OO p) : Sp (OO p))
local notation "gPt" p:max => spMap (ValuationSubring.subtype (OO p))

namespace GlobalTheory

namespace HomExtension

theorem finite_torsion_images
    (hab : ∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B →
      ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1})
    {Z : Scheme.{0}} (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (z : Z) {n : ℕ} (hn : 1 ≤ n) :
    {w : G.left | G.hom w = z ∧ ∃ (k : Type) (_ : Field k) (_ : Finite k) (t : Sp k ⟶ Z)
      (x : Over.mk t ⟶ G), x ^ n = 1 ∧ w ∈ Set.range x.left}.Finite := by
  let Ω : Type := AlgebraicClosure (Z.residueField z)
  let q : Sp Ω ⟶ Z :=
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) Ω)) ≫ Z.fromSpecResidueField z
  have := hG.comm
  have h1 := (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hab).1 Ω
    ((Over.pullback q).obj G) (hG.fibres Ω q) n hn
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G q) (𝟙 (Sp Ω)) q
    (Category.id_comp _).symm
  have h2 : Finite {x : Over.mk q ⟶ G // x ^ n = 1} := by
    have : Finite {x : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback q).obj G // x ^ n = 1} := h1
    refine Finite.of_injective (β := {x : Over.mk (𝟙 (Sp Ω)) ⟶ (Over.pullback q).obj G // x ^ n = 1})
      (fun x => ⟨e.symm x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (e.symm.injective (congrArg Subtype.val h))
  let pt : Sp Ω := (⊥ : PrimeSpectrum Ω)
  refine (Set.finite_range fun x : {x : Over.mk q ⟶ G // x ^ n = 1} => x.1.left pt).subset ?_
  rintro w ⟨hw, k, _, _, t, x, hx, s, rfl⟩
  obtain ⟨⟨z', ψ⟩, rfl⟩ := (Scheme.SpecToEquivOfField k Z).symm.surjective t
  have hz : z' = z := by
    rw [← hw, ← Scheme.Hom.comp_apply, Over.w x]
    exact (Z.fromSpecResidueField_apply z' _).symm
  subst hz
  letI : Algebra (Z.residueField z') k := ψ.hom.toAlgebra
  let τ : k →ₐ[Z.residueField z'] Ω := IsAlgClosed.lift
  have hτ : spMap τ.toRingHom ≫ Spec.map ψ =
      Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z') Ω)) := by
    rw [← Spec.map_comp]
    congr 1
    ext a
    exact τ.commutes a
  let u : Over.mk q ⟶ Over.mk ((Scheme.SpecToEquivOfField k Z).symm ⟨z', ψ⟩) :=
    Over.homMk (spMap τ.toRingHom) (by
      change spMap τ.toRingHom ≫ Spec.map ψ ≫ _ = _
      rw [reassoc_of% hτ]; rfl)
  refine ⟨⟨u ≫ x, by rw [← SemiAbTorsion.comp_pow_points, hx, MonObj.comp_one]⟩, ?_⟩
  have : Subsingleton (Sp k) := inferInstanceAs (Subsingleton (PrimeSpectrum k))
  change (spMap τ.toRingHom ≫ x.left) pt = _
  rw [Scheme.Hom.comp_apply]
  exact congrArg _ (Subsingleton.elim (α := Sp k) _ _)

theorem exists_image_point_dvr
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {Z U : Scheme.{0}} (j : U ⟶ Z) {G G' : Over Z} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (φ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom φ]
    (V K : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
    [IsFractionRing V K] (a : Sp V ⟶ G.left) (a₀ : Sp K ⟶ pullback G.hom j)
    (ha : a₀ ≫ pullback.fst G.hom j = spMap (algebraMap V K) ≫ a) :
    ∃ b : Sp V ⟶ G'.left, b ≫ G'.hom = a ≫ G.hom ∧
      spMap (algebraMap V K) ≫ b = a₀ ≫ φ.left ≫ pullback.fst G'.hom j ∧
      ∀ (T : Scheme.{0}) (r : T ⟶ Sp V) (t : T ⟶ Z) (x : Over.mk t ⟶ G) (n : ℕ),
        x.left = r ≫ a → x ^ n = 1 → ∃ x' : Over.mk t ⟶ G', x'.left = r ≫ b ∧ x' ^ n = 1 := by
  let y : Sp V ⟶ Z := a ≫ G.hom
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  let y₀ : Sp K ⟶ U := a₀ ≫ pullback.snd G.hom j
  have hy : y₀ ≫ j = g ≫ y := by
    rw [Category.assoc, ← pullback.condition, reassoc_of% ha]
  obtain ⟨α, hα, hα'⟩ := grpPullback_iso
    ((isGrpPullback_pullback ((Over.pullback y).obj G) g).comp (isGrpPullback_pullback G y))
    (((isGrpPullback_pullback ((Over.pullback j).obj G) y₀).comp
      (isGrpPullback_pullback G j)).congr hy rfl)
  obtain ⟨β, hβ, hβ'⟩ := grpPullback_iso
    (((isGrpPullback_pullback ((Over.pullback j).obj G') y₀).comp
      (isGrpPullback_pullback G' j)).congr hy rfl)
    ((isGrpPullback_pullback ((Over.pullback y).obj G') g).comp (isGrpPullback_pullback G' y))
  obtain ⟨F, ⟨hF, hF'⟩, -⟩ := hext V K _ _ (IsSemiAbelian.pullback y G hG)
    (IsSemiAbelian.pullback y G' hG') (α.hom ≫ (Over.pullback y₀).map φ ≫ β.hom) inferInstance
  let a' : Sp V ⟶ pullback G.hom y := pullback.lift a (𝟙 _) (Category.id_comp _).symm
  have ha1 : a' ≫ pullback.fst G.hom y = a := pullback.lift_fst _ _ _
  have ha2 : a' ≫ pullback.snd G.hom y = 𝟙 _ := pullback.lift_snd _ _ _
  have hFw : F.left ≫ pullback.snd G'.hom y = pullback.snd G.hom y := Over.w F
  refine ⟨a' ≫ F.left ≫ pullback.fst G'.hom y, ?_, ?_, fun T r t x n hx hn => ?_⟩
  · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hFw, reassoc_of% ha2]
  · let c : Sp K ⟶ pullback (pullback.snd G.hom y) g :=
      pullback.lift (g ≫ a') (𝟙 _) (by rw [Category.assoc, ha2, Category.comp_id, Category.id_comp])
    have hc1 : c ≫ pullback.fst _ _ = g ≫ a' := pullback.lift_fst _ _ _
    have hc2 : c ≫ pullback.snd _ _ = 𝟙 _ := pullback.lift_snd _ _ _
    have h₁ := ExtUnique.pullback_map_left_fst g F
    have h₂ := ExtUnique.pullback_map_left_fst y₀ φ
    have hαw : α.hom.left ≫ pullback.snd (pullback.snd G.hom j) y₀ =
      pullback.snd (pullback.snd G.hom y) g := Over.w α.hom
    have h₃ : c ≫ α.hom.left ≫ pullback.fst (pullback.snd G.hom j) y₀ = a₀ := by
      apply pullback.hom_ext
      · erw [Category.assoc, Category.assoc, hα', reassoc_of% hc1, ha1, ha]
      · rw [Category.assoc, Category.assoc, pullback.condition, reassoc_of% hαw, reassoc_of% hc2]
    erw [hF'] at h₁
    rw [Over.comp_left, Over.comp_left] at h₁
    change g ≫ _ = _
    rw [← reassoc_of% hc1]
    erw [← reassoc_of% h₁, hβ', reassoc_of% h₂, reassoc_of% h₃]
  · have ht : t = r ≫ y := by
      rw [← Category.assoc, ← hx]; exact (Over.w x).symm
    obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G y) r t ht
    obtain ⟨e', he'⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G' y) r t ht
    have h₁ : (e.symm x).left = r ≫ a' := by
      apply pullback.hom_ext
      · erw [← he, e.apply_symm_apply, hx, Category.assoc, ha1]
      · rw [Category.assoc, ha2, Category.comp_id]; exact Over.w (e.symm x)
    refine ⟨e' (e.symm x ≫ F), ?_, ?_⟩
    · rw [he', Over.comp_left, h₁]; simp only [Category.assoc]
    · rw [← map_pow, ← MonObj.pow_comp, ← map_pow, hn, map_one, MonObj.one_comp, map_one]

theorem finite_residueField_integralClosure_padicInt (p : ℕ) [Fact p.Prime]
    (L : IntermediateField ℚ_[p] (PadicAlgCl p)) [FiniteDimensional ℚ_[p] L] :
    Finite (IsLocalRing.ResidueField (integralClosure ℤ_[p] L)) := by
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_faithful ℤ_[p] ℚ_[p] L
  have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_isLocalHom ℤ_[p] L
  have : Finite (IsLocalRing.ResidueField ℤ_[p]) :=
    Finite.of_equiv _ (PadicInt.residueField).symm.toEquiv
  exact Module.finite_of_finite (IsLocalRing.ResidueField ℤ_[p])

theorem exists_image_point_padic
    (hext : ∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K]
      [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'],
      IsSemiAbelian G → IsSemiAbelian G' →
      ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶
        (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f →
        ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f)
    {Z U : Scheme.{0}} (π : Z ⟶ Sp ℤ) [LocallyOfFiniteType π] (j : U ⟶ Z) [IsOpenImmersion j]
    {G G' : Over Z} [GrpObj G] [GrpObj G'] (hG : IsSemiAbelian G)
    (hG' : IsSemiAbelian G') (φ : (Over.pullback j).obj G ⟶ (Over.pullback j).obj G') [IsMonHom φ]
    (p : ℕ) [Fact p.Prime] (a : Sp (OO p) ⟶ G.left) (a₀ : Sp (PadicAlgCl p) ⟶ pullback G.hom j)
    (ha : a₀ ≫ pullback.fst G.hom j = gPt p ≫ a) (n : ℕ)
    (hn : ∀ (K : Type) [Field K] (t : Sp K ⟶ Z) (x : Over.mk t ⟶ G),
      Set.range x.left = {a (cPt p)} → x ^ n = 1) :
    ∃ b : Sp (OO p) ⟶ G'.left, b ≫ G'.hom = a ≫ G.hom ∧
      gPt p ≫ b = a₀ ≫ φ.left ≫ pullback.fst G'.hom j ∧
      ∃ (k : Type) (_ : Field k) (_ : Finite k) (t : Sp k ⟶ Z) (x : Over.mk t ⟶ G'),
        x ^ n = 1 ∧ b (cPt p) ∈ Set.range x.left := by
  have := hG.smooth
  obtain ⟨K, hK, H⟩ := padicAlgCl_integral_points.2 G.left (G.hom ≫ π) p a
  obtain ⟨i, a₁, hi, hloc, rfl⟩ := H K le_rfl
  let V : Type := integralClosure ℤ_[p] K
  let g : Sp K ⟶ Sp V := spMap (algebraMap V K)
  let d : Sp (PadicAlgCl p) ⟶ Sp K := spMap K.val.toRingHom
  have hd : d ≫ g = gPt p ≫ spMap i := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext x
    exact (hi x).symm
  have hsub : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hr : Set.range (g ≫ a₁) ⊆ Set.range (pullback.fst G.hom j) := by
    rintro _ ⟨s, rfl⟩
    let pt : Sp (PadicAlgCl p) := (⊥ : PrimeSpectrum (PadicAlgCl p))
    refine ⟨a₀ pt, ?_⟩
    rw [← Scheme.Hom.comp_apply, ha, ← reassoc_of% hd, Scheme.Hom.comp_apply d]
    exact congrArg _ (Subsingleton.elim _ _)
  let a₂ : Sp K ⟶ pullback G.hom j := IsOpenImmersion.lift (pullback.fst G.hom j) (g ≫ a₁) hr
  have ha₂ : a₂ ≫ pullback.fst G.hom j = g ≫ a₁ := IsOpenImmersion.lift_fac _ _ _
  have hda : d ≫ a₂ = a₀ := by
    rw [← cancel_mono (pullback.fst G.hom j), Category.assoc, ha₂, reassoc_of% hd, ha]
  obtain ⟨b, hb₁, hb₂, hb₃⟩ := exists_image_point_dvr hext j hG hG' φ V K a₁ a₂ ha₂
  have hcl : spMap i (cPt p) = IsLocalRing.closedPoint V := IsLocalRing.comap_closedPoint i
  let k : Type := IsLocalRing.ResidueField V
  let r : Sp k ⟶ Sp V := spMap (IsLocalRing.residue V)
  have hrc : ∀ s, r s = IsLocalRing.closedPoint V := fun s => by
    rw [Subsingleton.elim (α := PrimeSpectrum k) s (IsLocalRing.closedPoint k)]
    exact IsLocalRing.comap_closedPoint (IsLocalRing.residue V)
  have hkey : ∀ {Y : Scheme.{0}} (c : Sp V ⟶ Y) (s : Sp k), (r ≫ c) s = (spMap i ≫ c) (cPt p) :=
    fun c s => (Scheme.Hom.comp_apply _ _ _).trans ((congrArg c ((hrc s).trans hcl.symm)).trans
      (Scheme.Hom.comp_apply _ _ _).symm)
  let x : Over.mk ((r ≫ a₁) ≫ G.hom) ⟶ G := Over.homMk (r ≫ a₁) rfl
  have hx : x ^ n = 1 := hn k _ x (by
    ext w
    change w ∈ Set.range (r ≫ a₁) ↔ _
    exact ⟨fun ⟨s, h⟩ => h.symm.trans (hkey a₁ s),
      fun h => ⟨IsLocalRing.closedPoint k, (hkey a₁ _).trans h.symm⟩⟩)
  obtain ⟨x', hx', hx''⟩ := hb₃ _ r _ x n rfl hx
  refine ⟨spMap i ≫ b, by rw [Category.assoc, hb₁, Category.assoc], ?_, k, inferInstance,
    finite_residueField_integralClosure_padicInt p K, _, x', hx'', IsLocalRing.closedPoint k, ?_⟩
  · rw [← reassoc_of% hd, hb₂, reassoc_of% hda]
  · rw [hx']
    exact hkey b _

end HomExtension

open HomExtension

theorem existsUnique_hom_extension_semiAbelian_normal_base : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → (∀ (K : Type) [Field K] [IsAlgClosed K] (B : Over (Sp K)) [GrpObj B], IsAbelianScheme B → ∀ n : ℕ, 1 ≤ n → Finite {x : 𝟙_ (Over (Sp K)) ⟶ B // x ^ n = 1}) → ∀ (Z : Scheme.{0}) [IsIntegral Z] (π : Z ⟶ Sp ℤ) [Flat π] [LocallyOfFiniteType π] [QuasiCompact π], ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z → ∀ (G G' P' : Over Z) [GrpObj G] [GrpObj G'] (κ : G' ⟶ P'), IsSemiAbelian G → IsSemiAbelian G' → IsProper P'.hom → IsOpenImmersion κ.left → ∀ (U : Z.Opens), (U : Set Z).Nonempty → ∀ φ : (Over.pullback U.ι).obj G ⟶ (Over.pullback U.ι).obj G', IsMonHom φ → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback U.ι).map F = φ := by
  intro hext hab Z _ π _ _ _ hZ G G' P' _ _ κ hG hG' hP hκ U hU φ hφ
  have := hG.smooth
  have := hG.quasiCompact
  have := hG'.separated
  have : IsIntegral G.left := isIntegral_left_of_isSemiAbelian G
  have hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme G.left :=
    forall_isDomain_and_isIntegrallyClosed_stalk_of_smooth G.hom hZ
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian π
  obtain ⟨_, _⟩ := ExtUnique.dense_open U (U.isOpen.dense hU)
  let ν : pullback G.hom U.ι ⟶ G.left := pullback.fst G.hom U.ι
  have hκw : κ.left ≫ P'.hom = G'.hom := Over.w κ
  have hφw : φ.left ≫ pullback.snd G'.hom U.ι = pullback.snd G.hom U.ι := Over.w φ
  have hνe : ν.isoOpensRange.inv ≫ ν = ν.opensRange.ι := ν.isoOpensRange_inv_comp
  have hne : (ν.opensRange : Set G.left).Nonempty := by
    obtain ⟨z, hz⟩ := hU
    refine ⟨(η : 𝟙_ (Over Z) ⟶ G).left z, ?_⟩
    change _ ∈ Set.range (pullback.fst G.hom U.ι)
    rw [Scheme.Pullback.range_fst, Set.mem_preimage, ← Scheme.Hom.comp_apply, Over.w]
    exact ⟨⟨z, hz⟩, rfl⟩
  obtain ⟨Φ, ⟨hΦ₁, hΦ₂⟩, -⟩ := existsUnique_extension_of_finite_specializations G.left (G.hom ≫ π)
    hnorm Z P'.left G.hom P'.hom κ.left.opensRange ν.opensRange
    (ν.isoOpensRange.inv ≫ φ.left ≫ pullback.fst G'.hom U.ι ≫ κ.left) hne
    (by
      rw [Category.assoc, Category.assoc, Category.assoc, hκw, pullback.condition,
        reassoc_of% hφw, ← pullback.condition, reassoc_of% hνe])
    (fun σ hσ => by
      obtain ⟨n, hn, hn'⟩ :=
        (semiAbelian_torsion_finite_and_closedPoint_finiteOrder hab).2 Z π G σ hσ
      refine ⟨_, (finite_torsion_images hab G' hG' (G.hom σ) hn).image κ.left, ?_, ?_⟩
      · rintro _ ⟨w, -, rfl⟩
        exact ⟨w, rfl⟩
      · rintro p _ a a₀ b rfl ha hb hb'
        obtain ⟨c, hc₁, hc₂, hc₃⟩ := exists_image_point_padic hext π U.ι hG hG' φ p a
          (a₀ ≫ ν.isoOpensRange.inv) (by rw [Category.assoc, hνe, ha]) n hn'
        have : IsSchemeTheoreticallyDominant (gPt p) :=
          ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ Subtype.val_injective
        have hbc : b = c ≫ κ.left := ExtUnique.hom_ext_of_dominant P'.hom
          (by rw [Category.assoc, hκw, hb', hc₁]) (gPt p)
          (by rw [hb, reassoc_of% hc₂])
        refine ⟨c (cPt p), ⟨?_, hc₃⟩, ?_⟩
        · exact (Scheme.Hom.comp_apply c G'.hom _).symm.trans
            ((congrArg (fun f => f (cPt p)) hc₁).trans (Scheme.Hom.comp_apply a G.hom _))
        · rw [hbc]
          exact (Scheme.Hom.comp_apply c κ.left _).symm)
  have hκe : κ.left.isoOpensRange.inv ≫ κ.left = κ.left.opensRange.ι :=
    κ.left.isoOpensRange_inv_comp
  let F : G ⟶ G' := Over.homMk (Φ ≫ κ.left.isoOpensRange.inv) (by
    rw [← hκw, Category.assoc, reassoc_of% hκe, hΦ₂])
  have hF : (Over.pullback U.ι).map F = φ := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · refine (ExtUnique.pullback_map_left_fst U.ι F).trans ?_
      change ν ≫ Φ ≫ κ.left.isoOpensRange.inv = _
      rw [← cancel_mono κ.left, ← cancel_epi ν.isoOpensRange.inv, Category.assoc, Category.assoc,
        hκe, reassoc_of% hνe, hΦ₁, Category.assoc]
    · exact (Over.w _).trans (Over.w _).symm
  refine ⟨F, ⟨ExtUnique.isMonHom_of_pullback U.ι F (hF ▸ hφ), hF⟩, fun F' hF' => ?_⟩
  exact ExtUnique.pullback_map_injective U.ι G G' (hF'.2.trans hF.symm)

end GlobalTheory
