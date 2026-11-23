import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqTorusOfClassify
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SmoothCommGroupSchemeEqOfPowEqOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointField
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.SpreadTorMatch

theorem spMap_comp_ringHom' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp [spMap]

theorem section_over_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G →
    ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (k : ℕ)
    (s : ∀ (B : Type) [CommRing B] (a : R →+* B) (τ : Multiplicative D.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G)),
    (∀ (B : Type) [CommRing B] (a : R →+* B) τ h, s B a τ h ^ k = 1) →
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (a' : R →+* B') (f : B →+* B') τ h τ' h',
      a' = f.comp a → (∀ χ, (τ' χ : B') = f (τ χ : B)) → (s B' a' τ' h').left = spMap f ≫ (s B a τ h).left) →
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : R →+* B) (ha : ∀ x ∈ maximalIdeal R ^ (0 + 1), a x = 0) (a' : R →+* B') (f : B →+* B')
      (G₀ : Over (Sp B)) [GrpObj G₀] (m₀ : G₀.left ⟶ G.left) (hm₀ : IsGrpPullback G₀ G (spMap a) m₀) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) ha hm₀).left ≫ m₀) →
    ∀ (X' : Type) [AddCommGroup X'] (ρ : D.toPre.X →+ X')
      (V : Type) [CommRing V] [IsLocalRing V] (ψ : R →+* V) (GV : Over (Sp V)) [GrpObj GV] [IsCommMonObj GV]
      (mV : GV.left ⟶ G.left) (hmV : IsGrpPullback GV G (spMap ψ) mV)
      (j : splitTorus (Sp V) X' ⟶ GV) [IsMonHom j]
      (G₀ : Over (Sp (ResidueField V))) [GrpObj G₀] (m₀ : G₀.left ⟶ GV.left)
      (hm₀ : IsGrpPullback G₀ GV (spMap (residue V)) m₀)
      (h₀ : ∀ x ∈ maximalIdeal R ^ (0 + 1), (residue V).comp ψ x = 0) (m₀' : G₀.left ⟶ G.left)
      (hm₀' : IsGrpPullback G₀ G (spMap ((residue V).comp ψ)) m₀'),
      m₀' = m₀ ≫ mV →
      GlobalTheory.TorusPart.pullTorus hm₀ j = GlobalTheory.SplitTorus.torusMap _ ρ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀' →
    ∀ (W : Type) [CommRing W] [IsLocalRing W] (u : V →+* W), IsLocalHom u → IsUnit (k : W) →
    ∀ (τW : Multiplicative X' →* Wˣ) (τ : Multiplicative D.toPre.X →* Wˣ) (h : τ ^ k = 1),
      τW ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τW (Multiplicative.ofAdd (ρ χ))) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) X'),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τW (Multiplicative.ofAdd χ))) →
      (s W (u.comp ψ) τ h).left = (z ≫ j).left ≫ mV := by
  intro R _ _ _ G _ _ hG D A U k s hpow hnat htor X' _ ρ V _ _ ψ GV _ _ mV hmV j _ G₀ _ m₀ hm₀ h₀ m₀' hm₀'
    hmm hpt W _ _ u hu hk τW τ h hτWk hτ z hz
  obtain ⟨_, hsm, _, _, _, _⟩ := hG
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hmV (Over.mk (spMap u)) (spMap (u.comp ψ))
    (spMap_comp_ringHom' ψ u)

  have hzk : z ^ k = 1 := by
    apply (GlobalTheory.splitTorusPointsEquiv (Sp V) X' (Over.mk (spMap u))).injective
    rw [map_pow, map_one]
    refine MonoidHom.ext fun χ => ?_
    have h1 := hz (Multiplicative.toAdd χ)
    simp only [GlobalTheory.UU.chV, ofAdd_toAdd] at h1
    have h2 : τW χ ^ k = 1 := by simpa using DFunLike.congr_fun hτWk χ
    rw [MonoidHom.pow_apply, MonoidHom.one_apply, h1]
    simp only [unitOn, ← map_pow, h2, map_one]
  have hy : (e (z ≫ j)) ^ k = 1 := by
    rw [← map_pow, ← MonObj.pow_comp, hzk, MonObj.one_comp, map_one]
  suffices hxy : s W (u.comp ψ) τ h = e (z ≫ j) by
    rw [hxy, he]
  refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hsm W (spMap (u.comp ψ)) k hk _ _
    (by rw [hpow W (u.comp ψ) τ h, hy]) (ResidueField W) (residue W) inferInstance ?_

  let τκ : Multiplicative D.toPre.X →* (ResidueField W)ˣ := (Units.map (residue W).toMonoidHom).comp τ
  have h3 : ∀ χ, τ χ ^ k = 1 := fun χ => by simpa using DFunLike.congr_fun h χ
  have hκ : τκ ^ k = 1 := by
    refine MonoidHom.ext fun χ => ?_
    rw [MonoidHom.pow_apply, MonoidHom.one_apply]
    show (Units.map (residue W).toMonoidHom (τ χ)) ^ k = 1
    rw [← map_pow, h3, map_one]
  have hres : (ResidueField.map u).comp (residue V) = (residue W).comp u := ResidueField.map_comp_residue u
  have hb := GlobalTheory.SplitTorus.isGrpPullback_bcMap (spMap (residue V)) X'
  have hw : (spMap (residue W) ≫ z.left) ≫ (splitTorus (Sp V) X').hom =
      spMap (ResidueField.map u) ≫ spMap (residue V) := by
    rw [Category.assoc, Over.w z]
    show spMap (residue W) ≫ spMap u = _
    rw [← spMap_comp_ringHom', ← spMap_comp_ringHom', hres]
  let z₁ : Over.mk (spMap (ResidueField.map u)) ⟶ splitTorus (Sp (ResidueField V)) X' :=
    Over.homMk (hb.1.lift _ _ hw) (hb.1.lift_snd _ _ _)
  have key : z₁.left ≫ GlobalTheory.SplitTorus.bcMap (spMap (residue V)) X' = spMap (residue W) ≫ z.left :=
    hb.1.lift_fst _ _ _
  let z₀ := z₁ ≫ GlobalTheory.SplitTorus.torusMap (Sp (ResidueField V)) ρ
  have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τκ (Multiplicative.ofAdd χ)) := by
    intro χ
    apply Units.ext
    have hτκ : ((τκ (Multiplicative.ofAdd χ) : (ResidueField W)ˣ) : ResidueField W) =
        residue W (τW (Multiplicative.ofAdd (ρ χ)) : W) := by
      show residue W (τ (Multiplicative.ofAdd χ) : W) = _
      rw [hτ]
    rw [GlobalTheory.UU.chV_val, GlobalTheory.ToricOverField.unitOn_val_map (residue W) _ _ hτκ, ← hz (ρ χ), GlobalTheory.UU.chV_val]
    have hk2 := congrArg (fun φ => φ.appTop.hom (charUnit (Sp V) X' (ρ χ)).val) key
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hk2
    rw [← hk2, GlobalTheory.UU.bcMap_charUnit]
    simp only [z₀, Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply,
      GlobalTheory.SplitTorus.charUnit_val, GlobalTheory.SplitTorus.torusMap_appTop_chi]
  have hfa : (residue W).comp (u.comp ψ) = (ResidueField.map u).comp ((residue V).comp ψ) := by
    rw [← RingHom.comp_assoc, ← RingHom.comp_assoc, hres]
  have hT := htor (ResidueField V) (ResidueField W) ((residue V).comp ψ) h₀ ((residue W).comp (u.comp ψ))
    (ResidueField.map u) G₀ m₀' hm₀' τκ hκ z₀ hfa hz₀
  have hN := hnat W (ResidueField W) (u.comp ψ) ((residue W).comp (u.comp ψ)) (residue W) τ h τκ hκ rfl
    (fun χ => rfl)
  rw [← hN, hT, he]
  have hz0gt : z₀ ≫ GlobalTheory.TorusPart.gtTorus (U.gt 0) h₀ hm₀' = z₁ ≫ GlobalTheory.TorusPart.pullTorus hm₀ j := by
    show (z₁ ≫ _) ≫ _ = _
    rw [Category.assoc, ← hpt]
  rw [hz0gt, hmm]
  simp only [Over.comp_left, Category.assoc]
  rw [← Category.assoc (GlobalTheory.TorusPart.pullTorus hm₀ j).left, GlobalTheory.TorusPart.pullTorus_left, ← Category.assoc,
    ← Category.assoc, key]
  simp only [Category.assoc]

theorem section_over_field : ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (G' : Over (Sp W)) [GrpObj G'] [IsCommMonObj G']
    (D' : DegData W (maximalIdeal W)) (A' : PolAV (Sp (FractionRing W))) (U' : Unif (maximalIdeal W) D' A' G') (k : ℕ)
    (s' : ∀ (B : Type) [CommRing B] (a : W →+* B) (τ : Multiplicative D'.toPre.X →* Bˣ), τ ^ k = 1 → (Over.mk (spMap a) ⟶ G')),
    (∀ (B B' : Type) [CommRing B] [CommRing B'] (a : W →+* B) (ha : ∀ x ∈ maximalIdeal W ^ (0 + 1), a x = 0) (a' : W →+* B') (f : B →+* B')
      (G₀ : Over (Sp B)) [GrpObj G₀] (m₀ : G₀.left ⟶ G'.left) (hm₀ : IsGrpPullback G₀ G' (spMap a) m₀) τ h
      (z : Over.mk (spMap f) ⟶ splitTorus (Sp B) D'.toPre.X),
      a' = f.comp a → (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) →
      (s' B' a' τ h).left = (z ≫ GlobalTheory.TorusPart.gtTorus (U'.gt 0) ha hm₀).left ≫ m₀) →
    ∀ (R : Type) [CommRing R] (G : Over (Sp R)) (β : G'.left ⟶ G.left)
      (V : Type) [CommRing V] (G₁ : Over (Sp V)) [GrpObj G₁] (m₁ : G₁.left ⟶ G.left)
      (Ω : Type) [Field Ω] (α : V →+* Ω) (b : W →+* Ω) (hb : ∀ x ∈ maximalIdeal W ^ (0 + 1), b x = 0)
      (GΩ : Over (Sp Ω)) [GrpObj GΩ] (n : GΩ.left ⟶ G₁.left) (hn : IsGrpPullback GΩ G₁ (spMap α) n)
      (n' : GΩ.left ⟶ G'.left) (hn' : IsGrpPullback GΩ G' (spMap b) n')
      (j : splitTorus (Sp V) D'.toPre.X ⟶ G₁),
      GlobalTheory.TorusPart.pullTorus hn j = GlobalTheory.TorusPart.gtTorus (U'.gt 0) hb hn' →
      n ≫ m₁ = n' ≫ β →
    ∀ (Ω' : Type) [Field Ω'] (σ : Ω →+* Ω') (a' : W →+* Ω'), a' = σ.comp b →
    ∀ (Y : Type) [CommRing Y] (u : V →+* Y) (w : Y →+* Ω'), w.comp u = σ.comp α →
    ∀ (τY : Multiplicative D'.toPre.X →* Yˣ) (τ'' : Multiplicative D'.toPre.X →* Ω'ˣ) (h : τ'' ^ k = 1),
      (∀ χ, (τ'' χ : Ω') = w (τY χ : Y)) →
    ∀ (z : Over.mk (spMap u) ⟶ splitTorus (Sp V) D'.toPre.X),
      (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τY (Multiplicative.ofAdd χ))) →
      (s' Ω' a' τ'' h).left ≫ β = spMap w ≫ (z ≫ j).left ≫ m₁ := by
  intro W _ _ _ G' _ _ D' A' U' k s' htor R _ G β V _ G₁ _ m₁ Ω _ α b hb GΩ _ n hn n' hn' j hpull hcomm
    Ω' _ σ a' ha' Y _ u w hwu τY τ'' h hτ z hz
  have hb2 := GlobalTheory.SplitTorus.isGrpPullback_bcMap (spMap α) D'.toPre.X
  have hw : (spMap w ≫ z.left) ≫ (splitTorus (Sp V) D'.toPre.X).hom = spMap σ ≫ spMap α := by
    rw [Category.assoc, Over.w z]
    show spMap w ≫ spMap u = _
    rw [← spMap_comp_ringHom', ← spMap_comp_ringHom', hwu]
  let z₀ : Over.mk (spMap σ) ⟶ splitTorus (Sp Ω) D'.toPre.X :=
    Over.homMk (hb2.1.lift _ _ hw) (hb2.1.lift_snd _ _ _)
  have key : z₀.left ≫ GlobalTheory.SplitTorus.bcMap (spMap α) D'.toPre.X = spMap w ≫ z.left :=
    hb2.1.lift_fst _ _ _
  have hz₀ : ∀ χ, GlobalTheory.UU.chV z₀ χ = unitOn (τ'' (Multiplicative.ofAdd χ)) := by
    intro χ
    apply Units.ext
    rw [GlobalTheory.UU.chV_val, GlobalTheory.ToricOverField.unitOn_val_map w _ _ (hτ _), ← hz χ, GlobalTheory.UU.chV_val]
    have hk2 := congrArg (fun φ => φ.appTop.hom (charUnit (Sp V) D'.toPre.X χ).val) key
    simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at hk2
    rw [← hk2, GlobalTheory.UU.bcMap_charUnit]
  have hT := htor Ω Ω' b hb a' σ GΩ n' hn' τ'' h z₀ ha' hz₀
  rw [hT, ← hpull]
  simp only [Over.comp_left, Category.assoc]
  rw [← hcomm, ← Category.assoc (GlobalTheory.TorusPart.pullTorus hn j).left, GlobalTheory.TorusPart.pullTorus_left,
    ← Category.assoc, ← Category.assoc, key]
  simp only [Category.assoc]

private theorem powComp_lemma {L M N : Type} [Monoid L] [Monoid M] [CommMonoid N] (τ : M →* N) (ρ : L →* M)
    (k : ℕ) (h : τ ^ k = 1) : (τ.comp ρ) ^ k = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply]

private theorem powMap_lemma_2 {M N P : Type} [Monoid M] [CommMonoid N] [CommMonoid P] (f : N →* P) (τ : M →* N)
    (k : ℕ) (h : τ ^ k = 1) : (f.comp τ) ^ k = 1 := by
  refine MonoidHom.ext fun x => ?_
  rw [MonoidHom.pow_apply, MonoidHom.comp_apply, ← map_pow, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply, map_one]

private theorem unitsLift_lemma_3 (K : Type) [Field K] (O : ValuationSubring K) (X : Type) [AddCommGroup X] (k : ℕ)
    (hk : 1 ≤ k) (τ : Multiplicative X →* Kˣ) (h : τ ^ k = 1) :
    ∃ τO : Multiplicative X →* Oˣ, τO ^ k = 1 ∧ (Units.map O.subtype.toMonoidHom).comp τO = τ := by
  obtain ⟨τO, hτO⟩ := GlobalTheory.ToricTorsionCompare.units_of_pow_eq_one K O X k hk τ h
  have e : (Units.map O.subtype.toMonoidHom).comp τO = τ := MonoidHom.ext fun x => Units.ext (hτO x)
  refine ⟨τO, MonoidHom.ext fun x => ?_, e⟩
  apply Units.map_injective (f := O.subtype.toMonoidHom) (fun a b hab => Subtype.ext hab)
  rw [MonoidHom.pow_apply, map_pow, ← MonoidHom.comp_apply, e, ← MonoidHom.pow_apply, h]
  simp only [MonoidHom.one_apply, map_one]

private theorem exists_dom_lemma_4 (A : Type) [CommRing A] [IsLocalRing A] (K : Type) [Field K] (f : A →+* K) :
    ∃ (O : ValuationSubring K) (φ : A →+* O), IsLocalHom φ ∧ ∀ x, (φ x : K) = f x := by
  obtain ⟨O, hle, hloc⟩ := (LocalSubring.range f).exists_le_valuationSubring
  refine ⟨O, f.codRestrict O (fun x => hle (f.mem_range_self x)), ⟨fun x hx => ?_⟩, fun x => rfl⟩
  have h1 : IsUnit (Subring.inclusion hle (f.rangeRestrict x)) := hx
  have h2 : IsUnit (f.rangeRestrict x) := hloc.map_nonunit _ h1
  have : IsLocalHom f.rangeRestrict := IsLocalHom.of_surjective _ f.rangeRestrict_surjective
  exact this.map_nonunit _ h2

private theorem exists_comp_lemma_5 (A : Type) [CommRing A] [IsLocalRing A] (K L : Type) [Field K] [Field L]
    (f : A →+* K) (hf : ∀ x ∈ maximalIdeal A, f x = 0) (g : A →+* L) (hg : ∀ x ∈ maximalIdeal A, g x = 0) :
    ∃ (M : Type) (_ : Field M) (p : K →+* M) (q : L →+* M), p.comp f = q.comp g := by
  let f' : ResidueField A →+* K := Ideal.Quotient.lift (maximalIdeal A) f hf
  let g' : ResidueField A →+* L := Ideal.Quotient.lift (maximalIdeal A) g hg
  letI := f'.toAlgebra
  letI := g'.toAlgebra
  haveI : Nontrivial (K ⊗[ResidueField A] L) :=
    Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_isDomain _ K L f'.injective g'.injective
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (K ⊗[ResidueField A] L)
  have key : ∀ x, f x ⊗ₜ[ResidueField A] (1 : L) = (1 : K) ⊗ₜ[ResidueField A] g x := by
    intro x
    have e1 : f x = algebraMap (ResidueField A) K (residue A x) := rfl
    have e2 : g x = algebraMap (ResidueField A) L (residue A x) := rfl
    rw [e1, e2, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact ⟨_ ⧸ m, Ideal.Quotient.field m, (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeLeftRingHom,
    (Ideal.Quotient.mk m).comp Algebra.TensorProduct.includeRight.toRingHom,
    RingHom.ext fun x => congrArg (Ideal.Quotient.mk m) (key x)⟩

theorem torMatch_of_spread : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], GlobalTheory.Mum.Base V → ∀ (G' : Over (Sp V)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData V (maximalIdeal V)) (A' : PolAV (Sp (FractionRing V))) (U' : Unif (maximalIdeal V) D' A' G') (g : R →+* V) (β : G'.left ⟶ G.left), IsGrpPullback G' G (spMap g) β → ∀ ρ, Spread U U' g β ρ → TorMatch U U' g β ρ := by
  intro R _ _ _ hR G _ _ hG D A U V _ _ _ hV G' _ _ hG' D' A' U' g β hβ ρ hsp
  obtain ⟨V₁, _, _, _, ψ, G₁, _, _, φ₁, Ω, _, α, b, hb, GΩ, _, n, hn, n', hn', j, G₀, _, m₀, hm₀, h₀, hm₀',
    hψ, hφ₁, hj, hα, hαψ, hcomm, hpull, hpt⟩ := hsp
  intro F _ _ _ _ hF k hk τ τ' q q' a a' hτ'k hτρ hqy hqt hq'y hq't hQ hQ'
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · simp at hk
    · exact hpos
  obtain ⟨_, hsm, _, _, _, _⟩ := id hG
  obtain ⟨s, hpow, hnat, htor, hgen⟩ := GlobalTheory.ToricTorsionUnif.main R hR G hG D A U k hk1
  obtain ⟨s', hpow', hnat', htor', hgen'⟩ := GlobalTheory.ToricTorsionUnif.main V hV G' hG' D' A' U' k hk1
  let ρm : Multiplicative D.toPre.X →* Multiplicative D'.toPre.X := AddMonoidHom.toMultiplicative ρ
  have hτeq : τ = τ'.comp ρm := MonoidHom.ext fun χ => hτρ (Multiplicative.toAdd χ)
  subst hτeq
  have hτk := powComp_lemma τ' ρm k hτ'k
  rw [hgen F _ _ hτk q a rfl hqy hqt hQ, ← Category.assoc, hgen' F _ τ' hτ'k q' a' rfl hq'y hq't hQ']

  obtain ⟨O, φ, hφ, hφv⟩ := exists_dom_lemma_4 V F ((algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
  obtain ⟨τ'O, hτ'O, eO⟩ := unitsLift_lemma_3 F O D'.toPre.X k hk1 τ' hτ'k
  have hτO := powComp_lemma τ'O ρm k hτ'O

  obtain ⟨Ω', _, σ, c₀, hσ⟩ := exists_comp_lemma_5 V Ω (ResidueField O) b (fun x hx => hb x (by simpa using hx))
    ((residue O).comp φ) (fun x hx => (IsLocalRing.residue_eq_zero_iff _).mpr (map_nonunit φ x hx))
  let c : O →+* Ω' := c₀.comp (residue O)
  have hc : IsLocalHom c := ⟨fun x hx => by
    by_contra hne
    have h0 : residue O x = 0 := (IsLocalRing.residue_eq_zero_iff x).mpr hne
    have h1 : c x = 0 := by simp only [c, RingHom.comp_apply, h0, map_zero]
    rw [h1] at hx
    exact not_isUnit_zero hx⟩
  have hcφ : c.comp φ = σ.comp b := hσ.symm

  obtain ⟨O₁, u, hu, hu'⟩ := exists_dom_lemma_4 V₁ Ω' (σ.comp α)
  have hwu : O₁.subtype.comp u = σ.comp α := RingHom.ext hu'
  let τ'Ω : Multiplicative D'.toPre.X →* Ω'ˣ := (Units.map c.toMonoidHom).comp τ'O
  have hτ'Ω : τ'Ω ^ k = 1 := powMap_lemma_2 _ τ'O k hτ'O
  have hτΩ := powComp_lemma τ'Ω ρm k hτ'Ω
  obtain ⟨τW, hτW, eW⟩ := unitsLift_lemma_3 Ω' O₁ D'.toPre.X k hk1 τ'Ω hτ'Ω
  have hτWR := powComp_lemma τW ρm k hτW
  obtain ⟨z, hz⟩ := GlobalTheory.ToricOverField.exists_point (A := V₁) u τW
  haveI := hj
  have hkW : IsUnit (k : O₁) := by simpa using hk.map (u.comp ψ)
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hloc := section_over_local R G hG D A U k s hpow hnat htor D'.toPre.X ρ V₁ ψ G₁ φ₁ hφ₁ j G₀ m₀ hm₀ h₀
    (m₀ ≫ φ₁) hm₀' rfl hpt O₁ u hu hkW τW (τW.comp ρm) hτWR hτW (fun χ => rfl) z hz
  have hfld := section_over_field V G' D' A' U' k s' htor' R G β V₁ G₁ φ₁ Ω α b hb GΩ n hn n' hn' j hpull hcomm
    Ω' σ (c.comp φ) hcφ O₁ u O₁.subtype hwu τW τ'Ω hτ'Ω (fun χ => by rw [← eW]; try rfl) z hz
  have hcomp : c.comp (φ.comp g) = O₁.subtype.comp (u.comp ψ) := by
    refine RingHom.ext fun r => ?_
    have h1 := congrArg (fun f => f (g r)) hcφ
    have h2 := congrArg (fun f => f r) hαψ
    have h3 := congrArg (fun f => f (ψ r)) hwu
    simp only [RingHom.comp_apply] at h1 h2 h3 ⊢
    rw [h1, ← h2, h3]
  have hx1 := hnat O₁ Ω' (u.comp ψ) (c.comp (φ.comp g)) O₁.subtype (τW.comp ρm) hτWR (τ'Ω.comp ρm) hτΩ hcomp
    (fun χ => by rw [← eW]; try rfl)
  obtain ⟨e, he⟩ := GlobalTheory.LiePull.exists_pushEquiv hβ (Over.mk (spMap φ)) (spMap (φ.comp g))
    (spMap_comp_ringHom' g φ)
  have hxy : s O (φ.comp g) (τ'O.comp ρm) hτO = e (s' O φ τ'O hτ'O) := by
    refine GlobalTheory.LocalRigid.eq_of_pow_eq_of_closedPoint (Sp R) G hsm O (spMap (φ.comp g)) k hkO _ _ ?_ Ω' c hc ?_
    · rw [hpow O (φ.comp g) _ hτO, ← map_pow e, hpow' O φ τ'O hτ'O, map_one]
    · rw [he, ← hnat O Ω' (φ.comp g) (c.comp (φ.comp g)) c _ hτO _ hτΩ rfl (fun χ => rfl), ← Category.assoc,
        ← hnat' O Ω' φ (c.comp φ) c τ'O hτ'O τ'Ω hτ'Ω rfl (fun χ => rfl), hfld, hx1, hloc]
  have haR : (algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)) = O.subtype.comp (φ.comp g) := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    rw [hF r]
    exact (hφv (g r)).symm
  have haV : (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)) = O.subtype.comp φ :=
    RingHom.ext fun x => (hφv x).symm
  rw [hnat O F (φ.comp g) _ O.subtype _ hτO _ hτk haR (fun χ => by rw [← eO]; try rfl),
    hnat' O F φ _ O.subtype τ'O hτ'O τ' hτ'k haV (fun χ => by rw [← eO]; try rfl), hxy, he, Category.assoc]

end GlobalTheory.SpreadTorMatch

end
