import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EndOnId
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionSectionEqPulledTraitPointField
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Eq8 GlobalTheory.Poinc.Sep.Spz Classical

noncomputable section

namespace GlobalTheory.SpreadTorSection

theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, spMap, spMap, ← Spec.map_comp]; rfl

theorem spMap_id' (A : Type) [CommRing A] : spMap (RingHom.id A) = 𝟙 _ := by
  show Spec.map (𝟙 _) = _
  exact Spec.map_id _

theorem spMap_injective' {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := by
  have := congrArg (fun u => (Spec.preimage u).hom) h
  simpa [spMap, Spec.preimage_map] using this

theorem range_sub {W κ : Type} [CommRing W] [IsLocalRing W] [Field κ] {B : Scheme.{0}} (ψ : Sp W ⟶ B)
    (Wo : B.Opens) (c : W →+* κ) [IsLocalHom c] (y : Sp κ ⟶ Wo.toScheme) (e : spMap c ≫ ψ = y ≫ Wo.ι) :
    Set.range ψ ⊆ Set.range Wo.ι := by
  rintro _ ⟨x, rfl⟩
  rw [Scheme.Opens.range_ι]
  obtain ⟨p, hp⟩ : ∃ p : Sp κ, (spMap c p : PrimeSpectrum W) = closedPoint W :=
    ⟨closedPoint κ, comap_closedPoint c⟩
  have hx : x ⤳ spMap c p := by
    have := specializes_closedPoint (R := W) x
    rw [← hp] at this
    exact this
  refine (hx.map ψ.continuous).mem_open Wo.isOpen ?_
  rw [← Scheme.Hom.comp_apply, e, Scheme.Hom.comp_apply]
  have := Set.mem_range_self (f := Wo.ι) (y p)
  rwa [Scheme.Opens.range_ι] at this

def powChar {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) : Multiplicative X →* Aˣ :=
  (zpowersHom Aˣ u).comp (AddMonoidHom.toMultiplicative c)

theorem powChar_apply {A X : Type} [CommRing A] [AddCommGroup X] (u : Aˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    powChar u c χ = u ^ c (Multiplicative.toAdd χ) := rfl

theorem powChar_map {o A A' X : Type} [CommRing o] [CommRing A] [CommRing A'] [AddCommGroup X] (g : o →+* A)
    (f : A →+* A') (u : oˣ) (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map (f.comp g).toMonoidHom u) c χ : A'ˣ) : A') = f (powChar (Units.map g.toMonoidHom u) c χ) := by
  rw [powChar_apply, powChar_apply,
    show Units.map (f.comp g).toMonoidHom u = Units.map f.toMonoidHom (Units.map g.toMonoidHom u) from rfl,
    ← map_zpow]
  rfl

theorem powChar_val {o K X : Type} [CommRing o] [Field K] [AddCommGroup X] (g : o →+* K) (u : oˣ)
    (c : X →+ ℤ) (χ : Multiplicative X) :
    ((powChar (Units.map g.toMonoidHom u) c χ : Kˣ) : K) = g u ^ c (Multiplicative.toAdd χ) := by
  rw [powChar_apply, Units.val_zpow_eq_zpow_val]; rfl

theorem bc_point {W L X : Type} [CommRing W] [CommRing L] [AddCommGroup X] (f : W →+* L)
    {GW : Over (Sp W)} [GrpObj GW] {GLf : Over (Sp L)} [GrpObj GLf] {n : GLf.left ⟶ GW.left}
    (hn : IsGrpPullback GLf GW (spMap f) n) (j : splitTorus (Sp W) X ⟶ GW)
    (τW : Multiplicative X →* Wˣ) (τL : Multiplicative X →* Lˣ) (hτ : ∀ χ, (τL χ : L) = f (τW χ : W))
    (zW : Over.mk (spMap (RingHom.id W)) ⟶ splitTorus (Sp W) X)
    (hzW : ∀ χ, GlobalTheory.UU.chV zW χ = unitOn (τW (Multiplicative.ofAdd χ)))
    (zL : Over.mk (spMap (RingHom.id L)) ⟶ splitTorus (Sp L) X)
    (hzL : ∀ χ, GlobalTheory.UU.chV zL χ = unitOn (τL (Multiplicative.ofAdd χ))) :
    spMap f ≫ (zW ≫ j).left = (zL ≫ GlobalTheory.TorusPart.pullTorus hn j).left ≫ n := by
  have key : zL.left ≫ GlobalTheory.SplitTorus.bcMap (spMap f) X = spMap f ≫ zW.left := by
    refine GlobalTheory.UU.splitTorus_left_hom_ext _ _ ?_ fun χ => ?_
    · rw [Category.assoc, GlobalTheory.SplitTorus.bcMap_hom, ← Category.assoc, Over.w zL, Category.assoc, Over.w zW]
      change spMap (RingHom.id L) ≫ spMap f = spMap f ≫ spMap (RingHom.id W)
      rw [spMap_id', spMap_id', Category.id_comp, Category.comp_id]
    · rw [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply, GlobalTheory.UU.bcMap_charUnit,
        Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply]
      have e1 := (GlobalTheory.UU.chV_val zL χ).symm.trans (congrArg Units.val (hzL χ))
      have e2 := (GlobalTheory.UU.chV_val zW χ).symm.trans (congrArg Units.val (hzW χ))
      exact e1.trans ((GlobalTheory.ToricOverField.unitOn_val_map f _ _ (hτ _)).trans (congrArg _ e2.symm))
  rw [Over.comp_left, Over.comp_left, Category.assoc, GlobalTheory.TorusPart.pullTorus_left,
    ← Category.assoc zL.left, key, Category.assoc]

theorem trait_section : ∀ (B : Scheme.{0}) (H : Over B) [GrpObj H] [IsCommMonObj H], IsSemiAbelian H → ∀ (V₁ : Type) [CommRing V₁] [IsDomain V₁] [IsLocalRing V₁] (G₁ : Over (Sp V₁)) [GrpObj G₁] [IsCommMonObj G₁] (D₁ : DegData V₁ (maximalIdeal V₁)) (A₁ : PolAV (Sp (FractionRing V₁))) (U₁ : Unif (maximalIdeal V₁) D₁ A₁ G₁) (ξ₁ : Sp V₁ ⟶ B) (β₁ : G₁.left ⟶ H.left) (V₂ : Type) [CommRing V₂] [IsDomain V₂] [IsLocalRing V₂] (G₂ : Over (Sp V₂)) [GrpObj G₂] [IsCommMonObj G₂] (D₂ : DegData V₂ (maximalIdeal V₂)) (A₂ : PolAV (Sp (FractionRing V₂))) (U₂ : Unif (maximalIdeal V₂) D₂ A₂ G₂) (ξ₂ : Sp V₂ ⟶ B) (β₂ : G₂.left ⟶ H.left) (ρ : D₂.toPre.X →+ D₁.toPre.X), Spread₂ H U₁ ξ₁ β₁ U₂ ξ₂ β₂ ρ → ∀ (o : Type) [CommRing o] (s : B ⟶ Sp o) (o₁ : o →+* V₁) (o₂ : o →+* V₂), ξ₁ ≫ s = spMap o₁ → ξ₂ ≫ s = spMap o₂ → ∀ (k : ℕ) (ζ : o), 1 ≤ k → ζ ^ k = 1 → ∀ (Wo : B.Opens) (h : Wo.toScheme ⟶ H.left) (ξ₁' : Sp V₁ ⟶ Wo.toScheme) (ξ₂' : Sp V₂ ⟶ Wo.toScheme), h ≫ H.hom = Wo.ι → ξ₁' ≫ Wo.ι = ξ₁ → ξ₂' ≫ Wo.ι = ξ₂ → ∀ (c : D₁.toPre.X →+ ℤ), (∀ (κ : Type) [Field κ] (b : V₁ →+* κ) (hb : ∀ y ∈ maximalIdeal V₁ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) [GrpObj Gκ] (m : Gκ.left ⟶ G₁.left) (hm : IsGrpPullback Gκ G₁ (spMap b) m) (τ : Multiplicative D₁.toPre.X →* κˣ), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₁ ζ) ^ c χ) → ∀ (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₁.toPre.X), (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) → spMap b ≫ ξ₁' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₁.gt 0) hb hm).left ≫ m ≫ β₁) → ∃ (κ : Type) (_ : Field κ) (b : V₂ →+* κ) (hb : ∀ y ∈ maximalIdeal V₂ ^ (0 + 1), b y = 0) (Gκ : Over (Sp κ)) (_ : GrpObj Gκ) (m : Gκ.left ⟶ G₂.left) (hm : IsGrpPullback Gκ G₂ (spMap b) m) (τ : Multiplicative D₂.toPre.X →* κˣ) (z : Over.mk (spMap (RingHom.id κ)) ⟶ splitTorus (Sp κ) D₂.toPre.X), (∀ χ, (τ (Multiplicative.ofAdd χ) : κ) = b (o₂ ζ) ^ (c.comp ρ) χ) ∧ (∀ χ, GlobalTheory.UU.chV z χ = unitOn (τ (Multiplicative.ofAdd χ))) ∧ spMap b ≫ ξ₂' ≫ h = (z ≫ GlobalTheory.TorusPart.gtTorus (U₂.gt 0) hb hm).left ≫ m ≫ β₂ := by
  intro B H _ _ hH V₁ _ _ _ G₁ _ _ D₁ A₁ U₁ ξ₁ β₁ V₂ _ _ _ G₂ _ _ D₂ A₂ U₂ ξ₂ β₂ ρ hS o _ s o₁ o₂ hs₁ hs₂ k ζ hk hζ
    Wo h ξ₁' ξ₂' hh hξ₁ hξ₂ c hyp
  obtain ⟨W, _, _, _, ψ, GW, _, _, φW, j, Ω, _, α, b₁, hb₁, GΩ, _, n, hn, n₁, hn₁, κ, _, c', b₂, hb₂, Gκ, _, m, hm,
    m₂, hm₂, hψ, _, hα, hc', hαψ, hc'ψ, hnφ, hmφ, hjn, hjm⟩ := hS
  haveI := hc'

  have hrange : Set.range ψ ⊆ Set.range Wo.ι :=
    range_sub ψ Wo c' (spMap b₂ ≫ ξ₂') (by rw [hc'ψ, Category.assoc, hξ₂])
  let ψ' := IsOpenImmersion.lift Wo.ι ψ hrange
  have hψ' : ψ' ≫ Wo.ι = ψ := IsOpenImmersion.lift_fac _ _ _
  have e₁ : spMap α ≫ ψ' = spMap b₁ ≫ ξ₁' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hαψ, Category.assoc, hξ₁]
  have e₂ : spMap c' ≫ ψ' = spMap b₂ ≫ ξ₂' := by
    rw [← cancel_mono Wo.ι, Category.assoc, hψ', hc'ψ, Category.assoc, hξ₂]

  let oW : o →+* W := (Spec.preimage (ψ ≫ s)).hom
  have hoW : spMap oW = ψ ≫ s := by
    show Spec.map (CommRingCat.ofHom (Spec.preimage (ψ ≫ s)).hom) = _
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have ho₁ : α.comp oW = b₁.comp o₁ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hαψ, Category.assoc, hs₁])
  have ho₂ : c'.comp oW = b₂.comp o₂ := spMap_injective' (by
    rw [spMap_comp', spMap_comp', hoW, ← Category.assoc, hc'ψ, Category.assoc, hs₂])

  have hζu : IsUnit ζ := IsUnit.of_pow_eq_one hζ (by omega)
  let u := hζu.unit
  have hu : (u : o) = ζ := hζu.unit_spec
  let τW := powChar (Units.map oW.toMonoidHom u) c
  obtain ⟨zW, hzW⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id W) τW
  let τΩ := powChar (Units.map (α.comp oW).toMonoidHom u) c
  obtain ⟨zΩ, hzΩ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id Ω) τΩ
  have hτΩ : ∀ χ, (τΩ (Multiplicative.ofAdd χ) : Ω) = b₁ (o₁ ζ) ^ c χ := fun χ => by
    rw [powChar_val, ho₁, hu]; rfl
  have hyp₁ := hyp Ω b₁ hb₁ GΩ n₁ hn₁ τΩ hτΩ zΩ hzΩ
  have hbcΩ := bc_point α hn j τW τΩ (fun χ => powChar_map oW α u c χ) zW hzW zΩ hzΩ

  haveI : IsSeparated H.hom := hH.separated
  haveI : IsDominant (spMap α) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical α).2
    (by rw [(RingHom.injective_iff_ker_eq_bot _).1 hα]; exact bot_le)⟩
  have hd : ψ' ≫ h = (zW ≫ j).left ≫ φW := by
    refine ext_of_isDominant_of_isSeparated H.hom ?_ (spMap α) ?_
    · simp only [Category.assoc]
      rw [hh, hψ', hψ.1.w, ← Category.assoc, Over.w (zW ≫ j)]
      change ψ = spMap (RingHom.id W) ≫ ψ
      rw [spMap_id', Category.id_comp]
    · rw [← Category.assoc, e₁, Category.assoc, hyp₁, ← hjn, ← hnφ, ← Category.assoc (spMap α), hbcΩ,
        Category.assoc]

  let τ₁ := powChar (Units.map (c'.comp oW).toMonoidHom u) c
  obtain ⟨zκ, hzκ⟩ := GlobalTheory.ToricOverField.exists_point (RingHom.id κ) τ₁
  have hbcκ := bc_point c' hm j τW τ₁ (fun χ => powChar_map oW c' u c χ) zW hzW zκ hzκ
  let τ₂ : Multiplicative D₂.toPre.X →* κˣ := powChar (Units.map (c'.comp oW).toMonoidHom u) (c.comp ρ)
  refine ⟨κ, inferInstance, b₂, hb₂, Gκ, inferInstance, m₂, hm₂, τ₂, zκ ≫ GlobalTheory.SplitTorus.torusMap _ ρ,
    fun χ => ?_, fun χ => ?_, ?_⟩
  · rw [powChar_val, ho₂, hu]; rfl
  · apply Units.ext
    rw [GlobalTheory.UU.chV_val, GlobalTheory.SplitTorus.charUnit_val, ← GlobalTheory.SplitTorus.val_eq,
      GlobalTheory.SplitTorus.val_comp_torusMap, GlobalTheory.SplitTorus.val_eq, ← GlobalTheory.SplitTorus.charUnit_val,
      ← GlobalTheory.UU.chV_val, hzκ]
    rfl
  · rw [← Category.assoc (spMap b₂), ← e₂, Category.assoc, hd, ← Category.assoc (spMap c'), hbcκ,
      Category.assoc zκ, ← hjm, ← hmφ]
    simp only [Category.assoc]

end GlobalTheory.SpreadTorSection
