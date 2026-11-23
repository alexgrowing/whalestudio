import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AmplePt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveOfComplexPointsLiftOfUniversallyClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsReducedIsNormalSchemeIsLocallyNoetherianOfSmoo

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

section Pts

variable {k : Type} [Field k] [IsAlgClosed k]

theorem hom_ext_pts {X Y : Over (Sp k)} (hX : Smooth X.hom) [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ X.hom hX).1
  exact Over.OverMorphism.ext (ComplexPoints.hom_ext_of_points X.hom Y.hom (by rw [Over.w, Over.w]) fun x hx =>
    congrArg (fun q => q.left) (h (Over.homMk x hx)))

theorem exists_lift_pt {S : Scheme.{0}} {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left]
    (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (default : PrimeSpectrum k)
  obtain ⟨x, hx, -⟩ := ComplexPoints.exists_point_mem (pullback.snd ψ.left y') (Z := Set.univ)
    isClosed_univ.isLocallyClosed ⟨z, trivial⟩
  have e : (x ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  exact ⟨Over.homMk (x ≫ pullback.fst ψ.left y') (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y),
    Over.OverMorphism.ext e⟩

theorem exists_fac {A B Y : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj Y] (hA : Smooth A.hom) [IsSeparated Y.hom]
    (ψ₀ : A ⟶ B) [IsMonHom ψ₀] [Etale ψ₀.left] [Surjective ψ₀.left] [QuasiCompact ψ₀.left] (ψ : A ⟶ Y) [IsMonHom ψ]
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ ψ₀ = 1 → x ≫ ψ = 1) : ∃ α : B ⟶ Y, ψ₀ ≫ α = ψ := by
  let R : Over (Sp k) := Over.mk (pullback.fst ψ₀.left ψ₀.left ≫ A.hom)
  let p₁ : R ⟶ A := Over.homMk (pullback.fst _ _) rfl
  let p₂ : R ⟶ A := Over.homMk (pullback.snd _ _) (by
    show _ = pullback.fst ψ₀.left ψ₀.left ≫ A.hom
    rw [← Over.w ψ₀, ← pullback.condition_assoc])
  have e₀ : p₁ ≫ ψ₀ = p₂ ≫ ψ₀ := Over.OverMorphism.ext pullback.condition
  have e : p₁ ≫ ψ = p₂ ≫ ψ := hom_ext_pts (inferInstanceAs (Smooth (pullback.fst ψ₀.left ψ₀.left ≫ A.hom))) fun x => by
    have := h ((x ≫ p₁) * (x ≫ p₂)⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, e₀, Category.assoc, mul_inv_cancel])
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc, Category.assoc] at this
    exact this
  have e' : pullback.fst ψ₀.left ψ₀.left ≫ ψ.left = pullback.snd ψ₀.left ψ₀.left ≫ ψ.left :=
    congrArg (fun q => q.left) e
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ ψ₀.left = g₂ ≫ ψ₀.left → g₁ ≫ ψ.left = g₂ ≫ ψ.left :=
    fun g₁ g₂ hg => by
      rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e', pullback.lift_snd_assoc]
  have f := EffectiveEpi.fac ψ₀.left ψ.left hd
  refine ⟨Over.homMk (EffectiveEpi.desc ψ₀.left ψ.left hd) ?_, Over.OverMorphism.ext f⟩
  rw [← cancel_epi ψ₀.left, reassoc_of% f, Over.w, Over.w]

theorem isIso_of_mono {A B : Over (Sp k)} (α : A ⟶ B) [IsProper A.hom] [IsSeparated B.hom] (hB : Smooth B.hom)
    [Mono α.left] (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ B, ∃ x, x ≫ α = y) : IsIso α := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ B.hom hB).1
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper α.left := IsProper.of_comp α.left B.hom
  have : IsClosedImmersion α.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : Surjective α.left := ComplexPoints.surjective_of_geomPoints_lift B.hom (𝟙 (Sp k)) α.left
    α.left.isClosedEmbedding.isClosed_range fun y hy => by
      obtain ⟨x, hx⟩ := h (Over.homMk y hy)
      exact ⟨x.left, congrArg (fun q => q.left) hx⟩
  have : IsIso α.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map α) := ‹_›
  exact isIso_of_reflects_iso α (Over.forget _)

omit [IsAlgClosed k] in

theorem toUnit_comp_injective {K : Type} [Field K] (x : Sp K ⟶ Sp k) (A : Over (Sp k)) :
    Function.Injective (fun z : 𝟙_ (Over (Sp k)) ⟶ A => toUnit (Over.mk x) ≫ z) := by
  have : Surjective x := ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi x := Flat.epi_of_flat_of_surjective x
  intro a b h
  have e : (toUnit (Over.mk x)).left = x := by simp
  have h' : (toUnit (Over.mk x)).left ≫ a.left = (toUnit (Over.mk x)).left ≫ b.left := congrArg (fun q => q.left) h
  rw [e] at h'
  exact Over.OverMorphism.ext ((cancel_epi x).1 h')

theorem exists_of_torsion (hM : Out.MulNSt) (P : Out.PolAV (Sp k)) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ Sp k) {n : ℕ} (hk : (n : k) ≠ 0) (hK : (n : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ n = 1) :
    ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ P.A, toUnit (Over.mk x) ≫ z₀ = z := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have c₁ : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := (hM _ P n hn).2.2.2.2 k (𝟙 _) hk
  have c₂ := (hM _ P n hn).2.2.2.2 K x hK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} → {y : Over.mk x ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨toUnit _ ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

end Pts

theorem exists_ptsEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (y : T.left ⟶ S) (e : T.hom ≫ f = y) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst e
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem unitOn_pow {R : Type} [CommRing R] (c : Rˣ) (n : ℕ) : unitOn (c ^ n) = unitOn c ^ n := map_pow _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩

theorem exists_dim {k : Type} [Field k] (t : SAB H (Sp k)) : ∃ g, SmoothOfRelativeDimension g t.G.hom := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum k))

abbrev polOf {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) : Out.PolAV S where
  A := t.G
  isAb := isAbelianScheme_of_proper t hp
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => ⟨⊤, trivial, by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := ha
  ktriv := hk

end GlobalTheory.HeckePoint
