import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapStalkMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.GenFibre

variable {Y P : Scheme.{0}} {Ω : Type} [Field Ω]

theorem isIso_stalkMap_of_lift (f : Y ⟶ P) [Mono f] (y : Y)
    (t : Spec (P.presheaf.stalk (f y)) ⟶ Y) (ht : t ≫ f = P.fromSpecStalk (f y)) :
    IsIso (f.stalkMap y) := by
  have h0 : Spec.map (f.stalkMap y) ≫ P.fromSpecStalk (f y) = Y.fromSpecStalk y ≫ f :=
    Scheme.SpecMap_stalkMap_fromSpecStalk f
  have h1 : Spec.map (f.stalkMap y) ≫ t = Y.fromSpecStalk y := by
    rw [← cancel_mono f, Category.assoc, ht, h0]
  have hc : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) = y := by
    have e1 : Spec.map (f.stalkMap y) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) =
        IsLocalRing.closedPoint (P.presheaf.stalk (f y)) := Spec_closedPoint
    have e2 : (Spec.map (f.stalkMap y) ≫ t) (IsLocalRing.closedPoint (Y.presheaf.stalk y)) = y := by
      rw [h1]
      exact Scheme.fromSpecStalk_closedPoint
    rw [← e1]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans e2
  have hs : t (IsLocalRing.closedPoint (P.presheaf.stalk (f y))) ⤳ y := by rw [hc]
  have h2 : Spec.map (Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t) ≫ Y.fromSpecStalk y = t := by
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  generalize Y.presheaf.stalkSpecializes hs ≫ Scheme.stalkClosedPointTo t = τ at h2
  refine ⟨τ, ?_, ?_⟩
  · apply Spec.map_injective
    rw [← cancel_mono (P.fromSpecStalk (f y)), Spec.map_comp, Category.assoc, h0, ← Category.assoc, h2, ht,
      Spec.map_id, Category.id_comp]
  · apply Spec.map_injective
    rw [← cancel_mono (Y.fromSpecStalk y), Spec.map_comp, Category.assoc, h2, h1, Spec.map_id, Category.id_comp]

theorem genMap_bijective {ζ : Spec (CommRingCat.of Ω) ⟶ P} (h : IsCptGen ζ) (p : Cpt ζ) (e : p.1 = genPt ζ) :
    Function.Bijective (genMap ζ p) := by
  obtain ⟨p, hp⟩ := p
  obtain rfl : p = genPt ζ := e
  have : P.presheaf.stalkSpecializes hp = 𝟙 _ := TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [genMap, this]
  exact h.bij

theorem isCptGen_of_isIso_stalkMap (f : Y ⟶ P) (hf : ∀ y, IsIso (f.stalkMap y))
    (ξ : Spec (CommRingCat.of Ω) ⟶ Y) (h : IsCptGen (ξ ≫ f)) : IsCptGen ξ := by
  have hd : Dominates ξ (ξ ≫ f) f (RingHom.id Ω) := by
    show ξ ≫ f = Spec.map (CommRingCat.ofHom (RingHom.id Ω)) ≫ ξ ≫ f
    rw [show CommRingCat.ofHom (RingHom.id Ω) = 𝟙 _ from rfl, Spec.map_id, Category.id_comp]
  have hb : ∀ q, Function.Bijective (f.stalkMap q).hom := fun q =>
    have := hf q
    ConcreteCategory.bijective_of_isIso (f.stalkMap q)
  have hcl : ∀ (q : Cpt ξ), genPt (ξ ≫ f) ⤳ f q.1 := fun q =>
    RegAtDom.map_genPt hd ▸ q.2.map f.continuous
  have hcomp : ∀ (q : Cpt ξ), genMap ξ q ∘ (f.stalkMap q.1).hom = genMap (ξ ≫ f) ⟨f q.1, hcl q⟩ := fun q =>
    funext fun t => RegAtDom.genMap_stalkMap hd q.1 q.2 (hcl q) t
  have hself : genMap ξ ⟨genPt ξ, specializes_rfl⟩ = (Scheme.stalkClosedPointTo ξ).hom := by
    have : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) = 𝟙 _ :=
      TopCat.Presheaf.stalkSpecializes_refl _ _
    have e : Y.presheaf.stalkSpecializes (specializes_rfl : genPt ξ ⤳ genPt ξ) ≫ Scheme.stalkClosedPointTo ξ =
        Scheme.stalkClosedPointTo ξ := by
      rw [this]
      exact Category.id_comp _
    exact congrArg (fun g => g.hom) e
  refine ⟨?_, fun q => ?_⟩
  · have e := hcomp ⟨genPt ξ, specializes_rfl⟩
    have hB := genMap_bijective h ⟨f (genPt ξ), hcl ⟨genPt ξ, specializes_rfl⟩⟩ (RegAtDom.map_genPt hd)
    rw [← e] at hB
    rw [← hself]
    exact ⟨hB.1.of_comp_right (hb _).2, hB.2.of_comp⟩
  · have hi := h.inj ⟨f q.1, hcl q⟩
    rw [← hcomp q] at hi
    exact hi.of_comp_right (hb _).2

variable {F : Type} [Field F] [NumberField F]

omit [NumberField F] in

theorem injective_of_charZero [CharZero Ω] (φ : 𝓞 F →+* Ω) : Function.Injective φ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  apply Ideal.eq_bot_of_comap_eq_bot (R := ℤ)
  ext n
  simp [Ideal.mem_comap, RingHom.mem_ker]

theorem exists_lift_field {R : CommRingCat.{0}} [IsLocalRing R] (g : Spec R ⟶ Sp (𝓞 F)) (z : Sp F)
    (hz : g (IsLocalRing.closedPoint R) = spMap (algebraMap (𝓞 F) F) z) :
    ∃ v : Spec R ⟶ Sp F, v ≫ spMap (algebraMap (𝓞 F) F) = g := by
  have hg : Spec.map (Spec.preimage g) = g := Spec.map_preimage g
  generalize Spec.preimage g = c at hg
  subst hg
  have hu : ∀ a : nonZeroDivisors (𝓞 F), IsUnit (c.hom a) := by
    intro a
    by_contra hn
    have h1 : (a : 𝓞 F) ∈ (Spec.map c (IsLocalRing.closedPoint R)).asIdeal :=
      (IsLocalRing.mem_maximalIdeal _).2 hn
    rw [hz] at h1
    have h2 : algebraMap (𝓞 F) F a ∈ PrimeSpectrum.asIdeal z := h1
    have hp : (PrimeSpectrum.asIdeal z).IsPrime := PrimeSpectrum.isPrime _
    rw [Ideal.eq_bot_of_prime (PrimeSpectrum.asIdeal z), Ideal.mem_bot] at h2
    have h3 : (a : 𝓞 F) = 0 := IsFractionRing.injective (𝓞 F) F (h2.trans (map_zero _).symm)
    exact nonZeroDivisors.ne_zero a.2 h3
  refine ⟨Spec.map (CommRingCat.ofHom (IsLocalization.lift (M := nonZeroDivisors (𝓞 F)) (S := F) hu)), ?_⟩
  rw [← Spec.map_comp]
  congr 1
  ext a
  simp

theorem isIso_stalkMap_fst (s : P ⟶ Sp (𝓞 F)) (y : ↑(pullback s (spMap (algebraMap (𝓞 F) F)))) :
    IsIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap y) := by
  have : Epi (CommRingCat.ofHom (algebraMap (𝓞 F) F)) := IsLocalization.epi (nonZeroDivisors (𝓞 F)) F
  have : Mono (spMap (algebraMap (𝓞 F) F)) := Scheme.Spec.map_mono (CommRingCat.ofHom _).op
  have hz : (P.fromSpecStalk (pullback.fst s (spMap (algebraMap (𝓞 F) F)) y) ≫ s) (IsLocalRing.closedPoint _) =
      spMap (algebraMap (𝓞 F) F) (pullback.snd s (spMap (algebraMap (𝓞 F) F)) y) := by
    refine (Scheme.Hom.comp_apply _ _ _).trans ?_
    rw [Scheme.fromSpecStalk_closedPoint]
    have e : (pullback.fst s (spMap (algebraMap (𝓞 F) F)) ≫ s) y =
        (pullback.snd s (spMap (algebraMap (𝓞 F) F)) ≫ spMap (algebraMap (𝓞 F) F)) y := by
      rw [pullback.condition]
    exact (Scheme.Hom.comp_apply _ _ _).symm.trans (e.trans (Scheme.Hom.comp_apply _ _ _))
  obtain ⟨v, hv⟩ := exists_lift_field _ _ hz
  exact isIso_stalkMap_of_lift _ y (pullback.lift _ v hv.symm) (pullback.lift_fst _ _ _)

theorem exists_point : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ P), IsCptGen ξ₀ → ∃ (b : F →+* Ω) (ξF : Sp Ω ⟶ pullback s (spMap (algebraMap (𝓞 F) F))), ξF ≫ pullback.fst _ _ = ξ₀ ∧ ξF ≫ pullback.snd _ _ = spMap b ∧ IsCptGen ξF := by
  intro F _ _ P s Ω _ _ ξ₀ h
  have hφ : Spec.map (Spec.preimage (ξ₀ ≫ s)) = ξ₀ ≫ s := Spec.map_preimage _
  generalize Spec.preimage (ξ₀ ≫ s) = φ at hφ
  have hinj : Function.Injective φ.hom := injective_of_charZero φ.hom
  have hb : (CommRingCat.ofHom (algebraMap (𝓞 F) F)) ≫ CommRingCat.ofHom (IsFractionRing.lift hinj) = φ := by
    ext a
    simp
  have hw : ξ₀ ≫ s = spMap (IsFractionRing.lift hinj) ≫ spMap (algebraMap (𝓞 F) F) :=
    hφ.symm.trans ((congrArg Spec.map hb.symm).trans (Spec.map_comp _ _))
  refine ⟨IsFractionRing.lift hinj, pullback.lift ξ₀ _ hw, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
  apply isCptGen_of_isIso_stalkMap (pullback.fst _ _) (isIso_stalkMap_fst s)
  rwa [pullback.lift_fst]

end GlobalTheory.CompanionTheory.Ar.GenFibre
