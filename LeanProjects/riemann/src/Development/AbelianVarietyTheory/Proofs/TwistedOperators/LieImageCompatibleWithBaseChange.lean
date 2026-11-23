import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsTranslSum

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HeckeFrCompare GlobalTheory.PlaceInt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.HkIntegral

namespace GlobalTheory.LieImageBC

theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) :=
  (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom g)).symm

theorem epi_of_local {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B] (d : A →+* B)
    [IsLocalHom d] (hd : Function.Injective d) : Epi (spMap d) := by
  refine ⟨fun {X} a b h => ?_⟩
  obtain ⟨⟨x, f, hf⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective a
  obtain ⟨⟨y, g, hg⟩, rfl⟩ := (SpecToEquivOfLocalRing X (CommRingCat.of A)).symm.surjective b
  have h1 : IsLocalHom (f ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d f.hom
  have h2 : IsLocalHom (g ≫ CommRingCat.ofHom d).hom := by
    rw [CommRingCat.hom_comp]; exact RingHom.isLocalHom_comp d g.hom
  have h3 : (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨x, _, h1⟩ =
      (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm ⟨y, _, h2⟩ := by
    simpa [SpecToEquivOfLocalRing] using h
  have h4 := (SpecToEquivOfLocalRing X (CommRingCat.of B)).symm.injective h3
  obtain rfl : x = y := congrArg Sigma.fst h4
  have h5 : f ≫ CommRingCat.ofHom d = g ≫ CommRingCat.ofHom d :=
    congrArg Subtype.val (eq_of_heq (Sigma.mk.inj h4).2)
  obtain rfl : f = g := by
    ext s
    exact hd (congrArg (fun k => k.hom s) h5)
  rfl

theorem epi_dualMap {K L : Type} [Field K] [Field L] (φ : K →+* L) : Epi (spMap (dualMap φ)) := by
  have : IsLocalHom (dualMap φ) := ⟨fun a ha => by
    rw [TrivSqZeroExt.isUnit_iff_isUnit_fst, isUnit_iff_ne_zero] at ha ⊢
    intro h
    exact ha (by simp [dualMap, h])⟩
  refine epi_of_local _ fun a b h => ?_
  have h1 := congrArg TrivSqZeroExt.fst h
  have h2 := congrArg TrivSqZeroExt.snd h
  ext
  · exact φ.injective (by simpa [dualMap] using h1)
  · exact φ.injective (by simpa [dualMap] using h2)

theorem dual_eps {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) (a : S) :
    spMap (dualMap ψ) ≫ spMap (epsMul a) = spMap (epsMul (ψ a)) ≫ spMap (dualMap ψ) := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, epsMul, TrivSqZeroExt.algebraMap_eq_inl]

theorem dual_alg {S T : Type} [CommRing S] [CommRing T] (ψ : S →+* T) :
    spMap (dualMap ψ) ≫ spMap (algebraMap S (DualNumber S)) = spMap (algebraMap T (DualNumber T)) ≫ spMap ψ := by
  rw [sp_comp, sp_comp]
  congr 1
  ext s <;> simp [dualMap, TrivSqZeroExt.algebraMap_eq_inl]

theorem isLieImageH_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (K L : Type) [Field K] [Field L] (φ : K →+* L) (x x' : Sp K ⟶ Xo.X) (w w' : Sp L ⟶ Xo.X) (f : Fib Xo x ⟶ Fib Xo x') (g : Fib Xo w ⟶ Fib Xo w') (p : ℕ) (v u : Sp (DualNumber K) ⟶ Xo.univ.t.G.left), IsBC φ f g → IsTanAt x v → (IsLieImageH p f.left v u ↔ IsLieImageH p g.left (spMap (dualMap φ) ≫ v) (spMap (dualMap φ) ≫ u)) := by
  intro E _ _ _ H Dw l Xo K L _ _ φ x x' w w' f g p v u hbc hv
  obtain ⟨rfl, rfl, hbc⟩ := hbc
  let π : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom x :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  let π' : pullback Xo.univ.t.G.hom (spMap φ ≫ x') ⟶ pullback Xo.univ.t.G.hom x' :=
    pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ spMap φ) (by rw [pullback.condition, Category.assoc])
  have hπ1 : π ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2 : π ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hπ1' : π' ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _
  have hπ2' : π' ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap φ := pullback.lift_snd _ _ _
  have hc := hbc π π' hπ1 hπ2 hπ1' hπ2'
  generalize hF : (f.left : pullback Xo.univ.t.G.hom x ⟶ pullback Xo.univ.t.G.hom x') = F at hc ⊢
  generalize hG : (g.left : pullback Xo.univ.t.G.hom (spMap φ ≫ x) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x')) = G
    at hc ⊢
  have key : ∀ (a : Sp (DualNumber K) ⟶ pullback Xo.univ.t.G.hom x)
      (b : Sp (DualNumber L) ⟶ pullback Xo.univ.t.G.hom (spMap φ ≫ x)),
      a ≫ pullback.fst _ _ = v → a ≫ pullback.snd _ _ = spMap (algebraMap K (DualNumber K)) →
      b ≫ pullback.fst _ _ = spMap (dualMap φ) ≫ v → b ≫ pullback.snd _ _ = spMap (algebraMap L (DualNumber L)) →
      spMap (dualMap φ) ≫ spMap (epsMul ((p : K)⁻¹)) ≫ a ≫ F ≫ pullback.fst _ _ =
        spMap (epsMul ((p : L)⁻¹)) ≫ b ≫ G ≫ pullback.fst _ _ := by
    intro a b ha1 ha2 hb1 hb2
    have hab : b ≫ π = spMap (dualMap φ) ≫ a := by
      apply pullback.hom_ext
      · rw [Category.assoc, hπ1, hb1, Category.assoc, ha1]
      · rw [Category.assoc, hπ2, ← Category.assoc, hb2, Category.assoc, ha2, dual_alg]
    have hGF : G ≫ pullback.fst _ _ = π ≫ F ≫ pullback.fst _ _ := by
      rw [← hπ1', ← Category.assoc, hc, Category.assoc]
    rw [hGF, ← Category.assoc b, hab, ← Category.assoc, dual_eps, map_inv₀, map_natCast]
    simp only [Category.assoc]
  constructor
  · rintro ⟨a, ha1, ha2, rfl⟩
    refine ⟨pullback.lift (spMap (dualMap φ) ≫ v) (spMap (algebraMap L (DualNumber L))) ?_,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
      key a _ ha1 ha2 (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)⟩
    rw [Category.assoc, hv.1, ← Category.assoc, dual_alg, Category.assoc]
  · rintro ⟨b, hb1, hb2, hu⟩
    refine ⟨pullback.lift v (spMap (algebraMap K (DualNumber K))) hv.1,
      pullback.lift_fst _ _ _, pullback.lift_snd _ _ _, ?_⟩
    have := epi_dualMap φ
    rw [← cancel_epi (spMap (dualMap φ)), hu]
    exact (key _ b (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hb1 hb2).symm

end GlobalTheory.LieImageBC
