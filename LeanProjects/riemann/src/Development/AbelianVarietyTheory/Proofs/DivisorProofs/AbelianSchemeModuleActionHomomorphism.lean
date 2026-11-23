import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AbelianSchemeIdPowFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionWithRangeInOpen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDivLocal

theorem exists_pow_eq {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V]
    (hc : IsAdicComplete (maximalIdeal V) V) (hk : IsAlgClosed (ResidueField V))
    (B : Over (Sp V)) [GrpObj B] (hB : IsAbelianScheme B) (n : ℕ) (hn : IsUnit (n : V))
    (P : 𝟙_ (Over (Sp V)) ⟶ B) : ∃ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = P := by
  have hn' : IsUnit (n : Γ(Sp V, ⊤)) := by
    simpa using hn.map (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom
  obtain ⟨-, hfin, het, hsurj⟩ :=
    GlobalTheory.abelianScheme_id_pow_finite_etale_surjective (Sp V) B n hB hn'
  set m : B ⟶ B := (𝟙 B) ^ n with hm
  let U : Over (Sp V) := Over.mk (pullback.snd m.left P.left)
  have hU : Smooth U.hom := by dsimp [U]; infer_instance
  let r : Sp (ResidueField V) ⟶ Sp V := spMap (residue V)
  let P₀ : Sp (ResidueField V) ⟶ B.left := r ≫ P.left
  have : CompactSpace ↥(pullback m.left P₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd m.left P₀)
  obtain ⟨p, -⟩ := (pullback.snd m.left P₀).surjective (default : PrimeSpectrum (ResidueField V))
  obtain ⟨z, -, hz⟩ :=
    isClosed_univ.exists_closed_singleton (X := ↥(pullback m.left P₀)) ⟨p, trivial⟩
  have hw := pointOfClosedPoint_comp (pullback.snd m.left P₀) z hz
  let x₀ : Sp (ResidueField V) ⟶ U.left :=
    pullback.lift (pointOfClosedPoint (pullback.snd m.left P₀) z hz ≫ pullback.fst _ _) r (by
      rw [Category.assoc, pullback.condition, ← Category.assoc, hw, Category.id_comp])
  have hx₀ : x₀ ≫ U.hom = spMap ((residue V).comp (RingHom.id V)) := by
    rw [RingHom.comp_id]
    exact pullback.lift_snd _ _ _
  obtain ⟨a, ha, -⟩ :=
    GlobalTheory.HenselLift.exists_lift_mem_open V V hc (RingHom.id V) U hU x₀ hx₀ ⊤ (by simp)
  have ha' : a ≫ pullback.snd m.left P.left = 𝟙 _ := by
    refine ha.trans ?_
    rw [spMap, show CommRingCat.ofHom (RingHom.id V) = 𝟙 (CommRingCat.of V) from rfl, Spec.map_id]
  have key : (a ≫ pullback.fst m.left P.left) ≫ m.left = P.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, ha', Category.id_comp]
  refine ⟨Over.homMk (a ≫ pullback.fst m.left P.left) ?_, ?_⟩
  · rw [← Over.w m, ← Category.assoc, key]
    exact Over.w P
  · have e : ∀ Q : 𝟙_ (Over (Sp V)) ⟶ B, Q ^ n = Q ≫ m := fun Q => by
      rw [hm, comp_pow, Category.comp_id]
    rw [e]
    exact Over.OverMorphism.ext key

end GlobalTheory.AbDivLocal

namespace GlobalTheory.AbDivLocal

abbrev ptsModule {S : Scheme.{0}} (T : Over S) (B : Over S) [GrpObj B] [IsCommMonObj B] (O : Type)
    [CommRing O] (a : OAct O B) : Module O (Additive (T ⟶ B)) where
  smul o p := Additive.ofMul (p.toMul ≫ a.act o)
  one_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 1) = p
    rw [a.one, Category.comp_id]; rfl
  mul_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o * o')) =
      Additive.ofMul ((p.toMul ≫ a.act o') ≫ a.act o)
    rw [mul_comm, a.mul, Category.assoc]
  smul_zero o := by
    change Additive.ofMul ((1 : T ⟶ B) ≫ a.act o) = Additive.ofMul 1
    haveI := a.hom o
    rw [one_comp]
  smul_add o p q := by
    change Additive.ofMul ((p.toMul * q.toMul) ≫ a.act o) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (q.toMul ≫ a.act o))
    haveI := a.hom o
    rw [mul_comp]
  add_smul o o' p := by
    change Additive.ofMul (p.toMul ≫ a.act (o + o')) =
      Additive.ofMul ((p.toMul ≫ a.act o) * (p.toMul ≫ a.act o'))
    rw [a.add, comp_mul]
  zero_smul p := by
    change Additive.ofMul (p.toMul ≫ a.act 0) = Additive.ofMul 1
    have h0 : a.act 0 = 1 := by
      have h := a.add 0 0
      rw [add_zero] at h
      exact (mul_eq_left.mp h.symm)
    rw [h0, comp_one]

theorem exists_divided_linear : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [IsNoetherianRing V], IsAdicComplete (maximalIdeal V) V → IsAlgClosed (ResidueField V) → ∀ (B : Over (Sp V)) [GrpObj B], IsAbelianScheme B → ∀ (O : Type) [CommRing O] [IsDomain O] [Module.Finite ℤ O] (a : OAct O B) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X] (x : X → (𝟙_ (Over (Sp V)) ⟶ B)), (∀ y z, x (y + z) = x y * x z) → (∀ (o : O) y, x (o • y) = x y ≫ a.act o) → ∀ n : ℕ, IsUnit (n : V) → ∃ x' : X → (𝟙_ (Over (Sp V)) ⟶ B), (∀ y z, x' (y + z) = x' y * x' z) ∧ (∀ (o : O) y, x' (o • y) = x' y ≫ a.act o) ∧ ∀ y, x' (n • y) = x y := by
  intro V _ _ _ _ hc hk B _ hB O _ _ _ a X _ _ _ _ x hadd hsmul n hn
  haveI := hB.comm
  letI := ptsModule (𝟙_ (Over (Sp V))) B O a
  let g : X →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    { toFun := fun y => Additive.ofMul (x y)
      map_add' := fun y z => by rw [hadd]; rfl
      map_smul' := fun o y => by rw [hsmul]; rfl }
  let f : Additive (𝟙_ (Over (Sp V)) ⟶ B) →ₗ[O] Additive (𝟙_ (Over (Sp V)) ⟶ B) :=
    n • LinearMap.id
  have hf : Function.Surjective f := by
    intro p
    obtain ⟨Q, hQ⟩ := exists_pow_eq hc hk B hB n hn p.toMul
    refine ⟨Additive.ofMul Q, ?_⟩
    change n • Additive.ofMul Q = p
    rw [← ofMul_pow, hQ]; rfl
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  refine ⟨fun y => (h y).toMul, fun y z => by
      change (h (y + z)).toMul = (h y).toMul * (h z).toMul
      rw [map_add]; rfl,
    fun o y => by
      change (h (o • y)).toMul = (h y).toMul ≫ a.act o
      rw [map_smul]; rfl, fun y => ?_⟩
  have e : n • h y = Additive.ofMul (x y) := LinearMap.congr_fun hh y
  change (h (n • y)).toMul = x y
  rw [map_nsmul, e]; rfl

end GlobalTheory.AbDivLocal
