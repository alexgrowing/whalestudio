import Development.EtaleCohomology.EtaleSheaves.LeafTwistPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafTwSecPf

def ρ {B : Type} [CommRing B] (U : Over (Spec (CommRingCat.of B))) : B →+* Γ(U.left, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ U.hom.appTop).hom

abbrev Pr (q : ℕ) (k : ℤ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Over.forget X).op ⋙ (Scheme.Γ ⋙ twF q k)

abbrev Cst (q : ℕ) (X : Scheme.{0}) : (Over X)ᵒᵖ ⥤ ModuleCat.{1} (ULift.{1} (ZMod q)) :=
  (Functor.const _).obj (ModuleCat.of _ (ULift.{1} (ZMod q)))

def gen {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) (U : Over (Spec (CommRingCat.of B))) :
    (Pr q k _).obj (op U) :=
  Submodule.Quotient.mk (Finsupp.single (Prim.map (ρ U) ζ) 1)

theorem gen_map {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) {U V : Over (Spec (CommRingCat.of B))}
    (f : V ⟶ U) : ((Pr q k _).map f.op).hom (gen ζ k U) = gen ζ k V := by
  change Submodule.Quotient.mk (Finsupp.mapDomain _ (Finsupp.single _ _)) = _
  rw [Finsupp.mapDomain_single]
  have h : Prim.map (Scheme.Γ.map f.left.op).hom (Prim.map (ρ U) ζ) = Prim.map (ρ V) ζ := by
    apply Subtype.ext
    change (Scheme.Γ.map f.left.op).hom (ρ U ζ.1) = ρ V ζ.1
    simp only [ρ]
    rw [← Over.w f]
    first | rfl | simp [Scheme.Hom.comp_appTop] | simp
  exact congrArg (fun z => Submodule.Quotient.mk (p := twRel q k _) (Finsupp.single z (1 : ULift.{1} (ZMod q)))) h

def cmap {q : ℕ} {B : Type} [CommRing B] (ζ : Prim q B) (k : ℤ) : Cst q _ ⟶ Pr q k (Spec (CommRingCat.of B)) where
  app U := ModuleCat.ofHom (LinearMap.toSpanSingleton _ _ (gen ζ k U.unop))
  naturality := by
    intro U V f
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    change (LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k V.unop)) (1 : ULift.{1} (ZMod q)) =
      ((Pr q k _).map f).hom ((LinearMap.toSpanSingleton (ULift.{1} (ZMod q)) _ (gen ζ k U.unop)) (1 : ULift.{1} (ZMod q)))
    simp only [LinearMap.toSpanSingleton_apply, one_smul]
    exact (gen_map ζ k f.unop).symm

def LeafTwLB : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  IsIso ((presheafToSheaf (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (ModuleCat.{1} (ULift.{1} (ZMod q)))).map
    (cmap ζ k))

theorem LeafTwSec_of (h : LeafTwLB) : LateralTheory.E.LeafTwistPf.LeafTwSec := by
  intro q _ B _ ζ i j
  let K := (Over.forget (Spec (CommRingCat.of B))).pushforwardContinuousSheafificationCompatibility
    (ModuleCat.{1} (ULift.{1} (ZMod q))) (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) Scheme.etaleTopology
  haveI := h q B ζ i
  haveI := h q B ζ j
  let Φ := (K.app (Scheme.Γ ⋙ twF q i)).symm ≪≫ (asIso ((presheafToSheaf _ _).map (cmap ζ i))).symm ≪≫
    asIso ((presheafToSheaf _ _).map (cmap ζ j)) ≪≫ K.app (Scheme.Γ ⋙ twF q j)
  let Ψ := (sheafToPresheaf _ _).mapIso Φ
  refine ⟨fun U x => (Ψ.app (op (Over.mk x))).toLinearEquiv, ?_⟩
  intro V U g x s
  have := congrArg (fun f => f.hom s) (Ψ.hom.naturality (Over.homMk g : Over.mk (g ≫ x) ⟶ Over.mk x).op)
  exact this

def LeafTwSurj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallySurjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

def LeafTwInj : Prop := ∀ (q : ℕ) [NeZero q] (B : Type) [CommRing B] (ζ : Prim q B) (k : ℤ),
  Presheaf.IsLocallyInjective (Scheme.etaleTopology.over (Spec (CommRingCat.of B))) (cmap ζ k)

theorem LeafTwLB_of (hI : LeafTwInj) (hS : LeafTwSurj) : LeafTwLB := by
  intro q _ B _ ζ k
  haveI := hI q B ζ k
  haveI := hS q B ζ k
  exact (GrothendieckTopology.W_iff _ _).1 (GrothendieckTopology.W_of_isLocallyBijective _ _)

theorem LeafTwSec_of' (hI : LeafTwInj) (hS : LeafTwSurj) : LateralTheory.E.LeafTwistPf.LeafTwSec :=
  LeafTwSec_of (LeafTwLB_of hI hS)

end LateralTheory.E.LeafTwSecPf
