import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ProjectiveSpaceOverSpec

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing

namespace GlobalTheory.NCyc

structure StrictLoc (X : Scheme.{0}) (x : X) where

  A : Type
  [ring : CommRing A]
  [isLocal : IsLocalRing A]

  φ : X.presheaf.stalk x →+* A
  isStrictHenselisation : IndefiniteRowSideFullHecke.ProjectiveSpaceOverSpec.IsStrictHenselisation φ

attribute [instance] StrictLoc.ring StrictLoc.isLocal

namespace StrictLoc

variable {X : Scheme.{0}} {x : X}

abbrev scheme (L : StrictLoc X x) : Scheme.{0} := Spec (CommRingCat.of L.A)

def toX (L : StrictLoc X x) : L.scheme ⟶ X :=
  Spec.map (CommRingCat.ofHom L.φ) ≫ X.fromSpecStalk x

theorem henselian (L : StrictLoc X x) : HenselianLocalRing L.A := L.isStrictHenselisation.1

theorem isSepClosed (L : StrictLoc X x) : IsSepClosed (ResidueField L.A) := L.isStrictHenselisation.2.1

def ofStrictlyHenselian (R : Type) [CommRing R] [HenselianLocalRing R] [IsSepClosed (ResidueField R)] :
    StrictLoc (Spec (CommRingCat.of R)) (closedPoint R) where
  A := R
  φ := (stalkClosedPointIso (CommRingCat.of R)).hom.hom
  isStrictHenselisation := by
    have hb : Function.Bijective (stalkClosedPointIso (CommRingCat.of R)).hom.hom :=
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance)
    refine ⟨inferInstance, inferInstance, ?_, ?_⟩
    · refine ⟨fun a ha => ?_⟩
      have := ha.map (RingEquiv.ofBijective _ hb).symm
      rwa [show (RingEquiv.ofBijective _ hb).symm ((stalkClosedPointIso (CommRingCat.of R)).hom.hom a) = a from
        (RingEquiv.ofBijective _ hb).symm_apply_apply a] at this
    · exact MorphismProperty.le_ind _ _ (RingHom.Etale.of_bijective hb)

end StrictLoc

def SpecialPoint {O : Type} [CommRing O] [IsLocalRing O] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) : Type :=
  {x : X // p x = closedPoint O}

section Milnor

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {O : Type} [CommRing O] (K : Type) [Field K] [Algebra O K]

abbrev gfib {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) : Scheme.{0} := GlobalTheory.Et.fibre g (algebraMap O K)

def gfibAut {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) : gfib K g ⟶ gfib K g :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K))) (by
    rw [Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, pullback.condition]
    congr 3
    ext a
    simp)

@[reassoc] theorem gfibAut_fst {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) :
    gfibAut K g σ ≫ pullback.fst _ _ = pullback.fst _ _ := pullback.lift_fst _ _ _

@[reassoc] theorem gfibAut_snd {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ : K ≃ₐ[O] K) :
    gfibAut K g σ ≫ pullback.snd _ _ = pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom (σ : K →+* K)) :=
  pullback.lift_snd _ _ _

theorem gfibAut_one {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) : gfibAut K g 1 = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [gfibAut_fst, Category.id_comp]
  · have h : CommRingCat.ofHom ((1 : K ≃ₐ[O] K) : K →+* K) = 𝟙 _ := by ext a; rfl
    rw [gfibAut_snd, h, Spec.map_id, Category.id_comp, Category.comp_id]

theorem gfibAut_mul {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (σ τ : K ≃ₐ[O] K) :
    gfibAut K g (σ * τ) = gfibAut K g σ ≫ gfibAut K g τ := by
  apply pullback.hom_ext
  · rw [Category.assoc, gfibAut_fst, gfibAut_fst, gfibAut_fst]
  · have h : CommRingCat.ofHom ((σ * τ : K ≃ₐ[O] K) : K →+* K) =
        CommRingCat.ofHom (τ : K →+* K) ≫ CommRingCat.ofHom (σ : K →+* K) := by ext a; rfl
    rw [Category.assoc, gfibAut_snd, gfibAut_snd, gfibAut_snd_assoc, h, Spec.map_comp]

def gfibRep {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) (n : ℕ) :
    Representation R (K ≃ₐ[O] K) (GlobalTheory.Et.H R n (gfib K g)) where
  toFun σ := GlobalTheory.Et.pull R n (gfibAut K g σ)
  map_one' := by rw [gfibAut_one, GlobalTheory.Et.pull_id]; rfl
  map_mul' σ τ := by rw [gfibAut_mul, GlobalTheory.Et.pull_comp]; rfl

def gfibMap {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)} (u : T ⟶ T')
    (hu : u ≫ g' = g) : gfib K g ⟶ gfib K g' :=
  pullback.lift (pullback.fst _ _ ≫ u) (pullback.snd _ _) (by rw [Category.assoc, hu, pullback.condition])

@[reassoc] theorem gfibMap_fst {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) : gfibMap K u hu ≫ pullback.fst _ _ = pullback.fst _ _ ≫ u := pullback.lift_fst _ _ _

@[reassoc] theorem gfibMap_snd {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) : gfibMap K u hu ≫ pullback.snd _ _ = pullback.snd _ _ := pullback.lift_snd _ _ _

theorem gfibMap_id {T : Scheme.{0}} (g : T ⟶ Spec (CommRingCat.of O)) :
    gfibMap K (𝟙 T) (Category.id_comp g) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp [gfibMap]

theorem gfibMap_comp {T T' T'' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    {g'' : T'' ⟶ Spec (CommRingCat.of O)} (u : T ⟶ T') (hu : u ≫ g' = g) (v : T' ⟶ T'') (hv : v ≫ g'' = g') :
    gfibMap K (u ≫ v) (by rw [Category.assoc, hv, hu]) = gfibMap K u hu ≫ gfibMap K v hv := by
  apply pullback.hom_ext
  · rw [gfibMap_fst, Category.assoc, gfibMap_fst, gfibMap_fst_assoc]
  · rw [gfibMap_snd, Category.assoc, gfibMap_snd, gfibMap_snd]

theorem gfibMap_aut {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) (σ : K ≃ₐ[O] K) :
    gfibAut K g σ ≫ gfibMap K u hu = gfibMap K u hu ≫ gfibAut K g' σ := by
  apply pullback.hom_ext
  · rw [Category.assoc, Category.assoc, gfibMap_fst, gfibAut_fst, gfibAut_fst_assoc, gfibMap_fst]
  · rw [Category.assoc, Category.assoc, gfibMap_snd, gfibAut_snd, gfibAut_snd, gfibMap_snd_assoc]

def gfibPull {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)} (u : T ⟶ T')
    (hu : u ≫ g' = g) (n : ℕ) : GlobalTheory.Et.H R n (gfib K g') →ₗ[R] GlobalTheory.Et.H R n (gfib K g) :=
  GlobalTheory.Et.pull R n (gfibMap K u hu)

theorem gfibPull_rep {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (u : T ⟶ T') (hu : u ≫ g' = g) (n : ℕ) (σ : K ≃ₐ[O] K) :
    (gfibPull R K u hu n).comp (gfibRep R K g' n σ) = (gfibRep R K g n σ).comp (gfibPull R K u hu n) := by
  change (GlobalTheory.Et.pull R n (gfibMap K u hu)).comp (GlobalTheory.Et.pull R n (gfibAut K g' σ)) =
    (GlobalTheory.Et.pull R n (gfibAut K g σ)).comp (GlobalTheory.Et.pull R n (gfibMap K u hu))
  rw [← GlobalTheory.Et.pull_comp, ← GlobalTheory.Et.pull_comp, gfibMap_aut]

end Milnor

end GlobalTheory.NCyc

namespace GlobalTheory.NCyc

section Stalk

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (K : Type) [Field K] [Algebra O K]
variable [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K]
variable {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

abbrev milnor [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {x : X} (L : StrictLoc X x) : Scheme.{0} := gfib K (L.toX ≫ p)

def stalk [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Type 1 := GlobalTheory.Et.H R n (milnor K p L)

instance (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : AddCommGroup (stalk R K p n x L) :=
  inferInstanceAs (AddCommGroup (GlobalTheory.Et.H R n (milnor K p L)))

instance (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Module R (stalk R K p n x L) :=
  inferInstanceAs (Module R (GlobalTheory.Et.H R n (milnor K p L)))

def inertia (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Representation R (K ≃ₐ[O] K) (stalk R K p n x L) :=
  gfibRep R K (L.toX ≫ p) n

variable {p} {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)}

def stalkPull (f : X ⟶ Y) (hf : f ≫ q = p) {x : SpecialPoint p} {y : SpecialPoint q} (L : StrictLoc X x.1)
    (M : StrictLoc Y y.1) (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f) (n : ℕ) :
    stalk R K q n y M →ₗ[R] stalk R K p n x L :=
  gfibPull R K h (by rw [← Category.assoc, hh, Category.assoc, hf]) n

theorem stalkPull_inertia (f : X ⟶ Y) (hf : f ≫ q = p) {x : SpecialPoint p} {y : SpecialPoint q}
    (L : StrictLoc X x.1) (M : StrictLoc Y y.1) (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f) (n : ℕ)
    (σ : K ≃ₐ[O] K) :
    (stalkPull R K f hf L M h hh n).comp (inertia R K q n y M σ) =
      (inertia R K p n x L σ).comp (stalkPull R K f hf L M h hh n) :=
  gfibPull_rep R K h _ n σ

theorem stalkPull_id {x : SpecialPoint p} (L : StrictLoc X x.1) (n : ℕ) :
    stalkPull R K (𝟙 X) (Category.id_comp p) L L (𝟙 _) (by rw [Category.id_comp, Category.comp_id]) n =
      LinearMap.id := by
  change GlobalTheory.Et.pull R n (gfibMap K (𝟙 _) _) = _
  rw [gfibMap_id, GlobalTheory.Et.pull_id]; rfl

theorem stalkPull_comp {Z : Scheme.{0}} {r : Z ⟶ Spec (CommRingCat.of O)} (f : X ⟶ Y) (hf : f ≫ q = p) (g : Y ⟶ Z)
    (hg : g ≫ r = q) {x : SpecialPoint p} {y : SpecialPoint q} {z : SpecialPoint r} (L : StrictLoc X x.1)
    (M : StrictLoc Y y.1) (N : StrictLoc Z z.1) (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f)
    (k : M.scheme ⟶ N.scheme) (hk : k ≫ N.toX = M.toX ≫ g) (n : ℕ) :
    stalkPull R K (f ≫ g) (by rw [Category.assoc, hg, hf]) L N (h ≫ k)
        (by rw [Category.assoc, hk, ← Category.assoc, hh, Category.assoc]) n =
      (stalkPull R K f hf L M h hh n).comp (stalkPull R K g hg M N k hk n) := by
  change GlobalTheory.Et.pull R n (gfibMap K (h ≫ k) _) = (GlobalTheory.Et.pull R n (gfibMap K h _)).comp (GlobalTheory.Et.pull R n (gfibMap K k _))
  rw [gfibMap_comp K h _ k _, GlobalTheory.Et.pull_comp]

variable (p)

abbrev pushMilnor [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {X' : Scheme.{0}} (π : X' ⟶ X) {x : X} (L : StrictLoc X x) : Scheme.{0} :=
  gfib K (pullback.snd π L.toX ≫ L.toX ≫ p)

def pushStalk [IsSepClosed (ResidueField O)] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : Type 1 :=
  GlobalTheory.Et.H R n (pushMilnor K p π L)

instance {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    AddCommGroup (pushStalk R K p π n x L) := inferInstanceAs (AddCommGroup (GlobalTheory.Et.H R n (pushMilnor K p π L)))

instance {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    Module R (pushStalk R K p π n x L) := inferInstanceAs (Module R (GlobalTheory.Et.H R n (pushMilnor K p π L)))

def pushInertia {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    Representation R (K ≃ₐ[O] K) (pushStalk R K p π n x L) :=
  gfibRep R K (pullback.snd π L.toX ≫ L.toX ≫ p) n

def pushAut {X' : Scheme.{0}} (π : X' ⟶ X) (g : X' ⟶ X') (hg : g ≫ π = π) (n : ℕ) (x : SpecialPoint p)
    (L : StrictLoc X x.1) : pushStalk R K p π n x L →ₗ[R] pushStalk R K p π n x L :=
  gfibPull R K (pullback.map π L.toX π L.toX g (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hg]) (by simp))
    (by rw [← Category.assoc, pullback.lift_snd, Category.comp_id]) n

theorem pushAut_congr {X' : Scheme.{0}} (π : X' ⟶ X) {g g' : X' ⟶ X'} (e : g = g') (hg : g ≫ π = π) (hg' : g' ≫ π = π)
    (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) : pushAut R K p π g hg n x L = pushAut R K p π g' hg' n x L := by
  subst e; rfl

theorem pushAut_id {X' : Scheme.{0}} (π : X' ⟶ X) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) :
    pushAut R K p π (𝟙 _) (Category.id_comp _) n x L = LinearMap.id := by
  unfold pushAut gfibPull
  erw [← GlobalTheory.Et.pull_id, ← gfibMap_id]
  congr 2
  apply pullback.hom_ext <;> simp only [pullback.map, pullback.lift_fst, pullback.lift_snd, Category.comp_id,
    Category.id_comp]

theorem pushAut_comp {X' : Scheme.{0}} (π : X' ⟶ X) (g g' : X' ⟶ X') (hg : g ≫ π = π) (hg' : g' ≫ π = π) (n : ℕ)
    (x : SpecialPoint p) (L : StrictLoc X x.1) :
    pushAut R K p π (g ≫ g') (by rw [Category.assoc, hg', hg]) n x L =
      (pushAut R K p π g hg n x L).comp (pushAut R K p π g' hg' n x L) := by
  unfold pushAut gfibPull
  erw [← GlobalTheory.Et.pull_comp, ← gfibMap_comp]
  congr 2
  apply pullback.hom_ext <;> simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
    pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

theorem pushAut_inertia {X' : Scheme.{0}} (π : X' ⟶ X) (g : X' ⟶ X') (hg : g ≫ π = π) (n : ℕ) (x : SpecialPoint p)
    (L : StrictLoc X x.1) (σ : K ≃ₐ[O] K) :
    (pushAut R K p π g hg n x L).comp (pushInertia R K p π n x L σ) =
      (pushInertia R K p π n x L σ).comp (pushAut R K p π g hg n x L) :=
  gfibPull_rep R K _ _ n σ

def pushAct {X' : Scheme.{0}} (π : X' ⟶ X) {G : Type} [Group G] (ρ : G →* End X') (hρ : ∀ g, ρ g ≫ π = π) (n : ℕ)
    (x : SpecialPoint p) (L : StrictLoc X x.1) : Representation R G (pushStalk R K p π n x L) where
  toFun g := pushAut R K p π (ρ g⁻¹) (hρ _) n x L
  map_one' := by
    rw [pushAut_congr R K p π (show ρ 1⁻¹ = 𝟙 X' by rw [inv_one, map_one]; rfl) _ (Category.id_comp _),
      pushAut_id]
    rfl
  map_mul' g h := by
    rw [pushAut_congr R K p π (show ρ (g * h)⁻¹ = ρ g⁻¹ ≫ ρ h⁻¹ by rw [mul_inv_rev, map_mul]; rfl) _
      (by rw [Category.assoc, hρ, hρ]), pushAut_comp]
    rfl

theorem pushAct_apply {X' : Scheme.{0}} (π : X' ⟶ X) {G : Type} [Group G] (ρ : G →* End X') (hρ : ∀ g, ρ g ≫ π = π)
    (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) (g : G) :
    pushAct R K p π ρ hρ n x L g = pushAut R K p π (ρ g⁻¹) (hρ _) n x L := rfl

theorem pushAct_inertia {X' : Scheme.{0}} (π : X' ⟶ X) {G : Type} [Group G] (ρ : G →* End X')
    (hρ : ∀ g, ρ g ≫ π = π) (n : ℕ) (x : SpecialPoint p) (L : StrictLoc X x.1) (g : G) (σ : K ≃ₐ[O] K) :
    (pushAct R K p π ρ hρ n x L g).comp (pushInertia R K p π n x L σ) =
      (pushInertia R K p π n x L σ).comp (pushAct R K p π ρ hρ n x L g) :=
  pushAut_inertia R K p π _ (hρ _) n x L σ

end Stalk

section Examples

abbrev SpecialPoint.closed (O : Type) [CommRing O] [IsLocalRing O] : SpecialPoint (𝟙 (Spec (CommRingCat.of O))) :=
  ⟨closedPoint O, rfl⟩

example : StrictLoc (Spec (CommRingCat.of ℂ)) (closedPoint ℂ) := by
  haveI : IsSepClosed (ResidueField ℂ) := by
    have e : ℂ ≃+* ResidueField ℂ := RingEquiv.ofBijective (residue ℂ) ⟨(residue ℂ).injective, residue_surjective⟩
    haveI : IsAlgClosed (ResidueField ℂ) := IsAlgClosed.of_ringEquiv ℂ _ e
    infer_instance
  exact StrictLoc.ofStrictlyHenselian ℂ

example (O : Type) [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)] (K : Type) [Field K]
    [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K] [Algebra.IsAlgebraic O K] (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (n : ℕ) : Type 1 :=
  stalk R K (𝟙 (Spec (CommRingCat.of O))) n (SpecialPoint.closed O) (StrictLoc.ofStrictlyHenselian O)

end Examples

end GlobalTheory.NCyc

namespace GlobalTheory.NCyc

theorem henselian_powerSeries_complex : HenselianLocalRing (PowerSeries ℂ) := by
  have : IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  exact { is_henselian := fun f hf a h1 h2 =>
    HenselianRing.is_henselian (I := maximalIdeal (PowerSeries ℂ)) f hf a h1 (h2.map _) }

theorem isSepClosed_residueField_powerSeries_complex : IsSepClosed (ResidueField (PowerSeries ℂ)) := by
  let f : ℂ →+* ResidueField (PowerSeries ℂ) := (residue _).comp PowerSeries.C
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨g, rfl⟩ := residue_surjective y
    refine ⟨PowerSeries.constantCoeff g, ?_⟩
    simp only [f, RingHom.comp_apply]
    rw [← sub_eq_zero, ← map_sub, residue_eq_zero_iff, PowerSeries.maximalIdeal_eq_span_X, Ideal.mem_span_singleton,
      PowerSeries.X_dvd_iff]
    simp
  haveI : IsAlgClosed (ResidueField (PowerSeries ℂ)) :=
    IsAlgClosed.of_ringEquiv ℂ _ (RingEquiv.ofBijective f ⟨f.injective, hs⟩)
  infer_instance

attribute [local instance] henselian_powerSeries_complex isSepClosed_residueField_powerSeries_complex

theorem faithfulSMul_powerSeries_complex :
    FaithfulSMul (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) := by
  rw [faithfulSMul_iff_algebraMap_injective, IsScalarTower.algebraMap_eq (PowerSeries ℂ) (FractionRing (PowerSeries ℂ))]
  exact (algebraMap (FractionRing (PowerSeries ℂ)) _).injective.comp (IsFractionRing.injective _ _)

theorem isAlgebraic_powerSeries_complex :
    Algebra.IsAlgebraic (PowerSeries ℂ) (AlgebraicClosure (FractionRing (PowerSeries ℂ))) :=
  ⟨fun x => (IsFractionRing.isAlgebraic_iff (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) _).2
    (Algebra.IsAlgebraic.isAlgebraic x)⟩

attribute [local instance] faithfulSMul_powerSeries_complex isAlgebraic_powerSeries_complex

example : StrictLoc (Spec (CommRingCat.of (PowerSeries ℂ))) (closedPoint (PowerSeries ℂ)) :=
  StrictLoc.ofStrictlyHenselian (PowerSeries ℂ)

example (n : ℕ) : Representation ℤ_[3] (AlgebraicClosure (FractionRing (PowerSeries ℂ)) ≃ₐ[PowerSeries ℂ]
    AlgebraicClosure (FractionRing (PowerSeries ℂ)))
    (stalk ℤ_[3] (AlgebraicClosure (FractionRing (PowerSeries ℂ))) (𝟙 (Spec (CommRingCat.of (PowerSeries ℂ)))) n
      (SpecialPoint.closed _) (StrictLoc.ofStrictlyHenselian (PowerSeries ℂ))) :=
  inertia _ _ _ n _ _

end GlobalTheory.NCyc
