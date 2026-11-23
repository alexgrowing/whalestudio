import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsSepClosedResidueFieldPowerSeriesComplex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NearbyCyclesDegreeZeroEquiv

noncomputable section

open CategoryTheory Limits AlgebraicGeometry IsLocalRing TensorProduct

namespace GlobalTheory.FormalInv

def IsAdicCoef (l : ℕ) [Fact l.Prime] (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] : Prop :=
  (Finite Λ ∧ DiscreteTopology Λ ∧ ∃ k : ℕ, ((l ^ k : ℕ) : Λ) = 0) ∨
  (∃ _ : Algebra ℤ_[l] Λ, Module.Finite ℤ_[l] Λ ∧ IsModuleTopology ℤ_[l] Λ) ∨
  (∃ _ : Algebra ℚ_[l] Λ, IsField Λ ∧ Algebra.IsAlgebraic ℚ_[l] Λ ∧ IsModuleTopology ℚ_[l] Λ)

def IsCompletedStalk {O : Type} [CommRing O] {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O)) (x : X)
    {B : Type} [CommRing B] [Algebra O B] (ψ : X.presheaf.stalk x →+* B) : Prop :=
  (∃ e : AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) ≃+* B,
    ∀ a, e (algebraMap _ (AdicCompletion (maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x)) a) = ψ a) ∧
  Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x ≫ p = Spec.map (CommRingCat.ofHom (algebraMap O B))

section Maps

variable {O : Type} [CommRing O] (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω]
  [IsScalarTower O K Ω]

abbrev formalFibre (O : Type) [CommRing O] [Algebra O K] (B : Type) [CommRing B] [Algebra O B] : Scheme.{0} :=
  GlobalTheory.Et.geom Ω (GlobalTheory.FNC.str K (K ⊗[O] B))

abbrev toSpec (O : Type) [CommRing O] [Algebra O K] (B : Type) [CommRing B] [Algebra O B] :
    Spec (CommRingCat.of (K ⊗[O] B)) ⟶ Spec (CommRingCat.of B) :=
  Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight (R := O) (A := K) (B := B)).toRingHom)

theorem toSpec_str (B : Type) [CommRing B] [Algebra O B] :
    toSpec K O B ≫ Spec.map (CommRingCat.ofHom (algebraMap O B)) =
      GlobalTheory.FNC.str K (K ⊗[O] B) ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) := by
  rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext a
  simp [Algebra.TensorProduct.tmul_one_eq_one_tmul]

theorem spec_tower : Spec.map (CommRingCat.ofHom (algebraMap K Ω)) ≫ Spec.map (CommRingCat.ofHom (algebraMap O K)) =
    Spec.map (CommRingCat.ofHom (algebraMap O Ω)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, ← IsScalarTower.algebraMap_eq]

def toGfib {B : Type} [CommRing B] [Algebra O B] {T : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)}
    (u : Spec (CommRingCat.of B) ⟶ T) (hu : u ≫ g = Spec.map (CommRingCat.ofHom (algebraMap O B))) :
    formalFibre K Ω O B ⟶ GlobalTheory.NCyc.gfib Ω g :=
  pullback.lift (pullback.fst _ _ ≫ toSpec K O B ≫ u) (pullback.snd _ _) (by
    rw [Category.assoc, Category.assoc, hu, toSpec_str, pullback.condition_assoc, spec_tower])

def gfibSemi {T T' : Scheme.{0}} {g : T ⟶ Spec (CommRingCat.of O)} {g' : T' ⟶ Spec (CommRingCat.of O)}
    (σ : O →+* O) (τ : Ω →+* Ω) (hτ : τ.comp (algebraMap O Ω) = (algebraMap O Ω).comp σ) (h : T ⟶ T')
    (hh : h ≫ g' = g ≫ Spec.map (CommRingCat.ofHom σ)) : GlobalTheory.NCyc.gfib Ω g ⟶ GlobalTheory.NCyc.gfib Ω g' :=
  pullback.lift (pullback.fst _ _ ≫ h) (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom τ)) (by
    rw [Category.assoc, hh, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ])

def formalSemi {B B' : Type} [CommRing B] [Algebra O B] [CommRing B'] [Algebra O B']
    (σ : O →+* O) (ρ : K →+* K) (hρ : ρ.comp (algebraMap O K) = (algebraMap O K).comp σ)
    (τ : Ω →+* Ω) (hτ : τ.comp (algebraMap K Ω) = (algebraMap K Ω).comp ρ)
    (γ : B' →+* B) (hγ : γ.comp (algebraMap O B') = (algebraMap O B).comp σ) :
    formalFibre K Ω O B ⟶ formalFibre K Ω O B' :=
  pullback.lift (pullback.fst _ _ ≫ Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom σ ρ γ hρ hγ)))
    (pullback.snd _ _ ≫ Spec.map (CommRingCat.ofHom τ)) (by
    have h1 : Spec.map (CommRingCat.ofHom (Algebra.TensorProduct.mapRingHom σ ρ γ hρ hγ)) ≫
        GlobalTheory.FNC.str K (K ⊗[O] B') = GlobalTheory.FNC.str K (K ⊗[O] B) ≫ Spec.map (CommRingCat.ofHom ρ) := by
      rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp]
      congr 2
      ext a
      simp
    rw [Category.assoc, h1, pullback.condition_assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
      ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hτ])

theorem semi_tower {σ : O →+* O} {ρ : K →+* K} (hρ : ρ.comp (algebraMap O K) = (algebraMap O K).comp σ)
    {τ : Ω →+* Ω} (hτ : τ.comp (algebraMap K Ω) = (algebraMap K Ω).comp ρ) :
    τ.comp (algebraMap O Ω) = (algebraMap O Ω).comp σ := by
  rw [IsScalarTower.algebraMap_eq O K Ω, ← RingHom.comp_assoc, hτ, RingHom.comp_assoc, hρ, RingHom.comp_assoc]

end Maps

section Comparison

open GlobalTheory.NCyc

variable (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
variable (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
variable [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {x : SpecialPoint p}

omit [IsSepClosed (ResidueField O)] in
theorem spec_lift_over (L : StrictLoc X x.1) {B : Type} [CommRing B] [Algebra O B] {ψ : X.presheaf.stalk x.1 →+* B}
    (hψ : IsCompletedStalk p x.1 ψ) {θ : L.A →+* B} (hθ : θ.comp L.φ = ψ) :
    Spec.map (CommRingCat.ofHom θ) ≫ L.toX ≫ p = Spec.map (CommRingCat.ofHom (algebraMap O B)) := by
  rw [← hψ.2, ← hθ, StrictLoc.toX, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, Category.assoc]

def cmp (L : StrictLoc X x.1) {B : Type} [CommRing B] [Algebra O B] {ψ : X.presheaf.stalk x.1 →+* B}
    (hψ : IsCompletedStalk p x.1 ψ) {θ : L.A →+* B} (hθ : θ.comp L.φ = ψ) (n : ℕ) :
    stalk Λ Ω p n x L →ₗ[Λ] GlobalTheory.FNC.H Λ K Ω O n B :=
  GlobalTheory.Et.pull Λ n (toGfib K Ω (Spec.map (CommRingCat.ofHom θ)) (spec_lift_over L hψ hθ))

variable {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {y : SpecialPoint q}

def stalkSemi (σ : O →+* O) (τ : Ω →+* Ω) (hτ : τ.comp (algebraMap O Ω) = (algebraMap O Ω).comp σ)
    (f : X ⟶ Y) (hf : f ≫ q = p ≫ Spec.map (CommRingCat.ofHom σ)) (L : StrictLoc X x.1) (M : StrictLoc Y y.1)
    (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f) (n : ℕ) :
    stalk Λ Ω q n y M →ₗ[Λ] stalk Λ Ω p n x L :=
  GlobalTheory.Et.pull Λ n (gfibSemi Ω (g := L.toX ≫ p) (g' := M.toX ≫ q) σ τ hτ h
    (by rw [← Category.assoc, hh, Category.assoc, hf, Category.assoc]))

end Comparison

open GlobalTheory.NCyc in

def FormalInvarianceSt : Prop :=
  ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O]
    [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
    (K : Type) [Field K] [Algebra O K] [IsFractionRing O K]
    (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
    [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
    (l : ℕ) [Fact l.Prime], IsUnit (l : O) →
  ∀ (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ], IsAdicCoef l Λ →
  ∀ (X : Scheme.{0}) (p : X ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType p] (x : SpecialPoint p),
    IsClosed ({x.1} : Set X) →
  ∀ (L : StrictLoc X x.1) (B : Type) [CommRing B] [Algebra O B] (ψ : X.presheaf.stalk x.1 →+* B)
    (hψ : IsCompletedStalk p x.1 ψ),
    (∃! θ : L.A →+* B, θ.comp L.φ = ψ) ∧
    ∀ (θ : L.A →+* B) (hθ : θ.comp L.φ = ψ) (n : ℕ),
      Function.Bijective (cmp Λ K Ω L hψ hθ n) ∧
      (∀ σ : Ω ≃ₐ[K] Ω, (cmp Λ K Ω L hψ hθ n).comp (inertia Λ Ω p n x L (σ.restrictScalars O)) =
        (GlobalTheory.FNC.gal Λ K Ω O n B σ).comp (cmp Λ K Ω L hψ hθ n)) ∧
      ∀ (Y : Scheme.{0}) (q : Y ⟶ Spec (CommRingCat.of O)) [LocallyOfFiniteType q] (y : SpecialPoint q),
        IsClosed ({y.1} : Set Y) →
      ∀ (M : StrictLoc Y y.1) (B' : Type) [CommRing B'] [Algebra O B'] (ψ' : Y.presheaf.stalk y.1 →+* B')
        (hψ' : IsCompletedStalk q y.1 ψ') (θ' : M.A →+* B') (hθ' : θ'.comp M.φ = ψ')
        (f : X ⟶ Y), f x.1 = y.1 →
      ∀ (h : L.scheme ⟶ M.scheme) (hh : h ≫ M.toX = L.toX ≫ f),
        (∀ (hf : f ≫ q = p) (γ : B' →ₐ[O] B),
          Spec.map (CommRingCat.ofHom (γ : B' →+* B)) ≫ Spec.map (CommRingCat.ofHom ψ') ≫ Y.fromSpecStalk y.1 =
            Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x.1 ≫ f →
          (cmp Λ K Ω L hψ hθ n).comp (stalkPull Λ Ω f hf L M h hh n) =
            (GlobalTheory.FNC.map Λ K Ω O n γ).comp (cmp Λ K Ω M hψ' hθ' n)) ∧
        ∀ (σ : O →+* O) (ρ : K →+* K) (hρ : ρ.comp (algebraMap O K) = (algebraMap O K).comp σ)
          (τ : Ω →+* Ω) (hτ : τ.comp (algebraMap K Ω) = (algebraMap K Ω).comp ρ)
          (hf : f ≫ q = p ≫ Spec.map (CommRingCat.ofHom σ))
          (γ : B' →+* B) (hγ : γ.comp (algebraMap O B') = (algebraMap O B).comp σ),
          Spec.map (CommRingCat.ofHom γ) ≫ Spec.map (CommRingCat.ofHom ψ') ≫ Y.fromSpecStalk y.1 =
            Spec.map (CommRingCat.ofHom ψ) ≫ X.fromSpecStalk x.1 ≫ f →
          (cmp Λ K Ω L hψ hθ n).comp (stalkSemi Λ Ω σ τ (semi_tower K Ω hρ hτ) f hf L M h hh n) =
            (GlobalTheory.Et.pull Λ n (formalSemi K Ω σ ρ hρ τ hτ γ hγ)).comp (cmp Λ K Ω M hψ' hθ' n)

section Formal

open GlobalTheory.NCyc

variable (Λ : Type) [CommRing Λ] [TopologicalSpace Λ] [IsTopologicalRing Λ]
variable {O : Type} [CommRing O] [HenselianLocalRing O] [IsSepClosed (ResidueField O)]
variable (K : Type) [Field K] [Algebra O K] (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
variable [IsAlgClosed Ω] [FaithfulSMul O Ω] [Algebra.IsAlgebraic O Ω]
variable {X : Scheme.{0}} {p : X ⟶ Spec (CommRingCat.of O)} {x : SpecialPoint p}

variable {Y : Scheme.{0}} {q : Y ⟶ Spec (CommRingCat.of O)} {y : SpecialPoint q}

end Formal

section Tests

open GlobalTheory.NCyc

def closedSpecial (O : Type) [CommRing O] [IsLocalRing O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R]
    [IsLocalHom (algebraMap O R)] : SpecialPoint (Spec.map (CommRingCat.ofHom (algebraMap O R))) :=
  ⟨closedPoint R, comap_closedPoint (algebraMap O R)⟩

abbrev Zbreve (p : ℕ) [Fact p.Prime] : Type := WittVector p (AlgebraicClosure (ZMod p))

def Ram : Type := PowerSeries ℂ

instance : CommRing Ram := inferInstanceAs (CommRing (PowerSeries ℂ))

instance : HenselianLocalRing Ram := henselian_powerSeries_complex

instance : IsSepClosed (ResidueField Ram) := isSepClosed_residueField_powerSeries_complex

instance : IsAdicComplete (maximalIdeal Ram) Ram := by
  change IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ)
  rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance

instance : Algebra (PowerSeries ℂ) Ram := (PowerSeries.expand (R := ℂ) 2 two_ne_zero).toRingHom.toAlgebra

instance : IsLocalHom (algebraMap (PowerSeries ℂ) Ram) := by
  refine ⟨fun a ha => ?_⟩
  have h : IsUnit (PowerSeries.expand (R := ℂ) 2 two_ne_zero a) := ha
  rw [PowerSeries.isUnit_iff_constantCoeff, ← PowerSeries.coeff_zero_eq_constantCoeff_apply] at h ⊢
  rwa [PowerSeries.coeff_expand, if_pos (dvd_zero 2)] at h

instance : Module.Finite (PowerSeries ℂ) Ram := by
  let s : Ram := (PowerSeries.X : PowerSeries ℂ)
  refine Module.finite_def.2 (Submodule.fg_def.2 ⟨{1, s}, Set.toFinite _, eq_top_iff.2 fun a _ => ?_⟩)
  refine Submodule.mem_span_pair.2 ⟨PowerSeries.mk fun n => PowerSeries.coeff (R := ℂ) (2 * n) a,
    PowerSeries.mk fun n => PowerSeries.coeff (R := ℂ) (2 * n + 1) a, ?_⟩
  show @Eq (PowerSeries ℂ) (PowerSeries.expand (R := ℂ) 2 two_ne_zero _ * (1 : PowerSeries ℂ) +
    PowerSeries.expand (R := ℂ) 2 two_ne_zero _ * (PowerSeries.X : PowerSeries ℂ)) a
  refine PowerSeries.ext fun n => ?_
  rw [mul_one, map_add]
  rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
  · rcases k with _ | k
    · simp [PowerSeries.coeff_expand]
    · rw [show 2 * (k + 1) = 2 * k + 1 + 1 by ring, PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_expand,
        PowerSeries.coeff_expand, if_pos (by omega), if_neg (by omega), PowerSeries.coeff_mk, add_zero,
        show 2 * ((2 * k + 1 + 1) / 2) = 2 * k + 1 + 1 by omega]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_expand, PowerSeries.coeff_expand, if_neg (by omega),
      if_pos (by omega), PowerSeries.coeff_mk, zero_add, show 2 * (2 * k / 2) + 1 = 2 * k + 1 by omega]

attribute [local instance] henselian_powerSeries_complex isSepClosed_residueField_powerSeries_complex
  faithfulSMul_powerSeries_complex isAlgebraic_powerSeries_complex

end Tests

end GlobalTheory.FormalInv

end
