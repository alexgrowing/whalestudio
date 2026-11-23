import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

namespace GlobalTheory.EigDescentFrac

theorem span_image_span {K L P V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup P]
    [Module K P] [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
    (g : P →ₗ[K] V) (S : Set P) :
    Submodule.span L (g '' (Submodule.span K S : Set P)) = Submodule.span L (g '' S) := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono (Set.image_mono Submodule.subset_span))
  rintro _ ⟨x, hx, rfl⟩
  have : Submodule.span K S ≤ ((Submodule.span L (g '' S)).restrictScalars K).comap g :=
    Submodule.span_le.2 fun y hy => Submodule.subset_span ⟨y, hy, rfl⟩
  exact this hx

theorem span_image_iSup {K L P V : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup P]
    [Module K P] [AddCommGroup V] [Module K V] [Module L V] [IsScalarTower K L V]
    (g : P →ₗ[K] V) {κ : Sort*} (W : κ → Submodule K P) :
    Submodule.span L (g '' ((⨆ i, W i : Submodule K P) : Set P)) =
      ⨆ i, Submodule.span L (g '' (W i : Set P)) := by
  refine le_antisymm (Submodule.span_le.2 ?_)
    (iSup_le fun i => Submodule.span_mono (Set.image_mono (SetLike.coe_subset_coe.2 (le_iSup W i))))
  rintro _ ⟨x, hx, rfl⟩
  have : (⨆ i, W i) ≤ ((⨆ i, Submodule.span L (g '' (W i : Set P))).restrictScalars K).comap g :=
    iSup_le fun i y hy =>
      (le_iSup (fun i => Submodule.span L (g '' (W i : Set P))) i) (Submodule.subset_span ⟨y, hy, rfl⟩)
  exact this hx

theorem baseChange_eq_iSup_eigK : ∀ {E : Type} [Field E] [NumberField E] {c : Ideal (OF E)} {R : Type} [CommRing R] [IsDomain R]
    {L : Type} [Field L] [Algebra R L] (j : FractionRing R →+* L)
    (hj : ∀ x : R, j (algebraMap R (FractionRing R) x) = algebraMap R L x) {n : ℕ} {V : Type*} [AddCommGroup V]
    [Module L V] (β : (Fin n → R) →ₛₗ[algebraMap R L] V)
    (hβ : LinearIndependent L (fun k ↦ β (Pi.single k 1)) ∧ Submodule.span L (Set.range fun k ↦ β (Pi.single k 1)) = ⊤)
    (ρ : orderC c →+* Module.End R (Fin n → R)) (T : orderC c → Module.End L V)
    (hT : ∀ a x, β (ρ a x) = T a (β x)) (N : Submodule R (Fin n → R)) {I : Type} [Fintype I]
    (σ : I → E →+* FractionRing R)
    (h : Submodule.span L (β '' (N : Set (Fin n → R))) = ⨆ i, ⨅ a : orderC c, Module.End.eigenspace (T a) (j (σ i a))),
   N.baseChange (FractionRing R) = ⨆ i, GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK ρ (σ i) := by
  intro E _ _ c R _ _ L _ _ j hj n V _ _ β hβ ρ T hT N I _ σ h
  classical
  letI : Algebra (FractionRing R) L := j.toAlgebra
  letI : Module (FractionRing R) V := Module.compHom V j
  haveI : IsScalarTower (FractionRing R) L V := ⟨fun k l v => by
    show (j k * l) • v = j k • l • v
    rw [mul_smul]⟩
  have hsmul : ∀ (k : FractionRing R) (v : V), k • v = j k • v := fun _ _ => rfl
  let bK : Module.Basis (Fin n) (FractionRing R) (FractionRing R ⊗[R] (Fin n → R)) :=
    Algebra.TensorProduct.basis (FractionRing R) (Pi.basisFun R (Fin n))
  have hbK : ∀ k, bK k = (1 : FractionRing R) ⊗ₜ[R] (Pi.single k (1 : R) : Fin n → R) := fun k => by
    simp [bK, Algebra.TensorProduct.basis_apply, Pi.basisFun_apply]
  let bL : Module.Basis (Fin n) L V := Module.Basis.mk hβ.1 hβ.2.ge
  have hbL : ∀ k, bL k = β (Pi.single k 1) := fun k => Module.Basis.mk_apply _ _ _
  let g : (FractionRing R ⊗[R] (Fin n → R)) →ₗ[FractionRing R] V :=
    bK.constr (FractionRing R) fun k => β (Pi.single k 1)
  have hgb : ∀ k, g (bK k) = β (Pi.single k 1) := fun k => bK.constr_basis _ _ _
  have hg1 : ∀ m : Fin n → R, g (1 ⊗ₜ m) = β m := by
    intro m
    have hm : m = ∑ k, m k • (Pi.single k (1 : R) : Fin n → R) := by
      ext i; simp [Finset.sum_apply, Pi.single_apply]
    rw [hm, TensorProduct.tmul_sum, map_sum, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [TensorProduct.tmul_smul, ← algebraMap_smul (FractionRing R) (m k), map_smul, ← hbK, hgb,
      β.map_smulₛₗ, hsmul, hj]
  let e : L ⊗[FractionRing R] (FractionRing R ⊗[R] (Fin n → R)) ≃ₗ[L] V :=
    (Algebra.TensorProduct.basis L bK).equiv bL (Equiv.refl _)
  have hbc : IsBaseChange L g := by
    refine IsBaseChange.of_equiv e fun m => ?_
    have h' : (e.toLinearMap.restrictScalars (FractionRing R) ∘ₗ
        TensorProduct.mk (FractionRing R) L _ 1) = g := by
      refine bK.ext fun k => ?_
      have := (Algebra.TensorProduct.basis L bK).equiv_apply k bL (Equiv.refl _)
      rw [Algebra.TensorProduct.basis_apply] at this
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe]
      rw [this, Equiv.refl_apply, hbL, hgb]
    exact congrArg (fun φ => φ m) h'
  have hF : ∀ (a : orderC c) (v : FractionRing R ⊗[R] (Fin n → R)),
      T a (g v) = g ((ρ a).baseChange (FractionRing R) v) := by
    intro a v
    have h' : (T a).restrictScalars (FractionRing R) ∘ₗ g =
        g ∘ₗ (ρ a).baseChange (FractionRing R) := by
      refine bK.ext fun k => ?_
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars]
      rw [hgb, hbK, LinearMap.baseChange_tmul, hg1, hT]
    exact congrArg (fun φ => φ v) h'
  have heig : ∀ (a : orderC c) (t : FractionRing R),
      Submodule.span L (g '' (Module.End.eigenspace ((ρ a).baseChange (FractionRing R)) t :
        Set (FractionRing R ⊗[R] (Fin n → R)))) = Module.End.eigenspace (T a) (j t) := by
    intro a t
    rw [Module.End.eigenspace_def, Module.End.eigenspace_def]
    refine GlobalTheory.GaloisDescent.span_image_ker hbc hbc _ _ fun v => ?_
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hF]
    rfl
  apply GlobalTheory.GaloisDescent.span_image_injective hbc
  simp only
  rw [Submodule.baseChange_eq_span, span_image_span, Submodule.map_coe, Set.image_image]
  simp only [TensorProduct.mk_apply, hg1]
  rw [h, span_image_iSup]
  refine iSup_congr fun i => ?_
  rw [GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.eigK, GlobalTheory.GaloisDescent.span_image_iInf hbc]
  exact iInf_congr fun a => (heig a _).symm

end GlobalTheory.EigDescentFrac
