import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.PolarisationModuleIndex
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ConjugateOrderData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPlaceRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGeneratorTopExteriorPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraFreeRankDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieAlgebraPeriodCoordinatesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmOrderActionDescendsStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatModel
open GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds (IsClassZetaVals c_vp cE_vp a0)
open TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.LatModel

theorem exists_detGen_wedge_val_le : GlobalTheory.Published.AbelianDeRham → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] [IsAbelianGalois ℚ E] (I : Type) [Fintype I] (d : ℕ)
      (φ : I → E →+* ℂ), GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.IsFieldData d φ → ∀ (𝔣 : Ideal (OF E)), IsBaseCond 𝔣 →
    ∀ (l : ℕ) [Fact l.Prime] (Q : Finset (HeightOneSpectrum (OF E))), IsFinSetSplitPlacesCoprimeConductor 𝔣 Q → (∀ q ∈ Q, (l : OF E) ∉ q.asIdeal) →
    ∀ y : (Af E)ˣ, OneOver l y → ∀ (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (𝔠 : FracId (FR E)) (R : Subring ℂ)
      [IsDiscreteValuationRing R], GlobalTheory.LatModel.IsPlaceRing E l lam R →
    ∀ (X₀ : Obj (FR E) 𝔠 (Sp R)) (X : Obj (FR E) 𝔠 (Sp ℂ)) (U : Unif φ (lattice (condQ 𝔣 Q) y) 0 X)
      (p : X.A.left ⟶ X₀.A.left) (cm : OAct (orderC (condQ 𝔣 Q)) X₀.A), X.IsPullBy X₀ (spMap R.subtype) p →
      (∀ a : OF E, cm.act (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ofF (condQ 𝔣 Q) a) = X₀.rm.act a) →
      (∀ a : orderC (condQ 𝔣 Q), ∃ (α : X.A ⟶ X.A) (_ : IsMonHom α), α.left ≫ p = p ≫ (cm.act a).left ∧
        ∀ w, U.u.ex (fun j ↦ φ (U.e j) (a : E) * w j) = U.u.ex w ≫ α) →
    ∀ (j : FractionRing R →+* ℂ), (∀ x : R, j (algebraMap R (FractionRing R) x) = x) →
    ∀ (φK : I → E →+* FractionRing R), (∀ i, j.comp (φK i) = φ i) →
    ∀ (e : I → (X₀.Lie →ₗ[R] R)) (a : I → ℂ), (∀ i, a i ≠ 0 ∧ GlobalTheory.LatModel.IsPeriodGen X₀ U p i (e i) (a i) ∧
        ∀ (e' : X₀.Lie →ₗ[R] R) (a' : ℂ), GlobalTheory.LatModel.IsPeriodGen X₀ U p i e' a' → ∃ t : R, e' = t • e i) →
    ∀ (D : R), D ≠ 0 → GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.ClearsIdem (FractionRing R) (condQ 𝔣 Q) D →
    ∃ (δ₀ : X₀.DetGen) (u₀ : R),
      (Matrix.detRowAlternating.compLinearMap (LinearMap.pi fun k ↦ e (U.e k)) : X₀.DetOmega) = u₀ • δ₀.1 ∧
      GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) u₀) ≤
        Fintype.card I • GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.val_vp R l (algebraMap R (FractionRing R) D) := by
  classical
  intro _hdR E _ _ _ _ I _ d φ hφ 𝔣 _h𝔣 l _ Q _hQ _hQl y _hy lam 𝔠 R _ _hR X₀ X U p cm hpull _hcm hα j hj φK hφK e a he D hD hcl
  have hinj : Function.Injective φ := by
    intro i i' h
    obtain ⟨k, -, hk⟩ := hφ.2.2.2.2.2.2.1 (φ i)
    exact (hk i (Or.inl rfl)).trans (hk i' (Or.inl h)).symm
  have hKinj : Function.Injective φK := fun i i' h ↦ hinj (by rw [← hφK i, ← hφK i', h])
  obtain ⟨hfree, hfin, hrk⟩ := GlobalTheory.T.lie_algebra_free_rank_degree R X₀
  obtain ⟨cd, hcd1, hcd2, hlam⟩ := GlobalTheory.T.lie_algebra_period_coordinates R X₀ X U p hpull
  choose t ht using fun i ↦ hcl (φK i)
  choose T hT using fun i ↦ GlobalTheory.T.cm_order_action_descends R X₀ X U p (condQ 𝔣 Q) cm hα cd hcd1 hcd2 (t i)
  have hfac : ∀ i k, Algebra.TensorProduct.productMap ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom
      (algebraMap R ℂ).toIntAlgHom (t i) = if U.e k = i then ((D : R) : ℂ) else 0 := by
    intro i k
    have h2 : ∀ x : orderC (condQ 𝔣 Q) ⊗[ℤ] R, Algebra.TensorProduct.productMap
        ((φ (U.e k)).comp (orderC (condQ 𝔣 Q)).subtype).toIntAlgHom (algebraMap R ℂ).toIntAlgHom x =
        j (GlobalTheory.IndefiniteRowSideFullHecke.DifferentConductorValuations.coordAt R (condQ 𝔣 Q) (φK (U.e k)) x) := by
      intro x
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul a x =>
        show φ (U.e k) (a : E) * (x : ℂ) = j (φK (U.e k) (a : E) * algebraMap R (FractionRing R) x)
        rw [map_mul, hj, ← hφK (U.e k)]
        rfl
      | add x z hx hz => rw [map_add, map_add, hx, hz, map_add]
    rw [h2, ht i (φK (U.e k))]
    by_cases h : U.e k = i
    · subst h
      simp [hj]
    · rw [if_neg (fun h' ↦ h (hKinj h')), if_neg h]
      simp
  have hspan : ∀ ω : X₀.Lie →ₗ[R] R, D • ω ∈ Submodule.span R (Set.range fun k ↦ e (U.e k)) := by
    intro ω
    obtain ⟨lm, hlm⟩ := hlam ω
    have hval : ∀ i v, (((ω ∘ₗ T i) v : R) : ℂ) =
        ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
      intro i v
      rw [LinearMap.comp_apply, hlm]
      simp_rw [hT i v, hfac i]
    have hg : ∀ i, ∃ s : R, ω ∘ₗ T i = s • e i := by
      intro i
      refine (he i).2.2 _ ((D : ℂ) * lm (U.e.symm i)) ?_
      intro v v' W hv hW
      rw [hcd2 v v' W hv hW, hval i v, Finset.sum_eq_single (U.e.symm i)]
      · simp only [Equiv.apply_symm_apply, if_true]
        ring
      · intro k _ hk
        rw [if_neg (fun (h : U.e k = i) ↦ hk (by rw [← h, Equiv.symm_apply_apply]))]
        simp
      · intro h
        exact absurd (Finset.mem_univ _) h
    choose s hs using hg
    have heq : D • ω = ∑ i, s i • e i := by
      ext v
      rw [LinearMap.smul_apply, LinearMap.sum_apply, AddSubmonoidClass.coe_finsetSum]
      have key : ∀ i, (((s i • e i) v : R) : ℂ) =
          ∑ k, lm k * ((if U.e k = i then ((D : R) : ℂ) else 0) * cd v k) := by
        intro i
        rw [← hs i, hval]
      simp_rw [key]
      rw [Finset.sum_comm]
      simp only [ite_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [smul_eq_mul, Subring.coe_mul, hlm, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ ↦ ?_
      ring
    rw [heq]
    exact Submodule.sum_mem _ fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span ⟨U.e.symm i, by simp⟩)
  haveI := hfree
  haveI := hfin
  obtain ⟨δ₀, u₀, hδ, hu, hv⟩ := GlobalTheory.T.exists_generator_top_exterior_power R X₀.Lie _ hrk (fun k ↦ e (U.e k)) D hD hspan l
  refine ⟨⟨δ₀, hδ⟩, u₀, hu, ?_⟩
  have hc : Fintype.card I = Module.finrank ℚ (FR E) := by
    rw [← Fintype.card_congr U.e, Fintype.card_fin]
  rw [hc]
  exact hv

end GlobalTheory.LatModel
