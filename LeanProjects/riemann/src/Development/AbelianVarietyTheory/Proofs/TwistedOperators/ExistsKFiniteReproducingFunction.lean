import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DecompAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.FinitePartTypes
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOnOfRapidDec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaGrowthOfThetaSquareIntegrable
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspAlongOfPairLifts
import Development.AbelianVarietyTheory.Proofs.HeightProofs.TypeAtOfDiscreteSeries
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsGrowthSobNeTopOfIsAutFunSm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GrowthSobZeroNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GKModuleMapCuspFormsExtendsMultiplicitySpace
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.KTypeExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdelicUnitaryUnimodularExistsFundamentalDomain
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIffStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KFinAtZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasCtpId
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.Grow GlobalTheory.Size
open Formalism.REAL Formalism.MainNotions.S GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum GlobalTheory.SeriesToClosure GlobalTheory.PlaceDecomp GlobalTheory.KFinDecomp Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.ReproKFin

variable {K : Type} [Group K]

def conjSub (S : Submodule ℂ (K → ℂ)) : Submodule ℂ (K → ℂ) where
  carrier := {f | (fun k => star (f k)) ∈ S}
  add_mem' := by
    intro f g hf hg
    have h : (fun k => star ((f + g) k)) = (fun k => star (f k)) + (fun k => star (g k)) :=
      funext fun k => by simp [star_add]
    show (fun k => star ((f + g) k)) ∈ S
    rw [h]; exact S.add_mem hf hg
  zero_mem' := by
    show (fun k => star ((0 : K → ℂ) k)) ∈ S
    have h : (fun k => star ((0 : K → ℂ) k)) = 0 := funext fun k => by simp
    rw [h]; exact S.zero_mem
  smul_mem' := by
    intro c f hf
    have h : (fun k => star ((c • f) k)) = star c • (fun k => star (f k)) :=
      funext fun k => by simp only [Pi.smul_apply, smul_eq_mul, star_mul', Pi.smul_apply]
    show (fun k => star ((c • f) k)) ∈ S
    rw [h]; exact S.smul_mem _ hf

theorem mem_conjSub {S : Submodule ℂ (K → ℂ)} {f : K → ℂ} : f ∈ conjSub S ↔ (fun k => star (f k)) ∈ S := Iff.rfl

instance conjSub_finiteDimensional (S : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ S] :
    FiniteDimensional ℂ (conjSub S) := by
  let b := Module.finBasis ℂ S
  have hle : conjSub S ≤ Submodule.span ℂ (Set.range fun i => fun k => star ((b i : K → ℂ) k)) := by
    intro f hf
    have hsum := b.sum_repr ⟨_, hf⟩
    have hf' : f = ∑ i, star (b.repr ⟨_, hf⟩ i) • (fun k => star ((b i : K → ℂ) k)) := by
      funext k
      have h2 := congrArg (fun x : S => star ((x : K → ℂ) k)) hsum
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
        star_sum, star_mul', star_star] at h2
      rw [Finset.sum_apply]
      simpa [Pi.smul_apply, smul_eq_mul] using h2.symm
    rw [hf']
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun i => fun k => star ((b i : K → ℂ) k))) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range _)
  exact Submodule.finiteDimensional_of_le hle

theorem star_mem_sup {S : Submodule ℂ (K → ℂ)} {f : K → ℂ} (hf : f ∈ S ⊔ conjSub S) :
    (fun k => star (f k)) ∈ S ⊔ conjSub S := by
  obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hf
  have h : (fun k => star ((a + c) k)) = (fun k => star (c k)) + (fun k => star (a k)) :=
    funext fun k => by simp [add_comm]
  rw [h]
  refine Submodule.add_mem_sup hc ?_
  rw [mem_conjSub]
  simpa using ha

end GlobalTheory.ReproKFin

namespace GlobalTheory.ReproKFin

theorem coeffSpan_finDim {K W : Type} [Group K] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ K W) : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  let b := Module.finBasis ℂ W
  let g : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W) → (K → ℂ) := fun ij k => b.repr (ρ k (b ij.2)) ij.1
  have hle : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ Submodule.span ℂ (Set.range g) := by
    refine Submodule.span_le.2 ?_
    rintro f ⟨ℓ, w, rfl⟩
    have : (fun k => ℓ (ρ k w)) = ∑ ij : Fin (Module.finrank ℂ W) × Fin (Module.finrank ℂ W),
        (b.repr w ij.2 * ℓ (b ij.1)) • g ij := by
      funext k
      conv_lhs => rw [← b.sum_repr w]
      rw [Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_comm]
      simp only [map_sum, map_smul, smul_eq_mul, Pi.smul_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      conv_lhs => rw [← b.sum_repr (ρ k (b j))]
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum, g]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [SetLike.mem_coe, this]
    exact Submodule.sum_mem _ fun ij _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨ij, rfl⟩)
  haveI : FiniteDimensional ℂ (Submodule.span ℂ (Set.range g)) :=
    FiniteDimensional.span_of_finite ℂ (Set.finite_range g)
  exact Submodule.finiteDimensional_of_le hle

end GlobalTheory.ReproKFin

namespace GlobalTheory.ReproKFin

variable {K : Type} [Group K]

theorem sup_props {S : Submodule ℂ (K → ℂ)} [TopologicalSpace K] (hc : ∀ f ∈ S, Continuous f)
    (hL : ∀ f ∈ S, ∀ k₀ : K, (fun k => f (k₀ * k)) ∈ S) (hR : ∀ f ∈ S, ∀ k₀ : K, (fun k => f (k * k₀)) ∈ S) :
    (∀ f ∈ S ⊔ conjSub S, Continuous f) ∧ ∀ f ∈ S ⊔ conjSub S, ∀ k₀ : K,
      (fun k => f (k₀ * k)) ∈ S ⊔ conjSub S ∧ (fun k => f (k * k₀)) ∈ S ⊔ conjSub S := by
  refine ⟨fun f hf => ?_, fun f hf k₀ => ?_⟩
  · obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 hf
    have : Continuous c := by simpa using (hc _ hc').star
    exact (hc a ha).add this
  · obtain ⟨a, ha, c, hc', rfl⟩ := Submodule.mem_sup.1 hf
    exact ⟨Submodule.add_mem_sup (hL a ha k₀) (hL _ hc' k₀), Submodule.add_mem_sup (hR a ha k₀) (hR _ hc' k₀)⟩

theorem coeffSpan_props {W : Type} [TopologicalSpace K] [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ K W)
    (hρ : GlobalTheory.Published.AutFin.IsContRep ρ) :
    (∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, Continuous f) ∧
    (∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k₀ : K, (fun k => f (k₀ * k)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) ∧
    (∀ f ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∀ k₀ : K, (fun k => f (k * k₀)) ∈ GlobalTheory.Published.AutFin.coeffSpan ρ) := by
  refine ⟨fun f hf => ?_, fun f hf k₀ => ?_, fun f hf k₀ => ?_⟩
  · let C : Submodule ℂ (K → ℂ) :=
      { carrier := {f | Continuous f}
        add_mem' := fun ha hb => ha.add hb
        zero_mem' := continuous_const
        smul_mem' := fun c _ hx => continuous_const.mul hx }
    have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤ C := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨ℓ, w, rfl⟩
      exact hρ ℓ w
    exact this hf
  · have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤
        (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (k₀ * ·)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨ℓ, w, rfl⟩
      exact Submodule.subset_span ⟨ℓ ∘ₗ ρ k₀, w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
    exact this hf
  · have : GlobalTheory.Published.AutFin.coeffSpan ρ ≤
        (GlobalTheory.Published.AutFin.coeffSpan ρ).comap (LinearMap.funLeft ℂ ℂ (· * k₀)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨ℓ, w, rfl⟩
      exact Submodule.subset_span ⟨ℓ, ρ k₀ w, funext fun k => by simp [LinearMap.funLeft, map_mul]⟩
    exact this hf

end GlobalTheory.ReproKFin

namespace GlobalTheory.ReproKFin

theorem reproduce_one : ∀ (n : ℕ) (ε : Fin n → Bool) (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W] (ρ : Representation ℂ (Formalism.REAL.KG ε) W), GlobalTheory.Published.AutFin.IsContRep ρ → ∃ e : Formalism.REAL.KG ε → ℂ, KFinFun ε e ∧ ∀ h ∈ GlobalTheory.Published.AutFin.coeffSpan ρ, ∫ k, e k * h k ∂(Formalism.REAL.muK ε) = h 1 := by
  intro n ε W _ _ _ ρ hρ
  obtain ⟨hcS, hLS, hRS⟩ := coeffSpan_props ρ hρ
  haveI : FiniteDimensional ℂ (GlobalTheory.Published.AutFin.coeffSpan ρ) := coeffSpan_finDim ρ
  set S := GlobalTheory.Published.AutFin.coeffSpan ρ with hS
  obtain ⟨hcT, hTT⟩ := sup_props hcS hLS hRS
  set T := S ⊔ conjSub S with hT
  have hint : ∀ f g : Formalism.REAL.KG ε → ℂ, Continuous f → Continuous g →
      Integrable (fun k => f k * g k) (Formalism.REAL.muK ε) := fun f g hf hg =>
    (hf.mul hg).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let Φ : T →ₗ[ℂ] Module.Dual ℂ T :=
    LinearMap.mk₂ ℂ (fun e h : T => ∫ k, (e : Formalism.REAL.KG ε → ℂ) k * (h : Formalism.REAL.KG ε → ℂ) k ∂(Formalism.REAL.muK ε))
      (fun e e' h => by
        simp only [Submodule.coe_add, Pi.add_apply, add_mul]
        exact integral_add (hint _ _ (hcT _ e.2) (hcT _ h.2)) (hint _ _ (hcT _ e'.2) (hcT _ h.2)))
      (fun c e h => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_assoc]
        exact integral_const_mul c _)
      (fun e h h' => by
        simp only [Submodule.coe_add, Pi.add_apply, mul_add]
        exact integral_add (hint _ _ (hcT _ e.2) (hcT _ h.2)) (hint _ _ (hcT _ e.2) (hcT _ h'.2)))
      (fun c e h => by
        simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, mul_left_comm _ c]
        exact integral_const_mul c _)
  have hinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro e he
    have h0 : ∫ k, (e : Formalism.REAL.KG ε → ℂ) k * star ((e : Formalism.REAL.KG ε → ℂ) k) ∂(Formalism.REAL.muK ε) = 0 := by
      have := LinearMap.congr_fun he ⟨fun k => star ((e : Formalism.REAL.KG ε → ℂ) k), star_mem_sup e.2⟩
      simpa [Φ] using this
    have h1 : ∫ k, Complex.normSq ((e : Formalism.REAL.KG ε → ℂ) k) ∂(Formalism.REAL.muK ε) = 0 := by
      have h' : (fun k => (e : Formalism.REAL.KG ε → ℂ) k * star ((e : Formalism.REAL.KG ε → ℂ) k)) =
          fun k => ((Complex.normSq ((e : Formalism.REAL.KG ε → ℂ) k) : ℝ) : ℂ) :=
        funext fun k => by rw [Complex.star_def, Complex.mul_conj]
      rw [h', integral_complex_ofReal] at h0
      exact_mod_cast h0
    have hc : Continuous fun k => Complex.normSq ((e : Formalism.REAL.KG ε → ℂ) k) :=
      Complex.continuous_normSq.comp (hcT _ e.2)
    have hae := (integral_eq_zero_iff_of_nonneg (fun k => Complex.normSq_nonneg _)
      (hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))).1 h1
    have heq : (fun k => Complex.normSq ((e : Formalism.REAL.KG ε → ℂ) k)) = fun _ => 0 :=
      (Continuous.ae_eq_iff_eq (Formalism.REAL.muK ε) hc continuous_const).1 hae
    apply Subtype.ext
    funext k
    have := congrFun heq k
    simpa [Complex.normSq_eq_zero] using this
  have hsurj : Function.Surjective Φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (Subspace.dual_finrank_eq).symm).1 hinj
  let ev1 : Module.Dual ℂ T := (LinearMap.proj (R := ℂ) (φ := fun _ : Formalism.REAL.KG ε => ℂ) 1).comp T.subtype
  obtain ⟨e, he⟩ := hsurj ev1
  refine ⟨e, ⟨T, inferInstance, e.2, hcT, fun φ hφ k₀ => hTT φ hφ k₀⟩, fun h hh => ?_⟩
  have := LinearMap.congr_fun he ⟨h, Submodule.mem_sup_left hh⟩
  simpa [Φ, ev1] using this

end GlobalTheory.ReproKFin
