import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PlaceCharacterEqReferenceIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsAdelicChain

namespace MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

namespace CompanionTheory.Member.InnerProductScaling

theorem isMultiplicityInner_smul_measure {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    IsMultIP M (ENNReal.ofReal c • μ) 𝓕 T T' ((c : ℂ) * a) := by
  intro v v'
  obtain ⟨h1, h2⟩ := h v v'
  refine ⟨?_, ?_⟩
  · unfold IntegrableOn at h1 ⊢
    rw [Measure.restrict_smul]
    exact h1.smul_measure ENNReal.ofReal_ne_top
  · rw [Measure.restrict_smul, integral_smul_measure, h2, ENNReal.toReal_ofReal hc, Complex.real_smul, mul_assoc]

theorem ipM_smul {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (T T' : MMap M) (c : ℝ) (hc : 0 ≤ c) (a : ℂ) (h : IsMultIP M μ 𝓕 T T' a) :
    ipM M (ENNReal.ofReal c • μ) 𝓕 T T' = (c : ℂ) * a := by
  obtain ⟨v, hv⟩ := GlobalTheory.SchurConst.exists_vec M (GlobalTheory.GardingVec.sm_ne_bot D V S M)
  have h' := isMultiplicityInner_smul_measure M μ 𝓕 T T' c hc a h
  exact hasPeterssonInner_unique M _ 𝓕 T T' v hv (ipM_spec M _ 𝓕 T T' ⟨_, h'⟩) h'

theorem main {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (μ : Measure (GA D V))
    (𝓕 : Set (GA D V)) (H : HMod (MMap M)) (W W0 : Submodule ℂ (MMap M)) (hW : W ≤ W0)
    (hH : H.Is W0 (ipM M μ 𝓕)) (n : ℝ) (hn : 0 < n)
    {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE]
    (j : EE ≃ₗ[ℂ] (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap))
    (hj : HilbTie (W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap)
      (ipMT M (ENNReal.ofReal n⁻¹ • μ) 𝓕) j) :
    ∃ eE : EE →ₗ[ℂ] H.H, LinearMap.range eE = W.comap H.e ∧ (∀ x, ‖eE x‖ ^ 2 = n * ‖x‖ ^ 2) ∧
      ∀ x, ((j x : W.map (PiTensorProduct.lift : MMap M ≃ₗ[ℂ] AmbT M).toLinearMap) : AmbT M) =
        PiTensorProduct.lift (H.e (eE x)) := by
  let L : MMap M ≃ₗ[ℂ] AmbT M := PiTensorProduct.lift
  let f : EE →ₗ[ℂ] MMap M := L.symm.toLinearMap ∘ₗ (W.map L.toLinearMap).subtype ∘ₗ j.toLinearMap
  have hf : ∀ x, f x = L.symm (j x : AmbT M) := fun _ => rfl
  have hfW : ∀ x, f x ∈ W := fun x => by
    obtain ⟨y, hy, e⟩ := (j x).2
    have e' : L y = (j x : AmbT M) := e
    rw [hf, ← e', L.symm_apply_apply]
    exact hy
  obtain ⟨g, hg⟩ := GlobalTheory.Mem.Th.exists_factor H.e hH.1 f fun x => by
    rw [hH.2.1]; exact hW (hfW x)
  refine ⟨g, ?_, fun x => ?_, fun x => ?_⟩
  · ext u
    constructor
    · rintro ⟨x, rfl⟩
      show H.e (g x) ∈ W
      rw [hg]; exact hfW x
    · intro hu
      refine ⟨j.symm ⟨L (H.e u), Submodule.mem_map_of_mem hu⟩, hH.1 ?_⟩
      rw [hg, hf, j.apply_symm_apply]
      exact L.symm_apply_apply _
  · have h1 : IsMultIP M μ 𝓕 (H.e (g x)) (H.e (g x)) (1 * ⟪g x, g x⟫_ℂ) :=
      GlobalTheory.Mem.Th.isMultiplicityInner_mul_inner H.e one_ne_zero (fun a b => by rw [one_mul]; exact (hH.2.2 a b).symm) _ _
    have h2 := ipM_smul M μ 𝓕 _ _ n⁻¹ (inv_pos.2 hn).le _ h1
    have h3 : ⟪x, x⟫_ℂ = ipM M (ENNReal.ofReal n⁻¹ • μ) 𝓕 (f x) (f x) := hj x x
    rw [← hg, h2, one_mul, inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    have h4 : ‖x‖ ^ 2 = n⁻¹ * ‖g x‖ ^ 2 := by
      have h5 : ((‖x‖ ^ 2 : ℝ) : ℂ) = ((n⁻¹ * ‖g x‖ ^ 2 : ℝ) : ℂ) := by
        rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.ofReal_pow]
        exact h3
      exact Complex.ofReal_injective h5
    rw [h4, ← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul]
  · rw [hg, hf]
    exact (L.apply_symm_apply _).symm

end CompanionTheory.Member.InnerProductScaling

theorem CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F tupT hm hTop b EE _ _ _ X I hE hj
  exact CompanionTheory.Member.InnerProductScaling.main (R.MY 0) R.ν0 R.fd0 R.HE (R.EEat (R.levR F b)) (R.EEat R.triv)
    (GlobalTheory.Mem.Th.EEat_le_triv R _) hE (RealDat.nP F b) (RealDat.nP_pos b) I.jE hj

end

end MultiplicativeInnerProducts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
theorem _root_.GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A) (tupT : D.what₂.Tup → T) (hm : 0 < D.R.m) (hTop : TopMultH R) (b : Bool) (EE : Type) [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE] (X : RowSide D EE) (I : RowIds X (toChainReal R F tupT hm hTop) b), R.models_HE → HilbTie ((toChainReal R F tupT hm hTop).EEc b) ((toChainReal R F tupT hm hTop).ipE b) I.jE → ∃ eE : EE →ₗ[ℂ] R.HE.H, LinearMap.range eE = (R.EEat (R.levR F b)).comap R.HE.e ∧ (∀ x, ‖eE x‖ ^ 2 = RealDat.nP F b * ‖x‖ ^ 2) ∧ ∀ x, ((I.jE x : (toChainReal R F tupT hm hTop).EEc b) : (toChainReal R F tupT hm hTop).Amb 0) = PiTensorProduct.lift (R.HE.e (eE x)) := by
  first | exact @MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | exact MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows | (intros; apply MultiplicativeInnerProducts.CompanionTheory.Member.levelRowsReading_hilbert_embedding_goodRows <;> assumption)

end
