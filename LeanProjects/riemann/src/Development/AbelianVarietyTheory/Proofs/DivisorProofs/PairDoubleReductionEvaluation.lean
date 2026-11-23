import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemThInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarFundamentalDomainParabolicIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigBThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawIdentityConfigBSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBTripleIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationUnramifiedIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LintegralIdeleMajorantFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnfoldingIntegralCountable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzIntegralSuperposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzDoubleIntegralExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzContinuousAtOfPointwiseOfBounded
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigASchwartzEvalEqual
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviLiftOfAdaptedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneSecondVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairDoubleDescentModelsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviHaarStabilizerMeasureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomainAltBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviElementUniqueBisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviMapPreservesRationalPointsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviRationalPointVectorActionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipotentHaarLeviDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RelativelyCompactStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsClosedAdelicLatticeClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticTraceBasisExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermComplement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharactersRestrictionEta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SobolevBoundFiniteFamily

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.ThK.PairCone

section Analysis

end Analysis

end GlobalTheory.ThK.PairCone

namespace GlobalTheory.ThK.PairCone

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ThK.PairCone

namespace GlobalTheory.ThK.PairCone

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

section Decay

open GlobalTheory.XTermDecay

theorem decay {B : Base F E} {n d n₁ d₁ r s' r' s'' : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {χX χW : Chr F E}
    {om : Rep σ X W} (hT : IsPair B M χX χW om r s' r' s'') {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {M₂ : Model σ X₁ W₁}
    (H₀ : Plane E n n₁) (H' : Plane E d d₁) (hxy : form σ X.J H₀.x H₀.y = 1)
    (hxy' : form σ W.J H'.x H'.y = 1) {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁}
    (he : IsEv B M M₂ H₀.ι H'.ι (isoA H₀ H') e) {K : Subgroup (UA σ X.J)} (hK : IsStab B K)
    {Φ : Fn F n d} (hΦ : Φ ∈ schA F (Fin n × Fin d)) (h : UA σ W.J)
    (U : Set (Fin (Module.finrank F E) → Af F)) (hU : IsCompact U) (c : Fin n₁ × Fin d₁ → Af F) (N : ℕ)
    (s : Finset (ℕ × ℕ)) :
    ∃ C : ℝ, ∀ k ∈ K, ∀ l : (AE F E)ˣ, (fun i => (GlobalTheory.XTermMaj.crd F E (l : AE F E) i).2) ∈ U →
      ∃ f : SInf F (Fin n₁ × Fin d₁), (∀ y, f y = e (M.co.rho B.ψ (shiftA H₀ H' l) (om (k, h) Φ))
          (fun q => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (y q), c q))) ∧
        (s.sup (schwartzSeminormFamily ℂ _ ℂ)) f ≤
          C * (1 + ∑ i, ∑ v : InfinitePlace F, ‖(GlobalTheory.XTermMaj.crd F E (l : AE F E) i).1 v‖) ^ (-(N : ℝ)) := by
  have hKeq : K = GlobalTheory.StabHaar.stabK (σ := σ) B X :=
    Subgroup.ext fun g => (hK g).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X g).symm
  have hKc : IsCompact (K : Set (UA σ X.J)) := by
    have hX := hT.herm
    obtain ⟨C, hCc, hsub⟩ := GlobalTheory.T.relatively_compact_stabilizer F E σ B n X _ _ hT.base hX
    rw [hKeq]
    exact hCc.of_isClosed_subset (GlobalTheory.StabHaar.isClosed_stabK B X (GlobalTheory.T.isClosed_adelic_lattice_closure F E n X hX.lat)) hsub
  have hw : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F X.J) (incM F W.J) M.co χX χW om := hT.weil
  have hΦA : Φ ∈ schA F _ := hΦ
  obtain ⟨m, g, f, hg, hdec, hf⟩ := exists_decomp (fun k : K => om (k.1, h) Φ)
    (fun k => hw.isUSplitting.pres (k.1, h) Φ hΦA) fun l hl => by
      have hc := (hw.2.2 l hl Φ hΦA).comp
        (continuous_id.prodMk continuous_const : Continuous fun g : UA σ X.J => (g, h))
      obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hc.continuousOn
      exact ⟨C, fun k => hC k.1 k.2⟩
  obtain ⟨t, ht⟩ := GlobalTheory.T.symplectic_trace_basis_exists F E σ _ _ X.J W.J H₀.x H₀.y H'.x H'.y hxy (by
    rw [form_swap hT.base.cm hT.skew.skew, hxy', map_one])
  let S := fun j => M.co.e (inclR (F := F) (AF F) (Module.finBasis F E j) • Matrix.vecMulVec (incV F H₀.x) (incV F H'.y))
  let U' := fun i => M.co.e (Matrix.vecMulVec (inclR (F := F) (AF F) (t i) • incV F H₀.y) (incV F H'.x))
  have hp : Continuous ⇑(Finset.sup s (schwartzSeminormFamily ℂ (Fin n₁ × Fin d₁ → mixedEmbedding.mixedSpace F) ℂ)) :=
    Seminorm.continuous_finsetSup fun i _ => (schwartz_withSeminorms ℂ _ ℂ).continuous_seminorm i
  choose C hCb using fun j => slice_decay B.ψ hT.base.std S U' (fun i j => by rw [← M.co.form]; convert ht i j)
    (sliceL c ∘ₗ e) (exists_slice_clm hT.good he c) (fun i a Ψ hΨ => by
      have := he.inv (Matrix.vecMulVec (a • inclR (F := F) (AF F) (t i) • incV F H₀.y) (incV F H'.x)) (Or.inl ⟨_, rfl⟩) Ψ hΨ
      rw [Matrix.smul_vecMulVec, Darboux.rho, map_smul] at this
      exact congrArg (sliceL c) this) (hg j) (f j) (hf j) hU _ hp N
  refine ⟨∑ j, C j, fun k hk l hl => ?_⟩
  choose f₁ hf₁ hb₁ using fun j => hCb j ⟨k, hk⟩ (GlobalTheory.XTermMaj.crd F E (l : AE F E)) hl
  have hS : M.co.e (shiftA H₀ H' l) = ∑ i, GlobalTheory.XTermMaj.crd F E (l : AE F E) i • S i := by
    simp only [S, ← map_smul, ← map_sum, ← smul_assoc, ← Finset.sum_smul]
    congr 2
    rw [shiftA]
    congr 1
    refine ((Algebra.TensorProduct.basis (AF F) (Module.finBasis F E)).sum_equivFun (l : AE F E)).symm.trans ?_
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Algebra.TensorProduct.basis_apply]
    rfl
  refine ⟨∑ j, f₁ j, fun y => ?_, ?_⟩
  · have h1 := hdec ⟨k, hk⟩
    simp only at h1
    rw [h1, Darboux.rho, hS]
    change coeL (∑ j, f₁ j) y = (sliceL c ∘ₗ e) (schrL B.ψ _ _) y
    rw [map_sum, map_sum, map_sum]
    exact congrFun (Finset.sum_congr rfl fun j _ => hf₁ j) y
  · rw [Finset.sum_mul]
    exact (Finset.le_sum_of_subadditive _ (map_zero _).le (map_add_le_add _) _ _).trans
      (Finset.sum_le_sum fun j _ => hb₁ j)

end Decay

end GlobalTheory.ThK.PairCone

namespace GlobalTheory.ThK.PairCone

open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

end GlobalTheory.ThK.PairCone

end
