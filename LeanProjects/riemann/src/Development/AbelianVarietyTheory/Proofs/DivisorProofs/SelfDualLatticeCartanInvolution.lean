import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegFamOfContinuousAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCompactAndIwasawaOf
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasIwasawaOfSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInverseDifferentLocalUnitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualLatticeLocalisedByDifferentStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeDetNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCartanBasisDoubledGramStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling GlobalTheory.ThK.DblKer

noncomputable section

namespace GlobalTheory.SkewDblIwasawa

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_isStab_iwasawaOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (B : Base F E) (n : ℕ) (W : Spc F E n),
    (∀ i j, σ (W.J j i) = -W.J i j) → W.L.IsLattice E →
    (∀ y, y ∈ W.L ↔ ∀ x ∈ W.L, ∀ o : 𝓞 E, IsIntegral ℤ (Algebra.trace ℚ E (o * form σ W.J y x))) →
    (∀ w, IsCartan (Complex.I • W.J.map (B.emb w).1) (W.θ w)) →
    ∀ W₂ : Spc F E (n + n), W₂.J = dblGram finSumFinEquiv W.J → W₂.L = sumLat finSumFinEquiv W.L W.L →
    (∀ w, W₂.θ w = blkMat finSumFinEquiv (W.θ w) (-W.θ w)) →
    ∃ K₂ : Subgroup (UA σ W₂.J), IsStab B K₂ ∧ IwasawaOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype (absE F E) K₂ := by
  intro F E _ _ _ _ _ σ hcm hun B n W hJ hL hd hθ W₂ hJ₂ hL₂ hθ₂
  haveI : Submodule.IsLattice E W.L := hL
  have hQ : W₂.Jᵀ = dblGram finSumFinEquiv W.Jᵀ := by rw [hJ₂, GlobalTheory.DblIwasawa.transpose_dblGram]
  have hdet : W.J.det ≠ 0 := GlobalTheory.T.self_dual_lattice_det_ne_zero F E σ n W.J W.L hL hd
  have hfin : ∀ v, HasIwasawa σ W₂.Jᵀ (KFin σ W₂.Jᵀ W.L v) := by
    intro v
    obtain ⟨δ, hδ0, hσδ, s, hs, h1, h2⟩ := GlobalTheory.T.exists_inverse_different_local_unit F E σ hcm hun v
    have hH : IsHermND σ (δ • W.Jᵀ) := by
      refine ⟨fun i j => ?_, ?_⟩
      · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hσδ, hJ]
        ring
      · rw [Matrix.det_smul, Matrix.det_transpose]
        exact mul_ne_zero (pow_ne_zero _ hδ0) hdet
    have hSD : IsSelfDualAt σ (δ • W.Jᵀ) W.L v := GlobalTheory.T.dual_lattice_localised_by_different F E σ n W.J W.L hdet hL hd v δ s hδ0 hs h1 h2
    have hQ' : δ • W₂.Jᵀ = dblGram finSumFinEquiv (δ • W.Jᵀ) := by rw [hQ, dblGram_smul]
    have hQH : IsHermND σ (δ • W₂.Jᵀ) := hQ' ▸ GlobalTheory.GraphIwSplit.isHermND_dblGram σ hH
    haveI := hun
    have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
      GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
    have hI : HasIwasawa σ (δ • W₂.Jᵀ) (KFin σ (δ • W₂.Jᵀ) W.L v) := by
      rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hsp | ⟨w, hw⟩
      · obtain ⟨w, w', hne, e1, e2⟩ := GlobalTheory.LFun.isSplit_iff.1 hsp
        exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom hcm hQ' hH hQH
          (GlobalTheory.AdelicU.existsUnique_splitPrime_eq hcm hne e1 e2).exists.choose W.L hSD
      · exact GlobalTheory.InertIwasawaGen.hasIwasawa_of_inertAt hcm hH hQ' hw hSD
    exact hasIwasawa_of_smul σ δ hδ0 W₂.Jᵀ _ hI
  obtain ⟨a, harch⟩ := GlobalTheory.T.exists_cartan_basis_doubled_gram F E σ hcm B n W.J W.θ hJ hθ hQ
  have hI : HasIwasawa σ W₂.Jᵀ (KAd σ W₂.Jᵀ W.L a) :=
    HasIwasawa.adelic hfin (fun w => (harch w).1)
  have hL₂' : W₂.L.IsLattice E := by rw [hL₂]; infer_instance
  let K := GlobalTheory.StabHaar.stabK (σ := σ) B W₂
  have key : ∀ g : GAd σ W₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ W₂.J g ∈ K ↔ g ∈ KAd σ W₂.Jᵀ W.L a := by
    intro g
    rw [mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) W₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => ?_⟩
      · have := h2 v; rwa [hL₂] at this
      · rw [(harch w).2, ← hθ₂ w]; exact h1 w
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) W₂ hL₂' g (fun w => ?_) (fun v => ?_)
      · rw [hθ₂ w, ← (harch w).2]; exact h1 w
      · rw [hL₂]; exact h2 v
  have hcont : Continuous (GlobalTheory.IwLine.ofGAd σ W₂.J) := Continuous.subtype_mk continuous_subtype_val _
  have hKset : (K : Set (UA σ W₂.J)) =
      GlobalTheory.IwLine.ofGAd σ W₂.J '' (KAd σ W₂.Jᵀ W.L a : Set (GAd σ W₂.Jᵀ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨(GlobalTheory.IwLine.ofGAd σ W₂.J).symm g, (key _).1 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply _ _⟩
    · rintro ⟨g', hg', rfl⟩
      exact (key g').2 hg'
  have hKc : IsCompact (K : Set (UA σ W₂.J)) := by
    rw [hKset]; exact (isCompact_KAd hcm).image hcont
  refine ⟨K, GlobalTheory.StabHaar.isStab_stabK B W₂, ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  refine iwasawaOf_of_isCompact continuous_subtype_val continuous_absE hKc fun g => ?_
  obtain ⟨p, k, hk, e⟩ := hI ((GlobalTheory.IwLine.ofGAd σ W₂.J).symm g)
  have hp : (GlobalTheory.IwLine.ofGAd σ W₂.J p) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F W₂.J)).subtype := p.2
  refine ⟨⟨_, hp⟩, GlobalTheory.IwLine.ofGAd σ W₂.J k, (key k).2 hk, ?_⟩
  have := congrArg (GlobalTheory.IwLine.ofGAd σ W₂.J) e
  rw [MulEquiv.apply_symm_apply, map_mul] at this
  exact this

end GlobalTheory.SkewDblIwasawa

end
