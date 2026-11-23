import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSiegelHProjArchEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HasIwasawaDecompositionDoubledSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaDoubledHermitianSpaceRealPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaInertPlace
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StabiliserEqCentraliserCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatHomOfGAdSymm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantStabilizerIwasawaLine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MajorantFrameCommutesCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeSelfDualEverywhere
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StabilizerCommutesMajorantStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GraphElementIwasawaSplitPlace

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

noncomputable section
namespace GlobalTheory.DblIwasawa

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem transpose_dblGram {n : ℕ} (J : Matrix (Fin n) (Fin n) E) :
    (dblGram finSumFinEquiv J)ᵀ = dblGram finSumFinEquiv Jᵀ := by
  ext i j
  obtain ⟨i | i, rfl⟩ := finSumFinEquiv.surjective i <;> obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective j <;>
    simp only [dblGram, blkMat, Matrix.transpose_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, Matrix.neg_apply]

theorem hasIwasawa_fin (hcm : IsCMExt F E σ) (hun : Algebra.Unramified (𝓞 F) (𝓞 E)) {n : ℕ} (X : Spc F E n)
    (hX : IsHermND σ X.J) (hL : X.L.IsLattice E)
    (hd : ∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv X.Jᵀ) (v : HeightOneSpectrum (𝓞 F)) :
    HasIwasawa σ Q (KFin σ Q X.L v) := by
  haveI : Submodule.IsLattice E X.L := hL
  have hJt : IsHermND σ X.Jᵀ := ⟨fun i j => hX.1 j i, by rw [Matrix.det_transpose]; exact hX.2⟩
  have hSD : IsSelfDualAt σ X.Jᵀ X.L v := by
    refine (GlobalTheory.AdelicU.SelfDual.forall_isSelfDualAt_iff hJt.2 hL).2 (fun y => ?_) v
    rw [hd y]
    simp only [GlobalTheory.HermSelfDualLoc.hE_transpose, GlobalTheory.HermSelfDualLoc.isIntegral_iff_mem_range]
  have hQ' : IsHermND σ Q := hQ ▸ GlobalTheory.GraphIwSplit.isHermND_dblGram σ hJt
  haveI := hun
  have hU : Formalism.MainNotions.SchurIrreducible.IsUnram (E := E) v :=
    GlobalTheory.LFun.isUnram_iff.2 fun w _ => Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  rcases GlobalTheory.LFun.InertChart.isSplit_or_isInertAt hU with hs | ⟨w, hw⟩
  · obtain ⟨w, w', hne, h1, h2⟩ := GlobalTheory.LFun.isSplit_iff.1 hs
    exact GlobalTheory.Core.Rk.IwSplit.hasIwasawa_of_algHom hcm hQ hJt hQ'
      (GlobalTheory.AdelicU.existsUnique_splitPrime_eq hcm hne h1 h2).exists.choose X.L hSD
  · exact GlobalTheory.InertIwasawaGen.hasIwasawa_of_inertAt hcm hJt hQ hw hSD

section Arch

open Formalism.UG (bc UJ cT)

theorem arch (hcm : IsCMExt F E σ) (B : Base F E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (θ : InfinitePlace F → Matrix (Fin n) (Fin n) ℂ) (hJ : ∀ i j, σ (J j i) = J i j)
    (hθ : ∀ w, IsCartan (J.map (B.emb w).1) (θ w)) {Q : Matrix (Fin (n + n)) (Fin (n + n)) E}
    (hQ : Q = dblGram finSumFinEquiv Jᵀ) :
    ∃ a : GL (Fin n) (AF F ⊗[F] E), IsMajorantFrame σ Jᵀ a ∧ ∀ (w : InfinitePlace F) (k : GArch σ Q w),
      k ∈ KArch σ Q w (Formalism.UG.bc (compInf F E w) a) ↔
        Commute ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w))) (blkMat finSumFinEquiv (θ w) (-θ w)) := by
  have hM : ∀ w : InfinitePlace F, (J.map (B.emb w).1)ᴴ = J.map (B.emb w).1 := fun w => by
    ext i j
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [← hcm.2.2.2 (B.emb w).1, hJ]
  have hC : ∀ w : InfinitePlace F, Formalism.IndefR.Datum.IsCartanInv (Jᵀ.map (B.emb w).1) (θ w) := fun w => by
    rw [Matrix.transpose_map]
    exact GlobalTheory.MajFrameCartan.isCartanInv_transpose (hM w) (hθ w)
  choose b ε h1 h2 using fun w => GlobalTheory.Doubling.exists_frame_of_isCartanInv (hC w)
  let e := fun w : InfinitePlace F => RingEquiv.ofBijective _ (infEmb_bijective hcm (B.emb w))
  let c : ∀ w : InfinitePlace F, GL (Fin n) (w.Completion ⊗[F] E) := fun w => bc (e w).symm.toRingHom (b w)
  have hc : ∀ w, (c w).1.map (infEmb (B.emb w)) = (b w).1 := fun w =>
    Matrix.ext fun i j => (e w).apply_symm_apply _
  have hc' : ∀ w, ((c w)⁻¹).1.map (infEmb (B.emb w)) = ((b w)⁻¹).1 := fun w => by
    rw [show (c w)⁻¹ = bc (e w).symm.toRingHom (b w)⁻¹ from (map_inv _ _).symm]
    exact Matrix.ext fun i j => (e w).apply_symm_apply _
  obtain ⟨a, -, ha⟩ := GlobalTheory.AdelicU.Frames.exists_GL_of_components (F := F) (E := E) (n := n) ∅ (fun _ => 1)
    (fun _ _ => rfl) c
  refine ⟨a, fun w => ⟨ε w, ?_⟩, fun w k => ?_⟩
  · rw [ha w, GlobalTheory.Doubling.frame_local_iff hcm (B.emb w) Jᵀ (c w).1 (ε w), hc]
    exact h1 w
  · have hK : ((matHom w.Completion σ Q k).1.map (infEmb (B.emb w)))ᴴ * Q.map (B.emb w).1 *
        (matHom w.Completion σ Q k).1.map (infEmb (B.emb w)) = Q.map (B.emb w).1 :=
      (archEquiv Q hcm (B.emb w) k).2
    have key : ∀ x : GL (Fin (n + n)) (w.Completion ⊗[F] E), x ∈ UJ (sigR w.Completion σ) 1 ↔
        (x.1.map (infEmb (B.emb w)))ᴴ * x.1.map (infEmb (B.emb w)) = 1 := fun x => by
      change cT _ x.1 * 1 * x.1 = 1 ↔ _
      rw [← (Matrix.map_injective (infEmb_bijective hcm (B.emb w)).1).eq_iff]
      beta_reduce
      rw [mul_one, Matrix.map_mul, Frames.map_cT_sigR hcm, Matrix.map_one _ (map_zero _) (map_one _)]
    have hcT : ∀ x y : Matrix (Fin n) (Fin n) ℂ,
        (blkMat finSumFinEquiv x y)ᴴ = blkMat finSumFinEquiv xᴴ yᴴ := fun x y => by
      simp [blkMat, Matrix.fromBlocks_conjTranspose]
    have hbc : blkMat finSumFinEquiv (b w).1 (b w).1 * blkMat finSumFinEquiv ((b w)⁻¹).1 ((b w)⁻¹).1 = 1 := by
      rw [blkMat_mul, Units.mul_inv, blkMat_one]
    have hQw : Q.map (B.emb w).1 =
        blkMat finSumFinEquiv (Jᵀ.map (B.emb w).1) (-(Jᵀ.map (B.emb w).1)) := by
      rw [hQ, dblGram, blkMat_map _ _ (map_zero _), Matrix.map_neg _ (map_neg _)]
    set D : Matrix (Fin n) (Fin n) ℂ := Matrix.diagonal fun i => if ε w i then 1 else -1 with hD
    have hd : (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ * Q.map (B.emb w).1 *
        blkMat finSumFinEquiv (b w).1 (b w).1 = blkMat finSumFinEquiv D (-D) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, Matrix.neg_mul, h1 w]
    have hdd : blkMat finSumFinEquiv D (-D) * blkMat finSumFinEquiv D (-D) = 1 := by
      rw [blkMat_mul, neg_mul_neg, hD, GlobalTheory.Doubling.diagonal_sign_mul_self, blkMat_one]
    have hs : blkMat finSumFinEquiv (b w).1 (b w).1 * (blkMat finSumFinEquiv (b w).1 (b w).1)ᴴ *
        Q.map (B.emb w).1 = blkMat finSumFinEquiv (θ w) (-θ w) := by
      rw [hcT, hQw, blkMat_mul, blkMat_mul, Matrix.mul_neg, h2 w]
    rw [← hs, ← GlobalTheory.Doubling.unitary_iff_commute hbc hd hdd hK]
    show _ ∈ stabArch σ Q w (blkGL finSumFinEquiv (_, _)) ↔ _
    rw [mem_stabArch, ha w, key, ← map_inv, Prod.inv_mk, Units.val_mul, Units.val_mul, val_blkGL, val_blkGL,
      Matrix.map_mul, Matrix.map_mul, blkMat_map _ _ (map_zero _), blkMat_map _ _ (map_zero _), hc, hc']

end Arch

theorem isCompact_and_iwasawaOf : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → Algebra.Unramified (𝓞 F) (𝓞 E) → ∀ (B : Base F E) (n : ℕ) (X : Spc F E n),
    IsHermND σ X.J → X.L.IsLattice E → (∀ y, y ∈ X.L ↔ ∀ x ∈ X.L, IsIntegral ℤ (form σ X.J y x)) →
    (∀ w, IsCartan (X.J.map (B.emb w).1) (X.θ w)) → ∀ X₂ : Spc F E (n + n), X₂.J = dblGram finSumFinEquiv X.J →
    X₂.L = sumLat finSumFinEquiv X.L X.L → (∀ w, X₂.θ w = blkMat finSumFinEquiv (X.θ w) (-X.θ w)) →
    ∀ K : Subgroup (UA σ X₂.J), IsStab B K → IsCompact (K : Set (UA σ X₂.J)) ∧
      IwasawaOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K := by
  intro F E _ _ _ _ _ σ hcm hun B n X hX hL hd hθ X₂ hJ₂ hL₂ hθ₂ K hK
  haveI : Submodule.IsLattice E X.L := hL
  have hQ : X₂.Jᵀ = dblGram finSumFinEquiv X.Jᵀ := by rw [hJ₂, transpose_dblGram]
  obtain ⟨a, hmaj, harch⟩ := arch hcm B X.J X.θ hX.1 hθ hQ
  have hI : HasIwasawa σ X₂.Jᵀ (KAd σ X₂.Jᵀ X.L a) := by
    refine HasIwasawa.adelic (fun v => hasIwasawa_fin hcm hun X hX hL hd hQ v) (fun w => ?_)
    obtain ⟨ε, hε⟩ := hmaj w
    exact GlobalTheory.Core.Rk.IwArch.hasIwasawa_KArch hcm hQ w _ ε hε
  have hL₂' : X₂.L.IsLattice E := by rw [hL₂]; infer_instance
  have key : ∀ g : GAd σ X₂.Jᵀ, GlobalTheory.IwLine.ofGAd σ X₂.J g ∈ K ↔ g ∈ KAd σ X₂.Jᵀ X.L a := by
    intro g
    rw [(hK _).trans (GlobalTheory.StabHaar.isStab_stabK (σ := σ) B X₂ _).symm, mem_KAd]
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := GlobalTheory.T.stabilizer_commutes_majorant F E σ B (n + n) X₂ hL₂' g h
      refine ⟨fun v => ?_, fun w => ?_⟩
      · have := h2 v; rwa [hL₂] at this
      · rw [harch w, ← hθ₂ w]; exact h1 w
    · rintro ⟨h2, h1⟩
      refine GlobalTheory.KBridge.ofGAd_mem_stabK F E σ B (n + n) X₂ hL₂' g (fun w => ?_) (fun v => ?_)
      · rw [hθ₂ w, ← harch w]; exact h1 w
      · rw [hL₂]; exact h2 v
  have hcont : Continuous (GlobalTheory.IwLine.ofGAd σ X₂.J) := Continuous.subtype_mk continuous_subtype_val _
  have hKset : (K : Set (UA σ X₂.J)) =
      GlobalTheory.IwLine.ofGAd σ X₂.J '' (KAd σ X₂.Jᵀ X.L a : Set (GAd σ X₂.Jᵀ)) := by
    ext g
    constructor
    · intro hg
      refine ⟨(GlobalTheory.IwLine.ofGAd σ X₂.J).symm g, (key _).1 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply _ _⟩
    · rintro ⟨g', hg', rfl⟩
      exact (key g').2 hg'
  have hKc : IsCompact (K : Set (UA σ X₂.J)) := by
    rw [hKset]; exact (isCompact_KAd hcm).image hcont
  refine ⟨hKc, ?_⟩
  haveI : Module.Finite F E := Module.Finite.of_restrictScalars_finite ℚ F E
  haveI : IsModuleTopology (AF F) (AE F E) := ⟨rfl⟩
  haveI : IsTopologicalRing (AE F E) := IsModuleTopology.isTopologicalRing (AF F) _
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : T2Space (AE F E) := t2Space_tensorProduct_finiteExtension (F := F) (E := E) (R := AF F)
  refine iwasawaOf_of_isCompact continuous_subtype_val continuous_absE hKc fun g => ?_
  obtain ⟨p, k, hk, e⟩ := hI ((GlobalTheory.IwLine.ofGAd σ X₂.J).symm g)
  have hp : (GlobalTheory.IwLine.ofGAd σ X₂.J p) ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype := p.2
  refine ⟨⟨_, hp⟩, GlobalTheory.IwLine.ofGAd σ X₂.J k, (key k).2 hk, ?_⟩
  have := congrArg (GlobalTheory.IwLine.ofGAd σ X₂.J) e
  rw [MulEquiv.apply_symm_apply, map_mul] at this
  exact this

end GlobalTheory.DblIwasawa

end
