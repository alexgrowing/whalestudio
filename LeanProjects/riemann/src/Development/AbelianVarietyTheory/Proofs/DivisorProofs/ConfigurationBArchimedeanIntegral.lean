import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensInclInjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MaximalCompactOneParameterLinesOfLieLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieSecondOfPrints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDeriva
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivati
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeakExponentialActionOnFockVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyFinitePiTensorSumOfFactorOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IncMatTransposeConjTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialInclusionFockActionCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenvectorFixedByCompactCommutingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open Formalism.BasicNotions.TH GlobalTheory.RealLift GlobalTheory.FockIncl

noncomputable section

namespace GlobalTheory.FockInclK

open scoped Classical
open GlobalTheory.RealLift.KLineProof

section Lines

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem line_one_eq {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (hCM : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {b : ℂ} {C : InfinitePlace F → Matrix β (Ix R S) ℂ}
    (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) {γ : Multiplicative ℝ →* UG (cA σ) J} (hγ : γ ∈ RLines σ J)
    {Y : InfinitePlace F → Mat R S} (hgen : IsGen τ C γ Y) (k : UG (cA σ) J)
    (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hY : ∀ w, C w * NormedSpace.exp (Y w) = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w) :
    γ (Multiplicative.ofAdd 1) = k := by
  have hw : ∀ w, ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) =
      (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) := by
    intro w
    obtain ⟨A', hCA, -⟩ := frame_inv (hfr w)
    have h1 := hgen 1 w
    rw [one_smul, hY w] at h1
    calc _ = ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w * A' := by
          rw [Matrix.mul_assoc, hCA, Matrix.mul_one]
      _ = _ := by rw [h1, Matrix.mul_assoc, hCA, Matrix.mul_one]
  have hA1 := hγ.2 (Multiplicative.ofAdd 1)
  have hmat : ((γ (Multiplicative.ofAdd 1)).1 : Matrix β β (AE F E)) = k.1 := by
    ext i j
    rw [← sub_eq_zero]
    refine eq_zero_of_piInf hCM τ _ ?_ ?_
    · intro u hu0
      have e1 := congrFun (congrFun (hA1 u hu0) i) j
      have e2 := congrFun (congrFun (hk u hu0) i) j
      simp only [Matrix.smul_apply, Matrix.sub_apply, Matrix.zero_apply, smul_sub] at e1 e2 ⊢
      rw [← sub_sub_sub_cancel_right _ _ (u • (1 : Matrix β β (AE F E)) i j), e1, e2, sub_zero]
    · intro w
      have := congrFun (congrFun (hw w) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this, sub_self]
  exact Subtype.ext (Units.ext hmat)

theorem kLine_upq {β : Type} [Fintype β] [DecidableEq β] {R S : ℕ} (hCM : IsCMExt F E σ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (θ : InfinitePlace F → Matrix β β ℂ) (hfr : ∀ w, IsFrame (b • J.map (piInf (τ w))) (C w))
    (hθ : ∀ w, θ w * C w = C w * Jm R S) (k : UG (cA σ) J) (hk : At (evI F) ((k.1 : Matrix β β (AE F E)) - 1))
    (hkθ : ∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) :
    ∃ Y : InfinitePlace F → Mat R S, (∀ w, Y w ∈ upq R S) ∧ (∀ w, IsKC (Y w)) ∧
      (∀ w, C w * NormedSpace.exp (Y w) = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w) ∧
      ∃ γ ∈ RLines σ J, IsGen τ C γ Y ∧ γ (Multiplicative.ofAdd 1) = k := by
  have hu : (k.1 : Matrix β β (AE F E))ᵀ * J * (k.1 : Matrix β β (AE F E)).map (cA σ) = J := k.2
  have hloc : ∀ w, ∃ Y : Mat R S, Y ∈ upq R S ∧ IsKC Y ∧
      C w * NormedSpace.exp Y = (k.1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w := by
    intro w
    obtain ⟨A', hCA, hAC⟩ := frame_inv (hfr w)
    refine exists_gen_at (C w) A' hCA hAC (J.map (piInf (τ w))) b (hfr w).1 _ (θ w) ?_ (hθ w) (hkθ w)
    have := congrArg (fun X => X.map (piInf (τ w))) hu
    simp only [Matrix.map_mul, map_cA_map hCM, Matrix.transpose_map] at this
    exact this
  choose Y hY using hloc
  obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.RealLift.exists_line_of_upq F E σ β R S τ J b C hCM hfr Y (fun w => (hY w).1)
  exact ⟨Y, fun w => (hY w).1, fun w => (hY w).2.1, fun w => (hY w).2.2, γ, hγ, hgen,
    line_one_eq hCM τ hfr hγ hgen k hk fun w => (hY w).2.2⟩

theorem piInf_inclR {w : InfinitePlace F} (τ : EmbOver E w) (e : E) : piInf τ (inclR (F := F) (AF F) e) = τ.1 e := by
  have := congrFun (congrFun (GlobalTheory.RealLift.Main.incM_map_piInf (Matrix.of fun (_ : Fin 1) (_ : Fin 1) => e) τ) 0) 0
  simpa [incM] using this

end Lines

end GlobalTheory.FockInclK

open scoped Classical in
open GlobalTheory.FockInclK in

theorem GlobalTheory.FockInclK.tensIncl_acts : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b)
    (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F a (b + 2)) (Rf : FinMaps F a (b + 2))
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F a b) (Rf₁ : FinMaps F a b),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (P Q R₀ S₀ : ℕ) (A : InfinitePlace F → Matrix (Fin a) (Ix P Q) ℂ)
        (C₁ : InfinitePlace F → Matrix (Fin (a + b)) (Ix R₀ S₀) ℂ)
        (C : InfinitePlace F → Matrix (Fin (a + (b + 2))) (Ix (R₀ + 1) (S₀ + 1)) ℂ)
        (Φ₁ : Tens F P Q R₀ S₀ →ₗ[ℂ] SInf F (Fin a × Fin (a + b)))
        (Φ : Tens F P Q (R₀ + 1) (S₀ + 1) →ₗ[ℂ] SInf F (Fin a × Fin (a + (b + 2)))) (r₀ : Fin (R₀ + 1)) (s₀ : Fin (S₀ + 1)),
        GlobalTheory.FockBridge.IsFockData B G₁.M A C₁ Φ₁ → GlobalTheory.FockBridge.IsFockData B G.M A C Φ →
        GlobalTheory.FockBridge.IsAdaptedFrame B H' C r₀ s₀ → IsCompat B H' C C₁ r₀ s₀ →
        ∀ k₁ ∈ KInf σ G₁.W B.emb, ∀ k ∈ KInf σ G.W B.emb, IsLevi H' 1 k₁ k → ∀ T T₁ : Tens F P Q R₀ S₀,
          Acts (evI F) (om₁ (1, k₁)) (Φ₁ T) (Φ₁ T₁) →
          Acts (evI F) (om (1, k)) (Φ (tensIncl F P Q r₀ s₀ T)) (Φ (tensIncl F P Q r₀ s₀ T₁)) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ P Q R₀ S₀ A C₁ C Φ₁ Φ r₀ s₀
    hD₁ hD hAd hCo k₁ hk₁ k hk hL T T₁ hT
  have hb := hM.triple.base
  have hcm := hb.cm
  have hvl := GlobalTheory.VacLn.vacLine_of_derEx GlobalTheory.HeisDer.derEx
  have hsec := GlobalTheory.RealLift.LieSecondPf.lieSecond_of_lieScalar hKP.base GlobalTheory.HeisDer.derEx
    (GlobalTheory.FockMapEx.fockEx_of_derEx GlobalTheory.HeisDer.derEx) hvl (GlobalTheory.LieScal.lieScalar hKP.base GlobalTheory.HeisDer.derEx hvl)
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om :=
    hM.triple.weil
  have hwp₁ : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G₁.V.J) (incM F G₁.W.J) G₁.M.co X.β (X.β / X.α) om₁ :=
    hM₁.triple.weil
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hcm hb.std hD.1.1 hD.2 hwp.1
    hM.triple.chars.expβ
  have hW2₁ := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G₁.M.co 1 Complex.I A C₁ Φ₁ _ X.β B.mβ hcm hb.std hD₁.1.1 hD₁.2
    hwp₁.1 hM₁.triple.chars.expβ

  obtain ⟨Y₁, hY₁u, hY₁K, hY₁e, γ₁, hγ₁, hgen₁, hγ₁1⟩ := kLine_upq hcm B.emb (incM F G₁.W.J) Complex.I C₁ G₁.W.θ
    (fun w => hD₁.1.1.2.2 w) (fun w => hD₁.1.2.2 w) k₁ hk₁.1 hk₁.2

  obtain ⟨γ, hγ, hgen⟩ := GlobalTheory.RealLift.exists_line_of_upq F E σ (Fin (a + (b + 2))) (R₀ + 1) (S₀ + 1) B.emb
    (incM F G.W.J) Complex.I C hcm (fun w => hD.1.1.2.2 w) (fun w => extMat r₀ s₀ (Y₁ w))
    (fun w => extMat_mem_upq r₀ s₀ (hY₁u w))
  have hγ1 : γ (Multiplicative.ofAdd 1) = k := by
    refine line_one_eq hcm B.emb (fun w => hD.1.1.2.2 w) hγ hgen k hk.1 fun w => ?_
    obtain ⟨c, hc, hx⟩ := (hAd w).1
    refine (GlobalTheory.T.eigenvector_fixed_by_compact_commuting _ _ _ _ r₀ s₀ _ (G.W.θ w) ((mat k₁).map (piInf (B.emb w))) (H'.ι.map (B.emb w).1) (C w) (C₁ w) (Y₁ w) (fun i => (B.emb w).1 (H'.x i)) c hc hx ?_ (hk.2 w)
      (hD.1.2.2 w) (hCo w) ?_ (hY₁e w)).symm
    · funext i
      have := congrArg (fun v => piInf (B.emb w) (v i)) hL.1
      simp only [Units.val_one, one_smul] at this
      simpa [Matrix.mulVec, dotProduct, map_sum, map_mul, incV, piInf_inclR] using this
    · have := congrArg (fun M => M.map (piInf (B.emb w))) hL.2.2
      simpa only [Matrix.map_mul, GlobalTheory.RealLift.Main.incM_map_piInf] using this

  have hloc₁ := GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w => GlobalTheory.RealLift.Main.locFin_fock2 P Q R₀ S₀ (Y₁ w) (hY₁K w)
    (((B.mβ w : ℂ) / 2) * (Y₁ w).trace))
  obtain ⟨U₁, hU₁, hSA₁⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ₁ _ ((om₁.comp (MonoidHom.inr _ _)).comp γ₁) hloc₁
    (fun t l hl => (hwp₁.isUSplitting).adm _ l hl) (fun T => hW2₁ γ₁ hγ₁ Y₁ hgen₁ T)
  have hloc := GlobalTheory.RealLift.locFin_sumPl _ _ _ (fun w => GlobalTheory.RealLift.Main.locFin_fock2 P Q (R₀ + 1) (S₀ + 1)
    (extMat r₀ s₀ (Y₁ w)) (isKC_extMat r₀ s₀ (hY₁K w)) (((B.mβ w : ℂ) / 2) * (extMat r₀ s₀ (Y₁ w)).trace))
  obtain ⟨U, hU, hSA⟩ := GlobalTheory.ExpAct.expAct_fock F _ _ Φ _ ((om.comp (MonoidHom.inr _ _)).comp γ) hloc
    (fun t l hl => (hwp.isUSplitting).adm _ l hl) (fun T => hW2 γ hγ _ hgen T)

  have hA₁ := (GlobalTheory.RealLift.actsLaws F _ (Φ₁ T) (Φ₁ (U₁ T)) (Φ₁ T₁)).2.1 _ (map_zero _) (hSA₁ T)
  rw [MonoidHom.comp_apply, hγ₁1] at hA₁
  have eT : U₁ T = T₁ := hD₁.2.1 ((GlobalTheory.RealLift.actsLaws F _ (Φ₁ T) _ _).2.2.2.1 _ hA₁ hT)

  have hA := (GlobalTheory.RealLift.actsLaws F _ (Φ (tensIncl F P Q r₀ s₀ T)) (Φ (U (tensIncl F P Q r₀ s₀ T)))
    (Φ (U (tensIncl F P Q r₀ s₀ T)))).2.1 _ (map_zero _) (hSA _)
  rw [MonoidHom.comp_apply, hγ1] at hA
  have hLL := GlobalTheory.RealLift.Main.map_sumPl (fun _ : InfinitePlace F => (polIncl P Q r₀ s₀).toLinearMap)
    (fun w => fockAct2 P Q R₀ S₀ (Y₁ w) + (((B.mβ w : ℂ) / 2) * (Y₁ w).trace) • 1)
    (fun w => fockAct2 P Q (R₀ + 1) (S₀ + 1) (extMat r₀ s₀ (Y₁ w)) +
      (((B.mβ w : ℂ) / 2) * (extMat r₀ s₀ (Y₁ w)).trace) • 1) fun w => by
    rw [trace_extMat, LinearMap.comp_add, LinearMap.add_comp, GlobalTheory.T.polynomial_inclusion_fock_action_comm P Q R₀ S₀ r₀ s₀ (Y₁ w)]
    congr 1
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, Module.End.one_apply, map_smul]
  have hE := GlobalTheory.RealLift.Main.exp_equiv (q := tensIncl F P Q r₀ s₀) (q' := LinearMap.id) hU₁ hU hLL
    (by rw [LinearMap.id_comp, LinearMap.comp_id]) (v := T) (v' := tensIncl F P Q r₀ s₀ T) rfl
  rw [← eT, hE, LinearMap.id_apply]
  exact hA
