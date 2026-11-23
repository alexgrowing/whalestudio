import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdaptedFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGlobalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGlobalIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationACompactIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAConvergenceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigurationAGlobalZetaIdentity

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.FockBridge
open scoped Classical

namespace GlobalTheory.FockBridge.Bridge

theorem L_frames : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (r₀ : Fin (b + 2 + a' - (G.p + G.q))) (s₀ : Fin (G.p + G.q)), IsFrames B G.V G.W A C ∧ IsAdaptedFrame B H' C r₀ s₀ := GlobalTheory.T.configuration_a_global_identity

theorem L_ker : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)),
      Keeps (R.p ∘ₗ Φ) (GlobalTheory.RealLift.atPl w (Formalism.BasicNotions.TH.fockAct2 (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) Y)) := GlobalTheory.T.configuration_a_global_integral

theorem L_low : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)),
      Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ lowPartInf B G.M R.p, fockOp (R.p ∘ₗ Φ) w Y v ∈ lowPartInf B G.M R.p := GlobalTheory.T.configuration_a_compact_integral

theorem L_irr : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p →
      (∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)), Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ N, fockOp (R.p ∘ₗ Φ) w Y v ∈ N) →
      N = ⊥ ∨ N = lowPartInf B G.M R.p := GlobalTheory.T.configuration_a_convergence

theorem L_sub : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (r₀ : Fin (b + 2 + a' - (G.p + G.q))) (s₀ : Fin (G.p + G.q)) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → IsAdaptedFrame B H' C r₀ s₀ →
      ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → KStabL B G.M om R.p G₁.W H' N →
      ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)), Formalism.BasicNotions.TH.IsKC Y →
        (∀ a, Y a (.inl r₀) = 0 ∧ Y (.inl r₀) a = 0 ∧ Y a (.inr s₀) = 0 ∧ Y (.inr s₀) a = 0) → ∀ v ∈ N, fockOp (R.p ∘ₗ Φ) w Y v ∈ N := GlobalTheory.T.configuration_a_unfolding

theorem L_eigtop : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (r₀ : Fin (b + 2 + a' - (G.p + G.q))) (s₀ : Fin (G.p + G.q)) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → IsAdaptedFrame B H' C r₀ s₀ →
      ∃ c c' : InfinitePlace F → ℂ, (∀ v, v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ↔ v ∈ lowPartInf B G.M R.p ∧
        ∀ w, fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧ fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) ∧
      ((∀ v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
        ∀ j, j ≠ s₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) ∨
      (∀ v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inl i) (.inl r₀)) v = 0) ∧
        ∀ j, j ≠ s₀ → fockOp (R.p ∘ₗ Φ) w (Formalism.BasicNotions.TH.Eab (.inr j) (.inr s₀)) v = 0)) := GlobalTheory.T.configuration_a_global_zeta_identity

set_option maxHeartbeats 1000000 in
theorem fock_bridge : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∃ (Rn Sn : ℕ) (r₀ : Fin Rn) (s₀ : Fin Sn) (act : InfinitePlace F → Formalism.BasicNotions.TH.Mat Rn Sn →ₗ[ℂ] Module.End ℂ R.Pi)
        (c c' : InfinitePlace F → ℂ),
        (∀ w X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w (X * Y - Y * X) = act w X * act w Y - act w Y * act w X) ∧
        (∀ w w', w ≠ w' → ∀ X Y, Formalism.BasicNotions.TH.IsKC X → Formalism.BasicNotions.TH.IsKC Y → act w X * act w' Y = act w' Y * act w X) ∧
        (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ lowPartInf B G.M R.p, act w X v ∈ lowPartInf B G.M R.p) ∧
        (∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → (∀ w X, Formalism.BasicNotions.TH.IsKC X → ∀ v ∈ N, act w X v ∈ N) →
          N = ⊥ ∨ N = lowPartInf B G.M R.p) ∧
        (∀ v, v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p) ↔ v ∈ lowPartInf B G.M R.p ∧
          ∀ w, act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl r₀)) v = c w • v ∧ act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr s₀)) v = c' w • v) ∧
        (∀ v ∈ twPart B G.M om R.p G₁.W H' X.α ((a' : ℝ) / 2) (lowPartInf B G.M R.p), ∀ w, (∀ i, i ≠ r₀ → act w (Formalism.BasicNotions.TH.Eab (.inl r₀) (.inl i)) v = 0) ∧
          ∀ j, j ≠ s₀ → act w (Formalism.BasicNotions.TH.Eab (.inr s₀) (.inr j)) v = 0) ∧
        ∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → KStabL B G.M om R.p G₁.W H' N →
          ∀ w X, Formalism.BasicNotions.TH.IsKC X → (∀ a, X a (.inl r₀) = 0 ∧ X (.inl r₀) a = 0 ∧ X a (.inr s₀) = 0 ∧ X (.inr s₀) a = 0) →
            ∀ v ∈ N, act w X v ∈ N := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨A, C, r₀, s₀, hfr, had⟩ := L_frames hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.RealLift.Main.i_fockex GlobalTheory.RealLift.Main.i_derex F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1
    Complex.I A C hM.triple.base.cm hM.triple.base.std hfr.1
  have hfd : IsFockData B G.M A C Φ := ⟨hfr, hΦ⟩
  have hrange := GlobalTheory.RealLift.Main.i_polrange GlobalTheory.RealLift.Main.i_actslaws GlobalTheory.RealLift.Main.i_derex
    (GlobalTheory.RealLift.Main.i_vacline GlobalTheory.RealLift.Main.i_derex) F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ
    hM.triple.base.cm hM.triple.base.std hfr.1 hfr.2.1 hfr.2.2 hΦ
  have hq : Function.Surjective (R.p ∘ₗ Φ) := by
    rw [← LinearMap.range_eq_top, LinearMap.range_comp, hrange]
    exact hM.real.quot.onto
  have hK := L_ker hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C Φ hfd
  have h3 := L_low hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C Φ hfd
  have h4 := L_irr hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C Φ hfd
  obtain ⟨c, c', h5, h6⟩ := L_eigtop hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C r₀ s₀ Φ hfd had
  have h7 := L_sub hKP F E σ B b a' G G₁ H H' hcfg X om om' R Rf om₁ om₁' R₁ Rf₁ hM hM₁ A C r₀ s₀ Φ hfd had

  have common : ∀ ε : Bool,
      (∀ w Y Z, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.IsKC Z →
        twAct ε (R.p ∘ₗ Φ) w (Y * Z - Z * Y) = twAct ε (R.p ∘ₗ Φ) w Y * twAct ε (R.p ∘ₗ Φ) w Z - twAct ε (R.p ∘ₗ Φ) w Z * twAct ε (R.p ∘ₗ Φ) w Y) ∧
      (∀ w w', w ≠ w' → ∀ Y Z, Formalism.BasicNotions.TH.IsKC Y → Formalism.BasicNotions.TH.IsKC Z →
        twAct ε (R.p ∘ₗ Φ) w Y * twAct ε (R.p ∘ₗ Φ) w' Z = twAct ε (R.p ∘ₗ Φ) w' Z * twAct ε (R.p ∘ₗ Φ) w Y) ∧
      (∀ w Y, Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ lowPartInf B G.M R.p, twAct ε (R.p ∘ₗ Φ) w Y v ∈ lowPartInf B G.M R.p) ∧
      (∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → (∀ w Y, Formalism.BasicNotions.TH.IsKC Y → ∀ v ∈ N, twAct ε (R.p ∘ₗ Φ) w Y v ∈ N) →
        N = ⊥ ∨ N = lowPartInf B G.M R.p) ∧
      (∀ N : Submodule ℂ R.Pi, N ≤ lowPartInf B G.M R.p → KStabL B G.M om R.p G₁.W H' N →
        ∀ w Y, Formalism.BasicNotions.TH.IsKC Y → (∀ a, Y a (.inl r₀) = 0 ∧ Y (.inl r₀) a = 0 ∧ Y a (.inr s₀) = 0 ∧ Y (.inr s₀) a = 0) →
          ∀ v ∈ N, twAct ε (R.p ∘ₗ Φ) w Y v ∈ N) := by
    intro ε
    refine ⟨fun w Y Z _ _ => twAct_lie hq (hK w) ε Y Z, fun w w' hw Y Z _ _ => twAct_comm hq hK ε hw Y Z, ?_, ?_, ?_⟩
    · intro w Y hY v hv
      cases ε
      · exact h3 w _ (isKC_negT hY) v hv
      · exact h3 w Y hY v hv
    · intro N hN hs
      refine h4 N hN fun w Y hY v hv => ?_
      cases ε
      · have := hs w (negT _ _ Y) (isKC_negT hY) v hv
        simpa [twAct, negT_negT] using this
      · simpa [twAct] using hs w Y hY v hv
    · intro N hN hK1 w Y hY hz v hv
      cases ε
      · refine h7 N hN hK1 w _ (isKC_negT hY) (fun a => ?_) v hv
        obtain ⟨e1, e2, e3, e4⟩ := hz a
        simp [negT_apply, e1, e2, e3, e4]
      · exact h7 N hN hK1 w Y hY hz v hv
  rcases h6 with h6 | h6
  · obtain ⟨c1, c2, c3, c4, c7⟩ := common true
    refine ⟨_, _, r₀, s₀, twAct true (R.p ∘ₗ Φ), c, c', c1, c2, c3, c4, ?_, ?_, c7⟩
    · intro v
      simpa [twAct] using h5 v
    · intro v hv w
      simpa [twAct] using h6 v hv w
  · obtain ⟨c1, c2, c3, c4, c7⟩ := common false
    refine ⟨_, _, r₀, s₀, twAct false (R.p ∘ₗ Φ), fun w => -c w, fun w => -c' w, c1, c2, c3, c4, ?_, ?_, c7⟩
    · intro v
      rw [h5 v]
      simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply, negT_Eab, map_neg, LinearMap.neg_apply,
        Matrix.transpose_single, neg_smul, neg_inj]
    · intro v hv w
      obtain ⟨a1, a2⟩ := h6 v hv w
      refine ⟨fun i hi => ?_, fun j hj => ?_⟩
      · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply, negT_Eab, map_neg, LinearMap.neg_apply,
          a1 i hi, neg_zero]
      · simp only [twAct, Bool.false_eq_true, if_false, LinearMap.comp_apply, negT_Eab, map_neg, LinearMap.neg_apply,
          a2 j hj, neg_zero]

end GlobalTheory.FockBridge.Bridge
