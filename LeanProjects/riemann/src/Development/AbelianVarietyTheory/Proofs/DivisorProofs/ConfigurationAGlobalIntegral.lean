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
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)
open GlobalTheory.FockBridge
open scoped Classical

noncomputable section

namespace GlobalTheory.FockBridge.KerStable

open GlobalTheory.RealLift Formalism.BasicNotions.TH

variable {T P : Type} [AddCommGroup T] [Module ℂ T] [AddCommGroup P] [Module ℂ P]

theorem keeps_add {q : T →ₗ[ℂ] P} {L L' : Module.End ℂ T} (h : Keeps q L) (h' : Keeps q L') : Keeps q (L + L') :=
  fun t ht => by simp [h t ht, h' t ht]

theorem keeps_smul {q : T →ₗ[ℂ] P} {L : Module.End ℂ T} (c : ℂ) (h : Keeps q L) : Keeps q (c • L) :=
  fun t ht => by simp [h t ht]

theorem fock_keeps_ker : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a') (H : Plane E (b + 2) b)
    (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (R : RealMaps F (b + 2) a') (Rf : FinMaps F (b + 2) a')
      (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W) (R₁ : RealMaps F b a') (Rf₁ : FinMaps F b a'),
      IsMatched B G X om om' R Rf → IsMatched B G₁ X om₁ om₁' R₁ Rf₁ →
      ∀ (A : InfinitePlace F → Matrix (Fin (b + 2)) (Formalism.BasicNotions.TH.Ix (b + 2 - G.p) G.p) ℂ) (C : InfinitePlace F → Matrix (Fin (b + 2 + a')) (Formalism.BasicNotions.TH.Ix (b + 2 + a' - (G.p + G.q)) (G.p + G.q)) ℂ) (Φ : GlobalTheory.RealLift.Tens F (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) →ₗ[ℂ] SInf F (Fin (b + 2) × Fin (b + 2 + a'))), IsFockData B G.M A C Φ → ∀ (w : InfinitePlace F) (Y : Formalism.BasicNotions.TH.Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q)),
      Keeps (R.p ∘ₗ Φ) (GlobalTheory.RealLift.atPl w (Formalism.BasicNotions.TH.fockAct2 (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) Y)) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' _ X om om' R Rf om₁ om₁' R₁ Rf₁ hM _ A C Φ hΦd w Y
  obtain ⟨⟨fr, hAθ, hCθ⟩, hΦ⟩ := hΦd
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hM.triple
  have hvl := Main.i_vacline Main.i_derex
  have hfe := Main.i_fockex Main.i_derex
  have hsec := Main.i_liesecond hKP.base Main.i_derex hfe hvl (Main.i_liescalar hKP.base Main.i_derex hvl)
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1 hc.expβ
  have hr := Main.i_polrange Main.i_actslaws Main.i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr
    hAθ hCθ hΦ
  have hreal : ∀ Z ∈ upq (b + 2 + a' - (G.p + G.q)) (G.p + G.q),
      Keeps (R.p ∘ₗ Φ) (atPl w (fockAct2 (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) Z)) := by
    intro Z hZ T hT
    let Yg : InfinitePlace F → Mat (b + 2 + a' - (G.p + G.q)) (G.p + G.q) := Function.update (fun _ => 0) w Z
    have hYu : ∀ w', Yg w' ∈ upq _ _ := fun w' => by
      by_cases h : w' = w
      · subst h; simpa [Yg] using hZ
      · simpa [Yg, Function.update_of_ne h] using Main.zero_mem_upq _ _
    obtain ⟨γ, hγ, hgen⟩ := Main.i_lineex F E σ (Fin (b + 2 + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm fr.2.2 Yg hYu
    have hsd := hW2 γ hγ Yg hgen T
    have h1 := (Main.i_actslaws F _ (Φ T) _ (Φ T)).1 _ (fun t => map_zero _) hsd
    have h0 : ActsD (evI F) (fun t => om' (1, γ (Multiplicative.ofAdd t))) (⇑(0 : SInf F (Fin a' × Fin (b + 2 + a')))) ⇑(0 : SInf F (Fin a' × Fin (b + 2 + a'))) :=
      (Main.i_actslaws F _ 0 0 0).1 _ (fun t => map_zero _) (fun g _ l _ => by
        have e0 : pureA F (⇑(0 : SInf F (Fin a' × Fin (b + 2 + a')))) g = 0 := by
          funext x; simp [pureA]
        simp only [e0, map_zero]
        exact hasDerivAt_const _ _)
    have hf : Φ T ∈ G.M.Pol B.ψ B.emb := hr ▸ LinearMap.mem_range_self Φ T
    have e : R.p (Φ T) = R.p' 0 := by rw [map_zero]; exact hT
    have key := hM.real.lie γ hγ (Φ T) hf 0 (Submodule.zero_mem _) _ 0 h1 h0 e
    have hsum : sumPl (fun w' => fockAct2 (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) (Yg w') +
        ((B.mβ w' : ℂ) / 2 * (Yg w').trace) • 1) =
        atPl w (fockAct2 (b + 2 - G.p) G.p (b + 2 + a' - (G.p + G.q)) (G.p + G.q) Z) + (((B.mβ w : ℂ) / 2) * Z.trace) • 1 := by
      unfold sumPl
      rw [Finset.sum_eq_single w]
      · simp [Yg, Main.atPl_add, Main.atPl_smul, Main.atPl_one]
      · intro w' _ h
        simp [Yg, Function.update_of_ne h, Main.atPl_zero]
      · simp
    rw [hsum, map_zero, LinearMap.add_apply, LinearMap.smul_apply, Module.End.one_apply, map_add, map_add, map_smul,
      map_smul] at key
    change R.p (Φ T) = 0 at hT
    rw [hT, smul_zero, add_zero] at key
    exact key
  obtain ⟨Y₁, h₁, Y₂, h₂, rfl⟩ := GlobalTheory.CoverDS.exists_decomp Y
  rw [map_add, map_smul, Main.atPl_add, Main.atPl_smul]
  exact keeps_add (hreal _ h₁) (keeps_smul _ (hreal _ h₂))

end GlobalTheory.FockBridge.KerStable
