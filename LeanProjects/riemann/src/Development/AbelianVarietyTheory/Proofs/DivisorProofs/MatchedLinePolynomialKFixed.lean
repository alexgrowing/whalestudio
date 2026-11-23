import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedTripleFiniteMapsForallPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.DerivFix

open GlobalTheory.RealLift GlobalTheory.RealLift.Main GlobalTheory.FockCompactW Formalism.BasicNotions.TH GlobalTheory.FockAlg
open scoped Classical

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem exists_der_first (hP : GlobalTheory.FunPr.Hypotheses₂) {B : Base F E} {a a' : ℕ} {G : Geo σ a a'} {X : Chars F E}
    {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} (hT : IsTriple B G X om om') (γ : Multiplicative ℝ →* UA σ G.W.J)
    (hγ : γ ∈ Lines σ G.W) :
    ∃ D : SInf F (Fin a × Fin (a + a')) →ₗ[ℂ] SInf F (Fin a × Fin (a + a')),
      ∀ f ∈ G.M.Pol B.ψ B.emb, SD (fun t => om (1, γ (Multiplicative.ofAdd t))) f (D f) := by
  obtain ⟨hb, hg, hc, hw, hw'⟩ := hT
  choose A hA hAθ using fun w => i_frameex _ _ _ _ _ (hg.hV.sig w) (hg.hV.cartan w)
  choose C hC hCθ using fun w => i_frameex _ _ _ _ _ (hg.hW.sig w) (hg.hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F G.V.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F G.W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F G.V.J) (incM F G.W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  have hvl := i_vacline i_derex
  have hfe := i_fockex i_derex
  have hsec := i_liesecond hP i_derex hfe hvl (i_liescalar hP i_derex hvl)
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := i_polrange i_actslaws i_derex hvl F E σ _ _ _ _ _ _ G.V G.W G.M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hwp : IsUWeilPair (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V.J) (incM F G.W.J) G.M.co X.β (X.β / X.α) om := hw
  have hW2 := hsec F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ G.M.co 1 Complex.I A C Φ _ X.β B.mβ hb.cm hb.std fr hΦ hwp.1
    hc.expβ
  obtain ⟨Yg, -, hY⟩ := i_genex F E σ (Fin (a + a')) _ _ B.emb (incM F G.W.J) Complex.I C hb.cm hC1 γ hγ
  obtain ⟨Ψ, hΨ⟩ := LinearMap.exists_leftInverse_of_injective Φ (LinearMap.ker_eq_bot.2 hΦ.1)
  refine ⟨Φ ∘ₗ sumPl (fun w => fockAct2 _ _ _ _ (Yg w) + (((B.mβ w : ℂ) / 2) * (Yg w).trace) • 1) ∘ₗ Ψ, fun f hf => ?_⟩
  obtain ⟨T, rfl⟩ := pol_eq B G.M Φ hr hf
  have e : Ψ (Φ T) = T := by rw [← LinearMap.comp_apply, hΨ, LinearMap.id_apply]
  simp only [LinearMap.comp_apply, e]
  exact hW2 γ hγ Yg hY T

theorem sd_comm_left {n d : ℕ} {Y : Spc F E n} {W : Spc F E d} {M : Model σ Y W} {ψ : AddChar (AF F) ℂ}
    {χ₁ χ₂ : Chr F E} {om : Rep σ Y W} (hw : M.IsWeil ψ χ₁ χ₂ om) (k : UA σ Y.J) (γ : Multiplicative ℝ →* UA σ W.J)
    {f f₁ g g₁ : SInf F (Fin n × Fin d)} (hf : Acts (evI F) (om (k, 1)) f g) (hf₁ : Acts (evI F) (om (k, 1)) f₁ g₁)
    (hD : SD (fun t => om (1, γ (Multiplicative.ofAdd t))) f f₁) :
    SD (fun t => om (1, γ (Multiplicative.ofAdd t))) g g₁ := by
  have hS := IsUWeilPair.isUSplitting hw
  intro r hr l hl
  have h1 := hD r hr _ (hS.adm (k, 1) l hl)
  simp only [LinearMap.comp_apply] at h1
  rw [sa_of_acts hf₁ r hr] at h1
  refine h1.congr_of_eventuallyEq (.of_forall fun t => ?_)
  have hcomm : om (k, 1) (om (1, γ (Multiplicative.ofAdd t)) (pureA F f r)) =
      om (1, γ (Multiplicative.ofAdd t)) (om (k, 1) (pureA F f r)) := by
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 2
    exact Prod.ext (by simp) (by simp)
  show l (om (1, γ (Multiplicative.ofAdd t)) (pureA F g r)) = l (om (k, 1) (om (1, γ (Multiplicative.ofAdd t)) (pureA F f r)))
  rw [hcomm, sa_of_acts hf r hr]

theorem isKFix_of_actsD : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W)
    (R : RealMaps F a a') (Rf : FinMaps F a a'), IsMatched B G X om om' R Rf →
      ∀ γ ∈ Lines σ G.W, ∀ g ∈ G.M.Pol B.ψ B.emb, IsKFix B om g → ∀ f₁ : SInf F (Fin a × Fin (a + a')),
        ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g f₁ → IsKFix B om f₁ := by
  intro hK F E _ _ _ _ _ σ B a a' G X om om' R Rf hM γ hγ g hg hgk f₁ hf₁ k hk
  have hL := actsLaws F (Fin a × Fin (a + a'))
  obtain ⟨D, hD⟩ := exists_der_first hK.base hM.triple γ hγ
  have hSD := hD g hg
  have hAD : ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) g (D g) :=
    (hL g (D g) (D g)).1 _ (fun t => map_zero _) hSD
  have e1 : f₁ = D g := (hL g f₁ (D g)).2.2.1 _ hf₁ hAD
  subst e1
  have h1 : (1 : UA σ G.W.J) ∈ UAt σ G.W (evI F) := by
    intro u _
    simp [mat]
  obtain ⟨A, hA⟩ := exists_op_of_UAt hM.triple.base.std hM.triple.weil (k, 1) hk.1 h1
  have hAg : A g = g := (hL g (A g) g).2.2.2.1 _ (hA g) (hgk k hk)
  have h2 := sd_comm_left hM.triple.weil k γ (hA g) (hA (D g)) hSD
  rw [hAg] at h2
  have hAf : A (D g) = D g := (hL g (A (D g)) (D g)).2.2.2.2 _ h2 hSD
  have := hA (D g)
  rw [hAf] at this
  exact this

end GlobalTheory.DerivFix

end
