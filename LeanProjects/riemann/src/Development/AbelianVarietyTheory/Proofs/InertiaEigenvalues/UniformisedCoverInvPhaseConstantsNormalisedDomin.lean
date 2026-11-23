import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValRingLocRing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BaseCoverFramesDifferByRationalIsometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesSecond
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsGenReadsOfUnitAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacuumReadingConstantsLevelCoverRelateCoreStatement
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.SingleDatum GlobalTheory.CoverRead
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
open GlobalTheory.LevelSeries

noncomputable section

namespace GlobalTheory.CoverPinDom

set_option maxHeartbeats 2000000 in

theorem pin_at {D : D7} (T : CoreJ D) (hL : LawsJ T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ) (hσ : GoodEmb T.Q.c σ)
    (C : Cover T j σ) (hC : C.IsUnif) {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} (hV : T.V j σ = W)
    (hr : W.rank = D.R.r) {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hM : ∀ k, IsMod W hr ((T.U j σ).X k)) {f₀ : WO V W → ℂ}
    (hf₀ : IsThetaFunO ψ V W f₀) {mu : GA D (T.V j σ) → ℂ} (hmu0 : ∀ g, mu g ≠ 0)
    (hunit : ∀ h, IsUnitFr ((T.U j σ).X (T.dict j σ h).1) (T.dict j σ h).2)
    {c₁ : C.U₂.Comp → ℂ} {c₂ : (T.U j σ).Comp → ℂ}
    (h₁ : CcIs θ V W hr C.U₂ (castDict hV C.dict₂) (castDict hV mu) (T.x₀ j σ) om f₀ c₁)
    (h₂ : CcIs θ V W hr (T.U j σ) (castDict hV (T.dict j σ)) (castDict hV mu) (T.x₀ j σ) om f₀ c₂)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) (hf : f ∈ sec (T.Q.Xo j) T.Q.c a V.rank)
    (f₂ : Rul C.d.Xo₂ C.d.c₂) (hf₂ : f₂ ∈ sec C.d.Xo₂ C.d.c₂ a V.rank) (hp : C.IsPull f f₂) (g : GA D (T.V j σ)) :
    c₁ (C.dict₂ g).1 * rdU C.U₂ f₂ (C.dict₂ g).1 (C.dict₂ g).2 =
      c₂ (T.dict j σ g).1 * rdU (T.U j σ) f (T.dict j σ g).1 (T.dict j σ g).2 := by
  subst hV
  change CcIs θ V (T.V j σ) hr C.U₂ C.dict₂ mu (T.x₀ j σ) om f₀ c₁ at h₁
  change CcIs θ V (T.V j σ) hr (T.U j σ) (T.dict j σ) mu (T.x₀ j σ) om f₀ c₂ at h₂

  have hθ := hP.inf
  have hC₀ := hC
  have hU₁ := hL.unf j hj σ hσ
  have hU₂ : IsUnf C.U₂ := hC.2.2.2.1
  obtain ⟨_, _, -, hd⟩ := hL.dictU j hj σ hσ
  have hdom₁ : ∀ h, (T.dict j σ h).2 ∈ ((T.U j σ).X (T.dict j σ h).1).dom := hd.2.2.2.1
  obtain ⟨hr₁, g₁, e₁, F₁, ik₁, φ₁, th₁, -, -, hth₁, -, hd₁⟩ := hL.adPin j hj σ hσ
  obtain ⟨-, -, -, -, hdom₂, hr₂, g₂, e₂, F₂, ik₂, φ₂, th₂, hW₂, hth₂, -, hd₂⟩ := hC
  obtain ⟨hr₀, hW₁⟩ := hL.modelW j hj σ hσ
  obtain ⟨γ₁, hγ₁, hL₁, -, hq₁⟩ := hd₁ g
  obtain ⟨γ₂, hγ₂, hL₂, -, hq₂⟩ := hd₂ g
  obtain ⟨δ, hl, hi, hfδ⟩ := GlobalTheory.CoverFrameMove.move (T.V j σ) hr₁ g γ₁ γ₂ hγ₁ hγ₂ _ _ _ _ (hW₁ (T.dict j σ g).1).1 (hW₂ (C.dict₂ g).1).1 hL₁ hL₂
  have hfr : ∀ (τ : D.host.E →+* ℂ) (t₂ : τ ∈ (C.U₂.X (C.dict₂ g).1).Ψ) (t₁ : τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ),
      mat (T.dict j σ g).2 ⟨τ, t₁⟩ = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ * mat (C.dict₂ g).2 ⟨τ, t₂⟩ := by
    intro τ t₂ t₁
    have e₂' := hq₂ ⟨τ, t₂⟩
    have e₁' := hq₁ ⟨τ, t₁⟩
    rw [GlobalTheory.LettersCheck.isInfEmb_unique τ _ _ (hth₂ _ ⟨τ, t₂⟩) (hth₁ _ ⟨τ, t₁⟩)] at e₂'
    rw [e₁', e₂']
    exact hfδ τ _ (hth₁ _ ⟨τ, t₁⟩) _
  have hΨ₁ : ∀ k, ∀ τ ∈ ((T.U j σ).X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ => ((hM k).psi τ).1 hτ
  have hΨ₂ : ∀ k, ∀ τ ∈ (C.U₂.X k).Ψ, ∃ ρ, τ = tauE D ρ := fun k τ hτ =>
    hΨ₁ (T.dict j σ g).1 τ (((hU₁.2.1 _).2 τ).2 (((hU₂.2.1 k).2 τ).1 hτ))
  have hat₁ : AtComp θ (T.V j σ) hr (T.U j σ).X (T.dict j σ) (T.x₀ j σ) g γ₁ := by
    refine ⟨hγ₁, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₁, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₁ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₁ * g) τ.1 (hΨ₁ _ _ τ.2) _ (hth₁ _ τ)] at this
      exact this
  have hat₂ : AtComp θ (T.V j σ) hr C.U₂.X C.dict₂ (T.x₀ j σ) g γ₂ := by
    refine ⟨hγ₂, ?_, ?_⟩
    · apply SetLike.coe_injective
      rw [hL₂, latR, Submodule.map_coe]
      rfl
    · funext τ
      have := hq₂ τ
      rw [← GlobalTheory.AdTh.CcModel.realM_mt hθ _ (γ₂ * g) τ.1 (hΨ₂ _ _ τ.2) _ (hth₂ _ τ)] at this
      exact this
  have hrm : ∀ τ ∈ ((T.U j σ).X (T.dict j σ g).1).Ψ, Matrix.reindex (finCongr hr) (finCongr hr)
      (realM θ (Formalism.L2.Theta.mt (T.V j σ) (γ₁ * γ₂⁻¹)) τ) = (δ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E).map τ := by
    intro τ t₁
    have hth := hth₁ _ ⟨τ, t₁⟩
    rw [GlobalTheory.AdTh.CcModel.realM_mt hθ _ _ τ (hΨ₁ _ _ t₁) _ hth]
    generalize th₁ (T.dict j σ g).1 ⟨τ, t₁⟩ = th at hth ⊢
    have hmul : ∀ a b : GA D (T.V j σ), archM (T.V j σ) th (a * b) = archM _ th a * archM _ th b := fun a b => by
      rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]
    have hone : archM (T.V j σ) th 1 = 1 := by
      rw [archM, map_one, Units.val_one, Matrix.map_one] <;> simp
    have hre : ∀ A B : Matrix (Fin (T.V j σ).rank) (Fin (T.V j σ).rank) ℂ,
        Matrix.reindex (finCongr hr) (finCongr hr) (A * B) =
          Matrix.reindex (finCongr hr) (finCongr hr) A * Matrix.reindex (finCongr hr) (finCongr hr) B := fun A B => by
      simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    have e1 := hfδ τ th hth 1
    rw [Matrix.mul_one, Matrix.mul_one] at e1
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hmul, hre] at e1
    have e3 : Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
        Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹) = 1 := by
      rw [← hre, ← hmul, mul_inv_cancel, hone]
      simp
    calc _ = Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₁ * γ₂⁻¹)) *
          (Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)) *
            Matrix.reindex (finCongr hr) (finCongr hr) (archM (T.V j σ) th (γ₂ * g)⁻¹)) := by rw [e3, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, e1, Matrix.mul_assoc, e3, Matrix.mul_one]
  have hm2 : ∀ a b : GA D (T.V j σ), om (1, a * b) = om (1, a) * om (1, b) := fun a b => by
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hF : ∀ w, om (1, γ₁ * g) f₀ (actO V (T.V j σ) 1 (γ₁ * γ₂⁻¹) w) = om (1, γ₂ * g) f₀ w := fun w => by
    rw [show γ₁ * g = γ₁ * γ₂⁻¹ * (γ₂ * g) by group, hm2, Module.End.mul_apply]
    exact GlobalTheory.WeilRat.om_rat_actO D ψ hP.weil.std V (T.V j σ) χV χW om hP.weil 1 (one_mem _) _
      (mul_mem hγ₁ (inv_mem hγ₂)) _ (hP.weil.om_pres _ _ hf₀) w
  have key := GlobalTheory.T.vacuumReadingConstants_levelCover_relate_core D T hL j hj σ hσ C hC₀ ψ θ V χV χW om hP hr hM g δ hl hi hfr (γ₁ * γ₂⁻¹) hrm (hdom₁ g) (hdom₂ g)
    (hunit g) (om (1, γ₂ * g) f₀) (om (1, γ₁ * g) f₀) (c₁ (C.dict₂ g).1 * mu g) (c₂ (T.dict j σ g).1 * mu g)
    (h₁.2 g γ₂ hat₂ (hdom₂ g)) (h₂.2 g γ₁ hat₁ (hdom₁ g)) hF a f hf f₂ hf₂ hp
  apply mul_left_cancel₀ (hmu0 g)
  linear_combination key

set_option maxHeartbeats 2000000 in

theorem isPinned_inv_mul : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), LawsJ T → R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ → ∀ (i : Fin D.R.m), VStd D i → ∀ hV : T.V ((i : ℕ) + 1) T.σ₀ = Wc D i, ∀ ph : ℂ, ‖ph‖ = 1 → BaseCc T R i hV ph → ∀ C : Cover T ((i : ℕ) + 1) T.σ₀, C.IsUnif → ∀ cc : C.U₂.Comp → ℂ, CcIs R.θ (Vc D i) (Wc D i) (rank_Wc i) C.U₂ (castDict hV C.dict₂) (castDict hV (T.mu ((i : ℕ) + 1) T.σ₀)) (T.x₀ ((i : ℕ) + 1) T.σ₀) (R.ωP i A.μ0) (R.vacP i) cc → ∀ a, Dom a (κ i).n → ({ C with cc₂ := fun k => ph⁻¹ * cc k } : Cover T ((i : ℕ) + 1) T.σ₀).IsPinned a (κ i).n := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hL hlev hgrp hfam hmods hthP ht i hS hV ph hph hbase C hC cc hcc a ha
  have hC3 : GlobalTheory.Hk3.CoreNoChain R F := ⟨hlev, hgrp, hfam, hmods, hthP⟩
  have hj : InR D ((i : ℕ) + 1) := inR i
  have hσ : GoodEmb T.Q.c T.σ₀ := T.good_σ₀
  have hmod := GlobalTheory.AdTh.models_at_record_core_nc D G Pl0 T0 A T R F κ v₀ hC3 ht i T.σ₀ rfl
  have hP := (GlobalTheory.AdTh.RecPairCore.isPair_record_core_nc D G Pl0 T0 A T.Q.c.F R F hC3 i A.μ0 hS).1
  have hf₀ := (hthP.vP i A.μ0).1.2.theta
  have hmu0 : ∀ g, T.mu ((i : ℕ) + 1) T.σ₀ g ≠ 0 := fun g =>
    norm_ne_zero_iff.1 (((hL.muVal _ hj _ hσ).norm g).trans_ne one_ne_zero)
  have hunit := (hL.muUnit _ hj _ hσ).2.2.2
  have hph0 : ph ≠ 0 := norm_ne_zero_iff.1 (by rw [hph]; exact one_ne_zero)
  refine ⟨fun k => ?_, fun f hf f₂ hf₂ hp => ?_⟩
  · show ‖ph⁻¹ * cc k‖ = 1
    rw [norm_mul, norm_inv, hph, hcc.norm k, inv_one, one_mul]
  · funext g
    have hn : (κ i).n = (Vc D i).rank := (hmod (T.dict _ _ g).1).2.2.2.2.2.2.2.2.2.2.2.1
    rw [hn] at hf hf₂
    have key := GlobalTheory.CoverPinDom.pin_at T hL _ hj _ hσ C hC hV (rank_Wc i) hP (fun k => (hmod k).1) hf₀ hmu0 hunit hcc
      hbase a f hf f₂ hf₂ hp g
    show Cover.rd _ a f₂ g = T.phiJ _ _ a f g
    simp only [Cover.rd, CoreJ.phiJ, Pi.smul_apply, smul_eq_mul, adel_muPin] at key ⊢
    have hinv : ph⁻¹ * ph = 1 := inv_mul_cancel₀ hph0
    linear_combination (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * ph⁻¹ * T.mu ((i : ℕ) + 1) T.σ₀ g) * key +
      (↑(lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) a) * T.cE ((i : ℕ) + 1) T.σ₀ (T.dict ((i : ℕ) + 1) T.σ₀ g).1 *
        T.mu ((i : ℕ) + 1) T.σ₀ g * rdU (T.U ((i : ℕ) + 1) T.σ₀) f (T.dict ((i : ℕ) + 1) T.σ₀ g).1
          (T.dict ((i : ℕ) + 1) T.σ₀ g).2) * hinv

end GlobalTheory.CoverPinDom
