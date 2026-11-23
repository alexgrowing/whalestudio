import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Formalism.LocalToGlobal.IndefiniteReal.ConjSubConjSub
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsComplEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedNeBotOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsSplitChartOne
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.SplitFrameW

theorem eq_of_mul_eq_one {K : Type} [Field K] {m n : ℕ} (A : Matrix (Fin m) (Fin n) K) (B : Matrix (Fin n) (Fin m) K)
    (h1 : A * B = 1) (h2 : B * A = 1) : m = n := by
  let e : (Fin n → K) ≃ₗ[K] (Fin m → K) := LinearEquiv.ofLinear (Matrix.toLin' A) (Matrix.toLin' B)
    (by rw [← Matrix.toLin'_mul, h1, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, h2, Matrix.toLin'_one])
  have := e.finrank_eq
  simpa using this.symm

theorem complMap_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E)
    (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E) (hc : Continuous c)
    (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (h : s.w.under (𝓞 (maximalRealSubfield E)) = s.v)
    (a : s.v.adicCompletion (maximalRealSubfield E)) : GlobalTheory.LFun.complMap h a = c a := by
  refine congrFun ((HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) s.v).equalizer
    (GlobalTheory.LFun.SplitChart.continuous_complMap h) hc (funext fun k => ?_)) a
  change GlobalTheory.LFun.complMap h (algebraMap _ _ k) = c (algebraMap _ _ k)
  rw [GlobalTheory.LFun.complMap_algebraMap, ← hci]
  congr 1
  exact s.i.commutes k

theorem under_w {E : Type} [Field E] [NumberField E] [IsCMField E] (s : SplitPlace E) :
    s.w.under (𝓞 (maximalRealSubfield E)) = s.v :=
  HeightOneSpectrum.ext s.w_under

theorem cpt_swap {E : Type} [Field E] [NumberField E] [IsCMField E] (F1 : Subfield E)
    (hF : F1 = maximalRealSubfield E)
    (Φ : FiniteAdeleRing (𝓞 F1) F1 ⊗[F1] E →+* FiniteAdeleRing (𝓞 E) E)
    (hΦ : ∀ (a : FiniteAdeleRing (𝓞 F1) F1) (x : E),
      Φ (a ⊗ₜ[F1] x) = algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap F1 E a)
    (s : SplitPlace E) (c : s.v.adicCompletion (maximalRealSubfield E) ≃+* s.w.adicCompletion E)
    (hc : Continuous c) (hci : ∀ x : E, c (s.i x) = algebraMap E _ x) (y : AL E) :
    Φ ((swapCast hF).symm y) s.w = c (s.proj y) := by
  subst hF
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add y z hy hz =>
    rw [map_add, map_add, map_add, map_add, ← hy, ← hz]
    rfl
  | tmul x a =>
    change Φ (a ⊗ₜ x) s.w = c (s.i x * ReciprocityTheory.Aut.evalAt E s.v a)
    rw [hΦ, map_mul, hci]
    change algebraMap E _ x * GlobalTheory.AdeleBaseChange.adMap _ E a s.w = _
    rw [GlobalTheory.DefU.ClassFin.adMap_eq_complMap (under_w s), complMap_eq s c hc hci]
    rfl

end GlobalTheory.SplitFrameW

namespace GlobalTheory.SplitFrameW

set_option maxHeartbeats 2000000 in

theorem main : ∀ (D : D7) (V : HSp D) (n : ℕ) (hF : D.host.F = maximalRealSubfield D.host.E) (P : principalLevelFrame.RowPsi V n) (β : GL (Fin V.rank) (EAf D)), GlobalTheory.Mem.R3.StdFrame hF P → ∀ (s : SplitPlace D.host.E), ∃ h : GL (Fin n) (s.v.adicCompletion (maximalRealSubfield D.host.E)), ∀ κ : Formalism.AUTREP.GAf D.host.E n, TrivOutside {s.v} κ → h⁻¹ * s.loc n κ * h ∈ GlobalTheory.SplitWeil.KOne (s.v.adicCompletion (maximalRealSubfield D.host.E)) (Fin n) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V n hF P β hS s
  obtain ⟨⟨βs, βs', h1, h2, hfr⟩, -⟩ := hS
  obtain ⟨c, hc, hc', hci⟩ := GlobalTheory.SplitComplHomeo.exists_complEquiv D.host.E s
  obtain ⟨f, hf⟩ : ∃ f : (FiniteAdeleRing (𝓞 D.host.F) D.host.F ⊗[D.host.F] D.host.E) →+* s.w.adicCompletion D.host.E,
    f = (GlobalTheory.StdFrames.cpt s.w).comp (swapAE D) := ⟨_, rfl⟩
  have hn : V.rank = n := eq_of_mul_eq_one (βs.map f) (βs'.map f)
    (by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)])
    (by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)])
  subst hn
  obtain ⟨Φc, hΦc⟩ : ∃ Φc : Matrix (Fin V.rank) (Fin V.rank) (EAf D) →+*
      Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    Φc = (c.symm.toRingHom.comp (GlobalTheory.StdFrames.cpt s.w)).mapMatrix := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B = βs.map (swapAE D) := ⟨_, rfl⟩
  obtain ⟨B', hB'⟩ : ∃ B' : Matrix (Fin V.rank) (Fin V.rank) (EAf D), B' = βs'.map (swapAE D) := ⟨_, rfl⟩
  have hBB : B * B' = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h1, Matrix.map_one _ (map_zero _) (map_one _)]
  have hBB' : B' * B = 1 := by
    rw [hB, hB', ← Matrix.map_mul, h2, Matrix.map_one _ (map_zero _) (map_one _)]
  obtain ⟨X, hX⟩ : ∃ X, X = Φc ((β⁻¹).val * B) := ⟨_, rfl⟩
  obtain ⟨X', hX'⟩ : ∃ X', X' = Φc (B' * β.val) := ⟨_, rfl⟩
  have hXX : X * X' = 1 := by
    rw [hX, hX', ← map_mul, show (β⁻¹).val * B * (B' * β.val) = (β⁻¹).val * (B * B') * β.val by
      simp only [Matrix.mul_assoc], hBB, Matrix.mul_one, Units.inv_mul, map_one]
  have hXX' : X' * X = 1 := by
    rw [hX, hX', ← map_mul, show B' * β.val * ((β⁻¹).val * B) = B' * (β.val * (β⁻¹).val) * B by
      simp only [Matrix.mul_assoc], Units.mul_inv, Matrix.mul_one, hBB', map_one]
  obtain ⟨g, hg⟩ : ∃ g : GL (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E)),
    g = ⟨X', X, hXX', hXX⟩ := ⟨_, rfl⟩
  refine ⟨g, fun κ _ hk a b => ?_⟩
  have hK : Φc (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map (swapCast hF).symm).map (swapAE D)) =
      ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) := by
    rw [hΦc]
    refine Matrix.ext fun i j => ?_
    change c.symm (((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) ((swapCast hF).symm (κ.1.val i j)) s.w) = s.proj (κ.1.val i j)
    rw [cpt_swap D.host.F hF ((GlobalTheory.StdFrames.toAd D).comp (swapAE D)) (fun a x => GlobalTheory.StdFrames.toAd_spec D x a) s c hc hci]
    exact c.symm_apply_apply _
  have e1 : (finE V (P.ψ κ)).val = B * (((κ.1 : Matrix (Fin V.rank) (Fin V.rank) (ReciprocityTheory.Aut.AL D.host.E)).map
      (swapCast hF).symm).map (swapAE D)) * B' := by
    change (finMat D.sp.cm.sig V.gram (P.ψ κ)).map (swapAE D) = _
    rw [hfr κ, Matrix.map_mul, Matrix.map_mul, hB, hB']
  have hM : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) = X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [Units.val_mul, Units.val_mul, e1, ← hK, hX, hX', ← map_mul, ← map_mul]
    simp only [Matrix.mul_assoc]
  have hv := (GlobalTheory.FixedAtSplit.mem_KOne_iff' _).1 hk a b
  have e3 : (↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) =
      X * ((s.loc V.rank κ : GL _ _) : Matrix _ _ _) * X' := by
    rw [hg]; rfl
  have hent : Φc ((β⁻¹ * finE V (P.ψ κ) * β).val) a b =
      c.symm (GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b)) := by
    rw [hΦc]; rfl
  have e2 : GlobalTheory.StdFrames.cpt s.w ((β⁻¹ * finE V (P.ψ κ) * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b) =
      c (((↑(g⁻¹ * s.loc V.rank κ * g) : Matrix (Fin V.rank) (Fin V.rank) (s.v.adicCompletion (maximalRealSubfield D.host.E))) - 1) a b) := by
    rw [e3, ← hM, Matrix.sub_apply, hent, map_sub, map_sub, c.apply_symm_apply, Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  rw [e2]
  by_contra hne
  push_neg at hne
  have := GlobalTheory.FixedAtSplit.valued_lt_one_of_map c.symm hc' (c _) (by rw [c.symm_apply_apply]; exact hv)
  exact absurd this (not_lt.2 hne)

end GlobalTheory.SplitFrameW
