import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.AdjointIsotropicDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisOApplyZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdjEqZeroOfSymplO

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LeviRes

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem adj_rat {m n : ℕ} (M : Matrix (Fin m) (Fin n) D.host.E) :
    GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat M) = GlobalTheory.MixModel.rat Mᴴ := by
  rw [← GlobalTheory.MixModel.cT_sig]
  ext i j
  simp [GlobalTheory.MixModel.adj, GlobalTheory.MixModel.rat, Formalism.UG.cT, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR]

theorem symplOH_add_right (S T : HSp D) (x y z : WO S T) :
    symplOH S T x (y + z) = symplOH S T x y + symplOH S T x z := by
  simp only [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, GlobalTheory.MixModel.adj_add, Matrix.add_mul,
    Matrix.mul_add, Matrix.trace_add, map_add]

theorem symplOH_mul_rat (V W : HSp D) {s t : ℕ} (X : Matrix (Fin s) (Fin V.rank) D.host.E)
    (Y : Matrix (Fin t) (Fin V.rank) D.host.E) (hXY : X * V.gram⁻¹ * Yᴴ = 0) (q : Mx D W.rank s) (a : Mx D W.rank t) :
    symplOH V W (q ⬝ GlobalTheory.MixModel.rat X) (a ⬝ GlobalTheory.MixModel.rat Y) = 0 := by
  have hz : GlobalTheory.MixModel.rat X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.rat Yᴴ = 0 := by
    rw [GlobalTheory.MixModel.giA, ← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul, hXY, GlobalTheory.MixModel.rat_zero]
  have hre : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj (a ⬝ GlobalTheory.MixModel.rat Y) ⬝ (GlobalTheory.MixModel.gA W ⬝ (q ⬝ GlobalTheory.MixModel.rat X)))
      = (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.rat Yᴴ ⬝ (GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ q)) ⬝ GlobalTheory.MixModel.rat X := by
    rw [GlobalTheory.MixModel.adj_mul, adj_rat]
    simp only [Matrix.mul_assoc]
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace, hre, Matrix.trace_mul_comm]
  simp only [← Matrix.mul_assoc, hz, Matrix.zero_mul, Matrix.trace_zero, map_zero]

section Split

variable {V V' W : HSp D} {r : ℕ} {C : Matrix (Fin V.rank) (Fin r) D.host.E}
  {B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E}

theorem iso_iso (hs : IsIsoSplit V V' C B) : (adj D C * V.gram) * V.gram⁻¹ * (adj D C * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * C = 0 := hs.frame.2.2
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, h0]

theorem iso_mid (hs : IsIsoSplit V V' C B) :
    (adj D C * V.gram) * V.gram⁻¹ * (V'.gram⁻¹ * adj D B * V.gram)ᴴ = 0 := by
  have h0 : adj D C * V.gram * B = 0 := hs.orth
  have hcan : ∀ {n : ℕ} (Z : Matrix (Fin V.rank) (Fin n) D.host.E), V.gram * (V.gram⁻¹ * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig] at h0 ⊢
  simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, GlobalTheory.MixModel.gram_conjTranspose,
    Matrix.mul_assoc, hcan]
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h0, Matrix.zero_mul]

theorem periodic (hs : IsIsoSplit V V' C B) {ψ : AddChar (AF D.host.F) ℂ} {f : WO V W → ℂ}
    (hf : IsThetaFunO ψ V W f) (x : WO V' W) :
    ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ y : Mx D W.rank r,
      f (isoPart V W C (γ + y) + midPart V V' W B x) = f (isoPart V W C y + midPart V V' W B x) := by
  intro γ hγ y
  obtain ⟨γ0, rfl⟩ := GlobalTheory.MixModel.mem_ratMx.1 hγ
  have e1 : ∀ z : Mx D W.rank r, isoPart V W C z = z ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram) := fun z => rfl
  have e2 : midPart V V' W B x = (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) := rfl
  have h0 : symplOH V W (GlobalTheory.MixModel.rat γ0 ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram))
      (isoPart V W C y + midPart V V' W B x) = 0 := by
    rw [symplOH_add_right, e1, e2,
      symplOH_mul_rat V W (adj D C * V.gram) (adj D C * V.gram) (iso_iso hs) (GlobalTheory.MixModel.rat γ0) y,
      symplOH_mul_rat V W (adj D C * V.gram) (V'.gram⁻¹ * adj D B * V.gram) (iso_mid hs) (GlobalTheory.MixModel.rat γ0) x,
      add_zero]
  have hq : f (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram)) + (isoPart V W C y + midPart V V' W B x)) =
      ψ (-(symplOH V W (GlobalTheory.MixModel.rat (γ0 * (adj D C * V.gram))) (isoPart V W C y + midPart V V' W B x))) *
        f (isoPart V W C y + midPart V V' W B x) :=
    hf.quasi (γ0 * (adj D C * V.gram)) (isoPart V W C y + midPart V V' W B x)
  rw [e1 (GlobalTheory.MixModel.rat γ0 + y), Matrix.add_mul, add_assoc, ← e1 y, ← GlobalTheory.MixModel.rat_mul, hq,
    GlobalTheory.MixModel.rat_mul, h0, neg_zero, AddChar.map_zero_eq_one, one_mul]

end Split

theorem mt_unitary (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a) ⬝ GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.gA V := by
  rw [Matrix.mul_assoc]
  exact GlobalTheory.MixModel.mt_unitary V a

theorem mt_mul (V : HSp D) (a b : GA D V) :
    Formalism.L2.Theta.mt V (a * b) = Formalism.L2.Theta.mt V a * Formalism.L2.Theta.mt V b := by
  simp only [Formalism.L2.Theta.mt, map_mul, Units.val_mul]

theorem mt_one (V : HSp D) : Formalism.L2.Theta.mt V 1 = 1 := by
  simp only [Formalism.L2.Theta.mt, map_one, Units.val_one]

theorem actO_mul_mt (S T : HSp D) (g : GA D S) (w : WO S T) :
    actO S T g 1 (HMul.hMul (w : Matrix (Fin T.rank) (Fin S.rank) (AE D)) (Formalism.L2.Theta.mt S g)) = w := by
  rw [GlobalTheory.MixModel.actO_eq, mt_one, Matrix.one_mul, Matrix.mul_assoc, ← mt_mul, mul_inv_cancel, mt_one,
    Matrix.mul_one]

private lemma rat_adj_mul_gram_eq (V : HSp D) {s : ℕ} (B : Matrix (Fin V.rank) (Fin s) D.host.E) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) = GlobalTheory.MixModel.adj (GlobalTheory.MixModel.rat B) ⬝ GlobalTheory.MixModel.gA V := by
  rw [GlobalTheory.MixModel.rat_mul, adj_rat, GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition.adj, GlobalTheory.MixModel.cT_sig, GlobalTheory.MixModel.gA]

private lemma gA_mul_mt_eq_adj_mt_inv_mul (V : HSp D) (a : GA D V) :
    GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V := by
  calc GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a
      = (GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V ⬝ Formalism.L2.Theta.mt V a⁻¹) ⬝ Formalism.L2.Theta.mt V a := by
        rw [mt_unitary]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V ⬝ (Formalism.L2.Theta.mt V a⁻¹ ⬝ Formalism.L2.Theta.mt V a) := by
        rw [Matrix.mul_assoc]
    _ = GlobalTheory.MixModel.adj (Formalism.L2.Theta.mt V a⁻¹) ⬝ GlobalTheory.MixModel.gA V := by
        rw [← mt_mul, inv_mul_cancel, mt_one, Matrix.mul_one]

theorem form_fix (V : HSp D) {s : ℕ} (a : GA D V) (B : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B) :
    GlobalTheory.MixModel.rat (adj D B * V.gram) ⬝ Formalism.L2.Theta.mt V a = GlobalTheory.MixModel.rat (adj D B * V.gram) := by
  have hinv : Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := by
    conv_lhs => rw [← h]
    rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv]

theorem form_scale (V : HSp D) {s : ℕ} (a : GA D V) (C : Matrix (Fin V.rank) (Fin s) D.host.E)
    (h : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C) :
    GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      incA D (1 / 2) • GlobalTheory.MixModel.rat (adj D C * V.gram) := by
  have h2 : incA D (1 / 2) * (2 : AE D) = 1 := by
    rw [← map_ofNat (incA D) 2, ← map_mul]
    norm_num
  have hinv : Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
    calc Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C
        = (incA D (1 / 2) * (2 : AE D)) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ GlobalTheory.MixModel.rat C) := by rw [h2, one_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ ((2 : AE D) • GlobalTheory.MixModel.rat C)) := by
        rw [mul_smul, Matrix.mul_smul]
      _ = incA D (1 / 2) • (Formalism.L2.Theta.mt V a⁻¹ ⬝ (Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C)) := by rw [h]
      _ = incA D (1 / 2) • GlobalTheory.MixModel.rat C := by
        rw [← Matrix.mul_assoc, ← mt_mul, inv_mul_cancel, mt_one, Matrix.one_mul]
  have hc : cA D (incA D (1 / 2)) = incA D (1 / 2) := GlobalTheory.MixModel.cA_half
  rw [rat_adj_mul_gram_eq, Matrix.mul_assoc, gA_mul_mt_eq_adj_mt_inv_mul, ← Matrix.mul_assoc, ← GlobalTheory.MixModel.adj_mul, hinv,
    GlobalTheory.MixModel.adj_smul, hc, Matrix.smul_mul]

theorem res_levi : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ a : GA D V, a ∈ GQ V → HMul.hMul (matHom V a).1 (C.map (incA D)) = (2 : AE D) • C.map (incA D) → HMul.hMul (matHom V a).1 (B.map (incA D)) = B.map (incA D) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (χS χT : (AE D)ˣ →* Circle) (ω : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)), IsWeilDatumO ψ V W χS χT ω → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∃ l : ℂ, ∀ f, IsThetaFunO ψ V W f → res V V' W C B μ 𝓨 (ω (a, 1) f) = l • res V V' W C B μ 𝓨 f := by
  intro D V V' W r C B hs a haQ haC haB ψ χS χT ω hω μ 𝓨 hcov
  refine ⟨1, fun f hf => ?_⟩
  have hC' : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat C = (2 : AE D) • GlobalTheory.MixModel.rat C := haC
  have hB' : Formalism.L2.Theta.mt V a ⬝ GlobalTheory.MixModel.rat B = GlobalTheory.MixModel.rat B := haB
  have hsub : ∀ w : WO V W,
      ω (a, 1) f w = f (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a)) := by
    intro w
    have h1 := GlobalTheory.WeilRat.om_rat_actO D ψ hω.std V W χS χT ω hω a haQ 1 (one_mem _) f hf
      (HMul.hMul (w : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a))
    rwa [actO_mul_mt] at h1
  have hiso : ∀ y : Mx D W.rank r,
      HMul.hMul (isoPart V W C y : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
        isoPart V W C (incA D (1 / 2) • y) := by
    intro y
    show y ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      (incA D (1 / 2) • y) ⬝ GlobalTheory.MixModel.rat (adj D C * V.gram)
    rw [Matrix.mul_assoc, form_scale V a C hC', Matrix.mul_smul, Matrix.smul_mul]
  rw [one_smul]
  funext x
  have hmid : HMul.hMul (midPart V V' W B x : Matrix (Fin W.rank) (Fin V.rank) (AE D)) (Formalism.L2.Theta.mt V a) =
      midPart V V' W B x := by
    show (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram) ⬝ Formalism.L2.Theta.mt V a =
      (x : Mx D W.rank V'.rank) ⬝ GlobalTheory.MixModel.rat (V'.gram⁻¹ * adj D B * V.gram)
    rw [Matrix.mul_assoc V'.gram⁻¹ (adj D B) V.gram, GlobalTheory.MixModel.rat_mul]
    simp only [Matrix.mul_assoc]
    rw [form_fix V a B hB']
  calc res V V' W C B μ 𝓨 (ω (a, 1) f) x
      = ∫ y in 𝓨, f (isoPart V W C (incA D (1 / 2) • y) + midPart V V' W B x) ∂μ := by
        show ∫ y in 𝓨, ω (a, 1) f (isoPart V W C y + midPart V V' W B x) ∂μ = _
        congr 1
        funext y
        rw [hsub, Matrix.add_mul, hiso, hmid]
    _ = ∫ y in 𝓨, f (isoPart V W C y + midPart V V' W B x) ∂μ :=
        GlobalTheory.UnipMean.mean_smul hcov (c := 1 / 2) (by norm_num)
          (fun y => f (isoPart V W C y + midPart V V' W B x)) (periodic hs hf x)
    _ = res V V' W C B μ 𝓨 f x := rfl

end GlobalTheory.LeviRes
