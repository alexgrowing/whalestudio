import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerAlong
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RestrictedHeisenbergTermsPermutedRationalUnitary
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SmulEqZeroOfInf

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition GlobalTheory.MixedTerm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MixedTermTranslate

local infixl:70 " ⬝ " => HMul.hMul

variable {D : D7}

theorem symplOH_isoPart_isoPart (V W : HSp D) {r : ℕ} (C : Matrix (Fin V.rank) (Fin r) D.host.E) (hC : IsIsoFrame V C)
    (b a : Mx D W.rank r) : symplOH V W (isoPart V W C b) (isoPart V W C a) = 0 := by
  set X : Mx D r V.rank := (adj D C * V.gram).map (incA D) with hXdef
  have hM : (adj D C * V.gram)ᴴ = V.gram * C := by
    rw [Matrix.conjTranspose_mul, GlobalTheory.MixModel.gram_conjTranspose]
    show V.gram * (Cᴴ)ᴴ = V.gram * C
    rw [Matrix.conjTranspose_conjTranspose]
  have hX0 : X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X = 0 := by
    have e : GlobalTheory.MixModel.adj X = GlobalTheory.MixModel.rat (V.gram * C) := by
      rw [hXdef, ← hM]; rfl
    rw [e, hXdef]
    show GlobalTheory.MixModel.rat (adj D C * V.gram) ⬝ GlobalTheory.MixModel.rat V.gram⁻¹ ⬝ GlobalTheory.MixModel.rat (V.gram * C) = 0
    rw [← GlobalTheory.MixModel.rat_mul, ← GlobalTheory.MixModel.rat_mul]
    have : adj D C * V.gram * V.gram⁻¹ * (V.gram * C) = adj D C * V.gram * C := by
      rw [Matrix.mul_assoc (adj D C * V.gram), ← Matrix.mul_assoc V.gram⁻¹,
        Matrix.nonsing_inv_mul _ (GlobalTheory.MixModel.gram_isUnit_det V), Matrix.one_mul]
    rw [this]
    exact (congrArg GlobalTheory.MixModel.rat hC.2.2).trans GlobalTheory.MixModel.rat_zero
  rw [GlobalTheory.MixModel.symplOH_eq, GlobalTheory.MixModel.hO_eq_trace]
  have e2 : isoPart V W C b = b ⬝ X := rfl
  have e3 : isoPart V W C a = a ⬝ X := rfl
  rw [e2, e3, GlobalTheory.MixModel.adj_mul]
  have e4 : GlobalTheory.MixModel.giA V ⬝ (GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ (GlobalTheory.MixModel.gA W ⬝ (b ⬝ X)))
      = (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b) ⬝ X := by
    simp only [Matrix.mul_assoc]
  rw [e4, Matrix.trace_mul_comm]
  have e5 : X ⬝ (GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X ⬝ GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b)
      = (X ⬝ GlobalTheory.MixModel.giA V ⬝ GlobalTheory.MixModel.adj X) ⬝ (GlobalTheory.MixModel.adj a ⬝ GlobalTheory.MixModel.gA W ⬝ b) := by
    simp only [Matrix.mul_assoc]
  rw [e5, hX0, Matrix.zero_mul, Matrix.trace_zero, map_zero]

theorem symplO_eq_add (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  unfold symplOH
  rw [← add_mul, ← map_add]
  norm_num

theorem heisO_heisO_apply (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (G : WO S T → ℂ) (u v a : WO S T)
    (hav : symplOH S T a v = 0) :
    heisO ψ S T u (heisO ψ S T v G) a =
      ψ (symplO S T u v) * (ψ (symplOH S T (a + v) u) * G (a + v + u)) := by
  simp only [heisO]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_right_comm a u v]
  congr 2
  rw [GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_left, hav, symplO_eq_add,
    GlobalTheory.FinTranslate.symplOH_skew S T v u]
  ring

end GlobalTheory.MixedTermTranslate

namespace GlobalTheory.MixedTermTranslate

theorem term_heisO_isoPart : ∀ (D : D7) (V V' W : HSp D) (r : ℕ) (C C' : Matrix (Fin V.rank) (Fin r) D.host.E) (B : Matrix (Fin V.rank) (Fin V'.rank) D.host.E), IsIsoSplit V V' C B → ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (μ : Measure (Mx D W.rank r)) (𝓨 : Set (Mx D W.rank r)), IsCovolOne (ratMx D W.rank r) μ 𝓨 → ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G → ∀ (y : Matrix (Fin W.rank) (Fin r) D.host.E) (κ : Mx D W.rank r), term ψ V V' W C C' B μ 𝓨 (heisO ψ V W (isoPart V W C κ) G) y = phase ψ V W C C' y κ * term ψ V V' W C C' B μ 𝓨 G y := by
  intro D V V' W r C C' B hs ψ _ μ 𝓨 hμ G hG y κ
  have hμ' : IsCovolOne (GlobalTheory.MixModel.ratMx D W.rank r) μ 𝓨 := hμ
  have hmid : midPart V V' W B 0 = 0 := by
    show HMul.hMul (0 : Matrix (Fin W.rank) (Fin V'.rank) (AE D)) _ = 0
    exact Matrix.zero_mul _
  have iso := symplOH_isoPart_isoPart V W C hs.frame
  obtain ⟨u, hu⟩ : ∃ u, u = isoPart V W C' (Matrix.map y (incA D)) := ⟨_, rfl⟩
  have hterm : ∀ F : WO V W → ℂ, term ψ V V' W C C' B μ 𝓨 F y =
      ∫ s in 𝓨, heisO ψ V W u F (isoPart V W C s) ∂μ := by
    intro F
    show ∫ s in 𝓨, heisO ψ V W _ F (isoPart V W C s + midPart V V' W B 0) ∂μ = _
    rw [hmid, hu]
    simp only [add_zero]
  let Ψ : Mx D W.rank r → ℂ := fun s => ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)
  have hper : ∀ γ ∈ GlobalTheory.MixModel.ratMx D W.rank r, ∀ s, Ψ (γ + s) = Ψ s := by
    rintro _ ⟨q₀, rfl⟩ s
    have e3 : (incA D).toAddMonoidHom.mapMatrix q₀ = q₀.map (incA D) := rfl
    simp only [Ψ]
    rw [e3, GlobalTheory.TwistEquiRat.isoPart_add, add_assoc (isoPart V W C (q₀.map (incA D))),
      ← GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀, hG.quasi, GlobalTheory.TwistEquiRat.ratW_eq_isoPart V W C q₀,
      GlobalTheory.FinTranslate.symplOH_add_left, GlobalTheory.FinTranslate.symplOH_add_right, iso, zero_add, AddChar.map_add_eq_mul]
    have h1 : ψ (symplOH V W (isoPart V W C (q₀.map (incA D))) u) *
        ψ (-(symplOH V W (isoPart V W C (q₀.map (incA D))) u)) = 1 := by
      rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
    linear_combination (ψ (symplOH V W (isoPart V W C s) u) * G (isoPart V W C s + u)) * h1
  have hph : phase ψ V W C C' y κ = ψ (symplO V W u (isoPart V W C κ)) := by rw [hu]; rfl
  have key : ∀ s, heisO ψ V W u (heisO ψ V W (isoPart V W C κ) G) (isoPart V W C s) =
      phase ψ V W C C' y κ * Ψ (s + κ) := by
    intro s
    rw [heisO_heisO_apply ψ V W G u _ _ (iso s κ), hph]
    show _ = _ * (ψ (symplOH V W (isoPart V W C (s + κ)) u) * G (isoPart V W C (s + κ) + u))
    rw [GlobalTheory.TwistEquiRat.isoPart_add]
  rw [hterm, hterm]
  simp only [key]
  rw [integral_const_mul, GlobalTheory.MixModel.covolOne_integral_add hμ' Ψ hper κ]
  rfl

end GlobalTheory.MixedTermTranslate

end
