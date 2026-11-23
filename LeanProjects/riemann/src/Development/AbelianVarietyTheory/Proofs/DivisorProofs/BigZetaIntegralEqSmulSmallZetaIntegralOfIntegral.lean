import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMixModelB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAwayUnitOfPowEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZetaIdentityPersistsRowColumnChanges
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

noncomputable section
namespace GlobalTheory.TopFlip.ZMatQ
open GlobalTheory.FlipMatch.ZMat

section
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instBorelGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [MeasurableSpace k] [BorelSpace k]

theorem smallF_rows {A C C₁ : Type} [Fintype A] [DecidableEq A]
    [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁)
    (μ : Measure (GL A k)) [μ.IsHaarMeasure] (ν : kˣ →* ℂˣ)
    {g₀ : GL A k} (hg : g₀ ∈ KO k A) (c : Matrix C C k) (Ψ : Matrix A C₁ k → ℂ) (Y : Matrix A C k) :
      (ν (gdet g₀) : ℂ) * smallF μ ν (fun Y => Ψ (reindex (Equiv.refl _) eC (g₀.val * Y * c))) Y =
        smallF μ ν Ψ (reindex (Equiv.refl _) eC (Y * c)) := by
  unfold smallF
  rw [← Fintype.card_congr eC,
    ← integral_mul_left_eq_self (fun g : GL A k => Ψ (g.val * reindex (Equiv.refl _) eC (Y * c)) *
      (ν (gdet g) : ℂ) * apow (gdet g) ((Fintype.card C : ℂ) / 2)) g₀, ← integral_const_mul]
  congr 1
  funext g
  have h2 : (g₀ * g).val * reindex (Equiv.refl _) eC (Y * c) =
      reindex (Equiv.refl _) eC (g₀.val * (g.val * Y) * c) := by
    have h5 : ∀ (M : Matrix A A k) (N : Matrix A C k),
        M * reindex (Equiv.refl _) eC N = reindex (Equiv.refl _) eC (M * N) := fun M N => by
      ext i j
      simp [Matrix.mul_apply]
    rw [h5]
    simp only [Units.val_mul, Matrix.mul_assoc]
  rw [h2, gdet_mul, map_mul, Units.val_mul, apow_mul, apow_of_valuation_eq_one (valuation_gdet_of_mem_KO hg)]
  ring

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in

theorem exists_reindex_unit_val {C C₁ : Type} [Fintype C] [DecidableEq C] [Fintype C₁] [DecidableEq C₁]
    (τ eC : C ≃ C₁) :
    ∃ s : kˣ, ValuativeRel.valuation k (s : k) = 1 ∧ ∀ u : GL C k, ∃ u₁ : GL C₁ k, u₁.val = reindex τ eC u.val ∧
      (invT u₁).val = reindex τ eC (invT u).val ∧ gdet u₁ = s * gdet u := by
  refine ⟨Units.map (Int.castRingHom k).toMonoidHom (Equiv.Perm.sign (eC.trans τ.symm)), ?_, fun u => ?_⟩
  · rcases Int.units_eq_one_or (Equiv.Perm.sign (eC.trans τ.symm)) with h | h <;> rw [h] <;> simp
  refine ⟨⟨reindex τ eC u.val, reindex eC τ (u⁻¹).val, ?_, ?_⟩, rfl, rfl, Units.ext ?_⟩
  · simp [submatrix_mul_equiv]
  · simp [submatrix_mul_equiv]
  · exact det_reindex τ eC u.val

end

theorem bigZeta_eq_smul_smallZeta_change : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (a : ℕ) (A' : Type) [Fintype A'] [DecidableEq A'] (C : Type) [Fintype C] [DecidableEq C]
      (C₁ : Type) [Fintype C₁] [DecidableEq C₁] (eC : C ≃ C₁) (σ : Fin a ⊕ A' ≃ C) (σ₁ : Fin a ⊕ A' ≃ C₁)
      (gA : GL (Fin a) k) (gB : GL A' k) (c : GL C k), gA ∈ KO k (Fin a) → gB ∈ KO k A' → c ∈ KO k C →
      ∃ x : kˣ, ValuativeRel.valuation k (x : k) = 1 ∧ ∀ (ϖ : kˣ) (ν β : kˣ →* ℂˣ) (Ξ : Matrix (Fin a) C₁ k → ℂ) (Ψ : Matrix A' C₁ k → ℂ),
        bigP (haarVol (KO k (Fin a))) ϖ σ₁ ν β Ξ = smallP (haarVol (KO k A')) σ₁ ν (ν * β) Ψ →
        bigP (haarVol (KO k (Fin a))) ϖ σ ν β (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) =
          (ν x : ℂ) • smallP (haarVol (KO k A')) σ ν (ν * β) fun Y => Ψ (reindex (Equiv.refl _) eC (gB.val * Y * c.val)) := by
  intro k _ _ _ _ _ _ a A' _ _ C _ _ C₁ _ _ eC σ σ₁ gA gB c hA hB hC
  let τ : C ≃ C₁ := σ.symm.trans σ₁
  obtain ⟨s, hs1, hs⟩ := exists_reindex_unit_val (k := k) τ eC
  have vA := valuation_gdet_of_mem_KO hA
  have vB := valuation_gdet_of_mem_KO hB
  have vC := valuation_gdet_of_mem_KO hC
  have vs : ValuativeRel.valuation k ((s * gdet c : kˣ) : k) = 1 := by
    rw [Units.val_mul, map_mul, hs1, vC, mul_one]
  refine ⟨(gdet gA)⁻¹ * (s * gdet c) * gdet gB, ?_, fun ϖ ν β Ξ Ψ H => ?_⟩
  · rw [Units.val_mul, Units.val_mul, map_mul, map_mul, vs, vB, Units.val_inv_eq_inv_val, map_inv₀, vA]
    simp
  have n1 : (ν (gdet gA) : ℂ) ≠ 0 := Units.ne_zero _
  have n2 : (ν (s * gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  have n3 : (β (s * gdet c) : ℂ) ≠ 0 := Units.ne_zero _
  funext h
  obtain ⟨u, hu1, hu2, hu3⟩ := hs (h * c)
  have hd : gdet u = (s * gdet c) * gdet h := by rw [hu3, gdet_mul, mul_comm (gdet h), mul_assoc]
  have hX : reindex (Equiv.refl _) eC (X0 k σ * (invT (h * c)).val) = X0 k σ₁ * (invT u).val := by
    ext i j
    rw [frameMatrixFirstColumnBlock_mul_apply, hu2]
    simp [frameMatrixFirstColumnBlock_mul_apply, τ]
  have hY : reindex (Equiv.refl _) eC (Y0 k σ * h.val * c.val) = Y0 k σ₁ * u.val := by
    ext i j
    rw [frameMatrixSecondColumnBlock_mul_apply, hu1, Matrix.mul_assoc, ← Units.val_mul]
    simp only [reindex_apply, submatrix_apply, frameMatrixSecondColumnBlock_mul_apply]
    simp [τ]
  have H1 := congrFun H u
  have hF : (ν (gdet gA) : ℂ) * bigF (haarVol (KO k (Fin a))) ϖ ν
      (fun X => Ξ (reindex (Equiv.refl _) eC (gA.val * X * (invT c).val))) (X0 k σ * (invT h).val) =
      bigF (haarVol (KO k (Fin a))) ϖ ν Ξ (X0 k σ₁ * (invT u).val) := by
    unfold bigF
    rw [← shellSum_mul_left _ ϖ ν _ (fun g => Ξ (g * (X0 k σ₁ * (invT u).val))) hA, Fintype.card_congr eC, ← hX]
    congr 2
    funext g
    refine congrArg Ξ ?_
    have h5 : ∀ (M : Matrix (Fin a) (Fin a) k) (N : Matrix (Fin a) C k),
        M * reindex (Equiv.refl _) eC N = reindex (Equiv.refl _) eC (M * N) := fun M N => by
      ext i j
      simp [Matrix.mul_apply]
    simp only [h5, ← Matrix.mul_assoc gA.val g, map_mul, Units.val_mul]
    simp only [Matrix.mul_assoc]
  have hG := smallF_rows eC (haarVol (KO k A')) ν hB c.val Ψ (Y0 k σ * h.val)
  rw [bigZetaIntegral_eq, smallP, ← hF, ← hY, hd, ← hG] at H1
  rw [Pi.smul_apply, smul_eq_mul, bigZetaIntegral_eq, smallP]
  simp only [map_mul _ (s * gdet c), apow_mul (s * gdet c), Units.val_mul, MonoidHom.mul_apply,
    apow_of_valuation_eq_one vs, map_mul ν _ (gdet gB), map_mul ν (gdet gA)⁻¹, map_inv,
    Units.val_inv_eq_inv_val] at H1 ⊢
  generalize (ν (s * gdet c) : ℂ) = x2 at *
  generalize (β (s * gdet c) : ℂ) = x3 at *
  refine mul_left_cancel₀ (mul_ne_zero n1 n3) ?_
  refine Eq.trans (by ring) (H1.trans ?_)
  field_simp

end GlobalTheory.TopFlip.ZMatQ
