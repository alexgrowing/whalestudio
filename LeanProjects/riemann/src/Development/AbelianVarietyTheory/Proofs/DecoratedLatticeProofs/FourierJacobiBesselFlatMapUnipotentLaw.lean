import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

namespace GlobalTheory.FlatFBUnip

theorem det_of_mem_N {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} {g : GL (n ⊕ Fin c) k}
    (hg : g ∈ N k n c p) : Matrix.GeneralLinearGroup.det g = 1 := by
  refine Subgroup.closure_induction (p := fun g _ => Matrix.GeneralLinearGroup.det g = 1) ?_ ?_ ?_ ?_ hg
  · intro g hg
    have hb : (g.val).BlockTriangular (lev p) := fun r s h => by
      rw [hg r s h.le, Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb.det, Units.val_one]
    refine Finset.prod_eq_one fun a _ => ?_
    have : g.val.toSquareBlock (lev p) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
      rw [hg i j (by rw [hi, hj])]
      by_cases h : i = j
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]; intro e; exact h (congrArg Subtype.val e)
    rw [this, Matrix.det_one]
  · exact map_one _
  · intro x y _ _ hx hy; rw [map_mul, hx, hy, one_mul]
  · intro x _ hx; rw [map_inv, hx, inv_one]

end GlobalTheory.FlatFBUnip

namespace GlobalTheory.FlatFBUnip

theorem unip_law : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ u : GL (Fin c) k, embA n u ∈ N k n c (σ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → flatFB st (Tm Φ') = (ψk (-simpleSum (embA n u)) : ℂ) • flatFB st (Tm Φ) := by
  intro D hFL hOm k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ hC hB Tm hTm u hu Φ Φ' hΦ
  obtain ⟨v, ε, hv, hε⟩ := p.split.2.2
  have hF := (hFL ψ (· = v)).2 σ J B st
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B.V (n ⊕ Fin c) FV).1 (embA n u)
  have hgN : g ∈ flagN B.d := GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal D k p σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg
  have hgP : g ∈ GlobalTheory.FinPl.grpAt B.V (· = v) := by
    have hS := hg.1
    obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hv
    rw [SuppAt, hε] at hS
    simp only [← GlobalTheory.FinPl.Model.mem_idAt_iff] at hS
    rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    intro i j
    have h1 := hS i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
    have : Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D (· = v)) ((1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D)) i j) =
        (1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D (· = v))) i j := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this] at h1
    exact h1
  have hdet : Matrix.GeneralLinearGroup.det (embA n u) = 1 := det_of_mem_N hu
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std
  obtain ⟨μS, hμS⟩ := hcomp st.χV
  obtain ⟨μT, hμT⟩ := hcomp st.χW
  have h1 : p.IsLoc FW (1 : GA D J.W) 1 := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp [mt_one]
    · rw [mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, FW.βγ]
  have hΦ'' : Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin (c + 1)) k)) : ℂˣ) : ℂ) •
      om μS⁻¹ 1 (embA n u) Φ.1 := by
    funext t
    simp only [om, hdet, map_one, Units.val_one, nabs, Real.one_rpow, inv_one, one_mul, one_smul, Pi.smul_apply,
      Matrix.mul_one, hΦ t]
    norm_num
  have hω := hOm k p ψ J.W B.V st.χV st.χW st.om st.weil μS μT hμS hμT (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) FW FV Tm hTm
    1 1 g (embA n u) h1 hg Φ Φ' hΦ''
  have heq := hF.equiv (Tm Φ) (hTm.theta Φ) g hgN hgP 1 (one_mem _)
  rw [map_one, mul_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one] at heq
  rw [← hω, heq, GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum D k p ψ ψk hχ σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg]
  simp only [Module.End.one_apply]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

end GlobalTheory.FlatFBUnip
