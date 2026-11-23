import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.StandardOrderExtendedBasisApplyLowBlock
import Development.AbelianVarietyTheory.Definitions.Foundations.GLintEqKOAndPrincEqKOne
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FourierJacobiAverage
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnipotentRadicalBasic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableOfMemSB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExDownExUpAndExUpExDown
import Development.AbelianVarietyTheory.Proofs.HeightProofs.SymplecticValTauCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardAdelicCharacterLocalComponentNeOne
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.MemLevelFunOfIsAutFun
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsHermitianAuxiliaryVectorSystemBesselVectors

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SplitWeil
open GlobalTheory.AdelicU (splitProj compFin splitEquiv splitEquivIn splitHom isCMExt_host)
open GlobalTheory.EmbChart (tensAt atPlace idem)
open GlobalTheory.StepData (LatFrame reGL)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocFrame

variable {D : D7} {v : HeightOneSpectrum (𝓞 D.host.F)}

section Chain

section Step

variable {V V₀ W W₀ : HSp D} {ρ : ℕ}

def xZeroQ (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) : Matrix (Fin W.rank) (Fin V.rank) D.host.E := dW.e * dV.qX

def xLastQ (dV : HypDec V V₀ (ρ + 1)) (dW : HypDec W W₀ ρ) (z' : Fin W₀.rank → D.host.E) :
    Matrix (Fin W.rank) (Fin V.rank) D.host.E :=
  (Matrix.of fun y (i : Fin (ρ + 1)) => besselAuxiliaryVectors dW z' i y) * dV.qX

theorem rat_xZeroQ (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) : rat (xZeroQ dV dW) = dV.extX W (xZero dW) := rat_mul _ _

theorem rat_xLastQ (dV : HypDec V V₀ (ρ + 1)) (dW : HypDec W W₀ ρ) (z' : Fin W₀.rank → D.host.E) :
    rat (xLastQ dV dW z') = dV.extX W (xLast dW z') := by
  rw [xLastQ, rat_mul, HypDec.extX_apply]
  refine congrArg₂ _ (funext fun y => funext fun i => ?_) rfl
  change incA D (besselAuxiliaryVectors dW z' i y) = Fin.snoc (α := fun _ => AE D) (dW.jX y) ((dW.j0 *ᵥ ratV z') y) i
  refine Fin.lastCases ?_ (fun i => ?_) i
  · rw [Fin.snoc_last, besselAuxiliaryVectors, Fin.val_last, if_neg (lt_irrefl _), if_pos rfl]
    exact congrFun (ratV_mulVec _ _) y
  · rw [Fin.snoc_castSucc, besselAuxiliaryVectors, Fin.val_castSucc, if_pos i.2, colN_fin]; rfl

theorem mul_qX_colN {m : ℕ} (d : HypDec V V₀ ρ) (M : Matrix (Fin m) (Fin ρ) D.host.E) (i : ℕ) :
    (M * d.qX) *ᵥ colN d.e i = colN M i := by
  by_cases hi : i < ρ
  · rw [colN_eq_mulVec _ hi, colN_eq_mulVec _ hi, mulVec_mulVec, Matrix.mul_assoc, qX_e, Matrix.mul_one]
  · rw [colN, colN, dif_neg hi, dif_neg hi, mulVec_zero]

variable {n n' : Type} {c c' : ℕ}

def IsFrameCompatibleAtPlace (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : Matrix (Fin W.rank) (Fin V.rank) D.host.E)
    (β' : LatFrame (Fv D.host.F v) (n' ⊕ Fin c') (Fin V.rank)) (β : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin W.rank)) : Prop :=
  ∀ (h' : 0 < c') (h : 0 < c), vec β (.inr ⟨0, h⟩) = x.map τ *ᵥ vec β' (.inr ⟨0, h'⟩)

end Step

structure ChainDec (Y X : ℕ → HSp D) (s : ℕ) where

  V₀ : ℕ → HSp D

  L : ℕ → HSp D

  ζ : ∀ i, Fin (L i).rank → D.host.E

  dE : ∀ i ρ, i + ρ = s → HypDec (Y (2 * i)) (V₀ i) ρ

  oE : ∀ i, i ≤ s → OrthDec (V₀ i) (X (2 * i)) (L i)

  dO : ∀ i ρ, i + ρ = s → HypDec (Y (2 * i + 1)) (X (2 * i + 1)) ρ

  line : ∀ i, i ≤ s → IsLineVec (L i) (ζ i)

variable {Y X : ℕ → HSp D} {s : ℕ} (C : ChainDec Y X s)

def ChainDec.z₀ (i ρ : ℕ) (h : i + ρ = s) : Fin (C.V₀ i).rank → D.host.E := vecB (C.oE i (Nat.le.intro h)) (C.ζ i)

def ChainDec.z (i ρ : ℕ) (h : i + ρ = s) : Fin (Y (2 * i)).rank → D.host.E := (C.dE i ρ h).i₀ *ᵥ C.z₀ i ρ h

variable (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v)
  {n : ℕ → Type} [∀ j, Fintype (n j)] [∀ j, DecidableEq (n j)]
  (γ : ∀ j, LatFrame (Fv D.host.F v) (n j) (Fin (X j).rank))

structure IsRule (β : ∀ j c, j + c = 2 * s + 1 → LatFrame (Fv D.host.F v) (n j ⊕ Fin c) (Fin (Y j).rank)) : Prop where

  even : ∀ i ρ (h : i + ρ = s), IsBesFrame ψ (C.dE i ρ h) (C.oE i (Nat.le.intro h)) (C.ζ i) (weilChar ψ hψ τ) τ
    (β (2 * i) (2 * ρ + 1) (by omega)) (γ (2 * i))

  odd : ∀ i ρ (h : i + ρ = s), IsFJFrameT ψ (C.dO i ρ h) (C.ζ i) (weilChar ψ hψ τ) τ
    (β (2 * i + 1) (2 * ρ) (by omega)) (γ (2 * i + 1))

  start : vec (β (2 * 0) (2 * s + 1) (by omega)) (.inr ⟨s, by omega⟩) = τ ∘ C.z 0 s (Nat.zero_add s)

  stepOdd : ∀ i ρ (h : i + ρ = s), IsFrameCompatibleAtPlace τ (xZeroQ (C.dE i ρ h) (C.dO i ρ h))
    (β (2 * i) (2 * ρ + 1) (by omega)) (β (2 * i + 1) (2 * ρ) (by omega))

  stepEven : ∀ i σ (h : i + (σ + 1) = s),
    IsFrameCompatibleAtPlace τ (xLastQ (srcDec (C.dO i (σ + 1) h)) (C.dE (i + 1) σ (by omega)) (C.z₀ (i + 1) σ (by omega)))
      (β (2 * i + 1) (2 * (σ + 1)) (by omega)) (β (2 * (i + 1)) (2 * σ + 1) (by omega))

theorem normScale_coef {θ : Fv D.host.F v} (p : ℕ) (a : D.host.E) (t₀ : Fv D.host.F v) {i : ℕ} (hi : i < p) :
    normScale θ (fun i => τ (coef p a i)) t₀ i = t₀ / θ ^ i := by
  rw [normScale, Finset.prod_congr rfl (g := fun _ => θ⁻¹) fun l hl => by
    rw [coef, if_pos (by have := Finset.mem_range.1 hl; omega), map_one, one_div], Finset.prod_const, Finset.card_range,
    inv_pow, div_eq_mul_inv]

theorem xZeroQ_first {V V₀ W W₀ : HSp D} {ρ : ℕ} (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (z) (h : 0 < ρ)
    (t : Fv D.host.F v) : (xZeroQ dV dW).map τ *ᵥ (t • (τ ∘ besselAuxiliaryVectors dV z 0)) = t • (τ ∘ fourierJacobiVectors dW 0) := by
  rw [mulVec_smul, ← comp_mulVec, besselAuxiliaryVectors, fourierJacobiVectors, if_pos h, if_pos h, xZeroQ, mul_qX_colN]

theorem xLastQ_first {V V₀ W W₀ : HSp D} {σ : ℕ} (dV : HypDec V V₀ (σ + 1)) (dW : HypDec W W₀ σ) (z) (t : Fv D.host.F v) :
    (xLastQ (srcDec dV) dW z).map τ *ᵥ ((t * τ D.host.xi0) • (τ ∘ fourierJacobiVectors dV 0)) = t • (τ ∘ besselAuxiliaryVectors dW z 0) := by
  have h : τ D.host.xi0 • (τ ∘ fourierJacobiVectors dV 0) = τ ∘ fourierJacobiVectors (srcDec dV) 0 := by
    rw [fourierJacobiVectors_source, if_pos σ.succ_pos]
    exact funext fun y => (map_mul τ _ _).symm
  rw [mul_smul, h, mulVec_smul, ← comp_mulVec, fourierJacobiVectors, if_pos σ.succ_pos, xLastQ, mul_qX_colN, colN, dif_pos σ.succ_pos]
  rfl

theorem exists_isRule : ∃ β, IsRule C ψ hψ τ γ β := by
  have hx : τ D.host.xi0 ≠ 0 := (map_ne_zero τ).2 cmHost_imaginaryGenerator_ne_zero
  choose βE hE hE' using fun i ρ (h : i + ρ = s) => exists_isBesFrame hψ (C.dE i ρ h) (C.oE i (Nat.le.intro h))
    (C.line i (Nat.le.intro h)) τ hx (γ (2 * i)) (pow_ne_zero ρ hx)
  choose βO hO hO' using fun i ρ (h : i + ρ = s) => exists_isFJFrameT hψ (C.dO i ρ h)
    (C.line i (Nat.le.intro h)) τ hx (γ (2 * i + 1)) (pow_ne_zero ρ hx)
  have glue (j c : ℕ) (h : j + c = 2 * s + 1) : ∃ b : LatFrame (Fv D.host.F v) (n j ⊕ Fin c) (Fin (Y j).rank),
      (∀ i ρ h', j = 2 * i → HEq b (βE i ρ h')) ∧ ∀ i ρ h', j = 2 * i + 1 → HEq b (βO i ρ h') := by
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ + 1 := ⟨s - i, by omega⟩
      refine ⟨βE i ρ (by omega), fun i' ρ' h' e => ?_, fun i' ρ' h' e => by omega⟩
      obtain rfl : i = i' := by omega
      obtain rfl : ρ = ρ' := by omega
      rfl
    · obtain ⟨ρ, rfl⟩ : ∃ ρ, c = 2 * ρ := ⟨s - i, by omega⟩
      refine ⟨βO i ρ (by omega), fun i' ρ' h' e => by omega, fun i' ρ' h' e => ?_⟩
      obtain rfl : i = i' := by omega
      obtain rfl : ρ = ρ' := by omega
      rfl
  choose β h1 h2 using glue
  have e1 (i ρ h h') : β (2 * i) (2 * ρ + 1) h = βE i ρ h' := eq_of_heq (h1 _ _ h i ρ h' rfl)
  have e2 (i ρ h h') : β (2 * i + 1) (2 * ρ) h = βO i ρ h' := eq_of_heq (h2 _ _ h i ρ h' rfl)
  refine ⟨β, fun i ρ h => e1 i ρ _ h ▸ hE i ρ h, fun i ρ h => e2 i ρ _ h ▸ hO i ρ h, ?_, fun i ρ h _ h0 => ?_,
    fun i σ h _ _ => ?_⟩
  · rw [e1 0 s _ (Nat.zero_add s), (hE' 0 s _).2, normScale_coef τ _ _ _ s.lt_succ_self, div_self (pow_ne_zero _ hx),
      one_smul, besselAuxiliaryVectors, if_neg (lt_irrefl _), if_pos rfl]
    rfl
  · rw [e1 i ρ _ h, e2 i ρ _ h, (hE' i ρ h).2, (hO' i ρ h).2, normScale_coef τ _ _ _ ρ.succ_pos,
      normScale_coef τ _ _ _ (show 0 < ρ by omega), xZeroQ_first τ _ _ _ (by omega)]
  · rw [e1 (i + 1) σ _ (by omega), e2 i _ _ h, (hE' _ _ _).2, (hO' _ _ h).2, normScale_coef τ _ _ _ σ.succ_pos,
      normScale_coef τ _ _ _ σ.succ_pos, pow_zero, div_one, div_one, pow_succ, xLastQ_first]
    rfl

variable {C ψ hψ τ γ} {β : ∀ j c, j + c = 2 * s + 1 → LatFrame (Fv D.host.F v) (n j ⊕ Fin c) (Fin (Y j).rank)}

theorem IsRule.source (H : IsRule C ψ hψ τ γ β) (i ρ : ℕ) (h : i + ρ = s)
    (hz : hQ (C.L i) (C.ζ i) (C.ζ i) = hQ (C.L (i + 1)) (C.ζ (i + 1)) (C.ζ (i + 1))) :
    IsFJFrameS ψ (srcDec (C.dO i ρ h)) (C.ζ (i + 1)) (weilChar ψ hψ τ) τ (β (2 * i + 1) (2 * ρ) (by omega)) (γ (2 * i + 1)) :=
  (isFJFrameS_srcDec_iff _ hz _).2 (H.odd i ρ h)

theorem vec_ne_zero {k ι Z : Type} [Field k] [Fintype ι] [DecidableEq ι] [Fintype Z] [DecidableEq Z] (b : LatFrame k ι Z)
    (i : ι) : vec b i ≠ 0 := fun e => by
  have h1 := congrFun (congrFun (rows_mul_cols b) i) i
  simp [Matrix.mul_apply, cols_apply, e] at h1

theorem IsRule.isScaled_even (H : IsRule C ψ hψ τ γ β) (h1 : weilChar ψ hψ τ ≠ 1) (i ρ : ℕ) (h : i + ρ = s) :
    IsScaled _ _ τ ((C.dE i ρ h).i₀ * (C.oE i (Nat.le.intro h)).iA) (besselAuxiliaryVectors (C.dE i ρ h) (C.z₀ i ρ h)) (γ (2 * i))
      (β (2 * i) (2 * ρ + 1) (by omega))
      (normScale (τ D.host.xi0) (fun l => τ (coef (ρ + 1) (-hQ (C.L i) (C.ζ i) (C.ζ i)) l)) (τ D.host.xi0 ^ ρ)) := by
  have hx : τ D.host.xi0 ≠ 0 := (map_ne_zero τ).2 cmHost_imaginaryGenerator_ne_zero
  induction i generalizing ρ with
  | zero =>
    obtain rfl : ρ = s := by omega
    obtain ⟨t₀, ht⟩ := (H.even 0 ρ h).exists_scale hψ _ _ h1 (C.line 0 ρ.zero_le)
    have h2 := ht.2 ⟨ρ, by omega⟩
    have h3 := vec_ne_zero (β (2 * 0) (2 * ρ + 1) (by omega)) (.inr ⟨ρ, by omega⟩)
    rw [normScale_coef τ _ _ _ ρ.lt_succ_self, besselAuxiliaryVectors, if_neg (lt_irrefl _), if_pos rfl, H.start] at h2
    rw [H.start] at h3
    obtain rfl : t₀ = τ D.host.xi0 ^ ρ := (div_eq_one_iff_eq (pow_ne_zero _ hx)).1
      (smul_left_injective _ h3 (h2.symm.trans (one_smul _ _).symm))
    exact ht
  | succ i ih =>
    have h' : i + (ρ + 1) = s := by omega
    obtain ⟨t₀, ht⟩ := (H.even (i + 1) ρ h).exists_scale hψ _ _ h1 (C.line _ (by omega))
    have h2 := H.stepOdd i _ h' (by omega) (by omega)
    have h3 := H.stepEven i _ h' (by omega) (by omega)
    have h4 := vec_ne_zero (β (2 * (i + 1)) (2 * ρ + 1) (by omega)) (.inr ⟨0, by omega⟩)
    rw [(ih _ h').2, normScale_coef τ _ _ _ (Nat.succ_pos _), xZeroQ_first τ _ _ _ ρ.succ_pos] at h2
    rw [h2, pow_zero, div_one, pow_succ, xLastQ_first, ht.2, normScale_coef τ _ _ _ ρ.succ_pos, pow_zero, div_one] at h3
    rw [ht.2] at h4
    obtain rfl : t₀ = τ D.host.xi0 ^ ρ := smul_left_injective _ (right_ne_zero_of_smul h4) h3
    exact ht

theorem IsRule.middle (H : IsRule C ψ hψ τ γ β) (h1 : weilChar ψ hψ τ ≠ 1) (i ρ : ℕ) (h : i + ρ = s) :
    vec (β (2 * i) (2 * ρ + 1) (by omega)) (.inr ⟨ρ, by omega⟩) = τ ∘ C.z i ρ h := by
  rw [(H.isScaled_even h1 i ρ h).2, normScale_coef τ _ _ _ ρ.lt_succ_self,
    div_self (pow_ne_zero _ ((map_ne_zero τ).2 cmHost_imaginaryGenerator_ne_zero)), one_smul, besselAuxiliaryVectors, if_neg (lt_irrefl _), if_pos rfl]
  rfl

end Chain

section Periods

open GlobalTheory.RootEx (N colE rowE IsNEquiv)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (schT schM)

variable (V : HSp D) {S : Finset (HeightOneSpectrum (𝓞 D.host.F))} (τ : ∀ v : S, D.host.E →ₐ[D.host.F] Fv D.host.F v)

def locGLs {ι : Type} [Fintype ι] [DecidableEq ι] (β : ∀ v : S, LatFrame (Fv D.host.F v) ι (Fin V.rank)) :
    (∀ v : S, GL ι (Fv D.host.F v)) →* GA D V :=
  MonoidHom.noncommPiCoprod (fun v : S => locGL V (τ v) (β v)) fun _ _ h x y =>
    commute_locGL_locGL V _ _ (fun e => h (Subtype.ext e)) _ _ x y

theorem locGLs_mulSingle [DecidableEq S] {ι : Type} [Fintype ι] [DecidableEq ι]
    (β : ∀ v : S, LatFrame (Fv D.host.F v) ι (Fin V.rank)) (v : S) (g : GL ι (Fv D.host.F v)) :
    locGLs V τ β (Pi.mulSingle v g) = locGL V (τ v) (β v) g :=
  MonoidHom.noncommPiCoprod_mulSingle (fun v : S => locGL V (τ v) (β v)) v g

theorem locGLs_mem_GfC {ι : Type} [Fintype ι] [DecidableEq ι] (β : ∀ v : S, LatFrame (Fv D.host.F v) ι (Fin V.rank))
    (g : ∀ v : S, GL ι (Fv D.host.F v)) : locGLs V τ β g ∈ GfC V := by
  have h : (locGLs V τ β).range ≤ GfC V :=
    (MonoidHom.noncommPiCoprod_range (fun v : S => locGL V (τ v) (β v))).trans_le
      (iSup_le fun v _ ⟨x, e⟩ => e ▸ locGL_mem_GfC V (τ v) (β v) x)
  exact h ⟨g, rfl⟩

variable {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (β : ∀ v : S, LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank))
  (ν : ∀ v : S, Measure (Fv D.host.F v))

def posAt (p q : S → ℕ) (l : (GA D V → ℂ) → ℂ) : (GA D V → ℂ) → ℂ :=
  exList ν (fun v => locReg V (τ v) (β v)) p q (Finset.univ : Finset S).toList l

def pos1 (l : (GA D V → ℂ) → ℂ) : (GA D V → ℂ) → ℂ := posAt V τ β ν (fun _ => c / 2 + 1) (fun _ => 1) l

theorem posAt_self (p : S → ℕ) (l : (GA D V → ℂ) → ℂ) : posAt V τ β ν p p l = l := exList_self _ _ _ _ _

theorem positionOne_of_unique [Unique S] (l : (GA D V → ℂ) → ℂ) :
    pos1 V τ β ν l = downIter (ν default) (locReg V (τ default) (β default)) 1 (c / 2) l := by
  rw [pos1, posAt, Finset.univ_unique, Finset.toList_singleton]
  exact exTo_of_ge _ _ (Nat.le_add_left 1 _) l

theorem posAt_of_isEmpty [IsEmpty S] (p q : S → ℕ) (l : (GA D V → ℂ) → ℂ) : posAt V τ β ν p q l = l := by
  rw [posAt, Finset.univ_eq_empty, Finset.toList_empty]; rfl

variable {V} {U : Submodule ℂ (GA D V → ℂ)} (hU : IsFinStable V U)

theorem posAt_coe (p q : S → ℕ) (l : (GA D V → ℂ) → ℂ) (F : U) : posAt V τ β ν p q l F =
    exList ν (fun v => locRepOn V (τ v) (β v) U hU) p q (Finset.univ : Finset S).toList (fun F : U => l F) F :=
  (exList_law ν _ (fun v => locRepOn V (τ v) (β v) U hU) (T := Subtype.val) (fun _ _ _ => rfl)
    (fun _ => (one_mul _).symm) p q _ F).trans (one_mul _)

include hU in

theorem posAt_congr (p q : S → ℕ) {l l' : (GA D V → ℂ) → ℂ} (h : ∀ F ∈ U, l F = l' F) {F : GA D V → ℂ} (hF : F ∈ U) :
    posAt V τ β ν p q l F = posAt V τ β ν p q l' F := by
  rw [posAt_coe τ β ν hU p q l ⟨F, hF⟩, posAt_coe τ β ν hU p q l' ⟨F, hF⟩, funext fun F : U => h F F.2]

theorem posAt_rTrans (p q : S → ℕ) (l : (GA D V → ℂ) → ℂ) {x : GA D V}
    (hx : ∀ v : S, GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v x = 1) (F : GA D V → ℂ) :
    posAt V τ β ν p q l (rTrans x F) = posAt V τ β ν p q (fun F => l (rTrans x F)) F :=
  (exList_law ν _ (fun v => locReg V (τ v) (β v)) (T := rTrans x) (fun v g F => funext fun y => by
    change F (y * x * _) = F (y * _ * x)
    rw [mul_assoc, mul_assoc, (commute_locGL V (τ v) (β v) g (hx v)).eq]) (fun _ => (one_mul _).symm) p q _ F).trans
    (one_mul _)

theorem posAt_isNEquiv [∀ v, (ν v).IsAddHaarMeasure] (hU' : U ≤ levelFun V) {ψv : ∀ v : S, AddChar (Fv D.host.F v) Circle}
    (hψ : ∀ v, Continuous (ψv v)) (hψ1 : ∀ v, ψv v ≠ 1) {p q : S → ℕ} (hp : ∀ v, 1 ≤ p v ∧ p v ≤ c)
    (hq : ∀ v, 1 ≤ q v ∧ q v ≤ c) {l : (GA D V → ℂ) → ℂ} (l₀ : U →ₗ[ℂ] ℂ) (h₀ : ∀ F : U, l F = l₀ F)
    (hl : ∀ v, IsNEquiv (ψv v) (p v) (locRepOn V (τ v) (β v) U hU) l₀) :
    ∃ l₁ : U →ₗ[ℂ] ℂ, (∀ F : U, posAt V τ β ν p q l F = l₁ F) ∧
      ∀ v, IsNEquiv (ψv v) (q v) (locRepOn V (τ v) (β v) U hU) l₁ := by
  classical
  obtain ⟨l₁, e, h⟩ := exList_isNEquiv ν hψ hψ1 (fun v => isSmoothRep_locRepOn V (τ v) (β v) hU hU')
    (fun u v huv g h F => Subtype.ext (funext fun y => by
      change F.1 (y * _ * _) = F.1 (y * _ * _)
      rw [mul_assoc, mul_assoc, (commute_locGL_locGL V _ _ (fun e => huv (Subtype.ext e)) _ _ g h).eq])) hp hq l₀ hl
    (Finset.nodup_toList Finset.univ)
  exact ⟨l₁, fun F => by rw [posAt_coe τ β ν hU, funext h₀, e], fun v => by simpa using h v⟩

section Bes

variable (ψ : AddChar (AF D.host.F) ℂ) {V₀ A L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L)
  (ζ : Fin L.rank → D.host.E) (μ : Measure (GA D A)) (𝓕 : Set (GA D A)) (νN : Measure (flagN d)) (𝓝 : Set (flagN d))

def besPos (q : S → ℕ) (φ : GA D A → ℂ) : (GA D V → ℂ) → ℂ :=
  posAt V τ β ν (fun _ => ρ + 1) q (besPer ψ 1 d o ζ μ 𝓕 νN 𝓝 φ)

def besPos1 (φ : GA D A → ℂ) : (GA D V → ℂ) → ℂ := besPos τ β ν ψ d o ζ μ 𝓕 νN 𝓝 (fun _ => 1) φ

theorem besPos1_eq (hc : c = 2 * ρ + 1) (φ : GA D A → ℂ) :
    besPos1 τ β ν ψ d o ζ μ 𝓕 νN 𝓝 φ = pos1 V τ β ν (besPer ψ 1 d o ζ μ 𝓕 νN 𝓝 φ) := by
  rw [pos1, show c / 2 = ρ by omega]; rfl

end Bes

section FJ

variable (V) in

def IsSchAt (ψw : AddChar (Fv D.host.F v) Circle) (τw : D.host.E →ₐ[D.host.F] Fv D.host.F v)
    (b : LatFrame (Fv D.host.F v) (n ⊕ Fin c) (Fin V.rank)) (ρ : ℕ) {Z : Type} (J : GA D V → (Z → ℂ) → Z → ℂ)
    (T : SB (n → Fv D.host.F v) →ₗ[ℂ] Z → ℂ) : Prop :=
  (∀ (β₀ : n → Fv D.host.F v) (Φ₀ Φ₁ : SB (n → Fv D.host.F v)), Φ₁.1 = schT β₀ Φ₀.1 →
    T Φ₁ = J (locGL V τw b (colE c (ρ + 1) β₀)) (T Φ₀)) ∧
  ∀ (u : n → Fv D.host.F v) (Φ₀ Φ₁ : SB (n → Fv D.host.F v)), Φ₁.1 = schM ψw u Φ₀.1 →
    T Φ₁ = J (locGL V τw b (rowE c ρ u)) (T Φ₀)

variable (ψv : ∀ v : S, AddChar (Fv D.host.F v) Circle)

open Classical in

def IsSchModel (ρ : ℕ) {Z : Type} (J : GA D V → (Z → ℂ) → Z → ℂ)
    (T : MultilinearMap ℂ (fun v : S => SB (n → Fv D.host.F v)) (Z → ℂ)) : Prop :=
  ∀ Φ (v : S), IsSchAt V (ψv v) (τ v) (β v) ρ J (T.toLinearMap Φ v)

def fjInt (ρ : ℕ) (b : (GA D V → ℂ) → ℂ) (F : GA D V → ℂ) (Φ : ∀ v : S, SB (n → Fv D.host.F v))
    (x : ∀ v : S, n → Fv D.host.F v) : ℂ :=
  (∏ v, (Φ v).1 (x v)) * b (rTrans (locGLs V τ β fun v => colE c (ρ + 1) (x v)) F)

variable (U) in

def IsFJBase (ρ : ℕ) (fj : (GA D V → ℂ) → (∀ v : S, SB (n → Fv D.host.F v)) → ℂ) (b : (GA D V → ℂ) → ℂ) : Prop :=
  (∀ v : S, ∀ g ∈ N _ n c (ρ + 1), ∀ F ∈ U,
    b (rTrans (locGL V (τ v) (β v) g) F) = (ψv v (GlobalTheory.RootEx.simpleSum g) : ℂ) * b F) ∧
  ∀ F ∈ U, ∀ Φ, Integrable (fjInt τ β ρ b F Φ) (Measure.pi fun v => Measure.pi fun _ => ν v) ∧
    fj F Φ = ∫ x, fjInt τ β ρ b F Φ x ∂(Measure.pi fun v => Measure.pi fun _ => ν v)

variable (U) in

def IsFJPos (ρ : ℕ) (q : S → ℕ) (fj : (GA D V → ℂ) → (∀ v : S, SB (n → Fv D.host.F v)) → ℂ) (b' : (GA D V → ℂ) → ℂ) :
    Prop :=
  ∃ b, IsFJBase τ β ν U ψv ρ fj b ∧ ∀ F ∈ U, b' F = posAt V τ β ν (fun _ => ρ + 1) q b F

variable (U) in

def IsPos1 (ρ : ℕ) (fj : (GA D V → ℂ) → (∀ v : S, SB (n → Fv D.host.F v)) → ℂ) (b₁ : (GA D V → ℂ) → ℂ) : Prop :=
  IsFJPos τ β ν U ψv ρ (fun _ => 1) fj b₁

variable (ψ : AddChar (AF D.host.F) ℂ) {V₀ L : HSp D} {ρ : ℕ} (d : HypDec V V₀ ρ) (ζ : Fin L.rank → D.host.E)

def jacLineT : GA D V → (WO L V₀ → ℂ) → WO L V₀ → ℂ := jacT ψ d L (yZero L ρ ζ)

def jacLineS (x : GA D V) (f : WO V₀ L → ℂ) : WO V₀ L → ℂ := star (jacS ψ d L (zEll L ρ ζ) x (star f))

variable (μ : Measure (GA D V₀)) (𝓕 : Set (GA D V₀)) (νN : Measure (flagN d)) (𝓝 : Set (flagN d))

variable (U) in

def IsFJPosT (omz : Om L V₀) (T : MultilinearMap ℂ (fun v : S => SB (n → Fv D.host.F v)) (WO L V₀ → ℂ)) (q : S → ℕ)
    (φ : GA D V₀ → ℂ) (b' : (GA D V → ℂ) → ℂ) : Prop :=
  IsFJPos τ β ν U ψv ρ q (fun F Φ => fjPer ψ d ζ omz μ 𝓕 νN 𝓝 φ F (T Φ)) b'

variable (U) in

def IsFJPosS (omz : Om V₀ L) (T : MultilinearMap ℂ (fun v : S => SB (n → Fv D.host.F v)) (WO V₀ L → ℂ)) (q : S → ℕ)
    (φ : GA D V₀ → ℂ) (b' : (GA D V → ℂ) → ℂ) : Prop :=
  IsFJPos τ β ν U ψv ρ q (fun F Φ => fjSrc ψ d ζ omz μ 𝓕 νN 𝓝 φ F (star (T Φ))) b'

end FJ

end Periods

section Examples

theorem locChar_ne_one {F : Type} [Field F] [NumberField F] {ψ : AddChar (AF F) ℂ} (hψ : ∀ x, ‖ψ x‖ = 1)
    {v : HeightOneSpectrum (𝓞 F)} (h : ∃ y, psiV F ψ v y ≠ 1) {a : Fv F v} (ha : a ≠ 0) : locChar ψ hψ a ≠ 1 := fun e => by
  obtain ⟨y, hy⟩ := h
  have h1 := coe_locChar ψ hψ a (y / a)
  rw [e, mul_div_cancel₀ _ ha] at h1
  exact hy h1.symm

theorem weilChar_spec {ψ : AddChar (AF D.host.F) ℂ} (h : IsStdChar D ψ (-1)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) :
    Continuous (weilChar ψ h.1.2.1 τ) ∧ weilChar ψ h.1.2.1 τ ≠ 1 :=
  ⟨continuous_locChar h.1.1 _ _, locChar_ne_one _ (GlobalTheory.StdCharLocal.psiV_ne_one D ψ h v) ((map_ne_zero τ).2 cmHost_imaginaryGenerator_ne_zero)⟩

theorem weilChar_piW (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (x : AE D) :
    (weilChar ψ hψ τ (piW τ x) : ℂ) = psiE ψ (idem τ * (incA D D.host.xi0 * x)) := by
  have h1 : piW τ (idem τ) = 1 := by
    change splitProj τ (compFin _ _ v (idem τ)) = 1
    rw [GlobalTheory.EmbChart.compFin_idem, GlobalTheory.AdelicU.splitProj_splitIdem]
  have h2 : piW τ (cA D (idem τ)) = 0 := by
    change splitProj τ (compFin _ _ v (cA D (idem τ))) = 0
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.compFin_tensAt, map_sub, map_one, GlobalTheory.AdelicU.splitProj_splitIdem, sub_self]
  have h3 : idem τ ∈ locIdeal D v := tensAt_mem _
  rw [psiE, trace_of_mem τ (Ideal.mul_mem_right _ _ h3), map_mul (cA D), map_mul (piW τ),
    map_mul (piW τ) (cA D _), h1, h2, zero_mul, add_zero, one_mul, map_mul, piW_incA]
  rfl

def hypDecZero (S : HSp D) : HypDec S S 0 where
  e := 0
  e' := 0
  i₀ := 1
  ee := Subsingleton.elim _ _
  e'e' := Subsingleton.elim _ _
  e'e := Subsingleton.elim _ _
  iso := by rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  i₀e := Matrix.mul_zero _
  i₀e' := Matrix.mul_zero _
  rank_add := rfl

def orthDecZero (S : HSp D) : OrthDec S (diagSp D 0 ![] 0 0) S where
  iA := 0
  iB := 1
  isoA := Matrix.ext fun i => i.elim0
  isoB := by rw [conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
  orth := Matrix.mul_zero _
  rank_add := Nat.zero_add _

def exY (D : D7) : ℕ → HSp D
  | 0 | 1 => diagSp D 3 ![false, false, true] 2 1
  | 2 => diagSp D 2 ![false, true] 1 1
  | _ => diagSp D 1 ![false] 1 0

def exX (D : D7) : ℕ → HSp D
  | 0 => diagSp D 0 ![] 0 0
  | 2 => diagSp D 1 ![true] 0 1
  | _ => diagSp D 1 ![false] 1 0

def exChain (D : D7) : ChainDec (exY D) (exX D) 1 where
  V₀ i := match i with
    | 0 => diagSp D 1 ![false] 1 0
    | _ => diagSp D 2 ![false, true] 1 1
  L _ := diagSp D 1 ![false] 1 0
  ζ _ _ := 1
  dE i ρ h := match i, ρ, h with
    | 0, 1, _ => hypDecThree D
    | 1, 0, _ => hypDecZero _
    | 1, _ + 1, h => absurd h (by omega)
    | _ + 2, _, h => absurd h (by omega)
  oE i h := match i, h with
    | 0, _ => orthDecZero _
    | 1, _ => (orthDecPlane D).symm
  dO i ρ h := match i, ρ, h with
    | 0, 1, _ => hypDecThree D
    | 1, 0, _ => hypDecZero _
    | 1, _ + 1, h => absurd h (by omega)
    | _ + 2, _, h => absurd h (by omega)
  line _ _ := ⟨rfl, by
    rw [diagSp_gram]
    change ∑ i : Fin 1, star (1 : D.host.E) * ∑ j : Fin 1, Matrix.diagonal (fun i => Examples₂.sgn (![false] i)) i j * 1 ≠ 0
    simp [Examples₂.sgn]⟩

example (ψ : AddChar (AF D.host.F) ℂ) (hψ : ∀ x, ‖ψ x‖ = 1) :
    ∃ (v : HeightOneSpectrum (𝓞 D.host.F)) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v),
      ∃ β, IsRule (n := fun j => Fin (exX D j).rank) (exChain D) ψ hψ τ (fun _ => LatFrame.refl _ _) β := by
  obtain ⟨v, ⟨τ⟩⟩ := GlobalTheory.AdelicU.exists_split_place (isCMExt_host D)
  exact ⟨v, τ, exists_isRule _ _ _ _ _⟩

example (a : D.host.E) : (List.range 4).map (coef 3 (-a)) = [1, 1, -a, -1] := by simp [coef, List.range_succ]

example (a : D.host.E) : (List.range 3).map (normScale 1 (coef 2 (-a)) 1) = [1, 1, -a] := by
  simp [normScale, coef, List.range_succ, Finset.prod_range_succ]

example (V : HSp D) (τ : D.host.E →ₐ[D.host.F] Fv D.host.F v) (g : GL (Fin V.rank) (Fv D.host.F v)) :
    (mt V (locGL V τ (LatFrame.refl _ _) g)).map (piW τ) = g.val := by
  rw [map_piW_locGL, conj_val]
  change (1 : Matrix _ _ _) * g.val * (1 : Matrix _ _ _) = _
  rw [Matrix.one_mul, Matrix.mul_one]

example (V : HSp D) {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} (U : Submodule ℂ (GA D V → ℂ)) (ρ : ℕ) (τ β ν ψv)
    (b : (GA D V → ℂ) → ℂ) : IsFJBase (S := ∅) (n := n) (c := c) τ β ν U ψv ρ (fun F _ => b F) b := by
  refine ⟨fun v => isEmptyElim v, fun F _ Φ => ?_⟩
  have h : fjInt τ β ρ b F Φ = fun _ => b F := funext fun x => by
    rw [fjInt, Finset.prod_of_isEmpty, one_mul, Subsingleton.elim (fun v => GlobalTheory.RootEx.colE c (ρ + 1) (x v)) 1, map_one]
    exact congrArg b (funext fun y => congrArg F (mul_one y))
  rw [h, Measure.pi_of_empty]
  exact ⟨integrable_const _, by simp⟩

end Examples

end GlobalTheory.LocFrame

end
