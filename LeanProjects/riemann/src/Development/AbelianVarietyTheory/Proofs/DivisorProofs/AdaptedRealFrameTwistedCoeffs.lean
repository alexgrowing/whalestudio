import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndLineInf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OffPartLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchOperatorCompactUnitaryWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KEqOnId
import Development.AbelianVarietyTheory.Definitions.Divisors.GenSubHwOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLiftCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAThetaLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowPartInvariantSubmoduleEquivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviLiftMaximalCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialFockSpaceStableArchimedeanMaximalCompaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerOfCoef
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeadMinorMulDiagonal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherRest
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ImportsFurtherSide
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwCoefFrame

open Matrix Formalism.BasicNotions.TH GlobalTheory.TwCoef GlobalTheory.RealLift GlobalTheory.RealLift.OneParam
open GlobalTheory.ThK.RealK (herm)

section Lin

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

def hf (M : Matrix n n ℂ) (u v : n → ℂ) : ℂ := u ⬝ᵥ (M *ᵥ star v)

theorem star_mulVec' (A : Matrix m n ℂ) (u : n → ℂ) : star (A *ᵥ u) = A.map star *ᵥ star u := by
  ext i; simp [Matrix.mulVec, dotProduct, star_sum]

theorem dot_mulVec_left (A : Matrix m n ℂ) (u : n → ℂ) (w : m → ℂ) : (A *ᵥ u) ⬝ᵥ w = u ⬝ᵥ (Aᵀ *ᵥ w) := by
  rw [Matrix.mulVec_transpose, dotProduct_comm, Matrix.dotProduct_mulVec, dotProduct_comm]

theorem hf_mulVec (M : Matrix m m ℂ) (A : Matrix m n ℂ) (u v : n → ℂ) :
    hf M (A *ᵥ u) (A *ᵥ v) = hf (Aᵀ * M * A.map star) u v := by
  simp only [hf]
  rw [dot_mulVec_left, star_mulVec', Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]

theorem hf_add_left (M : Matrix n n ℂ) (u u' v : n → ℂ) : hf M (u + u') v = hf M u v + hf M u' v := add_dotProduct _ _ _

theorem hf_sub_left (M : Matrix n n ℂ) (u u' v : n → ℂ) : hf M (u - u') v = hf M u v - hf M u' v := sub_dotProduct _ _ _

theorem hf_smul_left (M : Matrix n n ℂ) (c : ℂ) (u v : n → ℂ) : hf M (c • u) v = c * hf M u v := smul_dotProduct _ _ _

theorem hf_add_right (M : Matrix n n ℂ) (u v v' : n → ℂ) : hf M u (v + v') = hf M u v + hf M u v' := by
  first
  | exact @_root_.GlobalTheory.SpectralLemmaThird.main
  | exact _root_.GlobalTheory.SpectralLemmaThird.main
  | (apply _root_.GlobalTheory.SpectralLemmaThird.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpectralLemmaThird.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpectralLemmaThird.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpectralLemmaThird.main ..)

theorem hf_sub_right (M : Matrix n n ℂ) (u v v' : n → ℂ) : hf M u (v - v') = hf M u v - hf M u v' := by
  first
  | exact @_root_.GlobalTheory.SpectralLemmaFourth.main
  | exact _root_.GlobalTheory.SpectralLemmaFourth.main
  | (apply _root_.GlobalTheory.SpectralLemmaFourth.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SpectralLemmaFourth.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SpectralLemmaFourth.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SpectralLemmaFourth.main ..)

theorem hf_smul_right (M : Matrix n n ℂ) (c : ℂ) (u v : n → ℂ) : hf M u (c • v) = star c * hf M u v := by
  simp only [hf, star_smul, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hf_conj {M : Matrix n n ℂ} (hM : Mᵀ = M.map star) (u v : n → ℂ) : hf M v u = star (hf M u v) := by
  simp only [hf]
  rw [← Matrix.star_dotProduct_star, star_mulVec', star_star, ← hM, dot_mulVec_left, Matrix.transpose_transpose]

theorem gram_apply (M : Matrix m m ℂ) (A : Matrix m n ℂ) (i j : n) :
    (Aᵀ * M * A.map star) i j = hf M (fun r => A r i) (fun r => A r j) := by
  simp only [hf, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Pi.star_apply,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

end Lin

section Core

open GlobalTheory.RealPar.DerivedAdjoint

variable {d d₁ R S : ℕ}

def pcol (ι : Matrix (Fin d) (Fin d₁) ℂ) (C : Matrix (Fin d₁) (Ix R S) ℂ) (ε φ : Fin d → ℂ) :
    Ix R S ⊕ (Unit ⊕ Unit) → Fin d → ℂ :=
  Sum.elim (fun k => ι *ᵥ fun a => C a k) (Sum.elim (fun _ => ε) (fun _ => φ))

def sg2 : Ix R S ⊕ (Unit ⊕ Unit) → ℂ :=
  Sum.elim (Sum.elim (fun _ => 1) (fun _ => -1)) (Sum.elim (fun _ => 1) (fun _ => -1))

theorem sg2_splitIx_eq (A : Fin (R + 1)) (i : Ix (R + 1) (S + 1)) :
    sg2 (splitIx (S := S) A i) = Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) i := by
  rcases i with i | i
  · by_cases h : i = A
    · subst h; simp [sg2]
    · obtain ⟨j, rfl⟩ := Fin.exists_succAbove_eq h
      simp [sg2]
  · by_cases h : i = Fin.last S
    · subst h; simp [sg2]
    · obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.2 h
      simp [sg2]

theorem extFrame_apply (A : Fin (R + 1)) (ι : Matrix (Fin d) (Fin d₁) ℂ) (C : Matrix (Fin d₁) (Ix R S) ℂ)
    (ε φ : Fin d → ℂ) (r : Fin d) (i : Ix (R + 1) (S + 1)) :
    extFrame A (ι * C) ε φ r i = pcol ι C ε φ (splitIx A i) r := by
  simp only [extFrame, Matrix.submatrix_apply, id]
  rcases splitIx A i with k | u | u <;> simp [pcol, newCols, Matrix.mul_apply, Matrix.mulVec, dotProduct]

theorem frame_of_cols (A : Fin (R + 1)) (M θ : Matrix (Fin d) (Fin d) ℂ) (ι : Matrix (Fin d) (Fin d₁) ℂ)
    (C : Matrix (Fin d₁) (Ix R S) ℂ) (ε φ : Fin d → ℂ)
    (hG : ∀ z z', hf M (pcol ι C ε φ z) (pcol ι C ε φ z') = if z = z' then sg2 z else 0)
    (hT : ∀ z, θ *ᵥ pcol ι C ε φ z = sg2 z • pcol ι C ε φ z) (hcard : Fintype.card (Ix (R + 1) (S + 1)) = d) :
    IsFrame M (extFrame A (ι * C) ε φ) ∧
      θ * extFrame A (ι * C) ε φ = extFrame A (ι * C) ε φ * Jm (R + 1) (S + 1) := by
  set Fr := extFrame A (ι * C) ε φ with hFr
  have hc : ∀ i, (fun r => Fr r i) = pcol ι C ε φ (splitIx A i) := fun i => funext fun r => extFrame_apply A ι C ε φ r i
  have hG' : Frᵀ * M * Fr.map star = Jm (R + 1) (S + 1) := by
    ext i j
    rw [gram_apply, hc, hc, hG, Jm_diag, Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp [sg2_splitIx_eq]
    · simp [h]
  refine ⟨⟨hG', ?_⟩, ?_⟩
  · have h1 : (Jm (R + 1) (S + 1) * Frᵀ * M) * Fr.map star = 1 := by
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc Frᵀ, hG', Jm_mul_Jm]
    have e : Ix (R + 1) (S + 1) ≃ Fin d := Fintype.equivOfCardEq (by simp [hcard])
    have h2 := (Matrix.mul_eq_one_comm_of_equiv e).1 h1
    refine ⟨(Jm (R + 1) (S + 1) * Frᵀ * M).map star, ?_⟩
    calc Fr * (Jm (R + 1) (S + 1) * Frᵀ * M).map star
        = (Fr.map star * (Jm (R + 1) (S + 1) * Frᵀ * M)).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; congr 1; ext i j; simp
      _ = 1 := by rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]
  · ext r i
    rw [show (θ * Fr) r i = (θ *ᵥ fun r => Fr r i) r from rfl, hc, hT, Jm_diag, Matrix.mul_diagonal, hFr,
      extFrame_apply, Pi.smul_apply, smul_eq_mul, sg2_splitIx_eq, mul_comm]

theorem exists_frame_core (A : Fin (R + 1)) (M θ : Matrix (Fin d) (Fin d) ℂ) (M₁ θ₁ : Matrix (Fin d₁) (Fin d₁) ℂ)
    (ι : Matrix (Fin d) (Fin d₁) ℂ) (x : Fin d → ℂ) (C : Matrix (Fin d₁) (Ix R S) ℂ)
    (hM : Mᵀ = M.map star) (hθ : IsCartan M θ) (hgram : ιᵀ * M * ι.map star = M₁)
    (horth : ιᵀ *ᵥ (M *ᵥ star x) = 0) (hθι : θ * ι = ι * θ₁) (hxx : hf M x x = 0) (hx : x ≠ 0)
    (hC : IsFrame M₁ C) (hθC : θ₁ * C = C * Jm R S) (hd : d = d₁ + 2) :
    ∃ ε φ : Fin d → ℂ, (IsFrame M (extFrame A (ι * C) ε φ) ∧
        θ * extFrame A (ι * C) ε φ = extFrame A (ι * C) ε φ * Jm (R + 1) (S + 1)) ∧
      ∀ (K : Matrix (Fin d) (Fin d) ℂ) (t : ℂ), Commute K θ → K *ᵥ x = t • x → K *ᵥ ε = t • ε ∧ K *ᵥ φ = t • φ := by
  obtain ⟨hθθ, hiso, hpos⟩ := hθ
  have hθθv : ∀ u, θ *ᵥ (θ *ᵥ u) = u := fun u => by rw [Matrix.mulVec_mulVec, hθθ, Matrix.one_mulVec]
  have hI : ∀ u w, hf M (θ *ᵥ u) (θ *ᵥ w) = hf M u w := fun u w => by rw [hf_mulVec, hiso]
  have hsw : ∀ u w, hf M u (θ *ᵥ w) = hf M (θ *ᵥ u) w := fun u w => by rw [← hI (θ *ᵥ u) w, hθθv]
  obtain ⟨v, hv⟩ : ∃ v, v = θ *ᵥ x := ⟨_, rfl⟩
  have hxv : hf M x v = hf M v x := by rw [hv, hsw]
  have hvv : hf M v v = 0 := by rw [hv, hI, hxx]
  have hreal : star (hf M v x) = hf M v x := by rw [← hf_conj hM v x, hxv]
  have him : (hf M v x).im = 0 := Complex.conj_eq_iff_im.1 hreal
  obtain ⟨r, har⟩ : ∃ r : ℝ, hf M v x = r := ⟨(hf M v x).re, Complex.ext (by simp) (by simp [him])⟩
  have hr : 0 < r := by
    have h0 : 0 < (hf M v x).re := by rw [hv]; exact hpos x hx
    rwa [har, Complex.ofReal_re] at h0
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s * star s * (2 * r) = 1 := by
    refine ⟨((Real.sqrt (2 * r))⁻¹ : ℝ), ?_⟩
    have h1 := Real.mul_self_sqrt (show (0 : ℝ) ≤ 2 * r by linarith)
    have h2 : Real.sqrt (2 * r) ≠ 0 := (Real.sqrt_pos.2 (by linarith)).ne'
    have h3 : (Real.sqrt (2 * r))⁻¹ * (Real.sqrt (2 * r))⁻¹ * (2 * r) = 1 := by
      calc _ = (Real.sqrt (2 * r))⁻¹ * (Real.sqrt (2 * r))⁻¹ * (Real.sqrt (2 * r) * Real.sqrt (2 * r)) := by rw [h1]
        _ = 1 := by field_simp
    have h4 : star (((Real.sqrt (2 * r))⁻¹ : ℝ) : ℂ) = (((Real.sqrt (2 * r))⁻¹ : ℝ) : ℂ) := Complex.conj_ofReal _
    rw [h4]; exact_mod_cast h3
  obtain ⟨ε, hε⟩ : ∃ ε : Fin d → ℂ, ε = s • (x + v) := ⟨_, rfl⟩
  obtain ⟨φ, hφ⟩ : ∃ φ : Fin d → ℂ, φ = s • (x - v) := ⟨_, rfl⟩
  have hee : hf M ε ε = 1 := by
    simp only [hε, hf_smul_left, hf_smul_right, hf_add_left, hf_add_right]
    rw [hxx, hvv, hxv, har]; linear_combination hs
  have hff : hf M φ φ = -1 := by
    simp only [hφ, hf_smul_left, hf_smul_right, hf_sub_left, hf_sub_right]
    rw [hxx, hvv, hxv, har]; linear_combination (-1 : ℂ) * hs
  have hef : hf M ε φ = 0 := by
    simp only [hε, hφ, hf_smul_left, hf_smul_right, hf_add_left, hf_sub_right]
    rw [hxx, hvv, hxv, har]; ring
  have hfe : hf M φ ε = 0 := by
    simp only [hε, hφ, hf_smul_left, hf_smul_right, hf_sub_left, hf_add_right]
    rw [hxx, hvv, hxv, har]; ring
  have hιx : ∀ p, hf M (ι *ᵥ p) x = 0 := fun p => by
    simp only [hf]; rw [dot_mulVec_left, horth, dotProduct_zero]
  have hιv : ∀ p, hf M (ι *ᵥ p) v = 0 := fun p => by
    rw [hv, hsw, Matrix.mulVec_mulVec, hθι, ← Matrix.mulVec_mulVec, hιx]
  have hιε : ∀ p, hf M (ι *ᵥ p) ε = 0 := fun p => by
    rw [hε, hf_smul_right, hf_add_right, hιx, hιv]; ring
  have hιφ : ∀ p, hf M (ι *ᵥ p) φ = 0 := fun p => by
    rw [hφ, hf_smul_right, hf_sub_right, hιx, hιv]; ring
  have hει : ∀ p, hf M ε (ι *ᵥ p) = 0 := fun p => by rw [hf_conj hM, hιε, star_zero]
  have hφι : ∀ p, hf M φ (ι *ᵥ p) = 0 := fun p => by rw [hf_conj hM, hιφ, star_zero]
  have hιι : ∀ p q, hf M (ι *ᵥ p) (ι *ᵥ q) = hf M₁ p q := fun p q => by rw [hf_mulVec, hgram]
  have hθε : θ *ᵥ ε = ε := by
    rw [hε, hv, Matrix.mulVec_smul, Matrix.mulVec_add, hθθv, add_comm]
  have hθφ : θ *ᵥ φ = -φ := by
    rw [hφ, hv, Matrix.mulVec_smul, Matrix.mulVec_sub, hθθv, ← smul_neg, neg_sub]
  have hθι' : ∀ p, θ *ᵥ (ι *ᵥ p) = ι *ᵥ (θ₁ *ᵥ p) := fun p => by
    rw [Matrix.mulVec_mulVec, hθι, ← Matrix.mulVec_mulVec]
  have hcolθ : ∀ k, θ₁ *ᵥ (fun a => C a k) = Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1) k • fun a => C a k := fun k => by
    funext a
    have e := congrFun (congrFun hθC a) k
    rw [Jm_diag, Matrix.mul_diagonal] at e
    rw [Pi.smul_apply, smul_eq_mul, mul_comm, ← e]
    rfl
  obtain ⟨C', hC'⟩ := hC.2
  have hC'' : C' * C = 1 := frame_inv hC.1 hC'
  have hcd : Fintype.card (Fin d₁) = Fintype.card (Ix R S) := by
    have h1 := Matrix.rank_mul_le_left C C'
    rw [hC', Matrix.rank_one] at h1
    have h2 := Matrix.rank_mul_le_left C' C
    rw [hC'', Matrix.rank_one] at h2
    exact le_antisymm (h1.trans (Matrix.rank_le_card_width C)) (h2.trans (Matrix.rank_le_card_width C'))
  have hcard : Fintype.card (Ix (R + 1) (S + 1)) = d := by
    simp only [Fintype.card_sum, Fintype.card_fin] at hcd ⊢; omega
  refine ⟨ε, φ, frame_of_cols A M θ ι C ε φ ?_ ?_ hcard, ?_⟩
  · rintro (k | ⟨⟩ | ⟨⟩) (l | ⟨⟩ | ⟨⟩) <;> simp only [pcol, sg2, Sum.elim_inl, Sum.elim_inr]
    · rw [hιι, ← gram_apply, hC.1, Jm_diag, Matrix.diagonal_apply]
      by_cases h : k = l
      · subst h; simp
      · simp [h]
    all_goals simp [hιε, hιφ, hει, hφι, hee, hff, hef, hfe]
  · rintro (k | ⟨⟩ | ⟨⟩) <;> simp only [pcol, sg2, Sum.elim_inl, Sum.elim_inr]
    · rw [hθι', hcolθ k, Matrix.mulVec_smul]
    · rw [hθε, one_smul]
    · rw [hθφ, neg_one_smul]
  · intro K t hKθ hKx
    have hKv : K *ᵥ v = t • v := by
      rw [hv, Matrix.mulVec_mulVec, hKθ.eq, ← Matrix.mulVec_mulVec, hKx, Matrix.mulVec_smul]
    constructor
    · rw [hε, Matrix.mulVec_smul, Matrix.mulVec_add, hKx, hKv, ← smul_add, smul_comm]
    · rw [hφ, Matrix.mulVec_smul, Matrix.mulVec_sub, hKx, hKv, ← smul_sub, smul_comm]

end Core

section Main

theorem exists_extFrame_adapted : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (d d₁ r s i₀ i₁ R S : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁), IsCMExt F E σ →
    W.IsSkew σ B r s → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ (A : Fin (R + 1)) (w : InfinitePlace F)
    (C : Matrix (Fin d₁) (Formalism.BasicNotions.TH.Ix R S) ℂ), GlobalTheory.ThK.RealK.IsAdapted B.emb w W₁ C →
    ∃ ε φ : Fin d → ℂ, GlobalTheory.ThK.RealK.IsAdapted B.emb w W (GlobalTheory.TwCoef.extFrame A (H'.ι.map (B.emb w).1 * C) ε φ) ∧
      ∀ (t : (AE F E)ˣ) (h₁ : UA σ W₁.J) (k : UA σ W.J), k ∈ KInf σ W B.emb → IsLevi H' t h₁ k →
        (mat k).map (piInf (B.emb w)) *ᵥ ε = piInf (B.emb w) t.1 • ε ∧
        (mat k).map (piInf (B.emb w)) *ᵥ φ = piInf (B.emb w) t.1 • φ := by
  intro F E _ _ _ _ _ σ B d d₁ r s i₀ i₁ R S W W₁ H' hCM hW hA A w C hC
  obtain ⟨hθι, -⟩ := hA.cartan w
  have hτ : ∀ e : E, (B.emb w).1 (σ e) = star ((B.emb w).1 e) := fun e => hCM.2.2.2 _ e
  have htr : ∀ {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (u v : Fin n → E),
      hf (Complex.I • J.map (B.emb w).1) (fun i => (B.emb w).1 (u i)) (fun i => (B.emb w).1 (v i)) =
        Complex.I * (B.emb w).1 (form σ J u v) := by
    intro n J u v
    have h1 : (fun i => (B.emb w).1 ((J *ᵥ fun j => σ (v j)) i)) = J.map (B.emb w).1 *ᵥ star (fun i => (B.emb w).1 (v i)) := by
      funext i; rw [RingHom.map_mulVec]; congr 1; funext j; simp [hτ]
    calc _ = Complex.I * ((fun i => (B.emb w).1 (u i)) ⬝ᵥ (J.map (B.emb w).1 *ᵥ star (fun i => (B.emb w).1 (v i)))) := by
          simp only [hf]; rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      _ = _ := by rw [← h1, form, RingHom.map_dotProduct]; rfl
  have hM : (herm W.J (B.emb w))ᵀ = (herm W.J (B.emb w)).map star := by
    ext i j
    simp only [herm, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
    rw [← hτ, hW.skew j i, map_neg, show star Complex.I = -Complex.I from Complex.conj_I]; ring
  have hgram : (H'.ι.map (B.emb w).1)ᵀ * herm W.J (B.emb w) * (H'.ι.map (B.emb w).1).map star = herm W₁.J (B.emb w) := by
    have g := congrArg (fun X => X.map (B.emb w).1) hA.gram
    simp only [Matrix.map_mul, Matrix.transpose_map] at g
    have e : (H'.ι.map σ).map (B.emb w).1 = (H'.ι.map (B.emb w).1).map star := by ext; simp [hτ]
    rw [e] at g
    simp only [herm]; rw [Matrix.mul_smul, Matrix.smul_mul, g]
  have hxx : hf (herm W.J (B.emb w)) (fun i => (B.emb w).1 (H'.x i)) (fun i => (B.emb w).1 (H'.x i)) = 0 := by
    have := htr W.J H'.x H'.x; rw [hA.xx, map_zero, mul_zero] at this; exact this
  have hx : (fun i => (B.emb w).1 (H'.x i)) ≠ 0 := by
    intro h0
    have := htr W.J H'.x H'.y
    rw [hA.xy, map_one, mul_one] at this
    change hf (herm W.J (B.emb w)) (fun i => (B.emb w).1 (H'.x i)) (fun i => (B.emb w).1 (H'.y i)) = Complex.I at this
    rw [h0] at this
    simp only [hf, zero_dotProduct] at this
    exact Complex.I_ne_zero this.symm
  have horth : (H'.ι.map (B.emb w).1)ᵀ *ᵥ (herm W.J (B.emb w) *ᵥ star (fun i => (B.emb w).1 (H'.x i))) = 0 := by
    funext j
    have h1 := htr W.J (H'.ι *ᵥ Pi.single j 1) H'.x
    rw [(hA.orth (Pi.single j 1)).1, map_zero, mul_zero] at h1
    have h2 : (fun i => (B.emb w).1 ((H'.ι *ᵥ Pi.single j 1) i)) = H'.ι.map (B.emb w).1 *ᵥ Pi.single j 1 := by
      funext i; rw [RingHom.map_mulVec]; congr 1; funext k; simp [Pi.single_apply, apply_ite]
    rw [h2] at h1
    change hf (herm W.J (B.emb w)) _ _ = 0 at h1
    simp only [hf] at h1
    rw [dot_mulVec_left] at h1
    simpa using h1
  obtain ⟨ε, φ, hF, hK⟩ := exists_frame_core A (herm W.J (B.emb w)) (W.θ w) (herm W₁.J (B.emb w)) (W₁.θ w)
    (H'.ι.map (B.emb w).1) (fun i => (B.emb w).1 (H'.x i)) C hM (hW.cartan w) hgram horth hθι hxx hx hC.1 hC.2 hA.rank
  refine ⟨ε, φ, hF, fun t h₁ k hk hL => hK _ _ (hk.2 w) ?_⟩
  have hπ : ∀ e : E, piInf (B.emb w) (inclR (F := F) (AF F) e) = (B.emb w).1 e := fun e => by
    have := congrFun (congrFun (GlobalTheory.ThK.RealK.incM_map (F := F) (Matrix.of fun (_ _ : Unit) => e) (B.emb w)) ()) ()
    simpa [incM] using this
  funext i
  have e : piInf (B.emb w) ((mat k *ᵥ incV F H'.x) i) = piInf (B.emb w) ((t.1 • incV F H'.x) i) := by rw [hL.1]
  rw [RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul, map_mul] at e
  have hv : (piInf (B.emb w) ∘ incV F H'.x) = fun i => (B.emb w).1 (H'.x i) := funext fun j => hπ (H'.x j)
  rw [hv, show piInf (B.emb w) (incV F H'.x i) = (B.emb w).1 (H'.x i) from hπ _] at e
  rw [Pi.smul_apply, smul_eq_mul]
  exact e

end Main

end GlobalTheory.TwCoefFrame
