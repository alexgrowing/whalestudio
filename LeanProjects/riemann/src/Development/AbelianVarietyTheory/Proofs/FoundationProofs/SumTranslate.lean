import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.IsZetaSystemFixedExponent
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleNewformZetaData
import Development.AbelianVarietyTheory.Definitions.Foundations.AdmissibleHodgeTateZetaClassParams
import Development.AbelianVarietyTheory.Definitions.Foundations.HTPresNuOfPolys
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFROfIsLamF
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLamFR2
import Development.AbelianVarietyTheory.Definitions.Foundations.ChiProj
import Development.AbelianVarietyTheory.Definitions.Foundations.CoPtMu
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLPowLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UntwistedRepresentationOrdinaryTriangularShape
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ShCocQuotCoord
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.KumValSubMem
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PieceTUnitSetMuModelSmoothedSb

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4
open scoped Matrix MatrixGroups

namespace GlobalTheory.HTLawZeta

open GlobalTheory.KummerEisensteinGalois GlobalTheory.LambdaValuationPowers

variable {l : ℕ} [Fact l.Prime] {Ω : Type} [Field Ω] [Algebra ℚ Ω]

theorem rho_on_dec [IsAlgClosure ℚ Ω] {ι : Qbar l ≃+* ℂ} {e : ℕ} {S : Finset Pl} {A : ValuationSubring Ω} {W : R2 Ω l}
    {g : Newform (2 * e + 1)} (hnf : Nf e S A W) (hsrc : SrcUr ι e A W g) {ε : Ω →+* ℂ} {X : Tower Ω ε}
    {pr : X.Fn l → Fin 2 → Qbar l} {N : ℕ} [NeZero N] {x : ZMod N} {c d : ℕ} {gm : (ZMod l)ˣ → SL(2, ℤ)} {ψ : ZMod l → Qbar l}
    {cf : Coef l} (hadm : AdmissibleNewformZetaData ι e g A W X pr N x c d gm ψ cf) :
    (∀ s ∈ Dec (F := ℚ) A, rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = (nuD W e ψ s : Qbar l)) ∧
    (∀ s ∈ Ine (F := ℚ) A, nuD W e ψ s = 1) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, χ', hχ'k, hχ'I, hχ'ψ⟩ := hadm
  have hth : ∀ s, thK l e ψ s = (eps l s ^ e)⁻¹ * (χ' s : Qbar l) := fun s => by rw [thK, ← hχ'ψ s]
  have hrho : ∀ s i j, rhoK W e ψ s i j = (thK l e ψ s)⁻¹ * mat W s i j := fun s i j => by
    simp [rhoK, Matrix.smul_apply, smul_eq_mul]
  have hE : ∀ s : G ℚ Ω, eps l s ^ e ≠ 0 := fun s => pow_ne_zero _ (Units.ne_zero _)
  have hth0 : ∀ s, thK l e ψ s ≠ 0 := fun s => by
    rw [hth]; exact mul_ne_zero (inv_ne_zero (hE s)) (Units.ne_zero _)
  have hnuD : ∀ s, rhoK W e ψ s 1 1 ≠ 0 → (nuD W e ψ s : Qbar l) = rhoK W e ψ s 1 1 := fun s h => by
    simp [nuD, h]
  have hr11 : ∀ s ∈ Dec (F := ℚ) A, rhoK W e ψ s 1 1 ≠ 0 := fun s hs => by
    rw [hrho]
    refine mul_ne_zero (inv_ne_zero (hth0 s)) ?_
    have hd : (mat W s).det ≠ 0 := ((Matrix.isUnit_iff_isUnit_det _).1 (W s).isUnit).ne_zero
    rw [Matrix.det_fin_two, hnf.upper s hs, mul_zero, sub_zero] at hd
    exact right_ne_zero_of_mul hd
  obtain ⟨ρ, hρ, -, -, hρI, -⟩ := GlobalTheory.RhoAdm.rho_ordinary_shape l Ω ι e S A W g ψ hnf hsrc ⟨χ', hχ'k, hχ'I, hχ'ψ⟩
  have hI11 : ∀ s ∈ Ine (F := ℚ) A, rhoK W e ψ s 1 1 = 1 := fun s hs => by
    rw [← hρ s]; exact hρI s hs
  exact ⟨fun s hs => ⟨by rw [hrho, hnf.upper s hs, mul_zero], (hnuD s (hr11 s hs)).symm⟩,
    fun s hs => Units.ext (by rw [hnuD s (hr11 s (Ine_le_Dec A hs)), hI11 s hs, Units.val_one])⟩

theorem htCoL_smooth {A : ValuationSubring Ω} {c : Coef l} {j : Ω →+* Qbar l} {Z : ∀ r : ℕ, G ℚ Ω → (ZMod (l ^ r))ˣ → Qbar l}
    {m a : ℕ} {y : (ZMod (l ^ m))ˣ} {h h' : Qbar l} (u : ∀ r : ℕ, (ZMod (l ^ r))ˣ) (d : ℕ) (H : HTCoL A c j Z m a y h)
    (H' : HTCoL A c j Z m a (y * u m) h') :
    HTCoL A c j (fun r s y' => Z r s y' - (d : Qbar l) * Z r s (y' * u r)) m a y (h - (d : Qbar l) * h') := by
  have h1 := GlobalTheory.LambdaValuationPowers.htCoL_sum l Ω A c j Bool (fun b => cond b 1 (-(d : Qbar l)))
    (fun b => cond b Z (fun r s y' => Z r s (y' * u r))) m a y (fun b => cond b h h')
    (fun b => by
      cases b
      · exact ⟨by simpa using IsUltrametricDist.norm_natCast_le_one (Qbar l) d, fun σ _ _ => by simp⟩
      · exact ⟨by simp, fun σ _ _ => by simp⟩)
    (fun b => by
      cases b
      · exact H'
      · exact H)
  convert h1 using 1
  · funext r s y'
    simp [sub_eq_add_neg]
  · simp [sub_eq_add_neg]

theorem sum_translate {m N : ℕ} (ψ : DirichletCharacter (Qbar l) (l ^ m)) (V : ℕ → Qbar l) (R : Qbar l)
    (hV : ∀ β : (ZMod (l ^ m))ˣ → ℕ, (∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) →
      ∑ b : (ZMod (l ^ m))ˣ, ψ b * V (β b) = R)
    (u : (ZMod (l ^ m))ˣ) (γ : ℕ) (hγ : (γ : ZMod (l ^ m)) = u ∧ (γ : ZMod N) = 1) (β : (ZMod (l ^ m))ˣ → ℕ)
    (hβ : ∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * V (β b * γ) = ψ⁻¹ u * R := by
  rw [← hV (fun b => β (b * u⁻¹) * γ) (fun b => by
    simp only [Nat.cast_mul, hβ, hγ, mul_one, and_true]
    rw [← Units.val_mul, inv_mul_cancel_right]), Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.mulRight u) _ _ fun b => ?_
  have hu : ψ u ≠ 0 := by
    rw [← MulChar.coe_toUnitHom]
    exact Units.ne_zero _
  simp only [Equiv.coe_mulRight, mul_inv_cancel_right, Units.val_mul, map_mul, MulChar.inv_apply_eq_inv']
  field_simp

def chiVal (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N : ℕ) [NeZero N] (k : ℕ) (χ : ℕ → Qbar l)
    (c d x : ℤ) (m β : ℕ) (t : ℤ) : Qbar l :=
  ∑ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ * unitVal ε j lam N k c d (x * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ))
    (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) m β

theorem sum_chiVal [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (j : Ω →+* Qbar l) (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l) (N : ℕ) [NeZero N]
    (k : ℕ) (χ : ℕ → Qbar l) (c d x t : ℤ) (m : ℕ) (β : (ZMod (l ^ m))ˣ → ℕ) (ψ : DirichletCharacter (Qbar l) (l ^ m))
    (hχ : ∀ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ = χ ((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val)
    (hl : l ≠ 2) (hN : ¬ l ∣ N) (hm : 1 ≤ m) (hk : 3 ≤ k) (hψ : ψ.IsPrimitive) (hc : ¬ (l : ℤ) ∣ c) (hd : ¬ (l : ℤ) ∣ d)
    (ht : (l : ℤ) ^ m * t ≡ 1 [ZMOD N]) (hβ : ∀ b, ((β b : ℕ) : ZMod (l ^ m)) = b ∧ ((β b : ℕ) : ZMod N) = 1) :
    ∑ b : (ZMod (l ^ m))ˣ, ψ b * chiVal ε j lam N k χ c d x m (β b) t =
      -((N : Qbar l) ^ ((2 : ℤ) - k)) * (∑ a : ZMod (l ^ m), ψ a * (j (eOm ε (1 / (l : ℚ) ^ m))) ^ a.val) *
        ψ⁻¹ (N : ZMod (l ^ m)) * lam (up (l ^ m) (chiProj N l m k ψ χ c d x)) := by
  have hN0 : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  have hup : up (l ^ m) (chiProj N l m k ψ χ c d x) = ∑ δ : (ZMod N)ˣ, χ ((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val •
      up (l ^ m) (coPtSb N l m k ψ c d (x * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) := by
    funext i
    simp only [up, chiProj, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Fintype.sum_equiv (Equiv.inv _) _ _ fun δ => by simp only [Equiv.inv_apply, inv_inv]
  simp only [chiVal, Finset.mul_sum (s := (Finset.univ : Finset (ZMod N)ˣ))]
  rw [Finset.sum_comm, hup, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun δ _ => ?_
  simp only [mul_left_comm (ψ _) (χ _)⁻¹]
  rw [← Finset.mul_sum, sum_unitVal ε j lam N k c d _ _ m β ψ
    (coPtSb N l m k ψ c d (x * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ)) hN hm hβ
    (fun ζ hζ r => by
      rw [mul_right_comm x t, mul_comm t]
      exact (GlobalTheory.LambdaValuationPowers.pieceT_unitSet_muModel_smoothedSb l N m k (Qbar l) ψ c d _ _ t ζ hl hζ hN0 hN hm hk hψ hc hd ht).2 r),
    map_smul, smul_eq_mul, hχ]
  ring

theorem law_of_inputs
  (hcoef : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (l : ℕ) [Fact l.Prime], l ≠ 2 →
  (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (A : ValuationSubring Ω) (j : Ω →+* Qbar l), OverL l A → (∀ z : Ω, z ∈ A ↔ ‖j z‖ ≤ 1) →
  ∀ (N : ℕ) [NeZero N], ¬ l ∣ N → ∀ (c d e : ℕ) (gm : (ZMod l)ˣ → SL(2, ℤ)), 1 ≤ e →
  ∀ (ι : Qbar l ≃+* ℂ) (gN : Newform (2 * e + 1)) (W : R2 Ω l) (pr : X.Fn l → Fin 2 → Qbar l) (ψ : ZMod l → Qbar l) (cf : Coef l),
  ∀ (α : Qbar l), GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  (∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l 1 s = 1 → rhoK W e ψ s 1 0 = 0 ∧ rhoK W e ψ s 1 1 = 1) →
  ∀ (χ : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χ δ)) → (∀ a b : ℕ, χ (a * b) = χ a * χ b) →
    (∀ a b : ℕ, a % N = b % N → χ a = χ b) →
  ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χ j pr cf lam →
  ∀ (c₀ : ℕ), ∃ (c' : ℕ) (κ₀ : Qbar l) (per : ℕ → Qbar l), κ₀ ≠ 0 ∧ (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧ ∀ (x : ZMod N),
  GlobalTheory.K4.AdmissibleNewformZetaData ι e gN A W X pr N x c d gm ψ cf →
  ∀ (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
  IsZetaSystemFixedExponent X l pr W e ψ N x c d (2 * e + 1) gm cf c₀ Y →
  ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
    (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
    GlobalTheory.LambdaValuationPowers.HTCoL A cf j (fun r s y' => Y r s y' 1) m c' y
      ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ * ∑ δ : (ZMod N)ˣ,
        (algebraMap ℚ_[l] (Qbar l) ((χ (δ : ZMod N).val : ℤ_[l]) : ℚ_[l]))⁻¹ *
        lam (fun i => (l : Qbar l) ^ m * j (GlobalTheory.KummerEisensteinGalois.toQ (l ^ m)
          (GlobalTheory.KummerEisensteinGalois.pieceT N l m m (2 * e + 1) (1 : DirichletCharacter Ω (l ^ m)) (c : ℤ) (d : ℤ)
            ((x.val : ℤ) * t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0) (t * (((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val : ℤ), 0)
            (eOm ε (1 / ((N : ℚ) * (l : ℚ) ^ m)) ^ β)
            ((GlobalTheory.KummerEisensteinGalois.unitSet l m).filter fun γ => (γ : Matrix (Fin 2) (Fin 2) (ZMod (l ^ m))).det = 1)) i))))
  (hunit : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₀' : ℕ), ∀ m, m₀ ≤ m → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ m) → ∃ (ι : Type) (_ : Fintype ι) (P : ι → Polynomial Ω) (o : ι → Qbar l),
    HTPresNuOfPolys A cf m c₀' (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) ζ P o) :
  ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ι : Qbar l ≃+* ℂ) (e : ℕ) (S : Finset Pl)
    (A : ValuationSubring Ω) (W : R2 Ω l) (g : Newform (2 * e + 1)), Nf e S A W → SrcUr ι e A W g →
  ∀ (ε : Ω →+* ℂ) (X : Tower Ω ε) (pr : X.Fn l → Fin 2 → Qbar l) (N : ℕ) [NeZero N] (cw : ZMod N → Qbar l) (c d : ℕ)
    (gm : (ZMod l)ˣ → SL(2, ℤ)) (ψ₀ : ZMod l → Qbar l) (cf : Coef l) (α : Qbar l),
    (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → l ≠ 2 → 1 ≤ e →
    AdmWn ι e g A W X pr N cw c d gm ψ₀ cf → GlobalTheory.LambdaValuationPowers.AdmissibleHodgeTateZetaClassParams e X pr N gm α →
  ∀ (j : Ω →+* Qbar l), (∀ y, y ∈ A ↔ ‖j y‖ ≤ 1) →
  ∀ (c₀ : ℕ) (Y : ∀ r : ℕ, (Ω ≃ₐ[ℚ] Ω) → (ZMod (l ^ r))ˣ → Fin 2 → Qbar l),
    IsZWc X l pr W e ψ₀ N cw c d (2 * e + 1) gm cf c₀ Y →
    (∀ r, GlobalTheory.KA.ShCoc (rhoK W e ψ₀) (cycMod (F := ℚ) (Ω := Ω) l r)⁻¹ (Y r)) →
    (∀ (r n : ℕ), ∃ E0 : Finset Ω, ∀ (s s' : Ω ≃ₐ[ℚ] Ω) (y : (ZMod (l ^ r))ˣ), (∀ z ∈ E0, s' z = z) → Cg n (Y r (s * s') y 1) (Y r s y 1)) →
    (∀ r s y, Y r s y 1 ∈ cf.O) →
  ∀ (χd : ℕ → ℤ_[l]), (∀ δ : ℕ, Nat.Coprime δ N → IsUnit (χd δ)) → (∀ a b : ℕ, χd (a * b) = χd a * χd b) →
    (∀ a b : ℕ, a % N = b % N → χd a = χd b) → ∀ (lam : (ℕ → Qbar l) →ₗ[Qbar l] Qbar l), GlobalTheory.KummerEisensteinGalois.IsLamFR2 X A N (2 * e - 1) χd j pr cf lam →
  ∀ (d₀ : ℕ) (hd₀ : Nat.Coprime d₀ l), 2 ≤ d₀ →
  ∃ (m₀ c₁ : ℕ) (κ : Qbar l) (v : ℕ → Qbar l), κ ≠ 0 ∧ (∀ m, ‖v m‖ = 1 ∧ Cg m (v (m + 1)) (v m)) ∧
    HTLawCsOfCoef A cf (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀)) 1) j m₀ c₁
      (fun m ψ z => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) * v m * κ * (∑ a : ZMod (l ^ m), ψ a * z ^ a.val) * ψ⁻¹ (N : ZMod (l ^ m)) *
        lam (GlobalTheory.KummerEisensteinGalois.up (l ^ m) (fun i => ∑ x : ZMod N, cw x *
          GlobalTheory.LambdaValuationPowers.chiProj N l m (2 * e + 1) ψ (fun n => ((χd n : ℤ_[l]) : Qbar l)) (c : ℤ) (d : ℤ) (x.val : ℤ) i))) := by
  intro l _ Ω _ _ _ ι e S A W g hnf hsrc ε X pr N _ cw c d gm ψ₀ cf α hjK hl he hadm hK5 j hj c₀ Y hZW hcoc hcont hint
    χd hχu hχm hχp lam hlam d₀ hd₀ hd₂
  classical
  have hp : l.Prime := Fact.out
  have hN : ¬ l ∣ N := (Nat.Prime.coprime_iff_not_dvd hp).1 hK5.2.1
  have hpres := hunit l Ω ι e S A W g hnf hsrc ε X pr N cw c d gm ψ₀ cf α hjK hl he hadm hK5 j hj c₀ Y hZW hcoc hcont hint
    d₀ hd₀ hd₂
  obtain ⟨Yx, hYx, hY⟩ := hZW
  set χ : ℕ → Qbar l := fun n => ((χd n : ℤ_[l]) : Qbar l) with hχ
  set u : ∀ r : ℕ, (ZMod (l ^ r))ˣ := fun r => ZMod.unitOfCoprime d₀ (Nat.Coprime.pow_right r hd₀) with hu

  obtain ⟨ν, κ₀, c', per, hνI, hνD, hκ, hper, hco⟩ : ∃ (ν : G ℚ Ω → (Qbar l)ˣ) (κ₀ : Qbar l) (c' : ℕ) (per : ℕ → Qbar l),
      (∀ s ∈ Ine (F := ℚ) A, ν s = 1) ∧
      (∀ m, ∀ s ∈ Dec (F := ℚ) A, ∀ t ∈ Dec (F := ℚ) A, ∀ x,
        Y m (s * t) x 1 = Y m s x 1 + (ν s : Qbar l) * Y m t (x * (cycMod ℚ Ω l m s)⁻¹) 1) ∧ κ₀ ≠ 0 ∧
      (∀ n, ‖per n‖ = 1 ∧ Cg n (per (n + 1)) (per n)) ∧
      ∀ x, cw x ≠ 0 → ∀ m : ℕ, 1 ≤ m → ∀ (y : (ZMod (l ^ m))ˣ) (β : ℕ) (t : ℤ),
        (β : ZMod (l ^ m)) = (y : ZMod (l ^ m)) → (β : ZMod N) = 1 → (l : ℤ) ^ m * t ≡ 1 [ZMOD N] →
        HTCoL A cf j (fun r s y' => Yx x r s y' 1) m c' y ((per m)⁻¹ * (l : Qbar l) ^ c₀ * κ₀ *
          chiVal ε j lam N (2 * e + 1) χ (c : ℤ) (d : ℤ) (x.val : ℤ) m β t) := by
    by_cases h0 : ∃ x, cw x ≠ 0
    · obtain ⟨x₀, hx₀⟩ := h0
      obtain ⟨hD, hI⟩ := rho_on_dec hnf hsrc (hadm.1 x₀ hx₀)
      have hρI : ∀ s ∈ Ine (F := ℚ) A, cycMod ℚ Ω l 1 s = 1 → rhoK W e ψ₀ s 1 0 = 0 ∧ rhoK W e ψ₀ s 1 1 = 1 :=
        fun s hs _ => ⟨(hD s (Ine_le_Dec A hs)).1, by rw [(hD s (Ine_le_Dec A hs)).2, hI s hs, Units.val_one]⟩
      obtain ⟨c', κ₀, per, hκ, hper, h⟩ := hcoef Ω ε X l hl hjK A j hnf.atL hj N hN c d e gm he ι g W pr ψ₀ cf α hK5 hρI
        χd hχu hχm hχp lam hlam c₀
      exact ⟨nuD W e ψ₀, κ₀, c', per, hI, fun m => GlobalTheory.KA.shCoc_quot_coord l Ω A _ _ Y m (hcoc m) hD, hκ, hper,
        fun x hx => h x (hadm.1 x hx) (Yx x) (hYx x)⟩
    · have h1 : ∀ x, cw x = 0 := fun x => by_contra fun h => h0 ⟨x, h⟩
      exact ⟨1, 1, 0, 1, fun _ _ => rfl, fun m s _ t _ x => by simp [hY, h1], one_ne_zero,
        fun n => by simp [Cg], fun x hx => (hx (h1 x)).elim⟩
  have hγ : ∀ m : ℕ, ∃ γ : ℕ, (γ : ZMod (l ^ m)) = u m ∧ (γ : ZMod N) = 1 := fun m => by
    obtain ⟨γ, h1, h2⟩ := Nat.chineseRemainder (Nat.Coprime.pow_left m hK5.2.1) d₀ 1
    refine ⟨γ, ?_, ?_⟩
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h1, hu, ZMod.coe_unitOfCoprime]
    · rw [(ZMod.natCast_eq_natCast_iff _ _ _).2 h2, Nat.cast_one]
  choose γ hγ using hγ
  have hχ1 : χd 1 = 1 := (hχu 1 (Nat.coprime_one_left N)).mul_left_cancel (by rw [← hχm, mul_one, mul_one])
  have hχinv : ∀ δ : (ZMod N)ˣ, (χ (δ : ZMod N).val)⁻¹ = χ ((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val := fun δ => by
    have h1 : χd (δ : ZMod N).val * χd ((δ⁻¹ : (ZMod N)ˣ) : ZMod N).val = 1 := by
      rw [← hχm, ← hχ1]
      refine hχp _ _ ((ZMod.natCast_eq_natCast_iff _ _ _).1 ?_)
      rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.mul_inv, Nat.cast_one]
    refine inv_eq_of_mul_eq_one_right ?_
    change algebraMap ℚ_[l] (Qbar l) _ * algebraMap ℚ_[l] (Qbar l) _ = 1
    rw [← map_mul, ← PadicInt.coe_mul, h1, PadicInt.coe_one, map_one]
  have hcd : ∀ x, cw x ≠ 0 → ¬ (l : ℤ) ∣ (c : ℤ) ∧ ¬ (l : ℤ) ∣ (d : ℤ) := fun x hx => by
    obtain ⟨-, -, h1, h2, -⟩ := hadm.1 x hx
    have hdv : l ∣ 6 * l * N := Dvd.dvd.mul_right (dvd_mul_left l 6) N
    exact ⟨fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 (h1.coprime_dvd_right hdv).symm (Int.natCast_dvd_natCast.1 h),
      fun h => (Nat.Prime.coprime_iff_not_dvd hp).1 (h2.coprime_dvd_right hdv).symm (Int.natCast_dvd_natCast.1 h)⟩
  have hN1 : (N : Qbar l) ≠ 0 := by exact_mod_cast NeZero.ne N
  obtain ⟨c₁, hloc⟩ := GlobalTheory.LambdaValuationPowers.LocGlue.localGlue l hl Ω A cf j hnf.atL hj
  obtain ⟨m₀, c₂, κ, v, hκ', hv, hlaw⟩ := law_of_parts A cf j ε N cw c₀
    (-((N : Qbar l) ^ ((2 : ℤ) - ((2 * e + 1 : ℕ) : ℤ))))
    (fun x m β t => chiVal ε j lam N (2 * e + 1) χ (c : ℤ) (d : ℤ) (x.val : ℤ) m β t -
      (d₀ : Qbar l) * chiVal ε j lam N (2 * e + 1) χ (c : ℤ) (d : ℤ) (x.val : ℤ) m (β * γ m) t)
    (fun m ψ x => (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) • chiProj N l m (2 * e + 1) ψ χ (c : ℤ) (d : ℤ) (x.val : ℤ))
    (fun x r s y => Yx x r s y 1 - (d₀ : Qbar l) * Yx x r s (y * u r) 1)
    (fun r s y => Y r s y 1 - (d₀ : Qbar l) * Y r s (y * u r) 1) lam per κ₀
    (fun r s y => by
      simp only [hY, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring)
    hper hκ (neg_ne_zero.2 (zpow_ne_zero _ hN1)) hN hadm.2
    (fun x hx m hm ψ hψ β t hβ ht => by
      have hV := fun β' hβ' => sum_chiVal ε j lam N (2 * e + 1) χ c d (x.val : ℤ) t m β' ψ hχinv hl hN hm (by omega) hψ
        (hcd x hx).1 (hcd x hx).2 ht hβ'
      have h2 := sum_translate ψ (fun b => chiVal ε j lam N (2 * e + 1) χ (c : ℤ) (d : ℤ) (x.val : ℤ) m b t) _ hV (u m) (γ m)
        (hγ m) β hβ
      have h3 : up (l ^ m) ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) •
          chiProj N l m (2 * e + 1) ψ χ (c : ℤ) (d : ℤ) (x.val : ℤ)) = (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) •
          up (l ^ m) (chiProj N l m (2 * e + 1) ψ χ (c : ℤ) (d : ℤ) (x.val : ℤ)) := rfl
      simp only [mul_sub, mul_left_comm (ψ _) (d₀ : Qbar l), Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [h2, hV β hβ, h3, map_smul, smul_eq_mul, hu, ZMod.coe_unitOfCoprime]
      ring)
    (fun x hx => ⟨c', fun m hm y β t h1 h2 ht => by
      have h3 := htCoL_smooth u d₀ (hco x hx m hm y β t h1 h2 ht) (hco x hx m hm (y * u m) (β * γ m) t
        (by rw [Nat.cast_mul, h1, (hγ m).1, Units.val_mul]) (by rw [Nat.cast_mul, h2, (hγ m).2, mul_one]) ht)
      convert h3 using 1
      ring⟩)
    hpres
    ⟨c₁, fun m C hC ζ ι' _ P o h hP hH => hloc ν _ m C hC hνI (fun s hs t ht x => by
      rw [hνD m s hs t ht x, hνD m s hs t ht (x * u m), mul_right_comm x (u m)]
      ring) ζ ι' P o h hP hH⟩
  refine ⟨m₀, c₂, κ, v, hκ', hv, ?_⟩
  convert hlaw using 1
  funext m ψ z
  have h4 : up (l ^ m) (fun i => ∑ x : ZMod N, cw x * ((1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) •
      chiProj N l m (2 * e + 1) ψ χ (c : ℤ) (d : ℤ) (x.val : ℤ)) i) = (1 - (d₀ : Qbar l) * ψ⁻¹ (d₀ : ZMod (l ^ m))) •
      up (l ^ m) (fun i => ∑ x : ZMod N, cw x * chiProj N l m (2 * e + 1) ψ χ (c : ℤ) (d : ℤ) (x.val : ℤ) i) := by
    funext i
    simp only [up, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h4, map_smul, smul_eq_mul]
  ring

end GlobalTheory.HTLawZeta

end
