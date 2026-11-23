import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant

variable {E : Type} [Field E] [NumberField E]

theorem entB_zero (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x : (Fin N' → E) →ₗ[E] (Fin N → E)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      Loc.atN (x (Loc.eN E N' (LocE.fIdx k₀ c' n' p'))) (LocE.fIdx k₀ c n p) := by
  simp [LocE.entB, LocE.scE]

theorem intAt_entB {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ)
    {y : (Fin N' → E) →ₗ[E] (Fin N → E)} (hy : IntHom P y) (p p' : ℕ) :
    IntAt P (LocE.entB q k₀ c' n' c n 0 0 y p p') := by
  rw [entB_zero]
  have h : IntV P (Loc.eN E N' (LocE.fIdx k₀ c' n' p')) := fun l => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one P
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  unfold Loc.atN
  split_ifs
  · exact hy _ h _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem entB_add (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x y : (Fin N' → E) →ₗ[E] (Fin N → E)) (a : E) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 (x + a • y) p p' =
      LocE.entB q k₀ c' n' c n 0 0 x p p' + a * LocE.entB q k₀ c' n' c n 0 0 y p p' := by
  rw [entB_zero, entB_zero, entB_zero, LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l ∧ LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem unitV_congr {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a = redP P b) : LocE.unitV ξ a = LocE.unitV ξ b := by
  unfold LocE.unitV
  have key : ∀ u v : 𝓞 E ⧸ P.asIdeal, u = v →
      (open Classical in if h : IsUnit u then ((ξ h.unit : Kˣ) : K) else 0) =
        (open Classical in if h : IsUnit v then ((ξ h.unit : Kˣ) : K) else 0) := by
    rintro u v rfl
    rfl
  exact key _ _ h

theorem intAt_add_iff {P : HeightOneSpectrum (𝓞 E)} {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  ⟨fun h => by simpa using h.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hb), fun h => h.add hb⟩

theorem phiQ_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  intro E _ _ K _ P ξ k₀ r c' n' c n hk' hk hr' hr
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · unfold LocE.PhiQ at hx
    split_ifs at hx with h
    · rw [intHom_iff]
      intro s l
      obtain ⟨a1, a2⟩ := fIdx_fPos hk l.2
      obtain ⟨b1, b2⟩ := fIdx_fPos hk' s.2
      have := h.1 _ _ a2 b2
      rw [entB_zero, a1, b1] at this
      have e : Loc.eN E (n' + c') s.1 = Pi.single s 1 := by
        funext i
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [e] at this
      simpa [Loc.atN] using this
    · exact absurd rfl hx
  · have hq : (qOf P : E) ≠ 0 := NormalFormAtPrime.qOf_ne_zero P
    have hI := intAt_entB (qOf P) k₀ c' n' c n hy
    have e1 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p') ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p') := fun p p' => by
      rw [entB_add, intAt_add_iff ((TopStep.intAt_nat (qOf P)).mul (hI p p'))]
    have e2 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p' / (qOf P : E)) ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)) := fun p p' => by
      rw [entB_add, add_div, mul_div_cancel_left₀ _ hq, intAt_add_iff (hI p p')]
    unfold LocE.PhiQ
    split_ifs with h' h h
    rotate_left
    · exact absurd ⟨fun p p' a b => (e1 p p').1 (h'.1 p p' a b), fun p p' a b d => (e2 p p').1 (h'.2 p p' a b d)⟩ h
    · exact absurd ⟨fun p p' a b => (e1 p p').2 (h.1 p p' a b), fun p p' a b d => (e2 p p').2 (h.2 p p' a b d)⟩ h'
    · rfl
    · apply unitV_congr
      have hx : ∀ s t : Fin r, IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1) :=
        fun s t => h.1 _ _ (by have := s.2; omega) (by have := t.2; omega)
      refine (TopStep.det_int ?_).2.trans (Eq.trans ?_ (TopStep.det_int ?_).2.symm)
      · exact fun s t => (e1 _ _).2 (hx s t)
      swap
      · exact hx
      refine congrArg Matrix.det (Matrix.ext fun s t => ?_)
      change redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) s.1 t.1) =
        redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1)
      rw [entB_add, reduction_add (hx s t) ((TopStep.intAt_nat (qOf P)).mul (hI _ _)), reduction_mul (TopStep.intAt_nat (qOf P)) (hI _ _), TopStep.reduction_absNorm_eq_zero, zero_mul, add_zero]

end GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant
