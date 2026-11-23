import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PhiTopAgree
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymLevelTestFunctionsAgreeRationalPointsStatement
open NumberField IsDedekindDomain MeasureTheory ValuativeRel Matrix Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymBridge

noncomputable section
namespace GlobalTheory.SymBridge.PsiStep

section Red
variable {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E))

theorem q_mem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := Ideal.absNorm_mem P.asIdeal

theorem q_ne_zero : ((qOf P : ℕ) : E) ≠ 0 := by
  have h : qOf P ≠ 0 := by
    unfold qOf
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact P.ne_bot
  exact_mod_cast h

theorem intAt_q : IntAt P (qOf P : E) := by
  have := IntAt.coe P ((qOf P : ℕ) : 𝓞 E)
  rwa [map_natCast] at this

theorem reduction_natCast_eq_zero : redP P (qOf P : E) = 0 := by
  have := reduction_coe P ((qOf P : ℕ) : 𝓞 E)
  rw [map_natCast] at this
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.2 (q_mem P)

theorem pow_red (k : ℕ) : IntAt P ((qOf P : E) ^ (k + 1)) ∧ redP P ((qOf P : E) ^ (k + 1)) = 0 := by
  induction k with
  | zero =>
    rw [zero_add, pow_one]
    exact ⟨intAt_q P, reduction_natCast_eq_zero P⟩
  | succ k ih =>
    rw [pow_succ]
    exact ⟨ih.1.mul (intAt_q P), by rw [reduction_mul ih.1 (intAt_q P), ih.2, zero_mul]⟩

theorem reduction_one' : redP P (1 : E) = 1 := by
  have := reduction_coe P 1
  rwa [map_one, map_one] at this

theorem valuation_one₂ : LocE.vP P (qOf P) (1 : E) = 0 := by
  have hq0 := q_ne_zero P
  have hex : ∃ z : ℤ, IsUnit (redP P ((1 : E) / (qOf P : E) ^ z)) :=
    ⟨0, by rw [zpow_zero, div_one, reduction_one']; exact isUnit_one⟩
  have hspec : IsUnit (redP P ((1 : E) / (qOf P : E) ^ LocE.vP P (qOf P) (1 : E))) := by
    unfold LocE.vP
    exact Classical.epsilon_spec hex
  by_contra hne
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg (LocE.vP P (qOf P) (1 : E))
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, zpow_natCast] at hspec
    by_cases hI' : IntAt P ((1 : E) / (qOf P : E) ^ (k' + 1))
    · have e : (qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1)) = 1 := by field_simp
      have h0 : redP P ((qOf P : E) ^ (k' + 1) * (1 / (qOf P : E) ^ (k' + 1))) = 0 := by
        rw [reduction_mul (pow_red P k').1 hI', (pow_red P k').2, zero_mul]
      rw [e, reduction_one'] at h0
      exact one_ne_zero h0
    · rw [reduction_eq_zero_of_not_integral P hI'] at hspec
      exact not_isUnit_zero hspec
  · obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    rw [hk, _root_.zpow_neg, zpow_natCast, div_inv_eq_mul, one_mul, (pow_red P k').2] at hspec
    exact not_isUnit_zero hspec

theorem locChar_one_ne {K : Type} [Field K] (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) :
    LocE.locChar (qOf P) cq χ (1 : E) ≠ 0 := by
  unfold LocE.locChar
  rw [valuation_one₂, zpow_zero, zpow_zero, one_mul, div_one]
  unfold LocE.unitV
  rw [dif_pos (by rw [reduction_one']; exact isUnit_one)]
  exact Units.ne_zero _

end Red

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Mat
variable {E : Type} [Field E]

theorem joinCol_apply {n' c' n c : ℕ} (x₀ : HomE E n' n) (y' : Sp E n) (v : Fin (n' + c') → E) (i : Fin n) :
    joinCol (c' := c') (c := c) x₀ y' v (Fin.castAdd c i) =
      x₀ (fun l => v (Fin.castAdd c' l)) i + atNL E (n' + c') n' v * y' i := by
  simp [joinCol, Loc.inX, LinearMap.funLeft]
  rfl

end Mat

theorem om_one_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ : kˣ →* ℂˣ) (Φ : Matrix b a k → ℂ) :
    om μ 1 1 Φ = Φ := by
  funext x
  simp [om, nabs]

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

theorem withCol_toLoc {E k : Type} [Field E] [NumberField E] [StarRing E]
    [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : E →+* k)
    {A B : Type} {n' n c' c : ℕ} (e : A ≃ Fin n) (e' : B ≃ Fin n') (hc' : c' = 0 + 1) (hc : c = 0)
    (x₀ : HomE E n' n) (y' : Sp E n) :
    withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι ((e.sumCongr (finCongr hc.symm)).trans finSumFinEquiv) ((e'.sumCongr (finCongr hc'.symm)).trans finSumFinEquiv)
        (joinCol (c' := c') (c := c) x₀ y') := by
  subst hc' hc
  ext (r | r) (j | j)
  · simp only [withCol, fromBlocks_apply₁₁, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl,
      finSumFinEquiv_apply_left, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.castAdd (0 + 1) (e' j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = Pi.single (e' j) 1 := by
      funext l
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.castAdd (0 + 1) (e' j)) 1) = 0 := by
      have hj := (e' j).isLt
      unfold atNL
      rw [dif_pos (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_castAdd]
      rw [if_neg (by omega)]
    rw [h1, h2, zero_mul, add_zero]
  · simp only [withCol, fromBlocks_apply₁₂, toLoc, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, joinCol_apply]
    have h1 : (fun l : Fin n' => (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) (1 : E) : Fin (n' + (0 + 1)) → E)
        (Fin.castAdd (0 + 1) l)) = 0 := by
      funext l
      have hl := l.isLt
      simp only [Pi.single_apply, Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd, Pi.zero_apply]
      rw [if_neg (by omega)]
    have h2 : atNL E (n' + (0 + 1)) n' (Pi.single (Fin.natAdd n' (finCongr (rfl : 0 + 1 = 0 + 1) j)) 1) = 1 := by
      unfold atNL
      rw [dif_pos (by omega)]
      simp only [LinearMap.coe_proj, Function.eval, Pi.single_apply, Fin.ext_iff, Fin.val_natAdd]
      rw [if_pos (by omega)]
    rw [h1, map_zero, Pi.zero_apply, h2, one_mul]
    rw [zero_add (y' (e r))]
    rfl
  · exact r.elim0
  · exact r.elim0

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge.PsiStep

section Main
variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S₀ : Set ℕ}
  (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu)

theorem omPhi_one_one (i : ℕ) (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu cst i P 1 1 x = PhiAt Ch mu cst.sharp i P.1 x := by
  have hm : muAt Ch sel mu cst i P 1 ≠ 0 := by
    unfold muAt
    exact locChar_one_ne _ _ _
  unfold omPhi Loc.om
  rw [map_one, map_one, Units.val_one, valuation_one₂]
  rw [mul_inv_cancel₀ hm]
  simp only [neg_zero, zero_mul, zpow_zero, one_mul]
  rfl

end Main

end GlobalTheory.SymBridge.PsiStep

namespace GlobalTheory.SymBridge

open PsiStep in

theorem psiAgree_of_atType : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S₀ : Set ℕ) (mu : Tup X.F X.E X.K S₀) (cst : LocCst X (rowSG Pr sel mu)) (σ₀ : X.K →+* ℂ) (P : rowSG Pr sel mu) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : X.E →+* k) (s : ℕ) (S : SymData k s R.k) [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → AtType Ch sel mu cst σ₀ P ι S → PsiAgree Ch sel mu cst σ₀ P ι S := by
  intro X Pr R Ch sel S₀ mu cst σ₀ P k _ _ _ _ ι s S _ _ ν _ hA e' e he' he
  have hc1 : cOf R s = 0 + 1 := by unfold cOf; rw [hA.steps]; omega
  have hc0 : cOf R (s + 1) = 0 := by unfold cOf; rw [hA.steps]; omega
  have hrS : R.rS = S.ρ := by
    have := S.odd
    unfold Ranks.rS; rw [hA.steps]; omega
  have hr : R.r = R.k + s + 1 := by unfold Ranks.r; rw [hA.steps]; omega
  let E' : XIx (Fin R.k) (Fin R.t) s ⊕ Fin (0 + 1) ≃ Fin (R.N s + cOf R s) :=
    (e'.sumCongr (finCongr hc1.symm)).trans finSumFinEquiv
  let E₁ : XIx (Fin R.k) (Fin R.t) (s + 1) ⊕ Fin 0 ≃ Fin (R.N (s + 1) + cOf R (s + 1)) :=
    (e.sumCongr (finCongr hc0.symm)).trans finSumFinEquiv
  have hE' : IsOrd (yPos xPos (R.N s)) E' := by
    rintro (a | a)
    · simp [E', yPos, he' a]
    · simp [E', yPos]
  have hE₁ : IsOrd (yPos xPos (R.N (s + 1))) E₁ := by
    rintro (a | a)
    · simp [E₁, yPos, he a]
    · exact a.elim0
  have hPhi := GlobalTheory.T.symLevelTestFunctions_agree_rationalPoints X.E X.K k P.1 (qOf P.1) ι σ₀ (psi0P Ch P.1) (chiP Ch P.1) s R.k S hA.tie
    R.t s 0 rfl (R.N s) (cOf R s) (R.N (s + 1)) (cOf R (s + 1)) rfl rfl hc1 hc0 E' E₁ hE' hE₁
  refine ⟨1, one_ne_zero, fun x₀ y' => ?_⟩
  have hmat : withCol (toLoc ι e e' x₀) (fun a => ι (y' (e a))) =
      toLoc ι E₁ E' (joinCol (c' := cOf R s) (c := cOf R (s + 1)) x₀ y') := by
    exact withCol_toLoc ι e e' hc1 hc0 x₀ y'
  rw [one_mul, Chain.Psi, om_one_one, hmat, hPhi, PsiAt, omPhi_one_one]
  unfold PhiAt
  rw [if_pos hA.mem, if_pos hA.sharp, hrS, hr]

end GlobalTheory.SymBridge
