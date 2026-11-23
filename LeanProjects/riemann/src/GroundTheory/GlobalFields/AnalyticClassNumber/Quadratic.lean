import Mathlib
import GroundTheory.GlobalFields.AnalyticClassNumber.DirichletHeckeCorrespondence
import GroundTheory.GlobalFields.Artin.OneDimL
import GroundTheory.GlobalFields.Artin.OneDimExistence
import GroundTheory.GlobalFields.Artin.AbelianHecke
import GroundTheory.GlobalFields.Artin.Regular
import GroundTheory.GlobalFields.AnalyticClassNumber.ClassNumberFormula
import GroundTheory.LocalFields.ArtinConductor
set_option maxSynthPendingDepth 1

noncomputable section

open NumberField IsDedekindDomain Filter Topology Complex NumberField.InfinitePlace NumberField.Units
open scoped Real

namespace GroundTheory.Global

namespace Quadratic

section Two

variable {G : Type*} [Group G] [Finite G]

theorem eq_of_ne_one_of_card_eq_two (hG : Nat.card G = 2) {σ τ : G} (hσ : σ ≠ 1) (hτ : τ ≠ 1) :
    σ = τ := by
  classical
  have := Fintype.ofFinite G
  by_contra h
  have hcard : ({1, σ, τ} : Finset G).card = 3 := by
    rw [Finset.card_insert_of_notMem, Finset.card_pair h]
    simp [Ne.symm hσ, Ne.symm hτ]
  have hle := Finset.card_le_univ ({1, σ, τ} : Finset G)
  rw [hcard, Fintype.card_eq_nat_card, hG] at hle
  omega

omit [Finite G] in

theorem mul_self_eq_one_of_card_eq_two (hG : Nat.card G = 2) (σ : G) : σ * σ = 1 := by
  have h := pow_card_eq_one' (G := G) (x := σ)
  rwa [hG, pow_two] at h

theorem exists_ne_one_of_card_eq_two (hG : Nat.card G = 2) : ∃ σ : G, σ ≠ 1 := by
  have : Nontrivial G := Finite.one_lt_card_iff_nontrivial.1 (by omega)
  exact exists_ne 1

open Classical in

def signChar (hG : Nat.card G = 2) : G →* ℂˣ where
  toFun σ := if σ = 1 then 1 else -1
  map_one' := if_pos rfl
  map_mul' σ τ := by
    by_cases hσ : σ = 1
    · subst hσ
      simp
    by_cases hτ : τ = 1
    · subst hτ
      simp
    obtain rfl := eq_of_ne_one_of_card_eq_two hG hσ hτ
    simp [mul_self_eq_one_of_card_eq_two hG, hσ]

theorem signChar_apply_of_ne_one (hG : Nat.card G = 2) {σ : G} (hσ : σ ≠ 1) :
    signChar hG σ = -1 := by
  classical
  simp [signChar, hσ]

theorem signChar_ne_one (hG : Nat.card G = 2) : signChar hG ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_ne_one_of_card_eq_two hG
  intro h
  have h1 := signChar_apply_of_ne_one hG hσ
  rw [h, MonoidHom.one_apply] at h1
  have h2 := congrArg (fun u : ℂˣ ↦ (u : ℂ)) h1
  norm_num at h2

end Two

variable (K : Type) [Field K] [NumberField K] [Algebra.IsQuadraticExtension ℚ K]

theorem card_gal : Nat.card Gal(K/ℚ) = 2 := by
  rw [IsGalois.card_aut_eq_finrank, Algebra.IsQuadraticExtension.finrank_eq_two]

def galChar : Gal(K/ℚ) →* ℂˣ :=
  signChar (card_gal K)

theorem galChar_apply_of_ne_one {σ : Gal(K/ℚ)} (hσ : σ ≠ 1) : galChar K σ = -1 :=
  signChar_apply_of_ne_one (card_gal K) hσ

theorem galChar_one_apply : galChar K 1 = 1 :=
  map_one _

theorem galChar_ne_one : galChar K ≠ 1 :=
  signChar_ne_one (card_gal K)

def heckeChar : HeckeCharacter ℚ :=
  heckeCharacterOfChar (galChar K)

theorem isOfFinOrder_heckeChar : IsOfFinOrder (heckeChar K) :=
  isOfFinOrder_heckeCharacterOfChar _

theorem heckeChar_ne_one : heckeChar K ≠ 1 := fun h ↦
  galChar_ne_one K (eq_one_of_heckeCharacterOfChar_eq_one _ h)

def kroneckerData : DirichletHecke.PrimitiveDirichletCharacter :=
  DirichletHecke.finiteOrderEquiv.symm ⟨heckeChar K, isOfFinOrder_heckeChar K⟩

def level : ℕ :=
  ((kroneckerData K).1 : ℕ)

instance : NeZero (level K) :=
  ⟨(kroneckerData K).1.ne_zero⟩

def kronecker : DirichletCharacter ℂ (level K) :=
  (kroneckerData K).2.1

theorem isPrimitive_kronecker : (kronecker K).IsPrimitive :=
  (kroneckerData K).2.2

theorem heckeCharacter_kronecker : DirichletHecke.heckeCharacter (kronecker K) = heckeChar K := by
  have h := DirichletHecke.coe_finiteOrderEquiv_apply (kroneckerData K)
  have h2 : DirichletHecke.finiteOrderEquiv (kroneckerData K) =
      ⟨heckeChar K, isOfFinOrder_heckeChar K⟩ :=
    Equiv.apply_symm_apply _ _
  rw [h2] at h
  exact h.symm

theorem kronecker_ne_one : kronecker K ≠ 1 := by
  intro h
  apply heckeChar_ne_one K
  rw [← heckeCharacter_kronecker K, h]
  ext x
  rw [DirichletHecke.coe_heckeCharacter_apply]
  refine (MulChar.one_apply ((Units.isUnit _).map _)).trans ?_
  rfl

theorem dedekindZeta_rat {s : ℂ} (hs : 1 < s.re) : dedekindZeta ℚ s = riemannZeta s := by
  rw [← LSeries_one_eq_riemannZeta hs, dedekindZeta]
  refine LSeries_congr (fun {n} _ ↦ ?_) s
  rw [Pi.one_apply, Nat.cast_eq_one, Nat.card_eq_one_iff_exists]
  refine ⟨⟨Ideal.span {(n : 𝓞 ℚ)}, DirichletHecke.absNorm_span_natCast n⟩, fun I ↦ ?_⟩
  exact Subtype.ext (DirichletHecke.eq_span_of_absNorm_eq I.2)

theorem character_leftRegular :
    (Representation.leftRegular ℂ Gal(K/ℚ)).character =
      1 + fun σ ↦ ((galChar K σ : ℂˣ) : ℂ) := by
  classical
  have := Fintype.ofFinite Gal(K/ℚ)
  funext σ
  rw [GroundTheory.LocalField.character_leftRegular, Fintype.card_eq_nat_card, card_gal, Pi.add_apply,
    Pi.one_apply]
  by_cases hσ : σ = 1
  · subst hσ
    rw [if_pos rfl, galChar_one_apply]
    norm_num
  · rw [if_neg hσ, galChar_apply_of_ne_one K hσ]
    norm_num

theorem dedekindZeta_eq_mul {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (kronecker K) s := by
  have := Fintype.ofFinite Gal(K/ℚ)
  rw [← Artin.artinL_leftRegular (K := ℚ) hs, character_leftRegular, artinL_add _ _ hs,
    artinL_one hs, artinL_eq_LFunction _ hs, dedekindZeta_rat hs,
    show heckeCharacterOfChar (galChar K) = DirichletHecke.heckeCharacter (kronecker K) from
      (heckeCharacter_kronecker K).symm,
    DirichletHecke.LFunction_heckeCharacter _ (isPrimitive_kronecker K) hs]

theorem continuedDedekindZeta_eq_mul {s : ℂ} (hs : s ≠ 1) :
    continuedDedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction (kronecker K) s := by
  have hU : IsOpen ({1}ᶜ : Set ℂ) := isOpen_compl_singleton
  have hpc : IsPreconnected ({1}ᶜ : Set ℂ) :=
    DirichletHecke.isPreconnected_compl_of_countable (Set.countable_singleton 1)
  have hf : AnalyticOnNhd ℂ (continuedDedekindZeta K) {1}ᶜ :=
    (differentiableOn_continuedDedekindZeta K).analyticOnNhd hU
  have hg : AnalyticOnNhd ℂ (fun z ↦ riemannZeta z * DirichletCharacter.LFunction (kronecker K) z)
      {1}ᶜ :=
    (DifferentiableOn.mul (fun z hz ↦ (differentiableAt_riemannZeta hz).differentiableWithinAt)
      (DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).differentiableOn).analyticOnNhd
      hU
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg hpc (show (2 : ℂ) ∈ ({1}ᶜ : Set ℂ) by norm_num)
    ?_ hs
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (1 : ℝ) < (2 : ℂ).re by norm_num)] with z hz
  rw [continuedDedekindZeta_eq K hz, dedekindZeta_eq_mul K hz]

theorem LFunction_kronecker_one :
    DirichletCharacter.LFunction (kronecker K) 1 = (dedekindZeta_residue K : ℂ) := by
  refine tendsto_nhds_unique ?_ (tendsto_sub_one_mul_continuedDedekindZeta K)
  have hc := (DirichletCharacter.differentiable_LFunction (kronecker_ne_one K)).continuous.continuousAt
    (x := 1)
  have h := riemannZeta_residue_one.mul (hc.tendsto.mono_left nhdsWithin_le_nhds)
  rw [one_mul] at h
  refine h.congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
  show _ = (s - 1) * continuedDedekindZeta K s
  rw [continuedDedekindZeta_eq_mul K hs, mul_assoc]

theorem LFunction_kronecker_one_pos :
    0 < (DirichletCharacter.LFunction (kronecker K) 1).re ∧
      (DirichletCharacter.LFunction (kronecker K) 1).im = 0 := by
  rw [LFunction_kronecker_one, Complex.ofReal_re, Complex.ofReal_im]
  exact ⟨dedekindZeta_residue_pos K, rfl⟩

theorem nrRealPlaces_add_two_mul : nrRealPlaces K + 2 * nrComplexPlaces K = 2 := by
  rw [card_add_two_mul_card_eq_rank, Algebra.IsQuadraticExtension.finrank_eq_two]

theorem places_of_discr_neg (hd : discr K < 0) : nrRealPlaces K = 0 ∧ nrComplexPlaces K = 1 := by
  have h2 := nrRealPlaces_add_two_mul K
  have hs := sign_discr K
  rw [Int.sign_eq_neg_one_of_neg hd] at hs
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h
  · rw [h, pow_zero] at hs
    norm_num at hs
  · omega

theorem places_of_discr_pos (hd : 0 < discr K) : nrRealPlaces K = 2 ∧ nrComplexPlaces K = 0 := by
  have h2 := nrRealPlaces_add_two_mul K
  have hs := sign_discr K
  rw [Int.sign_eq_one_of_pos hd] at hs
  rcases (by omega : nrComplexPlaces K = 0 ∨ nrComplexPlaces K = 1) with h | h
  · omega
  · rw [h, pow_one] at hs
    norm_num at hs

theorem regulator_eq_one_of_card_eq_one {F : Type*} [Field F] [NumberField F]
    (h : nrRealPlaces F + nrComplexPlaces F = 1) : regulator F = 1 := by
  have hcard : Fintype.card (InfinitePlace F) = 1 := by
    rw [card_eq_nrRealPlaces_add_nrComplexPlaces, h]
  have hrank : rank F = 0 := by
    rw [rank, hcard]
  classical
  have : IsEmpty (Fin (rank F)) := by
    rw [hrank]
    infer_instance
  have : IsEmpty {w : InfinitePlace F // w ≠ dirichletUnitTheorem.w₀} :=
    ⟨fun w ↦ w.2 (Fintype.card_le_one_iff.1 hcard.le _ _)⟩
  rw [regulator_eq_det', Matrix.det_isEmpty, abs_one]

set_option backward.isDefEq.respectTransparency false in

theorem torsionOrder_eq_two_of_nrRealPlaces_pos {F : Type*} [Field F] [NumberField F]
    (h : 0 < nrRealPlaces F) : torsionOrder F = 2 := by
  classical
  let := Fintype.ofFinite (torsion F)
  rw [torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2 ⟨1, ⟨-1, neg_one_mem_torsion⟩,
    by simp [← Subtype.coe_ne_coe], Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  by_cases! hc : 2 < orderOf (x : (𝓞 F)ˣ)
  · rw [← orderOf_units, ← orderOf_submonoid] at hc
    linarith [IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc (IsPrimitiveRoot.orderOf (x.1 : F))]
  · interval_cases hi : orderOf (x : (𝓞 F)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact Or.intro_left _ (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, ← Units.val_inj, Units.val_neg, Units.val_one, hi]

theorem classNumber_eq_of_discr_neg (hd : discr K < 0) :
    (classNumber K : ℂ) = torsionOrder K * Real.sqrt |(discr K : ℝ)| *
      DirichletCharacter.LFunction (kronecker K) 1 / (2 * π) := by
  obtain ⟨h1, h2⟩ := places_of_discr_neg K hd
  have hR : regulator K = 1 := regulator_eq_one_of_card_eq_one (by omega)
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hR]
  have hd0 : ((Real.sqrt |(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2
    (Real.sqrt_pos.2 (abs_pos.2 (Int.cast_ne_zero.2 (discr_ne_zero K)))).ne'
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (torsionOrder_ne_zero K)
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 Real.pi_ne_zero
  push_cast
  field_simp

theorem classNumber_mul_regulator_eq_of_discr_pos (hd : 0 < discr K) :
    ((classNumber K * regulator K : ℝ) : ℂ) = Real.sqrt (discr K : ℝ) *
      DirichletCharacter.LFunction (kronecker K) 1 / 2 := by
  obtain ⟨h1, h2⟩ := places_of_discr_pos K hd
  have hw : torsionOrder K = 2 := torsionOrder_eq_two_of_nrRealPlaces_pos (by omega)
  have hd' : (0 : ℝ) < discr K := Int.cast_pos.2 hd
  rw [LFunction_kronecker_one, dedekindZeta_residue_def, h1, h2, hw, abs_of_pos hd']
  have hd0 : ((Real.sqrt (discr K : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.2 (Real.sqrt_pos.2 hd').ne'
  push_cast
  field_simp

end Quadratic

end GroundTheory.Global
