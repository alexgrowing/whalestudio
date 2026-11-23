import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TeichmullerInertiaLabelCondition
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj

noncomputable section

namespace GlobalTheory.RowTie.Model

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.WeilDeligne GlobalTheory.ThetaExh

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

theorem sign_ne (ε : ℤˣ) : (0 : ℂ) ∉ ({((ε : ℤ) : ℂ)} : Multiset ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

theorem sign_inv (ε : ℤˣ) : ((ε : ℤ) : ℂ)⁻¹ = ((ε : ℤ) : ℂ) := by
  rcases Int.units_eq_one_or ε with rfl | rfl <;> simp

abbrev WDw (N : NData R H what₂) (w : PlE H) : Type := WD (E := H.E) (A := N.plOm.1 w) (w := w) (N.plOm.2 w)

def sg (N : NData R H what₂) (ε : ℤˣ) (w : PlE H) : WDw N w := WD.lpUnr _ {((ε : ℤ) : ℂ)}

theorem sg_spec (N : NData R H what₂) (ε : ℤˣ) (w : PlE H) :
    (sg N ε w).unr ∧ (sg N ε w).frobEig = {((ε : ℤ) : ℂ)} ∧ (sg N ε w).lpDim = 1 :=
  WD.lpUnr_spec _ (sign_ne ε)

theorem sg_mul (N : NData R H what₂) (ε δ : ℤˣ) (w : PlE H) :
    sg N (ε * δ) w = (sg N ε w).lpChar (sg N δ w) := by
  have hu := WD.unr_lpChar _ _ (sg_spec N ε w).1 (sg_spec N δ w).1
  rw [WD.unr_eq_lpUnr _ hu, WD.frobEig_char _ _ _ (sg_spec N ε w).1 (sg_spec N δ w).1 (sg_spec N δ w).2.1,
    (sg_spec N ε w).2.1]
  simp [sg]

set_option synthInstance.maxHeartbeats 400000 in

def wdAut (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) : NAut N where
  LP := WDw N
  lpDim := WD.lpDim
  lpZero := fun _ => WD.lpZero _
  lpSum := WD.lpSum
  lpTw := WD.lpTw
  lpChar := WD.lpChar
  lpUnr := fun _ m => WD.lpUnr _ m
  mono0 := WD.mono0
  unr := WD.unr
  frobEig := WD.frobEig
  tempered := WD.tempered
  inePol := WD.inePol
  items₂ := fun k w a => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab (τ k) (γ k w) a
  lpDim_zero := fun _ => WD.lpDim_zero _
  lpDim_sum := WD.lpDim_sum
  lpDim_tw := WD.lpDim_tw
  lpUnr_spec := fun _ m hm => WD.lpUnr_spec m hm
  unr_sum := WD.unr_sum
  monomial_sum_iff := WD.monomial_sum_iff
  frobEig_sum := fun a b _ _ => WD.frobEig_lpSum a b
  unr_tw := WD.unr_tw
  monomial_twist_iff := WD.monomial_twist_iff
  frobEig_tw := WD.frobEig_tw
  frobEig_char := fun a χ c ha hχ _ => WD.frobEig_char a χ c ha hχ
  lpDim_char := WD.lpDim_char
  unr_char := fun a χ _ => WD.unr_lpChar a χ
  monomial_char_iff := WD.monomial_char_iff
  lpZero_unr := fun _ => WD.lpZero_unr
  frobEig_zero := fun _ => WD.frobEig_zero
  lpSum_zero := WD.lpSum_zero
  lpSum_comm := WD.lpSum_comm
  lpSum_assoc := WD.lpSum_assoc
  lpTw_zero := WD.lpTw_zero
  lpTw_add := WD.lpTw_add
  lpTw_sum := WD.lpTw_sum
  unr_eq_lpUnr := WD.unr_eq_lpUnr
  unr_mono0 := WD.unr_mono0
  frobEig_ne_zero := WD.frobEig_ne_zero
  frobEig_card := fun a _ => WD.card_eig a _
  tempered_unr := WD.tempered_unr
  inePol_sum := WD.inePol_sum
  inePol_tw := WD.inePol_tw
  unr_iff_ine := WD.unr_iff_ine
  inertiaCharpoly_zero := fun k w => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩;
    WD.lab_of_lpDim_eq_zero _ _ (WD.lpDim_zero _)
  inertiaCharpoly_add := fun k w a b => haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; WD.lab_lpSum _ _ a b
  CG := fun a => {_ε : ℤˣ // a = 1}
  csd := fun _ => True
  ralg := fun {a} _ => ∀ _τ : H.E →+* ℂ, ({0} : Multiset ℂ).Nodup ∧
    ∀ z ∈ ({0} : Multiset ℂ), ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  locG := fun π w => sg N π.1 w
  locG_dim := fun π w => (sg_spec N π.1 w).2.2.trans π.2.symm
  locG_unr_ae := fun π => Filter.Eventually.of_forall fun w => (sg_spec N π.1 w).1
  tw := fun π χ => ⟨π.1 * χ.1, π.2⟩
  locG_tw := fun π χ w => sg_mul N _ _ w
  infG := fun _ _ => {0}
  infG_card := fun π _ => π.2.symm
  ralg_def := fun _ => Iff.rfl
  infG_tw := fun π χ τ s h => by
    have : (0 : ℂ) = s := Multiset.singleton_inj.1 h
    subst this; simp
  csd_tw := fun _ _ _ _ => trivial
  csd_unr := fun π w w' _ _ _ => ⟨(sg_spec N π.1 w').1, by
    rw [(sg_spec N π.1 w').2.1, (sg_spec N π.1 w).2.1, Multiset.map_singleton, sign_inv]⟩
  etaT := ⟨-1, rfl⟩
  etaTinv := ⟨-1, rfl⟩
  etaT_unr := fun w => (sg_spec N _ w).1
  etaT_inert := fun w _ => by rw [(sg_spec N _ w).2.1]; simp
  etaTinv_def := fun w => ⟨(sg_spec N _ w).1, by
    rw [(sg_spec N _ w).2.1, Multiset.map_singleton, sign_inv]⟩
  etaT_split := fun w w' _ _ a b ha hb => by
    rw [(sg_spec N _ _).2.1, Multiset.singleton_inj] at ha hb
    rw [← ha, ← hb]; simp
  plGw := A₀.plGw
  plGw_over := A₀.plGw_over
  plGw_inj := A₀.plGw_inj
  plGw_nconj := A₀.plGw_nconj
  iotaQ := fun i => isEmptyElim i
  iotaQC := fun i => isEmptyElim i
  iota_LL := fun i => isEmptyElim i
  iotaQ_alg := fun i => isEmptyElim i
  muC := fun i => isEmptyElim i
  muC_csd := fun i => isEmptyElim i
  AV := fun i => isEmptyElim i
  finAV := fun i => isEmptyElim i
  ptV := fun i => isEmptyElim i
  typeV := fun i => isEmptyElim i
  typeV_ne := fun i => isEmptyElim i
  typeV_indep := fun i => isEmptyElim i
  typeV_top := fun i => isEmptyElim i
  pt_surj := fun i => isEmptyElim i
  eig_dim := fun i => isEmptyElim i
  locV := fun i => isEmptyElim i
  satV := fun i => isEmptyElim i
  locV_unr := fun i => isEmptyElim i
  pt_loc := fun i => isEmptyElim i
  infWt := fun i => isEmptyElim i
  locW := fun i => isEmptyElim i
  satW := fun i => isEmptyElim i
  lab_loc := fun i => isEmptyElim i
  wdOf := fun i => isEmptyElim i
  wdOf_dim := fun i => isEmptyElim i
  wdOf_unr := fun i => isEmptyElim i
  wdOf_frob := fun i => isEmptyElim i
  wdOf_ine := fun i => isEmptyElim i
  wdOf_mono0 := fun i => isEmptyElim i
  IsCrysW := fun i => isEmptyElim i
  IsPotCrysW := fun i => isEmptyElim i
  IsdRW := fun i => isEmptyElim i
  jumpsW := fun i => isEmptyElim i
  wdOf_unrL := fun i => isEmptyElim i
  wdOf_mono0L := fun i => isEmptyElim i
  jumpsInf := fun i => isEmptyElim i
  locAutHodgeTateWeightsLevelZero := fun i => isEmptyElim i
  jumpsInf_def := fun i => isEmptyElim i
  locAut_hodgeTateWeightsLevelZero_def := fun i => isEmptyElim i
  chi_mu := fun i => isEmptyElim i
  kFbar := fun i => isEmptyElim i

section Inst

variable (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om)

def tie : WDTie N (wdAut N A₀ τ γ) where
  e := fun _ => Equiv.refl _
  dim := fun _ _ => rfl
  zero := fun _ => rfl
  sum := fun _ _ _ => rfl
  tw := fun _ _ _ => rfl
  char := fun _ _ _ _ => rfl
  mono0 := fun _ _ => Iff.rfl
  unr := fun _ _ => Iff.rfl
  frobEig := fun _ _ _ => rfl
  tempered := fun _ _ => Iff.rfl
  inePol := fun _ _ _ _ => rfl

theorem labTame : LabTame N (wdAut N A₀ τ γ) := fun k v a ha σ _ hσ =>
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  WD.inePol_wild_of_natDegree_lab ha hσ

theorem rankOneUnitary : RankOneUnitary (tie N A₀ τ γ) := by
  intro π w σ hσ α hα
  have hm := mem_Weil_of_isFrob (N.plOm.2 w) hσ
  have h1 : (tie N A₀ τ γ).eig w ((wdAut N A₀ τ γ).locG π w) σ = (sg N π.1 w).eig ⟨σ, hm⟩ := by
    show ((sg N π.1 w).inePol σ).roots = _
    rw [WD.inePol_of_mem _ hm]; rfl
  rw [h1, WD.eig_eq_frobEig (sg_spec N _ w).1 (deg_eq_one_iff.mpr hσ), (sg_spec N _ w).2.1,
    Multiset.mem_singleton] at hα
  subst hα
  rcases Int.units_eq_one_or π.1 with h | h <;> simp [h]

end Inst

section Laws

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w}

open TensorProduct

theorem char_sum (a b c : WD h) : (a.lpSum b).lpChar c = (a.lpChar c).lpSum (b.lpChar c) := by
  induction a using WD.ind with | hP _ a =>
  induction b using WD.ind with | hP _ b =>
  induction c using WD.ind with | hP _ c =>
  simp only [WD.lpSum_mk, WD.lpChar_mk]
  refine WD.sound ⟨TensorProduct.prodLeft ℂ ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨x, x'⟩ := x; simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | tmul x y => obtain ⟨x, x'⟩ := x; simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem char_tw_left (a c : WD h) (s : ℝ) : (a.lpTw s).lpChar c = (a.lpChar c).lpTw s := by
  induction a using WD.ind with | hP _ a =>
  induction c using WD.ind with | hP _ c =>
  simp only [WD.lpTw_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp [TensorProduct.map_smul_left]

theorem char_tw_right (a c : WD h) (s : ℝ) : a.lpChar (c.lpTw s) = (a.lpChar c).lpTw s := by
  induction a using WD.ind with | hP _ a =>
  induction c using WD.ind with | hP _ c =>
  simp only [WD.lpTw_mk, WD.lpChar_mk]
  refine WD.sound ⟨.refl _ _, fun σ v => ?_, fun v => rfl⟩
  simp [TensorProduct.map_smul_right]

theorem char_assoc (a b c : WD h) : (a.lpChar b).lpChar c = a.lpChar (b.lpChar c) := by
  induction a using WD.ind with | hP _ a =>
  induction b using WD.ind with | hP _ b =>
  induction c using WD.ind with | hP _ c =>
  simp only [WD.lpChar_mk]
  refine WD.sound ⟨TensorProduct.assoc ℂ _ _ _, fun σ v => ?_, fun v => ?_⟩
  · have : (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ ((a.tensor b).tensor c).ρ σ =
        (a.tensor (b.tensor c)).ρ σ ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap :=
      TensorProduct.ext_threefold fun x y z => by simp
    exact LinearMap.congr_fun this v
  · have : (TensorProduct.assoc ℂ _ _ _).toLinearMap ∘ₗ ((a.tensor b).tensor c).N =
        (a.tensor (b.tensor c)).N ∘ₗ (TensorProduct.assoc ℂ _ _ _).toLinearMap :=
      TensorProduct.ext_threefold fun x y z => by simp [add_tmul, tmul_add, add_assoc]
    exact LinearMap.congr_fun this v

theorem char_one (a : WD h) : a.lpChar (WD.lpUnr h {1}) = a := by
  have h1 : WD.lpUnr h {1} = WD.mk (WDRep.diag h fun _ : Fin 1 => 1) := by
    rw [WD.unr_eq_lpUnr (WD.mk (WDRep.diag h fun _ : Fin 1 => 1)) ((WD.unr_mk _).mpr (WDRep.unr_diag _)),
      WD.frobEig_diag]
    simp
  induction a using WD.ind with | hP _ a =>
  rw [h1, WD.lpChar_mk]
  refine WD.sound ⟨(TensorProduct.congr (.refl _ _) (LinearEquiv.funUnique (Fin 1) ℂ ℂ)).trans
    (TensorProduct.rid ℂ _), fun σ v => ?_, fun v => ?_⟩
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  · induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp
    | add x y hx hy => simp only [map_add, hx, hy]

end Laws

section Gen

variable {N : NData R H what₂} {A : NAut N}

theorem tie_lpUnr (T : WDTie N A) (w : PlE H) (m : Multiset ℂ) (hm : (0 : ℂ) ∉ m) :
    T.e w (A.lpUnr w m) = WD.lpUnr _ m := by
  obtain ⟨h1, h2, -⟩ := A.lpUnr_spec w m hm
  rw [WD.unr_eq_lpUnr _ ((T.unr w _).1 h1), ← T.frobEig w _ h1, h2]

theorem charLaws_of_tie (T : WDTie N A) : CharLaws N A := by
  intro w a b χ χ' s h1 h2
  have h3 : A.lpDim (A.lpTw χ s) = 1 := by rw [A.lpDim_tw, h1]
  have h4 : A.lpDim (A.lpChar χ χ') = 1 := by rw [A.lpDim_char _ _ h2, h1]
  have h5 : A.lpDim (A.lpUnr w {1}) = 1 := (A.lpUnr_spec w {1} (by simp)).2.2
  refine ⟨(T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_, (T.e w).injective ?_,
    (T.e w).injective ?_⟩
  · rw [T.char _ _ _ h1, T.sum, T.sum, T.char _ _ _ h1, T.char _ _ _ h1, char_sum]
  · rw [T.char _ _ _ h1, T.tw, T.tw, T.char _ _ _ h1, char_tw_left]
  · rw [T.char _ _ _ h3, T.tw, T.tw, T.char _ _ _ h1, char_tw_right]
  · rw [T.char _ _ _ h2, T.char _ _ _ h1, T.char _ _ _ h4, T.char _ _ _ h2, char_assoc]
  · rw [T.char _ _ _ h5, tie_lpUnr T w _ (by simp), char_one]

theorem exists_not_mono0 (T : WDTie N A) (w : PlE H) : ∃ a : A.LP w, ¬ A.mono0 a ∧ A.tempered a ∧ A.lpDim a = 2 := by
  refine ⟨(T.e w).symm (WD.lpSp _ 2), ?_, ?_, ?_⟩
  · rw [T.mono0, Equiv.apply_symm_apply]; exact WD.not_mono0_lpSp le_rfl
  · rw [T.tempered, Equiv.apply_symm_apply]; exact WD.tempered_lpSp 2
  · rw [← T.dim, Equiv.apply_symm_apply]; exact WD.lpDim_lpSp 2

theorem not_isobaricRigid {a : ℕ} (ha : 1 ≤ a) (π π' : A.CG a) {s : ℝ} (hs : s ≠ 0)
    (h : ∀ w, A.locG π' w = A.lpTw (A.locG π w) s) : ¬ IsobaricRigid N A := by
  intro hr
  have := hr [(⟨a, π⟩, s)] [(⟨a, π'⟩, 0)] (by simpa) (by simpa)
    (Filter.Eventually.of_forall fun w => by simp [twSum, A.lpTw_zero, h])
  rw [List.perm_singleton] at this
  simp at this
  exact hs this.2

end Gen

theorem infinite_places (K : Type) [Field K] [NumberField K] : Infinite (HeightOneSpectrum (𝓞 K)) := by
  have h : ∀ p : Nat.Primes, ∃ la : HeightOneSpectrum (𝓞 K), la.asIdeal.comap (algebraMap ℤ (𝓞 K)) =
      Ideal.span {((p : ℕ) : ℤ)} := fun p => by
    haveI : Fact (p : ℕ).Prime := ⟨p.2⟩
    haveI : (Ideal.span {((p : ℕ) : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
    obtain ⟨M, hM, hc⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 K) (Ideal.span {((p : ℕ) : ℤ)})
      (by rw [(RingHom.injective_iff_ker_eq_bot _).1 (algebraMap ℤ (𝓞 K)).injective_int]; exact bot_le)
    exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField K)⟩, hc⟩
  choose f hf using h
  refine Infinite.of_injective f fun p q hpq => ?_
  have e : Ideal.span {((p : ℕ) : ℤ)} = Ideal.span {((q : ℕ) : ℤ)} := by rw [← hf p, ← hf q, hpq]
  have := Int.associated_iff_natAbs.1 (Ideal.span_singleton_eq_span_singleton.1 e)
  exact Subtype.ext (by simpa using this)

section Rigid

variable (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om)

def ev (w : PlE H) (p : (Σ a : ℕ, {_ε : ℤˣ // a = 1}) × ℝ) : ℂ :=
  ((p.1.2.1 : ℤ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((p.2 : ℝ) : ℂ)

theorem ev_inj (w : PlE H) : Function.Injective (ev w) := by
  rintro ⟨⟨_, ε, rfl⟩, s⟩ ⟨⟨_, δ, rfl⟩, t⟩ h
  have hq : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast one_lt_normV w
  have hn : ∀ (ε : ℤˣ) (s : ℝ), ‖((ε : ℤ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ)‖ = ((normV w : ℕ) : ℝ) ^ s := by
    intro ε s
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos (by have := one_lt_normV w; omega)]
    rcases Int.units_eq_one_or ε with rfl | rfl <;> simp
  have h' := congrArg norm h
  simp only [ev, hn] at h'
  have hst : s = t := (Real.rpow_right_inj (zero_lt_one.trans hq) hq.ne').1 h'
  subst hst
  have h0 : ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) ≠ 0 := by
    intro h0
    have := hn 1 s
    rw [h0] at this
    have h2 := Real.rpow_pos_of_pos (zero_lt_one.trans hq) s
    simp at this
    linarith
  have h1 := mul_right_cancel₀ h0 h
  have h2 : ε = δ := Units.ext (by exact_mod_cast h1)
  subst h2
  rfl

theorem twSum_spec (w : PlE H) (L : List ((Σ a : ℕ, (wdAut N A₀ τ γ).CG a) × ℝ)) :
    WD.unr (twSum N (wdAut N A₀ τ γ) L w) ∧
      WD.frobEig (twSum N (wdAut N A₀ τ γ) L w) = ((L.map (ev w) : List ℂ) : Multiset ℂ) := by
  induction L with
  | nil => exact ⟨WD.lpZero_unr, WD.frobEig_zero⟩
  | cons p L ih =>
    have e : twSum N (wdAut N A₀ τ γ) (p :: L) w =
      WD.lpSum (WD.lpTw (sg N p.1.2.1 w) p.2) (twSum N (wdAut N A₀ τ γ) L w) := rfl
    rw [e]
    refine ⟨(WD.unr_sum _ _).2 ⟨(WD.unr_tw _ _).2 (sg_spec N _ w).1, ih.1⟩, ?_⟩
    refine (WD.frobEig_lpSum _ _).trans ?_
    refine (congrArg₂ (· + ·) ((WD.frobEig_tw _ _ (sg_spec N _ w).1).trans
      (congrArg _ (sg_spec N _ w).2.1)) ih.2).trans ?_
    rfl

theorem isobaricRigid : IsobaricRigid N (wdAut N A₀ τ γ) := by
  intro L L' _ _ h
  haveI : Infinite (PlE H) := infinite_places H.E
  obtain ⟨w, hw⟩ := h.exists
  have h1 := (twSum_spec N A₀ τ γ w L).2
  rw [hw, (twSum_spec N A₀ τ γ w L').2, Multiset.coe_eq_coe] at h1
  exact ((List.map_perm_map_iff (ev_inj w)).1 h1).symm

end Rigid

theorem label_full (N : NData R H what₂) [IsEmpty N.Loc] (A₀ : NAut N)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E N.Om) (k : Fin 2) (w : PlE H)
    (hL : haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩; TeichmullerInertiaLabelCondition (N.plOm.1 w) w (τ k) (γ k w)) :
    (wdAut N A₀ τ γ).items₂ k w (WD.lpSp _ 2) = (X - 1) ^ 2 :=
  haveI : Fact (H.g k).Prime := ⟨H.g_prime k⟩
  WD.lab_lpSp hL 2

theorem exists_tie (H : Host R) (what₂ : Rows.Data R) (h : Examples₂.NHyp H what₂)
    (τ : ∀ k, Fb (H.g k) (H.g_prime k) →* ℂ) (γ : Fin 2 → PlE H → G H.E (Examples₂.ndToy H what₂ h).Om) :
    ∃ (A : NAut (Examples₂.ndToy H what₂ h)) (T : WDTie _ A), CharLaws _ A ∧ LabTame _ A ∧ RankOneUnitary T ∧
      IsobaricRigid _ A :=
  haveI : IsEmpty (Examples₂.ndToy H what₂ h).Loc := inferInstanceAs (IsEmpty Empty)
  ⟨wdAut _ (Examples₂.nautToy H what₂ h) τ γ, tie _ _ _ _, charLaws_of_tie (tie _ _ _ _),
    labTame _ _ _ _, rankOneUnitary _ _ _ _, isobaricRigid _ _ _ _⟩

end GlobalTheory.RowTie.Model
