import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.SandZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodDiscExtensionTateElement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompleteSpaceFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormCoeffSubstLe
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocAinfUntiltEpsOneEqZeta

noncomputable section

namespace GlobalTheory.HWL.Cmp.OpenDisc

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.HWL.Cmp

variable {l : ℕ} [Fact l.Prime] {LL : FinExt l}

theorem norm_sub_one_lt {ζ : ↥LL.1} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) : ‖((ζ : Om l)) - 1‖ < 1 := by
  obtain ⟨j, hj⟩ := h
  have hl : l.Prime := Fact.out
  have hint : IsIntegral ℤ_[l] ζ :=
    IsIntegral.of_pow (pow_pos hl.pos j) (by rw [hj.pow_eq_one]; exact isIntegral_one)
  set z : ↥(OL LL) := ⟨ζ, hint⟩ with hz
  obtain ⟨r, hr⟩ : ∃ r : ↥(OL LL), ((z - 1) + 1) ^ l ^ j = (z - 1) ^ l ^ j + 1 ^ l ^ j + (l : ↥(OL LL)) * r := by
    obtain ⟨r, hr⟩ := exists_add_pow_prime_pow_eq hl (z - 1) 1 j
    exact ⟨_, by rw [hr, mul_assoc, mul_assoc]⟩
  have h1 := congrArg (algebraMap ↥(OL LL) ↥LL.1) hr
  have hzz : algebraMap ↥(OL LL) ↥LL.1 z = ζ := rfl
  simp only [sub_add_cancel, map_pow, map_add, map_mul, map_sub, map_one, map_natCast, hzz, hj.pow_eq_one,
    one_pow] at h1
  have h2 : (ζ - 1) ^ l ^ j = -((l : ↥LL.1) * algebraMap ↥(OL LL) ↥LL.1 r) := by linear_combination -h1
  have h3 : ‖(l : ↥LL.1)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] ↥LL.1), norm_algebraMap']
    exact Padic.norm_p_lt_one
  have h4 : ‖ζ - 1‖ ^ l ^ j < 1 := by
    rw [← norm_pow, h2, norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) h3 (norm_integer_le_one r)
  exact lt_of_pow_lt_pow_left₀ (l ^ j) zero_le_one (by rwa [one_pow])

theorem prim_of_pow {ζ : ↥LL.1} {j : ℕ} (h : ζ ^ l ^ j = 1) : ∃ k : ℕ, IsPrimitiveRoot ζ (l ^ k) := by
  obtain ⟨k, _, hk⟩ := (Nat.dvd_prime_pow (Fact.out : l.Prime)).1 (orderOf_dvd_of_pow_eq_one h)
  exact ⟨k, hk ▸ IsPrimitiveRoot.orderOf ζ⟩

theorem prim_pow {ζ : ↥LL.1} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) (a : ℕ) :
    ∃ k : ℕ, IsPrimitiveRoot (ζ ^ a) (l ^ k) := by
  obtain ⟨j, hj⟩ := h
  exact prim_of_pow (j := j) (by rw [← pow_mul, mul_comm, pow_mul, hj.pow_eq_one, one_pow])

theorem prim_one : ∃ k : ℕ, IsPrimitiveRoot (1 : ↥LL.1) (l ^ k) := prim_of_pow (j := 0) (one_pow _)

open Classical in

def pt (ζ : ↥LL.1) : ↥LL.1 := if ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) then ζ else 1

theorem pt_of {ζ : ↥LL.1} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) : pt ζ = ζ := if_pos h

theorem pt_of_not {ζ : ↥LL.1} (h : ¬ ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) : pt ζ = 1 := if_neg h

theorem prim_pt (ζ : ↥LL.1) : ∃ j : ℕ, IsPrimitiveRoot (pt ζ) (l ^ j) := by
  by_cases h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)
  · rwa [pt_of h]
  · rw [pt_of_not h]; exact prim_one

theorem isExp_unique {ζ : ↥LL.1} {a e f : PowerSeries ↥LL.1} (he : IsExp ζ a e) (hf : IsExp ζ a f) : e = f :=
  PowerSeries.ext fun k => Subtype.ext (tendsto_nhds_unique (he k) (hf k))

theorem conv_coe (p : Polynomial ↥LL.1) : Conv (p : PowerSeries ↥LL.1) := (conv_iff_sc _).2 (GlobalTheory.HWL.Disc.sc_coe p)

theorem conv_C (c : ↥LL.1) : Conv (PowerSeries.C c) := by simpa using conv_coe (Polynomial.C c)

theorem isExp_C {ζ : ↥LL.1} (hζ : ‖((ζ : Om l)) - 1‖ < 1) (c : ↥LL.1) :
    IsExp ζ (PowerSeries.C c) (PowerSeries.C c) := by
  rw [isExp_iff_ev hζ (conv_C c)]
  simpa using GlobalTheory.HWL.Disc.ev_coe (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) (Polynomial.C c)

theorem isExp_X {ζ : ↥LL.1} (hζ : ‖((ζ : Om l)) - 1‖ < 1) :
    IsExp ζ PowerSeries.X (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) := by
  rw [isExp_iff_ev hζ (by simpa using conv_coe (Polynomial.X : Polynomial ↥LL.1))]
  simpa using GlobalTheory.HWL.Disc.ev_coe (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) Polynomial.X

theorem isExp_one_dvd {a e : PowerSeries ↥LL.1} (ha : Conv a) (he : IsExp 1 a e) {w : ℕ}
    (hw : PowerSeries.X ^ w ∣ a) : PowerSeries.X ^ w ∣ e := by
  rw [isExp_iff_ev (norm_sub_one_lt prim_one) ha] at he
  rw [PowerSeries.X_pow_dvd_iff] at hw ⊢
  intro k hk
  refine (he k).unique ?_
  convert hasSum_zero with m
  rcases lt_or_ge m w with hm | hm
  · rw [hw m hm, zero_mul]
  · have hd : PowerSeries.X ^ m ∣ (PowerSeries.C (1 : ↥LL.1) * PowerSeries.exp ↥LL.1 - 1) ^ m :=
      pow_dvd_pow_of_dvd (PowerSeries.X_dvd_iff.2 (by simp)) m
    rw [PowerSeries.X_pow_dvd_iff.1 hd k (by omega), mul_zero]

def convAlg (LL : FinExt l) (n : ℕ) : Subalgebra ↥LL.1 (LetA ↥LL.1 n) where
  carrier := {a | ∀ i, Conv (a i)}
  mul_mem' ha hb i := (conv_iff_sc _).2 (((conv_iff_sc _).1 (ha i)).mul ((conv_iff_sc _).1 (hb i)))
  add_mem' ha hb i := (conv_iff_sc _).2 (((conv_iff_sc _).1 (ha i)).add ((conv_iff_sc _).1 (hb i)))
  algebraMap_mem' c _ := conv_C c

variable {n : ℕ}

def exFun (i : ZMod n) (ζ : ↥LL.1) (f : ↥(convAlg LL n)) : PowerSeries ↥LL.1 :=
  ((conv_expansion l LL (pt ζ) (norm_sub_one_lt (prim_pt ζ))).1 (f.1 i) (f.2 i)).exists.choose

theorem exFun_spec (i : ZMod n) (ζ : ↥LL.1) (f : ↥(convAlg LL n)) : IsExp (pt ζ) (f.1 i) (exFun i ζ f) :=
  ((conv_expansion l LL (pt ζ) (norm_sub_one_lt (prim_pt ζ))).1 (f.1 i) (f.2 i)).exists.choose_spec

def exAlg (i : ZMod n) (ζ : ↥LL.1) : ↥(convAlg LL n) →ₐ[↥LL.1] PowerSeries ↥LL.1 where
  toFun := exFun i ζ
  map_one' := isExp_unique (exFun_spec i ζ 1) (by simpa using isExp_C (norm_sub_one_lt (prim_pt ζ)) 1)
  map_zero' := isExp_unique (exFun_spec i ζ 0) (by simpa using isExp_C (norm_sub_one_lt (prim_pt ζ)) 0)
  map_mul' a b := isExp_unique (exFun_spec i ζ _)
    ((conv_expansion l LL (pt ζ) (norm_sub_one_lt (prim_pt ζ))).2.1 _ _ _ _ (a.2 i) (b.2 i)
      (exFun_spec i ζ a) (exFun_spec i ζ b)).2.2.2
  map_add' a b := isExp_unique (exFun_spec i ζ _)
    ((conv_expansion l LL (pt ζ) (norm_sub_one_lt (prim_pt ζ))).2.1 _ _ _ _ (a.2 i) (b.2 i)
      (exFun_spec i ζ a) (exFun_spec i ζ b)).2.2.1
  commutes' c := isExp_unique (exFun_spec i ζ _) (isExp_C (norm_sub_one_lt (prim_pt ζ)) c)

theorem exAlg_spec (i : ZMod n) (ζ : ↥LL.1) (f : ↥(convAlg LL n)) : IsExp (pt ζ) (f.1 i) (exAlg i ζ f) :=
  exFun_spec i ζ f

theorem exAlg_spec' (i : ZMod n) {ζ : ↥LL.1} (h : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) (f : ↥(convAlg LL n)) :
    IsExp ζ (f.1 i) (exAlg i ζ f) := by
  have := exAlg_spec i ζ f
  rwa [pt_of h] at this

def evalAlg {S : Type} [CommRing S] [Algebra ↥LL.1 S] (J : LetA ↥LL.1 n → S)
    (hadd : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a + b) = J a + J b)
    (hmul : ∀ a b, (∀ i, Conv (a i)) → (∀ i, Conv (b i)) → J (a * b) = J a * J b)
    (hsmul : ∀ (c : ↥LL.1) a, (∀ i, Conv (a i)) → J (c • a) = c • J a) (hone : J 1 = 1) :
    ↥(convAlg LL n) →ₐ[↥LL.1] S :=
  AlgHom.ofLinearMap
    { toFun := fun a => J a.1
      map_add' := fun a b => hadd _ _ a.2 b.2
      map_smul' := fun c a => hsmul c _ a.2 } hone fun a b => hmul _ _ a.2 b.2

variable {P : LocPrime l} {K : FinExt l} {s : ℕ} {Γ : GamS P K s LL}

abbrev LevExp (R : WSer Γ) : Prop :=
  ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) →
    ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a)

theorem lev_pi {R : WSer Γ} (h : LevExp R) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) {ζ : ↥LL.1}
    (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) :
    R.lev i ζ letπ = PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1 :=
  isExp_unique (h i ζ hζ letπ) (by simpa [toLL, letπ] using isExp_X (norm_sub_one_lt hζ))

theorem rescale_pt (c ζ : ↥LL.1) : PowerSeries.rescale c (PowerSeries.C ζ * PowerSeries.exp ↥LL.1 - 1) =
    PowerSeries.C ζ * PowerSeries.rescale c (PowerSeries.exp ↥LL.1) - 1 := by
  rw [map_sub, map_one]
  congr 1
  ext k
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  rw [mul_left_comm]

set_option maxHeartbeats 1600000 in
theorem subst_γ {R : WSer Γ} (h : LevExp R) (g : Γ.Gam) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (j a : ℕ) (hζ : IsPrimitiveRoot ζ ((P.PD K).p ^ j))
    (hv : (j : WithTop ℚ) ≤ P.v LL (algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ g : ↥(OL LL)) - (a : ↥LL.1)))
    (f : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) (e : PowerSeries ↥LL.1) (hf : Conv (f i))
    (he : IsExp (ζ ^ a) (f i) e) :
    Conv (γL R g f i) ∧ IsExp ζ (γL R g f i)
      (PowerSeries.rescale (algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ g : ↥(OL LL))) e) := by
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨j, by rwa [P.PD_p] at hζ⟩
  have h1 := h i ζ hζ' (letγ (R.γ₀ g) letπ)
  have h4 := R.lev_Γ g i ζ _ j a hζ hv rfl letπ
  rw [h4, lev_pi h i (prim_pow hζ' a), rescale_pt] at h1
  have h2 : IsExp ζ (PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.γ₀ g PowerSeries.X)) _ := h1
  have h3 := ExpSub.conv_isExp_subst l LL ζ (ζ ^ a) (algebraMap ↥(OL LL) ↥LL.1 (Γ.χΓ g : ↥(OL LL)))
    (R.γ₀ g PowerSeries.X) (norm_sub_one_lt hζ') (norm_sub_one_lt (prim_pow hζ' a)) (R.γ₀_X g).1 h2 _ e hf he
  have h5 := congrFun (γL_apply R g f) i
  rw [h5]
  exact h3

theorem subst_φ {R : WSer Γ} (h : LevExp R) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K)))
    (ζ : ↥LL.1) (hζ : ∃ j : ℕ, IsPrimitiveRoot ζ ((P.PD K).p ^ j))
    (f : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) (e : PowerSeries ↥LL.1) (hf : Conv (f (i - 1)))
    (he : IsExp (ζ ^ (P.PD K).p) (f (i - 1)) e) :
    Conv (φL ↥LL.1 _ (P.PD K).p f i) ∧ IsExp ζ (φL ↥LL.1 _ (P.PD K).p f i)
      (PowerSeries.rescale ((P.PD K).p : ↥LL.1) e) := by
  have hζ' : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by rwa [P.PD_p] at hζ
  have h1 := h i ζ hζ' (letφ R.φ₀ letπ)
  rw [R.lev_φ i ζ hζ, lev_pi h _ (prim_pow hζ' _), rescale_pt] at h1
  have hy : PowerSeries.map (algebraMap ↥(OL LL) ↥LL.1) (R.φ₀ PowerSeries.X) =
      (1 + PowerSeries.X) ^ (P.PD K).p - 1 := by
    rw [R.φ₀_X, R.q₀_def]
    simp
  rw [φL_apply, ← hy]
  exact ExpSub.conv_isExp_subst l LL ζ (ζ ^ (P.PD K).p) _ (R.φ₀ PowerSeries.X) (norm_sub_one_lt hζ')
    (norm_sub_one_lt (prim_pow hζ' _)) (by rw [R.φ₀_X]; simp) h1 _ e hf he

theorem γ_mem {R : WSer Γ} (h : LevExp R) (g : Γ.Gam) :
    ∀ a ∈ convAlg LL (Module.finrank ℚ_[l] ↥(K0 K)), γL R g a ∈ convAlg LL (Module.finrank ℚ_[l] ↥(K0 K)) := by
  intro a ha i
  refine (subst_γ h g i 1 0 0 (by simp) ?_ a _ (ha i)
    (by rw [pow_zero]; exact exAlg_spec' i prim_one ⟨a, ha⟩)).1
  rw [Nat.cast_zero, Nat.cast_zero, sub_zero, P.v_O]
  exact (Γ.χΓ g : ↥(OL LL)).2

theorem φ_mem {R : WSer Γ} (h : LevExp R) :
    ∀ a ∈ convAlg LL (Module.finrank ℚ_[l] ↥(K0 K)),
      φL ↥LL.1 _ (P.PD K).p a ∈ convAlg LL (Module.finrank ℚ_[l] ↥(K0 K)) := by
  intro a ha i
  exact (subst_φ h i 1 ⟨0, by simp⟩ a _ (ha _)
    (by rw [one_pow]; exact exAlg_spec' (i - 1) prim_one ⟨a, ha⟩)).1

theorem ζQ_pow (P : LocPrime l) (s : ℕ) : P.ζQ s ^ l ^ s = 1 := by
  induction s with
  | zero => simp [P.ζQ_zero]
  | succ s ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem unit_pi {AI : LocAinf l P} (T : LocTied l P AI) {R : WSer Γ} (I : IoS AI R)
    (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (hβ : IsBeta AI β) : IsUnit (β (I.io letπ)) := by
  rw [I.io_π, hβ]
  exact ((GlobalTheory.TiedMu.tied_mu_units l P AI T).1 s).map
    (Algebra.TensorProduct.includeRight : P.R.B →ₐ[ℚ_[l]] ↥LL.1 ⊗[ℚ_[l]] P.R.B)

theorem l_pow_inv_ne (s : ℕ) : (((l : ℚ_[l]) ^ s)⁻¹) ≠ 0 :=
  inv_ne_zero (pow_ne_zero _ (by exact_mod_cast (Fact.out : l.Prime).ne_zero))

set_option maxHeartbeats 1600000 in

theorem exists_disc (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI)
    (K : FinExt l) (s : ℕ) (LL : FinExt l) (_ : Good K s LL) (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R)
    (_ : IoW I) (β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B) (hβ : IsBeta AI β)
    (J : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1 ⊗[ℚ_[l]] P.R.B) (hJ : IsEval I β J)
    (h : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1), (∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)) →
      ∀ a : LetA ↥(OL LL) (Module.finrank ℚ_[l] ↥(K0 K)), IsExp ζ (toLL a i) (R.lev i ζ a))
    (hlet : ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (c : ↥(K0 K)),
      ((1 : ↥LL.1) ⊗ₜ[ℚ_[l]] algebraMap ↥(K0 K) P.R.B c) * β (I.io (letE i)) = Γ.emb i c • β (I.io (letE i))) :
    ∃ D : Disc R (β.comp I.io.toRingHom) ((((l : ℚ_[l]) ^ s)⁻¹) • P.ιB P.tB)
        (algebraMap (Om l) P.R.BdR (P.ζQ s)),
      (∀ a : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K)), (∀ i, Conv (a i)) → a ∈ D.C) ∧
        (D.t : LetA ↥LL.1 (Module.finrank ℚ_[l] ↥(K0 K))) = fun _ => logS LL := by
  have hc := conv_expansion l LL 1 (norm_sub_one_lt prim_one)
  have hone : J 1 = 1 := by
    have h1 := hJ.ext 1
    rw [map_one, map_one] at h1
    rw [← h1]
    congr 1
    funext i
    simp [toLL]
  have hιs : ∀ b, (P.PD K).ι ((((l : ℚ_[l]) ^ s)⁻¹) • b) = (((l : ℚ_[l]) ^ s)⁻¹) • P.ιB b := fun b => by
    rw [P.PD_ι, map_smul]
  refine ⟨{
    C := convAlg LL _
    toL_mem := fun a i => hc.2.2.1 (a i)
    cst_mem := fun c i => conv_C (c i)
    γ_mem := γ_mem h
    φ_mem := φ_mem h
    t := ⟨fun _ => logS LL, fun _ => hc.2.2.2.1⟩
    t_zero := fun _ => by simp [logS]
    J := evalAlg J hJ.add hJ.mul hJ.smul hone
    J_toL := fun a => hJ.ext a
    J_φ := fun a => ?_
    J_γ := fun g a => ?_
    tb := (((l : ℚ_[l]) ^ s)⁻¹) • P.tB
    tb_unit := ?_
    periodDiscJ_tateElement := hJ.log
    ι_tb := hιs _
    tS_mem := ?_
    π_unit := unit_pi T I β hβ
    letter := hlet
    ex := exAlg
    ex_toL := fun i ζ a => ?_
    ex_cst := fun i ζ c => isExp_unique (exAlg_spec i ζ _) (isExp_C (norm_sub_one_lt (prim_pt ζ)) (c i))
    numEx_t_eq_fifteen := fun i ζ => isExp_unique (exAlg_spec i ζ _)
      ((conv_expansion l LL _ (norm_sub_one_lt (prim_pt ζ))).2.2.2.2
        ((prim_pt ζ).imp fun _ hj => hj.pow_eq_one))
    ex_γ := fun g i ζ ζ' j a hζ hv hζ' f => ?_
    ex_φ := fun i ζ hζ f => ?_
    ex_one := fun i f w hw => isExp_one_dvd (f.2 i) (exAlg_spec' i prim_one f) hw
    taylor := fun i ζ ι hι hζ f m => ?_ }, fun a ha => ha, rfl⟩
  · have h1 : (P.PD K).φ = P.φB := AlgHom.ext (P.PD_φ K)
    rw [h1]
    change J (φL ↥LL.1 _ (P.PD K).p a.1) = _
    rw [φL_apply, P.PD_p]
    exact hJ.frob a.1 a.2
  · have h1 : ((P.PD K).actB g).toAlgHom.restrictScalars ℚ_[l] = (P.actQ (g : GQ l)).toAlgHom :=
      AlgHom.ext (P.PD_actB K g)
    rw [h1]
    change J (γL R _ a.1) = _
    rw [γL_apply]
    exact hJ.gal g a.1 a.2
  · rw [Algebra.smul_def]
    exact ((l_pow_inv_ne s).isUnit.map _).mul (P.period_datum_t_eq K ▸ (P.PD K).t_unit)
  · have h1 := (P.PD K).mem_filtration_one
    rw [P.PD_ι, P.period_datum_t_eq] at h1
    exact Submodule.smul_of_tower_mem _ _ h1
  · by_cases hζ : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j)
    · exact isExp_unique (exAlg_spec' i hζ _) (h i ζ hζ a)
    · have h1 := exAlg_spec i ζ (⟨toL _ _ _ a, fun i => hc.2.2.1 (a i)⟩ : ↥(convAlg LL _))
      rw [pt_of_not hζ] at h1
      rw [R.lev_junk i ζ (by rwa [P.PD_p])]
      exact isExp_unique h1 (h i 1 prim_one a)
  · have hζ1 : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := ⟨j, by rwa [P.PD_p] at hζ⟩
    subst hζ'
    exact isExp_unique (exAlg_spec' i hζ1 _)
      (subst_γ h g i ζ j a hζ hv f.1 _ (f.2 i) (exAlg_spec' i (prim_pow hζ1 a) f)).2
  · have hζ1 : ∃ j : ℕ, IsPrimitiveRoot ζ (l ^ j) := by rwa [P.PD_p] at hζ
    exact isExp_unique (exAlg_spec' i hζ1 _)
      (subst_φ h i ζ hζ f.1 _ (f.2 _) (exAlg_spec' (i - 1) (prim_pow hζ1 _) f)).2
  · rcases subsingleton_or_nontrivial P.R.BdR with hs | hs
    · rw [Subsingleton.elim (_ - _ : P.R.BdR) 0]
      exact Submodule.zero_mem _
    have hζ1 : ζ ^ l ^ s = 1 := by
      apply ι.toRingHom.injective
      change ι _ = ι _
      rw [map_pow, hζ, ← map_pow, ζQ_pow, map_one, map_one]
    have h1 : (P.PD K).ι.restrictScalars ℚ_[l] = P.ιB := AlgHom.ext (P.PD_ι K)
    rw [h1]
    exact hJ.taylor i ζ ι hι hζ f.1 f.2 _ (exAlg_spec' i (prim_of_pow hζ1) f) m

end GlobalTheory.HWL.Cmp.OpenDisc
