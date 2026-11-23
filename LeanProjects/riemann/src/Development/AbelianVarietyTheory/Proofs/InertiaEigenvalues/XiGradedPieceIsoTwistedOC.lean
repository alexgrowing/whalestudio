import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFontaineThetaOnAinfStatement

noncomputable section

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

namespace GlobalTheory.Cyc.Graded

variable {l : ℕ} [Fact l.Prime]

theorem mem_OC_iff (y : PadicComplex l) : y ∈ PadicComplexInt l ↔ ‖y‖ ≤ 1 := by
  rw [PadicComplexInt, Valuation.mem_valuationSubring_iff]
  rw [PadicComplex.norm_eq_norm]
  exact (Valued.toNormedField.norm_le_one_iff (L := PadicComplex l) (Γ₀ := NNReal)).symm

theorem norm_OC (y : OC l) : ‖(y : PadicComplex l)‖ ≤ 1 := (mem_OC_iff _).1 y.2

theorem norm_alg (x : ℚ_[l]) : ‖algebraMap ℚ_[l] (PadicComplex l) x‖ = ‖x‖ := by
  exact norm_algebraMap' _ x

theorem norm_lpow (m : ℕ) : ‖(l : PadicComplex l) ^ m‖ = (l : ℝ) ^ (-(m : ℤ)) := by
  have h := norm_alg ((l : ℚ_[l]) ^ m)
  rw [map_pow, map_natCast] at h
  rw [h, Padic.norm_p_pow]

theorem eq_zero_of_norm_le (y : PadicComplex l) (h : ∀ m : ℕ, ‖y‖ ≤ 2 * (l : ℝ) ^ (-(m : ℤ))) :
    y = 0 := by
  by_contra hy
  have hpos : 0 < ‖y‖ / 2 := by positivity
  have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one hpos (inv_lt_one_of_one_lt₀ hl)
  have := h m
  rw [zpow_neg, zpow_natCast, ← inv_pow] at this
  linarith

theorem theta_alg (θ : Ainf l →+* OC l) (z : ℤ_[l]) :
    ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) = zC z := by
  rw [← sub_eq_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec m z)
  have hz : z = (z.appr m : ℤ_[l]) + w * (l : ℤ_[l]) ^ m := by rw [hw]; ring
  have h1 : ((θ (algebraMap ℤ_[l] (Ainf l) z) : OC l) : PadicComplex l) - zC z =
      ((θ (algebraMap ℤ_[l] (Ainf l) w) : OC l) : PadicComplex l) * (l : PadicComplex l) ^ m -
        zC w * (l : PadicComplex l) ^ m := by
    generalize z.appr m = n at hz
    subst hz
    simp [zC]
  have h2 : ‖zC w‖ ≤ 1 := by rw [zC, norm_alg]; exact w.2
  have h3 := norm_OC (θ (algebraMap ℤ_[l] (Ainf l) w))
  have h4 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  rw [h1]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow]
  nlinarith

theorem inclW_inj : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

variable {P : LocPrime l} (AI : LocAinf l P)

theorem xi_cancel {a b : Ainf l} (h : AI.ξ * a = AI.ξ * b) : a = b := by
  apply inclW_inj
  have := congrArg (inclW l) h
  rw [map_mul, map_mul] at this
  exact AI.isUnit_inclW_ξ.mul_left_cancel this

theorem εroot_pow (m : ℕ) : AI.εroot m ^ (l ^ m) = AI.ε := by
  induction m with
  | zero => simp [LocAinf.εroot]
  | succ k ih =>
    rw [pow_succ', pow_mul, LocAinf.εroot, Function.iterate_succ_apply', frobeniusEquiv_symm_pow_p]
    exact ih

theorem ζQ_pow (m : ℕ) : P.ζQ m ^ (l ^ m) = 1 := by
  induction m with
  | zero => simp [P.ζQ_zero]
  | succ k ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]

theorem theta_lambda (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (g : GQ l)
    (hg : g (P.ζQ 1) = P.ζQ 1) (lam : Ainf l) (hlam : AI.actW g AI.ξ = lam * AI.ξ) :
    ((θ lam : OC l) : PadicComplex l) = algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l]) := by
  obtain ⟨-, -, hact, hker, hζ⟩ := hθ
  have hπ : θ AI.π₁ = AI.ζ 1 - 1 := by
    rw [LocAinf.π₁, map_sub, map_one, ← hζ 1]; rfl
  have hne : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) ≠ 0 := by
    intro h
    exact AI.ζ_one (sub_eq_zero.1 (Subtype.ext h))
  have hgπ : θ (AI.actW g AI.π₁) = AI.ζ 1 - 1 := by
    apply Subtype.ext
    have := hact g AI.π₁
    rw [hπ] at this
    rw [this]
    push_cast
    rw [map_sub, map_one, AI.ζ_eq, AI.actC_ext, hg]
  rw [← sub_eq_zero]
  apply mul_left_cancel₀ hne
  rw [mul_zero]
  apply eq_zero_of_norm_le
  intro m
  obtain ⟨a, ha, hga⟩ := P.χQ_cyc g m (P.ζQ m) (ζQ_pow m)
  set z : Ainf l := WittVector.teichmuller l (AI.εroot m) with hz
  have hzl : z ^ (l ^ m) = 1 + AI.μ := by
    rw [hz, ← map_pow, εroot_pow, LocAinf.μ]; ring
  have h0 : θ (AI.actW g z - z ^ a) = 0 := by
    apply Subtype.ext
    rw [map_sub, map_pow]
    push_cast
    rw [hact, hζ m, AI.ζ_eq, AI.actC_ext, hga, sub_eq_zero]
    exact map_pow (algebraMap (Om l) (PadicComplex l)) _ _
  obtain ⟨b, hb⟩ := (hker _).1 h0
  have hb' : AI.actW g z = z ^ a + AI.ξ * b := by rw [← hb]; ring
  obtain ⟨k, hk⟩ := Polynomial.powAddExpansion (z ^ a) (AI.ξ * b) (l ^ m)
  obtain ⟨k', hk'⟩ := Polynomial.powAddExpansion (1 : Ainf l) AI.μ a
  have h1 : 1 + AI.actW g AI.μ = (z ^ a + AI.ξ * b) ^ (l ^ m) := by
    rw [← hb', ← map_pow, hzl, map_add, map_one]
  rw [hk, ← pow_mul, mul_comm a, pow_mul, hzl, hk', AI.μ_eq, map_mul, hlam] at h1
  have h2 : AI.actW g AI.π₁ * lam = (a : Ainf l) * AI.π₁ +
      (l : Ainf l) ^ m * ((z ^ a) ^ (l ^ m - 1) * b) + AI.ξ * (k' * AI.π₁ ^ 2 + k * b ^ 2) := by
    apply xi_cancel AI
    rw [Nat.cast_pow, one_pow, one_pow] at h1
    linear_combination h1
  have hξ : θ AI.ξ = 0 := (hker _).2 dvd_rfl
  have h3 := congrArg (fun t => ((θ t : OC l) : PadicComplex l)) h2
  simp only [map_add, map_mul, hξ, hgπ, hπ, map_pow, map_natCast, zero_mul, add_zero] at h3
  set u : OC l := (θ z ^ a) ^ (l ^ m - 1) * θ b with hu
  have h4 : ((AI.ζ 1 - 1 : OC l) : PadicComplex l) * (((θ lam : OC l) : PadicComplex l) -
      algebraMap ℚ_[l] (PadicComplex l) (P.χQ g : ℚ_[l])) = (l : PadicComplex l) ^ m * (u : PadicComplex l) -
      ((AI.ζ 1 - 1 : OC l) : PadicComplex l) *
        algebraMap ℚ_[l] (PadicComplex l) ((P.χQ g : ℚ_[l]) - a) := by
    rw [map_sub, map_natCast]
    generalize (AI.ζ 1 - 1 : OC l) = t at h3 ⊢
    push_cast at h3
    linear_combination h3
  rw [h4]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, norm_lpow, norm_alg]
  have h5 := norm_OC u
  have h6 := norm_OC (AI.ζ 1 - 1)
  have h7 : 0 ≤ (l : ℝ) ^ (-(m : ℤ)) := by positivity
  have h8 := norm_nonneg ((P.χQ g : ℚ_[l]) - a)
  nlinarith

def toM (i : ℤ) : Ainf l →+ Mxi (AinfSub l) (xiU AI) i where
  toFun a := ⟨((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a, inclW l a, ⟨a, rfl⟩, rfl⟩
  map_zero' := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (by simp [mul_add])

theorem toM_val (i : ℤ) (a : Ainf l) :
    (toM AI i a : WCb l) = ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := rfl

theorem toM_bij (i : ℤ) : Function.Bijective (toM AI i) := by
  constructor
  · intro a b h
    have := congrArg Subtype.val h
    rw [toM_val, toM_val] at this
    exact inclW_inj ((Units.mul_right_inj _).1 this)
  · rintro ⟨x, y, ⟨a, rfl⟩, rfl⟩
    exact ⟨a, rfl⟩

theorem toM_mem (i : ℤ) (a : Ainf l) :
    toM AI i a ∈ (Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype ↔
      AI.ξ ∣ a := by
  have key : ∀ b : Ainf l, ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ * b) := by
    intro b
    rw [zpow_add_one, Units.val_mul, map_mul, mul_assoc]; rfl
  constructor
  · rintro ⟨y, ⟨b, rfl⟩, h⟩
    refine ⟨b, ?_⟩
    have h' : ((xiU AI ^ (i + 1) : (WCb l)ˣ) : WCb l) * inclW l b =
      ((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a := h
    rw [key] at h'
    exact (inclW_inj ((Units.mul_right_inj _).1 h')).symm
  · rintro ⟨b, rfl⟩
    exact ⟨inclW l b, ⟨b, rfl⟩, key b⟩

theorem toM_smul (i : ℤ) (z : ℤ_[l]) (a : Ainf l) :
    z • toM AI i a = toM AI i (algebraMap ℤ_[l] (Ainf l) z * a) := by
  apply Subtype.ext
  rw [Submodule.coe_smul, toM_val, toM_val, map_mul, Algebra.smul_def]
  have : inclW l (algebraMap ℤ_[l] (Ainf l) z) = algebraMap ℤ_[l] (WCb l) z := (inclWA l).commutes z
  rw [this]; ring

theorem toM_act (i : ℤ) (g : GQ l) : ∃ lam : (Ainf l)ˣ, AI.actW g AI.ξ = lam * AI.ξ ∧
    ∀ a : Ainf l, actM (xiOK AI) i g (toM AI i a) =
      toM AI i (((lam ^ i : (Ainf l)ˣ) : Ainf l) * AI.actW g a) := by
  obtain ⟨u, ⟨b, hb⟩, ⟨b', hb'⟩, hu⟩ := (xiOK AI).2.2 g
  have hb1 : inclW l b = u := hb
  have hb2 : inclW l b' = ((u⁻¹ : (WCb l)ˣ) : WCb l) := hb'
  have hbb : b * b' = 1 := by
    apply inclW_inj
    rw [map_mul, hb1, hb2, map_one, Units.mul_inv]
  let lam : (Ainf l)ˣ := ⟨b, b', hbb, by rw [mul_comm, hbb]⟩
  have hmap : Units.map (inclW l).toMonoidHom lam = u := Units.ext hb1
  refine ⟨lam, ?_, fun a => ?_⟩
  · apply inclW_inj
    have h1 := inclW_act AI g AI.ξ
    have h2 : AI.actWCbHom g (inclW l AI.ξ) = u * inclW l AI.ξ := hu
    rw [map_mul]
    change inclW l (AI.actWHom g AI.ξ) = inclW l b * _
    rw [← h1, h2, hb1]
  · apply Subtype.ext
    change AI.actWCbHom g (((xiU AI ^ i : (WCb l)ˣ) : WCb l) * inclW l a) = _
    rw [toM_val, map_mul, act_zpow (act := AI.actWCbHom) g i u hu, inclW_act, map_mul, mul_zpow, Units.val_mul]
    have h3 : inclW l ((lam ^ i : (Ainf l)ˣ) : Ainf l) = ((u ^ i : (WCb l)ˣ) : WCb l) := by
      rw [← hmap, ← map_zpow]; rfl
    rw [h3]
    change _ = _ * (_ * inclW l (AI.actWHom g a))
    ring

theorem graded_of_theta (θ : Ainf l →+* OC l) (hθ : IsTheta AI θ) (i : ℤ) :
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  let θ' : Ainf l →+* PadicComplex l := (PadicComplexInt l).subtype.comp θ
  have hθ' : ∀ a, θ' a = ((θ a : OC l) : PadicComplex l) := fun _ => rfl
  have hker : ∀ a, θ' a = 0 ↔ AI.ξ ∣ a := by
    intro a
    rw [← hθ.2.2.2.1 a, hθ']
    exact ZeroMemClass.coe_eq_zero
  let e := AddEquiv.ofBijective (toM AI i) (toM_bij AI i)
  let f : Mxi (AinfSub l) (xiU AI) i →+ PadicComplex l :=
    θ'.toAddMonoidHom.comp e.symm.toAddMonoidHom
  have hf : ∀ a, f (toM AI i a) = θ' a := fun a => congrArg θ' (e.symm_apply_apply a)
  let Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l :=
    QuotientAddGroup.lift
      ((Mxi (AinfSub l) (xiU AI) (i + 1)).comap (Mxi (AinfSub l) (xiU AI) i).subtype).toAddSubgroup f
      (by
        intro x hx
        obtain ⟨a, rfl⟩ := (toM_bij AI i).2 x
        rw [AddMonoidHom.mem_ker, hf, hker]
        exact (toM_mem AI i a).1 hx)
  have hΦ : ∀ a, Φ (Submodule.Quotient.mk (toM AI i a)) = θ' a := fun a => hf a
  have hsurj : ∀ x : Qab (AinfSub l) (xiU AI) i (i + 1), ∃ a, x = Submodule.Quotient.mk (toM AI i a) := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨a, rfl⟩ := (toM_bij AI i).2 y
    exact ⟨a, rfl⟩
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, rfl⟩ := hsurj x
    rw [hΦ, hker] at hx
    exact (Submodule.Quotient.mk_eq_zero _).2 ((toM_mem AI i a).2 hx)
  · ext y
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨a, rfl⟩ := hsurj x
      rw [Set.mem_setOf_eq, hΦ]
      exact norm_OC _
    · intro hy
      obtain ⟨a, ha⟩ := hθ.2.1 ⟨y, (mem_OC_iff y).2 hy⟩
      exact ⟨_, by rw [hΦ a, hθ', ha]⟩
  · intro z x
    obtain ⟨a, rfl⟩ := hsurj x
    rw [← Submodule.Quotient.mk_smul, toM_smul, hΦ, hΦ, map_mul, hθ', theta_alg]
  · intro g hg x
    obtain ⟨a, rfl⟩ := hsurj x
    obtain ⟨lam, h1, h2⟩ := toM_act AI i g
    have h3 := theta_lambda AI θ hθ g hg lam h1
    have h4 : actQab (xiOK AI) i (i + 1) g (Submodule.Quotient.mk (toM AI i a)) =
        Submodule.Quotient.mk (actM (xiOK AI) i g (toM AI i a)) := rfl
    rw [h4, h2, hΦ, hΦ, map_mul, hθ' (AI.actW g a), hθ.2.2.1, hθ' a]
    congr 1
    have h5 : Units.map θ'.toMonoidHom lam =
        Units.map (algebraMap ℚ_[l] (PadicComplex l)).toMonoidHom (P.χQ g) := Units.ext h3
    have h6 := congrArg (fun u : (PadicComplex l)ˣ => ((u ^ i : (PadicComplex l)ˣ) : PadicComplex l)) h5
    beta_reduce at h6
    rw [← map_zpow, ← map_zpow] at h6
    exact h6

theorem graded_iso : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (i : ℤ),
    ∃ Φ : Qab (AinfSub l) (xiU AI) i (i + 1) →+ PadicComplex l, Function.Injective Φ ∧
      Set.range Φ = {y | ‖y‖ ≤ 1} ∧ (∀ (z : ℤ_[l]) x, Φ (z • x) = zC z * Φ x) ∧
      ∀ g : GQ l, g (P.ζQ 1) = P.ζQ 1 → ∀ x,
        Φ (actQab (xiOK AI) i (i + 1) g x) = chiC P.χQ i g * AI.actC g (Φ x) := by
  intro l _ P AI i
  obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_fontaineTheta_on_Ainf l P AI
  exact graded_of_theta AI θ hθ i

end GlobalTheory.Cyc.Graded
