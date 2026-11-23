import Formalism.LocalToGlobal.KernelLattices.LateralTheory
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlock
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LocalComponentGL
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.LogarithmEquivalence
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Th0CharMulOpUTh0HalfPeriodEq
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.MatrixFormFourfoldBlockFirstBlockEmb
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyGaussianIntegralsCongrFact
import Formalism.SharpRestriction.GlobalSchurBounds.StandardIntegralLatticeExists
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.QuasiPeriodConstUniqueOf
import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
import Formalism.LocalToGlobal.GlobalTheory.GL3.DeterminantNormOneOfUnitDisc

noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField Formalism.BasicNotions Classical

namespace Formalism.L2.Ker

open Formalism.L2.Th1.H
open Formalism.MainNotions
open Formalism.MainNotions.GlobalTheoryTheory.Inhab (mem_stdL single_mem_stdL)

theorem kInterInv : InterInv :=
  InterInv_of heisenbergComm (InterReps_of semicharacterHom) (InterFixed_of semicharacterHom) cosetRepsExist
theorem kInterTh : InterTh := InterTh_of semicharacterHom heisenbergAnalytic
theorem kLineTransport : LineTransport := LineTransport_of kInterInv kInterTh
theorem kThetaVector : ThetaVector :=
  ThetaVector_of kLineTransport ThStd_proof product_theta_mem StdSelfDual_proof StdSemiChar_proof (ThIsom_of heisenbergIsometry)
    fourth_root

theorem formV_apply (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) (z w : n → Fin N' → Fin N → ℂ) :
    formV A n N N' z w = (∑ τ, ∑ i, ∑ j, z τ i j * conj (w τ i j)) / (A : ℂ) := rfl

theorem formV_herm (A : ℝ) (n : Type) [Fintype n] (N N' : ℕ) : IsHerm (formV A n N N') := by
  intro x y
  simp only [formV_apply, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun τ _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem Hf_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (z w : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Hf D T z w = formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N' z w := rfl

theorem U_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.U D T x G = opU (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') x G := rfl

theorem Iop_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ) :
    TaylorLogMetric.Iop D T La₁ La₂ G = inter (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La₁ La₂ G := rfl

theorem mem_ThSp_of (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La' : AddSubgroup (TaylorLogMetric.VC D N N'))
    (G : TaylorLogMetric.VC D N N' → ℂ)
    (h : G ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') (TaylorLogMetric.al D T) La') :
    G ∈ TaylorLogMetric.ThSp D T La' :=
  ⟨fun z => (h.1 z (Set.mem_univ z)).differentiableAt, fun x hx z => h.2 x hx z⟩

theorem Iop_smul (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (La₁ La₂ : AddSubgroup (TaylorLogMetric.VC D N N'))
    (c : ℂ) (G : TaylorLogMetric.VC D N N' → ℂ) (z : TaylorLogMetric.VC D N N') :
    TaylorLogMetric.Iop D T La₁ La₂ (fun v => c * G v) z = c * TaylorLogMetric.Iop D T La₁ La₂ G z := by
  unfold TaylorLogMetric.Iop
  have : ∀ q : La₂ ⧸ La₁.addSubgroupOf La₂,
      TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') (fun v => c * G v) z
      = c • (TaylorLogMetric.al D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') *
        TaylorLogMetric.U D T ((Quotient.out q : La₂) : TaylorLogMetric.VC D N N') G z) := by
    intro q; simp only [TaylorLogMetric.U, smul_eq_mul]; ring
  simp only [this]
  rw [← smul_finsum, smul_eq_mul]; ring

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]
  (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ)) (κ : ℂ)

theorem thM_spec (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) : IsThM L ω₀ c ΛM g κ (thM L ω₀ c ΛM g κ) := by
  obtain ⟨θ, h1, h2⟩ := (kThetaVector L ω₀ n _ ΛM _ _ g h κ hκ).1
  exact Classical.epsilon_spec (p := IsThM L ω₀ c ΛM g κ) ⟨θ, h1, h2⟩

theorem isThM_ne_zero (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) {θ : (n → ℂ) → ℂ} (hθ : IsThM L ω₀ c ΛM g κ θ) :
    θ ≠ 0 :=
  ((kThetaVector L ω₀ n _ ΛM _ _ g h κ hκ).2 θ hθ.1 hθ.2).1

theorem isThM_spans (h : StdOK L ω₀ c ΛM g) (hκ : κ ≠ 0) {θ : (n → ℂ) → ℂ} (hθ : IsThM L ω₀ c ΛM g κ θ) :
    ∀ F ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM, ∃ a : ℂ, F = a • θ :=
  ((kThetaVector L ω₀ n _ ΛM _ _ g h κ hκ).2 θ hθ.1 hθ.2).2.2

omit [DecidableEq n] in
theorem tensPow_ne_zero {θ : (n → ℂ) → ℂ} (hθ : θ ≠ 0) (N N' : ℕ) : tensPow θ N N' ≠ 0 := by
  obtain ⟨z₀, hz⟩ := Function.ne_iff.1 hθ
  intro h0
  have := congrFun h0 (fun τ _ _ => z₀ τ)
  simp only [tensPow, Pi.zero_apply, Finset.prod_const] at this
  exact absurd this (pow_ne_zero _ (pow_ne_zero _ hz))

end Gen

section Tens

variable {n : Type} [Fintype n] [DecidableEq n]

theorem matH_hOne (L : PeriodPair) (z w : n → ℂ) :
    matH (hOne L n) z w = (∑ τ, z τ * conj (w τ)) / ((Formalism.L2.Th1.F.area L : ℝ) : ℂ) := by
  show (∑ i, ∑ j, z i * hOne L n i j * conj (w j)) = _
  simp only [hOne, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_div]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [div_eq_mul_inv]; ring

theorem formV_sum (L : PeriodPair) (N N' : ℕ) (z w : n → Fin N' → Fin N → ℂ) :
    formV (Formalism.L2.Th1.F.area L) n N N' z w
      = ∑ i, ∑ j, matH (hOne L n) (fun τ => z τ i j) (fun τ => w τ i j) := by
  simp only [formV_apply, matH_hOne, ← Finset.sum_div]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem opU_tensPow (L : PeriodPair) (N N' : ℕ) (θ : (n → ℂ) → ℂ) (x z : n → Fin N' → Fin N → ℂ) :
    opU (formV (Formalism.L2.Th1.F.area L) n N N') x (tensPow θ N N') z
      = ∏ i, ∏ j, opU (matH (hOne L n)) (fun τ => x τ i j) θ (fun τ => z τ i j) := by
  simp only [opU, tensPow, formV_sum, Finset.prod_mul_distrib, ← Complex.exp_sum]
  congr 1
  congr 1
  simp only [Finset.mul_sum, Finset.sum_div, Finset.sum_sub_distrib]

theorem alphaQ_tensPow (c : ℝ) (L : PeriodPair) (N N' : ℕ) (x : n → Fin N' → Fin N → ℂ) :
    alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N') x
      = ∏ i, ∏ j, alphaQ c (matH (hOne L n)) (fun τ => x τ i j) := by
  simp only [alphaQ, qOf, formV_sum, ← Complex.exp_sum]
  congr 1
  simp only [Complex.re_sum, Finset.mul_sum, Complex.ofReal_sum, Complex.ofReal_mul]

def entry (n : Type) (N N' : ℕ) (i : Fin N') (j : Fin N) : (n → Fin N' → Fin N → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun τ =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N => ℂ) j).comp
      ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin N' => Fin N → ℂ) i).comp
        (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : n => Fin N' → Fin N → ℂ) τ))

theorem tensPow_mem (c : ℝ) (L : PeriodPair) (ΛM : AddSubgroup (n → ℂ)) {θ : (n → ℂ) → ℂ}
    (hθ : θ ∈ Formalism.L2.Th1.H.Th (matH (hOne L n)) (alphaQ c (matH (hOne L n))) ΛM) (N N' : ℕ) :
    tensPow θ N N' ∈ Formalism.L2.Th1.H.Th (formV (Formalism.L2.Th1.F.area L) n N N')
      (alphaQ c (formV (Formalism.L2.Th1.F.area L) n N N')) (powLat ΛM N N') := by
  refine ⟨?_, ?_⟩
  · intro z _
    have : tensPow θ N N' = fun z => ∏ i, ∏ j, θ (entry n N N' i j z) := rfl
    rw [this]
    refine Finset.analyticAt_fun_prod _ fun i _ => Finset.analyticAt_fun_prod _ fun j _ => ?_
    exact (hθ.1 _ (Set.mem_univ _)).comp ((entry n N N' i j).analyticAt z)
  · intro x hx z
    rw [opU_tensPow, alphaQ_tensPow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun j _ => hθ.2 _ (hx i j) _

end Tens

theorem Th_congr {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] (H : Sesq V) (α α' : V → ℂ) (Λ : AddSubgroup V)
    (h : ∀ x ∈ Λ, α x = α' x) {F : V → ℂ} (hF : F ∈ Formalism.L2.Th1.H.Th H α Λ) : F ∈ Formalism.L2.Th1.H.Th H α' Λ :=
  ⟨hF.1, fun x hx z => by rw [← h x hx]; exact hF.2 x hx z⟩

theorem al_eq (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') (m : ℤ)
    (h : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re = (m : ℝ)) :
    TaylorLogMetric.al D T x = alphaQ (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') x := by
  have h' : qOf (Real.sqrt D.host.d / 2) (formV (TaylorLogMetric.area T.abelian₂) D.what₂.Tau N N') x = (m : ℝ) := h
  unfold TaylorLogMetric.al alphaQ
  rw [h, h', round_intCast]
  rw [show (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * ((Real.pi : ℂ) * Complex.I) by push_cast; ring,
    Complex.exp_int_mul, Complex.exp_pi_mul_I]

section Kap

variable {D : D7} {γ₀ : IsoK D} (k : KapChoice γ₀)

theorem classNumber_ne (D : D7) : classNumber D.host.K ≠ 0 := Fintype.card_ne_zero

theorem KapChoice.pi_ne_zero (p : ℕ) (hp : p.Prime) (hs : SplitK D p) : k.pi p ≠ 0 := by
  intro h0
  have h := k.pi_gen p hp hs
  rw [h0, Ideal.span_singleton_eq_bot.2 rfl, ← Ideal.zero_eq_bot] at h
  exact (k.pp p).ne_bot ((pow_eq_zero_iff (classNumber_ne D)).1 h)

theorem KapChoice.rt_ne_zero (p : ℕ) (hp : p.Prime) (hs : SplitK D p) : k.rt p ≠ 0 := by
  intro h0
  have h := k.rt_pow p hp hs
  have hpi := k.pi_ne_zero p hp hs
  have h1 : ((k.pi p : 𝓞 D.host.K) : D.host.K) ≠ 0 := by simpa using hpi
  have h2 : (((k.pi p : 𝓞 D.host.K) : D.host.K) : D.host.E) ≠ 0 := by simpa using h1
  rw [h0, zero_pow (mul_ne_zero two_ne_zero (classNumber_ne D))] at h
  exact (div_ne_zero ((map_ne_zero _).2 h2) ((map_ne_zero _).2 ((map_ne_zero _).2 h2))) h.symm

theorem KapChoice.kappa_ne_zero : k.kappa ≠ 0 :=
  finprod_induction (· ≠ 0) one_ne_zero (fun _ _ => mul_ne_zero)
    (fun p => zpow_ne_zero _ (k.rt_ne_zero p p.2.1 p.2.2))

end Kap

theorem inter_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ : AddSubgroup V) :
    inter H α Λ₁ Λ₂ 0 = 0 := by
  funext z; simp [inter, opU]

theorem inter_ne_zero {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (Λ₁ Λ₂ : AddSubgroup V)
    (α : V → ℂ) (s₁ : IsSelfDual H Λ₁) (s₂ : IsSelfDual H Λ₂) (c₁ : IsSemiChar H Λ₁ α) (c₂ : IsSemiChar H Λ₂ α)
    (i₁ : relIdx Λ₁ Λ₂ ≠ 0) (i₂ : relIdx Λ₂ Λ₁ ≠ 0) {F : V → ℂ} (hF : F ∈ fixedBy H α Λ₁) (h0 : F ≠ 0) :
    inter H α Λ₁ Λ₂ F ≠ 0 := by
  intro h
  apply h0
  funext z
  have := kInterInv V H hH Λ₁ Λ₂ α s₁ s₂ c₁ c₂ i₁ i₂ F hF z
  rw [h, inter_zero] at this
  exact this.symm

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem kappa_ne_zero : B.kappa ≠ 0 := B.kc.kappa_ne_zero

theorem thMM_spec (h : B.StdOK) : B.IsThMM B.thMM := thM_spec _ _ _ _ _ _ h B.kappa_ne_zero

theorem thMM_ne_zero (h : B.StdOK) : B.thMM ≠ 0 := isThM_ne_zero _ _ _ _ _ _ h B.kappa_ne_zero (B.thMM_spec h)

theorem thZero_ne_zero (h : B.StdOK) (N N' : ℕ) : B.thZero N N' ≠ 0 := tensPow_ne_zero (B.thMM_ne_zero h) N N'

theorem eNat_base (χ : TaylorLogMetric.IdE D → ℂ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E))
    (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) :
    B.eNat χ N N' L L' = fun z => χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N') L') ^ (-((N / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L')
        (fun v => χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) * B.thHalf N N' L v) z := by
  funext z
  rw [Iop_smul]
  simp only [eNat, chiFac, thMoved]
  ring

theorem isAdmissible_flagPair_of_unitriangular_left_automorphism {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.admitted D N N' L (StandardLatticesGL3.stdL D N') := ⟨h.1, h.2.1, h.2.2.1, Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N'⟩

theorem first_coordinate_admissible {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (h : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.admitted D N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D N N' h.1 h.2.1

theorem thMoved_mem (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N') {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    B.thMoved N N' L L' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L L') := by
  have h1 := kInterTh _ _ (formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)).2 (hL.2 N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)).1 _ h0
  exact kInterTh _ _ (formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L L' hA).2 (hL.2 N N' _ _ _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) hA).1 _ h1

theorem thMoved_ne_zero (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N')
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : B.thMoved N N' L L' ≠ 0 := by
  have hH := formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'
  have a0 := hL.1 N N' _ _ (first_coordinate_admissible hA)
  have a1 := hL.1 N N' _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)
  have a2 := hL.1 N N' _ _ hA
  have c01 := hL.2 N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)
  have c12 := hL.2 N N' _ _ _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) hA
  have h1 := kInterTh _ _ hH _ _ _ a1.2 c01.1 _ h0
  have n1 := inter_ne_zero _ hH _ _ _ a0.1 a1.1 a0.2 a1.2 c01.1 c01.2 h0.2 (B.thZero_ne_zero hS N N')
  exact inter_ne_zero _ hH _ _ _ a1.1 a2.1 a1.2 a2.2 c12.1 c12.2 h1.2 n1

theorem eNat_mem_ne (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} (h0 : B.ThZeroMem N N') (χ : TaylorLogMetric.IdE D → ℂ)
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') (hχ : chiFac χ N N' L L' ≠ 0) :
    B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 := by
  have e : B.eNat χ N N' L L' = chiFac χ N N' L L' • B.thMoved N N' L L' := rfl
  refine ⟨mem_ThSp_of D B.tor _ _ ?_, ?_⟩
  · rw [e]; exact Submodule.smul_mem _ _ (B.thMoved_mem hL h0 hA)
  · rw [e]; exact smul_ne_zero hχ (B.thMoved_ne_zero hS hL h0 hA)

end Base

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem thZeroMem_of (hS : B.StdOK) (hA : B.AreaOK) {N N' : ℕ} (h0 : B.Lat0OK N N') (hq : B.QInt0 N N') :
    B.ThZeroMem N N' := by
  have h1 := tensPow_mem B.cq B.L B.lamM (B.thMM_spec hS).1 N N'
  have e : TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ) = Formalism.L2.Th1.F.area B.L := hA
  have h0' : TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat B.lamM N N' := h0
  have h2 : B.thZero N N' ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N')
      (alphaQ B.cq (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N'))
      (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) := by
    rw [e, h0']; exact h1
  refine Th_congr _ _ _ _ (fun x hx => ?_) h2
  obtain ⟨m, hm⟩ := hq x hx
  exact (al_eq D B.tor x m hm).symm

end Base

theorem area_eq (L : PeriodPair) : TaylorLogMetric.area L.lattice.toAddSubgroup = Formalism.L2.Th1.F.area L := by
  have hA := Formalism.L2.Th1.F.areaPos_thm L
  unfold TaylorLogMetric.area
  apply le_antisymm
  · apply csInf_le
    · exact ⟨0, fun a ha => ha.1.le⟩
    · exact ⟨hA, L.ω₁, L.ω₁_mem_lattice, L.ω₂, L.ω₂_mem_lattice, rfl⟩
  · apply le_csInf
    · exact ⟨_, hA, L.ω₁, L.ω₁_mem_lattice, L.ω₂, L.ω₂_mem_lattice, rfl⟩
    · rintro a ⟨ha, w₁, h₁, w₂, h₂, rfl⟩
      obtain ⟨m, n, rfl⟩ := PeriodPair.mem_lattice.1 h₁
      obtain ⟨k, l, rfl⟩ := PeriodPair.mem_lattice.1 h₂
      have key : (conj ((m : ℂ) * L.ω₁ + (n : ℂ) * L.ω₂) * ((k : ℂ) * L.ω₁ + (l : ℂ) * L.ω₂)).im
          = ((m * l - n * k : ℤ) : ℝ) * (conj L.ω₁ * L.ω₂).im := by
        simp only [map_add, map_mul, map_intCast, Complex.mul_im, Complex.add_im, Complex.add_re, Complex.mul_re,
          Complex.conj_re, Complex.conj_im, Complex.intCast_re, Complex.intCast_im]
        push_cast; ring
      rw [key, abs_mul] at ha ⊢
      have hne : (m * l - n * k : ℤ) ≠ 0 := by
        intro h; rw [h] at ha; simp at ha
      have h1 : (1 : ℝ) ≤ |((m * l - n * k : ℤ) : ℝ)| := by exact_mod_cast Int.one_le_abs hne
      calc Formalism.L2.Th1.F.area L = 1 * |(conj L.ω₁ * L.ω₂).im| := (one_mul _).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)

theorem Base.areaOK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.AreaOK := by
  unfold Base.AreaOK; rw [← B.lat]; exact area_eq B.L

theorem Base.omega_mem {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) : B.ω₀ ∈ B.L.lattice := by
  have h := B.t0.1
  rw [← B.lat] at h
  have e : 2 * (B.ω₀ / 2) = B.ω₀ := by ring
  rw [e] at h; exact h

theorem Base.stdOK_of {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (half : B.ω₀ / 2 ∉ B.L.lattice)
    (isom : IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)))
    (betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
      alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x)
    (betaSemi : IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))))
    (selfDual : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)))
    (idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0)
    (idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0) : B.StdOK :=
  { per := B.omega_mem
    half := half
    isom := isom
    alpha0 := by simp [alphaQ, qOf]
    betaStd := betaStd
    betaSemi := betaSemi
    betaAlpha := fun x => by
      rw [← quadMultiplierRules.2]
      exact quadMultiplierRules.1 _ _ _ _ _ isom _ x
    selfDual := selfDual
    idx₁ := idx₁
    idx₂ := idx₂ }

section Lat0

variable (D : D7) {N N' : ℕ}

theorem homL_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  unfold TaylorLogMetric.homL at hA
  induction hA using Submodule.span_induction with
  | mem A h =>
    have := (mem_stdL D _).1 (h _ (single_mem_stdL D j)) i
    simpa using this
  | zero => exact Subring.zero_mem _
  | add A B _ _ hA hB => exact Subring.add_mem _ hA hB
  | smul r A _ hA => exact Subring.mul_mem _ ⟨r, rfl⟩ hA

theorem YYl_std_entry {A : Matrix (Fin N') (Fin N) D.host.E}
    (hA : A ∈ TaylorLogMetric.YYl D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (i : Fin N') (j : Fin N) :
    A i j ∈ D.host.AA0 := by
  unfold TaylorLogMetric.YYl at hA
  induction hA using Submodule.span_induction with
  | mem B h =>
    obtain ⟨a, ha, A, hA, rfl⟩ := h
    obtain ⟨r, hr⟩ := homL_std_entry D hA i j
    have : (a • A) i j = r • a := by
      rw [Matrix.smul_apply, ← hr, smul_eq_mul, Algebra.smul_def, mul_comm]
    rw [this]
    exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) r ha
  | zero => exact Submodule.zero_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E)
  | add A B _ _ hA hB => exact Submodule.add_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) hA hB
  | smul r A _ hA => exact Submodule.smul_mem (D.host.AA0 : Submodule (𝓞 D.host.E) D.host.E) r hA

theorem single_mem_homL (i : Fin N') (j : Fin N) :
    (Matrix.single i j (1 : D.host.E)) ∈ TaylorLogMetric.homL D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') := by
  refine Submodule.subset_span fun x hx => ?_
  rw [mem_stdL] at hx ⊢
  intro i'
  by_cases h : i = i'
  · subst h; simpa [Matrix.mulVec, dotProduct, Matrix.single_apply] using hx j
  · simp [Matrix.mulVec, dotProduct, Matrix.single_apply, h]

def putE (D : D7) (N N' : ℕ) (i : Fin N') (j : Fin N) : (D.what₂.Tau → ℂ) →+ TaylorLogMetric.VC D N N' where
  toFun v := fun τ i' j' => if i' = i ∧ j' = j then v τ else 0
  map_zero' := by funext τ i' j'; simp
  map_add' := by intro a b; funext τ i' j'; by_cases h : i' = i ∧ j' = j <;> simp [h]

theorem Lat0 (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) :
    TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = powLat (lamMM D (TaylorLogMetric.lamOf D cc δ)) N N' := by
  apply le_antisymm
  · unfold TaylorLogMetric.La
    rw [AddSubgroup.closure_le]
    rintro z ⟨w, hw, A, hA, rfl⟩ i j
    exact AddSubgroup.subset_closure ⟨w, hw, A i j, YYl_std_entry D hA i j, rfl⟩
  · intro z hz
    have key : ∀ (i : Fin N') (j : Fin N), lamMM D (TaylorLogMetric.lamOf D cc δ) ≤
        (TaylorLogMetric.La D (TaylorLogMetric.tor0 D cc δ) (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')).comap (putE D N N' i j) := by
      intro i j
      unfold lamMM
      rw [AddSubgroup.closure_le]
      rintro v ⟨w, hw, a, ha, rfl⟩
      refine AddSubgroup.subset_closure ⟨w, hw, a • Matrix.single i j (1 : D.host.E),
        Submodule.subset_span ⟨a, ha, _, single_mem_homL D i j, rfl⟩, ?_⟩
      funext τ i' j'
      show (if i' = i ∧ j' = j then w * TaylorLogMetric.embT D τ a else 0)
        = w * TaylorLogMetric.embT D τ ((a • Matrix.single i j (1 : D.host.E)) i' j')
      by_cases h : i' = i ∧ j' = j
      · obtain ⟨rfl, rfl⟩ := h; simp
      · have h' : ¬ (i = i' ∧ j = j') := fun e => h ⟨e.1.symm, e.2.symm⟩
        simp [h, Matrix.single_apply, h']
    have hsum : z = ∑ i, ∑ j, putE D N N' i j (fun τ => z τ i j) := by
      funext τ i' j'
      simp only [Finset.sum_apply, putE, AddMonoidHom.coe_mk, ZeroHom.coe_mk]
      rw [Finset.sum_eq_single i', Finset.sum_eq_single j']
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [hsum]
    exact AddSubgroup.sum_mem _ fun i _ => AddSubgroup.sum_mem _ fun j _ => key i j (hz i j)

end Lat0

theorem Base.lat0OK {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (N N' : ℕ) : B.Lat0OK N N' :=
  Lat0 D cc δ

theorem int_of_sign {r : ℝ} (h : Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) = 1 ∨
    Complex.exp ((Real.pi : ℂ) * Complex.I * (r : ℂ)) = -1) : ∃ m : ℤ, r = (m : ℝ) := by
  have h2 : Complex.exp (2 * ((Real.pi : ℂ) * Complex.I * (r : ℂ))) = 1 := by
    rw [two_mul, Complex.exp_add]; rcases h with h | h <;> rw [h] <;> norm_num
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨m, ?_⟩
  have hpi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := Complex.two_pi_I_ne_zero
  have : (r : ℂ) = (m : ℂ) := by
    apply mul_left_cancel₀ hpi; linear_combination hm
  exact_mod_cast this

section Gen

variable (L : PeriodPair) (ω₀ : ℂ) (c : ℝ) {n : Type} [Fintype n] [DecidableEq n]
  (ΛM : AddSubgroup (n → ℂ)) (g : (Fin 4 × n → ℂ) ≃ₗ[ℂ] (Fin 4 × n → ℂ))

theorem qInt_of_stdOK (h : StdOK L ω₀ c ΛM g) {v : n → ℂ} (hv : v ∈ ΛM) :
    ∃ m : ℤ, qOf c (matH (hOne L n)) v = (m : ℝ) := by
  let x : Fin 4 × n → ℂ := fun w => if w.1 = 0 then v w.2 else 0
  have s0 : slice 0 x = v := by funext i; simp [slice, x]
  have s1 : slice 1 x = 0 := by funext i; simp [slice, x]
  have s2 : slice 2 x = 0 := by funext i; simp [slice, x]
  have s3 : slice 3 x = 0 := by funext i; simp [slice, x]
  have hx : x ∈ pow4 ΛM := by
    intro a
    fin_cases a
    · show slice 0 x ∈ ΛM; rw [s0]; exact hv
    · show slice 1 x ∈ ΛM; rw [s1]; exact ΛM.zero_mem
    · show slice 2 x ∈ ΛM; rw [s2]; exact ΛM.zero_mem
    · show slice 3 x ∈ ΛM; rw [s3]; exact ΛM.zero_mem
  have hb := h.betaSemi.1 (g x) ⟨x, hx, rfl⟩
  rw [h.betaAlpha x, Fin.prod_univ_four, s0, s1, s2, s3, h.alpha0, mul_one, mul_one, mul_one] at hb
  exact int_of_sign hb

end Gen

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem qInt0 (hS : B.StdOK) (N N' : ℕ) : B.QInt0 N N' := by
  intro x hx
  have hx' : x ∈ powLat B.lamM N N' := by
    have := B.lat0OK N N'
    unfold Lat0OK at this
    rw [this] at hx; exact hx
  have e : TaylorLogMetric.Hf D B.tor x x = formV (Formalism.L2.Th1.F.area B.L) D.what₂.Tau N N' x x := by
    rw [Hf_eq]
    have := B.areaOK
    unfold AreaOK at this
    show formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N' x x = _
    rw [this]
  rw [e, formV_sum]
  choose m hm using fun (i : Fin N') (j : Fin N) => qInt_of_stdOK _ _ _ _ _ hS (hx' i j)
  refine ⟨∑ i, ∑ j, m i j, ?_⟩
  push_cast
  simp only [Complex.re_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hm i j

theorem thZeroMem (hS : B.StdOK) (N N' : ℕ) : B.ThZeroMem N N' :=
  B.thZeroMem_of hS B.areaOK (B.lat0OK N N') (B.qInt0 hS N N')

theorem vec_parts (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ)
    (hχ : ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' → chiFac χ N N' L L' ≠ 0) :
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' →
      B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 :=
  fun N N' _ _ hA => B.eNat_mem_ne hS hL (B.thZeroMem hS N N') χ hA (hχ N N' _ _ hA)

end Base

theorem inter_self {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (Λ : AddSubgroup V)
    (α : V → ℂ) (hα : IsSemiChar H Λ α) {F : V → ℂ} (hF : F ∈ fixedBy H α Λ) : inter H α Λ Λ F = F := by
  funext z
  have hS : IsReps Λ Λ ({0} : Finset V) :=
    ⟨fun x hx => by rw [Finset.mem_singleton.1 hx]; exact Λ.zero_mem,
      fun x hx y hy _ => by rw [Finset.mem_singleton.1 hx, Finset.mem_singleton.1 hy],
      fun y hy => ⟨0, Finset.mem_singleton_self 0, by simpa using hy⟩⟩
  rw [InterReps_of semicharacterHom V H hH Λ Λ α hα F hF {0} hS z]
  have h1 : relIdx Λ Λ = 1 := AddSubgroup.relIndex_self Λ
  rw [h1]
  simp only [sumU, Finset.sum_singleton, Nat.cast_one, Real.sqrt_one, Complex.ofReal_one, inv_one, one_mul]
  exact hF 0 Λ.zero_mem z

theorem detId_std (D : D7) (N : ℕ) : TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N) = 1 := by
  apply le_antisymm
  · unfold TaylorLogMetric.detId
    rw [Submodule.span_le]
    rintro x ⟨A, hA, rfl⟩
    have hent : ∀ i j, A i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
      intro i j
      have := (mem_stdL D _).1 (hA _ (single_mem_stdL D j)) i
      simpa using this
    choose A' hA' using hent
    have e : A = (algebraMap (𝓞 D.host.E) D.host.E).mapMatrix (Matrix.of A') := by
      ext i j; simp [hA']
    show A.det ∈ (1 : Submodule (𝓞 D.host.E) D.host.E)
    rw [e, ← RingHom.map_det]
    exact Submodule.mem_one.2 ⟨_, rfl⟩
  · rw [Submodule.one_le]
    exact Submodule.subset_span ⟨1, fun v hv => by simpa using hv, by simp⟩

theorem chi_one (D : D7) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : χ 1 = 1 := by
  let _ := D.host.cmStar
  have h := hχ.2 (1 : unitary D.host.E)
  have e : Submodule.span (𝓞 D.host.E) {((1 : unitary D.host.E) : D.host.E)} = 1 := by
    rw [Submodule.one_eq_span]; rfl
  rw [e] at h
  rw [h]; simp

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem thHalf_mem (hS : B.StdOK) (hL : B.LatAll) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    B.thHalf N N' L ∈ Formalism.L2.Th1.H.Th (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') (TaylorLogMetric.al D B.tor)
      (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) :=
  kInterTh _ _ (formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _ _
    (hL.1 N N' L _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)).2 (hL.2 N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)).1 _ (B.thZeroMem hS N N')

theorem eNat_left (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') :
    B.eNat χ N N' L (StandardLatticesGL3.stdL D N') =
      fun z => χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L) ^ (((N' / 2 : ℕ) : ℤ)) * B.thHalf N N' L z := by
  have h1 : B.thMoved N N' L (StandardLatticesGL3.stdL D N') = B.thHalf N N' L :=
    inter_self _ (formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _
      (hL.1 N N' L _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA)).2 (B.thHalf_mem hS hL hA).2
  funext z
  simp only [eNat, chiFac, h1, detId_std, chi_one D χ hχ, one_zpow, mul_one]

theorem eNat_zero (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    (hN : Even N) (hN' : Even N') :
    B.eNat χ N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') = B.thZero N N' := by
  have hA := Formalism.MainNotions.GlobalTheoryTheory.Inhab.Adm_std D N N' hN hN'
  rw [B.eNat_left hS hL χ hχ hA]
  have h1 : B.thHalf N N' (StandardLatticesGL3.stdL D N) = B.thZero N N' :=
    inter_self _ (formV_herm (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau N N') _ _
      (hL.1 N N' _ _ hA).2 (B.thZeroMem hS N N').2
  funext z
  simp only [h1, detId_std, chi_one D χ hχ, one_zpow, one_mul]

theorem eq_change_right (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L'' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L'') :
    B.eNat χ N N' L L'' = fun z => χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N') L'') ^ (-((N / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor L (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L L'')
        (B.eNat χ N N' L (StandardLatticesGL3.stdL D N')) z := by
  rw [B.eNat_left hS hL χ hχ hA]; exact B.eNat_base χ N N' L L''

theorem eq_change_left (hS : B.StdOK) (hL : B.LatAll) (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L₁ : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L₁ L') :
    B.eNat χ N N' L₁ (StandardLatticesGL3.stdL D N') = fun z => χ (TaylorLogMetric.detId D (StandardLatticesGL3.stdL D N) L₁) ^ (((N' / 2 : ℕ) : ℤ)) *
      TaylorLogMetric.Iop D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (TaylorLogMetric.La D B.tor L₁ (StandardLatticesGL3.stdL D N'))
        (B.eNat χ N N' (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) z := by
  rw [B.eNat_left hS hL χ hχ hA, B.eNat_zero hS hL χ hχ hA.1 hA.2.1]; rfl

end Base

section Rec
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) := by
  have h : (Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)
      = -((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)) + (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast; ring

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 := by
  unfold TaylorLogMetric.al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

namespace Base

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)

theorem latAll (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) : B.LatAll := by
  refine ⟨fun N N' L L' hA => ⟨?_, fun x _ => al_sign D _ x, ?_⟩, fun N N' L₁ L₁' L₂ L₂' h₁ h₂ =>
    ⟨IO.La_index_ne_zero cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂, IO.La_index_ne_zero cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁⟩⟩
  · have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    apply le_antisymm
    · intro v hv
      exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
    · intro v hv y hy
      obtain ⟨a, b, -, hab⟩ := hI v hv y hy
      refine ⟨b, ?_⟩
      show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
      rw [hab]; simp
  · intro x hx y hy
    have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    have hs := IO.semiChar_of_HfInt _ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im = (b : ℝ) := by rw [hab]; simp
    rw [hs]
    congr 1
    show Complex.exp (-((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ)))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ))
    rw [him]; exact (exp_pi_int b).symm

theorem chiFac_ne_zero (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : chiFac χ N N' L L' ≠ 0 := by
  have h := character_unit_on_determinant D χ hχ
  have h1 := h N _ L hA.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hA.2.2.1
  have h2 := h N' _ L' hA.2.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hA.2.2.2
  refine mul_ne_zero (zpow_ne_zero _ ?_) (zpow_ne_zero _ ?_)
  · intro e; rw [e] at h1; simp at h1
  · intro e; rw [e] at h2; simp at h2

theorem vec_mem_ne (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) :
    ∀ N N' L L', TaylorLogMetric.admitted D N N' L L' →
      B.eNat χ N N' L L' ∈ TaylorLogMetric.Th D B.tor L L' ∧ B.eNat χ N N' L L' ≠ 0 :=
  B.vec_parts hS (B.latAll hcc hδ h0) χ fun _ _ _ _ hA => chiFac_ne_zero χ hχ hA

theorem chiFac_norm (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    (hA : TaylorLogMetric.admitted D N N' L L') : ‖chiFac χ N N' L L'‖ = 1 := by
  have h := character_unit_on_determinant D χ hχ
  have h1 := h N _ L hA.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N) hA.2.2.1
  have h2 := h N' _ L' hA.2.1 (Formalism.MainNotions.GlobalTheoryTheory.Inhab.stdL_isSD D N') hA.2.2.2
  unfold chiFac
  rw [norm_mul, norm_zpow, norm_zpow, h1, h2, one_zpow, one_zpow, mul_one]

theorem eNat_normSq (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (hA : TaylorLogMetric.admitted D N N' L L') :
    TaylorLogMetric.normSq D B.tor (TaylorLogMetric.La D B.tor L L') (B.eNat χ N N' L L')
      = TaylorLogMetric.normSq D B.tor (TaylorLogMetric.La D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N')) (B.thZero N N') := by
  have hL := B.latAll hcc hδ h0
  have hI := theta_operator_isometry D cc hcc δ hδ
  have e : B.eNat χ N N' L L' = fun z => chiFac χ N N' L L' * B.thMoved N N' L L' z := rfl
  rw [e, normSq_const_mul, chiFac_norm χ hχ hA, one_pow, one_mul]
  have m0 : B.thZero N N' ∈ TaylorLogMetric.Th D B.tor (StandardLatticesGL3.stdL D N) (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of D B.tor _ _ (B.thZeroMem hS N N')
  have m1 : B.thHalf N N' L ∈ TaylorLogMetric.Th D B.tor L (StandardLatticesGL3.stdL D N') :=
    mem_ThSp_of D B.tor _ _ (B.thHalf_mem hS hL hA)
  have s2 := hI N N' _ _ _ _ (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) hA _ m1
  have s1 := hI N N' _ _ _ _ (first_coordinate_admissible hA) (isAdmissible_flagPair_of_unitriangular_left_automorphism hA) _ m0
  exact s2.trans s1

theorem th_indep (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : ThetaNormIndependent D B.tor (B.eNat χ) :=
  fun _ _ _ _ _ _ h₁ h₂ => (B.eNat_normSq hcc hδ h0 hS χ hχ h₁).trans (B.eNat_normSq hcc hδ h0 hS χ hχ h₂).symm

theorem th_U (hcc : TaylorLogMetric.IsCurveIdeal D cc) (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) (h0 : δ ≠ 0) (hS : B.StdOK)
    (χ : TaylorLogMetric.IdE D → ℂ) (hχ : TaylorLogMetric.IsChi D χ) : th22U D B.tor (B.eNat χ) :=
  fun N N' L L' hA x => theta_unitary_linkage D cc hcc δ hδ N N' L L' hA _ (B.vec_mem_ne hcc hδ h0 hS χ hχ N N' L L' hA).1 x

end Base

end Rec

section Isom
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

variable {D : D7}

def emb4 (D : D7) (x : Fin 4 → D.host.E) : Fin 4 × D.what₂.Tau → ℂ := fun w => TaylorLogMetric.embT D w.2 (x w.1)

theorem span_range_emb4_eq_top (D : D7) : Submodule.span ℂ (Set.range (emb4 D)) = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = ∑ a : Fin 4, (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then v (a, w.2) else 0) := by
    funext w
    rw [Finset.sum_apply, Finset.sum_eq_single w.1]
    · simp
    · intro b _ hb; simp [Ne.symm hb]
    · simp
  rw [hv]
  refine Submodule.sum_mem _ fun a _ => ?_
  have key : ∀ u : D.what₂.Tau → ℂ, (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then u w.2 else 0)
      ∈ Submodule.span ℂ (Set.range (emb4 D)) := by
    intro u
    have hu : u ∈ Submodule.span ℝ (Set.range fun b : 𝓞 D.host.E => FL.embP D (b : D.host.E)) := by
      rw [FL.span_embP]; trivial
    induction hu using Submodule.span_induction with
    | mem u h =>
      obtain ⟨b, rfl⟩ := h
      refine Submodule.subset_span ⟨Pi.single a (b : D.host.E), ?_⟩
      funext w
      by_cases h : w.1 = a
      · simp [emb4, h, FL.embP]
      · simp [emb4, h, Pi.single_apply]
    | zero =>
      have : (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then (0 : D.what₂.Tau → ℂ) w.2 else 0) = 0 := by
        funext w; simp
      rw [this]; exact Submodule.zero_mem (Submodule.span ℂ (Set.range (emb4 D)))
    | add x y _ _ hx hy =>
      have : (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then (x + y) w.2 else 0)
          = (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then x w.2 else 0)
            + (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then y w.2 else 0) := by
        funext w; by_cases h : w.1 = a <;> simp [h]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx =>
      have : (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then (r • x) w.2 else 0)
          = (r : ℂ) • (fun w : Fin 4 × D.what₂.Tau => if w.1 = a then x w.2 else 0) := by
        funext w; by_cases h : w.1 = a <;> simp [h]
      rw [this]; exact Submodule.smul_mem _ _ hx
  exact key fun τ => v (a, τ)

theorem isoK_hermitian_sum_eq_emb4_hermitian_sum (γ : IsoK D) (x y : Fin 4 → D.host.E) :
    ∑ w, D.host.φ₀ ((γ.g x w : D.host.K) : D.host.E) * conj (D.host.φ₀ ((γ.g y w : D.host.K) : D.host.E))
      = ∑ w, emb4 D x w * conj (emb4 D y w) := by
  calc ∑ w, D.host.φ₀ ((γ.g x w : D.host.K) : D.host.E) * conj (D.host.φ₀ ((γ.g y w : D.host.K) : D.host.E))
      = D.host.φ₀ (∑ w, algebraMap D.host.K D.host.E (γ.g x w)
          * D.host.conj (algebraMap D.host.K D.host.E (γ.g y w))) := by
        rw [map_sum]; refine Finset.sum_congr rfl fun w _ => ?_
        rw [map_mul, CU.emb_conj]; rfl
    _ = D.host.φ₀ (algebraMap D.host.K D.host.E
          (∑ a, Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a)))) := by rw [γ.isom]
    _ = ∑ a, D.host.φ₀ (algebraMap D.host.K D.host.E
          (Algebra.trace D.host.K D.host.E (x a * D.host.conj (y a)))) := by rw [map_sum, map_sum]
    _ = ∑ a, ∑ τ, TaylorLogMetric.embT D τ (x a * D.host.conj (y a)) :=
        Finset.sum_congr rfl fun a _ => by rw [FL.sum_tau_trace]; rfl
    _ = ∑ w, emb4 D x w * conj (emb4 D y w) := by
        rw [Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun τ _ => ?_
        rw [map_mul, CU.emb_conj]; rfl

theorem blockFourfold_hOne_eq_hOne (L : PeriodPair) (n : Type) [Fintype n] [DecidableEq n] :
    blk4 (hOne L n) = hOne L (Fin 4 × n) := by
  ext ⟨a, i⟩ ⟨a', i'⟩
  simp only [blk4, hOne, Matrix.smul_apply, Matrix.one_apply, Prod.mk.injEq, smul_eq_mul]
  by_cases h1 : a = a' <;> by_cases h2 : i = i' <;> simp [h1, h2]

theorem Base.isomOK {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) :
    IsIsom (matH (blk4 (hOne B.L D.what₂.Tau))) (stdH B.L (Fin 4 × D.what₂.Tau))
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) := by
  rw [blockFourfold_hOne_eq_hOne]
  show ∀ x y, matH (hOne B.L (Fin 4 × D.what₂.Tau)) (B.gC x) (B.gC y) = matH (hOne B.L (Fin 4 × D.what₂.Tau)) x y
  have hS : ∀ x y, matH (hOne B.L (Fin 4 × D.what₂.Tau)) (B.gC (emb4 D x)) (B.gC (emb4 D y))
      = matH (hOne B.L (Fin 4 × D.what₂.Tau)) (emb4 D x) (emb4 D y) := by
    intro x y
    rw [show B.gC (emb4 D x) = _ from B.gC_spec x, show B.gC (emb4 D y) = _ from B.gC_spec y, matH_hOne, matH_hOne,
      isoK_hermitian_sum_eq_emb4_hermitian_sum]
  have h1 : ∀ y, ((matH (hOne B.L (Fin 4 × D.what₂.Tau))).flip (B.gC (emb4 D y))).comp
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      = (matH (hOne B.L (Fin 4 × D.what₂.Tau))).flip (emb4 D y) := by
    intro y
    refine LinearMap.ext_on (span_range_emb4_eq_top D) ?_
    rintro _ ⟨x, rfl⟩
    exact hS x y
  have h2 : ∀ u, (matH (hOne B.L (Fin 4 × D.what₂.Tau)) (B.gC u)).comp
      (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ))
      = matH (hOne B.L (Fin 4 × D.what₂.Tau)) u := by
    intro u
    refine LinearMap.ext_on (span_range_emb4_eq_top D) ?_
    rintro _ ⟨y, rfl⟩
    exact LinearMap.congr_fun (h1 y) u
  intro x y
  exact LinearMap.congr_fun (h2 x) y

theorem Base.stdOK_of' {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ)
    (half : B.ω₀ / 2 ∉ B.L.lattice)
    (betaStd : ∀ x ∈ stdLat B.L (Fin 4 × D.what₂.Tau),
      alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau)) x = stdChar B.L B.ω₀ x)
    (betaSemi : IsSemiChar (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (alphaQ B.cq (stdH B.L (Fin 4 × D.what₂.Tau))))
    (selfDual : IsSelfDual (stdH B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)))
    (idx₁ : relIdx (stdLat B.L (Fin 4 × D.what₂.Tau))
      (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM)) ≠ 0)
    (idx₂ : relIdx (imgLat (B.gC : (Fin 4 × D.what₂.Tau → ℂ) →ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)) (pow4 B.lamM))
      (stdLat B.L (Fin 4 × D.what₂.Tau)) ≠ 0) : B.StdOK :=
  B.stdOK_of half B.isomOK betaStd betaSemi selfDual idx₁ idx₂

end Isom

section KapInh

variable {D : D7}

theorem exists_prime_over (D : D7) (p : ℕ) (hp : p.Prime) :
    ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K), ((p : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := by
  have : Fact p.Prime := ⟨hp⟩
  have : (Ideal.span {(p : ℤ)}).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  obtain ⟨P, hP, hO⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (Ideal.span {(p : ℤ)}) (S := 𝓞 D.host.K)
  have hmem : ((p : ℕ) : 𝓞 D.host.K) ∈ P := by
    have h1 : (p : ℤ) ∈ P.under ℤ := by rw [← hO.over]; exact Ideal.mem_span_singleton_self _
    have h2 := Ideal.mem_comap.1 h1
    simpa using h2
  have hne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hmem
    exact hp.ne_zero (by exact_mod_cast hmem)
  exact ⟨⟨P, hP.isPrime, hne⟩, hmem⟩

theorem exists_gen (D : D7) (𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K)) :
    ∃ π : 𝓞 D.host.K, 𝔭.asIdeal ^ classNumber D.host.K = Ideal.span {π} := by
  have hmem : 𝔭.asIdeal ∈ nonZeroDivisors (Ideal (𝓞 D.host.K)) := mem_nonZeroDivisors_of_ne_zero 𝔭.ne_bot
  have h1 : ClassGroup.mk0 (⟨𝔭.asIdeal, hmem⟩ ^ classNumber D.host.K : nonZeroDivisors (Ideal (𝓞 D.host.K))) = 1 := by
    rw [map_pow]; exact pow_card_eq_one
  have h2 := (ClassGroup.mk0_eq_one_iff (Submonoid.pow_mem _ hmem _)).1 (by simpa using h1)
  obtain ⟨π, hπ⟩ := h2.principal
  exact ⟨π, hπ⟩

theorem KapChoice.nonempty_of (γ₀ : IsoK D)
    (h : ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p) : Nonempty (KapChoice γ₀) := by
  obtain ⟨𝔮, -⟩ := exists_prime_over D 2 Nat.prime_two
  have a1 : ∀ p : ℕ, ∃ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.K),
      p.Prime → SplitK D p → ((p : ℕ) : 𝓞 D.host.K) ∈ 𝔭.asIdeal := by
    intro p
    by_cases hp : p.Prime
    · obtain ⟨𝔭, h𝔭⟩ := exists_prime_over D p hp; exact ⟨𝔭, fun _ _ => h𝔭⟩
    · exact ⟨𝔮, fun h' => absurd h' hp⟩
  choose pp hpp using a1
  choose pi hpi using fun p : ℕ => exists_gen D (pp p)
  have a3 : ∀ p : ℕ, ∃ γ : IsoK D, p.Prime → SplitK D p → γ.AtP p := by
    intro p
    by_cases hp : p.Prime ∧ SplitK D p
    · obtain ⟨γ, hγ⟩ := h p hp.1 hp.2; exact ⟨γ, fun _ _ => hγ⟩
    · exact ⟨γ₀, fun h1 h2 => absurd ⟨h1, h2⟩ hp⟩
  choose gaP hgaP using a3
  choose rt hrt using fun p : ℕ => IsAlgClosed.exists_pow_nat_eq
    (D.host.φ₀ (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)
      / D.host.φ₀ (D.host.conj (((pi p : 𝓞 D.host.K) : D.host.K) : D.host.E)))
    (Nat.pos_of_ne_zero (mul_ne_zero two_ne_zero (classNumber_ne D)))
  exact ⟨⟨pp, hpp, pi, fun p _ _ => hpi p, gaP, hgaP, rt, fun p _ _ => hrt p⟩⟩

theorem Base.nonempty_of (cc : Ideal (𝓞 D.host.K)) (δ : ℂ)
    (hL : ∃ L : PeriodPair, L.lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ)
    (ht : ∃ t : ℂ, GL3Theta.IsTwoTorsionPointUnkilled D (TaylorLogMetric.lamOf D cc δ) t)
    (hγ : ∃ (γ₀ : IsoK D) (gC : (Fin 4 × D.what₂.Tau → ℂ) ≃ₗ[ℂ] (Fin 4 × D.what₂.Tau → ℂ)),
      ∀ x : Fin 4 → D.host.E, gC (fun w => TaylorLogMetric.embT D w.2 (x w.1))
        = fun w => D.host.φ₀ ((γ₀.g x w : D.host.K) : D.host.E))
    (hp : ∀ p : ℕ, p.Prime → SplitK D p → ∃ γ : IsoK D, γ.AtP p) : Nonempty (Base D cc δ) := by
  obtain ⟨L, hL⟩ := hL
  obtain ⟨t, ht⟩ := ht
  obtain ⟨γ₀, gC, hg⟩ := hγ
  obtain ⟨k⟩ := KapChoice.nonempty_of γ₀ hp
  exact ⟨⟨L, hL, 2 * t, by rw [mul_div_cancel_left₀ t two_ne_zero]; exact ht, γ₀, gC, hg, k⟩⟩

end KapInh

theorem conclusion_of_hecke_commutation (D : D7) (C : ℝ)
    (hper : ∀ cc : Ideal (𝓞 D.host.K), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      TaylorLogMetric.per22 D (TaylorLogMetric.tor0 D cc δ))
    (hχ : ∃ χ, TaylorLogMetric.IsChi D χ)
    (h : ∀ cc : Ideal (𝓞 D.host.K), TaylorLogMetric.IsCurveIdeal D cc → ∀ δ : ℂ, TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ →
      ∃ B : Base D cc δ, ∀ χ, TaylorLogMetric.IsChi D χ → B.LateralTheory C χ) : TaylorLogMetric.aux₃ D C := by
  intro cc hcc δ hδ
  obtain ⟨B, hB⟩ := h cc hcc δ hδ
  refine ⟨hper cc hcc δ hδ, hχ, fun χ hc => ⟨B.eNat χ, ?_⟩⟩
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hB χ hc
  exact ⟨a1, a2, a3, a4, a5.1, a5.2, a6⟩

namespace Test

open Formalism.L2.Th1.H.Inh (L7 gU stdData_seven seven_nontrivial)

variable (n : Type) [Fintype n] [DecidableEq n]

theorem seven_moves [Nonempty n] :
    imgLat (gU n : (Fin 4 × n → ℂ) →ₗ[ℂ] (Fin 4 × n → ℂ)) (pow4 (stdLat L7 n)) ≠ stdLat L7 (Fin 4 × n) :=
  seven_nontrivial n

end Test

namespace Test

def isoToy : IsoKG ℂ ℂ (starRingEnd ℂ) Unit where
  g := (LinearEquiv.smulOfNeZero ℂ (Fin 4 → ℂ) Complex.I Complex.I_ne_zero).trans
    (LinearEquiv.funCongrLeft ℂ ℂ (Equiv.prodPUnit (Fin 4)))
  isom := by
    intro x y
    simp only [Algebra.trace_self_apply, Algebra.algebraMap_self, RingHom.id_apply, Fintype.sum_prod_type,
      Finset.univ_unique, Finset.sum_singleton]
    refine Finset.sum_congr rfl fun a _ => ?_
    show (Complex.I * x a) * conj (Complex.I * y a) = x a * conj (y a)
    rw [map_mul, Complex.conj_I]
    linear_combination (-(x a * conj (y a))) * Complex.I_mul_I

end Test

end Formalism.L2.Ker
