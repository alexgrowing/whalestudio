import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRotCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTCHolPhaseRel

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRMat

theorem normSq_rot (ζ : ℂ) (φ : ℝ) :
    Complex.normSq (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = Complex.normSq ζ := by
  rw [Complex.normSq_mul, Complex.normSq_eq_norm_sq (Complex.exp _), Complex.norm_exp_ofReal_mul_I]
  ring

theorem wR_rot (k : ℕ) (TT : ℝ) (ζ : ℂ) (φ : ℝ) :
    wR k TT (ζ * Complex.exp ((φ : ℂ) * Complex.I)) = wR k TT ζ := by
  unfold wR
  rw [normSq_rot]

theorem exists_ann (P : M.Par) : ∃ ζ : ℂ, P.TT < Complex.normSq ζ := by
  refine ⟨((|P.TT| + 1 : ℝ) : ℂ), ?_⟩
  rw [Complex.normSq_ofReal]
  nlinarith [abs_nonneg P.TT, le_abs_self P.TT]

theorem hsVec_zero {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
    [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq] : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  simpa using VLem.hsV_smul (Wp := Wp) (Wq := Wq) 0 0

section

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wp] [FiniteDimensional ℂ Wq]

def rotA (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) (X : Wq →L[ℂ] Wp) : Wq →L[ℂ] Wp :=
  (Bs.π (hL P.k P.r Bs.z φ)).comp (X.comp (Bs.π' (hR P.k P.r Bs.z' φ)))

theorem rotA_sum (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) {ι : Type} (s : Finset ι) (a : ι → ℂ)
    (X : ι → (Wq →L[ℂ] Wp)) : rotA P Bs φ (∑ i ∈ s, a i • X i) = ∑ i ∈ s, a i • rotA P Bs φ (X i) := by
  ext v
  simp [rotA, map_sum, map_smul]

theorem rotA_smul (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (φ : ℝ) (a : ℂ) (X : Wq →L[ℂ] Wp) :
    rotA P Bs φ (a • X) = a • rotA P Bs φ X := by
  ext v
  simp [rotA]

theorem rotM_eq (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (E : M.Ty P → (Wq →L[ℂ] Wp)) (φ : ℝ) (ρ ρ' : M.Ty P) :
    rotM P Bs.z Bs.z' Bs.π Bs.π' E φ ρ ρ' = inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E ρ'))) := rfl

theorem ann_tz (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') {ζ : ℂ}
    (hζ : P.TT < Complex.normSq ζ) : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq ζ := by
  rw [SSTr.tz_eq P Bs hpl]; exact hζ

theorem rot_eqv (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hsec : Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z') (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (φ : ℝ) :
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r φ) =
      rotA P Bs φ ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c
        (NF.muZ P.k P.r Bs.μsec (ζ * Complex.exp ((φ : ℂ) * Complex.I)))) := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hζ1 := ann_tz P Bs hpl hζ
  have hζ2 : Tz P.k P.r Bs.z * Tz P.k P.r Bs.z' < Complex.normSq (ζ * Complex.exp ((φ : ℂ) * Complex.I)) := by
    rw [normSq_rot]; exact hζ1
  have hrot := (hS'.2.2.2.2 ζ hζ1 φ).1
  rw [← hsec] at hrot
  rw [hrot]
  exact Φ.2.2.2 (c, _) (Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1
    (q := (c, ζ * Complex.exp ((φ : ℂ) * Complex.I))) ⟨hc, hζ2⟩) _ (hS'.1 φ).1 _ (hS'.1 φ).2

theorem rot_fib (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (hsec : Bs.μsec = TheSec.theSection P.k P.r Bs.z Bs.z') (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π')
    (c : Fin P.r → ℂ) (hc : c ∈ OmX P.r) (ζ : ℂ) (hζ : P.TT < Complex.normSq ζ) (ψ : ℝ) :
    (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ) ∈
      NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ := by
  intro p hp
  obtain ⟨hp1, hp2, hp3⟩ := hp
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hζ1 := ann_tz P Bs hpl hζ
  have hD := (hS'.2.2.2.2 ζ hζ1 ψ).2 c hc
  rw [← hsec] at hD
  refine (Φ.2.2.2 _ hD _ hp1 _ hp2).symm.trans ?_
  dsimp only
  apply congrArg
  calc p.1 * (NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ) * p.2
      = p.1 * NF.muZ P.k P.r Bs.μsec ζ * (zc P.k P.r ψ * p.2) := by simp only [mul_assoc]
    _ = p.1 * NF.muZ P.k P.r Bs.μsec ζ * (p.2 * zc P.k P.r ψ) := by rw [hS'.2.2.2.1 ψ p.2 hp2]
    _ = (p.1 * NF.muZ P.k P.r Bs.μsec ζ * p.2) * zc P.k P.r ψ := by simp only [mul_assoc]
    _ = NF.muZ P.k P.r Bs.μsec ζ * zc P.k P.r ψ := by rw [hp3]

theorem rotA_add (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (φ ψ : ℝ) (X : Wq →L[ℂ] Wp) : rotA P Bs (φ + ψ) X = rotA P Bs φ (rotA P Bs ψ X) := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  have hL' : hL P.k P.r Bs.z (φ + ψ) = hL P.k P.r Bs.z φ * hL P.k P.r Bs.z ψ := (hS'.2.2.1 φ ψ).1
  have hR' : hR P.k P.r Bs.z' (φ + ψ) = hR P.k P.r Bs.z' ψ * hR P.k P.r Bs.z' φ := by
    rw [add_comm]; exact (hS'.2.2.1 ψ φ).2
  unfold rotA
  rw [hL', hR', hB.2.2.2.2.2.2.1.2 _ (hS'.1 φ).1 _ (hS'.1 ψ).1, hB.2.2.2.2.2.2.2.1.2 _ (hS'.1 ψ).2 _ (hS'.1 φ).2]
  ext v
  simp [ContinuousLinearMap.comp_apply]

theorem rotA_zero (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq) (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π')
    (X : Wq →L[ℂ] Wp) : rotA P Bs 0 X = X := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  unfold rotA
  rw [hS'.2.1.1, hS'.2.1.2.1, hB.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.1.1]
  ext v
  simp

theorem rotA_two_pi (hS : GTRRSec) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (hpl : Q.IsPlace P Bs.z Bs.z' Bs.π Bs.π') (X : Wq →L[ℂ] Wp) : rotA P Bs (2 * Real.pi) X = X := by
  have hB := SSTr.radBase P Bs hpl
  have hS' := hS P.k P.r Bs.z Bs.z' hB.1 hB.2.1 hB.2.2.1 hB.2.2.2.1 hB.2.2.2.2.1
  unfold rotA
  rw [hS'.2.1.2.2.1, hS'.2.1.2.2.2, hB.2.2.2.2.2.2.1.1, hB.2.2.2.2.2.2.2.1.1]
  ext v
  simp

theorem hasDerivAt_pair (hC : GTRRCentre) (P : M.Par) (Bs : B.RealPlaceData P.k P.r Wp Wq)
    (Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π') (x : (Fin P.r → ℂ) × Q.Mx P.k P.r)
    (hx : x ∈ Q.DomR P.k P.r Bs.z Bs.z') (E : Wq →L[ℂ] Wp) (w : ℂ) :
    HasDerivAt (fun φ : ℝ => w * inner ℂ (B.hsVec E) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1 (x.2 * zc P.k P.r φ))))
      (w * (Complex.I * inner ℂ (B.hsVec E) (B.hsVec (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
          Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
            ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x.1) x.2)))) 0 := by
  have h0 := hC P.k P.r Bs.z Bs.z' Wp Wq Bs.π Bs.π' Φ x hx
  have h1 := (hsCLM (Wp := Wp) (Wq := Wq)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) h0
  have h2 := ((hasDerivAt_const (0 : ℝ) (B.hsVec E)).inner ℂ h1).const_mul w
  simp only [Function.comp_def, hsCLM_apply, inner_zero_left, add_zero, VLem.hsV_smul, inner_smul_right] at h2
  exact h2

end

end RRMat

open RRMat in
theorem rotation_matrix_form_holds : GTRRMatFrom := by
  intro hC hS hO Wp Wq _ _ _ _ _ _ P Bs X d hyp hsec e he hk hc Rt s hRK hRt
  obtain ⟨hpl, hk2, -⟩ := hyp
  have hB := SSTr.radBase P Bs hpl
  obtain ⟨ζ₀, hζ₀⟩ := exists_ann P
  set c₀ : Fin P.r → ℂ := fun _ => 1 with hc₀def
  have hc₀ : c₀ ∈ OmX P.r := fun _ => one_ne_zero
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  set w₀ : ℂ := ((wR P.k P.TT ζ₀ : ℝ) : ℂ) with hw₀def
  have hw₀ : w₀ ≠ 0 := by simp only [hw₀def]; exact_mod_cast (SSTr.wR_pos P hζ₀).ne'

  have hex : ∀ ρ' : M.Ty P, ∃ Φ : Q.RadSp P.k P.r Bs.z Bs.z' Bs.π Bs.π',
      trR P Bs e Φ = (fun τ => if τ = ρ' then (1 : MA.SmQ P.r P.TT) else 0) ∧
      ∀ q : MA.Qp P.r P.TT, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2) =
        ∑ ρ, ((((wR P.k P.TT q.1.2)⁻¹ : ℝ) : ℂ) *
          ((if ρ = ρ' then (1 : MA.SmQ P.r P.TT) else 0 : MA.SmQ P.r P.TT) : MA.Qp P.r P.TT → ℂ) q) • e ρ q.1.2 :=
    fun ρ' => SSTr.exists_tr P Bs hpl hk2 e he _
  choose Φ hΦtr hΦv using hex

  have hval : ∀ ρ' (φ : ℝ), (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀
      (NF.muZ P.k P.r Bs.μsec (ζ₀ * Complex.exp ((φ : ℂ) * Complex.I))) = w₀⁻¹ • E ρ' := by
    intro ρ' φ
    have hq : ((c₀, ζ₀ * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hc₀, by rw [normSq_rot]; exact hζ₀⟩
    have h := hΦv ρ' ⟨_, hq⟩
    simp only at h
    rw [h, Finset.sum_eq_single ρ']
    · simp [wR_rot, hw₀def, heE]
    · intro τ _ hτ
      simp [hτ]
    · simp

  have hAE : ∀ ρ' (φ : ℝ), rotA P Bs φ (E ρ') =
      w₀ • (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀ (NF.muZ P.k P.r Bs.μsec ζ₀ * zc P.k P.r φ) := by
    intro ρ' φ
    rw [rot_eqv hS P Bs hpl hsec (Φ ρ') c₀ hc₀ ζ₀ hζ₀ φ, hval, rotA_smul, smul_smul, mul_inv_cancel₀ hw₀, one_smul]
  have hfib : ∀ ρ' (ψ : ℝ), rotA P Bs ψ (E ρ') ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₀ := by
    intro ρ' ψ
    rw [hAE]
    intro p hp
    have h := rot_fib hS P Bs hpl hsec (Φ ρ') c₀ hc₀ ζ₀ hζ₀ ψ p hp
    rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul, h]
  have hexp : ∀ Y ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' ζ₀,
      Y = ∑ σ, inner ℂ (B.hsVec (E σ)) (B.hsVec Y) • E σ := by
    intro Y hY
    have h := (he.2 ζ₀ hζ₀).2.2 Y hY
    simpa only [heE] using h
  have horth : ∀ ρ ρ', inner ℂ (B.hsVec (E ρ)) (B.hsVec (E ρ')) = if ρ = ρ' then (1 : ℂ) else 0 := by
    intro ρ ρ'
    have h := (he.2 ζ₀ hζ₀).2.1 ρ ρ'
    simpa only [heE] using h

  set Mf : ℝ → Matrix (M.Ty P) (M.Ty P) ℂ :=
    fun φ => Matrix.of fun ρ ρ' => rotM P Bs.z Bs.z' Bs.π Bs.π' (fun σ => e σ 0) φ ρ ρ' with hMfdef
  have hMf : ∀ φ ρ ρ', Mf φ ρ ρ' = inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E ρ'))) := fun _ _ _ => rfl
  set x₀ : (Fin P.r → ℂ) × Q.Mx P.k P.r := (c₀, NF.muZ P.k P.r Bs.μsec ζ₀) with hx₀def
  have hx₀ : x₀ ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := (c₀, ζ₀)) ⟨hc₀, ann_tz P Bs hpl hζ₀⟩
  set Bm : Matrix (M.Ty P) (M.Ty P) ℂ := Matrix.of fun ρ ρ' =>
    w₀ * (Complex.I * inner ℂ (B.hsVec (E ρ)) (B.hsVec (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
      Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
        ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1) x₀.2))) with hBmdef
  have h0 : Mf 0 = 1 := by
    ext ρ ρ'
    rw [hMf, rotA_zero hS P Bs hpl, horth, Matrix.one_apply]
  have h2π : Mf (2 * Real.pi) = 1 := by
    ext ρ ρ'
    rw [hMf, rotA_two_pi hS P Bs hpl, horth, Matrix.one_apply]
  have hmul : ∀ φ ψ, Mf (φ + ψ) = Mf φ * Mf ψ := by
    intro φ ψ
    ext ρ ρ'
    rw [hMf, rotA_add hS P Bs hpl, hexp _ (hfib ρ' ψ), rotA_sum, SSTr.hsVec_sum, inner_sum, Matrix.mul_apply]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [VLem.hsV_smul, inner_smul_right, hMf, hMf, mul_comm]
  have hder : ∀ ρ ρ', HasDerivAt (fun φ => Mf φ ρ ρ') (Bm ρ ρ') 0 := by
    intro ρ ρ'
    have h := hasDerivAt_pair hC P Bs (Φ ρ') x₀ hx₀ (E ρ) w₀
    have hfun : (fun φ => Mf φ ρ ρ') = fun φ : ℝ => w₀ * inner ℂ (B.hsVec (E ρ))
        (B.hsVec ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 (x₀.2 * zc P.k P.r φ))) := by
      funext φ
      rw [hMf, hAE, VLem.hsV_smul, inner_smul_right]
    rw [hfun]
    exact h
  have hoff : ∀ ρ ρ', ρ ≠ ρ' → Bm ρ ρ' = 0 := by
    intro ρ ρ' hne

    set f : M.Ty P → ℂ := fun τ => if τ = ρ then 1 else 0 with hfdef
    have hkz : (d.κ f).1 (Φ ρ') = 0 := by
      apply SSTr.trR_inj P Bs hpl hk2 e he
      funext τ
      apply Subtype.ext
      funext q
      rw [hk f (Φ ρ'), actA_kap, hΦtr ρ', SSTr.trR_apply P Bs hpl hk2 e he 0]
      simp only [rawR, ZeroMemClass.coe_zero, Pi.zero_apply, hsVec_zero, inner_zero_right, mul_zero]
      by_cases hτ : τ = ρ
      · subst hτ
        simp [hne]
      · simp [f, hτ]
    have hRz : (d.κ f).1 (Rt (Φ ρ')) = 0 := by
      rw [← hRK f (Φ ρ'), hkz, map_zero]
    set q₀ : MA.Qp P.r P.TT := ⟨(c₀, ζ₀), hc₀, hζ₀⟩ with hq₀def
    have h1 := congrArg (fun F : M.Ty P → MA.SmQ P.r P.TT => (F ρ : MA.Qp P.r P.TT → ℂ) q₀) (hk f (Rt (Φ ρ')))
    rw [hRz, actA_kap, SSTr.trR_apply P Bs hpl hk2 e he 0] at h1
    simp only [SetLike.val_smul, Pi.smul_apply, smul_eq_mul, hfdef, if_pos rfl, one_mul] at h1
    rw [SSTr.trR_apply P Bs hpl hk2 e he] at h1
    simp only [rawR, ZeroMemClass.coe_zero, Pi.zero_apply, hsVec_zero, inner_zero_right, mul_zero] at h1
    have hwq : ((wR P.k P.TT ζ₀ : ℝ) : ℂ) ≠ 0 := hw₀
    have hRt0 : inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Rt (Φ ρ') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) c₀
        (NF.muZ P.k P.r Bs.μsec ζ₀))) = 0 := by
      have h1' := h1.symm
      rw [heE] at h1'
      exact (mul_eq_zero.1 h1').resolve_left hwq
    have hsum := hRt (Φ ρ') x₀ hx₀
    have hS0 : (∑ a : Fin (Q.mdim P.k P.r (Fin.last P.r)),
        Q.EH P.k P.r (Q.posL P.k P.r (Fin.last P.r) a) (Q.posL P.k P.r (Fin.last P.r) a)
          ((Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1) x₀.2) =
        (Rt (Φ ρ') : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 - ((s : ℂ)) • (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 := by
      rw [hsum]; abel
    have hv0 : (Φ ρ' : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) x₀.1 x₀.2 = w₀⁻¹ • E ρ' := by
      have h := hval ρ' 0
      simpa using h
    show w₀ * (Complex.I * inner ℂ (B.hsVec (E ρ)) (B.hsVec _)) = 0
    rw [hS0, hv0, sub_eq_add_neg, VLem.hsV_add, inner_add_right, ← neg_smul, smul_smul, VLem.hsV_smul,
      inner_smul_right, horth, if_neg hne, mul_zero, add_zero]
    simp only [hx₀def] at hRt0 ⊢
    rw [hRt0]
    ring
  obtain ⟨n, hn⟩ := hO (M.Ty P) Mf Bm h0 hmul h2π hder hoff
  exact ⟨n, fun φ ρ ρ' => hn φ ρ ρ'⟩

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
