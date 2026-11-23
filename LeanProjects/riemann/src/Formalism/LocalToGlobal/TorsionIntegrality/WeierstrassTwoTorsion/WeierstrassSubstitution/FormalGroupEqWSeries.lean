import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.StatementG
import Formalism.EllipticTorsion.FormalGroupPointsNoTorsion

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace Univ

abbrev Z : Type := MvPolynomial (Fin 5) ℤ

def W₀ : WeierstrassCurve Z :=
  ⟨MvPolynomial.X 0, MvPolynomial.X 1, MvPolynomial.X 2, MvPolynomial.X 3, MvPolynomial.X 4⟩

def φ_of {R : Type u} [CommRing R] (W : WeierstrassCurve R) : Z →+* R :=
  MvPolynomial.eval₂Hom (Int.castRingHom R) ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

theorem map_eq {R : Type u} [CommRing R] (W : WeierstrassCurve R) : W₀.map (φ_of W) = W := by
  cases W
  simp [Univ.W₀, Univ.φ_of, WeierstrassCurve.map]

abbrev K₀ : Type := FractionRing Z

def ι : Z →+* K₀ := algebraMap Z K₀

theorem ι_injective : Function.Injective ι := IsFractionRing.injective Univ.Z Univ.K₀

instance charZero_K₀ : CharZero K₀ := charZero_of_injective_algebraMap (IsFractionRing.injective Z K₀)

def WK : WeierstrassCurve K₀ := W₀.map ι

theorem mv_map_injective {σ : Type*} {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) :
    Function.Injective (MvPowerSeries.map f : MvPowerSeries σ A →+* MvPowerSeries σ B) := by
  intro a b h
  ext e
  apply hf
  have h1 := congrArg (MvPowerSeries.coeff e) h
  simpa using h1

theorem ps_map_injective {A : Type*} {B : Type*} [CommRing A] [CommRing B] (f : A →+* B)
    (hf : Function.Injective f) : Function.Injective (PowerSeries.map f) := by
  intro a b h
  ext e
  apply hf
  have h1 := congrArg (PowerSeries.coeff e) h
  simpa using h1

theorem mv_transfer {σ : Type*} {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A B : MvPowerSeries σ Z} (h : MvPowerSeries.map ι A = MvPowerSeries.map ι B) :
    MvPowerSeries.map (φ_of W) A = MvPowerSeries.map (φ_of W) B := by
  rw [mv_map_injective ι ι_injective h]

theorem ps_transfer {R : Type u} [CommRing R] (W : WeierstrassCurve R)
    {A B : Z⟦X⟧} (h : PowerSeries.map ι A = PowerSeries.map ι B) :
    PowerSeries.map (φ_of W) A = PowerSeries.map (φ_of W) B := by
  rw [ps_map_injective ι ι_injective h]

end Univ

namespace Fgl1

local notation "L" i => MvPowerSeries.coeff (Finsupp.single i 1)
local notation "cc" => MvPowerSeries.constantCoeff

section Tools

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S]

theorem mv_map_invOfUnit {σ : Type*} (φ : R →+* S) (a : MvPowerSeries σ R) (e : Rˣ) (e' : Sˣ)
    (h : cc a = e) (h' : φ e = e') :
    MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by
  have h1 : a * MvPowerSeries.invOfUnit a e = 1 := MvPowerSeries.mul_invOfUnit a e h
  have h2 : MvPowerSeries.map φ a * MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [MvPowerSeries.constantCoeff_map, h, h'])
  have h3 : MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) = 1 := by
    rw [← map_mul, h1, map_one]
  calc MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)
      = MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e) *
          (MvPowerSeries.map φ a * MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e') := by
        rw [h2, mul_one]
    _ = (MvPowerSeries.map φ a * MvPowerSeries.map φ (MvPowerSeries.invOfUnit a e)) *
          MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by ring
    _ = MvPowerSeries.invOfUnit (MvPowerSeries.map φ a) e' := by rw [h3, one_mul]

theorem L_mul (φ ψ : MvPowerSeries (Fin 2) R) (i : Fin 2) :
    (L i) (φ * ψ) = cc φ * (L i) ψ + (L i) φ * cc ψ := by
  rw [MvPowerSeries.coeff_mul, Finsupp.antidiagonal_single]
  simp [Finset.Nat.antidiagonal_succ]
  try ring

theorem L_C (a : R) (i : Fin 2) : (L i) (MvPowerSeries.C a : MvPowerSeries (Fin 2) R) = 0 := by
  simp [MvPowerSeries.coeff_C]

theorem L_X (i j : Fin 2) :
    (L i) (MvPowerSeries.X j : MvPowerSeries (Fin 2) R) = if i = j then 1 else 0 := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj one_ne_zero]

theorem sub_cancel {f : MvPowerSeries (Fin 2) R}
    (h : f * (MvPowerSeries.X 0 - MvPowerSeries.X 1) = 0) : f = 0 := by
  have key : ∀ e : Fin 2 →₀ ℕ,
      (if Finsupp.single 0 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 0 1) f else 0) =
      (if Finsupp.single 1 1 ≤ e then MvPowerSeries.coeff (e - Finsupp.single 1 1) f else 0) := by
    intro e
    have h1 := congrArg (MvPowerSeries.coeff e) h
    rw [mul_sub, map_sub, map_zero, sub_eq_zero,
      show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
      show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
      MvPowerSeries.coeff_mul_monomial, MvPowerSeries.coeff_mul_monomial] at h1
    simpa using h1
  let mk : ℕ → ℕ → (Fin 2 →₀ ℕ) := fun a b => Finsupp.single 0 a + Finsupp.single 1 b
  have hall : ∀ b a, MvPowerSeries.coeff (mk a b) f = 0 := by
    intro b
    induction b with
    | zero =>
      intro a
      have h := key (mk (a + 1) 0)
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hn : ¬ Finsupp.single 1 1 ≤ mk (a + 1) 0 := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_neg hn] at h
      have e1 : mk (a + 1) 0 - Finsupp.single 0 1 = mk a 0 := by
        ext i
        fin_cases i <;> simp [mk]
      rw [e1] at h
      exact h
    | succ b ih =>
      intro a
      have h := key (mk (a + 1) (b + 1))
      have hp : Finsupp.single 0 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      have hq : Finsupp.single 1 1 ≤ mk (a + 1) (b + 1) := by
        rw [Finsupp.single_le_iff]
        simp [mk]
      rw [if_pos hp, if_pos hq] at h
      have e1 : mk (a + 1) (b + 1) - Finsupp.single 0 1 = mk a (b + 1) := by
        ext i
        fin_cases i <;> simp [mk]
      have e2 : mk (a + 1) (b + 1) - Finsupp.single 1 1 = mk (a + 1) b := by
        ext i
        fin_cases i <;> simp [mk]
      rw [e1, e2, ih (a + 1)] at h
      exact h
  ext e
  have he : e = mk (e 0) (e 1) := by
    ext i
    fin_cases i <;> simp [mk]
  rw [he, hall]
  simp

open Formalism.ELL.WeierstrassChordSeries in

theorem vieta' {A : Type*} [CommRing A] {a1 a2 a3 a4 a6 l n z1 z2 z3 : A}
    (hz : ∀ f : A, f * (z1 - z2) = 0 → f = 0)
    (h1 : G a1 a2 a3 a4 a6 z1 (l * z1 + n) = 0) (h2 : G a1 a2 a3 a4 a6 z2 (l * z2 + n) = 0)
    (he1 : c3 a2 a4 a6 l * (z1 + z2 + z3) + c2 a1 a2 a3 a4 a6 l n = 0) :
    G a1 a2 a3 a4 a6 z3 (l * z3 + n) = 0 := by
  have hQ : (c3 a2 a4 a6 l * (z1 ^ 2 + z1 * z2 + z2 ^ 2) + c2 a1 a2 a3 a4 a6 l n * (z1 + z2) +
      (a1 * n + 2 * a3 * l * n + a4 * n ^ 2 + 3 * a6 * l * n ^ 2 - l)) * (z1 - z2) = 0 := by
    unfold G at h1 h2
    unfold c3 c2
    linear_combination h1 - h2
  have hQ0 := hz _ hQ
  unfold G at h1 ⊢
  unfold c3 c2 at hQ0 he1
  linear_combination h1 + (z3 - z1) * hQ0 + (z3 - z1) * (z3 - z2) * he1

open Formalism.ELL.WeierstrassChordSeries in
theorem weq_iff (W : WeierstrassCurve R) (s v : MvPowerSeries (Fin 2) R) :
    Formalism.ELL.WEqAt W s v ↔ G (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
      (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) s v = 0 := by
  unfold Formalism.ELL.WEqAt G
  simp only [MvPowerSeries.smul_eq_C_mul]
  constructor
  · intro h
    linear_combination (-1 : MvPowerSeries (Fin 2) R) * h
  · intro h
    linear_combination (-1 : MvPowerSeries (Fin 2) R) * h

end Tools

section W

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

theorem wSer_fixed : Formalism.ELL.WFixed W (wSer W) := (Formalism.ELL.wSeriesUnique R W).choose_spec.1

theorem wSer_unique {w : R⟦X⟧} (hw : Formalism.ELL.WFixed W w) : w = wSer W := (Formalism.ELL.wSeriesUnique R W).choose_spec.2 w hw

theorem wSer_low : coeff 0 (wSer W) = 0 ∧ coeff 1 (wSer W) = 0 ∧ coeff 2 (wSer W) = 0 ∧
    coeff 3 (wSer W) = 1 := by
  obtain ⟨h0, hfix⟩ := wSer_fixed W
  have c0 : coeff 0 (wSer W) = 0 := by rwa [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  have c1 : coeff 1 (wSer W) = 0 := by
    have h := congrArg (coeff 1) hfix
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, mul_assoc] at h
    exact h
  have c2 : coeff 2 (wSer W) = 0 := by
    have h := congrArg (coeff 2) hfix
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, c1, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, mul_assoc] at h
    exact h
  have c3 : coeff 3 (wSer W) = 1 := by
    have h := congrArg (coeff 3) hfix
    simp [pow_succ, PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ, c0, c1, c2, PowerSeries.coeff_X_pow,
      PowerSeries.coeff_X, mul_assoc] at h
    exact h
  exact ⟨c0, c1, c2, c3⟩

theorem wSer_map (φ : R →+* S) : PowerSeries.map φ (wSer W) = wSer (W.map φ) := by
  refine wSer_unique (W.map φ) ⟨?_, ?_⟩
  · have h0 := (wSer_fixed W).1
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      PowerSeries.coeff_zero_eq_constantCoeff_apply, h0, map_zero]
  · have h := congrArg (PowerSeries.map φ) (wSer_fixed W).2
    simpa [map_add, map_mul, map_pow] using h

end W

section Map

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

theorem coeff_lam (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (lam W) = coeff (e 0 + e 1 + 1) (wSer W) := rfl

theorem lam_map : MvPowerSeries.map φ (lam W) = lam (W.map φ) := by
  ext e
  rw [MvPowerSeries.coeff_map, coeff_lam, coeff_lam, ← wSer_map, PowerSeries.coeff_map]

theorem nu_map : MvPowerSeries.map φ (nu W) = nu (W.map φ) := by
  simp only [nu, map_sub, map_mul, MvPowerSeries.map_X, lam_map]
  rw [PowerSeries.map_subst (PowerSeries.HasSubst.X 0), MvPowerSeries.map_X, wSer_map]

theorem cThree_map : MvPowerSeries.map φ (cThree W) = cThree (W.map φ) := by
  simp [cThree, map_add, map_mul, map_pow, lam_map]

theorem cTwo_map : MvPowerSeries.map φ (cTwo W) = cTwo (W.map φ) := by
  simp [cTwo, map_add, map_mul, map_pow, lam_map, nu_map, map_ofNat]

end Map

section Coeffs

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

abbrev Wi (i : Fin 2) : MvPowerSeries (Fin 2) R :=
  (wSer W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)

theorem coeff_Wi (i : Fin 2) (e : Fin 2 →₀ ℕ) :
    MvPowerSeries.coeff e (Wi W i)
      = if e = Finsupp.single i (e i) then coeff (e i) (wSer W) else 0 := by
  classical
  show MvPowerSeries.coeff e ((wSer W).subst (MvPowerSeries.X i : MvPowerSeries (Fin 2) R)) = _
  rw [PowerSeries.coeff_subst (PowerSeries.HasSubst.X i), finsum_eq_single _ (e i)]
  · simp only [MvPowerSeries.coeff_X_pow, smul_eq_mul]
    split_ifs <;> simp
  · intro d hd
    simp only [MvPowerSeries.coeff_X_pow]
    rw [if_neg]
    · simp
    · intro h
      apply hd
      rw [h]
      simp

open Formalism.ELL.WeierstrassChordSeries (eq_single_iff) in
theorem lam_mul : (MvPowerSeries.X 1 - MvPowerSeries.X 0) * lam W = Wi W 1 - Wi W 0 := by
  ext e
  have he := eq_single_iff e
  rw [sub_mul, map_sub, map_sub,
    show (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 1 1) 1 from rfl,
    show (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) R) = MvPowerSeries.monomial (Finsupp.single 0 1) 1 from rfl,
    MvPowerSeries.coeff_monomial_mul, MvPowerSeries.coeff_monomial_mul, coeff_Wi, coeff_Wi, coeff_lam, coeff_lam]
  simp only [he.1, he.2, Finsupp.single_le_iff, Finsupp.tsub_apply, Finsupp.single_apply, one_mul]
  by_cases h0 : e 0 = 0 <;> by_cases h1 : e 1 = 0 <;> simp [h0, h1]
  · rw [if_pos (by omega), Nat.sub_add_cancel (by omega)]
  · rw [if_pos (by omega), Nat.sub_add_cancel (by omega)]
  · rw [if_pos (by omega), if_pos (by omega), show e 0 + (e 1 - 1) + 1 = e 0 - 1 + e 1 + 1 by omega, sub_self]

theorem Wi_cc (i : Fin 2) : cc (Wi W i) = 0 := by
  have h0 : coeff 0 (wSer W) = 0 := by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (wSer_fixed W).1
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_Wi]
  simp [h0]

theorem Wi_L (i j : Fin 2) : (L j) (Wi W i) = 0 := by
  have h0 : coeff 0 (wSer W) = 0 := (wSer_low W).1
  have h1 : coeff 1 (wSer W) = 0 := (wSer_low W).2.1
  rw [coeff_Wi]
  split_ifs
  · simp only [Finsupp.single_apply]
    split_ifs <;> simp [h0, h1]
  · rfl

theorem lam_cc : cc (lam W) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_lam]
  simpa using (wSer_low W).2.1

theorem lam_L (i : Fin 2) : (L i) (lam W) = 0 := by
  rw [coeff_lam]
  fin_cases i <;> simp [(wSer_low W).2.2.1]

theorem nu_cc : cc (nu W) = 0 := by
  have h := Wi_cc W 0
  simp only [Wi] at h
  simp [nu, h, lam_cc]

theorem nu_L (i : Fin 2) : (L i) (nu W) = 0 := by
  have h := Wi_L W 0 i
  simp only [Wi] at h
  rw [nu, map_sub, L_mul, lam_cc, lam_L, h]
  simp

theorem cThree_cc : cc (cThree W) = 1 := by
  simp [cThree, lam_cc]

theorem cTwo_cc : cc (cTwo W) = 0 := by
  simp [cTwo, lam_cc, nu_cc]

theorem cTwo_L (i : Fin 2) : (L i) (cTwo W) = 0 := by
  simp [cTwo, sq, L_mul, L_C, lam_cc, lam_L, nu_cc, nu_L]

theorem uThird_cc : cc (uThird W) = 0 := by
  simp [uThird, cTwo_cc]

theorem uThird_L (i : Fin 2) : (L i) (uThird W) = -1 := by
  simp [uThird, L_mul, L_X, cTwo_cc, cTwo_L]
  fin_cases i <;> simp

theorem wThird_cc : cc (wThird W) = 0 := by
  simp [wThird, lam_cc, nu_cc, uThird_cc]

abbrev dd : MvPowerSeries (Fin 2) R :=
  -1 + MvPowerSeries.C W.a₁ * uThird W + MvPowerSeries.C W.a₃ * wThird W

theorem dd_cc : cc (dd W) = -1 := by
  simp [dd, uThird_cc, wThird_cc]

theorem fgl_cc : cc (fgl W) = 0 := by
  simp [fgl, uThird_cc]

theorem fgl_L (i : Fin 2) : (L i) (fgl W) = 1 := by
  rw [fgl, L_mul, uThird_cc, uThird_L, MvPowerSeries.constantCoeff_invOfUnit]
  simp

end Coeffs

section Map2

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] (W : WeierstrassCurve R) (φ : R →+* S)

theorem uThird_map : MvPowerSeries.map φ (uThird W) = uThird (W.map φ) := by
  simp only [uThird, map_sub, map_neg, map_mul, MvPowerSeries.map_X, cTwo_map]
  rw [mv_map_invOfUnit φ (cThree W) 1 1 (by simp [cThree_cc]) (by simp), cThree_map]

theorem wThird_map : MvPowerSeries.map φ (wThird W) = wThird (W.map φ) := by
  simp [wThird, map_add, map_mul, lam_map, uThird_map, nu_map]

theorem fgl_map : MvPowerSeries.map φ (fgl W) = fgl (W.map φ) := by
  simp only [fgl]
  rw [map_mul, mv_map_invOfUnit φ _ (-1) (-1) (by simpa using dd_cc W) (by simp)]
  simp [map_add, map_mul, uThird_map, wThird_map]

theorem wSer_univ : wSer W = PowerSeries.map (Univ.φ_of W) (wSer Univ.W₀) := by
  rw [wSer_map, Univ.map_eq]

theorem fgl_univ : fgl W = MvPowerSeries.map (Univ.φ_of W) (fgl Univ.W₀) := by
  rw [fgl_map, Univ.map_eq]

theorem fgl_WK : MvPowerSeries.map Univ.ι (fgl Univ.W₀) = fgl Univ.WK := fgl_map Univ.W₀ Univ.ι

end Map2

section Third

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

open Formalism.ELL.WeierstrassChordSeries (G c3 c2) in
theorem wThird_eq : wThird W = (wSer W).subst (uThird W) := by
  have hw := wSer_fixed W
  have hUs := fun (s : MvPowerSeries (Fin 2) R) (hs : cc s = 0) =>
    Formalism.ELL.wSubstUnique R W (wSer W) hw (Fin 2) s hs
  have h0 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 0) (by simp)).1
  have h1 := (weq_iff W _ _).mp (hUs (MvPowerSeries.X 1) (by simp)).1
  have hW0 : Wi W 0 = lam W * MvPowerSeries.X 0 + nu W := by unfold nu; ring
  have hW1 : Wi W 1 = lam W * MvPowerSeries.X 1 + nu W := by
    have := lam_mul W; unfold nu; linear_combination -this
  change G _ _ _ _ _ _ (Wi W 0) = 0 at h0
  change G _ _ _ _ _ _ (Wi W 1) = 0 at h1
  have hinv : cThree W * MvPowerSeries.invOfUnit (cThree W) 1 = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [cThree_cc]; rfl)
  have he1 : c3 (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) *
      (MvPowerSeries.X 0 + MvPowerSeries.X 1 + uThird W) +
      c2 (MvPowerSeries.C W.a₁) (MvPowerSeries.C W.a₂) (MvPowerSeries.C W.a₃)
        (MvPowerSeries.C W.a₄) (MvPowerSeries.C W.a₆) (lam W) (nu W) = 0 := by
    change cThree W * _ + cTwo W = 0
    rw [uThird]
    linear_combination (-cTwo W) * hinv
  rw [hW0] at h0
  rw [hW1] at h1
  have hG3 := vieta' (fun f hf => sub_cancel hf) h0 h1 he1
  exact (hUs (uThird W) (uThird_cc W)).2 (wThird W) (wThird_cc W) ((weq_iff W _ _).mpr hG3)

theorem fgl_eq : fgl W = (iSer W).subst (uThird W) := by
  have ha : PowerSeries.HasSubst (uThird W) := HasSubst.of_constantCoeff_zero (uThird_cc W)
  have hic : constantCoeff (iDen W) = ((-1 : Rˣ) : R) := by
    simp [iDen, (wSer_fixed W).1]
  have e := congrArg (PowerSeries.subst (uThird W)) (PowerSeries.mul_invOfUnit (iDen W) (-1) hic)
  have hs : (iDen W).subst (uThird W) = dd W := by
    unfold iDen
    rw [← PowerSeries.coe_substAlgHom ha]
    simp only [map_add, map_neg, map_one, map_mul]
    rw [PowerSeries.coe_substAlgHom ha, PowerSeries.subst_C, PowerSeries.subst_C,
      PowerSeries.subst_X ha, ← wThird_eq]
  have h1 : (1 : PowerSeries R).subst (uThird W) = 1 := by
    rw [← PowerSeries.coe_substAlgHom ha, map_one]
  rw [PowerSeries.subst_mul ha, hs, h1] at e
  have e2 : dd W * MvPowerSeries.invOfUnit (dd W) (-1) = 1 :=
    MvPowerSeries.mul_invOfUnit _ _ (by rw [dd_cc]; simp)
  have hinv : (invOfUnit (iDen W) (-1)).subst (uThird W) = MvPowerSeries.invOfUnit (dd W) (-1) :=
    left_inv_eq_right_inv (by rw [mul_comm]; exact e) e2
  rw [iSer, PowerSeries.subst_mul ha, PowerSeries.subst_X ha, hinv, fgl]

end Third

section Field

variable {K : Type u} [Field K] (W : WeierstrassCurve K)

open Formalism.ELL.WeierstrassChordSeries (z3 w3 F2) in
theorem formal_group_eq_w_series : fgl W = F2 W (wSer W) := by
  have h3 : uThird W = z3 W (wSer W) := by
    unfold uThird z3
    rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [cThree_cc]; rfl)]
    rfl
  have h4 : wThird W = w3 W (wSer W) := by
    unfold wThird w3
    rw [h3]
    rfl
  unfold fgl F2
  rw [MvPowerSeries.invOfUnit_eq' _ _ (by rw [dd_cc]; simp), h3, h4]
  rfl

end Field

end Fgl1

theorem formal_group_map : FglMap.{u, v} := fun _ _ _ _ φ W => Fgl1.fgl_map W φ

theorem formal_group_chord : FglChord.{u} := by
  intro R _ W
  refine ⟨?_, Fgl1.uThird_cc W, Fgl1.wThird_eq W, Fgl1.fgl_eq W, Fgl1.fgl_cc W, Fgl1.fgl_L W 0, Fgl1.fgl_L W 1⟩
  rw [mul_comm]
  exact Fgl1.lam_mul W

theorem formal_group_sum : FglSum.{u} := by
  intro K _ W
  rw [Fgl1.formal_group_eq_w_series]
  exact Formalism.ELL.WeierstrassChordSeries.chord Formalism.ELL.wSubstUnique (Fgl1.wSer_fixed W)

end Formalism.L2.Th1.A
