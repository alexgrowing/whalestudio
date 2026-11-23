import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TestObj
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsCoprimeTwoSubRtTwoAddRt
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.OneAddZeta21PowSevenAddPowFourteenEqZero
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange

noncomputable section

open NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

def AllClassesSt : Prop :=
  ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (U : FamilyUnif Xo σ ty),
    l.A = 1 → σ (baseKA l).ρ = H.rt0 → IsTypeFn H D.p D.q ty →
    ∀ (D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La), D'.p = D.p → D'.q = D.q →
      (∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
        (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e) →
      (∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a') →
      ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
        (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧
        ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
          ∃ e, gam (f l.M a) = U.t i a + l.M • e

namespace AllClasses

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def IsIsometryTower (D D' : Datum H) (f : ℕ → D.La →ₗ[𝓞 E] D'.La) : Prop :=
  ((∀ n m : ℕ, 0 < n → 0 < m → ∀ a, ∃ e, f (n * m) a = f n a + n • e) ∧
    (∀ n : ℕ, 0 < n → (∀ a, (∃ e, f n a = n • e) ↔ ∃ e, a = n • e) ∧ ∀ a', ∃ a e, a' = f n a + n • e)) ∧
  ∀ n : ℕ, 0 < n → ∀ a a', (n : ℤ) ∣ D'.EF (f n a) (f n a') - D.EF a a'

def SameMarking (l : Level H) {D D' : Datum H} (s t : D.La → D'.La) : Prop :=
  ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), ∃ e, s a = t a + l.M • e

def Occurs {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}
    (U : FamilyUnif Xo σ ty) (D' : Datum H) (s : D.La → D'.La) : Prop :=
  ∃ (i : Fin U.n) (gam : D'.La ≃ₗ[𝓞 E] (U.Di i).La),
    (∀ a a', (U.Di i).EF (gam a) (gam a') = D'.EF a a') ∧ SameMarking l (fun a => gam (s a)) (U.t i)

theorem exists_sign (n : ℕ) : ∃ s : ℤ, 0 < n → ((ordProj[2] n : ℕ) : ℤ) ∣ s - 1 ∧ ((ordCompl[2] n : ℕ) : ℤ) ∣ s + 1 := by
  rcases n.eq_zero_or_pos with rfl | hn
  · exact ⟨0, fun h => absurd h (lt_irrefl 0)⟩
  have hc : IsCoprime ((ordProj[2] n : ℕ) : ℤ) ((ordCompl[2] n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_ordCompl Nat.prime_two hn.ne').pow_left _)
  obtain ⟨u, v, huv⟩ := hc
  exact ⟨v * (ordCompl[2] n : ℕ) - u * (ordProj[2] n : ℕ), fun _ =>
    ⟨⟨-2 * u, by linear_combination huv⟩, ⟨2 * v, by linear_combination -huv⟩⟩⟩

def sign (n : ℕ) : ℤ := (exists_sign n).choose

theorem sign_spec {n : ℕ} (hn : 0 < n) :
    ((ordProj[2] n : ℕ) : ℤ) ∣ sign n - 1 ∧ ((ordCompl[2] n : ℕ) : ℤ) ∣ sign n + 1 :=
  (exists_sign n).choose_spec hn

theorem dvd_of_parts {n : ℕ} (hn : 0 < n) {x : ℤ} (h₁ : ((ordProj[2] n : ℕ) : ℤ) ∣ x)
    (h₂ : ((ordCompl[2] n : ℕ) : ℤ) ∣ x) : (n : ℤ) ∣ x := by
  have hc : IsCoprime ((ordProj[2] n : ℕ) : ℤ) ((ordCompl[2] n : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.coprime_ordCompl Nat.prime_two hn.ne').pow_left _)
  have := hc.mul_dvd h₁ h₂
  rwa [← Nat.cast_mul, Nat.ordProj_mul_ordCompl_eq_self] at this

theorem dvd_sign_sq {n : ℕ} (hn : 0 < n) : (n : ℤ) ∣ sign n * sign n - 1 := by
  obtain ⟨h₁, h₂⟩ := sign_spec hn
  rw [show sign n * sign n - 1 = (sign n - 1) * (sign n + 1) by ring]
  exact dvd_of_parts hn (h₁.mul_right _) (h₂.mul_left _)

theorem dvd_sign_mul_sub {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : (n : ℤ) ∣ sign (n * m) - sign n := by
  obtain ⟨h₁, h₂⟩ := sign_spec hn
  obtain ⟨k₁, k₂⟩ := sign_spec (Nat.mul_pos hn hm)
  have d₁ : ((ordProj[2] n : ℕ) : ℤ) ∣ ((ordProj[2] (n * m) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.ordProj_dvd_ordProj_of_dvd (Nat.mul_pos hn hm).ne' (dvd_mul_right n m) 2)
  have d₂ : ((ordCompl[2] n : ℕ) : ℤ) ∣ ((ordCompl[2] (n * m) : ℕ) : ℤ) :=
    Int.natCast_dvd_natCast.mpr (Nat.ordCompl_dvd_ordCompl_of_dvd (dvd_mul_right n m) 2)
  refine dvd_of_parts hn ?_ ?_
  · simpa using (d₁.trans k₁).sub h₁
  · simpa using (d₂.trans k₂).sub h₂

theorem dvd_sign_add_one {n : ℕ} (hn : Odd n) : (n : ℤ) ∣ sign n + 1 := by
  have h := (sign_spec hn.pos).2
  rwa [Nat.factorization_eq_zero_of_not_dvd (Odd.not_two_dvd_nat hn), pow_zero, Nat.div_one] at h

theorem exists_eq_add_nsmul {V : Type} [AddCommGroup V] {n : ℕ} {x y : ℤ} (h : (n : ℤ) ∣ x - y) (v : V) :
    ∃ e, x • v = y • v + n • e := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c • v, by rw [← natCast_zsmul, smul_smul, ← add_smul, ← hc, add_sub_cancel]⟩

theorem IsIsometryTower.twist {D D' : Datum H} {f : ℕ → D.La →ₗ[𝓞 E] D'.La} (hf : IsIsometryTower D D' f) :
    IsIsometryTower D D' fun n => sign n • f n := by
  obtain ⟨⟨h₁, h₂⟩, h₃⟩ := hf
  refine ⟨⟨fun n m hn hm a => ?_, fun n hn => ⟨fun a => ?_, fun a' => ?_⟩⟩, fun n hn a a' => ?_⟩
  · obtain ⟨e, he⟩ := h₁ n m hn hm a
    obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_mul_sub hn hm) (f n a)
    refine ⟨e' + sign (n * m) • e, ?_⟩
    simp only [LinearMap.smul_apply]
    rw [he, smul_add, he', smul_add, smul_comm n (sign (n * m)) e, add_assoc]
  · rw [← (h₂ n hn).1 a]
    simp only [LinearMap.smul_apply]
    constructor
    · rintro ⟨e, he⟩
      obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_sq hn) (f n a)
      refine ⟨sign n • e - e', ?_⟩
      rw [smul_sub, smul_comm n (sign n) e, ← he, smul_smul, he', one_smul, add_sub_cancel_right]
    · rintro ⟨e, he⟩
      exact ⟨sign n • e, by rw [he, smul_comm]⟩
  · obtain ⟨a, e, he⟩ := (h₂ n hn).2 a'
    obtain ⟨e', he'⟩ := exists_eq_add_nsmul (dvd_sign_sq hn) (f n a)
    refine ⟨sign n • a, e - e', ?_⟩
    simp only [LinearMap.smul_apply]
    rw [map_zsmul, smul_smul, he', one_smul, he, smul_sub]
    abel
  · simp only [LinearMap.smul_apply, map_zsmul, smul_eq_mul]
    have := ((dvd_sign_sq hn).mul_right (D'.EF (f n a) (f n a'))).add (h₃ n hn a a')
    rwa [show (sign n * sign n - 1) * D'.EF (f n a) (f n a') + (D'.EF (f n a) (f n a') - D.EF a a') =
      sign n * (sign n * D'.EF (f n a) (f n a')) - D.EF a a' by ring] at this

theorem isTorsionFree (D : Datum H) : Module.IsTorsionFree (𝓞 E) D.La := by
  have := D.proj
  infer_instance

theorem exists_isTypeFn (H : Host E) (p q : ℕ) : ∃ (g : ℕ) (ty : Fin g → (E →+* ℂ)), IsTypeFn H p q ty := by
  classical
  let m : (E →+* ℂ) → ℕ := fun τ => if τ (H.rt : E) = H.rt0 then p else q
  let e := (Fintype.equivFin (Σ τ : E →+* ℂ, Fin (m τ))).symm
  have h : ∀ τ, Nat.card {i // (e i).1 = τ} = m τ := fun τ => by
    rw [Nat.card_congr ((e.subtypeEquiv (q := fun x => x.1 = τ) fun _ => Iff.rfl).trans
      (Equiv.sigmaSubtype τ))]
    simp
  exact ⟨_, fun i => (e i).1, fun τ => ⟨fun hτ => by rw [h]; simp [m, hτ], fun hτ => by rw [h]; simp [m, hτ]⟩⟩

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)}

theorem subsingleton_of_rank_zero (D : Datum H) (hD : D.p + D.q = 0) : Subsingleton D.La := by
  have := D.fin
  have := isTorsionFree D
  exact Module.finrank_zero_iff.mp (D.rank.trans hD)

theorem occurs_of_rank_zero (U : FamilyUnif Xo σ ty) (hD : D.p + D.q = 0) (D' : Datum H) (hp : D'.p = D.p)
    (hq : D'.q = D.q) (s : D.La → D'.La) : Occurs U D' s := by
  let i : Fin U.n := ⟨0, U.n_pos⟩
  have := subsingleton_of_rank_zero D' (by omega)
  have := subsingleton_of_rank_zero (U.Di i) (by have := U.sig i; omega)
  exact ⟨i, LinearEquiv.ofSubsingleton _ _, fun a a' => by
    rw [Subsingleton.elim a 0, map_zero, map_zero, map_zero, LinearMap.zero_apply, LinearMap.zero_apply],
    fun a _ => ⟨0, Subsingleton.elim _ _⟩⟩

example (H : Host E) (l : Level H) (Xo : Moduli (Test.zeroDatum H) l) (σ : KA l →+* ℂ) (ty : Fin 0 → (E →+* ℂ))
    (U : FamilyUnif Xo σ ty) : Occurs U (Test.zeroDatum H) fun a => a :=
  occurs_of_rank_zero U rfl _ rfl rfl _

theorem Occurs.twist {U : FamilyUnif Xo σ ty} {D' : Datum H} {f : ℕ → D.La →ₗ[𝓞 E] D'.La}
    (h : Occurs U D' (f l.M)) : Occurs U D' ((fun n => sign n • f n) l.M) := by
  obtain ⟨i, gam, h₁, h₂⟩ := h
  refine ⟨i, gam.trans (LinearEquiv.neg _), fun a a' => by simp [h₁], fun a ha => ?_⟩
  obtain ⟨e, he⟩ := h₂ a ha
  obtain ⟨e', he'⟩ := exists_eq_add_nsmul (x := sign l.M) (y := -1) (by simpa using dvd_sign_add_one l.odd)
    (gam (f l.M a))
  refine ⟨e - e', ?_⟩
  simp only [LinearMap.smul_apply, LinearEquiv.trans_apply, LinearEquiv.neg_apply, map_zsmul] at he ⊢
  rw [smul_neg, he', neg_one_zsmul, he, smul_sub]
  abel

end AllClasses

end GlobalTheory
