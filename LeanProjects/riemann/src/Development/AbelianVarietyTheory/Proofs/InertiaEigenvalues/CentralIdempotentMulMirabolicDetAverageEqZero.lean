import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesKillsAvg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentOfIrrCharacterOrthogonalCentral
open GlobalTheory.GLq GlobalTheory.MirAvg Polynomial

noncomputable section

namespace GlobalTheory.MirAvg.Kill

theorem idem_eq_zero {G : Type} [Group G] [Fintype G] (E : MonoidAlgebra ℂ G) (h : E * E = E)
    (h1 : E.coeff 1 = 0) : E = 0 := by
  classical
  haveI : Module.Finite ℂ (MonoidAlgebra ℂ G) := Module.Finite.of_basis (MonoidAlgebra.basis G ℂ)
  haveI : Module.Free ℂ (MonoidAlgebra ℂ G) := Module.Free.of_basis (MonoidAlgebra.basis G ℂ)
  have hi : IsIdempotentElem (LinearMap.mulLeft ℂ E) := by
    refine LinearMap.ext fun x => ?_
    simp [← mul_assoc, h]
  have ht : LinearMap.trace ℂ _ (LinearMap.mulLeft ℂ E) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (MonoidAlgebra.basis G ℂ), Matrix.trace]
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [Matrix.diag_apply, LinearMap.toMatrix_apply]
    have : (MonoidAlgebra.basis G ℂ) x = MonoidAlgebra.single x 1 := by simp
    rw [this]
    show (E * MonoidAlgebra.single x 1).coeff x = 0
    rw [MonoidAlgebra.coeff_mul_single_apply]
    simp [h1]
  have h0 := LinearMap.IsIdempotentElem.eq_zero_of_trace_eq_zero hi ht
  simpa using LinearMap.congr_fun h0 1

variable {G : Type} [Group G] [Fintype G]

theorem coeff_sum_single (F : G → ℂ) (x : G) :
    (∑ h : G, MonoidAlgebra.single h (F h)).coeff x = F x := by
  classical
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul' (a b : MonoidAlgebra ℂ G) (x : G) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

def avg (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) : MonoidAlgebra ℂ G :=
  ∑ h : G, MonoidAlgebra.single h (if P h then χ h else 0)

theorem avg_coeff (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (x : G) :
    (avg P χ).coeff x = if P x then χ x else 0 :=
  coeff_sum_single _ x

theorem avg_mul_self (P : G → Prop) [DecidablePred P] (χ : G →* ℂ)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) :
    avg P χ * avg P χ = ((Finset.univ.filter P).card : ℂ) • avg P χ := by
  ext x
  rw [coeff_mul', MonoidAlgebra.coeff_smul_apply, avg_coeff, smul_eq_mul]
  have key : ∀ q, (avg P χ).coeff q * (avg P χ).coeff (q⁻¹ * x) = if P q then (if P x then χ x else 0) else 0 := by
    intro q
    simp only [avg_coeff]
    by_cases hq : P q
    · have hiff : P (q⁻¹ * x) ↔ P x := ⟨fun h => by simpa using hm _ _ hq h, fun h => hm _ _ (hi _ hq) h⟩
      by_cases hx : P x
      · rw [if_pos hq, if_pos (hiff.2 hx), if_pos hq, if_pos hx, ← map_mul, mul_inv_cancel_left]
      · rw [if_pos hq, if_neg (fun h => hx (hiff.1 h)), if_pos hq, if_neg hx, mul_zero]
    · rw [if_neg hq, if_neg hq, zero_mul]
  simp only [key]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]

theorem coeff_one_zOf_mul (ψ : G → ℂ) (a : MonoidAlgebra ℂ G) :
    (zOf ψ * a).coeff 1 = ψ 1 / (Fintype.card G : ℂ) * tr a ψ := by
  rw [coeff_mul', tr, Finset.mul_sum]
  refine Fintype.sum_equiv (Equiv.inv G) _ _ fun q => ?_
  rw [zOf, coeff_sum_single]
  simp only [Equiv.inv_apply, inv_inv, mul_one]
  ring

theorem zOf_mul_avg_eq_zero (ψ : G → ℂ) (hψ : IsIrr ψ) (P : G → Prop) [DecidablePred P] (χ : G →* ℂ) (h1 : P 1)
    (hm : ∀ x y, P x → P y → P (x * y)) (hi : ∀ x, P x → P x⁻¹) (htr : tr (avg P χ) ψ = 0) :
    zOf ψ * avg P χ = 0 := by
  obtain ⟨hid, hcen, -⟩ := GlobalTheory.GLq.ZOrth.zorth G ψ ψ hψ hψ
  rw [if_pos rfl] at hid
  set m := avg P χ with hmdef
  set n : ℂ := ((Finset.univ.filter P).card : ℂ) with hn
  have hn0 : n ≠ 0 := by
    rw [hn, Nat.cast_ne_zero]
    exact Finset.card_ne_zero.2 ⟨1, by simp [h1]⟩
  have hmm : m * m = n • m := avg_mul_self P χ hm hi
  have hE : (n⁻¹ • (zOf ψ * m)) * (n⁻¹ • (zOf ψ * m)) = n⁻¹ • (zOf ψ * m) := by
    rw [smul_mul_smul_comm]
    have : zOf ψ * m * (zOf ψ * m) = n • (zOf ψ * m) := by
      calc zOf ψ * m * (zOf ψ * m) = zOf ψ * (m * zOf ψ) * m := by simp only [mul_assoc]
        _ = zOf ψ * (zOf ψ * m) * m := by rw [← hcen m]
        _ = (zOf ψ * zOf ψ) * (m * m) := by simp only [mul_assoc]
        _ = n • (zOf ψ * m) := by rw [hid, hmm, mul_smul_comm]
    rw [this, smul_smul, mul_assoc, inv_mul_cancel₀ hn0, mul_one]
  have h1' : (n⁻¹ • (zOf ψ * m)).coeff 1 = 0 := by
    rw [MonoidAlgebra.coeff_smul_apply, coeff_one_zOf_mul, htr]
    simp
  have h0 := idem_eq_zero _ hE h1'
  rwa [smul_eq_zero, or_iff_right (inv_ne_zero hn0)] at h0

end GlobalTheory.MirAvg.Kill

namespace GlobalTheory.MirAvg

theorem mirSet_one {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) : mirSet a b (1 : Gn g r) := by
  cases b
  · intro x _; simp
  · intro x; exact ⟨0, by simp⟩

theorem mirSet_mul {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h h' : Gn g r)
    (hh : mirSet a b h) (hh' : mirSet a b h') : mirSet a b (h * h') := by
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh hh'
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh' x hx, hh x hx]
  · intro x
    simp only [mirSet, if_true] at hh hh'
    obtain ⟨c₂, hc₂⟩ := hh' x
    obtain ⟨c₁, hc₁⟩ := hh ((h' : Mt g r).mulVec x)
    refine ⟨c₁ + c₂, ?_⟩
    rw [Units.val_mul, ← Matrix.mulVec_mulVec, add_smul, ← hc₁, ← hc₂]
    abel

theorem mirSet_inv {g : ℕ} [Fact g.Prime] {r : ℕ} (a : Fin r → ZMod g) (b : Bool) (h : Gn g r)
    (hh : mirSet a b h) : mirSet a b h⁻¹ := by
  have hhi : ∀ x, (h : Mt g r).mulVec (((h⁻¹ : Gn g r) : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hih : ∀ x, ((h⁻¹ : Gn g r) : Mt g r).mulVec ((h : Mt g r).mulVec x) = x := by
    intro x
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
  cases b
  · intro x hx
    simp only [mirSet, Bool.false_eq_true, if_false] at hh
    conv_lhs => rw [← hh x hx]
    exact hih x
  · intro x
    simp only [mirSet, if_true] at hh
    obtain ⟨c, hc⟩ := hh (((h⁻¹ : Gn g r) : Mt g r).mulVec x)
    refine ⟨-c, ?_⟩
    rw [hhi x] at hc
    rw [neg_smul, ← hc]
    abel

open Classical in

theorem zOf_mul_mirEl_eq_zero : ∀ (g : ℕ) [Fact g.Prime] (r : ℕ) (ψ : Gn g r → ℂ), IsIrr ψ →
    ∀ (θ : (ZMod g)ˣ →* ℂˣ) (a : Fin r → ZMod g)
    (b : Bool), tr (mirEl θ a b) ψ = 0 → zOf ψ * mirEl θ a b = 0 := by
  intro g _ r ψ hψ θ a b htr
  let χ : Gn g r →* ℂ := (Units.coeHom ℂ).comp (θ.comp Matrix.GeneralLinearGroup.det)
  have hm : mirEl θ a b = Kill.avg (mirSet a b) χ := rfl
  rw [hm] at htr ⊢
  exact Kill.zOf_mul_avg_eq_zero ψ hψ (mirSet a b) χ (mirSet_one a b) (mirSet_mul a b) (mirSet_inv a b) htr

end GlobalTheory.MirAvg
