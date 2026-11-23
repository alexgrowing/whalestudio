import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.CosetTrace
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationTowerLevelAlgebraPrescribedStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDerivationOnISupOfCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DerivationOnAdjoinMemSpanImageStatement

noncomputable section

open GlobalTheory.AlmostEt GlobalTheory.K5
open scoped NNReal

namespace GlobalTheory.AlmostEt.QDer

section General

variable {A S M : Type*} [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M] [Module S M]

theorem isDerOn_mono {B B' : Subalgebra A S} {D : S → M} (h : IsDerOn B D) (hle : B' ≤ B) :
    IsDerOn B' D :=
  ⟨fun x hx y hy => h.add x (hle hx) y (hle hy), fun x hx y hy => h.mul x (hle hx) y (hle hy),
    h.alg⟩

theorem isDerOn_sub {B : Subalgebra A S} {D₁ D₂ : S → M} (h₁ : IsDerOn B D₁) (h₂ : IsDerOn B D₂) :
    IsDerOn B (fun x => D₁ x - D₂ x) where
  add x hx y hy := by simp only [h₁.add x hx y hy, h₂.add x hx y hy]; abel
  mul x hx y hy := by simp only [h₁.mul x hx y hy, h₂.mul x hx y hy, smul_sub]; abel
  alg a := by simp [h₁.alg a, h₂.alg a]

theorem isDerOn_pow {B : Subalgebra A S} {D : S → M} (h : IsDerOn B D) {x : S} (hx : x ∈ B)
    {n : ℕ} (hn : 1 ≤ n) : D (x ^ n) = ((n : S) * x ^ (n - 1)) • D x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, h.mul _ (pow_mem hx _) _ hx, ih (by omega), smul_smul, ← add_smul]
    congr 1
    push_cast
    ring

end General

variable {p : ℕ} [Fact p.Prime] {Ω : Type} [Field Ω] [Algebra (O0 p) Ω]

theorem zS_succ_pow (T : Tower p Ω) (m : ℕ) : zS T (m + 1) ^ p = zS T m :=
  Subtype.ext (by simp [zS, T.ζpow])

theorem qS_succ_pow (T : Tower p Ω) (m : ℕ) : qS T (m + 1) ^ p = qS T m :=
  Subtype.ext (by simp [qS, T.qpow])

theorem zS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : zS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert _ _)

theorem qS_mem_levelAlg (T : Tower p Ω) (m : ℕ) : qS T m ∈ levelAlg T m :=
  Algebra.subset_adjoin (Set.mem_insert_of_mem _ rfl)

theorem levelAlg_le_succ (T : Tower p Ω) (m : ℕ) : levelAlg T m ≤ levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x (rfl | rfl)
  · rw [← zS_succ_pow]; exact pow_mem (zS_mem_levelAlg T _) _
  · rw [← qS_succ_pow]; exact pow_mem (qS_mem_levelAlg T _) _

theorem towerAlg_le_iSup (T : Tower p Ω) : towerAlg T ≤ ⨆ m, levelAlg T (m + 1) := by
  refine Algebra.adjoin_le ?_
  rintro x ((⟨m, rfl⟩ | ⟨m, rfl⟩))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (zS_mem_levelAlg T m))
  · exact le_iSup (fun k => levelAlg T (k + 1)) m (levelAlg_le_succ T m (qS_mem_levelAlg T m))

theorem exists_level (hC : IsClo p Ω) (T : Tower p Ω) (n : ℕ) (hn : 1 ≤ n) :
    ∃ D : integralClosure (O0 p) Ω → Frac p Ω, IsDerOn (levelAlg T n) D ∧ D (zS T n) = 0 ∧
      D (qS T n) = Submodule.Quotient.mk (T.qq n / (p : Ω) ^ n) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  refine GlobalTheory.T.exists_derivation_towerLevelAlgebra_prescribed p Ω hC T n hn (Frac p Ω) 0 _ (smul_zero _) ?_
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
  refine ⟨algebraMap (O0 p) (integralClosure (O0 p) Ω) (qO p), ?_⟩
  have hpn : p ^ n ≠ 0 := pow_ne_zero _ (Fact.out : p.Prime).ne_zero
  rw [Algebra.linearMap_apply, ← IsScalarTower.algebraMap_apply, Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) ^ n * qS T n ^ (p ^ n - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) ^ n * T.qq n ^ (p ^ n - 1) := by
    simp [qS]
  rw [key, ← GlobalTheory.AlmostEt.qq_pow T n]
  field_simp
  rw [pow_sub_one_mul hpn]

theorem smul_mk_eq (hC : IsClo p Ω) (T : Tower p Ω) (m : ℕ) :
    ((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1)) •
        (Submodule.Quotient.mk (T.qq (m + 1) / (p : Ω) ^ (m + 1)) : Frac p Ω) =
      Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  haveI : CharZero Ω := charZero_of_injective_algebraMap hC.inj
  have hp0 : (p : Ω) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero
  have hpn : p ≠ 0 := (Fact.out : p.Prime).ne_zero
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  rw [Subalgebra.smul_def, smul_eq_mul]
  have key : (((p : integralClosure (O0 p) Ω) * qS T (m + 1) ^ (p - 1) :
      integralClosure (O0 p) Ω) : Ω) = (p : Ω) * T.qq (m + 1) ^ (p - 1) := by
    simp [qS]
  rw [key, ← T.qpow m, ← pow_sub_one_mul hpn (T.qq (m + 1)), pow_succ]
  field_simp

theorem exists_qDer (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra (O0 p) Ω]
    (hC : IsClo p Ω) (T : Tower p Ω) :
    ∃ D : (integralClosure (O0 p) Ω) → Frac p Ω, IsDerOn (towerAlg T) D ∧
      ∀ m : ℕ, D (zS T m) = 0 ∧ D (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := by
  have hp1 : 1 ≤ p := (Fact.out : p.Prime).one_lt.le
  choose Dl hDl hz hq using fun m : ℕ => exists_level hC T (m + 1) (by omega)

  have hz' : ∀ m, Dl m (zS T m) = 0 := fun m => by
    rw [← zS_succ_pow, isDerOn_pow (hDl m) (zS_mem_levelAlg T _) hp1, hz, smul_zero]
  have hq' : ∀ m, Dl m (qS T m) = Submodule.Quotient.mk (T.qq m / (p : Ω) ^ m) := fun m => by
    rw [← qS_succ_pow, isDerOn_pow (hDl m) (qS_mem_levelAlg T _) hp1, hq, smul_mk_eq hC T m]

  have hcomp : ∀ m, ∀ x ∈ levelAlg T (m + 1), Dl (m + 1) x = Dl m x := by
    intro m x hx
    have hE := isDerOn_sub (isDerOn_mono (hDl (m + 1)) (levelAlg_le_succ T (m + 1))) (hDl m)
    have hspan := GlobalTheory.T.derivationOn_adjoin_mem_span_image (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω) {zS T (m + 1), qS T (m + 1)}
      _ hE x hx
    have h1 : Dl (m + 1) (zS T (m + 1)) - Dl m (zS T (m + 1)) = 0 := by rw [hz' (m + 1), hz m, sub_zero]
    have h2 : Dl (m + 1) (qS T (m + 1)) - Dl m (qS T (m + 1)) = 0 := by rw [hq' (m + 1), hq m, sub_self]
    simp only [Set.image_insert_eq, Set.image_singleton, h1, h2, Set.insert_eq_of_mem,
      Set.mem_singleton_iff, Submodule.span_singleton_eq_bot.2 rfl, Submodule.mem_bot] at hspan
    exact sub_eq_zero.1 hspan
  have hmono : Monotone (fun m => levelAlg T (m + 1)) :=
    monotone_nat_of_le_succ fun m => levelAlg_le_succ T (m + 1)
  obtain ⟨D, hD, hag⟩ := GlobalTheory.T.exists_derivationOn_iSup_of_compatible (O0 p) (integralClosure (O0 p) Ω) (Frac p Ω)
    (fun m => levelAlg T (m + 1)) hmono Dl hDl hcomp
  refine ⟨D, isDerOn_mono hD (towerAlg_le_iSup T), fun m => ⟨?_, ?_⟩⟩
  · rw [hag m _ (levelAlg_le_succ T m (zS_mem_levelAlg T m)), hz']
  · rw [hag m _ (levelAlg_le_succ T m (qS_mem_levelAlg T m)), hq']

end GlobalTheory.AlmostEt.QDer
