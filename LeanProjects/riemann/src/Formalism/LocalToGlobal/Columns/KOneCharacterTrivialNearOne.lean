import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.TwChrOne
import Formalism.LocalToGlobal.Columns.ThetaOpenTwLevQ
import Formalism.LocalToGlobal.Columns.ChainTwFin
import Formalism.LocalToGlobal.Columns.UnfoldingNonvanishingDoubleCosetHolds
import Formalism.LocalToGlobal.Columns.RecLevelSymExt
import Formalism.LocalToGlobal.Columns.StabMapRLInjective
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section IntegralTwistedLevel

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] (P : HeightOneSpectrum (𝓞 E))

def kOneLastExponents (n c : ℕ) (l : ℕ) : ℤ := if l + 1 = n then (c : ℤ) else 0

def twistedLevelExponent (n c : ℕ) (l : ℕ) : ℤ := if l + 1 = n then 0 else (c : ℤ)

theorem scaledConstLattice_stable {n c : ℕ} {g : Sp E n ≃ₗ[E] Sp E n} (hg : g ∈ GLint E n P) {x : Sp E n}
    (hx : x ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ))) :
    g x ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ)) := by
  rw [ciMem_sclLat] at hx ⊢
  have hy : ((qOf P : E) ^ (c : ℤ))⁻¹ • x ∈ stdAt E n P := by
    rw [ciMem_stdAt]; intro l; simpa [Pi.smul_apply, smul_eq_mul] using hx l
  have h1 := (hg _).2 hy
  rw [map_smul, ciMem_stdAt] at h1
  intro l
  simpa [Pi.smul_apply, smul_eq_mul] using h1 l

def twK1H (n r c : ℕ) : Subgroup ↥(GLint E n P) where
  carrier := {g | (g : Sp E n ≃ₗ[E] Sp E n) ∈ LocE.JQ P (qOf P) r n 0 ∧
    (g : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (LocE.sclLat P (qOf P) n (kOneLastExponents n c)) ∧
    (g : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (LocE.sclLat P (qOf P) n (twistedLevelExponent n c)) ∧
    ∀ w ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c), (g : Sp E n ≃ₗ[E] Sp E n) w - w ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ))}
  one_mem' := ⟨Subgroup.one_mem _, Subgroup.one_mem _, Subgroup.one_mem _, fun w _ => by
    show (1 : Sp E n ≃ₗ[E] Sp E n) w - w ∈ _
    rw [show (1 : Sp E n ≃ₗ[E] Sp E n) w = w from rfl, sub_self]; exact zero_mem _⟩
  mul_mem' := by
    rintro a b ⟨ha1, ha2, ha3, ha4⟩ ⟨hb1, hb2, hb3, hb4⟩
    refine ⟨Subgroup.mul_mem _ ha1 hb1, Subgroup.mul_mem _ ha2 hb2, Subgroup.mul_mem _ ha3 hb3, fun w hw => ?_⟩
    show (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w) - w ∈ _
    have e : (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w) - w =
        (a : Sp E n ≃ₗ[E] Sp E n) ((b : Sp E n ≃ₗ[E] Sp E n) w - w) + ((a : Sp E n ≃ₗ[E] Sp E n) w - w) := by
      rw [map_sub]; abel
    rw [e]
    exact add_mem (scaledConstLattice_stable P a.2 (hb4 w hw)) (ha4 w hw)
  inv_mem' := by
    rintro a ⟨ha1, ha2, ha3, ha4⟩
    refine ⟨Subgroup.inv_mem _ ha1, Subgroup.inv_mem _ ha2, Subgroup.inv_mem _ ha3, fun w hw => ?_⟩
    have e : ((a⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) w - w =
        -(((a⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) ((a : Sp E n ≃ₗ[E] Sp E n) w - w)) := by
      rw [map_sub]
      show _ = -((a : Sp E n ≃ₗ[E] Sp E n).symm _ - (a : Sp E n ≃ₗ[E] Sp E n).symm w)
      rw [LinearEquiv.symm_apply_apply]
      show (a : Sp E n ≃ₗ[E] Sp E n).symm w - w = _
      abel
    rw [e]
    exact neg_mem (scaledConstLattice_stable P (a⁻¹).2 (ha4 w hw))

theorem mem_R1_zero {n : ℕ} (g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) : g ∈ Loc.R1 E n 0 := by
  have hc : ∀ r : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0), Loc.R1cond E n 0 r := fun r => by
    have hU : ∀ i (v : Sp E (n + 0)), v ∈ Loc.Ufl E n 0 i := fun i v l hl => absurd (show l.1 < n + i by have := l.2; omega) hl
    have he : Loc.eN E (n + 0) n = 0 := by
      funext l; unfold Loc.eN; rw [if_neg (by have := l.2; omega)]; rfl
    exact ⟨fun i v _ => hU i _, by rw [he, map_zero], fun i => hU i _⟩
  exact ⟨hc g, hc g⁻¹⟩

def kOneCharacter (n r c : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : ↥(twK1H P n r c) →* K where
  toFun g := LocE.lamQB ξ r n ((g : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n).toLinearMap
  map_one' := by
    obtain ⟨h1, h2⟩ := _root_.TwChrOne E K P (fun _ => 1) ξ r n 0 (fun _ _ => rfl)
    have hm : (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)) ∈ Loc.Cbe (LocE.JQ P (qOf P) r n 0) 1 := Subgroup.one_mem _
    have a := h2 1 hm 1 hm 1 hm (fun _ => rfl)
    have b := h1 1 hm
    have e : PI.TwChrOne.ChiL P (fun _ => (1 : K)) ξ r n 0 1 1 = LocE.lamQB ξ r n (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap := by
      unfold PI.TwChrOne.ChiL; simp only [inv_one, one_mul, mul_one]; rfl
    rw [e] at a b
    show LocE.lamQB ξ r n (1 : Sp E n ≃ₗ[E] Sp E n).toLinearMap = 1
    exact (mul_left_cancel₀ b ((mul_one _).trans a)).symm
  map_mul' g g' := by
    obtain ⟨-, h2⟩ := _root_.TwChrOne E K P (fun _ => 1) ξ r n 0 (fun _ _ => rfl)
    have hC : ∀ x : ↥(twK1H P n r c), ((x : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) ∈ Loc.Cbe (LocE.JQ P (qOf P) r n 0) 1 :=
      fun x => ⟨mem_R1_zero _, by
        show (MulAut.conj (1 : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0))⁻¹) _ ∈ _
        rw [inv_one, map_one]; exact x.2.1⟩
    have a := h2 _ (hC g) _ (hC g') _ (hC (g * g')) (fun _ => rfl)
    have e : ∀ y : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0), PI.TwChrOne.ChiL P (fun _ => (1 : K)) ξ r n 0 1 y = LocE.lamQB ξ r n y.toLinearMap :=
      fun y => by unfold PI.TwChrOne.ChiL; simp only [inv_one, one_mul, mul_one]; rfl
    rw [e, e, e] at a
    exact a

def kOneLevel (n r c : ℕ) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LevI E K n P :=
  ⟨twK1H P n r c, (kOneCharacter P n r c ξ).toHomUnits⟩

theorem twClose_c {m c : ℕ} (e : ℕ → ℤ) (he : ∀ l, 0 ≤ e l ∧ e l ≤ c) (hq0 : (qOf P : E) ≠ 0) (W : Sp E m ≃ₗ[E] Sp E m)
    (hW : ∀ i j, P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i j) ≤ P.valuation E (qOf P : E) ^ c)
    {x : Sp E m} (hx : x ∈ LocE.sclLat P (qOf P) m e) : W x ∈ LocE.sclLat P (qOf P) m e := by
  rw [ciMem_sclLat] at hx ⊢
  have hvq0 : P.valuation E (qOf P : E) ≠ 0 := (map_ne_zero _).2 hq0
  have hvq1 : P.valuation E (qOf P : E) ≤ 1 := qth_vq_le P (qOf P)
  have hpow : ∀ k : ℤ, 0 ≤ k → P.valuation E (qOf P : E) ^ k ≤ 1 := fun k hk => by
    rw [show k = ((k.toNat : ℕ) : ℤ) by omega, zpow_natCast]
    exact pow_le_one' hvq1 _
  have hxl : ∀ l : Fin m, P.valuation E (x l) ≤ P.valuation E (qOf P : E) ^ e l.1 := fun l => by
    have h1 := (qth_intAt_iff P _).1 (hx l)
    rw [map_mul, map_inv₀, map_zpow₀] at h1
    have h2 : P.valuation E (qOf P : E) ^ e l.1 ≠ 0 := zpow_ne_zero _ hvq0
    calc P.valuation E (x l) = P.valuation E (qOf P : E) ^ e l.1 * ((P.valuation E (qOf P : E) ^ e l.1)⁻¹ * P.valuation E (x l)) := by
          rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
      _ ≤ P.valuation E (qOf P : E) ^ e l.1 * 1 := mul_le_mul' le_rfl h1
      _ = _ := mul_one _
  have hxl1 : ∀ l : Fin m, P.valuation E (x l) ≤ 1 := fun l => le_trans (hxl l) (hpow _ (he l.1).1)
  intro i
  rw [qth_mulVec, Pi.add_apply, mul_add]
  refine IntAt.add (hx i) ((qth_intAt_iff P _).2 ?_)
  rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Valuation.map_sum_le _ fun l _ => ?_
  rw [map_mul, map_mul, map_inv₀, map_zpow₀]
  have h3 : P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i l) * P.valuation E (x l) ≤
      P.valuation E (qOf P : E) ^ c := by
    calc _ ≤ P.valuation E (qOf P : E) ^ c * 1 := mul_le_mul' (hW i l) (hxl1 l)
      _ = _ := mul_one _
  calc (P.valuation E (qOf P : E) ^ e i.1)⁻¹ * (P.valuation E ((((toGLm E m W : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1) i l) *
        P.valuation E (x l)) ≤ (P.valuation E (qOf P : E) ^ e i.1)⁻¹ * P.valuation E (qOf P : E) ^ c := mul_le_mul' le_rfl h3
    _ = P.valuation E (qOf P : E) ^ ((c : ℤ) - e i.1) := by
      rw [zpow_sub₀ hvq0, zpow_natCast, div_eq_mul_inv, mul_comm]
    _ ≤ 1 := hpow _ (by have := (he i.1).2; omega)

theorem twLamQB_one (hq : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : ((qOf P : ℕ) : E) ≠ 0) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ)
    {kj n' N : ℕ} (hn : n' ≤ N) (y : Sp E N ≃ₗ[E] Sp E N) (hy : QClose P (qOf P) y) :
    LocE.lamQB ξ kj n' (y : Sp E N →ₗ[E] Sp E N) = 1 := by
  classical
  unfold LocE.lamQB
  set D : Matrix (Fin (n' - kj)) (Fin (n' - kj)) E := Matrix.of fun s t : Fin (n' - kj) =>
    Loc.atN ((y : Sp E N →ₗ[E] Sp E N) (Loc.eN E N (kj + t.1))) (kj + s.1) with hD
  have hent : ∀ s t : Fin (n' - kj), IntAt P (D s t) ∧ redP P (D s t) = (1 : Matrix _ _ (𝓞 E ⧸ P.asIdeal)) s t := by
    intro s t
    have hs : kj + s.1 < N := by have := s.2; omega
    have ht : kj + t.1 < N := by have := t.2; omega
    have e1 : Loc.eN E N (kj + t.1) = Pi.single ⟨kj + t.1, ht⟩ 1 := by
      funext l
      unfold Loc.eN
      rw [Pi.single_apply]
      congr 1
      apply propext
      constructor
      · intro h; exact Fin.ext h
      · intro h; rw [h]
    have e2 : D s t = ((toGLm E N y : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩ := by
      rw [qsp_toGLm_apply, hD, Matrix.of_apply, e1]
      unfold Loc.atN
      rw [dif_pos hs]
      rfl
    obtain ⟨h1, h2⟩ := qth_red_entry P (qOf P) hq0 hq hy ⟨kj + s.1, hs⟩ ⟨kj + t.1, ht⟩
    rw [e2]
    refine ⟨h1, ?_⟩
    rw [h2, Matrix.one_apply, Matrix.one_apply]
    by_cases hst : s = t
    · rw [if_pos (Fin.ext (by simp [hst])), if_pos hst, redP_one]
    · rw [if_neg (fun h => hst (Fin.ext (by have := congrArg Fin.val h; simp at this; omega))), if_neg hst, redP_zero]
  have hdet : redP P D.det = 1 := by
    rw [redP_det D fun s t => (hent s t).1]
    have : D.map (redP P) = 1 := Matrix.ext fun s t => (hent s t).2
    rw [this, Matrix.det_one]
  unfold LocE.unitV
  have hu : IsUnit (redP P D.det) := by rw [hdet]; exact isUnit_one
  rw [dif_pos hu]
  have : hu.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, hdet]; rfl)
  rw [this, map_one, Units.val_one, inv_one]

theorem kOneCharacter_trivial_near_one (n r c : ℕ) (hc : 0 < c) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) :
    ∃ N : ℕ, 0 < N ∧ ∀ g : ↥(GLint E n P), lqPrinc P N (g : Sp E n ≃ₗ[E] Sp E n) →
      ∃ h : g ∈ (kOneLevel P n r c ξ).H, (kOneLevel P n r c ξ).lam ⟨g, h⟩ = 1 := by
  have hq0 : ((qOf P : ℕ) : E) ≠ 0 := by exact_mod_cast (Formalism.L2.Ker.qOf_pos P).ne'
  have hq : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal := ciQ_mem P
  have hv0 : P.valuation E ((qOf P : ℕ) : E) ≠ 0 := (map_ne_zero _).2 hq0
  have hvq1 : P.valuation E (qOf P : E) ≤ 1 := qth_vq_le P (qOf P)
  obtain ⟨e, he⟩ : ∃ e : ℕ, WithZero.exp (-(e : ℤ)) ≤ P.valuation E ((qOf P : ℕ) : E) := by
    refine ⟨(-(WithZero.log (P.valuation E ((qOf P : ℕ) : E)))).toNat, ?_⟩
    conv_rhs => rw [← WithZero.exp_log hv0]
    rw [WithZero.exp_le_exp]
    have := Int.self_le_toNat (-(WithZero.log (P.valuation E ((qOf P : ℕ) : E))))
    omega
  refine ⟨(e + 1) * c, Nat.mul_pos (Nat.succ_pos _) hc, fun g hg => ?_⟩

  have hexp : WithZero.exp (-(((e + 1) * c : ℕ) : ℤ)) ≤ P.valuation E (qOf P : E) ^ c := by
    calc WithZero.exp (-(((e + 1) * c : ℕ) : ℤ)) ≤ WithZero.exp (-(e : ℤ)) ^ c := by
          rw [← WithZero.exp_nsmul, WithZero.exp_le_exp, nsmul_eq_mul]; push_cast; nlinarith
      _ ≤ _ := pow_le_pow_left' he c
  have hqc : P.valuation E (qOf P : E) ^ c ≤ P.valuation E (qOf P : E) := by
    obtain ⟨d, rfl⟩ : ∃ d, c = d + 1 := ⟨c - 1, by omega⟩
    rw [pow_succ]
    exact mul_le_of_le_one_left' (pow_le_one' hvq1 d)
  have hWc : ∀ (y : ↥(GLint E n P)), lqPrinc P ((e + 1) * c) (y : Sp E n ≃ₗ[E] Sp E n) →
      ∀ i j, P.valuation E ((((toGLm E n (y : Sp E n ≃ₗ[E] Sp E n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) i j) ≤
        P.valuation E (qOf P : E) ^ c := fun y hy i j => le_trans (hy i j) hexp
  have hg' := qth_princ_inv P g hg
  have c1 := hWc g hg
  have c2 := hWc g⁻¹ hg'
  have q1 : QClose P (qOf P) (g : Sp E n ≃ₗ[E] Sp E n) := fun i j => le_trans (c1 i j) hqc
  have q2 : QClose P (qOf P) ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) := fun i j => le_trans (c2 i j) hqc
  have hstab : ∀ (f : ℕ → ℤ), (∀ l, 0 ≤ f l ∧ f l ≤ c) → (g : Sp E n ≃ₗ[E] Sp E n) ∈ stabL E n (LocE.sclLat P (qOf P) n f) :=
    fun f hf x => ⟨fun hx => by
      have := twClose_c P f hf hq0 _ c2 hx
      rwa [show ((g⁻¹ : ↥(GLint E n P)) : Sp E n ≃ₗ[E] Sp E n) ((g : Sp E n ≃ₗ[E] Sp E n) x) = x from
        (g : Sp E n ≃ₗ[E] Sp E n).symm_apply_apply x] at this,
      fun hx => twClose_c P f hf hq0 _ c1 hx⟩
  have hbound : ∀ l, 0 ≤ kOneLastExponents n c l ∧ kOneLastExponents n c l ≤ c := fun l => by unfold kOneLastExponents; split_ifs <;> omega
  have hboundX : ∀ l, 0 ≤ twistedLevelExponent n c l ∧ twistedLevelExponent n c l ≤ c := fun l => by unfold twistedLevelExponent; split_ifs <;> omega
  have hS : ∀ w ∈ LocE.sclLat P (qOf P) n (twistedLevelExponent n c),
      (g : Sp E n ≃ₗ[E] Sp E n) w - w ∈ LocE.sclLat P (qOf P) n (fun _ => (c : ℤ)) := by
    intro w hw
    rw [ciMem_sclLat] at hw ⊢
    have hwl : ∀ l : Fin n, P.valuation E (w l) ≤ 1 := fun l => by
      have h1 := (qth_intAt_iff P _).1 (hw l)
      rw [map_mul, map_inv₀, map_zpow₀] at h1
      have hpow : P.valuation E (qOf P : E) ^ twistedLevelExponent n c l.1 ≤ 1 := by
        rw [show twistedLevelExponent n c l.1 = (((twistedLevelExponent n c l.1).toNat : ℕ) : ℤ) by have := (hboundX l.1).1; omega, zpow_natCast]
        exact pow_le_one' hvq1 _
      have h2 : P.valuation E (qOf P : E) ^ twistedLevelExponent n c l.1 ≠ 0 := zpow_ne_zero _ hv0
      calc P.valuation E (w l) = P.valuation E (qOf P : E) ^ twistedLevelExponent n c l.1 *
            ((P.valuation E (qOf P : E) ^ twistedLevelExponent n c l.1)⁻¹ * P.valuation E (w l)) := by
            rw [← mul_assoc, mul_inv_cancel₀ h2, one_mul]
        _ ≤ 1 * 1 := mul_le_mul' hpow h1
        _ = 1 := one_mul 1
    intro i
    rw [qth_mulVec, Pi.sub_apply, Pi.add_apply, add_sub_cancel_left]
    rw [qth_intAt_iff, map_mul, map_inv₀, map_zpow₀, Matrix.mulVec, dotProduct]
    have hsum : P.valuation E (∑ l, (((toGLm E n (g : Sp E n ≃ₗ[E] Sp E n) : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) - 1) i l * w l) ≤
        P.valuation E (qOf P : E) ^ c := by
      refine Valuation.map_sum_le _ fun l _ => ?_
      rw [map_mul]
      calc _ ≤ P.valuation E (qOf P : E) ^ c * 1 := mul_le_mul' (c1 i l) (hwl l)
        _ = _ := mul_one _
    calc (P.valuation E (qOf P : E) ^ ((c : ℕ) : ℤ))⁻¹ * _ ≤ (P.valuation E (qOf P : E) ^ ((c : ℕ) : ℤ))⁻¹ * P.valuation E (qOf P : E) ^ c :=
          mul_le_mul' le_rfl hsum
      _ = 1 := by rw [zpow_natCast, inv_mul_cancel₀ (pow_ne_zero _ hv0)]
  have hmem : g ∈ (kOneLevel P n r c ξ).H :=
    ⟨qth_mem_JQ P (qOf P) hq0 (n := n) (c := 0) r (g : Sp E n ≃ₗ[E] Sp E n) q1 q2, hstab _ hbound, hstab _ hboundX, hS⟩
  refine ⟨hmem, Units.ext ?_⟩
  show LocE.lamQB ξ r n ((g : Sp E n ≃ₗ[E] Sp E n) : Sp E n →ₗ[E] Sp E n) = 1
  exact twLamQB_one P hq hq0 ξ (le_refl n) _ q1

end IntegralTwistedLevel

section TwTop

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)

def twTopDepth (R : Ranks) : ℕ := 4 * R.m + 1

def twLt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs := colLevSym Ch

def twTt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)) := fun j P =>
  kOneLevel P.1 (R.N j) R.r (twTopDepth R) (resChar (mu : Chr X.F X.E X.K) P.1)

theorem twTt_open (j : ℕ) : ThetaOpen (twTt (R := R) sel mu j) := fun P =>
  kOneCharacter_trivial_near_one P.1 (R.N j) R.r (twTopDepth R) (by unfold twTopDepth; omega) _

theorem twTop_chF_ok (W : Wts X Pr.Word R) (hX : X.Ok) {cst : LocCst X (rowSG Pr sel mu)} (hc : cst.Ok)
    (hQg : ∀ P ∈ QE sel (mu : Chr X.F X.E X.K), P ∉ Pr.vGs) (m2 : ℕ) (u : Pr.Word) (j : ℕ) :
    (chF W sel mu (twIdxTop Ch sel mu cst m2 (twLt Ch) (twTt sel mu)) u j).Ok :=
  chF_ok_twIdxTop W Ch sel mu cst m2 (twLt Ch) (twTt sel mu) hX hc hQg (fun j' _ => twTt_open (R := R) sel mu j') u j

open Classical in

theorem twLevExtL (hSG : Pr.vGs ⊆ rowSG Pr sel mu) :
    LevExtL (twLt Ch R.m) hSG (rowTy Ch sel mu (rPsymF Ch)).inv := by
  intro h w _
  have hg0 := h.2 ⟨w.1, hSG w.2⟩ (Set.mem_univ _)
  have e : (rowTy Ch sel mu (rPsymF Ch)) ⟨w.1, hSG w.2⟩ = (rowTyG Ch (rPsymF Ch)) w := by
    unfold rowTy
    rw [LevFam.glue_of_mem _ _ _ w.2]
  have hg : h.1 ⟨w.1, hSG w.2⟩ ∈ ((rowTyG Ch (rPsymF Ch)) w).inv.H := by
    change h.1 ⟨w.1, hSG w.2⟩ ∈ ((rowTy Ch sel mu (rPsymF Ch)) ⟨w.1, hSG w.2⟩).inv.inv.H at hg0
    rw [e] at hg0
    exact hg0
  have key := symX_ext_mem (N_m_succ R) R.k R.r R.t R.m R.rS (rank_X'_eq R) (r_le_X' R) (r_le_N_of_le (by omega)) h.1
    ⟨w.1, hSG w.2⟩ hg
  rw [← colLevSym_top_H Ch le_rfl w] at key
  exact key

end TwTop

end Formalism.L2.Col
