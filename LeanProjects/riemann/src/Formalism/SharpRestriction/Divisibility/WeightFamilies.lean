import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.LocalRingCardinality.DataDIV
import Formalism.LocalRingCardinality.DataParamsT
import Formalism.LocalRingCardinality.ConjSqrtMinusD
import Formalism.SharpRestriction.ParamsHeightRankConstant
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.GelfandTransference.EnergyIdentity

noncomputable section

namespace Formalism.MainNotions.WeightFamilies

open Formalism.BasicNotions NumberField IsDedekindDomain
open scoped ComplexOrder

def rho (D : D7) (j : ℕ) : ℕ := (D.R.sigW j).2

def dP (D : D7) (j : ℕ) : ℕ := 2 * D.R.f * rho D j

def RRv (D : D7) (CR : ℝ) : ℝ := D.host.rdE ^ CR

def PPv (D : D7) (L : SizeData₂ D) (C A : ℝ) : ℝ := C * zBase L ^ A

theorem PPv_rec {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L} (T : ParamsT D L P) : PPv D L T.CP T.eP = T.PP := by
  unfold PPv
  exact T.PP_eq.symm

def PP0v (D : D7) (L : SizeData₂ D) (C A : ℝ) : ℝ :=
  C * ((D.R.f : ℝ) * (D.R.r : ℝ) + L.sc.L + logdE D + |L.logOm|) ^ A

structure Wt (D : D7) (j : ℕ) where
  aP : D.what₂.Tau → Fin (D.R.sigW j).1 → ℕ
  aM : D.what₂.Tau → Fin (D.R.sigW j).2 → ℕ
  aPlus_antitone : ∀ τ, Antitone (aP τ)
  aM_anti : ∀ τ, Antitone (aM τ)
  n : ℕ
  n_even : Even n

def Wt.size {D : D7} {j : ℕ} (ka : Wt D j) : ℝ :=
  (∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ))) +
    (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) + 1

theorem Wt.one_le_size {D : D7} {j : ℕ} (ka : Wt D j) : 1 ≤ ka.size := by
  unfold Wt.size
  have h1 : 0 ≤ ∑ τ, ((∑ i, (ka.aP τ i : ℝ)) + ∑ i, (ka.aM τ i : ℝ)) :=
    Finset.sum_nonneg fun τ _ => add_nonneg (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
      (Finset.sum_nonneg fun i _ => Nat.cast_nonneg _)
  have h2 : 0 ≤ (D.R.f : ℝ) * ((max (D.R.sigW j).2 1 : ℕ) : ℝ) * (D.R.r : ℝ) * (ka.n : ℝ) := by
    positivity
  linarith

def dimY (D : D7) (j : ℕ) : ℕ :=
  D.R.f * ((D.R.sigW j).1 * (D.R.sigW j).2 + (D.R.sigW j).1 * ((D.R.sigW j).1 - 1) / 2 +
    (D.R.sigW j).2 * ((D.R.sigW j).2 - 1) / 2)

def Wt.LastPos {D : D7} {j : ℕ} (ka : Wt D j) : Prop :=
  ∀ τ (i : Fin (D.R.sigW j).1), i.1 + 1 = (D.R.sigW j).1 → 1 ≤ ka.aP τ i

section Cusp

variable (D : D7) {n : ℕ}

def ev (l x : Fin n → D.host.E) : D.host.E := ∑ i, l i * x i

def dualO (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  {l | ∀ x ∈ X, ev D l x ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)}

def dualZ (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Fin n → D.host.E) :=
  {l | ∀ x ∈ X, Algebra.trace ℚ D.host.E (ev D l x) ∈ Set.range (Int.cast : ℤ → ℚ)}

def hform (A : Matrix (Fin n) (Fin n) D.host.E) (l m : Fin n → D.host.E) : D.host.E :=
  ∑ i, ∑ k, l i * A i k * D.host.conj (m k)

def IsHerm (A : Matrix (Fin n) (Fin n) D.host.E) : Prop :=
  ∀ i k, A k i = D.host.conj (A i k)

def PosDefE (A : Matrix (Fin n) (Fin n) D.host.E) : Prop :=
  ∀ l : Fin n → D.host.E, l ≠ 0 → ∀ σ : D.host.E →+* ℂ, 0 < (σ (hform D A l l)).re

def IntOn (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (A : Matrix (Fin n) (Fin n) D.host.E)
    (c : D.host.E) : Prop :=
  ∀ l ∈ dualO D X, ∀ m ∈ dualO D X,
    c * hform D A l m ∈ Set.range (algebraMap (𝓞 D.host.E) D.host.E)

def ExpoSet (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) : Set (Matrix (Fin n) (Fin n) D.host.E) :=
  {A | IsHerm D A ∧ PosDefE D A ∧ IntOn D X A (((D.host.g 0 * D.host.g 1 : ℕ) : D.host.E))}

abbrev BForm (D : D7) (n : ℕ) : Type := D.what₂.Tau → Matrix (Fin n) (Fin n) ℂ

def embV (τ : D.what₂.Tau) (x : Fin n → D.host.E) : Fin n → ℂ := fun i => DV.tauEmb D τ (x i)

def Qv (b : BForm D n) (x : Fin n → D.host.E) : ℝ :=
  ∑ τ, (star (embV D τ x) ⬝ᵥ (b τ).mulVec (embV D τ x)).re

def PsdRat (b : BForm D n) : Prop :=
  (∀ τ, (b τ).PosSemidef) ∧ ∃ U : Submodule D.host.E (Fin n → D.host.E), ∀ τ,
    LinearMap.ker (Matrix.toLin' (b τ)) = Submodule.span ℂ (embV D τ '' (U : Set (Fin n → D.host.E)))

def pairB (A : Matrix (Fin n) (Fin n) D.host.E) (b : BForm D n) : ℝ :=
  ∑ τ, (Matrix.trace (b τ * A.map (DV.tauEmb D τ))).re

theorem emb_conj (σ : D.host.E →+* ℂ) (z : D.host.E) : σ (D.host.conj z) = star (σ z) := by
  have hg : D.host.gal D.host.conj = D.R.cc := by
    first
    | exact MulEquiv.apply_symm_apply _ _
    | simp [Formalism.HC.HostRaw.conj]
  exact (D.host.der.conj_iff σ D.host.conj).mpr hg z

theorem embV_add (τ : D.what₂.Tau) (x y : Fin n → D.host.E) :
    embV D τ (x + y) = embV D τ x + embV D τ y := by
  funext i
  simp [embV]

theorem embV_smul (τ : D.what₂.Tau) (c : D.host.E) (x : Fin n → D.host.E) :
    embV D τ (c • x) = DV.tauEmb D τ c • embV D τ x := by
  funext i
  simp [embV]

def Bv (b : BForm D n) (x y : Fin n → D.host.E) : ℝ :=
  ∑ τ, (star (embV D τ x) ⬝ᵥ (b τ).mulVec (embV D τ y) +
    star (embV D τ y) ⬝ᵥ (b τ).mulVec (embV D τ x)).re

theorem Bv_self (b : BForm D n) (x : Fin n → D.host.E) : Bv D b x x = 2 * Qv D b x := by
  unfold Bv Qv
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [Complex.add_re]
  ring

theorem Bv_comm (b : BForm D n) (x y : Fin n → D.host.E) : Bv D b x y = Bv D b y x := by
  unfold Bv
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [add_comm]

theorem Bv_add_left (b : BForm D n) (x x' y : Fin n → D.host.E) :
    Bv D b (x + x') y = Bv D b x y + Bv D b x' y := by
  unfold Bv
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun τ _ => ?_
  simp [embV_add, Matrix.mulVec_add, Complex.add_re]
  try ring

theorem Bv_bal (b : BForm D n) (c : D.host.E) (x y : Fin n → D.host.E) :
    Bv D b (c • x) y = Bv D b x (D.host.conj c • y) := by
  unfold Bv
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [embV_smul, embV_smul, emb_conj]
  simp [Matrix.mulVec_smul]
  try ring

def symB (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : BForm D n) :
    ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) X :=
  ⟨LinearMap.mk₂ ℤ (fun x y : X => Bv D b x y)
      (fun x x' y => Bv_add_left D b x x' y)
      (fun c x y => map_zsmul (AddMonoidHom.mk' (fun x : X => Bv D b x y)
        (fun x x' => Bv_add_left D b x x' y)) c x)
      (fun x y y' => by
        simp only [Bv_comm D b (x : Fin n → D.host.E)]; exact Bv_add_left D b y y' x)
      (fun c x y => map_zsmul (AddMonoidHom.mk' (fun y : X => Bv D b x y)
        (fun y y' => by
          simp only [Bv_comm D b (x : Fin n → D.host.E)]; exact Bv_add_left D b y y' x)) c y),
    fun x y => Bv_comm D b x y,
    fun c c' h x y => by
      change Bv D b ((c • x : X) : Fin n → D.host.E) y = Bv D b x ((c' • y : X) : Fin n → D.host.E)
      have h1 : ((c • x : X) : Fin n → D.host.E) = (c : D.host.E) • (x : Fin n → D.host.E) := rfl
      have h2 : ((c' • y : X) : Fin n → D.host.E) = (c' : D.host.E) • (y : Fin n → D.host.E) := rfl
      rw [h1, h2, h, Bv_bal]⟩

theorem symB_apply (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : BForm D n) (x y : X) :
    (symB D X b : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) x y = Bv D b x y := rfl

def phiC (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : BForm D n) : ℝ :=
  ModuliIntegralCharts.phiC (fun x : D.host.E => D.host.conj x) (symB D X b)

def trF (z : D.host.E) : ℝ := ∑ τ, (DV.tauEmb D τ z).re

def c1 (CR T c : ℝ) (j : ℕ) : ℝ :=
  RRv D CR * T * c * (dP D j : ℝ) ^ 2 * (rho D j : ℝ) / 2

end Cusp

section Half

variable {E : Type} [Field E] [NumberField E] {cj : E → E} {Y : Type} [AddCommGroup Y] [Module (𝓞 E) Y]

theorem halfForm_eq (β : ModuliIntegralCharts.SymB cj Y) (c c' : 𝓞 E) (hc : (c' : E) = cj (c : E)) (h1 : c + c' = 1) (y : Y) :
    (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y = 2 * (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • y) y := by
  have hs := β.2.1
  have hb := β.2.2 c c' hc y y
  have h2 : (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) ((c + c') • y) y =
      (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c • y) y + (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) (c' • y) y := by
    rw [add_smul, map_add, LinearMap.add_apply]
  rw [h1, one_smul, hs (c' • y) y, ← hb] at h2
  linarith

theorem halfForm_int (β : ModuliIntegralCharts.SymB cj Y) (c c' : 𝓞 E) (hc : (c' : E) = cj (c : E)) (h1 : c + c' = 1)
    (hβ : ∀ a b, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a b = z) (y : Y) :
    ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y / 2 = z := by
  obtain ⟨z, hz⟩ := hβ (c • y) y
  refine ⟨z, ?_⟩
  rw [halfForm_eq β c c' hc h1 y, hz]
  ring

end Half

private theorem isIntegral_one_add_sqrt_neg_div_two {E : Type} [Field E] [NumberField E] (s : E) (d : ℕ) (k : ℤ)
    (hs : s ^ 2 = -(d : E)) (hk : (d : ℤ) + 1 = 4 * k) : IsIntegral ℤ ((1 + s) / 2) := by
  refine ⟨Polynomial.X ^ 2 - Polynomial.X + Polynomial.C k, ?_, ?_⟩
  · first
    | monicity!
    | monicity
  · have h4 : (4 : E) * (k : E) = (d : E) + 1 := by exact_mod_cast hk.symm
    simp only [Polynomial.eval₂_add, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    try simp only [algebraMap_int_eq, eq_intCast]
    linear_combination (1 / 4 : E) * hs + (1 / 4 : E) * h4

theorem halfForm_int_host (D : D7) {Y : Type} [AddCommGroup Y] [Module (𝓞 D.host.E) Y]
    (β : ModuliIntegralCharts.SymB (fun x : D.host.E => D.host.conj x) Y)
    (hβ : ∀ a b, ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) a b = z) (y : Y) :
    ∃ z : ℤ, (β : Y →ₗ[ℤ] Y →ₗ[ℤ] ℝ) y y / 2 = z := by
  have h16 : D.host.d % 16 = 7 := D.host.hyp.2.2.2.1
  obtain ⟨k, hk⟩ : ∃ k : ℤ, (D.host.d : ℤ) + 1 = 4 * k := ⟨((D.host.d : ℤ) + 1) / 4, by omega⟩
  set s := D.host.sqd with hs_def
  have hs : s ^ 2 = -(D.host.d : D.host.E) := D.host.sqd_sq

  have hcs : D.host.conj s = -s := by
    apply D.host.φ₀.injective
    rw [emb_conj, map_neg]
    have hw : (D.host.φ₀ s) ^ 2 = -(D.host.d : ℂ) := by
      rw [← map_pow, hs, map_neg, map_natCast]
    set w := D.host.φ₀ s
    have hre : w.re * w.re - w.im * w.im = -(D.host.d : ℝ) := by
      have h := congrArg Complex.re hw
      first
      | rwa [pow_two, Complex.mul_re, Complex.neg_re, Complex.natCast_re] at h
      | simpa [pow_two] using h
    have him : w.re * w.im + w.im * w.re = 0 := by
      have h := congrArg Complex.im hw
      first
      | rwa [pow_two, Complex.mul_im, Complex.neg_im, Complex.natCast_im, neg_zero] at h
      | simpa [pow_two] using h
    have hdpos : (0 : ℝ) < (D.host.d : ℝ) := by
      have h : 0 < D.host.d := by omega
      exact_mod_cast h
    have h0 : w.re = 0 := by
      by_contra hne
      have him' : w.im = 0 := by
        have h : w.re * w.im = 0 := by linarith
        rcases mul_eq_zero.mp h with h | h
        · exact absurd h hne
        · exact h
      rw [him'] at hre
      nlinarith [mul_self_nonneg w.re]
    apply Complex.ext <;> simp [h0]

  have hint : IsIntegral ℤ ((1 + s) / 2) := isIntegral_one_add_sqrt_neg_div_two s D.host.d k hs hk
  let c : 𝓞 D.host.E := ⟨(1 + s) / 2, hint⟩
  have hc : ((1 - c : 𝓞 D.host.E) : D.host.E) = (fun x : D.host.E => D.host.conj x) (c : D.host.E) := by
    show (1 : D.host.E) - (1 + s) / 2 = D.host.conj ((1 + s) / 2)
    rw [map_div₀, map_add, map_one, hcs, map_ofNat]
    ring
  exact halfForm_int β c (1 - c) hc (add_sub_cancel c 1) hβ y

theorem Qv_int_host (D : D7) {n : ℕ} (X : Submodule (𝓞 D.host.E) (Fin n → D.host.E)) (b : BForm D n)
    (hb : ∀ x y : X, ∃ z : ℤ, Bv D b x y = z) (x : X) : ∃ z : ℤ, Qv D b x = z := by
  obtain ⟨z, hz⟩ := halfForm_int_host D (symB D X b) (fun a c => by rw [symB_apply]; exact hb a c) x
  refine ⟨z, ?_⟩
  rw [symB_apply, Bv_self] at hz
  linarith

structure Prov (D : D7) where

  KO : Type
  [fKO : Field KO]
  [nfKO : NumberField KO]

  eO : 𝓞 KO ≃+* D.what₂.O

  Cusp : (j : ℕ) → Wt D j → Type
  [acgC : ∀ j ka, AddCommGroup (Cusp j ka)]
  [modC : ∀ j ka, Module KO (Cusp j ka)]
  [fdC : ∀ j ka, FiniteDimensional KO (Cusp j ka)]
  [modOC : ∀ j ka, Module (𝓞 KO) (Cusp j ka)]
  [towC : ∀ j ka, IsScalarTower (𝓞 KO) KO (Cusp j ka)]

  Mlat : ∀ j ka, Submodule (𝓞 KO) (Cusp j ka)

  supN : ∀ j ka, (KO →+* ℂ) → Cusp j ka → ℝ
  supN_nonneg : ∀ j ka σ F, 0 ≤ supN j ka σ F
  supN_eq_zero : ∀ j ka σ F, supN j ka σ F = 0 ↔ F = 0
  supN_smul : ∀ j ka σ (a : KO) F, supN j ka σ (a • F) = ‖σ a‖ * supN j ka σ F
  supN_add : ∀ j ka σ F G, supN j ka σ (F + G) ≤ supN j ka σ F + supN j ka σ G

  l2NormAlt : ∀ j ka, (KO →+* ℂ) → Cusp j ka → ℝ
  l2Norm_nonneg_bis : ∀ j ka σ F, 0 ≤ l2NormAlt j ka σ F
  l2Norm_eq_zero_iff : ∀ j ka σ F, l2NormAlt j ka σ F = 0 ↔ F = 0
  l2Norm_smul_alt : ∀ j ka σ (a : KO) F, l2NormAlt j ka σ (a • F) = ‖σ a‖ * l2NormAlt j ka σ F
  l2Norm_add_le' : ∀ j ka σ F G, l2NormAlt j ka σ (F + G) ≤ l2NormAlt j ka σ F + l2NormAlt j ka σ G
  l2Norm_le_supNorm_alt : ∀ j ka σ F, l2NormAlt j ka σ F ≤ supN j ka σ F

  Cu : ℕ → Type

  Xc : ∀ j, Cu j → Submodule (𝓞 D.host.E) (Fin (rho D j) → D.host.E)
  Xc_lat : ∀ j c, Submodule.IsLattice D.host.E (Xc j c)

  FJt : ∀ j (c : Cu j), ExpoSet D (Xc j c) → Wt D j → Type
  [acgF : ∀ j c χ ka, AddCommGroup (FJt j c χ ka)]
  [modF : ∀ j c χ ka, Module KO (FJt j c χ ka)]

  sg : ∀ j (c : Cu j) (χ : ExpoSet D (Xc j c)) (ka : Wt D j), Cusp j ka →ₗ[KO] FJt j c χ ka

attribute [instance] Prov.fKO Prov.nfKO Prov.acgC Prov.modC Prov.fdC Prov.modOC Prov.towC
  Prov.acgF Prov.modF

section Derived

variable {D : D7} (X : Prov D)

def Killed (CR T c : ℝ) {j : ℕ} (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)) : Prop :=
  ∃ xi ∈ dualZ D (X.Xc j cu), xi ≠ 0 ∧ trF D (hform D χ.1 xi xi) ≤ c1 D CR T c j

def MggK (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Submodule X.KO (X.Cusp j ka) :=
  ⨅ (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)) (_ : Killed X CR T c cu χ), LinearMap.ker (X.sg j cu χ ka)

def MggIn (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Submodule (𝓞 X.KO) (X.Mlat j ka) :=
  ((MggK X CR T c j ka).restrictScalars (𝓞 X.KO)).comap (X.Mlat j ka).subtype

abbrev Qm (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : Type :=
  X.Mlat j ka ⧸ MggIn X CR T c j ka

def rhoP (CR T c : ℝ) (j : ℕ) (ka : Wt D j) : ℕ :=
  Module.finrank (𝓞 X.KO) (Qm X CR T c j ka)

def meanLogSup {j : ℕ} {ka : Wt D j} (F : X.Cusp j ka) : ℝ :=
  (∑ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F)) / (Fintype.card (X.KO →+* ℂ) : ℝ)

theorem meanLogSup_le {j : ℕ} {ka : Wt D j} (F : X.Cusp j ka) {b : ℝ}
    (h : ∀ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F) ≤ b) : meanLogSup X F ≤ b := by
  unfold meanLogSup
  have hc : (0 : ℝ) < (Fintype.card (X.KO →+* ℂ) : ℝ) := by
    have h0 : 0 < Fintype.card (X.KO →+* ℂ) := by
      first
      | (rw [NumberField.Embeddings.card]; exact Module.finrank_pos)
      | exact Fintype.card_pos
    exact_mod_cast h0
  rw [div_le_iff₀ hc]
  calc (∑ σ : X.KO →+* ℂ, Real.log (X.supN j ka σ F)) ≤ ∑ _σ : X.KO →+* ℂ, b :=
        Finset.sum_le_sum fun σ _ => h σ
    _ = b * (Fintype.card (X.KO →+* ℂ) : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_comm]

def degO : ℝ := (Module.finrank ℚ X.KO : ℝ)

def rdO : ℝ := |((discr X.KO : ℤ) : ℝ)| ^ (1 / degO X)

def lnN (la : HeightOneSpectrum (𝓞 X.KO)) : ℝ := Real.log (Ideal.absNorm la.asIdeal : ℝ)

def lenAt (la : HeightOneSpectrum (𝓞 X.KO)) (N : Type) [AddCommGroup N] [Module (𝓞 X.KO) N] : ℕ∞ :=
  Module.length (Localization.AtPrime la.asIdeal) (LocalizedModule la.asIdeal.primeCompl N)

def Obound (L : SizeData₂ D) (C A : ℝ) : Prop :=
  Real.log (degO X) ≤ PPv D L C A ∧ Real.log (rdO X) ≤ PPv D L C A

end Derived

section Statements

variable {D : D7}

def adm1 (X : Prov D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ka : Wt D j, Submodule.IsLattice X.KO (X.Mlat j ka)

def adm2 (L : SizeData₂ D) (X : Prov D) (CG AG : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (ka : Wt D j) (F : X.Cusp j ka) (σ : X.KO →+* ℂ),
    X.supN j ka σ F ^ 2 ≤
      Real.exp (PPv D L CG AG * (1 + Real.log ka.size)) * X.l2NormAlt j ka σ F ^ 2

def adm3 (X : Prov D) : Prop :=
  ∀ j, 1 ≤ j → j < D.R.m → ∀ (ka : Wt D j) (F : X.Cusp j ka),
    (∀ (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)), X.sg j cu χ ka F = 0) → F = 0

def TransferenceTheoremCond : Prop := Formalism.HadamardInequality.Transference

def ChowlaSelbergPeriod (L : SizeData₂ D) : Prop := D.gx.OmValue D.host.v L.logDerivativeAtOne

def admitted (L : SizeData₂ D) (X : Prov D) (CG AG : ℝ) : Prop :=
  adm1 X ∧ adm2 L X CG AG ∧ adm3 X ∧ TransferenceTheoremCond ∧ ChowlaSelbergPeriod L

def Conclusion1 (L : SizeData₂ D) (X : Prov D) (C A : ℝ) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ (ka : Wt D j) (F : X.Cusp j ka), F ∈ X.Mlat j ka → F ≠ 0 →
    -(PP0v D L C A * ka.size) ≤ meanLogSup X F

def Conclusion2 (X : Prov D) (CR : ℝ) : Prop :=
  0 ≤ CR → ∀ j, 1 ≤ j → j < D.R.m → (dP D j : ℝ) ^ 2 ≤ RRv D CR →
    ∀ (ka : Wt D j) (T c : ℝ), 0 < T → 0 < c → T * c ≤ 1 →
    ∀ F ∈ X.Mlat j ka, F ∈ MggK X CR T c j ka →
    ∀ (cu : X.Cu j) (χ : ExpoSet D (X.Xc j cu)), X.sg j cu χ ka F ≠ 0 →
    ∀ b : BForm D (rho D j), PsdRat D b → b ≠ 0 →
      T * c * phiC D (X.Xc j cu) b < pairB D χ.1 b

def PointsLemma (L : SizeData₂ D) (X : Prov D) (CR Ck Ch Ah Cc Ac : ℝ) : Prop :=
  0 ≤ CR → Obound X L Ch Ah →
  ∀ j, 1 ≤ j → j < D.R.m → ∀ ka : Wt D j, ka.n = D.R.nV → ka.LastPos →
    ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * L.sc.b →
  ∀ T c : ℝ, 0 < T → 0 < c → T * c ≤ 1 →
  ∃ be : HeightOneSpectrum (𝓞 X.KO) →₀ ℝ, (∀ la, 0 ≤ be la) ∧
    (be.sum fun la v => v * lnN X la) / degO X ≤ PPv D L Cc Ac * ka.size ∧
  ∀ th : Fin (rhoP X CR T c j ka) → X.Mlat j ka,
    Submodule.span X.KO (Set.range fun i => ((th i : X.Mlat j ka) : X.Cusp j ka)) ⊔
      MggK X CR T c j ka = ⊤ →
    (∀ i, meanLogSup X ((th i : X.Mlat j ka) : X.Cusp j ka) ≤ PPv D L Ch Ah * ka.size) →
  ∃ nn : HeightOneSpectrum (𝓞 X.KO) →₀ ℝ,
    (∀ la, ∃ ℓ : ℕ,
      lenAt X la (Qm X CR T c j ka ⧸ Submodule.span (𝓞 X.KO)
        (Set.range fun i => (Submodule.Quotient.mk (th i) : Qm X CR T c j ka))) = ℓ ∧
      (ℓ : ℝ) ≤ nn la + (rhoP X CR T c j ka : ℝ) * be la) ∧
    (nn.sum fun la v => v * lnN X la) / degO X ≤
      (rhoP X CR T c j ka : ℝ) * PPv D L Cc Ac * ka.size

def Stmt (L : SizeData₂ D) (X : Prov D) (CG AG C A CR Ck Ch Ah Cc Ac : ℝ) : Prop :=
  admitted L X CG AG → Conclusion1 L X C A ∧ Conclusion2 X CR ∧ PointsLemma L X CR Ck Ch Ah Cc Ac

def TransferenceBound (X : Prov D) (CR : ℝ) : Prop := TransferenceTheoremCond → Conclusion2 X CR

end Statements

theorem isLattice_of_le_of_le {K V : Type*} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {N₁ M N₂ : Submodule (𝓞 K) V}
    (h₁ : Submodule.IsLattice K N₁) (h₂ : Submodule.IsLattice K N₂) (a : N₁ ≤ M) (b : M ≤ N₂) :
    Submodule.IsLattice K M := by
  refine ⟨?_, ?_⟩
  · exact (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian N₂ h₂.fg)) M b
  · apply eq_top_iff.mpr
    rw [← h₁.span_eq_top]
    exact Submodule.span_mono (fun v hv => a hv)

def Between {D : D7} (X : Prov D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ ka : Wt D j, ∃ N₁ N₂ : Submodule (𝓞 X.KO) (X.Cusp j ka),
    Submodule.IsLattice X.KO N₁ ∧ Submodule.IsLattice X.KO N₂ ∧ N₁ ≤ X.Mlat j ka ∧ X.Mlat j ka ≤ N₂

theorem lattice_iff_between_lattices {D : D7} (X : Prov D) : adm1 X ↔ Between X := by
  constructor
  · intro h j hj hjm ka
    exact ⟨X.Mlat j ka, X.Mlat j ka, h j hj hjm ka, h j hj hjm ka, le_rfl, le_rfl⟩
  · intro h j hj hjm ka
    obtain ⟨N₁, N₂, h₁, h₂, ha, hb⟩ := h j hj hjm ka
    exact isLattice_of_le_of_le h₁ h₂ ha hb

theorem two_le_dP (D : D7) {j : ℕ} (hj : j < D.R.m) : 2 ≤ dP D j := by
  unfold dP rho
  have h1 : 1 ≤ (D.R.sigW j).2 := by
    show 1 ≤ D.R.m - j
    omega
  have h2 : 1 ≤ D.R.f := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    have := D.R.m_le_f
    have := D.R.two_le_m
    omega
  calc 2 = 2 * 1 * 1 := by norm_num
    _ ≤ 2 * D.R.f * (D.R.sigW j).2 := by gcongr

theorem sup_bound_at_zero_exponent {D : D7} (X : Prov D) : Conclusion2 X 0 := by
  intro _ j _ hjm hd
  exfalso
  have h2 : (2 : ℝ) ≤ (dP D j : ℝ) := by exact_mod_cast two_le_dP D hjm
  unfold RRv at hd
  rw [Real.rpow_zero] at hd
  nlinarith

theorem q_bound_at_zero_weight_constant {D : D7} (L : SizeData₂ D) (X : Prov D) (CR Ch Ah Cc Ac : ℝ) : PointsLemma L X CR 0 Ch Ah Cc Ac := by
  intro _ _ j _ _ ka _ _ hs
  exfalso
  rw [zero_mul, zero_mul, zero_mul] at hs
  linarith [Wt.one_le_size ka]

abbrev ProvF {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) : Type 1 :=
  ∀ x (_ : Fm.x1 < x) (i : Fm.Ix x), Prov (Fm.D x i)

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm)

def familyUnitInput : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm1 (XF x hx i)

def FamilySecondHypothesis : Prop :=
  ∃ CG AG x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, adm2 (Fm.L x i) (XF x hx i) CG AG

def FamilyAdmittedLemmaThree : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), adm3 (XF x hx i)

def ChowlaSelbergFamily : Prop := ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, ChowlaSelbergPeriod (Fm.L x i)

def AdmF : Prop := familyUnitInput Fm XF ∧ FamilySecondHypothesis Fm XF ∧ FamilyAdmittedLemmaThree Fm XF ∧ TransferenceTheoremCond ∧ ChowlaSelbergFamily Fm

def Conclusion1Family : Prop :=
  ∃ C A x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.L x i) (XF x hx i) C A

def Conclusion2Family (CR : ℝ) : Prop := ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), Conclusion2 (XF x hx i) CR

def Conclusion3Family (CR Ck : ℝ) : Prop :=
  ∀ Ch Ah : ℝ, ∃ Cc Ac x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
    PointsLemma (Fm.L x i) (XF x hx i) CR Ck Ch Ah Cc Ac

def KudlaFamilyStatement (CR Ck : ℝ) : Prop := AdmF Fm XF → Conclusion1Family Fm XF ∧ Conclusion2Family Fm XF CR ∧ Conclusion3Family Fm XF CR Ck

def TransferenceBoundFamily (CR : ℝ) : Prop := TransferenceTheoremCond → Conclusion2Family Fm XF CR

end Family

abbrev ObjClass : Type 1 := ∀ {D : D7} (_ : SizeData₂ D), Prov D → Prop

section FamilyK

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm)

def GrowthBoundFamilyGivenPolynomial (CG AG : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, adm2 (Fm.L x i) (XF x hx i) CG AG

def AdmFK (CG AG : ℝ) : Prop :=
  familyUnitInput Fm XF ∧ GrowthBoundFamilyGivenPolynomial Fm XF CG AG ∧ FamilyAdmittedLemmaThree Fm XF ∧ TransferenceTheoremCond ∧ ChowlaSelbergFamily Fm

def MeanLogSupLowerBoundFamilyGivenPolynomial (C A : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, Conclusion1 (Fm.L x i) (XF x hx i) C A

def QBoundFamilyGivenPolynomials (CR Ck Ch Ah Cc Ac : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, PointsLemma (Fm.L x i) (XF x hx i) CR Ck Ch Ah Cc Ac

theorem AdmFK.toF {CG AG : ℝ} (h : AdmFK Fm XF CG AG) : AdmF Fm XF := by
  obtain ⟨h1, ⟨x0, h2⟩, h3, h4, h5⟩ := h
  exact ⟨h1, ⟨CG, AG, x0, h2⟩, h3, h4, h5⟩

theorem MeanLogSupLowerBoundFamilyGivenPolynomial.toF {C A : ℝ} (h : MeanLogSupLowerBoundFamilyGivenPolynomial Fm XF C A) : Conclusion1Family Fm XF := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨C, A, x0, hx⟩

theorem q_bound_family_of_polynomials {CR Ck : ℝ} (h : ∀ Ch Ah : ℝ, ∃ Cc Ac : ℝ, QBoundFamilyGivenPolynomials Fm XF CR Ck Ch Ah Cc Ac) :
    Conclusion3Family Fm XF CR Ck := by
  intro Ch Ah
  obtain ⟨Cc, Ac, x0, hx⟩ := h Ch Ah
  exact ⟨Cc, Ac, x0, hx⟩

end FamilyK

theorem one_le_zBase {D : D7} (L : SizeData₂ D) : 1 ≤ zBase L := by
  unfold zBase
  have hL : 1 ≤ L.sc.L := by
    unfold Formalism.BasicNotions.Scale.L
    exact le_of_lt (Real.one_lt_rpow L.sc.one_lt_alt L.sc.eps_pos)
  have hf : (1 : ℝ) ≤ (D.R.f : ℝ) := by
    have h : 1 ≤ D.R.f := by
      unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
      have := D.R.m_le_f
      have := D.R.two_le_m
      omega
    exact_mod_cast h
  have hr : (1 : ℝ) ≤ (D.R.r : ℝ) := by
    have h : 1 ≤ D.R.r := by
      unfold Formalism.BasicNotions.Ranks.r
      have := D.R.two_le_m
      omega
    exact_mod_cast h
  calc (1 : ℝ) = 1 * 1 * 1 := by norm_num
    _ ≤ (D.R.f : ℝ) * (D.R.r : ℝ) * L.sc.L := by gcongr

theorem PPv_mono {D : D7} (L : SizeData₂ D) {C C' A A' : ℝ} (h0 : 0 ≤ C) (hC : C ≤ C') (hA : A ≤ A') :
    PPv D L C A ≤ PPv D L C' A' := by
  unfold PPv
  have hZ := one_le_zBase L
  have h1 : zBase L ^ A ≤ zBase L ^ A' := Real.rpow_le_rpow_of_exponent_le hZ hA
  have h2 : 0 ≤ zBase L ^ A := Real.rpow_nonneg (by linarith) _
  calc C * zBase L ^ A ≤ C * zBase L ^ A' := mul_le_mul_of_nonneg_left h1 h0
    _ ≤ C' * zBase L ^ A' := mul_le_mul_of_nonneg_right hC (le_trans h2 h1)

theorem PointsLemma.mono {D : D7} {L : SizeData₂ D} {X : Prov D} {CR Ck Ch Ah Cc Ac Ch' Ah' Cc' Ac' : ℝ}
    (hh : PPv D L Ch' Ah' ≤ PPv D L Ch Ah) (hc : PPv D L Cc Ac ≤ PPv D L Cc' Ac')
    (h : PointsLemma L X CR Ck Ch Ah Cc Ac) : PointsLemma L X CR Ck Ch' Ah' Cc' Ac' := by
  intro hCR hO j hj hjm ka hn hL hs T c hT hc0 hTc
  obtain ⟨hOd, hOr⟩ := hO
  obtain ⟨be, hbe0, hbe, H⟩ := h hCR ⟨hOd.trans hh, hOr.trans hh⟩ j hj hjm ka hn hL hs T c hT hc0 hTc
  have hsz : 0 ≤ ka.size := le_trans zero_le_one (Wt.one_le_size ka)
  refine ⟨be, hbe0, hbe.trans (mul_le_mul_of_nonneg_right hc hsz), fun th hspan hth => ?_⟩
  obtain ⟨nn, hnn, hsum⟩ := H th hspan (fun i => (hth i).trans (mul_le_mul_of_nonneg_right hh hsz))
  refine ⟨nn, hnn, hsum.trans ?_⟩
  have hr : (0 : ℝ) ≤ (rhoP X CR T c j ka : ℝ) := Nat.cast_nonneg _
  calc (rhoP X CR T c j ka : ℝ) * PPv D L Cc Ac * ka.size
        = (rhoP X CR T c j ka : ℝ) * (PPv D L Cc Ac * ka.size) := by ring
    _ ≤ (rhoP X CR T c j ka : ℝ) * (PPv D L Cc' Ac' * ka.size) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hc hsz) hr
    _ = (rhoP X CR T c j ka : ℝ) * PPv D L Cc' Ac' * ka.size := by ring

theorem QBoundFamilyGivenPolynomials.mono {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {XF : ProvF Fm} {CR Ck Ch Ah Cc Ac Ch' Ah' Cc' Ac' : ℝ}
    (h1 : 0 ≤ Ch') (h2 : Ch' ≤ Ch) (h3 : Ah' ≤ Ah) (h4 : 0 ≤ Cc) (h5 : Cc ≤ Cc') (h6 : Ac ≤ Ac')
    (h : QBoundFamilyGivenPolynomials Fm XF CR Ck Ch Ah Cc Ac) : QBoundFamilyGivenPolynomials Fm XF CR Ck Ch' Ah' Cc' Ac' := by
  obtain ⟨x0, hx⟩ := h
  exact ⟨x0, fun x hx1 hx0 i =>
    PointsLemma.mono (PPv_mono _ h1 h2 h3) (PPv_mono _ h4 h5 h6) (hx x hx1 hx0 i)⟩

def PolynomialFamilyAtObjects (CG AG C A CR Ck Ch Ah Cc Ac : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (XF : ProvF Fm) : Prop :=
  AdmFK Fm XF CG AG → MeanLogSupLowerBoundFamilyGivenPolynomial Fm XF C A ∧ Conclusion2Family Fm XF CR ∧ QBoundFamilyGivenPolynomials Fm XF CR Ck Ch Ah Cc Ac

def PacketAlongFamilyInClass (𝒪 : ObjClass) (CG AG C A CR Ck Ch Ah Cc Ac : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ProvF Fm, (∀ x hx i, 𝒪 (Fm.L x i) (XF x hx i)) → AdmFK Fm XF CG AG →
    MeanLogSupLowerBoundFamilyGivenPolynomial Fm XF C A ∧ Conclusion2Family Fm XF CR ∧ QBoundFamilyGivenPolynomials Fm XF CR Ck Ch Ah Cc Ac

theorem polynomial_family_iff_objects {𝒪 : ObjClass} {CG AG C A CR Ck Ch Ah Cc Ac : ℝ} {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {CH : ℝ} :
    PacketAlongFamilyInClass 𝒪 CG AG C A CR Ck Ch Ah Cc Ac Fm CH ↔
      ∀ XF : ProvF Fm, (∀ x hx i, 𝒪 (Fm.L x i) (XF x hx i)) → PolynomialFamilyAtObjects CG AG C A CR Ck Ch Ah Cc Ac Fm XF := Iff.rfl

def LambdaBoundFamilyOnly (𝒪 : ObjClass) (CG AG C A : ℝ) {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (_CH : ℝ) : Prop :=
  ∀ XF : ProvF Fm, (∀ x hx i, 𝒪 (Fm.L x i) (XF x hx i)) → AdmFK Fm XF CG AG → MeanLogSupLowerBoundFamilyGivenPolynomial Fm XF C A

theorem PacketAlongFamilyInClass.lam {𝒪 : ObjClass} {CG AG C A CR Ck Ch Ah Cc Ac : ℝ} {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {CH : ℝ}
    (h : PacketAlongFamilyInClass 𝒪 CG AG C A CR Ck Ch Ah Cc Ac Fm CH) : LambdaBoundFamilyOnly 𝒪 CG AG C A Fm CH := by
  intro XF hX hA
  exact (h XF hX hA).1

theorem polynomial_family_zero_iff_lambda {𝒪 : ObjClass} {CG AG C A Ch Ah Cc Ac : ℝ} {eps : ℝ} {Fm : Formalism.MainNotions.FamP eps} {CH : ℝ} :
    PacketAlongFamilyInClass 𝒪 CG AG C A 0 0 Ch Ah Cc Ac Fm CH ↔ LambdaBoundFamilyOnly 𝒪 CG AG C A Fm CH := by
  constructor
  · intro h
    exact PacketAlongFamilyInClass.lam h
  · intro h XF hX hA
    exact ⟨h XF hX hA, fun x hx i => sup_bound_at_zero_exponent _, ⟨0, fun x hx _ i => q_bound_at_zero_weight_constant _ _ _ _ _ _ _⟩⟩

structure Sel where
  C : ℝ → ℝ → ℝ
  A : ℝ → ℝ → ℝ
  Cc : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ
  Ac : ℝ → ℝ → ℝ → ℝ → ℝ → ℝ → ℝ

def ClosedAbsoluteShare (𝒪 : ObjClass) (𝒞 : Formalism.MainNotions.FamClass) : Prop :=
  ∃ s : Sel, Formalism.MainNotions.Closed 𝒞 (fun Fm CH => ∀ CG AG CR Ck Ch Ah : ℝ,
    PacketAlongFamilyInClass 𝒪 CG AG (s.C CG AG) (s.A CG AG) CR Ck Ch Ah (s.Cc CG AG CR Ck Ch Ah) (s.Ac CG AG CR Ck Ch Ah) Fm CH)

theorem ClosedAbsoluteShare.fixed {𝒪 : ObjClass} {𝒞 : Formalism.MainNotions.FamClass} (h : ClosedAbsoluteShare 𝒪 𝒞) :
    ∀ CG AG : ℝ, ∃ C A : ℝ, ∀ CR Ck Ch Ah : ℝ, ∃ Cc Ac : ℝ,
      Formalism.MainNotions.Closed 𝒞 (fun Fm CH => PacketAlongFamilyInClass 𝒪 CG AG C A CR Ck Ch Ah Cc Ac Fm CH) := by
  obtain ⟨s, hs⟩ := h
  unfold Formalism.MainNotions.Closed at hs
  obtain ⟨ε1, hε1, hK⟩ := hs
  intro CG AG
  refine ⟨s.C CG AG, s.A CG AG, fun CR Ck Ch Ah => ⟨s.Cc CG AG CR Ck Ch Ah, s.Ac CG AG CR Ck Ch Ah, ?_⟩⟩
  unfold Formalism.MainNotions.Closed
  refine ⟨ε1, hε1, fun eps he1 he2 => ?_⟩
  obtain ⟨K, hK'⟩ := hK eps he1 he2
  exact ⟨K, fun Fm CH hC hL => hK' Fm CH hC hL CG AG CR Ck Ch Ah⟩

end Formalism.MainNotions.WeightFamilies

end
