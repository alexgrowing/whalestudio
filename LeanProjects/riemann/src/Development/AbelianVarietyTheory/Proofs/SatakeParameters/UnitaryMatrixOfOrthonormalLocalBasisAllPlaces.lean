import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.StdBases
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.BeData
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsConstantCoeffOne
import Formalism.LocalRingCardinality.CoeNeZeroOfNotMem
import Formalism.LocalRingCardinality.FactDelDualNabla
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsKurFrobTauEmbPosPl
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormLeOneOfValuationLeOne
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepFrame
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.RepTrace
import Formalism.LocalToGlobal.InertKernelTheory.InertCoprimeLemmas.IntBasis
import Formalism.GaussJetBounds.GaussJetProofs.NormNatCastEqPowPadicValNat

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.TaylorLogMetric GlobalTheory.KerStd Classical
open Formalism.L2.Th1.CM (MaximalUnramifiedExtension)
open Formalism.L2.Th1.D (F1 F2 OwOK TrDual phFF)
open Formalism.InvariantFactorPaths.G7 (UnrOK IsLawOfLog cob)
open Formalism.L2.KerInert.RepFrame (lamB lamBc LamONB)
open GlobalTheory.PadicPlaceBound (smallIdeal norm_int_le_one smallIdeal_isPrime norm_prime_padicComplex)
open scoped Pointwise

namespace GlobalTheory.KerStd.UnitaryMat

variable {D : D7} {p : ℕ} [Fact p.Prime]

def rho (D : D7) (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : D.host.E →+* ℂ_[p] :=
  lam.comp (Formalism.L2.KerInert.IntegralOrthonormalChange.embQ D τ)

theorem lamC_embT_eq (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) (x : D.host.E) :
    lamC lam (embT D τ x) = rho D lam τ x :=
  Formalism.L2.KerInert.IntegralOrthonormalChange.lamC_embT D lam τ x

theorem tauEmb_eq (lam : Qbar →+* ℂ_[p]) (τ : D.what₂.Tau) : tauEmb D lam τ = rho D lam τ :=
  funext fun x => lamC_embT_eq lam τ x

theorem posPl_one (hc : IsResidueClassZero D p) (h0 : hP D p = 0) (z : Bool × HH D) : posPl D p z 1 = z := by
  have hs : ¬ IsSg D p := fun h => by
    have h' : D.host.cls p = PrimeClass.signal := h
    rw [show D.host.cls p = PrimeClass.inertClass from hc] at h'
    cases h'
  simp [posPl, partner, hs, h0]

theorem norm_sigma_lt {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) {a : MaximalUnramifiedExtension p} (ha : ‖(a : ℂ_[p])‖ < 1) :
    ‖((σ a : MaximalUnramifiedExtension p) : ℂ_[p])‖ < 1 := by
  obtain ⟨hp, -, -, -, h⟩ := hσ
  have h1 : ‖((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p])‖ < 1 :=
    lt_of_le_of_lt (h a ha.le) (inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt))
  have h3 : ‖((a ^ p : MaximalUnramifiedExtension p) : ℂ_[p])‖ < 1 := by
    push_cast
    rw [norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) ha hp.ne_zero
  have e : ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = ((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) + ((a ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
    push_cast
    ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h1 h3)

theorem norm_sigma_le {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) {a : MaximalUnramifiedExtension p} (ha : ‖(a : ℂ_[p])‖ ≤ 1) :
    ‖((σ a : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1 := by
  obtain ⟨hp, -, -, -, h⟩ := hσ
  have h1 : ‖((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1 :=
    (h a ha).trans (inv_le_one_of_one_le₀ (by exact_mod_cast hp.one_lt.le))
  have h3 : ‖((a ^ p : MaximalUnramifiedExtension p) : ℂ_[p])‖ ≤ 1 := by
    push_cast
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) ha
  have e : ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = ((σ a - a ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) + ((a ^ p : MaximalUnramifiedExtension p) : ℂ_[p]) := by
    push_cast
    ring
  rw [e]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le h1 h3)

section Frob

variable (lam : Qbar →+* ℂ_[p]) {σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p} (hσ : UnrOK (MaximalUnramifiedExtension p) p σ) (hc : IsResidueClassZero D p) (h0 : hP D p = 0)
include hσ hc h0

theorem frob (z : Bool × HH D) (y : D.host.E) :
    ∃ a : MaximalUnramifiedExtension p, (a : ℂ_[p]) = rho D lam (tauPl D z) y ∧
      ((σ a : MaximalUnramifiedExtension p) : ℂ_[p]) = rho D lam (tauPl D z) (D.host.conj y) := by
  obtain ⟨a, h1, h2⟩ := GlobalTheory.KerStd.exists_kur_frob_tauEmb_posPl D p lam σ hσ (Or.inl hc) z y
  rw [posPl_one hc h0] at h2
  exact ⟨a, by rw [h1, tauEmb_eq], by rw [h2, tauEmb_eq]⟩

theorem norm_conj_lt (z : Bool × HH D) {y : D.host.E} (hy : ‖rho D lam (tauPl D z) y‖ < 1) :
    ‖rho D lam (tauPl D z) (D.host.conj y)‖ < 1 := by
  obtain ⟨a, h1, h2⟩ := frob lam hσ hc h0 z y
  rw [← h2]
  exact norm_sigma_lt hσ (by rw [h1]; exact hy)

theorem norm_conj_le (z : Bool × HH D) {y : D.host.E} (hy : ‖rho D lam (tauPl D z) y‖ ≤ 1) :
    ‖rho D lam (tauPl D z) (D.host.conj y)‖ ≤ 1 := by
  obtain ⟨a, h1, h2⟩ := frob lam hσ hc h0 z y
  rw [← h2]
  exact norm_sigma_le hσ (by rw [h1]; exact hy)

theorem norm_cmTypeEmbeddingPadic_le_one_of_mem_baseIdeal (z : Bool × HH D) {a : D.host.E} (ha : a ∈ D.host.AA0) : ‖rho D lam (tauPl D z) a‖ ≤ 1 := by
  set ρ := rho D lam (tauPl D z) with hρ
  have hn : ¬ D.host.𝔟 ≤ smallIdeal ρ := fun h => by
    have h2 : D.host.conj • D.host.𝔟 ≤ smallIdeal ρ := by
      rw [Ideal.pointwise_smul_def, Ideal.map_le_iff_le_comap]
      exact fun x hx => norm_conj_lt lam hσ hc h0 z (h hx)
    have h3 : D.host.𝔟 ⊔ D.host.conj • D.host.𝔟 = ⊤ := D.host.𝔟_spec.2
    exact (smallIdeal_isPrime ρ).ne_top (top_le_iff.1 (h3 ▸ sup_le h h2))
  obtain ⟨t, ht, htP⟩ := SetLike.not_le_iff_exists.1 hn
  have hb : ((D.host.𝔟 : Ideal (𝓞 D.host.E)) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.2 fun h => hn (h ▸ bot_le)
  obtain ⟨u, hu⟩ := (FractionalIdeal.mem_one_iff _).1
    ((FractionalIdeal.mem_inv_iff hb).1 ha _ (FractionalIdeal.mem_coeIdeal_of_mem _ ht))
  have hnt : 1 ≤ ‖ρ (t : D.host.E)‖ := not_lt.1 htP
  have e : ρ (u : D.host.E) = ρ a * ρ (t : D.host.E) := by
    rw [← map_mul]
    exact congrArg ρ hu
  have h4 := norm_int_le_one ρ u
  rw [e, norm_mul] at h4
  exact (le_mul_of_one_le_right (norm_nonneg _) hnt).trans h4

end Frob

theorem conj_conj (D : D7) (x : D.host.E) : D.host.conj (D.host.conj x) = x :=
  D.host.φ₀.injective (by
    rw [Formalism.HC.HostAx.conjE_apply, Formalism.HC.HostAx.conjE_apply, Complex.conj_conj])

section Entries

variable {ρ : D.host.E →+* ℂ_[p]} {N N' : ℕ} {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
  {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {P : Matrix (Fin N) (Fin N) D.host.E}
  {P' Q' : Matrix (Fin N') (Fin N') D.host.E}

theorem entry_le_of_maps (hQ : Q' * P' = 1) (hP : LocBasisW D ρ L P) (hP' : LocBasisW D ρ L' P')
    {A : Matrix (Fin N') (Fin N) D.host.E} (hA : ∀ x ∈ L, A.mulVec x ∈ L') (b : Fin N') (a : Fin N) :
    ‖ρ ((Q' * A * P) b a)‖ ≤ 1 := by
  obtain ⟨s, hs, hsL⟩ := hP.2.1 a
  obtain ⟨s', hs', c, hc⟩ := hP'.2.2 _ (hA _ hsL)
  have hcol : ∀ a' : Fin N', Q'.mulVec (P'.transpose a') = fun b => (1 : Matrix (Fin N') (Fin N') D.host.E) b a' :=
    fun a' => by
      funext b
      rw [← hQ]
      rfl
  have key : (s' : D.host.E) * ((s : D.host.E) * (Q' * A * P) b a) = (c b : D.host.E) := by
    have h1 := congrArg (fun v => Q'.mulVec v b) hc
    simp only [Matrix.mulVec_smul, Matrix.mulVec_sum, hcol] at h1
    have e1 : Q'.mulVec (A.mulVec (P.transpose a)) b = (Q' * A * P) b a := by
      rw [Matrix.mulVec_mulVec]
      rfl
    have e2 : (∑ x, c x • fun b => (1 : Matrix (Fin N') (Fin N') D.host.E) b x) b = (c b : D.host.E) := by
      rw [Finset.sum_apply]
      simp [Algebra.smul_def, Matrix.one_apply]
    rw [e2, Pi.smul_apply, Pi.smul_apply, e1, Algebra.smul_def, Algebra.smul_def] at h1
    exact h1
  have h4 := norm_int_le_one ρ (c b)
  rw [← key, map_mul, map_mul, norm_mul, norm_mul, hs, hs', one_mul, one_mul] at h4
  exact h4

def IntIn (ρ : D.host.E →+* ℂ_[p]) (Q' : Matrix (Fin N') (Fin N') D.host.E) (P : Matrix (Fin N) (Fin N) D.host.E)
    (B : Matrix (Fin N') (Fin N) D.host.E) : Prop :=
  ∀ b a, ‖ρ ((Q' * B * P) b a)‖ ≤ 1

theorem entry_smul (e : D.host.E) (B : Matrix (Fin N') (Fin N) D.host.E) (b : Fin N') (a : Fin N) :
    (Q' * (e • B) * P) b a = e * (Q' * B * P) b a := by
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_apply, smul_eq_mul]

theorem IntIn.smul {e : D.host.E} (he : ‖ρ e‖ ≤ 1) {B : Matrix (Fin N') (Fin N) D.host.E} (h : IntIn ρ Q' P B) :
    IntIn ρ Q' P (e • B) := fun b a => by
  rw [entry_smul, map_mul, norm_mul]
  exact mul_le_one₀ he (norm_nonneg _) (h b a)

theorem IntIn.add {B C : Matrix (Fin N') (Fin N) D.host.E} (hB : IntIn ρ Q' P B) (hC : IntIn ρ Q' P C) :
    IntIn ρ Q' P (B + C) := fun b a => by
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.add_apply, map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hB b a) (hC b a))

theorem IntIn.zero : IntIn ρ Q' P (0 : Matrix (Fin N') (Fin N) D.host.E) := fun b a => by
  simp

theorem IntIn.smul_int (c : 𝓞 D.host.E) {B : Matrix (Fin N') (Fin N) D.host.E} (h : IntIn ρ Q' P B) :
    IntIn ρ Q' P (c • B) := by
  have e : c • B = (c : D.host.E) • B := (algebraMap_smul D.host.E c B).symm
  rw [e]
  exact h.smul (norm_int_le_one ρ c)

theorem intIn_of_mem (hA0 : ∀ a ∈ D.host.AA0, ‖ρ a‖ ≤ 1) (hQ : Q' * P' = 1) (hP : LocBasisW D ρ L P)
    (hP' : LocBasisW D ρ L' P') {B : Matrix (Fin N') (Fin N) D.host.E} (hB : B ∈ YYl D L L') : IntIn ρ Q' P B := by
  have hhom : ∀ A ∈ homL D L L', IntIn ρ Q' P A := by
    intro A hA
    induction hA using Submodule.span_induction with
    | mem A hA => exact fun b a => entry_le_of_maps hQ hP hP' hA b a
    | zero => exact IntIn.zero
    | add X Y _ _ h1 h2 => exact h1.add h2
    | smul c X _ h => exact h.smul_int c
  induction hB using Submodule.span_induction with
  | mem B hB =>
    obtain ⟨a, ha, A, hA, rfl⟩ := hB
    exact (hhom A hA).smul (hA0 a (FractionalIdeal.mem_coe.1 ha))
  | zero => exact IntIn.zero
  | add X Y _ _ h1 h2 => exact h1.add h2
  | smul c X _ h => exact h.smul_int c

theorem intIn_of_locBasis (hp : ‖(p : ℂ_[p])‖ < 1) (hA0 : ∀ a ∈ D.host.AA0, ‖ρ a‖ ≤ 1) (hQ : Q' * P' = 1)
    (hP : LocBasisW D ρ L P) (hP' : LocBasisW D ρ L' P') {r : ℕ} {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hb : LocBasis D p (YYl D L L') b) (i : Fin r) : IntIn ρ Q' P (b i) := fun x a => by
  obtain ⟨s, hs, hsb⟩ := hb.2.1 i
  have h1 := intIn_of_mem hA0 hQ hP hP' hsb x a
  have hs1 : ‖(s : ℂ_[p])‖ = 1 :=
    Formalism.DworkPowerSeriesWeights.norm_natCast_eq_one_of_not_dvd (Fact.out : p.Prime) hp
      (fun h => (Fact.out : p.Prime).one_lt.ne' (Nat.Coprime.eq_one_of_dvd hs.symm h))
  rw [entry_smul, map_mul, map_natCast, norm_mul, hs1, one_mul] at h1
  exact h1

end Entries

section Sums

variable {R ι κ : Type} [CommRing R] [Fintype ι] [Fintype κ] [DecidableEq κ]

theorem lin_of_inv {u v : κ → ι → R} (h : ∀ k k', ∑ i, u k i * v k' i = if k = k' then 1 else 0) (A : κ → R) (k : κ) :
    ∑ i, u k i * ∑ k', v k' i * A k' = A k := by
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have e : ∀ k', ∑ i, u k i * (v k' i * A k') = (if k = k' then 1 else 0) * A k' := fun k' => by
    rw [← h k k', Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp [e]

theorem bilin_of_inv {u v : κ → ι → R} (h : ∀ k k', ∑ i, u k i * v k' i = if k = k' then 1 else 0) (B A : κ → R) :
    ∑ i, (∑ k, u k i * B k) * ∑ k', v k' i * A k' = ∑ k, B k * A k := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← lin_of_inv h A k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

end Sums

section Subst

variable {K : Type} [Field K] {κ ν ι : Type} [Fintype κ] [Fintype ν] [Fintype ι]

theorem subst_lin {a : ν → MvPowerSeries ι K} (hs : MvPowerSeries.HasSubst a) (w : ν → K) :
    MvPowerSeries.subst a (∑ j, MvPowerSeries.C (w j) * MvPowerSeries.X j : MvPowerSeries ν K) =
      ∑ j, MvPowerSeries.C (w j) * a j := by
  rw [← MvPowerSeries.coe_substAlgHom hs, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [MvPowerSeries.coe_substAlgHom hs, MvPowerSeries.subst_mul hs, MvPowerSeries.subst_X hs, MvPowerSeries.subst_C]

end Subst

section Subst2

variable {p : ℕ} [Fact p.Prime] {κ ν ι : Type} [Finite κ] [Fintype ν] [Fintype ι]

theorem subst_atLin {s : Type} [Fintype s] [Finite s] (m : s → ν → ℂ_[p]) (t : s → ι → ℂ_[p]) (g : ι → ν → ℂ_[p]) (c : ℂ_[p])
    (h : ∀ k j, m k j * c = ∑ i, t k i * g i j) (G : MvPowerSeries s ℂ_[p]) :
    (MvPowerSeries.subst (fun v : ν => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries ν ℂ_[p]))
      (atLin m (fun j => MvPowerSeries.X j) G) : MvPowerSeries ν ℂ_[p]) =
    MvPowerSeries.subst (fun i : ι => (∑ j, MvPowerSeries.C (g i j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p]))
      (MvPowerSeries.subst (fun k : s => (∑ i, MvPowerSeries.C (t k i) * MvPowerSeries.X i : MvPowerSeries ι ℂ_[p])) G :
        MvPowerSeries ι ℂ_[p]) := by
  have h1 : MvPowerSeries.HasSubst (fun k : s =>
      (∑ j, algebraMap ℂ_[p] (MvPowerSeries ν ℂ_[p]) (m k j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h2 : MvPowerSeries.HasSubst (fun v : ν => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h3 : MvPowerSeries.HasSubst (fun k : s => (∑ i, MvPowerSeries.C (t k i) * MvPowerSeries.X i : MvPowerSeries ι ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  have h4 : MvPowerSeries.HasSubst (fun i : ι => (∑ j, MvPowerSeries.C (g i j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p])) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun k => by simp
  unfold atLin
  rw [MvPowerSeries.subst_comp_subst_apply h1 h2, MvPowerSeries.subst_comp_subst_apply h3 h4]
  congr 1
  funext k
  have e : (∑ j, algebraMap ℂ_[p] (MvPowerSeries ν ℂ_[p]) (m k j) * MvPowerSeries.X j : MvPowerSeries ν ℂ_[p]) =
      ∑ j, MvPowerSeries.C (m k j) * MvPowerSeries.X j := rfl
  rw [e, subst_lin h2, subst_lin h4]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← mul_assoc, ← map_mul, h k j, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_mul, mul_assoc]

end Subst2

section Main

variable (D) {N N' r : ℕ} (lam : Qbar →+* ℂ_[p]) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E)
  (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E)

def yy (i : Fin r) (j : (Bool × HH D) × Fin N × Fin N') : D.host.E :=
  ∑ b', ∑ a', D.host.conj (b i b' a') * P' (tauPl D j.1) b' j.2.2 * D.host.conj (P (tauPl D j.1) a' j.2.1)

def cA (j : (Bool × HH D) × Fin N × Fin N') (k : D.what₂.Tau × Fin N' × Fin N) : ℂ_[p] :=
  if tauPl D j.1 = k.1 then
    rho D lam (tauPl D j.1) (P' (tauPl D j.1) k.2.1 j.2.2) * rho D lam (tauPl D j.1) (D.host.conj (P (tauPl D j.1) k.2.2 j.2.1))
  else 0

def cB (j : (Bool × HH D) × Fin N × Fin N') (k : D.what₂.Tau × Fin N' × Fin N) : ℂ_[p] :=
  if tauPl D j.1 = k.1 then
    rho D lam (tauPl D j.1) (D.host.conj (P' (tauPl D j.1) k.2.1 j.2.2)) * rho D lam (tauPl D j.1) (P (tauPl D j.1) k.2.2 j.2.1)
  else 0

theorem lamB_eq (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) :
    lamB D lam b k i = rho D lam k.1 (b i k.2.1 k.2.2) := lamC_embT_eq lam _ _

theorem lamBc_eq (k : D.what₂.Tau × Fin N' × Fin N) (i : Fin r) :
    lamBc D lam b k i = rho D lam k.1 (D.host.conj (b i k.2.1 k.2.2)) := lamC_embT_eq lam _ _

theorem rho_yy (i : Fin r) (j : (Bool × HH D) × Fin N × Fin N') :
    rho D lam (tauPl D j.1) (yy D P P' b i j) = ∑ k, lamBc D lam b k i * cA D lam P P' j k := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (tauPl D j.1)]
  · rw [Fintype.sum_prod_type]
    simp only [yy, map_sum, map_mul, cA, if_true, lamBc_eq]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro t _ ht
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [cA, Ne.symm ht]
  · simp

theorem rho_conj_yy (i : Fin r) (j : (Bool × HH D) × Fin N × Fin N') :
    rho D lam (tauPl D j.1) (D.host.conj (yy D P P' b i j)) = ∑ k, lamB D lam b k i * cB D lam P P' j k := by
  rw [Fintype.sum_prod_type, Finset.sum_eq_single (tauPl D j.1)]
  · rw [Fintype.sum_prod_type]
    simp only [yy, map_sum, map_mul, cB, if_true, lamB_eq, conj_conj]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    ring
  · intro t _ ht
    refine Finset.sum_eq_zero fun x _ => ?_
    simp [cB, Ne.symm ht]
  · simp

theorem conj_yy (i : Fin r) (j : (Bool × HH D) × Fin N × Fin N') :
    D.host.conj (yy D P P' b i j) =
      (((P' (tauPl D j.1)).map D.host.conj).transpose * b i * P (tauPl D j.1)) j.2.2 j.2.1 := by
  simp only [yy, map_sum, map_mul, conj_conj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

variable {P P'}

theorem chgB_eq (hU : ∀ z, ((P (tauPl D z)).map D.host.conj).transpose * P (tauPl D z) = 1)
    (j : (Bool × HH D) × Fin N × Fin N') (k : D.what₂.Tau × Fin N' × Fin N) :
    chgB D lam P P' k ((0 : ZMod 1), (tauPl D j.1, j.2)) = cA D lam P P' j k := by
  have hinv : ((P (tauPl D j.1)).map (tauEmb D lam (tauPl D j.1)))⁻¹ =
      (((P (tauPl D j.1)).map D.host.conj).transpose).map (rho D lam (tauPl D j.1)) := by
    refine Matrix.inv_eq_left_inv ?_
    rw [tauEmb_eq, ← Matrix.map_mul, hU, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold chgB cA
  by_cases h : tauPl D j.1 = k.1
  · simp only [if_pos h]
    rw [hinv, tauEmb_eq]
    rfl
  · simp only [if_neg h]

theorem sum_cB_cA (hU : ∀ z, ((P (tauPl D z)).map D.host.conj).transpose * P (tauPl D z) = 1)
    (hU' : ∀ z, ((P' (tauPl D z)).map D.host.conj).transpose * P' (tauPl D z) = 1)
    (j j' : (Bool × HH D) × Fin N × Fin N') :
    ∑ k, cB D lam P P' j k * cA D lam P P' j' k = if j = j' then 1 else 0 := by
  obtain ⟨z, a, b⟩ := j
  obtain ⟨z', a', b'⟩ := j'
  by_cases hz : z = z'
  · subst hz
    have e1 : ∑ x, D.host.conj (P' (tauPl D z) x b) * P' (tauPl D z) x b' = if b = b' then 1 else 0 := by
      have := congrFun (congrFun (hU' z) b) b'
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have e2 : ∑ x, D.host.conj (P (tauPl D z) x a') * P (tauPl D z) x a = if a' = a then 1 else 0 := by
      have := congrFun (congrFun (hU z) a') a
      rw [Matrix.mul_apply, Matrix.one_apply] at this
      exact this
    have e3 : ∑ k, cB D lam P P' (z, a, b) k * cA D lam P P' (z, a', b') k =
        rho D lam (tauPl D z) (∑ x, D.host.conj (P' (tauPl D z) x b) * P' (tauPl D z) x b') *
          rho D lam (tauPl D z) (∑ x, D.host.conj (P (tauPl D z) x a') * P (tauPl D z) x a) := by
      rw [Fintype.sum_prod_type, Finset.sum_eq_single (tauPl D z)]
      · rw [Fintype.sum_prod_type]
        rw [map_sum, map_sum, Finset.sum_mul_sum]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
        simp only [map_mul, cA, cB, if_true]
        ring
      · intro t _ ht
        refine Finset.sum_eq_zero fun x _ => ?_
        simp [cA, Ne.symm ht]
      · simp
    rw [e3, e1, e2]
    by_cases hb : b = b'
    · by_cases ha : a = a'
      · simp [hb, ha]
      · have ha' : ¬ a' = a := fun h => ha h.symm
        simp [hb, ha, ha']
    · simp [hb]
  · have hne : tauPl D z ≠ tauPl D z' := fun h => hz ((tauPl_bij D).1 h)
    rw [if_neg (fun h => hz (congrArg Prod.fst h))]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases h : tauPl D z = k.1
    · have h' : tauPl D z' ≠ k.1 := fun h2 => hne (h.trans h2.symm)
      simp [cA, h']
    · simp [cB, h]

end Main

end GlobalTheory.KerStd.UnitaryMat

open GlobalTheory.KerStd.UnitaryMat in

theorem GlobalTheory.KerStd.unitary_of_orthonormal : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (σ : MaximalUnramifiedExtension p →+* MaximalUnramifiedExtension p), UnrOK (MaximalUnramifiedExtension p) p σ → 5 ≤ p → IsResidueClassZero D p → hP D p = 0 → ∀ (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)) (P : D.what₂.Tau → Matrix (Fin N) (Fin N) D.host.E) (P' : D.what₂.Tau → Matrix (Fin N') (Fin N') D.host.E), admitted D N N' L L' → StdBases D lam L P → StdBases D lam L' P' → ∀ (r : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E), LocBasis D p (YYl D L L') b → TaylorLogMetric.Orthonormal D b → ∃ γ : Fin r → (OrbitPlaces.Pl D × Fin N × Fin N') → MaximalUnramifiedExtension p, (∀ i j, ‖γ i j‖ ≤ 1 ∧ σ (σ (γ i j)) = γ i j) ∧ (∀ j j', ∑ i, σ (γ i j) * γ i j' = if j = j' then 1 else 0) ∧ ∀ (c : ℂ_[p]) (G : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p]), (MvPowerSeries.subst (fun v : OrbitPlaces.Pl D × Fin N × Fin N' => (MvPowerSeries.C c * MvPowerSeries.X v : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (stdSer D lam (fun _ => 1) P P' G) : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p]) = MvPowerSeries.subst (fun i => (∑ j, MvPowerSeries.C (γ i j : ℂ_[p]) * MvPowerSeries.X j : MvPowerSeries (OrbitPlaces.Pl D × Fin N × Fin N') ℂ_[p])) (thOrth D lam c b G) := by
  intro D p _ lam σ hσ h5 hc h0 N N' L L' P P' hadm hP hP' r b hb ho
  have hon : LamONB D lam b := Formalism.L2.KerInert.RepFrame.lamONB_of_cols D lam b
    (Formalism.L2.KerInert.RepFrame.rank_of_locBasis L L' hadm.2.2.1 hadm.2.2.2 b hb)
    (Formalism.L2.KerInert.RepFrame.cols_of_trace D (Formalism.L2.KerInert.RepFrame.trace_tau_sum D) lam b ho)
  have hU : ∀ z, ((P (tauPl D z)).map D.host.conj).transpose * P (tauPl D z) = 1 := fun z => by
    have := hP.2.1 (Or.inl hc) z
    rwa [posPl_one hc h0] at this
  have hU' : ∀ z, ((P' (tauPl D z)).map D.host.conj).transpose * P' (tauPl D z) = 1 := fun z => by
    have := hP'.2.1 (Or.inl hc) z
    rwa [posPl_one hc h0] at this
  have hp1 : ‖(p : ℂ_[p])‖ < 1 := by
    rw [norm_prime_padicComplex]
    exact inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  choose g hg1 hg2 using fun (i : Fin r) (j : (Bool × HH D) × Fin N × Fin N') =>
    frob lam hσ hc h0 j.1 (yy D P P' b i j)
  refine ⟨g, fun i j => ⟨?_, ?_⟩, fun j j' => ?_, fun c G => ?_⟩
  · show ‖(g i j : ℂ_[p])‖ ≤ 1
    rw [hg1, ← conj_conj D (yy D P P' b i j)]
    refine norm_conj_le lam hσ hc h0 j.1 ?_
    rw [conj_yy]
    have hb' := intIn_of_locBasis hp1 (fun a ha => norm_cmTypeEmbeddingPadic_le_one_of_mem_baseIdeal lam hσ hc h0 j.1 ha) (hU' j.1)
      (by rw [← tauEmb_eq]; exact hP.1 _) (by rw [← tauEmb_eq]; exact hP'.1 _) hb i
    exact hb' _ _
  · obtain ⟨a', h1, h2⟩ := frob lam hσ hc h0 j.1 (D.host.conj (yy D P P' b i j))
    have e : a' = σ (g i j) := Subtype.ext (h1.trans (hg2 i j).symm)
    rw [e, conj_conj] at h2
    exact Subtype.ext (h2.trans (hg1 i j).symm)
  · have e : ((∑ i, σ (g i j) * g i j' : MaximalUnramifiedExtension p) : ℂ_[p]) = ∑ i, (σ (g i j) : ℂ_[p]) * (g i j' : ℂ_[p]) := by
      push_cast
      rfl
    apply Subtype.ext
    rw [e]
    simp only [hg1, hg2, rho_yy, rho_conj_yy]
    rw [bilin_of_inv hon, sum_cB_cA D lam hU hU']
    split_ifs <;> simp
  · refine subst_atLin _ _ _ c (fun k j => ?_) G
    rw [one_mul, chgB_eq D lam hU]
    have e : ∀ i, c * lamC lam (embT D k.1 (b i k.2.1 k.2.2)) * (g i j : ℂ_[p]) =
        c * (lamB D lam b k i * ∑ k', lamBc D lam b k' i * cA D lam P P' j k') := fun i => by
      rw [hg1, rho_yy, mul_assoc]
      rfl
    simp only [e]
    rw [← Finset.mul_sum, lin_of_inv hon, mul_comm]
