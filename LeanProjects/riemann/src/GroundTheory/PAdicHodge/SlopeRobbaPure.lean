import Mathlib
import GroundTheory.PAdicHodge.SlopeRobbaDegree
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

open Filter Topology Module Matrix

set_option linter.unusedSectionVars false

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  [IsDiscreteValuationRing (normInteger K)]

theorem Robba.gaussNorm_single_alt (k : ℤ) (c : K) : Robba.norm1 (Robba.single k c) = ‖c‖ := by
  refine le_antisymm (ciSup_le fun n => ?_) ?_
  · by_cases hn : n = k
    · subst hn; simp
    · simp [hn]
  · simpa using Robba.norm_coeff_le_norm1 (Robba.single_mem_bounded k c) k

namespace FrobeniusLift

variable (F : FrobeniusLift K)

theorem gaussNorm_phi_unit (u : (Robba K)ˣ) :
    Robba.norm1 (F.phi u) = Robba.norm1 (u : Robba K) :=
  gaussNorm_phi (Robba.unit_mem_bounded u)

theorem gaussNorm_phi_pow_unit (d : ℕ) (u : (Robba K)ˣ) :
    Robba.norm1 ((F.phi ^ d) u) = Robba.norm1 (u : Robba K) := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ', RingHom.mul_def, RingHom.comp_apply]
    have hu : IsUnit ((F.phi ^ d) (u : Robba K)) := u.isUnit.map _
    have := F.gaussNorm_phi_unit hu.unit
    rw [IsUnit.unit_spec] at this
    rw [this, ih]

def unitOrd : PhiModule.UnitOrd (Robba K) F.phi := Robba.unitOrd F.phi F.gaussNorm_phi_unit

def unitOrdPow (d : ℕ) : PhiModule.UnitOrd (Robba K) (F.phi ^ d) :=
  Robba.unitOrd (F.phi ^ d) (F.gaussNorm_phi_pow_unit d)

theorem unitOrdPow_eq (d : ℕ) : F.unitOrdPow d = F.unitOrd.pow d := rfl

end FrobeniusLift

namespace PhiModule

variable {R : Type*} [CommRing R] {φ : R →+* R}

theorem isPhiModule_of_smul [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {Ψ : M →ₛₗ[φ] M} {c : R} (h : IsPhiModule (c • Ψ)) : IsPhiModule Ψ := by
  classical
  let b := Module.Free.chooseBasis R M
  rw [isPhiModule_iff_isUnit_det b, phiMatrix_smul, det_smul] at h
  rw [isPhiModule_iff_isUnit_det b]
  exact isUnit_of_mul_isUnit_right h

theorem isPhiModule_of_iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M]
    [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {d : ℕ} (hd : 0 < d) (h : IsPhiModule (iterate Φ d)) :
    IsPhiModule Φ := by
  classical
  let b := Module.Free.chooseBasis R M
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hd
  rw [isPhiModule_iff_isUnit_det b, zero_add, phiMatrix_iterate_succ, det_mul] at h
  rw [isPhiModule_iff_isUnit_det b]
  exact isUnit_of_mul_isUnit_left h

theorem IsStable.iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M} (h : IsStable Φ N) : ∀ d, IsStable (iterate Φ d) N
  | 0 => fun x hx => hx
  | d + 1 => fun x hx => by rw [iterate_succ_apply]; exact h _ (IsStable.iterate h d x hx)

theorem IsStable.smul {M : Type*} [AddCommGroup M] [Module R M] {ψ : R →+* R} {Ψ : M →ₛₗ[ψ] M}
    {N : Submodule R M} (h : IsStable Ψ N) (c : R) : IsStable (c • Ψ) N :=
  fun x hx => N.smul_mem c (h x hx)

theorem coe_iterate_restrict [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M}
    [Module.Free R N] [Module.Finite R N] (h : IsStable Φ N) : ∀ (d : ℕ) (x : N),
    ((iterate (restrict Φ N h) d x : N) : M) = iterate Φ d (x : M)
  | 0, _ => rfl
  | d + 1, x => by
    rw [iterate_succ_apply, iterate_succ_apply, coe_restrict_apply, coe_iterate_restrict h d x]

theorem restrict_smul_iterate [Nontrivial R] {M : Type*} [AddCommGroup M] [Module R M]
    [Module.Free R M] [Module.Finite R M] {Φ : M →ₛₗ[φ] M} {N : Submodule R M}
    [Module.Free R N] [Module.Finite R N] (h : IsStable Φ N) (d : ℕ) (c : R) :
    restrict (c • iterate Φ d) N ((h.iterate d).smul c) = c • iterate (restrict Φ N h) d := by
  ext x
  simp [coe_iterate_restrict h d x]

end PhiModule

namespace PhiModule

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M]
variable (F : FrobeniusLift K)

def twistUnit (c : ℤ) : (Robba K)ˣ :=
  (Robba.isUnit_single 0 (zpow_ne_zero (-c) (dvUnif_ne_zero (K := K)))).unit

theorem coe_twistUnit (c : ℤ) : (twistUnit (K := K) c : Robba K) = Robba.single 0 (dvUnif K ^ (-c)) := rfl

theorem ord_twistUnit (c : ℤ) : Robba.ord (twistUnit (K := K) c) = -c := by
  apply Robba.ord_eq_of_norm1_eq
  rw [coe_twistUnit, Robba.gaussNorm_single_alt, norm_zpow]

def twistIter (Φ : M →ₛₗ[F.phi] M) (s : ℚ) : M →ₛₗ[F.phi ^ s.den] M :=
  (twistUnit (K := K) s.num : Robba K) • iterate Φ s.den

def IsPure (Φ : M →ₛₗ[F.phi] M) (s : ℚ) : Prop := IsEtale (twistIter F Φ s)

variable [Module.Free (Robba K) M] [Module.Finite (Robba K) M] {F}

theorem IsPure.isPhiModule {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) : IsPhiModule Φ :=
  isPhiModule_of_iterate s.den_pos (isPhiModule_of_smul (IsEtale.isPhiModule h))

theorem deg_twistIter {Φ : M →ₛₗ[F.phi] M} (hΦ : IsPhiModule Φ) (s : ℚ) :
    deg (F.unitOrdPow s.den) (twistIter F Φ s) =
      s.den * deg F.unitOrd Φ - finrank (Robba K) M * s.num := by
  rw [twistIter, deg_smul _ (isPhiModule_iterate hΦ _) (twistUnit s.num), F.unitOrdPow_eq,
    deg_iterate F.unitOrd hΦ s.den]
  change _ + _ * Robba.ord _ = _
  rw [ord_twistUnit]
  ring

theorem IsPure.deg_eq {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) :
    (deg F.unitOrd Φ : ℚ) = s * finrank (Robba K) M := by
  have h0 := IsEtale.deg_eq_zero (F.gaussNorm_phi_pow_unit s.den) (show IsEtale _ from h)
  rw [show Robba.unitOrd (F.phi ^ s.den) (F.gaussNorm_phi_pow_unit s.den) = F.unitOrdPow s.den from rfl,
    deg_twistIter h.isPhiModule] at h0
  have hd : (s.den : ℚ) ≠ 0 := by exact_mod_cast s.den_pos.ne'
  have e : (s.den : ℚ) * deg F.unitOrd Φ = finrank (Robba K) M * s.num := by exact_mod_cast (by linarith)
  rw [← Rat.num_div_den s]
  field_simp
  linarith

theorem IsPure.le_deg {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) {N : Submodule (Robba K) M}
    (hN : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N]
    [Module.Finite (Robba K) N] :
    s * finrank (Robba K) N ≤ deg F.unitOrd (restrict Φ N hN) := by
  have hNphi := isPhiModule_restrict h.isPhiModule hN
  have hst : IsStable (twistIter F Φ s) N := (hN.iterate s.den).smul _
  have h0 := deg_restrict_nonneg_of_isEtale ((F.isGaussScaling).pow F.q_pos s.den)
    (pow_pos F.q_pos _) (F.gaussNorm_phi_pow_unit s.den) h hst
  rw [show Robba.unitOrd (F.phi ^ s.den) (F.gaussNorm_phi_pow_unit s.den) = F.unitOrdPow s.den from rfl]
    at h0
  have e : restrict (twistIter F Φ s) N hst = twistIter F (restrict Φ N hN) s :=
    restrict_smul_iterate hN s.den _
  rw [e, deg_twistIter hNphi] at h0
  have hd : (0 : ℚ) < s.den := by exact_mod_cast s.den_pos
  have h1 : (finrank (Robba K) N : ℚ) * s.num ≤ s.den * deg F.unitOrd (restrict Φ N hN) := by
    exact_mod_cast (by linarith)
  rw [← Rat.num_div_den s, div_mul_eq_mul_div, div_le_iff₀ hd]
  linarith

def degSub (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] : ℤ :=
  letI := free_of_saturated N
  letI := finite_of_saturated N
  deg v (restrict Φ N h)

theorem degSub_eq (v : UnitOrd (Robba K) F.phi) (Φ : M →ₛₗ[F.phi] M) (N : Submodule (Robba K) M)
    (h : IsStable Φ N) [Module.IsTorsionFree (Robba K) (M ⧸ N)] [Module.Free (Robba K) N]
    [Module.Finite (Robba K) N] : degSub v Φ N h = deg v (restrict Φ N h) := rfl

variable (F) in

def IsSemistable (Φ : M →ₛₗ[F.phi] M) : Prop :=
  IsPhiModule Φ ∧ ∀ (N : Submodule (Robba K) M) (h : IsStable Φ N)
    [Module.IsTorsionFree (Robba K) (M ⧸ N)],
    deg F.unitOrd Φ * (finrank (Robba K) N : ℤ) ≤ degSub F.unitOrd Φ N h * finrank (Robba K) M

theorem IsPure.isSemistable {Φ : M →ₛₗ[F.phi] M} {s : ℚ} (h : IsPure F Φ s) :
    IsSemistable F Φ := by
  refine ⟨h.isPhiModule, fun N hN _ => ?_⟩
  have := free_of_saturated N
  have := finite_of_saturated N
  rw [degSub_eq]
  have h1 := h.le_deg hN
  have h2 := h.deg_eq
  have hM : (0 : ℚ) ≤ finrank (Robba K) M := by positivity
  have key : (deg F.unitOrd Φ : ℚ) * finrank (Robba K) N ≤
      (deg F.unitOrd (restrict Φ N hN) : ℚ) * finrank (Robba K) M := by
    rw [h2]
    calc s * finrank (Robba K) M * finrank (Robba K) N
        = (s * finrank (Robba K) N) * finrank (Robba K) M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right h1 hM
  exact_mod_cast key

end PhiModule

namespace PhiModule

variable {F : FrobeniusLift K}
variable {A B : Type*} [AddCommGroup A] [Module (Robba K) A] [Module.Free (Robba K) A]
  [Module.Finite (Robba K) A] [AddCommGroup B] [Module (Robba K) B] [Module.Free (Robba K) B]
  [Module.Finite (Robba K) B]

theorem IsPure.hom_eq_zero {ΦA : A →ₛₗ[F.phi] A} {ΦB : B →ₛₗ[F.phi] B} {s t : ℚ}
    (hA : IsPure F ΦA s) (hB : IsPure F ΦB t) (hst : s < t) {f : A →ₗ[Robba K] B}
    (hf : IsEquivariant f ΦA ΦB) : f = 0 := by
  by_contra hf0

  have hK : IsStable ΦA (LinearMap.ker f) := hf.isStable_ker
  have : Module.IsTorsionFree (Robba K) (A ⧸ LinearMap.ker f) := isTorsionFree_quotient_ker f
  have := free_of_saturated (LinearMap.ker f)
  have := finite_of_saturated (LinearMap.ker f)
  have := free_quot_of_saturated (LinearMap.ker f)

  have hI : IsStable ΦB (LinearMap.range f) := hf.isStable_range
  let e : (A ⧸ LinearMap.ker f) ≃ₗ[Robba K] LinearMap.range f := f.quotKerEquivRange
  have : Module.Free (Robba K) (LinearMap.range f) := Module.Free.of_equiv e
  have : Module.Finite (Robba K) (LinearMap.range f) := Module.Finite.equiv e
  have he : ∀ x, e (quot ΦA _ hK x) = restrict ΦB _ hI (e x) := hf.quotKerEquivRange
  have hQphi : IsPhiModule (quot ΦA _ hK) := isPhiModule_quot hA.isPhiModule hK
  have hIphi : IsPhiModule (restrict ΦB _ hI) := (isPhiModule_congr e he).1 hQphi
  have hdegI : deg F.unitOrd (restrict ΦB _ hI) = deg F.unitOrd (quot ΦA _ hK) :=
    deg_congr _ e he

  have hN : IsStable ΦB (saturation (LinearMap.range f)) := hI.saturation F.phi_injective
  have := free_of_saturated (saturation (LinearMap.range f))
  have := finite_of_saturated (saturation (LinearMap.range f))
  have hNphi := isPhiModule_restrict hB.isPhiModule hN
  have hrank : finrank (Robba K) (LinearMap.range f) =
      finrank (Robba K) (saturation (LinearMap.range f)) := (finrank_saturation _).symm
  have hle : deg F.unitOrd (restrict ΦB _ hN) ≤ deg F.unitOrd (restrict ΦB _ hI) :=
    le_deg_of_le F.isGaussScaling F.q_pos F.gaussNorm_phi_unit (le_saturation _) hI hN hIphi hNphi hrank

  have h1 := hB.le_deg hN
  have hadd := deg_eq_deg_restrict_add F.unitOrd hA.isPhiModule hK
  have h2 := hA.le_deg hK
  have h3 := hA.deg_eq
  have hrk := finrank_add_finrank_quotient (LinearMap.ker f)
  have hrkI : finrank (Robba K) (LinearMap.range f) = finrank (Robba K) (A ⧸ LinearMap.ker f) :=
    e.finrank_eq.symm
  have hIne : LinearMap.range f ≠ ⊥ := fun h => hf0 (LinearMap.range_eq_bot.1 h)
  have hpos : 0 < finrank (Robba K) (LinearMap.range f) := Submodule.one_le_finrank_iff.2 hIne

  set r := finrank (Robba K) (LinearMap.range f)
  have hrQ : (r : ℚ) > 0 := by exact_mod_cast hpos
  have hle' : (deg F.unitOrd (restrict ΦB _ hN) : ℚ) ≤ deg F.unitOrd (restrict ΦB _ hI) := by
    exact_mod_cast hle
  have hadd' : (deg F.unitOrd ΦA : ℚ) = deg F.unitOrd (restrict ΦA _ hK) + deg F.unitOrd (quot ΦA _ hK) := by
    exact_mod_cast hadd
  have hdegI' : (deg F.unitOrd (restrict ΦB _ hI) : ℚ) = deg F.unitOrd (quot ΦA _ hK) := by
    exact_mod_cast hdegI
  have hrk' : (finrank (Robba K) (LinearMap.ker f) : ℚ) + finrank (Robba K) (A ⧸ LinearMap.ker f) =
      finrank (Robba K) A := by exact_mod_cast hrk
  rw [← hrank] at h1
  have hrkI' : (r : ℚ) = finrank (Robba K) (A ⧸ LinearMap.ker f) := by exact_mod_cast hrkI
  have key : t * r ≤ s * r := by
    have : s * finrank (Robba K) A - s * finrank (Robba K) (LinearMap.ker f) = s * r := by
      rw [hrkI', ← hrk']; ring
    linarith
  nlinarith

section Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

def subquotMap {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) :
    (X ⧸ inSub P X) →ₗ[Robba K] (Y ⧸ inSub Z Y) :=
  (inSub P X).mapQ (inSub Z Y) (Submodule.inclusion hXY) fun _ hx => hPZ hx

theorem subquotMap_mk {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z) (x : X) :
    subquotMap hXY hPZ (Submodule.Quotient.mk x) = Submodule.Quotient.mk (Submodule.inclusion hXY x) :=
  rfl

theorem isEquivariant_subquotMap {Φ : M →ₛₗ[F.phi] M} {P X Z Y : Submodule (Robba K) M}
    (hP : IsStable Φ P) (hX : IsStable Φ X) (hZ : IsStable Φ Z) (hY : IsStable Φ Y)
    (hXY : X ≤ Y) (hPZ : P ≤ Z) :
    IsEquivariant (subquotMap hXY hPZ) (subquot Φ P X hP hX) (subquot Φ Z Y hZ hY) := by
  intro x
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rfl

theorem subquotMap_ne_zero {P X Z Y : Submodule (Robba K) M} (hXY : X ≤ Y) (hPZ : P ≤ Z)
    (hXZ : ¬ X ≤ Z) : subquotMap hXY hPZ ≠ 0 := by
  intro h0
  apply hXZ
  intro x hx
  have := LinearMap.congr_fun h0 (Submodule.Quotient.mk ⟨x, hx⟩)
  rw [subquotMap_mk, LinearMap.zero_apply, Submodule.Quotient.mk_eq_zero] at this
  exact this

variable (F) in

def IsPureSubquot (Φ : M →ₛₗ[F.phi] M) (N N' : Submodule (Robba K) M) (h : IsStable Φ N)
    (h' : IsStable Φ N') [Module.IsTorsionFree (Robba K) (M ⧸ N)]
    [Module.IsTorsionFree (Robba K) (M ⧸ N')] (s : ℚ) : Prop :=
  letI := free_subquot (N := N) (N' := N')
  letI := finite_subquot (N := N) (N' := N')
  IsPure F (subquot Φ N N' h h') s

theorem subquotMap_eq_zero {Φ : M →ₛₗ[F.phi] M} {P X Z Y : Submodule (Robba K) M}
    (hP : IsStable Φ P) (hX : IsStable Φ X) (hZ : IsStable Φ Z) (hY : IsStable Φ Y)
    [Module.IsTorsionFree (Robba K) (M ⧸ P)] [Module.IsTorsionFree (Robba K) (M ⧸ X)]
    [Module.IsTorsionFree (Robba K) (M ⧸ Z)] [Module.IsTorsionFree (Robba K) (M ⧸ Y)]
    (hXY : X ≤ Y) (hPZ : P ≤ Z) {s t : ℚ} (hs : IsPureSubquot F Φ P X hP hX s)
    (ht : IsPureSubquot F Φ Z Y hZ hY t) (hst : s < t) : subquotMap hXY hPZ = 0 := by
  have := free_subquot (N := P) (N' := X)
  have := finite_subquot (N := P) (N' := X)
  have := free_subquot (N := Z) (N' := Y)
  have := finite_subquot (N := Z) (N' := Y)
  exact IsPure.hom_eq_zero hs ht hst (isEquivariant_subquotMap hP hX hZ hY hXY hPZ)

end Subquotients

variable {M : Type*} [AddCommGroup M] [Module (Robba K) M] [Module.Free (Robba K) M]
  [Module.Finite (Robba K) M]

variable (F) in

structure SlopeFiltration (Φ : M →ₛₗ[F.phi] M) where

  length : ℕ

  N : ℕ → Submodule (Robba K) M

  slope : ℕ → ℚ
  N_zero : N 0 = ⊥
  N_of_le : ∀ i, length ≤ i → N i = ⊤
  lt_succ : ∀ i, i < length → N i < N (i + 1)
  stable : ∀ i, IsStable Φ (N i)
  saturated : ∀ i, Module.IsTorsionFree (Robba K) (M ⧸ N i)
  pure : ∀ i, i < length →
    haveI := saturated i
    haveI := saturated (i + 1)
    IsPureSubquot F Φ (N i) (N (i + 1)) (stable i) (stable (i + 1)) (slope i)
  slope_lt : ∀ i j, i < j → j < length → slope i < slope j

namespace SlopeFiltration

variable {Φ : M →ₛₗ[F.phi] M}

theorem N_mono (S : SlopeFiltration F Φ) : Monotone S.N := by
  refine monotone_nat_of_le_succ fun i => ?_
  by_cases hi : i < S.length
  · exact (S.lt_succ i hi).le
  · rw [S.N_of_le i (not_lt.1 hi), S.N_of_le (i + 1) (by omega)]

theorem lt_length_of_ne_top (S : SlopeFiltration F Φ) {i : ℕ} (h : S.N i ≠ ⊤) : i < S.length := by
  by_contra hi
  exact h (S.N_of_le i (not_lt.1 hi))

theorem step (S₁ S₂ : SlopeFiltration F Φ) {i : ℕ} (hi₁ : i < S₁.length) (hi₂ : i < S₂.length)
    (hN : S₁.N i = S₂.N i) (hs : S₁.slope i ≤ S₂.slope i) :
    S₁.N (i + 1) ≤ S₂.N (i + 1) ∧ S₂.slope i ≤ S₁.slope i := by
  classical
  have := S₁.saturated i
  have := S₁.saturated (i + 1)
  constructor
  · by_contra hcon
    have hex : ∃ j, S₁.N (i + 1) ≤ S₂.N j := ⟨S₂.length, by rw [S₂.N_of_le _ le_rfl]; exact le_top⟩
    set j := Nat.find hex
    have hj : S₁.N (i + 1) ≤ S₂.N j := Nat.find_spec hex
    have hj1 : i + 1 < j := by
      by_contra hle
      exact hcon (hj.trans (S₂.N_mono (not_lt.1 hle)))
    obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    have hkmin : ¬ S₁.N (i + 1) ≤ S₂.N k := Nat.find_min hex (by omega)
    have hkl : k < S₂.length := S₂.lt_length_of_ne_top fun htop => hkmin (htop ▸ le_top)
    have := S₂.saturated k
    have := S₂.saturated (k + 1)
    have hPZ : S₁.N i ≤ S₂.N k := hN ▸ S₂.N_mono (by omega)
    have hXY : S₁.N (i + 1) ≤ S₂.N (k + 1) := hk ▸ hj
    have hlt : S₁.slope i < S₂.slope k := lt_of_le_of_lt hs (S₂.slope_lt i k (by omega) hkl)
    exact subquotMap_ne_zero hXY hPZ hkmin (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
      (S₂.stable k) (S₂.stable (k + 1)) hXY hPZ (S₁.pure i hi₁) (S₂.pure k hkl) hlt)
  · by_contra hcon
    rw [not_le] at hcon

    have hle : S₁.N (i + 1) ≤ S₂.N (i + 1) := by
      by_contra hcon'
      have hex : ∃ j, S₁.N (i + 1) ≤ S₂.N j :=
        ⟨S₂.length, by rw [S₂.N_of_le _ le_rfl]; exact le_top⟩
      set j := Nat.find hex
      have hj : S₁.N (i + 1) ≤ S₂.N j := Nat.find_spec hex
      have hj1 : i + 1 < j := by
        by_contra hle
        exact hcon' (hj.trans (S₂.N_mono (not_lt.1 hle)))
      obtain ⟨k, hk⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
      have hkmin : ¬ S₁.N (i + 1) ≤ S₂.N k := Nat.find_min hex (by omega)
      have hkl : k < S₂.length := S₂.lt_length_of_ne_top fun htop => hkmin (htop ▸ le_top)
      have := S₂.saturated k
      have := S₂.saturated (k + 1)
      have hPZ : S₁.N i ≤ S₂.N k := hN ▸ S₂.N_mono (by omega)
      have hXY : S₁.N (i + 1) ≤ S₂.N (k + 1) := hk ▸ hj
      have hlt : S₁.slope i < S₂.slope k := lt_of_le_of_lt hs (S₂.slope_lt i k (by omega) hkl)
      exact subquotMap_ne_zero hXY hPZ hkmin (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
        (S₂.stable k) (S₂.stable (k + 1)) hXY hPZ (S₁.pure i hi₁) (S₂.pure k hkl) hlt)
    have := S₂.saturated i
    have := S₂.saturated (i + 1)
    have hnot : ¬ S₁.N (i + 1) ≤ S₂.N i := fun h' =>
      not_le_of_gt (S₁.lt_succ i hi₁) (by rw [hN]; exact h')
    exact subquotMap_ne_zero hle hN.le hnot (subquotMap_eq_zero (S₁.stable i) (S₁.stable (i + 1))
      (S₂.stable i) (S₂.stable (i + 1)) hle hN.le (S₁.pure i hi₁) (S₂.pure i hi₂) hcon)

theorem unique (S₁ S₂ : SlopeFiltration F Φ) :
    S₁.length = S₂.length ∧ S₁.N = S₂.N ∧ ∀ i < S₁.length, S₁.slope i = S₂.slope i := by

  have hN : ∀ i, S₁.N i = S₂.N i := by
    intro i
    induction i with
    | zero => rw [S₁.N_zero, S₂.N_zero]
    | succ i ih =>
      by_cases h₁ : i < S₁.length
      · by_cases h₂ : i < S₂.length
        · rcases le_total (S₁.slope i) (S₂.slope i) with hs | hs
          · obtain ⟨hle, hs'⟩ := step S₁ S₂ h₁ h₂ ih hs
            exact le_antisymm hle (step S₂ S₁ h₂ h₁ ih.symm hs').1
          · obtain ⟨hle, hs'⟩ := step S₂ S₁ h₂ h₁ ih.symm hs
            exact le_antisymm (step S₁ S₂ h₁ h₂ ih hs').1 hle
        · exfalso
          have h2 := S₂.N_of_le i (not_lt.1 h₂)
          have := S₁.lt_succ i h₁
          rw [ih, h2] at this
          exact (this.trans_le le_top).false
      · have h1 := S₁.N_of_le i (not_lt.1 h₁)
        by_cases h₂ : i < S₂.length
        · exfalso
          have := S₂.lt_succ i h₂
          rw [← ih, h1] at this
          exact (this.trans_le le_top).false
        · rw [S₁.N_of_le (i + 1) (by omega), S₂.N_of_le (i + 1) (by omega)]

  have hlen : S₁.length = S₂.length := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := S₂.lt_succ S₁.length h
      rw [← hN, ← hN, S₁.N_of_le _ le_rfl, S₁.N_of_le _ (by omega)] at this
      exact this.false
    · have := S₁.lt_succ S₂.length h
      rw [hN, hN, S₂.N_of_le _ le_rfl, S₂.N_of_le _ (by omega)] at this
      exact this.false
  refine ⟨hlen, funext hN, fun i hi => ?_⟩
  have hi₂ : i < S₂.length := hlen ▸ hi
  rcases le_total (S₁.slope i) (S₂.slope i) with hs | hs
  · exact le_antisymm hs (step S₁ S₂ hi hi₂ (hN i) hs).2
  · exact le_antisymm (step S₂ S₁ hi₂ hi (hN i).symm hs).2 hs

end SlopeFiltration

end PhiModule

end GroundTheory.PAdicHodge
