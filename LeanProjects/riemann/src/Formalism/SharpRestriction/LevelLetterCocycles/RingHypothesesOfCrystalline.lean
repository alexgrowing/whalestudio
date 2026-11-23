import Formalism.SharpRestriction.LevelLetterCocycles.ExpRules
import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.SaturationUnramifiedOfRingCondition
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusPowUniformizerFactorisation

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase IsTrunc InI IsSer IsRem eY PolesFin)
open Formalism.MainNotions.LiftingTheory (qp pk CaseA)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

section Letters

variable {T : LocLat G Qp LL O}

theorem φA_letE' (i : ZMod n) : W.φA (letE i : LetA O n) = letE (i + 1) := by
  have := Formalism.MainNotions.WachCoordinates.Br.φA_letE W (i + 1)
  rwa [add_sub_cancel_right] at this

theorem dl_φ {i : ZMod n} {x : W.DD T} (h : DL W T i x) : DL W T (i + 1) (W.φD T x) := by
  obtain ⟨h1, h2⟩ := h
  have e1 : W.φD T x = (letE (i + 1) : LetA O n) • W.φD T x := by
    conv_lhs => rw [← h1]
    rw [Formalism.MainNotions.WachCoordinates.Br.φD_smulA, φA_letE']
  refine ⟨?_, fun δ hδ => ?_⟩
  · rw [e1, smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self]
  · rw [← W.φγ_comm, h2 δ hδ]

theorem dl_φpow {i : ZMod n} {x : W.DD T} (h : DL W T i x) (j : ℕ) :
    DL W T (i + (j : ZMod n)) (((W.φD T) ^ j) x) := by
  induction j with
  | zero => simpa using h
  | succ j ih =>
    have e : i + ((j + 1 : ℕ) : ZMod n) = (i + (j : ZMod n)) + 1 := by push_cast; ring
    rw [e, pow_succ', Module.End.mul_apply]
    exact dl_φ W ih

theorem dl_add {i : ZMod n} {x y : W.DD T} (hx : DL W T i x) (hy : DL W T i y) : DL W T i (x + y) :=
  ⟨by rw [smul_add, hx.1, hy.1], fun δ hδ => by rw [map_add, hx.2 δ hδ, hy.2 δ hδ]⟩

theorem dl_zero (i : ZMod n) : DL W T i (0 : W.DD T) :=
  ⟨smul_zero _, fun δ _ => map_zero _⟩

theorem dl_neg {i : ZMod n} {x : W.DD T} (hx : DL W T i x) : DL W T i (-x) :=
  ⟨by rw [smul_neg, hx.1], fun δ hδ => by rw [map_neg, hx.2 δ hδ]⟩

theorem dl_sub {i : ZMod n} {x y : W.DD T} (hx : DL W T i x) (hy : DL W T i y) : DL W T i (x - y) := by
  rw [sub_eq_add_neg]; exact dl_add W hx (dl_neg W hy)

theorem dl_smulA {i : ZMod n} {a : LetA O n} (ha : a ∈ W.AΔ) {x : W.DD T} (hx : DL W T i x) :
    DL W T i (a • x) :=
  ⟨by rw [smul_smul, mul_comm, ← smul_smul, hx.1],
    fun δ hδ => by rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, ha δ hδ, hx.2 δ hδ]⟩

theorem dl_smulO {i : ZMod n} (c : O) {x : W.DD T} (hx : DL W T i x) : DL W T i (c • x) := by
  rw [← algebraMap_smul (LetA O n) c x]
  exact dl_smulA W (W.AΔ.algebraMap_mem c) hx

theorem dl_sum {i : ZMod n} {ι : Type} (s : Finset ι) (f : ι → W.DD T) (h : ∀ k ∈ s, DL W T i (f k)) :
    DL W T i (∑ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simpa using dl_zero W (T := T) i
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact dl_add W (h a (Finset.mem_insert_self a s)) (ih fun k hk => h k (Finset.mem_insert_of_mem hk))

theorem φpow_mem_pullJ {i : ZMod n} {x : W.DD T} (hx : x ∈ W.N T) (hd : DL W T i x) (j : ℕ) :
    ((W.φD T) ^ j) x ∈ pullJ W T i j :=
  Submodule.subset_span ⟨x, ⟨hx, hd⟩, rfl⟩

theorem γD_φpow (δ : W.Gam) (x : W.DD T) (j : ℕ) :
    W.γD T δ (((W.φD T) ^ j) x) = ((W.φD T) ^ j) (W.γD T δ x) := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow_succ', Module.End.mul_apply, Module.End.mul_apply, ← W.φγ_comm, ih]

theorem γD_mem_pullJ {i : ZMod n} {j : ℕ} {δ : W.Gam} (hδ : δ ∈ W.DelF) {p : W.DD T}
    (hp : p ∈ pullJ W T i j) : W.γD T δ p ∈ pullJ W T i j := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hy, hd⟩, rfl⟩ := hx
    rw [γD_φpow, hd.2 δ hδ]
    exact φpow_mem_pullJ W hy hd j
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA]; exact Submodule.smul_mem _ _ hx

end Letters

section At0

variable (hz : PowerSeries.constantCoeff W.π₀₁ = 0)
include hz

theorem hasSubst_π₀ : PowerSeries.HasSubst W.π₀₁ := PowerSeries.HasSubst.of_constantCoeff_zero hz

theorem evaluation_add (f g : PowerSeries O) : at0 W (f + g) = at0 W f + at0 W g := by
  funext j; simp only [at0, Pi.add_apply]; exact PowerSeries.subst_add (hasSubst_π₀ W hz) f g

theorem evalZero_mul (f g : PowerSeries O) : at0 W (f * g) = at0 W f * at0 W g := by
  funext j; simp only [at0, Pi.mul_apply]; exact PowerSeries.subst_mul (hasSubst_π₀ W hz) f g

theorem evalZero_X_eq_pi0 : at0 W PowerSeries.X = W.π₀ := by
  funext j; simp only [at0]; exact PowerSeries.subst_X (hasSubst_π₀ W hz)

omit hz in
theorem evalZero_C (c : O) : at0 W (PowerSeries.C c) = algebraMap O (LetA O n) c := by
  funext j; simp only [at0]; rw [PowerSeries.subst_C]; rfl

theorem evalZero_sub (f g : PowerSeries O) : at0 W (f - g) = at0 W f - at0 W g := by
  rw [eq_sub_iff_add_eq, ← evaluation_add W hz, sub_add_cancel]

theorem evalZero_zero : at0 W (0 : PowerSeries O) = 0 := by
  have := evalZero_C W (0 : O); rwa [map_zero, map_zero] at this

theorem evalZero_sum {ι : Type} (s : Finset ι) (f : ι → PowerSeries O) :
    at0 W (∑ k ∈ s, f k) = ∑ k ∈ s, at0 W (f k) := by
  induction s using Finset.induction_on with
  | empty => simpa using evalZero_zero W hz
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, evaluation_add W hz, ih]

theorem evalZero_pow (f : PowerSeries O) (k : ℕ) : at0 W (f ^ k) = at0 W f ^ k := by
  induction k with
  | zero => have := evalZero_C W (1 : O); rw [map_one, map_one] at this; rw [pow_zero, pow_zero]; exact this
  | succ k ih => rw [pow_succ, evalZero_mul W hz, ih, pow_succ]

end At0

section Avg

variable {T : LocLat G Qp LL O}

theorem delF_mul {a b : W.Gam} (ha : a ∈ W.DelF) (hb : b ∈ W.DelF) : a * b ∈ W.DelF := by
  obtain ⟨k, hk, hka⟩ := (W.DelF_def a).1 ha
  obtain ⟨m, hm, hmb⟩ := (W.DelF_def b).1 hb
  refine (W.DelF_def _).2 ⟨k * m, Nat.mul_pos hk hm, ?_⟩
  rw [mul_pow, pow_mul, hka, one_pow, one_mul, mul_comm, pow_mul, hmb, one_pow]

theorem delF_inv {a : W.Gam} (ha : a ∈ W.DelF) : a⁻¹ ∈ W.DelF := by
  obtain ⟨k, hk, hka⟩ := (W.DelF_def a).1 ha
  exact (W.DelF_def _).2 ⟨k, hk, by rw [inv_pow, hka, inv_one]⟩

def avD (x : W.DD T) : W.DD T := ∑ δ ∈ W.DelF, W.γD T δ x

def avA (a : LetA O n) : LetA O n := ∑ δ ∈ W.DelF, W.γA δ a

theorem γA_mul (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext k
  simp [LocWach.γA, letγ, map_mul]

theorem sum_delF_shift {M : Type} [AddCommMonoid M] (f : W.Gam → M) {δ' : W.Gam} (hδ' : δ' ∈ W.DelF) :
    ∑ δ ∈ W.DelF, f (δ' * δ) = ∑ δ ∈ W.DelF, f δ := by
  refine Finset.sum_nbij' (fun δ => δ' * δ) (fun δ => δ'⁻¹ * δ) (fun δ hδ => delF_mul W hδ' hδ)
    (fun δ hδ => delF_mul W (delF_inv W hδ') hδ) (fun δ _ => by simp) (fun δ _ => by simp) (fun δ _ => rfl)

theorem avA_mem (a : LetA O n) : avA W a ∈ W.AΔ := by
  intro δ' hδ'
  simp only [avA, map_sum]
  simp_rw [← γA_mul]
  exact sum_delF_shift W (fun δ => W.γA δ a) hδ'

theorem avD_inv (x : W.DD T) : ∀ δ' ∈ W.DelF, W.γD T δ' (avD W x) = avD W x := by
  intro δ' hδ'
  simp only [avD, map_sum]
  simp_rw [← W.γD_mul]
  exact sum_delF_shift W (fun δ => W.γD T δ x) hδ'

theorem avD_smul (a : LetA O n) {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    avD W (a • x) = avA W a • x := by
  simp only [avD, avA, Finset.sum_smul]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, hx δ hδ]

theorem avD_add (x y : W.DD T) : avD W (x + y) = avD W x + avD W y := by
  simp only [avD, map_add, Finset.sum_add_distrib]

theorem avD_smulΔ {a : LetA O n} (ha : a ∈ W.AΔ) (x : W.DD T) : avD W (a • x) = a • avD W x := by
  simp only [avD, Finset.smul_sum]
  refine Finset.sum_congr rfl fun δ hδ => ?_
  rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, ha δ hδ]

theorem avD_of_inv {x : W.DD T} (hx : ∀ δ ∈ W.DelF, W.γD T δ x = x) :
    avD W x = (W.DelF.card : O) • x := by
  simp only [avD]
  rw [Finset.sum_congr rfl fun δ hδ => hx δ hδ, Finset.sum_const, ← Nat.cast_smul_eq_nsmul O]

theorem avD_mem_pullJ {i : ZMod n} {j : ℕ} {p : W.DD T} (hp : p ∈ pullJ W T i j) :
    avD W p ∈ pullJ W T i j :=
  Submodule.sum_mem _ fun δ hδ => γD_mem_pullJ W hδ hp

end Avg

section Conv

variable {M : Type} [AddCommGroup M] [Module LL M]

theorem conv_supp_fin (f : PowerSeries LL) {d : ℤ → M} {m : ℤ} (hd : ∀ k < m, d k = 0) (k : ℤ) :
    (Function.support fun j : ℕ => PowerSeries.coeff j f • d (k - j)).Finite := by
  refine (Finset.range ((k - m).toNat + 1)).finite_toSet.subset fun j hj => ?_
  simp only [Function.mem_support] at hj
  simp only [Finset.coe_range, Set.mem_Iio]
  by_contra h
  apply hj
  have h1 : k - m ≤ ((k - m).toNat : ℤ) := Int.self_le_toNat _
  rw [hd _ (by omega), smul_zero]

theorem conv_sub (f : PowerSeries LL) {d d' : ℤ → M} {m m' : ℤ} (hd : ∀ k < m, d k = 0)
    (hd' : ∀ k < m', d' k = 0) (k : ℤ) : conv f (d - d') k = conv f d k - conv f d' k := by
  simp only [conv, Pi.sub_apply, smul_sub]
  exact finsum_sub_distrib (conv_supp_fin f hd k) (conv_supp_fin f hd' k)

theorem conv_one (d : ℤ → M) (k : ℤ) : conv (1 : PowerSeries LL) d k = d k := by
  simp only [conv]
  rw [finsum_eq_single _ 0 (fun j hj => by simp [PowerSeries.coeff_one, hj])]
  simp

theorem conv_delta (f : PowerSeries LL) (C : M) (r : ℤ) :
    conv f (fun k => if k = 0 then C else 0) r = if r < 0 then 0 else PowerSeries.coeff r.toNat f • C := by
  simp only [conv]
  split_ifs with hr
  · refine finsum_eq_zero_of_forall_eq_zero fun j => ?_
    rw [if_neg (by omega), smul_zero]
  · rw [finsum_eq_single _ r.toNat (fun j hj => by rw [if_neg (by omega), smul_zero])]
    rw [if_pos (by omega)]

theorem conv_cancel (L U : PowerSeries LL) (Kk Xx : ℕ) (hL : L = PowerSeries.X ^ Kk * U)
    (hU : PowerSeries.constantCoeff U ≠ 0) {e : ℤ → M} {m : ℤ} (he : ∀ k < m, e k = 0)
    (hc : ∀ r : ℤ, r < (Kk : ℤ) + Xx → conv L e r = 0) : ∀ s : ℤ, s < Xx → e s = 0 := by
  by_contra hne
  push Not at hne
  obtain ⟨s, hs, hes⟩ := hne
  have hsm : m ≤ s := by
    by_contra h
    exact hes (he s (by omega))
  let P : ℕ → Prop := fun t => e (m + t) ≠ 0 ∧ m + t < Xx
  have hP : ∃ t, P t := ⟨(s - m).toNat, by
    have h1 : m + ((s - m).toNat : ℤ) = s := by omega
    show e (m + ((s - m).toNat : ℤ)) ≠ 0 ∧ m + ((s - m).toNat : ℤ) < Xx
    rw [h1]; exact ⟨hes, hs⟩⟩
  have ht₀ : P (Nat.find hP) := Nat.find_spec hP
  have hmin : ∀ t < Nat.find hP, ¬ P t := fun t ht => Nat.find_min hP ht
  have hcs := hc (m + (Nat.find hP : ℤ) + Kk) (by have := ht₀.2; omega)
  simp only [conv] at hcs
  rw [finsum_eq_single _ Kk] at hcs
  · rw [hL, PowerSeries.coeff_X_pow_mul', if_pos le_rfl, Nat.sub_self,
      PowerSeries.coeff_zero_eq_constantCoeff_apply] at hcs
    have h2 : m + (Nat.find hP : ℤ) + Kk - (Kk : ℤ) = m + (Nat.find hP : ℤ) := by ring
    rw [h2] at hcs
    exact ht₀.1 ((smul_eq_zero.1 hcs).resolve_left hU)
  · intro j hj
    rcases lt_or_gt_of_ne hj with hlt | hgt
    · rw [hL, PowerSeries.coeff_X_pow_mul', if_neg (by omega), zero_smul]
    · by_cases hlow : m + (Nat.find hP : ℤ) + Kk - j < m
      · rw [he _ hlow, smul_zero]
      · have ht : (m + (Nat.find hP : ℤ) + Kk - j - m).toNat < Nat.find hP := by omega
        have h3 := hmin _ ht
        have h4 : m + ((m + (Nat.find hP : ℤ) + Kk - j - m).toNat : ℤ) = m + (Nat.find hP : ℤ) + Kk - j := by
          omega
        have h5 : e (m + (Nat.find hP : ℤ) + Kk - j) = 0 := by
          by_contra hne0
          exact h3 ⟨by rw [h4]; exact hne0, by rw [h4]; have := ht₀.2; omega⟩
        rw [h5, smul_zero]

end Conv

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct Module
open Formalism.MainNotions.CrystallineLiftingInputs (DL InPN pullJ fMX TCase IsTrunc InI IsSer IsRem eY PolesFin TTool2 THor)
open Formalism.MainNotions.LiftingTheory (qp pk CaseA)

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

structure R9 (T : LocLat G Qp LL O) : Prop where
  hz : PowerSeries.constantCoeff W.π₀₁ = 0
  πΔ : W.π₀ ∈ W.AΔ
  πsub : ∀ a ∈ W.AΔ, ∃ f : ZMod n → PowerSeries O, ∀ c, a c = PowerSeries.subst W.π₀₁ (f c)
  qq : ∃ w : (LetA O n)ˣ, W.q = (w : LetA O n) * qp W
  φπ : ∃ w : (LetA O n)ˣ, W.φA W.π₀ = (w : LetA O n) * W.π₀ * qp W ^ (PD.p - 1)
  πinj : ∀ y : W.DD T, W.π₀ • y = 0 → y = 0
  γπ : ∀ x ∈ W.NΔ T, ∃ x' ∈ W.NΔ T, W.γ T x - x = W.π₀ • x'

theorem eat_qp :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qp W := by
  funext c
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qp, LocWach.π₀]

theorem ring_hypotheses_of_crystalline (hA : CaseA W) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : R9 W T := by
  have hfin1 : finrank K₀ K = 1 := Formalism.MainNotions.LiftingTheory.gen_finrank_one hA.1
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, hmod⟩ := h9' hfin1
  obtain ⟨hπΔ, hsub, ⟨w, hw⟩, -, ⟨wq, hwq⟩, ⟨wφ, hwφ⟩, -⟩ := hring
  have hs' : 1 ≤ PD.p - 1 := by have := PD.hp.two_le; omega
  have hz : PowerSeries.constantCoeff W.π₀₁ = 0 := by
    have h1 := congrFun hw 0
    simp only [LocWach.π₀, Pi.mul_apply, Pi.pow_apply, letπ] at h1
    rw [h1, map_mul, map_pow, PowerSeries.constantCoeff_X, zero_pow (by omega), mul_zero]
  have hπu : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
    rw [hw, map_mul, map_pow]
    exact ((w.isUnit.map _)).mul (W.EE_π.pow _)
  refine ⟨hz, hπΔ, fun a ha => (hsub a ha).exists, ⟨wq, by rw [hwq, eat_qp]⟩,
    ⟨wφ, by rw [hwφ, eat_qp]⟩, fun y hy => ?_, hmod.2⟩
  rw [← algebraMap_smul W.EE W.π₀ y] at hy
  obtain ⟨u, hu⟩ := hπu
  have := congrArg (fun z => (↑u⁻¹ : W.EE) • z) hy
  simp only [smul_zero, ← hu, smul_smul, Units.inv_mul, one_smul] at this
  exact this

section Trunc

variable {W} {T : LocLat G Qp LL O} (hR9 : R9 W T)
include hR9

theorem inI_of {i : ZMod n} {x : W.DD T} (hx : x ∈ W.N T) (hd : DL W T i x) : InI W T i x := by
  refine ⟨hd, ⟨0, 0, by simpa using hx⟩, ?_⟩
  obtain ⟨x', hx', h⟩ := hR9.γπ x ⟨hx, hd.2⟩
  exact ⟨x', hx'.1, hx'.2, by rw [pow_one]; exact h⟩

omit hR9 in
theorem φpow_π₀ (hR9 : R9 W T) (j : ℕ) : ∃ h : LetA O n, (W.φA ^ j) W.π₀ = W.π₀ * h := by
  induction j with
  | zero => exact ⟨1, by simp⟩
  | succ j ih =>
    obtain ⟨h, hh⟩ := ih
    obtain ⟨w, hw⟩ := hR9.φπ
    refine ⟨(W.φA ^ j) (w : LetA O n) * h * ((W.φA ^ j) (qp W)) ^ (PD.p - 1), ?_⟩
    rw [pow_succ, AlgHom.mul_apply, hw, map_mul, map_mul, map_pow, hh]
    ring

theorem trunc_dl (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0) {i : ZMod n} {j X σ : ℕ} {w z : W.DD T}
    (hw : InI W T i w) (ht : IsTrunc W T i j 1 X σ w z) : DL W T (i + (j : ZMod n)) z := by
  obtain ⟨c, r', s, hser, hrs, rfl⟩ := ht
  have hr : ∀ y, r' y ∈ W.AΔ := by
    intro y
    obtain ⟨⟨a, ha⟩, -⟩ := (hrs y).1
    rw [ha]
    exact Subalgebra.sum_mem _ fun k _ => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
      (Subalgebra.pow_mem _ hR9.πΔ _)
  have hs : ∀ y, s y ∈ W.AΔ := by
    intro y
    refine Formalism.MainNotions.UnusedSlot80.SatW.mem_AΔ_of_p_pow W hO (eY PD.p y) ?_
    rw [(hrs y).2]
    exact Subalgebra.mul_mem _ (Subalgebra.pow_mem _ (Subalgebra.natCast_mem _ _) _) (hr y)
  exact dl_sub W (dl_smulO W _ (dl_φpow W hw.1 j))
    (dl_sum W _ _ fun y _ => dl_smulA W (hs y) (dl_φpow W (hser.2.1 y).1 j))

omit hR9 in
theorem smulO_eq (c : O) (x : W.DD T) : c • x = (algebraMap O (LetA O n) c) • x :=
  (algebraMap_smul (LetA O n) c x).symm

theorem trunc_split {i : ZMod n} {j X σ : ℕ} {w z : W.DD T} (ht : IsTrunc W T i j 1 X σ w z) :
    ∃ (E : ℕ) (x' : W.DD T), x' ∈ pullJ W T i j ∧
      ((PD.p : ℕ) : O) ^ E • (((PD.p : ℕ) : O) ^ σ • ((W.φD T) ^ j) w - z) = W.π₀ • x' := by
  obtain ⟨c, r', s, hser, hrs, rfl⟩ := ht
  have hdiv : ∀ y, ∃ r'' : LetA O n, r' y • ((W.φD T) ^ j) (c y) = W.π₀ • (r'' • ((W.φD T) ^ j) (c y)) := by
    intro y
    rcases Nat.eq_zero_or_pos y with rfl | hy
    · refine ⟨0, ?_⟩
      rw [hser.1, map_zero, smul_zero, smul_zero, smul_zero]
    · obtain ⟨-, g, hg⟩ := (hrs y).1
      obtain ⟨h, hh⟩ := φpow_π₀ hR9 j
      refine ⟨W.π₀ ^ (y - 1) * h ^ y - qp W ^ X * g, ?_⟩
      rw [smul_smul]
      congr 1
      have e1 : r' y = (W.φA ^ j) W.π₀ ^ y - fMX W 1 X * g := by rw [← hg]; ring
      obtain ⟨y', rfl⟩ : ∃ y', y = y' + 1 := ⟨y - 1, by omega⟩
      rw [e1, hh, Formalism.MainNotions.CrystallineLiftingInputs.fMX, Nat.add_sub_cancel, pow_one]
      ring
  choose r'' hr'' using hdiv
  set N := max 1 X + 1
  refine ⟨∑ y ∈ Finset.range N, eY PD.p y,
    ∑ y ∈ Finset.range N, (((PD.p : ℕ) : LetA O n) ^ (∑ y ∈ Finset.range N, eY PD.p y - eY PD.p y) *
      ((PD.p : ℕ) : LetA O n) ^ σ * r'' y) • ((W.φD T) ^ j) (c y), ?_, ?_⟩
  · exact Submodule.sum_mem _ fun y _ => Submodule.smul_mem _ _ (φpow_mem_pullJ W (hser.2.1 y).2 (hser.2.1 y).1 j)
  · rw [sub_sub_cancel, Finset.smul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hle : eY PD.p y ≤ ∑ y ∈ Finset.range N, eY PD.p y :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) hy
    rw [smulO_eq, smul_smul, smul_smul, map_pow, map_natCast]
    have e2 : ((PD.p : ℕ) : LetA O n) ^ (∑ y ∈ Finset.range N, eY PD.p y) * s y =
        ((PD.p : ℕ) : LetA O n) ^ (∑ y ∈ Finset.range N, eY PD.p y - eY PD.p y) *
          (((PD.p : ℕ) : LetA O n) ^ σ * r' y) := by
      rw [← (hrs y).2, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hle]
    rw [e2, ← smul_smul, ← smul_smul, hr'' y, smul_smul, smul_smul, smul_smul]
    congr 1
    ring

theorem dl_of_π₀ {i : ZMod n} {x' y : W.DD T} (hy : DL W T i y) (h : y = W.π₀ • x') : DL W T i x' := by
  refine ⟨?_, fun δ hδ => ?_⟩
  · refine sub_eq_zero.1 (hR9.πinj _ ?_)
    rw [smul_sub, smul_comm, ← h, hy.1, h, sub_self]
  · refine sub_eq_zero.1 (hR9.πinj _ ?_)
    rw [smul_sub, ← hR9.πΔ δ hδ, ← Formalism.MainNotions.WachCoordinates.Br.γD_smulA, ← h, hy.2 δ hδ, h, hR9.πΔ δ hδ, sub_self]

end Trunc

theorem p_ne_zero (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have hv := W.v_l
  rw [← map_natCast (algebraMap O LL), h, map_zero, AddValuation.map_zero] at hv
  exact WithTop.top_ne_one hv

section Const

variable {W} {T : LocLat G Qp LL O}

theorem const_coord [IsDomain O] (hR9 : R9 W T) (hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0)
    {i : ZMod n} {j X σ r : ℕ} {e : Fin r → W.DD T}
    (hU : ∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
      ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k))
    (he1 : ∀ k, e k ∈ W.N T ∧ DL W T i (e k)) {k : Fin r} {zk : W.DD T} (hI : InI W T i (e k))
    (ht : IsTrunc W T i j 1 X σ (e k) zk) (FinalFormK : Fin r → PowerSeries O)
    (hZk : zk = ∑ m, at0 W (FinalFormK m) • ((W.φD T) ^ j) (e m)) (hzJ : zk ∈ pullJ W T i j) :
    ∀ m, PowerSeries.constantCoeff (FinalFormK m) = if m = k then ((PD.p : ℕ) : O) ^ σ else 0 := by
  set vv : Fin r → W.DD T := fun m => ((W.φD T) ^ j) (e m) with hvv
  obtain ⟨E, x', hx'J, hx'⟩ := trunc_split hR9 ht
  have hyD : DL W T (i + (j : ZMod n)) (((PD.p : ℕ) : O) ^ E • (((PD.p : ℕ) : O) ^ σ • vv k - zk)) :=
    dl_smulO W _ (dl_sub W (dl_smulO W _ (dl_φpow W (he1 k).2 j)) (trunc_dl hR9 hO hI ht))
  have hyJ : ((PD.p : ℕ) : O) ^ E • (((PD.p : ℕ) : O) ^ σ • vv k - zk) ∈ pullJ W T i j :=
    Submodule.smul_of_tower_mem _ _ (Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _
      (φpow_mem_pullJ W (he1 k).1 (he1 k).2 j)) hzJ)
  have hx'D : DL W T (i + (j : ZMod n)) x' := dl_of_π₀ hR9 hyD hx'
  obtain ⟨b, hb⟩ := (hU x' hx'J hx'D).exists
  have hs : ∑ m, (algebraMap O (LetA O n) (if m = k then ((PD.p : ℕ) : O) ^ σ else 0)) • vv m =
      ((PD.p : ℕ) : O) ^ σ • vv k := by
    rw [Finset.sum_eq_single k (fun m _ hm => by rw [if_neg hm, map_zero, zero_smul]) (by simp),
      if_pos rfl, algebraMap_smul]
  have e1 : ((PD.p : ℕ) : O) ^ E • (((PD.p : ℕ) : O) ^ σ • vv k - zk) =
      ∑ m, at0 W (PowerSeries.C (((PD.p : ℕ) : O) ^ E) *
        (PowerSeries.C (if m = k then ((PD.p : ℕ) : O) ^ σ else 0) - FinalFormK m)) • vv m := by
    rw [hZk, ← hs, ← Finset.sum_sub_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← sub_smul, smulO_eq, smul_smul, evalZero_mul W hR9.hz, evalZero_sub W hR9.hz, evalZero_C, evalZero_C]
  have e2 : ((PD.p : ℕ) : O) ^ E • (((PD.p : ℕ) : O) ^ σ • vv k - zk) =
      ∑ m, at0 W (PowerSeries.X * b m) • vv m := by
    rw [hx', hb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [smul_smul, evalZero_mul W hR9.hz, evalZero_X_eq_pi0 W hR9.hz]
  have huq := (hU _ hyJ hyD).unique e1 e2
  intro m
  have hm := congrArg PowerSeries.constantCoeff (congrFun huq m)
  simp only [map_mul, map_sub, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, zero_mul] at hm
  have hm2 := (mul_eq_zero.1 hm).resolve_left (pow_ne_zero _ (p_ne_zero W))
  rw [sub_eq_zero] at hm2
  exact hm2.symm

end Const

section Exp

variable {W} {T : LocLat G Qp LL O}

theorem qp_pow_φ (hR9 : R9 W T) (hs1 : W.s = 1) {x : W.DD T} (hx : x ∈ W.N T) :
    ∃ k : ℕ, qp W ^ k • W.φD T x ∈ W.N T := by
  obtain ⟨k, hk⟩ := W.N_φ T x hx
  obtain ⟨w, hw⟩ := hR9.qq
  refine ⟨k, ?_⟩
  have e0 : ((letφ W.φ₀ ^ (W.s - 1)) (fun _ => W.q₀) : LetA O n) = W.q := by
    rw [hs1, Nat.sub_self, pow_zero, AlgHom.one_apply]; rfl
  rw [e0, hw, mul_pow] at hk
  have := (W.N T).smul_mem ((↑(w⁻¹) : LetA O n) ^ k) hk
  rwa [smul_smul, ← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] at this

theorem clear_pullJ (hR9 : R9 W T) (hs1 : W.s = 1) {i : ZMod n} {j : ℕ} (hj : j = 1 ∨ j = 2) {z : W.DD T}
    (hz : z ∈ pullJ W T i j) :
    ∃ K : ℕ, (qp W ^ K * (if j = 1 then (1 : LetA O n) else pk W 1) ^ K) • z ∈ W.N T := by
  set b : LetA O n := if j = 1 then 1 else pk W 1
  suffices h : ∃ k, ∀ K ≥ k, (qp W ^ K * b ^ K) • z ∈ W.N T by
    obtain ⟨k, hk⟩ := h; exact ⟨k, hk k le_rfl⟩
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, ⟨hy, -⟩, rfl⟩ := hx
    rcases hj with rfl | rfl
    · obtain ⟨k, hk⟩ := qp_pow_φ hR9 hs1 hy
      refine ⟨k, fun K hK => ?_⟩
      have e1 : (qp W ^ K * b ^ K) = qp W ^ (K - k) * qp W ^ k := by
        simp only [b, if_pos rfl, one_pow, mul_one]; rw [← pow_add, Nat.sub_add_cancel hK]
      rw [e1, ← smul_smul, pow_one]
      exact (W.N T).smul_mem _ hk
    · obtain ⟨k, hk⟩ := qp_pow_φ hR9 hs1 hy
      obtain ⟨k', hk'⟩ := qp_pow_φ hR9 hs1 hk
      refine ⟨max k k', fun K hK => ?_⟩
      rw [Formalism.MainNotions.WachCoordinates.Br.φD_smulA, smul_smul] at hk'
      have e1 : (qp W ^ K * b ^ K) = (qp W ^ (K - k') * pk W 1 ^ (K - k)) * (qp W ^ k' * W.φA (qp W ^ k)) := by
        simp only [b, if_neg (by norm_num : (2 : ℕ) ≠ 1), map_pow, Formalism.MainNotions.LiftingTheory.pk, pow_one]
        rw [mul_mul_mul_comm, ← pow_add, ← pow_add, Nat.sub_add_cancel (le_of_max_le_right hK),
          Nat.sub_add_cancel (le_of_max_le_left hK)]
      rw [e1, ← smul_smul, pow_two, Module.End.mul_apply]
      exact (W.N T).smul_mem _ hk'
  | zero => exact ⟨0, fun K _ => by rw [smul_zero]; exact (W.N T).zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨k, hk⟩ := hx
    obtain ⟨k', hk'⟩ := hy
    exact ⟨max k k', fun K hK => by
      rw [smul_add]; exact (W.N T).add_mem (hk K (by omega)) (hk' K (by omega))⟩
  | smul a x _ hx =>
    obtain ⟨k, hk⟩ := hx
    exact ⟨k, fun K hK => by rw [smul_comm]; exact (W.N T).smul_mem a (hk K hK)⟩

theorem exp_const (hA : CaseA W) (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.ExpRules W) (hT : IsCrys PD T.ρ) {i : ZMod n} {ζ : LL}
    (hζ : IsPrimitiveRoot ζ PD.p) {z : W.DD T} {a : LetA O n} (hx : a • z ∈ W.N T) {K X : ℕ}
    (U : PowerSeries LL) (hU : IsUnit U) (hlev : W.lev i ζ a = PowerSeries.X ^ K * U)
    (C : T.V ⊗[Qp] BdR)
    (hTH : (∀ r : ℤ, r < 0 → W.levN T i ζ ⟨a • z, hx⟩ r = 0) ∧
      ∀ r : ℕ, r < K + X → W.levN T i ζ ⟨a • z, hx⟩ (r : ℤ) = PowerSeries.coeff r (W.lev i ζ a) • C)
    {d : ℤ → T.V ⊗[Qp] BdR} (hd : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ z d) :
    ∀ s : ℤ, s < X → d s = if s = 0 then C else 0 := by
  have hRR := hR hA T hT i ζ hζ
  have hd2 := hRR.2.2.2.2.1 a z d hd
  have h1x : (1 : LetA O n) • (a • z) ∈ W.N T := by rwa [one_smul]
  have hd3 : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsExp W T i ζ (a • z) (fun k => W.levN T i ζ ⟨a • z, hx⟩ k) := by
    refine ⟨W.levN_supp T i ζ _, 1, h1x, by rw [map_one]; exact one_ne_zero, fun k => ?_⟩
    have : (⟨(1 : LetA O n) • (a • z), h1x⟩ : ↥(W.N T)) = ⟨a • z, hx⟩ := Subtype.ext (one_smul _ _)
    rw [this, map_one, conv_one]
  have heq := (hRR.1 (a • z) 1 h1x (by rw [map_one]; exact one_ne_zero)).unique hd2 hd3
  obtain ⟨md, hmd⟩ := hd.1
  have hδ : ∀ k < (0 : ℤ), (fun k : ℤ => if k = 0 then C else 0) k = 0 := fun k hk => if_neg (by omega)
  have hcc : PowerSeries.constantCoeff U ≠ 0 := (hU.map PowerSeries.constantCoeff).ne_zero
  have key := conv_cancel (W.lev i ζ a) U K X hlev hcc (e := d - fun k : ℤ => if k = 0 then C else 0)
    (m := min md 0) (fun k hk => by simp only [Pi.sub_apply]; rw [hmd k (by omega), if_neg (by omega), sub_self])
    (fun r hr => by
      rw [conv_sub (W.lev i ζ a) hmd hδ, conv_delta, show conv (W.lev i ζ a) d r = W.levN T i ζ ⟨a • z, hx⟩ r from
        congrFun heq r]
      split_ifs with h0
      · rw [hTH.1 r h0, sub_self]
      · have hr' : r = ((r.toNat : ℕ) : ℤ) := by omega
        rw [hr', hTH.2 r.toNat (by omega), Int.toNat_natCast, sub_self])
  intro s hs
  have := key s hs
  simp only [Pi.sub_apply, sub_eq_zero] at this
  exact this

end Exp

section Inv

variable {W} {T : LocLat G Qp LL O} (hR9 : R9 W T) {i : ZMod n} {j X σ r : ℕ}
  (hc1 : ∀ w, InI W T i w → ∃ z, IsTrunc W T i j 1 X σ w z)
  (hc4 : ∀ (a a' : O) (w w' z z' z'' : W.DD T), InI W T i w → InI W T i w' → IsTrunc W T i j 1 X σ w z →
    IsTrunc W T i j 1 X σ w' z' → IsTrunc W T i j 1 X σ (a • w + a' • w') z'' →
      ∃ p ∈ pullJ W T i j, z'' - (a • z + a' • z') = fMX W 1 X • p)
  (hc5 : ∀ w z, InI W T i w → InPN W T 1 w → IsTrunc W T i j 1 X σ w z → ∃ p ∈ pullJ W T i j, z = fMX W 1 X • p)
  {e : Fin r → W.DD T} (he1 : ∀ k, e k ∈ W.N T ∧ DL W T i (e k)) (z : Fin r → W.DD T)
  (hz : ∀ k, IsTrunc W T i j 1 X σ (e k) (z k))
include hR9 hc1 hc4 hc5 he1 hz

theorem inI_comb (α : Fin r → O) (s : Finset (Fin r)) : InI W T i (∑ k ∈ s, α k • e k) :=
  inI_of hR9 (Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (he1 k).1)
    (dl_sum W _ _ fun k _ => dl_smulO W _ (he1 k).2)

theorem trunc_lin (α : Fin r → O) (s : Finset (Fin r)) :
    ∀ z', IsTrunc W T i j 1 X σ (∑ k ∈ s, α k • e k) z' →
      ∃ p ∈ pullJ W T i j, z' - ∑ k ∈ s, α k • z k = fMX W 1 X • p := by
  induction s using Finset.induction_on with
  | empty =>
    intro z' hz'
    have h0 : InI W T i (0 : W.DD T) := inI_of hR9 (W.N T).zero_mem (dl_zero W i)
    simp only [Finset.sum_empty] at hz' ⊢
    obtain ⟨p, hp, hpe⟩ := hc5 0 z' h0 ⟨0, (W.N T).zero_mem, fun δ _ => map_zero _, by rw [smul_zero]⟩ hz'
    exact ⟨p, hp, by rw [sub_zero, hpe]⟩
  | insert a s ha ih =>
    intro z' hz'
    obtain ⟨zs, hzs⟩ := hc1 _ (inI_comb hR9 hc1 hc4 hc5 he1 z hz α s)
    have hIa : InI W T i (e a) := inI_of hR9 (he1 a).1 (he1 a).2
    have e1 : ∑ k ∈ insert a s, α k • e k = (1 : O) • (∑ k ∈ s, α k • e k) + α a • e a := by
      rw [Finset.sum_insert ha, one_smul, add_comm]
    rw [e1] at hz'
    obtain ⟨p1, hp1, hp1e⟩ := hc4 1 (α a) _ _ _ _ _ (inI_comb hR9 hc1 hc4 hc5 he1 z hz α s) hIa hzs (hz a) hz'
    obtain ⟨p2, hp2, hp2e⟩ := ih zs hzs
    refine ⟨p1 + p2, Submodule.add_mem _ hp1 hp2, ?_⟩
    rw [Finset.sum_insert ha, smul_add, ← hp1e, ← hp2e, one_smul]
    abel

theorem trunc_cong (hB : ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k)
    {w zw : W.DD T} (hw : w ∈ W.N T) (hwI : InI W T i w) (hzw : IsTrunc W T i j 1 X σ w zw) :
    ∃ α : Fin r → O, ∃ p ∈ pullJ W T i j, zw - ∑ k, α k • z k = fMX W 1 X • p := by
  obtain ⟨a, ha⟩ := (hB w hw hwI.1).exists
  set α : Fin r → O := fun k => PowerSeries.constantCoeff (a k)
  set a' : Fin r → PowerSeries O := fun k => PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (a k)
  have hsplit : ∀ k, a k = PowerSeries.C (α k) + PowerSeries.X * a' k := by
    intro k
    have := PowerSeries.sub_const_eq_X_mul_shift (a k)
    rw [← this]; ring
  set w' := ∑ k, α k • e k
  set y := ∑ k, at0 W (a' k) • e k
  have hyN : y ∈ W.N T := Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (he1 k).1
  have hdiff : w - w' = W.π₀ • y := by
    rw [ha, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsplit k, evaluation_add W hR9.hz, evalZero_C, evalZero_mul W hR9.hz, evalZero_X_eq_pi0 W hR9.hz, add_smul, smul_smul,
      algebraMap_smul, add_sub_cancel_left]
  have hw'I : InI W T i w' := inI_comb hR9 hc1 hc4 hc5 he1 z hz α Finset.univ
  have hdD : DL W T i (w - w') := dl_sub W hwI.1 hw'I.1
  have hdI : InI W T i (w - w') :=
    inI_of hR9 (Submodule.sub_mem _ hw (Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (he1 k).1)) hdD
  have hyD : DL W T i y := dl_of_π₀ hR9 hdD hdiff
  obtain ⟨zw', hzw'⟩ := hc1 w' hw'I
  obtain ⟨zd, hzd⟩ := hc1 (w - w') hdI
  have e1 : (1 : O) • w' + (1 : O) • (w - w') = w := by rw [one_smul, one_smul, add_sub_cancel]
  rw [← e1] at hzw
  obtain ⟨p1, hp1, hp1e⟩ := hc4 1 1 _ _ _ _ _ hw'I hdI hzw' hzd hzw
  obtain ⟨p2, hp2, hp2e⟩ := hc5 _ _ hdI ⟨y, hyN, hyD.2, by rw [pow_one]; exact hdiff⟩ hzd
  obtain ⟨p3, hp3, hp3e⟩ := trunc_lin hR9 hc1 hc4 hc5 he1 z hz α Finset.univ zw' hzw'
  refine ⟨α, p1 + p2 + p3, Submodule.add_mem _ (Submodule.add_mem _ hp1 hp2) hp3, ?_⟩
  rw [smul_add, smul_add, ← hp1e, ← hp2e, ← hp3e, one_smul, one_smul]
  abel

theorem span_cong (hB : ∀ x ∈ W.N T, DL W T i x → ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • e k)
    {x : W.DD T} (hx : x ∈ Submodule.span (LetA O n) {z | ∃ w, w ∈ W.N T ∧ InI W T i w ∧ IsTrunc W T i j 1 X σ w z}) :
    ∃ a : Fin r → LetA O n, ∃ p ∈ pullJ W T i j, x - ∑ k, a k • z k = fMX W 1 X • p := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, hw, hwI, hzw⟩ := hy
    obtain ⟨α, p, hp, hpe⟩ := trunc_cong hR9 hc1 hc4 hc5 he1 z hz hB hw hwI hzw
    refine ⟨fun k => algebraMap O (LetA O n) (α k), p, hp, ?_⟩
    simp only [algebraMap_smul]
    exact hpe
  | zero => exact ⟨0, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, p, hp, hpe⟩ := hx
    obtain ⟨b, q, hq, hqe⟩ := hy
    refine ⟨a + b, p + q, Submodule.add_mem _ hp hq, ?_⟩
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, smul_add, ← hpe, ← hqe]
    abel
  | smul c x _ hx =>
    obtain ⟨a, p, hp, hpe⟩ := hx
    refine ⟨fun k => c * a k, c • p, Submodule.smul_mem _ _ hp, ?_⟩
    simp only [← smul_smul, ← Finset.smul_sum, ← smul_sub, hpe]
    rw [smul_comm]

end Inv

section Avg2

variable {W} {T : LocLat G Qp LL O}

theorem avD_sum {ι : Type} (s : Finset ι) (f : ι → W.DD T) : avD W (∑ k ∈ s, f k) = ∑ k ∈ s, avD W (f k) := by
  simp only [avD, map_sum]
  exact Finset.sum_comm

theorem frobeniusPoly_eq_evalZero (hR9 : R9 W T) (X : ℕ) :
    fMX W 1 X = at0 W (PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X) := by
  rw [evalZero_mul W hR9.hz, evalZero_pow W hR9.hz, evaluation_add W hR9.hz, evalZero_X_eq_pi0 W hR9.hz, ← map_natCast PowerSeries.C, evalZero_C,
    map_natCast, Formalism.MainNotions.CrystallineLiftingInputs.fMX, pow_one]
  rfl

theorem qp_mem (hR9 : R9 W T) : qp W ∈ W.AΔ := Subalgebra.add_mem _ hR9.πΔ (Subalgebra.natCast_mem _ _)

theorem f_mem (hR9 : R9 W T) (X : ℕ) : fMX W 1 X ∈ W.AΔ :=
  Subalgebra.mul_mem _ (Subalgebra.pow_mem _ hR9.πΔ _) (Subalgebra.pow_mem _ (qp_mem hR9) _)

theorem idempotent_mul_eq_eval_zero (hR9 : R9 W T) {a : LetA O n} (ha : a ∈ W.AΔ) (c : ZMod n) :
    ∃ g : PowerSeries O, a * letE c = at0 W g * letE c := by
  obtain ⟨f, hf⟩ := hR9.πsub a ha
  refine ⟨f c, funext fun c' => ?_⟩
  by_cases h : c' = c
  · subst h; simp [letE, hf, at0]
  · simp [letE, Pi.single_apply, h]

theorem inv_col [IsDomain O] (hR9 : R9 W T) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) {i : ZMod n} {j X σ r : ℕ}
    {e : Fin r → W.DD T} (z : Fin r → W.DD T) (Z : Matrix (Fin r) (Fin r) (PowerSeries O))
    (hU : ∀ x ∈ pullJ W T i j, DL W T (i + (j : ZMod n)) x →
      ∃! a : Fin r → PowerSeries O, x = ∑ k, at0 W (a k) • ((W.φD T) ^ j) (e k))
    (he1 : ∀ k, e k ∈ W.N T ∧ DL W T i (e k)) (hzD : ∀ k, DL W T (i + (j : ZMod n)) (z k))
    (hzZ : ∀ k, z k = ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m)) (m : Fin r) (a : Fin r → LetA O n)
    (q : W.DD T) (hq : q ∈ pullJ W T i j)
    (heq : ((PD.p : ℕ) : O) ^ (2 * σ) • ((W.φD T) ^ j) (e m) = ∑ k, a k • z k + fMX W 1 X • q) :
    ∃ Zc Pc : Fin r → PowerSeries O, ∀ m', PowerSeries.C (if m' = m then ((PD.p : ℕ) : O) ^ (2 * σ) else 0) =
      ∑ k, Z m' k * Zc k + PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X * Pc m' := by
  set vv : Fin r → W.DD T := fun m => ((W.φD T) ^ j) (e m) with hvv
  set c := i + (j : ZMod n)
  have hvD : ∀ m, DL W T c (vv m) := fun m => dl_φpow W (he1 m).2 j
  have hvJ : ∀ m, vv m ∈ pullJ W T i j := fun m => φpow_mem_pullJ W (he1 m).1 (he1 m).2 j
  set u : O := ↑hΔ.unit⁻¹
  have hu : u * ((W.DelF.card : ℕ) : O) = 1 := by simp [u]
  have h1 : avD W (((PD.p : ℕ) : O) ^ (2 * σ) • vv m) = ((W.DelF.card : ℕ) : O) • (((PD.p : ℕ) : O) ^ (2 * σ) • vv m) :=
    avD_of_inv W (dl_smulO W _ (hvD m)).2
  have h2 : avD W (∑ k, a k • z k) = ∑ k, avA W (a k) • z k := by
    rw [avD_sum]; exact Finset.sum_congr rfl fun k _ => avD_smul W (a k) (hzD k).2
  have h3 : avD W (fMX W 1 X • q) = fMX W 1 X • avD W q := avD_smulΔ W (f_mem hR9 X) q
  have hav : ((W.DelF.card : ℕ) : O) • (((PD.p : ℕ) : O) ^ (2 * σ) • vv m) =
      ∑ k, avA W (a k) • z k + fMX W 1 X • avD W q := by
    rw [← h1, ← h2, ← h3, ← avD_add W]; exact congrArg (avD W) heq
  set w : Fin r → LetA O n := fun k => algebraMap O (LetA O n) u * avA W (a k)
  set q₁ := u • avD W q
  have hav2 : ((PD.p : ℕ) : O) ^ (2 * σ) • vv m = ∑ k, w k • z k + fMX W 1 X • q₁ := by
    have := congrArg (fun x => u • x) hav
    simp only [smul_smul] at this
    rw [← mul_assoc, hu, one_mul] at this
    rw [this, smul_add, Finset.smul_sum]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [smulO_eq, smul_smul]
    · rw [smul_comm]
  set qb := (letE c : LetA O n) • q₁
  have hav3 : ((PD.p : ℕ) : O) ^ (2 * σ) • vv m = ∑ k, w k • z k + fMX W 1 X • qb := by
    have := congrArg (fun x => (letE c : LetA O n) • x) hav2
    simp only [smul_add, Finset.smul_sum] at this
    rw [(dl_smulO W _ (hvD m)).1] at this
    rw [this]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [smul_comm, (hzD k).1]
    · rw [smul_comm]
  have hqbJ : qb ∈ pullJ W T i j :=
    Submodule.smul_mem _ _ (Submodule.smul_of_tower_mem _ _ (avD_mem_pullJ W hq))
  have hqbD : DL W T c qb := by
    refine ⟨by rw [smul_smul, Formalism.MainNotions.WachCoordinates.Br.letE_mul_self], fun δ hδ => ?_⟩
    rw [Formalism.MainNotions.WachCoordinates.Br.γD_smulA, Formalism.MainNotions.WachCoordinates.Br.γA_letE, map_smul, avD_inv W q δ hδ]
  obtain ⟨Pc, hPc⟩ := (hU qb hqbJ hqbD).exists
  have hw : ∀ k, w k ∈ W.AΔ :=
    fun k => Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (avA_mem W (a k))
  choose g hg using fun k => idempotent_mul_eq_eval_zero hR9 (hw k) c
  have hterm : ∀ k, w k • z k = at0 W (g k) • z k := by
    intro k
    conv_lhs => rw [← (hzD k).1]
    conv_rhs => rw [← (hzD k).1]
    rw [smul_smul, smul_smul, hg k]
  have hs : ∑ m', (at0 W (PowerSeries.C (if m' = m then ((PD.p : ℕ) : O) ^ (2 * σ) else 0))) • vv m' =
      ((PD.p : ℕ) : O) ^ (2 * σ) • vv m := by
    simp only [evalZero_C]
    rw [Finset.sum_eq_single m (fun m' _ hm => by rw [if_neg hm, map_zero, zero_smul]) (by simp),
      if_pos rfl, algebraMap_smul]
  have hexp : ((PD.p : ℕ) : O) ^ (2 * σ) • vv m = ∑ m', at0 W (∑ k, Z m' k * g k +
      PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X * Pc m') • vv m' := by
    rw [hav3, Finset.sum_congr rfl fun k _ => hterm k, frobeniusPoly_eq_evalZero hR9 X, hPc, Finset.smul_sum]
    simp only [hzZ, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [← Finset.sum_smul, ← add_smul]
    congr 1
    rw [evaluation_add W hR9.hz, evalZero_sum W hR9.hz]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [evalZero_mul W hR9.hz, mul_comm]
    · simp only [evalZero_mul W hR9.hz]
  have hxJ : ((PD.p : ℕ) : O) ^ (2 * σ) • vv m ∈ pullJ W T i j := Submodule.smul_of_tower_mem _ _ (hvJ m)
  have huq := (hU _ hxJ (dl_smulO W _ (hvD m))).unique hs.symm hexp
  exact ⟨g, Pc, fun m' => congrFun huq m'⟩

end Avg2

section Main

theorem zTool_of [NeZero n] [IsDomain O] (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hT2 : TTool2 W) (hTH : THor W)
    (hB : BasTool W) (hR : ExpRules W) (hRing : ExpRing W) (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) :
    ZTool W := by
  intro hA hp11 j X σ hTC T hT i r e he
  have hR9 := ring_hypotheses_of_crystalline W hA h9 T hT
  have hO : ∀ c : O, ((PD.p : ℕ) : O) * c = 0 → c = 0 := fun c h => (mul_eq_zero.1 h).resolve_left (p_ne_zero W)
  have T2 := (hT2 hA hp11 j 1 X σ hTC).1 T hT i
  have hI : ∀ k, InI W T i (e k) := fun k => inI_of hR9 (he.1 k).1 (he.1 k).2
  choose z hz using fun k => T2.1 (e k) (hI k)
  have hφe : ∀ k, ((W.φD T) ^ j) (e k) ∈ pullJ W T i j := fun k => φpow_mem_pullJ W (he.1 k).1 (he.1 k).2 j
  have hzJ : ∀ k, z k ∈ pullJ W T i j := by
    intro k
    have h1 := (T2.2.1 (e k) (z k) (hI k) (hz k)).1
    have h2 := Submodule.add_mem _ h1 (Submodule.smul_of_tower_mem _ (((PD.p : ℕ) : O) ^ σ) (hφe k))
    rwa [sub_add_cancel] at h2
  have hzD : ∀ k, DL W T (i + (j : ZMod n)) (z k) := fun k => trunc_dl hR9 hO (hI k) (hz k)
  have hU := ((hB hA T hT i).2 r e he j).1
  choose Zf hZf using fun k => (hU (z k) (hzJ k) (hzD k)).exists
  let Z : Matrix (Fin r) (Fin r) (PowerSeries O) := fun m k => Zf k m
  have hzZ : ∀ k, ∑ m, at0 W (Z m k) • ((W.φD T) ^ j) (e m) = z k := fun k => (hZf k).symm
  have hcol : ∀ m, ∃ Zc Pc : Fin r → PowerSeries O, ∀ m', PowerSeries.C (if m' = m then ((PD.p : ℕ) : O) ^ (2 * σ) else 0) =
      ∑ k, Z m' k * Zc k + PowerSeries.X * (PowerSeries.X + ((PD.p : ℕ) : PowerSeries O)) ^ X * Pc m' := by
    intro m
    obtain ⟨p', hp', hsp⟩ := T2.2.2.2.2.2 _ (hφe m)
    obtain ⟨a, p'', hp'', hpe⟩ := span_cong hR9 T2.1 T2.2.2.2.1 T2.2.2.2.2.1 he.1 z hz he.2 hsp
    refine inv_col hR9 hΔ z Z hU he.1 hzD (fun k => (hzZ k).symm) m a (p' + p'') (Submodule.add_mem _ hp' hp'') ?_
    rw [smul_add, ← hpe]
    abel
  choose Zc Pc hZc using hcol
  refine ⟨Z, Matrix.of fun k m => Zc m k, Matrix.of fun m' m => -(Pc m m'), fun m k => ?_, ?_, fun k => ⟨?_, ?_⟩⟩
  · exact const_coord hR9 hO hU he.1 (hI k) (hz k) (fun m => Z m k) (hZf k) (hzJ k) m
  · refine Matrix.ext fun m' m => ?_
    rw [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul,
      smul_eq_mul]
    simp only [Matrix.of_apply]
    have h := hZc m m'
    rw [eq_sub_of_add_eq h.symm]
    split_ifs with hmm <;> simp [map_pow, map_natCast] <;> ring
  · rw [hzZ k]
    exact (T2.2.1 (e k) (z k) (hI k) (hz k)).2
  · intro ζ hζ d hd s hs
    rw [hzZ k] at hd
    have hj12 : j = 1 ∨ j = 2 := by
      rcases hTC with ⟨h, -⟩ | ⟨h, -⟩
      · exact Or.inl h
      · exact Or.inr h
    obtain ⟨Kk, hK⟩ := clear_pullJ hR9 hA.2.1 hj12 (hzJ k)
    have hTHk := hTH hA hp11 j 1 X σ hTC T hT i (e k) (z k) (he.1 k).1 (hI k) (hz k) ζ (Kk + X) Kk
      ((if j = 1 then (1 : LetA O n) else pk W 1) ^ Kk) hK (Or.inl ⟨hζ, rfl⟩)
    obtain ⟨⟨u, hu, hqu⟩, -, hp1⟩ := hRing hA (i + (j : ZMod n)) ζ hζ
    have hb : IsUnit (W.lev (i + (j : ZMod n)) ζ (if j = 1 then (1 : LetA O n) else pk W 1)) := by
      split_ifs
      · rw [map_one]; exact isUnit_one
      · exact hp1
    have hlev : W.lev (i + (j : ZMod n)) ζ (qp W ^ Kk * (if j = 1 then (1 : LetA O n) else pk W 1) ^ Kk) =
        PowerSeries.X ^ Kk * (u ^ Kk * (W.lev (i + (j : ZMod n)) ζ (if j = 1 then (1 : LetA O n) else pk W 1)) ^ Kk) := by
      rw [map_mul, map_pow, map_pow, hqu, mul_pow]
      ring
    exact exp_const hA hR hT hζ hK _ ((hu.pow Kk).mul (hb.pow Kk)) hlev _ hTHk hd s hs

end Main

end Formalism.MainNotions.RamifiedCoefficientChains.Sh.ZT

end
