import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.LettersFreeOfRank
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.PointRingCommRing
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.WachModuleUniqueness
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubstInvariants
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntegralCyclotomicChar

open PowerSeries GlobalTheory.WachUse Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.SenLines

namespace GlobalTheory.WachRankOne

section Series

variable {O : Type} [CommRing O] [IsDomain O]

theorem exists_gamma_q (l : ℕ) (q : O⟦X⟧) (hq : X * q = (1 + X) ^ l - 1) (γ : O⟦X⟧ →ₐ[O] O⟦X⟧)
    (hγ : γ X = (1 + X) ^ (1 + l) - 1) : ∃ w, γ q = q * w ∧ q ∣ w - (1 + (l : O⟦X⟧)) := by
  have hy : (1 + X : O⟦X⟧) ^ l = 1 + X * q := by rw [hq]; ring
  set S : O⟦X⟧ := ∑ j ∈ Finset.range (1 + l), (1 + X * q) ^ j with hS
  have h1 : γ X = X * (1 + (1 + X) * q) := by rw [hγ, pow_add, hy]; ring
  have h2 : γ X * γ q = X * q * S := by
    have := geom_sum_mul (1 + X * q : O⟦X⟧) (1 + l)
    rw [← map_mul, hq, map_sub, map_pow, map_add, map_one, hγ, add_sub_cancel, ← pow_mul, mul_comm (1 + l),
      pow_mul, hy, ← this, ← hS]
    ring
  have h3 : (1 + (1 + X) * q) * γ q = q * S := by
    apply mul_left_cancel₀ (X_ne_zero (R := O))
    rw [← mul_assoc, ← h1, h2, mul_assoc]
  have h4 : γ q = q * (S - (1 + X) * γ q) := by linear_combination h3
  refine ⟨_, h4, ?_⟩
  have h5 : q ∣ S - (1 + (l : O⟦X⟧)) := by
    have : (1 + (l : O⟦X⟧)) = ∑ j ∈ Finset.range (1 + l), (1 : O⟦X⟧) ^ j := by simp
    rw [this, hS, ← Finset.sum_sub_distrib]
    refine Finset.dvd_sum fun j _ => Dvd.dvd.trans ?_ (sub_dvd_pow_sub_pow _ _ j)
    exact ⟨X, by ring⟩
  have h6 : q ∣ (1 + X) * γ q := Dvd.dvd.mul_left ⟨_, h4⟩ _
  convert dvd_sub h5 h6 using 1
  ring

theorem dvd_of_comm [IsNoetherianRing O] (l : ℕ) (q : O⟦X⟧) (hq0 : q ≠ 0) (hq : X * q = (1 + X) ^ l - 1)
    (γ : O⟦X⟧ →ₐ[O] O⟦X⟧) (hγ : γ X = (1 + X) ^ (1 + l) - 1) (k m : ℕ) (u : (O⟦X⟧)ˣ) (h h' : O⟦X⟧) (e : O)
    (hh : q ∣ h - C e) (hh' : q ∣ h' - 1)
    (E : γ q ^ k * h' * (q ^ m * u) = q ^ k * γ (q ^ m * u) * h) :
    q ∣ C ((1 + (l : O)) ^ k - (1 + (l : O)) ^ m * e) := by
  obtain ⟨w, hw, hw'⟩ := exists_gamma_q l q hq γ hγ
  have h1 : γ X = X * (1 + (1 + X) * q) := by rw [hγ, pow_add]; linear_combination (-(1 + X)) * hq
  have hu : q ∣ γ u - u := GlobalTheory.CycFr.dvd_algHom_sub γ (AlgHom.id O _) ⟨_, h1⟩ dvd_rfl q
    ⟨X * (1 + X), by rw [h1, AlgHom.id_apply]; ring⟩ u
  have E' : w ^ k * h' * u = w ^ m * γ u * h := by
    apply mul_left_cancel₀ (pow_ne_zero (k + m) hq0)
    rw [map_mul, map_pow, hw] at E
    linear_combination E
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq] at hh hh' hw' hu
  have E2 := congrArg (Ideal.Quotient.mk (Ideal.span {q})) E'
  simp only [map_mul, map_pow, hh, hh', hw', hu, map_one, mul_one] at E2
  rw [map_sub, ← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  apply (u.isUnit.map (Ideal.Quotient.mk (Ideal.span {q}))).mul_left_cancel
  simp only [map_mul, map_pow, map_add, map_one, map_natCast] at E2 ⊢
  linear_combination E2

variable {ι : Type} (J : O⟦X⟧ →ₐ[O] O⟦X⟧) (hJ : Function.Injective J) (S : Finset ι)
  (d : ι → (O⟦X⟧ →ₐ[O] O⟦X⟧)) (hr : ∀ a, (∃ b, J b = a) ↔ ∀ δ ∈ S, d δ a = a)
include hJ hr

theorem associated_of_dvd (f : O⟦X⟧) (hf : ∀ δ ∈ S, d δ f = f) (N : ℕ) (h : f ∣ J X ^ N) :
    ∃ m, Associated f (J X ^ m) := by
  obtain ⟨g, hg⟩ := h
  have h0 : J X ^ N ≠ 0 := pow_ne_zero _ fun h => X_ne_zero (hJ (h.trans (map_zero J).symm))
  have hf0 : f ≠ 0 := fun h => h0 (by rw [hg, h, zero_mul])
  obtain ⟨G, rfl⟩ := (hr g).2 fun δ hδ => by
    apply mul_left_cancel₀ hf0
    have h1 := congrArg (d δ) hg
    rw [map_mul, hf δ hδ, map_pow, (hr _).1 ⟨X, rfl⟩ δ hδ] at h1
    rw [← h1, hg]
  obtain ⟨F, rfl⟩ := (hr f).2 hf
  have h2 : F ∣ X ^ N := ⟨G, hJ (by rw [map_pow, map_mul, hg])⟩
  obtain ⟨m, -, hm⟩ := (dvd_prime_pow X_prime N).1 h2
  exact ⟨m, by simpa using hm.map J⟩

theorem eq_zero_of_dvd_C (c : O) (h : J X ∣ C c) : c = 0 := by
  obtain ⟨g, hg⟩ := h
  have h0 : J X ≠ 0 := fun h => X_ne_zero (hJ (h.trans (map_zero J).symm))
  have hC : ∀ t : O⟦X⟧ →ₐ[O] O⟦X⟧, t (C c) = C c := fun t => t.commutes c
  obtain ⟨G, rfl⟩ := (hr g).2 fun δ hδ => by
    apply mul_left_cancel₀ h0
    have h1 := congrArg (d δ) hg
    rw [map_mul, hC, (hr _).1 ⟨X, rfl⟩ δ hδ] at h1
    rw [← h1, hg]
  have h2 : C c = X * G := hJ (by rw [hC, map_mul, hg])
  simpa using congrArg constantCoeff h2

end Series

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem φD_smulA (a : LetA O n) (x : W.DD T) : W.φD T (a • x) = W.φA a • W.φD T x := by
  have := W.φD_smul T (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.φE_ext, algebraMap_smul] at this

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) : W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rwa [algebraMap_smul, W.γE_ext, algebraMap_smul] at this

theorem φpull_eq {β : W.DD T} (hN : W.N T = Submodule.span (LetA O n) {β}) :
    W.φpull T = Submodule.span (LetA O n) {W.φD T β} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, hN, Submodule.mem_span_singleton] at hx
    obtain ⟨a, rfl⟩ := hx
    rw [φD_smulA]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨β, by rw [hN]; exact Submodule.mem_span_singleton_self _, rfl⟩

variable [IsDomain O]

theorem exists_frob (hs : W.s = 1) {g : W.Gam} {J : O⟦X⟧ →ₐ[O] O⟦X⟧} (hJ : QFrame W g J) {β : W.DD T}
    (hβ : β ∈ W.NΔ T) (hN : W.N T = Submodule.span (LetA O n) {β})
    (hi : ∀ a b : LetA O n, a • β = b • β → a = b) :
    ∃ (k : ℕ) (f : LetA O n), W.q ^ k • W.φD T β = f • β ∧
      ∀ i, ∃ (m : ℕ) (u : (O⟦X⟧)ˣ), f i = W.q₀ ^ m * u := by
  obtain ⟨h1, h2, -, -, -, h6, -⟩ := hJ
  obtain ⟨k, hk⟩ := W.N_φ T β hβ.1
  obtain ⟨k', hk'⟩ := W.N_φinv T β hβ.1
  change _ ∈ W.φpull T at hk'
  rw [φpull_eq W T hN, Submodule.mem_span_singleton] at hk'
  rw [hN, Submodule.mem_span_singleton] at hk
  simp only [hs, Nat.sub_self, pow_zero, AlgHom.one_apply] at hk hk'
  obtain ⟨f, hf⟩ := hk
  obtain ⟨f', hf'⟩ := hk'
  change f • β = W.q ^ k • W.φD T β at hf
  change f' • W.φD T β = W.q ^ k' • β at hf'
  refine ⟨k, f, hf.symm, fun i => ?_⟩
  have e1 : f * f' = W.q ^ (k + k') := hi _ _ (by
    rw [mul_comm, mul_smul, hf, smul_comm, hf', smul_smul, pow_add])
  obtain ⟨w, hw⟩ := h6.symm
  let w' : LetA O n := fun _ => w
  let q' : LetA O n := fun _ => J X
  have hq' : q' = w' * W.q := funext fun _ => by
    change J X = w * W.q₀
    rw [← hw, mul_comm]
  have e2 : (w' ^ k * f) • β = q' ^ k • W.φD T β := by rw [mul_smul, hf, smul_smul, hq', mul_pow]
  have e3 : ∀ δ ∈ W.DelF, W.γ₀ δ ((w : O⟦X⟧) ^ k * f i) = (w : O⟦X⟧) ^ k * f i := fun δ hδ => by
    have h3 := congrArg (W.γD T δ) e2
    have h4 : W.γA δ q' = q' := funext fun _ => (h2 _).1 ⟨X, rfl⟩ δ hδ
    rw [γD_smulA, γD_smulA, ← W.φγ_comm, hβ.2 δ hδ, map_pow, h4, ← e2] at h3
    exact congrFun (hi _ _ h3) i
  have e4 : f i * f' i = W.q₀ ^ (k + k') := congrFun e1 i
  have hwf : Associated ((w : O⟦X⟧) ^ k * f i) (f i) := associated_unit_mul_left _ _ (w.isUnit.pow k)
  obtain ⟨m, hm⟩ := associated_of_dvd J h1 W.DelF (fun δ => W.γ₀ δ) h2 _ e3 (k + k')
    (hwf.dvd.trans ((Dvd.intro _ e4).trans h6.symm.pow_pow.dvd))
  obtain ⟨u, hu⟩ := ((hwf.symm.trans hm).trans h6.pow_pow).symm
  exact ⟨m, u, hu.symm⟩

theorem pow_eq_of_frob [IsNoetherianRing O] {g : W.Gam} {J : O⟦X⟧ →ₐ[O] O⟦X⟧} (hJ : QFrame W g J)
    (hg : W.γ₀ g X = (1 + X) ^ (1 + PD.p) - 1) {β : W.DD T}
    (hN : W.N T = Submodule.span (LetA O n) {β})
    (hi : ∀ a b : LetA O n, a • β = b • β → a = b) {k : ℕ} {f : LetA O n} (hf : W.q ^ k • W.φD T β = f • β)
    {i : ZMod n} {m : ℕ} {u : (O⟦X⟧)ˣ} (hu : f i = W.q₀ ^ m * u) {y z : W.DD T} (hy : y ∈ W.N T)
    (hz : z ∈ W.N T) (hγ : W.γD T g β - β = W.π₀ • y) {c : O}
    (hc : (letE i : LetA O n) • (y - c • β) = (W.π₀ + (PD.p : LetA O n)) • z) :
    (1 + (PD.p : O)) ^ k = (1 + (PD.p : O)) ^ m * (1 - PD.p * c) := by
  obtain ⟨h1, h2, h3, -, -, h6, -⟩ := hJ
  obtain ⟨y', hy', hπ⟩ := W.N_π T g β (by rw [hN]; exact Submodule.mem_span_singleton_self _)
  rw [hN, Submodule.mem_span_singleton] at hy hz hy'
  obtain ⟨r, rfl⟩ := hy
  obtain ⟨z, rfl⟩ := hz
  obtain ⟨r', rfl⟩ := hy'
  have hq0 : W.q₀ ≠ 0 := h6.ne_zero_iff.1 fun h => X_ne_zero (h1 (h.trans (map_zero J).symm))
  have e1 : W.γD T g β = (1 + W.π₀ * r) • β := by
    rw [add_smul, one_smul, mul_smul, ← hγ, add_sub_cancel]
  have e2 : W.π₀ * r = letπ * r' := hi _ _ (by rw [mul_smul, mul_smul, ← hγ, hπ])
  have e3 : letE i * (r - algebraMap O (LetA O n) c) = (W.π₀ + (PD.p : LetA O n)) * z := hi _ _ (by
    rw [mul_smul, mul_smul, ← hc, sub_smul, algebraMap_smul])
  have e4 : r i - C c = J X * z i := by
    have := congrFun e3 i
    simp only [Pi.mul_apply, letE, Pi.single_eq_same, one_mul] at this
    rw [h3]; exact this
  have e5 : W.γA g W.q ^ k * W.φA (1 + W.π₀ * r) * f = W.q ^ k * W.γA g f * (1 + W.π₀ * r) := hi _ _ (by
    have := congrArg (W.γD T g) hf
    rw [γD_smulA, γD_smulA, ← W.φγ_comm, e1, φD_smulA, map_pow] at this
    rw [mul_smul, ← hf, mul_assoc (W.q ^ k), mul_smul (W.q ^ k), mul_smul (W.γA g f), ← this, smul_comm,
      mul_smul])
  have e6 : W.γ₀ g W.q₀ ^ k * W.φ₀ (1 + X * r' (i - 1)) * (W.q₀ ^ m * u) =
      W.q₀ ^ k * W.γ₀ g (W.q₀ ^ m * u) * (1 + W.π₀₁ * r i) := by
    have := congrFun e5 i
    rw [← hu]
    conv_lhs at this => rw [e2]
    exact this
  have e7 := dvd_of_comm PD.p W.q₀ hq0 W.q₀_def (W.γ₀ g) hg k m u _ _ (1 - PD.p * c)
    (h6.symm.dvd.trans ⟨W.π₀₁ * z i + C c, by
      rw [map_sub, map_mul, map_natCast, map_one]
      linear_combination W.π₀₁ * e4 - C c * h3⟩)
    ⟨X * W.φ₀ (r' (i - 1)), by rw [map_add, map_one, map_mul, W.φ₀_X]; ring⟩ e6
  exact sub_eq_zero.1 (eq_zero_of_dvd_C J h1 W.DelF (fun δ => W.γ₀ δ) h2 _ (h6.dvd.trans e7))

omit [IsDomain O] in

theorem lines_of_frob (hq : IsUnit (algebraMap (LetA O n) W.EE W.q)) {β : W.DD T}
    (hN : W.N T = Submodule.span (LetA O n) {β}) {k : ℕ} {f : LetA O n} (hf : W.q ^ k • W.φD T β = f • β)
    {i : ZMod n} {m : ℕ} {u : (O⟦X⟧)ˣ} (hu : f i = W.q₀ ^ m * u) {a : ℤ} (ha : (m : ℤ) = k + a) :
    (∀ x ∈ W.φpull T, ∃ y ∈ W.N T,
      W.q ^ (-a).toNat • (letE i : LetA O n) • x = W.q ^ a.toNat • (letE i : LetA O n) • y) ∧
    ∀ y ∈ W.N T, ∃ x ∈ W.φpull T,
      W.q ^ (-a).toNat • (letE i : LetA O n) • x = W.q ^ a.toNat • (letE i : LetA O n) • y := by
  let U : LetA O n := fun _ => u
  let U' : LetA O n := fun _ => (u⁻¹ : (O⟦X⟧)ˣ)
  have hU : U' * U = 1 := funext fun _ => u.inv_mul
  have key : W.q ^ (-a).toNat • (letE i : LetA O n) • W.φD T β =
      W.q ^ a.toNat • (letE i : LetA O n) • U • β := by
    have hc : ∀ x y : W.DD T, W.q ^ k • x = W.q ^ k • y → x = y := fun x y h => by
      rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE (W.q ^ k) y, map_pow] at h
      exact (hq.pow k).smul_left_cancel.1 h
    apply hc
    rw [smul_comm (W.q ^ k), smul_comm (W.q ^ k), hf]
    simp only [smul_smul]
    congr 1
    funext j
    by_cases h : j = i
    · subst h
      simp only [Pi.mul_apply, Pi.pow_apply, letE, Pi.single_eq_same, one_mul, hu, LocWach.q, U]
      rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]
      congr 2
      omega
    · simp [letE, h]
  rw [φpull_eq W T hN, hN]
  simp only [Submodule.mem_span_singleton]
  constructor
  · rintro _ ⟨c, rfl⟩
    refine ⟨c • U • β, ⟨c * U, mul_smul _ _ _⟩, ?_⟩
    rw [smul_comm _ c, smul_comm _ c, key, smul_comm _ c (U • β), smul_comm _ c]
  · rintro _ ⟨c, rfl⟩
    refine ⟨(c * U') • W.φD T β, ⟨_, rfl⟩, ?_⟩
    have : c • β = (c * U') • U • β := by rw [smul_smul, mul_assoc, hU, mul_one]
    rw [this, smul_comm _ (c * U'), smul_comm _ (c * U'), key, smul_comm _ (c * U') (U • β),
      smul_comm _ (c * U')]

theorem rankOne_of_qFrame [IsNoetherianRing O] [CharZero LL] (hs : W.s = 1) {g : W.Gam}
    {J : O⟦X⟧ →ₐ[O] O⟦X⟧} (hJ : QFrame W g J) (hχ : (W.χΓ g : O) = 1 + (PD.p : O))
    (hg : W.γ₀ g X = (1 + X) ^ (1 + PD.p) - 1) {c : ℤ → O} (hc : IsC PD LL c)
    (h1 : InvBasis W) (h2 : SenOp W) : RankOne W := by
  intro T a hT _ i
  have hQ : W.Q = W.q := by simp only [LocWach.Q, hs, Nat.sub_self, pow_zero, AlgHom.one_apply]
  obtain ⟨b, hb1, hb2, hb3⟩ := h1 T hT.1
  generalize Module.finrank O ↥T.L.T = r at b hb1 hb2 hb3
  obtain ⟨ν, hν, -, hA⟩ := h2 T _ hT g hχ c hc
  obtain ⟨A, hA1, hA2⟩ := hA r (fun j => ⟨b j, hb1 j⟩) hb2 hb3 i
  simp only [Multiset.map_singleton, Multiset.prod_singleton] at hA1
  obtain rfl : r = 1 := by
    have := congrArg Polynomial.natDegree hA1
    rwa [Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin, Polynomial.natDegree_X_sub_C] at this
  have hA0 : A 0 0 = c (-a i) := by
    rw [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply_eq] at hA1
    exact Polynomial.C_injective (sub_right_injective hA1)
  have hN : W.N T = Submodule.span (LetA O n) {b 0} := by
    rw [hb3, Set.range_unique]; rfl
  have hi : ∀ x y : LetA O n, x • b 0 = y • b 0 → x = y := fun x y h => by
    have := Fintype.linearIndependent_iff.1 hb2 (fun _ => x - y) (by simp [sub_smul, h]) 0
    exact sub_eq_zero.1 this
  obtain ⟨k, f, hf, hm⟩ := exists_frob W T hs hJ (hb1 0) hN hi
  obtain ⟨m, u, hu⟩ := hm i
  obtain ⟨z, hz, hz'⟩ := hA2 0
  rw [Fin.sum_univ_one, hA0] at hz'
  have e := pow_eq_of_frob W T hJ hg hN hi hf hu (ν ⟨b 0, hb1 0⟩).2.1 hz (hν ⟨b 0, hb1 0⟩) hz'
  have e1 := congrArg (algebraMap O LL) e
  simp only [map_pow, map_mul, map_add, map_sub, map_one, map_natCast] at e1
  rw [hc, sub_sub_cancel] at e1
  have e2 : (1 + (PD.p : ℚ)) ^ (k : ℤ) = (1 + (PD.p : ℚ)) ^ ((m : ℤ) + -a i) := by
    rw [zpow_add₀ (by positivity), zpow_natCast, zpow_natCast]
    apply (Rat.cast_injective (α := LL))
    push_cast
    exact e1
  have hp : (0 : ℚ) < PD.p := by exact_mod_cast PD.hp.pos
  have e3 := zpow_right_injective₀ (by positivity) (by linarith) e2
  rw [hQ]
  refine lines_of_frob W T ?_ hN hf hu (by omega)
  obtain ⟨-, -, h3, -, -, ⟨w, hw⟩, h7⟩ := hJ
  have : W.q = (W.π₀ + (PD.p : LetA O n)) * fun _ => (w : O⟦X⟧) := funext fun _ => by
    change W.q₀ = (W.π₀₁ + (PD.p : O⟦X⟧)) * w
    rw [← h3, hw]
  rw [this, map_mul]
  exact h7.mul (IsUnit.map _ (Pi.isUnit_iff.2 fun _ => w.isUnit))

end Generic

theorem dvd_one_sub_zpow {O : Type} [CommRing O] (x : O) (u : Oˣ) (hu : (u : O) = 1 + x) (a : ℤ) :
    x ∣ 1 - ((u ^ a : Oˣ) : O) := by
  rw [← Ideal.mem_span_singleton, ← Ideal.Quotient.eq]
  have h : Units.map (Ideal.Quotient.mk (Ideal.span {x}) : O →* O ⧸ Ideal.span {x}) u = 1 := by
    apply Units.ext
    change Ideal.Quotient.mk (Ideal.span {x}) (u : O) = 1
    rw [hu, map_add, map_one, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self x), add_zero]
  have h2 := congrArg Units.val (map_zpow
    (Units.map (Ideal.Quotient.mk (Ideal.span {x}) : O →* O ⧸ Ideal.span {x})) u a)
  rw [h, one_zpow] at h2
  rw [map_one]
  exact h2.symm

theorem exists_c {O LL : Type} [CommRing O] [Field LL] [Algebra O LL] (p : ℕ) (u : Oˣ)
    (hu : (u : O) = 1 + (p : O)) :
    ∃ c : ℤ → O, ∀ a : ℤ, (p : LL) * algebraMap O LL (c a) = 1 - (1 + (p : LL)) ^ a := by
  choose c hc using dvd_one_sub_zpow (p : O) u hu
  refine ⟨c, fun a => ?_⟩
  have h2 := congrArg (algebraMap O LL) (hc a)
  rw [map_mul, map_natCast, map_sub, map_one] at h2
  rw [← h2]
  congr 1
  have h3 := congrArg Units.val (map_zpow (chiLL LL (MonoidHom.id Oˣ)) u a)
  rw [Units.val_zpow_eq_zpow_val, chiLL_apply, chiLL_apply, MonoidHom.id_apply, MonoidHom.id_apply, hu,
    map_add, map_one, map_natCast] at h3
  exact h3

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) {n : ℕ}
  (W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) n)

theorem exists_gam (h : K.1 ≤ Ks K 1) : ∃ g : W.Gam, (W.χΓ g : ↥(OL LL)) = 1 + (l : ↥(OL LL)) := by
  obtain ⟨χ, hχ, -, hon⟩ := GlobalTheory.Cyc.exists_integral_cyclotomicChar l P
  have hu : IsUnit (1 + (l : ℤ_[l])) := by
    have := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits (-(l : ℤ_[l]))
      (fun hh => PadicInt.p_nonunit ((IsUnit.neg_iff _).1 hh))
    rwa [sub_neg_eq_add] at this
  obtain ⟨g₀, hg₀, hg₀'⟩ := hon K 1 h hu.unit (by simp)
  refine ⟨W.resΓ ⟨g₀, hg₀⟩, ?_⟩
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  apply hinj
  rw [W.χΓ_res, P.PD_χ, ← hχ, hg₀', hu.unit_spec, map_add, map_one, map_natCast, PadicInt.coe_add,
    PadicInt.coe_one, PadicInt.coe_natCast, map_add, map_one, map_natCast]

theorem gam_X {g : W.Gam} (hg : (W.χΓ g : ↥(OL LL)) = 1 + (l : ↥(OL LL))) :
    W.γ₀ g X = (1 + X) ^ (1 + l) - 1 := by
  obtain ⟨χ', hχ', -⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL W
  have h1 : (χ' g : ℤ_[l]) = ((1 + l : ℕ) : ℤ_[l]) := GlobalTheory.algebraMap_padicInt_OL_injective LL (by
    rw [hχ', hg, map_natCast, Nat.cast_add, Nat.cast_one])
  rw [GlobalTheory.WachTie.γ₀_eq W (P.PD_p K) χ' hχ', h1, GlobalTheory.CycFr.act_nat_X]

theorem isNoetherianRing_OL : IsNoetherianRing ↥(OL LL) := by
  obtain ⟨_, -, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  infer_instance

theorem rankOne_of_caseA (h : CaseA K LL) (hs : W.s = 1) (h1 : InvBasis W) (h2 : SenOp W) : RankOne W := by
  have hp := P.PD_p K
  obtain ⟨g, hg⟩ := exists_gam P K LL W h.2.2.2.2.1
  obtain ⟨-, J, hJ⟩ := exists_qFrame P K LL W g h hg
  have hγ := gam_X P K LL W hg
  obtain ⟨c, hc⟩ := exists_c (LL := ↥LL.1) l (W.χΓ g) hg
  haveI := isNoetherianRing_OL LL
  exact rankOne_of_qFrame W hs hJ (by rw [hp]; exact hg) (by rw [hp]; exact hγ) (c := c)
    (fun a => by rw [hp]; exact hc a) h1 h2

end Local

theorem rankOne_of_senOp : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (C : LocCmpT l P AI H E), ∀ (K LL : FinExt l) (h : CaseA K LL), InvBasis (H.W K 1 LL h.2.2) → SenOp (H.W K 1 LL h.2.2) → RankOne (H.W K 1 LL h.2.2) :=
  fun {_} _ {P} _ H _ _ K LL h => rankOne_of_caseA P K LL _ h (H.W_s K 1 LL h.2.2)

end GlobalTheory.WachRankOne
