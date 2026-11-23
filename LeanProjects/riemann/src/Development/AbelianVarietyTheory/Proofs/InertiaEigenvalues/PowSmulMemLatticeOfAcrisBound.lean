import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationBoundOfPrimePowDvdMuPowAcrisStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.Count

section Coord

variable {l : ℕ} [hl : Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

def cfO {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) : O ⊗[ℤ_[l]] R →ₗ[ℤ_[l]] R :=
  (TensorProduct.lid ℤ_[l] R).toLinearMap ∘ₗ TensorProduct.map f LinearMap.id

theorem cfO_tmul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) (r : R) :
    cfO f (o ⊗ₜ[ℤ_[l]] r) = f o • r := by
  simp [cfO]

theorem cfO_mul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (β : R)
    (y : O ⊗[ℤ_[l]] R) : cfO f (((1 : O) ⊗ₜ[ℤ_[l]] β) * y) = β * cfO f y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [mul_add, map_add, map_add, hx, hy, mul_add]
  | tmul o r => rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, cfO_tmul, cfO_tmul, mul_smul_comm]

theorem cfO_map {R R' : Type} [CommRing R] [Algebra ℤ_[l] R] [CommRing R'] [Algebra ℤ_[l] R']
    (f : O →ₗ[ℤ_[l]] ℤ_[l]) (φ : R →ₐ[ℤ_[l]] R') (y : O ⊗[ℤ_[l]] R) :
    cfO f (Algebra.TensorProduct.map (AlgHom.id O O) φ y) = φ (cfO f y) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul o r => rw [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, cfO_tmul, cfO_tmul, map_smul]

theorem cfO_natCast_smul {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (m : ℕ)
    (y : O ⊗[ℤ_[l]] R) : cfO f ((m : O) • y) = (m : R) * cfO f y := by
  rw [Nat.cast_smul_eq_nsmul, map_nsmul, nsmul_eq_mul]

theorem cfO_smul_one {R : Type} [CommRing R] [Algebra ℤ_[l] R] (f : O →ₗ[ℤ_[l]] ℤ_[l]) (o : O) :
    cfO f (o • (1 : O ⊗[ℤ_[l]] R)) = algebraMap ℤ_[l] R (f o) := by
  rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one, cfO_tmul,
    Algebra.smul_def, mul_one]

variable {G : Type} [Group G] [TopologicalSpace G] {Qp LL : Type} [Field Qp] [Field LL] [Algebra Qp LL]
  [Algebra O LL] [TopologicalSpace LL]

def cfT {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) :
    TW R T →ₗ[O] R :=
  (TensorProduct.rid O R).toLinearMap ∘ₗ TensorProduct.map LinearMap.id g

theorem cfT_tmul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (s : R) (t : ↥T.L.T) : cfT T g (s ⊗ₜ[O] t) = g t • s := by
  simp [cfT]

theorem cfT_incl {R R' : Type} [CommRing R] [Algebra O R] [CommRing R'] [Algebra O R']
    (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O) (φ : R →ₐ[O] R') (z : TW R T) :
    cfT T g (TWincl φ T z) = φ (cfT T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul s t => rw [TWincl, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      cfT_tmul, cfT_tmul, map_smul]

theorem cfT_smul {R : Type} [CommRing R] [Algebra O R] (T : LocLat G Qp LL O) (g : ↥T.L.T →ₗ[O] O)
    (r : R) (z : TW R T) : cfT T g (r • z) = r * cfT T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [smul_add, map_add, map_add, hx, hy, mul_add]
  | tmul s t => rw [TensorProduct.smul_tmul', cfT_tmul, cfT_tmul, smul_eq_mul, mul_smul_comm]

end Coord

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

variable {l : ℕ} [hl : Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
  [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
  [NormedAlgebra ℚ_[l] K]

theorem smul_cancel (T : LocLat (Gl l) ℚ_[l] K O) (c : ℕ) {u v : TW (OB l O) T}
    (h : ((l : O) ^ c) • u = ((l : O) ^ c) • v) : u = v := by
  have e : ∀ w : TW (OB l O) T, ((l : O) ^ c) • w = ((l : OB l O) ^ c) • w := by
    intro w
    rw [← algebraMap_smul (OB l O) ((l : O) ^ c) w, map_pow, map_natCast]
  rw [e, e] at h
  exact (isUnit_l_OB.pow c).smul_left_cancel.1 h

theorem toB_algebraMap (q : ℤ_[l]) :
    acrisToBcris l (ainfToAcris l (algebraMap ℤ_[l] (Ainf l) q)) = algebraMap ℤ_[l] (Per.Bcris l) q := by
  rw [AlgHom.commutes, AlgHom.commutes]

theorem le_of_bound {n c v j : ℕ} (hj : 2 * j < l - 1) (h : (l - 1) * n ≤ (l - 1) * (c + v) + 2 * j) :
    n ≤ c + v := by
  have h1 : (l - 1) * n < (l - 1) * (c + v + 1) := by
    rw [mul_add, mul_one]; omega
  exact Nat.lt_succ_iff.1 (Nat.lt_of_mul_lt_mul_left h1)

end GlobalTheory.BKGal.Count

namespace GlobalTheory.BKGal.Count

theorem count : ∀ (l : ℕ) [Fact l.Prime] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O]
    [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K]
    [NormedAlgebra ℚ_[l] K] (T : LocLat (Gl l) ℚ_[l] K O), l ≠ 2 → ∀ ε : OCb l, IsEps ε → ∀ (j n c : ℕ),
    2 * j < l - 1 → ∀ (u : TW (OB l O) T) (x : ↥T.L.T) (w : TW (OCr l O) T),
    (l : O) ^ n • u = (1 : OB l O) ⊗ₜ[O] x →
    toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) • ((l : O) ^ c • u) = TWincl (toOB l O) T w →
    ∃ x' : ↥T.L.T, (l : O) ^ c • u = (1 : OB l O) ⊗ₜ[O] x' := by
  intro l _ O K _ _ _ _ _ _ _ _ _ T hl2 ε hε j n c hj u x w h1 h2
  let bO := Module.Free.chooseBasis ℤ_[l] O
  let bT := latBasis T
  have hr0 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (muOf ε)) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
  have hr : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] muOf ε ^ j) =
      (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l (ainfToAcris l (muOf ε)) ^ j) := by
    rw [map_pow, hr0, Algebra.TensorProduct.tmul_pow, one_pow]
  have hlO : ∀ m : ℕ, (l : O) ^ m = ((l ^ m : ℕ) : O) := fun m => by push_cast; rfl
  have key : ∀ k i, (l : ℤ_[l]) ^ (n - c) ∣ bO.coord k (bT.coord i x) := by
    intro k i
    by_cases ha : bO.coord k (bT.coord i x) = 0
    · rw [ha]; exact dvd_zero _
    have e1 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h1
    have e2 := congrArg (fun z => cfO (bO.coord k) (cfT T (bT.coord i) z)) h2
    rw [hlO, map_smul, cfO_natCast_smul, cfT_tmul, cfO_smul_one] at e1
    rw [hr, cfT_smul, cfO_mul, hlO, map_smul, cfO_natCast_smul, cfT_incl, toOB, cfO_map] at e2
    set U := cfO (bO.coord k) (cfT T (bT.coord i) u)
    set a := bO.coord k (bT.coord i x)
    set W' := cfO (bO.coord k) (cfT T (bT.coord i) w)
    have e3 : acrisToBcris l ((l : Per.Acris l) ^ n * W') = acrisToBcris l
        (ainfToAcris l (muOf ε ^ j * algebraMap ℤ_[l] (Ainf l) ((l : ℤ_[l]) ^ c * a))) := by
      rw [map_mul, map_mul, ← e2, map_pow, map_natCast, map_mul, toB_algebraMap, map_mul, ← e1]
      push_cast
      simp only [map_pow]
      ring
    have e4 := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l e3
    have hne : (l : ℤ_[l]) ^ c * a ≠ 0 :=
      mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)) ha
    have hb := GlobalTheory.T.valuation_bound_of_primePow_dvd_mu_pow_acris l hl2 ε hε j n ((l : ℤ_[l]) ^ c * a) hne ⟨W', e4.symm⟩
    rw [PadicInt.valuation_p_pow_mul c a ha] at hb
    have hv : n - c ≤ a.valuation := by have := le_of_bound hj hb; omega
    exact Ideal.mem_span_singleton.1 ((PadicInt.mem_span_pow_iff_le_valuation a ha (n - c)).2 hv)
  choose q hq using key
  let x' : ↥T.L.T := bT.equivFun.symm fun i => bO.equivFun.symm fun k => q k i
  have hx' : (l : O) ^ (n - c) • x' = x := by
    apply bT.equivFun.injective
    funext i
    rw [map_smul, Pi.smul_apply, LinearEquiv.apply_symm_apply, smul_eq_mul]
    apply bO.equivFun.injective
    funext k
    rw [show (l : O) ^ (n - c) = algebraMap ℤ_[l] O ((l : ℤ_[l]) ^ (n - c)) by rw [map_pow, map_natCast],
      ← Algebra.smul_def, map_smul, LinearEquiv.apply_symm_apply, Pi.smul_apply, smul_eq_mul,
      Module.Basis.equivFun_apply, Module.Basis.equivFun_apply, ← hq k i]
    rfl
  refine ⟨(l : O) ^ (c + (n - c) - n) • x', smul_cancel T (n - c) ?_⟩
  have e5 : (l : O) ^ (n - c) • ((l : O) ^ c • u) = (l : O) ^ (c + (n - c) - n) • ((l : O) ^ n • u) := by
    rw [smul_smul, smul_smul, ← pow_add, ← pow_add]
    congr 2
    omega
  rw [e5, h1, ← hx', TensorProduct.tmul_smul, TensorProduct.tmul_smul, smul_smul,
    smul_smul, mul_comm]

end GlobalTheory.BKGal.Count
