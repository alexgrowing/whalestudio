import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EventuallySubMemPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSmulEqAcrisLatticeImageStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCoordAcrisBcrisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisLpowDvdBoundTeichmullerMonoidStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedActionAcrisTensorSubEventuallyLpowStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisLatticeSubMemPowSmulEventuallyStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemPowSmulLatticeOfCoordDvdStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowSmulMemGaloisStableLatticeQlStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrobeniusPeriodRingInjective
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.CocycleCont

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G]

theorem twact_smul {R : Type} [CommRing R] [Algebra O R] (f : R →ₐ[O] R) (T : LocLat G ℚ_[l] K O) (g : G)
    (r : R) (z : TW R T) : TWact f T g (r • z) = f r • TWact f T g z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem twincl_smul {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem twact_incl (T : LocLat G ℚ_[l] K O) (h : GQ l) (g : G) (z : TW (OCr l O) T) :
    TWact (galOB O h) T g (TWincl (toOB l O) T z) = TWincl (toOB l O) T (TWact (galOCr O h) T g z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => simp [TWact, TWincl, TensorProduct.map_tmul, galOB_toOB]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem natCast_pow_smul {O K : Type} [CommRing O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K]
    (T : LocLat G ℚ_[l] K O) (k : ℕ) (v : T.V) : ((l : O) ^ k) • v = ((l : K) ^ k) • v := by
  rw [← algebraMap_smul K, map_pow, map_natCast]

theorem main_gen {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (s : G →* GQ l) (hs : Continuous s) (T : LocLat G ℚ_[l] K O) (hK : (l : K) ≠ 0)
    (hcont : ∀ (β : TW (OCr l O) T) (m : ℕ), ∀ᶠ g in nhds (1 : G), ∃ γ : TW (OCr l O) T,
      TWact (galOCr O (s g)) T g β - β = ((l : O) ^ m) • γ)
    (hden : ∀ v : T.V, ∃ n : ℕ, ∃ x ∈ T.L.T, x = ((l : O) ^ n) • v)
    (hmem : ∀ (x : ↥T.L.T) (k : ℕ), (∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ k ∣ φ x) →
      ∃ y ∈ T.L.T, (x : T.V) = ((l : O) ^ k) • y)
    (b : TW (OB l O) T) (c : G → T.V) (hc : IsCobOf s T b c) (m : ℕ) :
    ∀ᶠ g in nhds (1 : G), ∃ x ∈ T.L.T, c g = ((l : O) ^ m) • x := by
  obtain ⟨s0, hs0, β, hβ⟩ := GlobalTheory.T.exists_smul_eq_acrisLattice_image T b
  obtain ⟨C, hC⟩ := GlobalTheory.T.acris_lpow_dvd_bound_teichmullerMonoid l (s0 * s0) (by rw [map_mul]; exact mul_ne_zero hs0 hs0)
  set a : Per.Acris l := ainfToAcris l s0 with ha
  set m' := m + C + 1 with hm'
  have h2 : ∀ᶠ g in nhds (1 : G), (l : Per.Acris l) ^ m' ∣ galC (s g) a - a := by
    have h := GlobalTheory.AcrisGal.galC_sub_dvd_mem_nhds l a m'
    rw [← map_one s] at h
    exact hs.continuousAt.preimage_mem_nhds h
  filter_upwards [hcont β m', h2] with g ⟨γ, hγ⟩ ⟨w, hw⟩
  obtain ⟨n, x, hxT, hx⟩ := hden (c g)
  have hcob := hc g n ⟨x, hxT⟩ (by show x = _; rw [hx, ← algebraMap_smul K, map_pow, map_natCast])
  have hconv : ∀ (k : ℕ) (v : T.V), ((l : O) ^ k) • v = ((l : K) ^ k) • v := fun k v => by
    rw [← algebraMap_smul K, map_pow, map_natCast]
  set x' : ↥T.L.T := ⟨x, hxT⟩ with hx'
  set ga : Per.Acris l := galC (s g) a with hga
  set σA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] a with hσA
  set gσA : OCr l O := (1 : O) ⊗ₜ[ℤ_[l]] ga with hgσA
  have hgσA' : galOCr O (s g) σA = gσA := rfl
  set σ : OB l O := toOB l O σA with hσ
  set gσ : OB l O := toOB l O gσA with hgσ
  have hgσ' : galOB O (s g) σ = gσ := by rw [hσ, galOB_toOB, hgσA']
  have hβ' : σ • b = TWincl (toOB l O) T β := hβ
  set gβ := TWact (galOCr O (s g)) T g β with hgβ
  have key1 : gσ • actB s T g b = TWincl (toOB l O) T gβ := by
    rw [actB, ← hgσ', ← twact_smul, hβ', twact_incl]
  have key : (σ * gσ) • ((1 : OB l O) ⊗ₜ[O] x') = TWincl (toOB l O) T (((l : O) ^ n) • (σA • gβ - gσA • β)) := by
    rw [hcob, smul_comm, map_smul, map_sub, twincl_smul, twincl_smul, ← hσ, ← hgσ, smul_sub, mul_smul, key1,
      mul_comm, mul_smul, hβ']
  have hfin : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → ∃ X : Per.Acris l, a * a * algebraMap ℤ_[l] (Per.Acris l) (φ x') =
      (l : Per.Acris l) ^ (n + m') * X - (l : Per.Acris l) ^ m' * (a * w * algebraMap ℤ_[l] (Per.Acris l) (φ x')) := by
    intro φ hφ
    obtain ⟨ΦA, ΦB, hA, hB, h1, hN, hI⟩ := GlobalTheory.T.exists_coord_acris_bcris_alt T φ hφ
    have hσσ : σ * gσ = (1 : O) ⊗ₜ[ℤ_[l]] (acrisToBcris l a * acrisToBcris l ga) := by
      rw [hσ, hgσ, hσA, hgσA]
      simp only [toOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply, Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    have e1 := congrArg ΦB key
    rw [hσσ, hB, h1, hI, hN, map_sub, hA, hA] at e1
    have hΦ : ΦA gβ - ΦA β = (l : Per.Acris l) ^ m' * ΦA γ := by rw [← map_sub, hγ, hN]
    have heq : a * ga * algebraMap ℤ_[l] (Per.Acris l) (φ x') = (l : Per.Acris l) ^ n * (a * ΦA gβ - ga * ΦA β) := by
      have hinj : Function.Injective (acrisToBcris l) := GlobalTheory.MemLoc.PhiInj.algebraMap_acris_bcris_injective l
      apply hinj
      have := e1
      simp only [map_mul, AlgHom.commutes] at this ⊢
      exact this
    refine ⟨a * ΦA γ - w * ΦA β, ?_⟩
    linear_combination heq - (a * algebraMap ℤ_[l] (Per.Acris l) (φ x')) * hw + ((l : Per.Acris l) ^ n * a) * hΦ - ((l : Per.Acris l) ^ n * ΦA β) * hw
  have hdiv : ∀ φ : ↥T.L.T →+ ℤ_[l], (∀ (z : ℤ_[l]) (t : ↥T.L.T), φ (algebraMap ℤ_[l] O z • t) = z * φ t) → (l : ℤ_[l]) ^ (n + m) ∣ φ x' := by
    intro φ hφ
    by_cases hz : φ x' = 0
    · rw [hz]; exact dvd_zero _
    have hspec := PadicInt.unitCoeff_spec hz
    suffices hv : n + m ≤ (φ x').valuation by
      rw [hspec]
      exact Dvd.dvd.mul_left (pow_dvd_pow _ hv) _
    by_contra hlt
    push_neg at hlt
    obtain ⟨X, hX⟩ := hfin φ hφ
    set v := (φ x').valuation
    have hzA : algebraMap ℤ_[l] (Per.Acris l) (φ x') =
        algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]) * (l : Per.Acris l) ^ v := by
      conv_lhs => rw [hspec]
      rw [map_mul, map_pow, map_natCast]
    have hd : (l : Per.Acris l) ^ (min (n + m') (m' + v)) ∣ ainfToAcris l (s0 * s0) * algebraMap ℤ_[l] (Per.Acris l) (φ x') := by
      rw [map_mul, ← ha, hX]
      refine Dvd.dvd.sub (Dvd.dvd.mul_right (pow_dvd_pow _ (min_le_left _ _)) _) ?_
      refine (pow_dvd_pow _ (min_le_right _ _)).trans ?_
      rw [hzA, pow_add]
      exact ⟨a * w * algebraMap ℤ_[l] (Per.Acris l) (PadicInt.unitCoeff hz : ℤ_[l]), by ring⟩
    have := hC (φ x') _ hz hd
    omega
  obtain ⟨y, hyT, hy⟩ := hmem x' (n + m) hdiv
  refine ⟨y, hyT, ?_⟩
  have h3 : ((l : K) ^ n) • c g = ((l : K) ^ n) • (((l : O) ^ m) • y) := by
    rw [← hconv, ← hconv, ← mul_smul, ← pow_add]
    exact hx.symm.trans hy
  exact smul_right_injective T.V (pow_ne_zero n hK) h3

set_option maxHeartbeats 800000 in

theorem cont_at_one : ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (LL : FinExt l) (T : QLat LL) (b : TW (OB l ↥(OL LL)) T) (c : Gl l → T.V), IsCobOf (sQ l) T b c → ∀ m : ℕ, ∀ᶠ g in nhds (1 : Gl l), ∃ x ∈ T.L.T, c g = ((l : ↥LL.1) ^ m) • x := by
  intro l _ _ LL T b c hc m
  have hK : (l : ↥LL.1) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] ↥LL.1)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero)
  refine (main_gen (sQ l) continuous_subtype_val T hK (GlobalTheory.T.twistedAction_acrisTensor_sub_eventually_lpow (sQ l) continuous_subtype_val T ?hT) ?hD
    (GlobalTheory.T.mem_pow_smul_lattice_of_coord_dvd T) b c hc m).mono ?fin
  case fin =>
    rintro g ⟨x, hx, e⟩
    exact ⟨x, hx, e.trans (natCast_pow_smul T m x)⟩
  case hT =>
    intro t ht k
    filter_upwards [GlobalTheory.T.galoisLattice_sub_mem_pow_smul_eventually l LL T t ht k] with g ⟨t', ht', e⟩
    exact ⟨t', ht', e.trans (natCast_pow_smul T k t').symm⟩
  case hD =>
    intro v
    obtain ⟨n, x, hx, e⟩ := GlobalTheory.T.exists_pow_smul_mem_galoisStableLattice_Ql l LL T v
    exact ⟨n, x, hx, e.trans (natCast_pow_smul T n v).symm⟩

end GlobalTheory.CocycleCont
