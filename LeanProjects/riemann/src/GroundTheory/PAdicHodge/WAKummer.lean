import Mathlib
import GroundTheory.PAdicHodge.WAKummerBCris
set_option maxSynthPendingDepth 1

noncomputable section

open _root_.WittVector IsLocalRing

namespace GroundTheory.PAdicHodge

namespace ACris

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝒪" => normInteger ℂ_[p]
local notation "𝒪♭" => PreTilt (normInteger ℂ_[p]) p
local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {K : IntermediateField ℚ_[p] (PadicAlgCl p)}

section Abstract

variable {R : Type*} [CommRing R]

omit hp in

theorem map_sub_sum_eq_of_eq (F : R →+* R) {n : ℕ} (a L : Fin n → R) (ha : ∀ i, F (a i) = a i)
    (hL : ∀ i, F (L i) = (p : R) * L i) {y : R} (hy : F y = (p : R) * y) :
    F (y - ∑ i, a i * L i) = (p : R) * (y - ∑ i, a i * L i) := by
  rw [map_sub, map_sum, hy, mul_sub, Finset.mul_sum]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by rw [map_mul, ha, hL]; ring

theorem eq_sum_of_sub_sum_eq (A : ℚ_[p] →+* R) (hA : Function.Injective A) (g : R →+* R)
    (hgA : ∀ q, g (A q) = A q) {t : R} (ht : IsUnit t) {χ c : ℚ_[p]} (hgt : g t = A χ * t)
    {y : R} (hy : g y - y = A c * t) {n : ℕ} (f κ : Fin n → ℚ_[p]) (L : Fin n → R)
    (hgL : ∀ i, g (L i) = L i + A (κ i) * t) {l : ℚ_[p]}
    (hl : y - ∑ i, A (f i) * L i = A l * t) : c = ∑ i, f i * κ i + l * (χ - 1) := by
  have h1 : g (y - ∑ i, A (f i) * L i) - (y - ∑ i, A (f i) * L i) =
      A (c - ∑ i, f i * κ i) * t := by
    have e : ∀ i, g (A (f i) * L i) = A (f i) * L i + A (f i * κ i) * t := fun i => by
      rw [map_mul, hgA, hgL, map_mul]; ring
    rw [map_sub g, map_sum g, Finset.sum_congr rfl fun i _ => e i, Finset.sum_add_distrib, map_sub A,
      map_sum A, sub_mul, Finset.sum_mul]
    linear_combination hy
  have h2 : g (y - ∑ i, A (f i) * L i) - (y - ∑ i, A (f i) * L i) = A (l * (χ - 1)) * t := by
    rw [hl, map_mul, hgA, hgt, map_mul, map_sub, map_one]
    ring
  have h3 : A ((c - ∑ i, f i * κ i) - l * (χ - 1)) * t = 0 := by
    rw [map_sub]
    linear_combination h1.symm.trans h2
  have h4 := ht.mul_left_eq_zero.1 h3
  rw [← map_zero A] at h4
  linear_combination hA h4

end Abstract

set_option maxHeartbeats 4000000 in

theorem exists_phiB_eq_of_galB_sub_eq [FiniteDimensional ℚ_[p] K] {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    (c : Gal(PadicAlgCl p/K) → ℚ_[p]) {u : BCris hε}
    (hu : ∀ σ, galB hε σ u - u = algebraMap ℚ_[p] (BCris hε) (c σ) * periodTCris hε) :
    ∃ y : BCris hε, phiB hε y = (p : BCris hε) * y ∧
      ∀ σ, galB hε σ y - y = algebraMap ℚ_[p] (BCris hε) (c σ) * periodTCris hε := by
  have hper : ∀ μ : BCris hε, (∀ σ : Gal(PadicAlgCl p/K), galB hε σ μ = μ) →
      ∃ n d, 0 < d ∧ (phiB hε)^[n + d] μ = (phiB hε)^[n] μ := by
    intro μ hμ
    obtain ⟨k, -, hk⟩ := bCris_fixed_mem_maxUnramified hε hζ μ hμ
    let ιA : BCris hε →ₐ[ℚ_[p]] 𝔹dR :=
      { toRingHom := iotaB hε hζ, commutes' := iotaB_algebraMap_padic hε hζ }
    let φA : BCris hε →ₐ[ℚ_[p]] BCris hε :=
      { toRingHom := phiB hε, commutes' := phiB_algebraMap_padic' hε }
    have halg : IsAlgebraic ℚ_[p] (ιA μ) := by
      change IsAlgebraic ℚ_[p] (iotaB hε hζ μ)
      rw [hk]
      exact (Algebra.IsAlgebraic.isAlgebraic k).algHom
        ((IsScalarTower.toAlgHom ℚ_[p] 𝔹 𝔹dR).comp (algClToBdR p))
    exact exists_iterate_eq_of_algebraic ιA (iotaB_injective hε hζ) φA halg
  exact exists_eq_p_mul_of_sub_eq (phiB hε) (phiB_algebraMap_padic' hε)
    (fun σ : Gal(PadicAlgCl p/K) => galB hε σ) (fun σ q => galB_algebraMap_padic hε σ q)
    (fun σ x => (phiB_galB hε σ x).symm) (phiB_periodTCris hε) hper c hu

set_option maxHeartbeats 16000000 in

theorem exists_iotaB_eq_uBdR_add [FiniteDimensional ℚ_[p] K] {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    {u : BCris hε}
    (hu : ∀ σ : Gal(PadicAlgCl p/K), galB hε σ u - u =
      algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε) :
    ∃ k : K, iotaB hε hζ u = algebraMap 𝔹 𝔹dR (uBdR p + algClToBdR p k) := by
  have hιt : iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (fontaineT ε hε) :=
    (iotaB_periodTCris hε hζ).trans (congrArg _ (iota_periodT hε))
  have hιA : ∀ q : ℚ_[p], iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) q) =
      algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 q) := fun q =>
    (iotaB_algebraMap_padic hε hζ q).trans (IsScalarTower.algebraMap_apply ℚ_[p] 𝔹 𝔹dR q)
  have hfixw : ∀ σ : Gal(PadicAlgCl p/K), σ • (iotaB hε hζ u - algebraMap 𝔹 𝔹dR (uBdR p)) =
      iotaB hε hζ u - algebraMap 𝔹 𝔹dR (uBdR p) := by
    intro σ
    have hgy : galB hε σ u = u + algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) *
        periodTCris hε := by
      linear_combination hu σ
    have h1 : σ • iotaB hε hζ u = iotaB hε hζ u + algebraMap 𝔹 𝔹dR
        (algebraMap ℚ_[p] 𝔹 (kummerC hε hζ σ : ℚ_[p]) * fontaineT ε hε) := by
      rw [← iotaB_galB, hgy, map_add, map_mul, hιA, hιt, map_mul]
    have h2 : σ • algebraMap 𝔹 𝔹dR (uBdR p) = algebraMap 𝔹 𝔹dR (uBdR p) + algebraMap 𝔹 𝔹dR
        (algebraMap ℚ_[p] 𝔹 (kummerC hε hζ σ : ℚ_[p]) * fontaineT ε hε) := by
      rw [gal_smul_algebraMap_bDeRham, gal_smul_uBdR_eq hε hζ σ, map_add]
    rw [smul_sub, h1, h2]
    ring
  obtain ⟨k, hk⟩ := bDeRham_fixed K _ hfixw
  rw [algebraMap_intermediateField_bDeRham] at hk
  refine ⟨k, ?_⟩
  rw [map_add]
  linear_combination -hk

set_option maxHeartbeats 4000000 in

theorem exists_eq_mul_periodTCris {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCris hε}
    (hφ : phiB hε y = (p : BCris hε) * y) {b : 𝔹} (hιy : iotaB hε hζ y = algebraMap 𝔹 𝔹dR b)
    (hθb : thetaAlgHom p b = 0) :
    ∃ l : ℚ_[p], y = algebraMap ℚ_[p] (BCris hε) l * periodTCris hε := by
  have : IsDomain (BCris hε) := isDomain_bCris hε hζ
  have hιt : iotaB hε hζ (periodTCris hε) = algebraMap 𝔹 𝔹dR (fontaineT ε hε) :=
    (iotaB_periodTCris hε hζ).trans (congrArg _ (iota_periodT hε))
  have hbm : b ∈ maximalIdeal 𝔹 := by
    rw [IsPerfectoidField.maximalIdeal_bDeRhamPlus, RingHom.mem_ker, ← thetaAlgHom_apply]
    exact hθb
  rw [maximalIdeal_eq_span_fontaineT hε hζ, Ideal.mem_span_singleton'] at hbm
  obtain ⟨a, ha⟩ := hbm
  have htu := isUnit_periodTCris hε
  obtain ⟨z, hz⟩ : ∃ z, z = y * ↑htu.unit⁻¹ := ⟨_, rfl⟩
  have hzt : z * periodTCris hε = y := by rw [hz, mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hpu : IsUnit ((p : BCris hε) * periodTCris hε) := by
    refine IsUnit.mul ?_ htu
    have e : (p : BCris hε) = algebraMap ℚ_[p] (BCris hε) (p : ℚ_[p]) := by rw [map_natCast]
    rw [e]
    exact (isUnit_iff_ne_zero.2 (by exact_mod_cast hp.out.ne_zero : (p : ℚ_[p]) ≠ 0)).map _
  have hφz : phiB hε z = z := by
    apply hpu.mul_right_cancel
    have e : phiB hε z * phiB hε (periodTCris hε) = phiB hε y := by rw [← map_mul, hzt]
    have hφt : phiB hε (periodTCris hε) = (p : BCris hε) * periodTCris hε := phiB_periodTCris hε
    linear_combination e + hφ - phiB hε z * hφt - (p : BCris hε) * hzt
  have hιz : iotaB hε hζ z = algebraMap 𝔹 𝔹dR a := by
    have hιt0 : iotaB hε hζ (periodTCris hε) ≠ 0 := by
      rw [hιt]
      exact fun h => fontaineT_ne_zero hε hζ
        (IsFractionRing.injective 𝔹 𝔹dR (h.trans (map_zero _).symm))
    apply mul_right_cancel₀ hιt0
    have e1 : iotaB hε hζ z * iotaB hε hζ (periodTCris hε) = iotaB hε hζ y := by rw [← map_mul, hzt]
    have e2 : algebraMap 𝔹 𝔹dR b = algebraMap 𝔹 𝔹dR a * algebraMap 𝔹 𝔹dR (fontaineT ε hε) := by
      rw [← ha, map_mul]
    linear_combination e1 + hιy + e2 - algebraMap 𝔹 𝔹dR a * hιt
  obtain ⟨l, hl⟩ := (iotaB_mem_range_iff hε hζ hφz).1 ⟨a, hιz.symm⟩
  exact ⟨l, by rw [← hzt, hl]⟩

set_option maxHeartbeats 8000000 in

theorem exists_iotaB_sub_sum_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {y : BCris hε} {k : PadicAlgCl p}
    (hk : iotaB hε hζ y = algebraMap 𝔹 𝔹dR (uBdR p + algClToBdR p k)) {n : ℕ} (f : Fin n → ℚ_[p])
    (g : Fin n → PadicAlgCl p) (hfg : ∑ i, f i • g i = k) (x : Fin n → 𝒪♭)
    (hx : ∀ i, PreTilt.untilt (x i) - 1 ∈ Ideal.span {(p : 𝒪)})
    (hθ : ∀ i, ((theta ℂ_[p] p (logTeich (hx i)) : 𝒪) : ℂ_[p]) = ((g i : PadicAlgCl p) : ℂ_[p])) :
    ∃ b : 𝔹, iotaB hε hζ (y - ∑ i, algebraMap ℚ_[p] (BCris hε) (f i) * logTeichB hε (hx i)) =
      algebraMap 𝔹 𝔹dR b ∧ thetaAlgHom p b = 0 := by
  refine ⟨uBdR p + algClToBdR p k -
    ∑ i, algebraMap ℚ_[p] 𝔹 (f i) * iota ℂ_[p] p (logTeich (hx i)), ?_, ?_⟩
  · have hterm : ∀ i, iotaB hε hζ (algebraMap ℚ_[p] (BCris hε) (f i) * logTeichB hε (hx i)) =
        algebraMap 𝔹 𝔹dR (algebraMap ℚ_[p] 𝔹 (f i) * iota ℂ_[p] p (logTeich (hx i))) := fun i => by
      rw [map_mul, iotaB_algebraMap_padic, IsScalarTower.algebraMap_apply ℚ_[p] 𝔹 𝔹dR, logTeichB,
        iotaB_algebraMap, iotaPlus_algebraMap, map_mul]
    rw [map_sub, map_sum, hk, Finset.sum_congr rfl fun i _ => hterm i, ← map_sum, ← map_sub]
  · have h1 : thetaAlgHom p (uBdR p) = 0 := by
      rw [thetaAlgHom_apply, ← RingHom.mem_ker, ← IsPerfectoidField.maximalIdeal_bDeRhamPlus]
      exact uBdR_mem
    have h2 : ∀ i, thetaAlgHom p (algebraMap ℚ_[p] 𝔹 (f i) * iota ℂ_[p] p (logTeich (hx i))) =
        algebraMap ℚ_[p] ℂ_[p] (f i) * ((g i : PadicAlgCl p) : ℂ_[p]) := fun i => by
      rw [map_mul, AlgHom.commutes, thetaAlgHom_apply, thetaField_iota, hθ]
    have h3 : ((k : PadicAlgCl p) : ℂ_[p]) =
        ∑ i, algebraMap ℚ_[p] ℂ_[p] (f i) * ((g i : PadicAlgCl p) : ℂ_[p]) := by
      rw [← hfg, coe_padicAlgCl_eq, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, coe_padicAlgCl_eq]
    rw [map_sub, map_add, h1, thetaAlgHom_algClToBdR, map_sum,
      Finset.sum_congr rfl fun i _ => h2 i, h3, zero_add, sub_self]

set_option maxHeartbeats 8000000 in

theorem eq_sum_kummerCocycle_of_sub_sum_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (c : Gal(PadicAlgCl p/K) → ℚ_[p])
    {y : BCris hε}
    (hy : ∀ σ, galB hε σ y - y = algebraMap ℚ_[p] (BCris hε) (c σ) * periodTCris hε)
    {n : ℕ} (f : Fin n → ℚ_[p]) (x : Fin n → 𝒪♭) (hx0 : ∀ i, x i ≠ 0)
    (hfix : ∀ i, ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]))
    (hx : ∀ i, PreTilt.untilt (x i) - 1 ∈ Ideal.span {(p : 𝒪)}) (l : ℚ_[p])
    (hl : y - ∑ i, algebraMap ℚ_[p] (BCris hε) (f i) * logTeichB hε (hx i) =
      algebraMap ℚ_[p] (BCris hε) l * periodTCris hε) (σ : Gal(PadicAlgCl p/K)) :
    c σ = ∑ i, f i * (kummerCocycle hε hζ (hx0 i) (hfix i) σ : ℚ_[p]) +
      l * (((cycloChar K σ : ℤ_[p]) : ℚ_[p]) - 1) := by
  have : IsDomain (BCris hε) := isDomain_bCris hε hζ
  exact eq_sum_of_sub_sum_eq (algebraMap ℚ_[p] (BCris hε)) (algebraMap ℚ_[p] (BCris hε)).injective
    (galB hε σ) (galB_algebraMap_padic hε σ) (isUnit_periodTCris hε) (galB_periodTCris hε hζ σ) (hy σ)
    f (fun i => (kummerCocycle hε hζ (hx0 i) (hfix i) σ : ℚ_[p])) (fun i => logTeichB hε (hx i))
    (fun i => galB_logTeichB hε hζ (hx0 i) (hfix i) (hx i) σ) hl

set_option maxHeartbeats 4000000 in

theorem not_forall_galB_sub_eq_kummerC [FiniteDimensional ℚ_[p] K] {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    (u : BCris hε) :
    ¬ ∀ σ : Gal(PadicAlgCl p/K), galB hε σ u - u =
      algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε := by
  intro hu
  obtain ⟨y, hφy, hy⟩ := exists_phiB_eq_of_galB_sub_eq hε hζ (fun σ => (kummerC hε hζ σ : ℚ_[p])) hu
  obtain ⟨k, hk⟩ := exists_iotaB_eq_uBdR_add hε hζ hy
  obtain ⟨n, f, g, hfg⟩ := Submodule.mem_span_set'.1 (mem_span_thetaLogSet (K := K) k.2)
  choose x hx hrest using fun i => (g i).2.2
  have hx0 : ∀ i, x i ≠ 0 := fun i => (hrest i).1
  have hfix : ∀ i, ∀ σ : Gal(PadicAlgCl p/K),
      σ • ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]) = ((PreTilt.untilt (x i) : 𝒪) : ℂ_[p]) :=
    fun i => (hrest i).2.1
  have hθ : ∀ i, ((theta ℂ_[p] p (logTeich (hx i)) : 𝒪) : ℂ_[p]) =
      ((g i : PadicAlgCl p) : ℂ_[p]) := fun i => (hrest i).2.2
  have hφy' : phiB hε (y - ∑ i, algebraMap ℚ_[p] (BCris hε) (f i) * logTeichB hε (hx i)) =
      (p : BCris hε) * (y - ∑ i, algebraMap ℚ_[p] (BCris hε) (f i) * logTeichB hε (hx i)) := by
    exact map_sub_sum_eq_of_eq (phiB hε) (fun i => algebraMap ℚ_[p] (BCris hε) (f i))
      (fun i => logTeichB hε (hx i)) (fun i => phiB_algebraMap_padic' hε (f i))
      (fun i => phiB_logTeichB hε (hx i)) hφy
  obtain ⟨b, hιb, hθb⟩ := exists_iotaB_sub_sum_eq hε hζ hk f (fun i => (g i : PadicAlgCl p)) hfg x hx hθ
  obtain ⟨l, hl⟩ := exists_eq_mul_periodTCris hε hζ hφy' hιb hθb
  exact false_of_kummerC_eq hε hζ f l x hx0 hfix (fun i => norm_eq_one_of_sub_one_mem (hx i))
    (eq_sum_kummerCocycle_of_sub_sum_eq hε hζ _ hy f x hx0 hfix hx l hl)

set_option maxHeartbeats 1600000 in

theorem not_forall_galB_sub_eq_neg_kummerC [FiniteDimensional ℚ_[p] K] {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1) (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1)
    (u : BCris hε) :
    ¬ ∀ σ : Gal(PadicAlgCl p/K), galB hε σ u - u =
      -(algebraMap ℚ_[p] (BCris hε) (kummerC hε hζ σ : ℚ_[p]) * periodTCris hε) := by
  intro hu
  refine not_forall_galB_sub_eq_kummerC (K := K) hε hζ (-u) fun σ => ?_
  have e := map_neg (galB hε σ) u
  linear_combination e - hu σ

end ACris

end GroundTheory.PAdicHodge
