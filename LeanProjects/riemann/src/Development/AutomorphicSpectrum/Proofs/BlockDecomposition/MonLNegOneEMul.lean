import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.NLeA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AlgebraMapConeRing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMulPowEqIncl
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PolyEqPolyEquiv

set_option autoImplicit false
noncomputable section
open CrystallineSemistableComparison.Onto GlobalTheory.CompanionTheory.SurjectionOntoH4

namespace GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis

def allE {n d : ℕ} : Gam n d := ∑ e, oneE e

theorem allE_mem {n d : ℕ} : (allE : Gam n d) ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  unfold allE
  exact AddSubmonoid.sum_mem _ (fun e _ => oneE_mem ∅ e)

theorem allE_apply {n d : ℕ} (e : E n d) : (allE : Gam n d) e = 1 := by
  unfold allE
  rw [Finset.sum_apply]
  simp [oneE, Pi.single_apply]

theorem exists_add_mem {n d : ℕ} (g : Gam n d) :
    ∃ N : ℕ, g + N • allE ∈ (cone ∅ : AddSubmonoid (Gam n d)) := by
  refine ⟨∑ e, (g e).natAbs, ?_⟩
  have hnn : ∀ e, 0 ≤ (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e := by
    intro e
    have h1 : (g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e
        = g e + ((∑ e, (g e).natAbs : ℕ) : ℤ) := by
      change g e + (∑ e, (g e).natAbs) • (allE : Gam n d) e = _
      rw [allE_apply, nsmul_one]
    have h2 : (g e).natAbs ≤ ∑ e, (g e).natAbs :=
      Finset.single_le_sum (f := fun e => (g e).natAbs) (fun i _ => Nat.zero_le _) (Finset.mem_univ e)
    have h3 : ((g e).natAbs : ℤ) ≤ ((∑ e, (g e).natAbs : ℕ) : ℤ) := by exact_mod_cast h2
    rw [h1]
    have h4 := Int.natCast_natAbs (g e)
    have h5 := neg_abs_le (g e)
    linarith
  have key := PolyBij.coe_mem_cone (n := n) (d := d)
    (Finsupp.equivFunOnFinite.symm fun e => ((g + (∑ e, (g e).natAbs) • (allE : Gam n d)) e).toNat)
  convert key using 2
  rename_i e
  exact (Int.toNat_of_nonneg (hnn e)).symm

theorem monL_neg_oneE_mul {K : Type} [Field K] {n d : ℕ} (e : E n d) : monL K (-oneE e) * monL K (oneE e) = 1 := by
  rw [monL, monL, mon_mul]
  change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
  congr 1
  exact Subtype.ext (neg_add_cancel (oneE e))

theorem exists_basis_dl : ∀ {K : Type} [Field K] {n d : ℕ},
    ∃ b : Module.Basis (E n d) (Lr K n d) Ω[Lr K n d⁄K], ∀ e, b e = dl e := by
  intro K _ n d
  have hle : (cone ∅ : AddSubmonoid (Gam n d)) ≤ ⊤ := le_top
  let φ : MvPolynomial (E n d) K →ₐ[K] Lr K n d := (incl (K := K) hle).comp (poly n K ∅)
  letI : Algebra (MvPolynomial (E n d) K) (Lr K n d) := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K (MvPolynomial (E n d) K) (Lr K n d) := IsScalarTower.of_algHom φ
  let s0 : MvPolynomial (E n d) K := (PolyBij.polyEquiv K).symm (mon K (allE : Gam n d) allE_mem)
  have hpe : ∀ a, poly n K ∅ ((PolyBij.polyEquiv (n := n) (d := d) K).symm a) = a := by
    intro a
    rw [PolyBij.poly_eq_polyEquiv, AlgEquiv.coe_toAlgHom, AlgEquiv.apply_symm_apply]
  have e1 : φ s0 = incl (K := K) hle (mon K (allE : Gam n d) allE_mem) := by
    change incl (K := K) hle (poly n K ∅ s0) = _
    rw [hpe]
  have hmul : φ s0 * mon K (-(allE : Gam n d)) (AddSubmonoid.mem_top _) = 1 := by
    rw [e1, incl_mon, mon_mul]
    change AddMonoidAlgebra.single _ (1 : K) = AddMonoidAlgebra.single 0 1
    congr 1
    exact Subtype.ext (add_neg_cancel (allE : Gam n d))
  have hunit : IsUnit (φ s0) := ⟨⟨φ s0, _, hmul, by rw [mul_comm]; exact hmul⟩, rfl⟩
  have hinj : Function.Injective φ :=
    (Away.incl_injective (K := K) hle).comp (PolyBij.poly_bijective (K := K) (n := n) (d := d)).1
  haveI : IsLocalization (Submonoid.powers s0) (Lr K n d) := by
    refine ⟨?_, ?_, ?_⟩
    · intro y
      obtain ⟨k, hk⟩ := (Submonoid.mem_powers_iff _ _).mp y.2
      rw [← hk]
      change IsUnit (φ (s0 ^ k))
      rw [map_pow]
      exact hunit.pow k
    · intro z
      obtain ⟨N, a, ha⟩ := Away.exists_mul_pow_eq_incl (K := K) hle (allE : Gam n d) allE_mem
        (fun g _ => exists_add_mem g) z
      refine ⟨((PolyBij.polyEquiv K).symm a, ⟨s0 ^ N, N, rfl⟩), ?_⟩
      change z * φ (s0 ^ N) = φ ((PolyBij.polyEquiv K).symm a)
      have e2 : φ ((PolyBij.polyEquiv K).symm a) = incl (K := K) hle a := by
        change incl (K := K) hle (poly n K ∅ _) = _
        rw [hpe]
      rw [map_pow, e1, e2, ← map_pow]
      exact ha
    · intro x y hxy
      have hxy' : φ x = φ y := hxy
      exact ⟨1, by rw [hinj hxy']⟩
  let b0 := (KaehlerDifferential.mvPolynomialBasis K (E n d)).ofIsLocalizedModule (Lr K n d)
    (Submonoid.powers s0) (KaehlerDifferential.map K K (MvPolynomial (E n d) K) (Lr K n d))
  let w : E n d → (Lr K n d)ˣ := fun e =>
    ⟨monL K (-oneE e), monL K (oneE e), monL_neg_oneE_mul e, by rw [mul_comm]; exact monL_neg_oneE_mul e⟩
  refine ⟨b0.unitsSMul w, fun e => ?_⟩
  have e4 : KaehlerDifferential.mvPolynomialBasis K (E n d) e
      = KaehlerDifferential.D K (MvPolynomial (E n d) K) (MvPolynomial.X e) :=
    Module.Basis.apply_eq_iff.mpr (by rw [KaehlerDifferential.mvPolynomialBasis_repr_D_X])
  rw [Module.Basis.unitsSMul_apply, Module.Basis.ofIsLocalizedModule_apply, e4, KaehlerDifferential.map_D]
  have e3 : φ (MvPolynomial.X e) = monL K (oneE e) := by
    change incl (K := K) hle (poly n K ∅ (MvPolynomial.X e)) = _
    rw [poly_X, incl_mon]
    rfl
  change monL K (-oneE e) • KaehlerDifferential.D K (Lr K n d) (φ (MvPolynomial.X e)) = dl e
  rw [e3]
  rfl

end GlobalTheory.CompanionTheory.SurjectionOntoH4.OmBasis
