import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EvalMod
import GroundTheory.PAdicHodge.ExistsGalFixCyclotomicLayerCycloCharNeOne
noncomputable section
open NumberField IsDedekindDomain Neutral.B1 Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
open GlobalTheory.HeckeGal GlobalTheory.Pst GlobalTheory.TripleGal GlobalTheory.CompanionTheory.LTHodge GlobalTheory.CompanionTheory.LTPer
open scoped Classical

namespace GlobalTheory.CompanionTheory.LTPer

theorem finite_units_zpow_eq {F : Type*} [Field F] {d : ℤ} (hd : d ≠ 0) (w : Fˣ) :
    {z : Fˣ | z ^ d = w}.Finite := by
  have hm : 0 < d.natAbs := Int.natAbs_pos.2 hd
  have key : ∀ c : F, {z : Fˣ | (z : F) ^ d.natAbs = c}.Finite := fun c =>
    ((Polynomial.nthRoots d.natAbs c).toFinset.finite_toSet.preimage
      (Units.val_injective (α := F)).injOn).subset fun z hz => by
        simpa [Polynomial.mem_nthRoots hm] using hz
  rcases Int.natAbs_eq d with h | h
  · refine (key (w : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = w
    rw [← Units.val_pow_eq_pow_val, hz']
  · refine (key ((w⁻¹ : Fˣ) : F)).subset fun z hz => ?_
    have hz' : z ^ d = w := hz
    rw [h, zpow_neg, zpow_natCast] at hz'
    change (z : F) ^ d.natAbs = ((w⁻¹ : Fˣ) : F)
    rw [← Units.val_pow_eq_pow_val, ← hz', inv_inv]

theorem eq_one_of_tpow_mul_unit_eigen {l : ℕ} [Fact l.Prime] (L : IntermediateField ℚ_[l] (Om l))
    [FiniteDimensional ℚ_[l] ↥L]
    (hI : ((GroundTheory.PAdicHodge.cycloChar L) ''
        {σ : Gal(Om l/↥L) | ∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w}).Infinite)
    (u : (Formalism.Per6.BdRp l)ˣ) (n : ℕ) (a : Gal(Om l/↥L) → ℚ_[l])
    (hact : ∀ σ : Gal(Om l/↥L), σ • (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)) =
      algebraMap ℚ_[l] (Formalism.Per6.BdRp l) (a σ) * (GroundTheory.PAdicHodge.tBdR l ^ n * (u : Formalism.Per6.BdRp l)))
    (hin : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      a σ = (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])) :
    n = 1 := by
  by_contra hn
  have ht : GroundTheory.PAdicHodge.tBdR l ≠ 0 := (GroundTheory.PAdicHodge.irreducible_tBdR (p := l)).ne_zero
  let c : ℤ_[l]ˣ →* ℚ_[l]ˣ := Units.map (PadicInt.Coe.ringHom (p := l)).toMonoidHom
  have hc : Function.Injective c := fun x y h =>
    Units.ext (Subtype.ext (congrArg Units.val h))
  let χ : Gal(Om l/↥L) → ℚ_[l] := fun σ => (((GroundTheory.PAdicHodge.cycloChar L σ : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l])
  have hχ : ∀ σ, χ σ ≠ 0 := fun σ => (c (GroundTheory.PAdicHodge.cycloChar L σ)).ne_zero
  let A : ℚ_[l] →+* Formalism.Per6.BdRp l := algebraMap ℚ_[l] (Formalism.Per6.BdRp l)
  have hu : ∀ σ : Gal(Om l/↥L), A (χ σ) ^ n * (σ • (u : Formalism.Per6.BdRp l)) = A (a σ) * u := by
    intro σ
    have h := hact σ
    rw [smul_mul', smul_pow', GroundTheory.PAdicHodge.gal_smul_tBdR, mul_pow] at h
    refine mul_left_cancel₀ (pow_ne_zero n ht) ?_
    change _ = _ at h
    linear_combination h
  have hu' : ∀ σ : Gal(Om l/↥L), σ • (u : Formalism.Per6.BdRp l) = A (a σ * (χ σ ^ n)⁻¹) * u := by
    intro σ
    have e : A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n = 1 := by
      rw [← map_pow, ← map_mul, inv_mul_cancel₀ (pow_ne_zero n (hχ σ)), map_one]
    calc σ • (u : Formalism.Per6.BdRp l)
        = (A ((χ σ ^ n)⁻¹) * A (χ σ) ^ n) * (σ • (u : Formalism.Per6.BdRp l)) := by rw [e, one_mul]
      _ = A ((χ σ ^ n)⁻¹) * (A (a σ) * u) := by rw [mul_assoc, hu]
      _ = A (a σ * (χ σ ^ n)⁻¹) * u := by rw [map_mul]; ring
  have hx0 : GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) ≠ 0 :=
    (u.isUnit.map (GroundTheory.PAdicHodge.thetaAlgHom l)).ne_zero
  have hθ : ∀ (σ : Gal(Om l/↥L)) (q : ℚ_[l]),
      σ • (u : Formalism.Per6.BdRp l) = algebraMap ℚ_[l] (Formalism.Per6.BdRp l) q * u →
        σ • GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) =
          algebraMap ℚ_[l] ℂ_[l] q * GroundTheory.PAdicHodge.thetaAlgHom l (u : Formalism.Per6.BdRp l) := by
    intro σ q h
    rw [GroundTheory.PAdicHodge.thetaAlgHom_apply, ← GroundTheory.PAdicHodge.thetaBDeRhamPlusField_gal_smul, h,
      ← GroundTheory.PAdicHodge.thetaAlgHom_apply, map_mul, AlgHom.commutes]
    rfl
  obtain ⟨ψ, hψc, hψx⟩ := GroundTheory.PAdicHodge.EigenChar.exists_eigenChar hx0
    fun σ : Gal(Om l/↥L) => ⟨_, hθ σ _ (hu' σ)⟩
  have hfin := GroundTheory.PAdicHodge.ACris.senTateCharacters (p := l) L ψ hψc _ hx0 hψx
  have hd : (1 - (n : ℤ)) ≠ 0 := fun h => hn (by omega)
  have hψ : ∀ σ : Gal(Om l/↥L), (∀ w ∈ GroundTheory.PAdicHodge.unramifiedClosure l, σ w = w) →
      (c (GroundTheory.PAdicHodge.cycloChar L σ)) ^ (1 - (n : ℤ)) = ψ σ := by
    intro σ hσ
    have h2 : a σ * (χ σ ^ n)⁻¹ = ψ σ := GroundTheory.PAdicHodge.EigenChar.eq_of_mul_eq hx0
      ((hθ σ _ (hu' σ)).symm.trans (hψx σ))
    refine Units.ext ?_
    rw [Units.val_zpow_eq_zpow_val, ← h2, hin σ hσ]
    change χ σ ^ (1 - (n : ℤ)) = χ σ * (χ σ ^ n)⁻¹
    rw [zpow_sub₀ (hχ σ), zpow_one, zpow_natCast, div_eq_mul_inv]
  refine (hI.image hc.injOn) (Set.Finite.of_finite_fibers (fun z => z ^ (1 - (n : ℤ))) ?_ ?_)
  · refine hfin.subset ?_
    rintro _ ⟨_, ⟨_, ⟨σ, hσ, rfl⟩, rfl⟩, rfl⟩
    exact ⟨σ, hσ, (hψ σ hσ).symm⟩
  · intro w _
    refine (finite_units_zpow_eq hd w).subset fun z hz => ?_
    exact hz.2

end GlobalTheory.CompanionTheory.LTPer
