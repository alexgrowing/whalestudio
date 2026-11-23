import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoeffRingsHaveRootsOfUnity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralIdempotentsSimpleFDRepFiniteFinsumEqOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SimpleRepCentralIdempotentIsCentralIdempotent
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.L2 NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module Polynomial GlobalTheory.Pass GlobalTheory.PendOf

noncomputable section

namespace GlobalTheory.PrimCentIdem

open CategoryTheory

variable {Γ : Type} [Group Γ] [Fintype Γ]

theorem eq_sum_single (e : MonoidAlgebra ℂ Γ) : e = ∑ q : Γ, MonoidAlgebra.single q (e.coeff q) := by
  classical
  ext x
  simp [MonoidAlgebra.coeff_sum, Finset.sum_apply', Finsupp.single_apply]

theorem coeff_mul_fin (a b : MonoidAlgebra ℂ Γ) (x : Γ) :
    (a * b).coeff x = ∑ q, a.coeff q * b.coeff (q⁻¹ * x) := by
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
  intro q; simp

theorem exists_scalar (e : MonoidAlgebra ℂ Γ) (he : ∀ w, e * w = w * e) (ρ : FDRep ℂ Γ) [Simple ρ] :
    ∃ c : ℂ, ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v := by
  let T : ρ →ₗ[ℂ] ρ := ∑ q : Γ, e.coeff q • ρ.ρ q
  have hTA : T = Representation.asAlgebraHom ρ.ρ e := by
    conv_rhs => rw [eq_sum_single e]
    simp only [T, map_sum, Representation.asAlgebraHom_single]
  have hcomm : ∀ h : Γ, ∀ v : ρ, T (ρ.ρ h v) = ρ.ρ h (T v) := by
    intro h v
    have h1 : Representation.asAlgebraHom ρ.ρ (e * MonoidAlgebra.single h 1) = Representation.asAlgebraHom ρ.ρ (MonoidAlgebra.single h 1 * e) := by
      rw [he]
    rw [map_mul, map_mul, Representation.asAlgebraHom_single, one_smul] at h1
    rw [hTA]
    exact LinearMap.congr_fun h1 v
  let f' : ρ ⟶ ρ := ⟨FGModuleCat.ofHom T, fun g => by
    ext v
    exact hcomm g v⟩
  obtain ⟨c, hc⟩ := CategoryTheory.endomorphism_simple_eq_smul_id ℂ f'
  refine ⟨c, fun v => ?_⟩
  have := congrArg (fun φ : ρ ⟶ ρ => φ.hom.hom v) hc
  exact this.symm

theorem mul_zIdem_eq_smul (e : MonoidAlgebra ℂ Γ) (ρ : FDRep ℂ Γ) (c : ℂ)
    (hc : ∀ v : ρ, (∑ q : Γ, e.coeff q • ρ.ρ q) v = c • v) :
    e * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ = c • Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  ext x
  rw [coeff_mul_fin, MonoidAlgebra.coeff_smul_apply, smul_eq_mul]
  simp only [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  have hT : (∑ q : Γ, e.coeff q • ρ.ρ q) = c • (1 : Module.End ℂ ρ) := LinearMap.ext fun v => by simp [hc v]
  have h1 : ∀ q : Γ, ρ.ρ (q⁻¹ * x)⁻¹ = ρ.ρ x⁻¹ * ρ.ρ q := fun q => by rw [mul_inv_rev, inv_inv, map_mul]
  have h2 : ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) =
      LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ∑ q : Γ, e.coeff q • ρ.ρ q) := by
    simp only [Finset.mul_sum, mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  have h3 : ∑ q : Γ, e.coeff q * ((Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * LinearMap.trace ℂ ρ (ρ.ρ (q⁻¹ * x)⁻¹)) =
      (Module.finrank ℂ ρ : ℂ) / Fintype.card Γ * ∑ q : Γ, e.coeff q * LinearMap.trace ℂ ρ (ρ.ρ x⁻¹ * ρ.ρ q) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [h1]; ring
  rw [h3, h2, hT, mul_smul_comm, mul_one, map_smul, smul_eq_mul]
  ring

end GlobalTheory.PrimCentIdem

open GlobalTheory.PrimCentIdem in
theorem GlobalTheory.PrimCentIdem.main : ∀ (g a : ℕ) [Fact g.Prime] (L : PairedCharacterCondition.LzData g) (τ : L.Irr a),
    ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧ L.idem τ = Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ := by
  intro g a _ L τ
  classical
  obtain ⟨hfin, hsum⟩ := GlobalTheory.SerOSys.zIdem_finite_and_finsum_eq_one (GL (Fin a) (ZMod g))
  have hex : ∃ ρ : FDRep ℂ (GL (Fin a) (ZMod g)), CategoryTheory.Simple ρ ∧
      L.idem τ * Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ ≠ 0 := by
    by_contra hno
    push_neg at hno
    apply L.idem_ne τ
    rw [← mul_one (L.idem τ), ← hsum, finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum]
    refine Finset.sum_eq_zero fun z hz => ?_
    obtain ⟨ρ, hρ, rfl⟩ := (Set.Finite.mem_toFinset hfin).1 hz
    exact hno ρ hρ
  obtain ⟨ρ, hρ, hne⟩ := hex
  haveI := hρ
  refine ⟨ρ, hρ, ?_⟩
  set e := L.idem τ with he_def
  set z := Formalism.IrreducibleCountingLemmas.TYPES.zIdem ρ with hz_def
  have hzz : z * z = z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).1
  have hee : e * e = e := L.idem_idem τ
  have hec : ∀ w, e * w = w * e := L.idem_central τ
  have hzc : ∀ w, z * w = w * z := (GlobalTheory.SerOSys.zIdem_centralIdempotent ρ hρ).2
  obtain ⟨c, hc⟩ := exists_scalar e hec ρ
  have hmul : e * z = c • z := mul_zIdem_eq_smul e ρ c hc
  have hze : z * e = e * z := hzc e
  have hprim := L.idem_prim τ (e * z)
    (calc e * z * (e * z) = e * (z * e) * z := by simp only [mul_assoc]
      _ = e * (e * z) * z := by rw [hze]
      _ = (e * e) * (z * z) := by simp only [mul_assoc]
      _ = e * z := by rw [hee, hzz])
    (fun w => calc e * z * w = e * (z * w) := mul_assoc _ _ _
      _ = e * (w * z) := by rw [hzc w]
      _ = (e * w) * z := (mul_assoc _ _ _).symm
      _ = (w * e) * z := by rw [hec w]
      _ = w * (e * z) := mul_assoc _ _ _)
    (show e * z * e = e * z from calc e * z * e = e * (z * e) := mul_assoc _ _ _
      _ = e * (e * z) := by rw [hze]
      _ = (e * e) * z := (mul_assoc _ _ _).symm
      _ = e * z := by rw [hee])
  have hez : e * z = e := hprim.resolve_left hne
  have hcz : c • z ≠ 0 := hmul ▸ hne
  have hc0 : c ≠ 0 := fun h => hcz (by rw [h, zero_smul])
  have hz0 : z ≠ 0 := fun h => hcz (by rw [h, smul_zero])
  have hidem : (c * c - c) • z = 0 := by
    have h1 : (c • z) * (c • z) = c • z := by rw [← hmul, hez, hee]
    rw [smul_mul_smul_comm, hzz] at h1
    rw [sub_smul, h1, sub_self]
  have hcc : c * c - c = 0 := (smul_eq_zero.1 hidem).resolve_right hz0
  have hc1 : c = 1 := by
    have : c * (c - 1) = 0 := by rw [mul_sub, mul_one]; exact hcc
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h hc0
    · exact sub_eq_zero.1 h
  rw [← hez, hmul, hc1, one_smul]
