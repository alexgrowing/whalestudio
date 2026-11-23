import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import GroundTheory.AutomorphicForms.ReductionFinite
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicMinkowskiExistsShortRationalVectorStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

noncomputable section

namespace GlobalTheory.QSA.FujisakiQ

variable {R : Type*} [CommRing R] {a b : R}

def ofCoords (v : Fin 4 → R) : ℍ[R, a, b] := ⟨v 0, v 1, v 2, v 3⟩

theorem coords_ofCoords (v : Fin 4 → R) : coords (ofCoords v : ℍ[R, a, b]) = v := by
  ext i; fin_cases i <;> rfl

theorem ofCoords_coords (x : ℍ[R, a, b]) : ofCoords (coords x) = x := by
  ext <;> rfl

def lmat (w : ℍ[R, a, b]) : Matrix (Fin 4) (Fin 4) R :=
  !![w.re, a * w.imI, b * w.imJ, -(a * b) * w.imK;
     w.imI, w.re, b * w.imK, -(b * w.imJ);
     w.imJ, -(a * w.imK), w.re, a * w.imI;
     w.imK, -w.imJ, w.imI, w.re]

theorem lmat_mulVec (w v : ℍ[R, a, b]) : lmat w *ᵥ coords v = coords (w * v) := by
  ext i; fin_cases i <;>
    simp [lmat, coords, Matrix.mulVec, dotProduct, Fin.sum_univ_four] <;> ring

theorem det_lmat (w : ℍ[R, a, b]) : (lmat w).det = nrm w ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp [lmat, Fin.sum_univ_succ, Matrix.det_fin_three, nrm]
  have h1 : (Fin.succAbove 1 2 : Fin 4) = 3 := by decide
  have h2 : (Fin.succAbove 2 2 : Fin 4) = 3 := by decide
  have h3 : (Fin.succAbove 3 2 : Fin 4) = 2 := by decide
  simp [h1, h2, h3]
  ring

theorem nrm_smul (t : R) (x : ℍ[R, a, b]) : nrm (t • x) = t ^ 2 * nrm x := by
  simp [nrm]; ring

theorem nrm_star (x : ℍ[R, a, b]) : nrm (star x) = nrm x := by
  simp [nrm]

theorem star_mul_eq (x : ℍ[R, a, b]) : star x * x = algebraMap R ℍ[R, a, b] (nrm x) := by
  ext <;> simp [nrm, QuaternionAlgebra.algebraMap_eq] <;> ring

theorem mul_inv_of_unit (x : ℍ[R, a, b]) (u : Rˣ) (hu : (u : R) = nrm x) :
    x * (((u⁻¹ : Rˣ) : R) • star x) = 1 ∧ (((u⁻¹ : Rˣ) : R) • star x) * x = 1 := by
  constructor
  · rw [mul_smul_comm, mul_star_eq, ← hu, Algebra.algebraMap_eq_smul_one, smul_smul,
      Units.inv_mul, one_smul]
  · rw [smul_mul_assoc, star_mul_eq, ← hu, Algebra.algebraMap_eq_smul_one, smul_smul,
      Units.inv_mul, one_smul]

variable [TopologicalSpace R] [IsTopologicalRing R]

theorem continuous_coord (i : Fin 4) : Continuous fun x : ℍ[R, a, b] => coords x i :=
  (continuous_apply i).comp continuous_induced_dom

@[fun_prop] theorem continuous_re : Continuous fun x : ℍ[R, a, b] => x.re := continuous_coord 0
@[fun_prop] theorem continuous_imI : Continuous fun x : ℍ[R, a, b] => x.imI := continuous_coord 1
@[fun_prop] theorem continuous_imJ : Continuous fun x : ℍ[R, a, b] => x.imJ := continuous_coord 2
@[fun_prop] theorem continuous_imK : Continuous fun x : ℍ[R, a, b] => x.imK := continuous_coord 3

theorem continuous_ofCoords : Continuous (ofCoords : (Fin 4 → R) → ℍ[R, a, b]) :=
  continuous_induced_rng.2 (by
    have : (coords ∘ (ofCoords : (Fin 4 → R) → ℍ[R, a, b])) = id := funext coords_ofCoords
    rw [this]; exact continuous_id)

theorem continuous_star' : Continuous (star : ℍ[R, a, b] → ℍ[R, a, b]) := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_mul' : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => p.1 * p.2 := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_star_mul : Continuous fun p : ℍ[R, a, b] × ℍ[R, a, b] => star p.1 * p.2 := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

theorem continuous_const_mul' (c : ℍ[R, a, b]) : Continuous fun u : ℍ[R, a, b] => c * u := by
  refine continuous_induced_rng.2 (continuous_pi fun i => ?_)
  fin_cases i <;> simp [coords, Function.comp_def] <;> fun_prop

end GlobalTheory.QSA.FujisakiQ

namespace GlobalTheory.QSA.FujisakiQ

variable {F : Type} [Field F] [NumberField F] {a b : F}

theorem rat_mul (x y : ℍ[F, a, b]) : rat (x * y) = rat x * rat y := by
  ext <;> simp [rat]

theorem rat_star (x : ℍ[F, a, b]) : rat (star x) = star (rat x) := by
  ext <;> simp [rat]

theorem rat_one : rat (1 : ℍ[F, a, b]) = 1 := by
  ext <;> simp [rat]

theorem coords_rat (x : ℍ[F, a, b]) :
    coords (rat x) = fun i => algebraMap F (AF F) (coords x i) := by
  ext i; fin_cases i <;> rfl

theorem rat_inv (x : ℍ[F, a, b]) (hx : nrm x ≠ 0) :
    x * ((nrm x)⁻¹ • star x) = 1 ∧ ((nrm x)⁻¹ • star x) * x = 1 :=
  mul_inv_of_unit x (Units.mk0 (nrm x) hx) rfl

theorem exists_rat_mem (B : Set (Fin 4 → AF F))
    (hB : ∀ g : Matrix (Fin 4) (Fin 4) (AF F), IsUnit g.det → (∃ u : (AF F)ˣ, (u : AF F) = g.det ∧
      (GroundTheory.Global.IdeleGroup.ideleModule F u : ℝ) ≤ 1) →
      ∃ ξ : Fin 4 → F, ξ ≠ 0 ∧ g *ᵥ (fun i => algebraMap F (AF F) (ξ i)) ∈ B)
    (hdiv : ∀ x : ℍ[F, a, b], nrm x = 0 → x = 0)
    (w : DA F a b) (u : (AF F)ˣ) (hu : (u : AF F) = nrm w)
    (hmod : GroundTheory.Global.IdeleGroup.ideleModule F u = 1) :
    ∃ δ : ℍ[F, a, b], nrm δ ≠ 0 ∧ w * rat δ ∈ ofCoords '' B := by
  have hdet : (lmat w).det = ((u ^ 2 : (AF F)ˣ) : AF F) := by rw [det_lmat, Units.val_pow_eq_pow_val, hu]
  obtain ⟨ξ, hξ0, hξ⟩ := hB (lmat w) (by rw [hdet]; exact Units.isUnit _)
    ⟨u ^ 2, hdet.symm, by rw [map_pow, hmod, one_pow]; simp⟩
  let δ : ℍ[F, a, b] := ofCoords ξ
  refine ⟨δ, fun h => hξ0 ?_, ⟨lmat w *ᵥ coords (rat δ), ?_, ?_⟩⟩
  · have h0 := hdiv _ h
    ext i
    have := congrArg (fun x => coords x i) h0
    simp only [δ, coords_ofCoords] at this
    rw [this]; fin_cases i <;> rfl
  · rw [coords_rat, coords_ofCoords]; exact hξ
  · rw [lmat_mulVec, ofCoords_coords]

end GlobalTheory.QSA.FujisakiQ

namespace GlobalTheory.QSA.FujisakiQ

open GroundTheory.Global.IdeleGroup in

theorem fujisaki_mod_centre : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → (∀ x : ℍ[F, a, b], nrm x = 0 → x = 0) → ∃ C : Set (DA F a b), IsCompact C ∧ ∀ y : DA F a b, IsUnit (nrm y) → ∃ (δ : ℍ[F, a, b]) (l : AF F) (c c' : DA F a b), nrm δ ≠ 0 ∧ IsUnit l ∧ c ∈ C ∧ c' ∈ C ∧ c * c' = 1 ∧ c' * c = 1 ∧ y = l • (rat δ * c) := by
  intro F _ _ a b _ _ hdiv
  obtain ⟨B, hBc, hB⟩ := GlobalTheory.T.adelic_minkowski_exists_short_rational_vector F 4 (by norm_num)
  obtain ⟨B', hB'⟩ : ∃ B' : Set (DA F a b), B' = ofCoords '' B := ⟨_, rfl⟩
  have hB'c : IsCompact B' := hB' ▸ hBc.image continuous_ofCoords
  obtain ⟨S, hS⟩ : ∃ S : Set (DA F a b), S = (fun p : DA F a b × DA F a b => star p.1 * p.2) '' (B' ×ˢ B') := ⟨_, rfl⟩
  have hSc : IsCompact S := hS ▸ (hB'c.prod hB'c).image continuous_star_mul
  obtain ⟨Z, hZ⟩ : ∃ Z : Set ℍ[F, a, b], Z = {γ | rat γ ∈ S} := ⟨_, rfl⟩
  have hZf : Z.Finite := by
    have hT : (Set.pi Set.univ (fun i : Fin 4 =>
        {k : F | algebraMap F (AF F) k ∈ (fun y : DA F a b => coords y i) '' S})).Finite :=
      Set.Finite.pi fun i => GroundTheory.Automorphic.Reduction.finite_setOf_algebraMap_mem
        (hSc.image (continuous_coord i))
    refine (hT.image (ofCoords : (Fin 4 → F) → ℍ[F, a, b])).subset fun γ hγ => ?_
    rw [hZ] at hγ
    refine ⟨coords γ, fun i _ => ⟨rat γ, hγ, ?_⟩, ofCoords_coords γ⟩
    show coords (rat γ) i = _
    rw [coords_rat]
  obtain ⟨C, hC⟩ : ∃ C : Set (DA F a b), C =
    B' ∪ ⋃ γ ∈ Z, (fun u => rat ((nrm γ)⁻¹ • star γ) * u) '' (star '' B') := ⟨_, rfl⟩
  have hCc : IsCompact C := hC ▸ hB'c.union (hZf.isCompact_biUnion fun γ _ =>
    (hB'c.image continuous_star').image (continuous_const_mul' _))
  refine ⟨C, hCc, fun y hy => ?_⟩
  obtain ⟨uy, huy⟩ := hy
  obtain ⟨l, hl⟩ := ideleModule_surjective (K := F)
    ⟨Real.sqrt (ideleModule F uy : ℝ), Real.sqrt_pos.2 (ideleModule F uy).2⟩
  obtain ⟨uz, huz⟩ : ∃ uz : (AF F)ˣ, uz = l⁻¹ ^ 2 * uy := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : DA F a b, z = ((l⁻¹ : (AF F)ˣ) : AF F) • y := ⟨_, rfl⟩
  have hnz : (uz : AF F) = nrm z := by
    rw [hz, nrm_smul, ← huy, huz, Units.val_mul, Units.val_pow_eq_pow_val]
  have hmod : ideleModule F uz = 1 := by
    have h : ideleModule F uz * ideleModule F l ^ 2 = ideleModule F uy := by
      rw [← map_pow, ← map_mul]
      congr 1
      rw [huz, mul_comm, ← mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, one_mul]
    have h' := congrArg Subtype.val h
    rw [hl] at h'
    have hp := (ideleModule F uy).2
    have h'' : (ideleModule F uz : ℝ) * (ideleModule F uy : ℝ) = (ideleModule F uy : ℝ) := by
      have e : ((⟨Real.sqrt (ideleModule F uy : ℝ), Real.sqrt_pos.2 hp⟩ : {r : ℝ // 0 < r}) ^ 2 : {r : ℝ // 0 < r}).1
          = (ideleModule F uy : ℝ) := by
        show Real.sqrt (ideleModule F uy : ℝ) ^ 2 = _
        exact Real.sq_sqrt hp.le
      rw [Positive.val_mul, e] at h'; exact h'
    exact Subtype.ext (mul_right_cancel₀ hp.ne' (h''.trans (one_mul _).symm))
  obtain ⟨zi, hzi_def⟩ : ∃ zi : DA F a b, zi = ((uz⁻¹ : (AF F)ˣ) : AF F) • star z := ⟨_, rfl⟩
  have hzi := mul_inv_of_unit z uz hnz
  rw [← hzi_def] at hzi
  have hu1 : ((uz⁻¹ : (AF F)ˣ) : AF F) = nrm zi := by
    rw [hzi_def, nrm_smul, nrm_star, ← hnz, sq, mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨δ, hδ, hc'⟩ := exists_rat_mem B hB hdiv zi uz⁻¹ hu1 (by rw [map_inv, hmod, inv_one])
  obtain ⟨δ', hδ', hc2⟩ := exists_rat_mem B hB hdiv (star z) uz ((nrm_star z).trans hnz.symm).symm hmod
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℍ[F, a, b], γ = star δ' * δ := ⟨_, rfl⟩
  have hγ : rat γ = star (star z * rat δ') * (zi * rat δ) := by
    rw [hγdef, rat_mul, rat_star, star_mul, star_star]
    simp only [mul_assoc]
    rw [← mul_assoc z zi, hzi.1, one_mul]
  have hγZ : γ ∈ Z := by
    rw [hZ]; show rat γ ∈ S; rw [hS]; exact ⟨(star z * rat δ', zi * rat δ), ⟨hB' ▸ hc2, hB' ▸ hc'⟩, hγ.symm⟩
  have hγ0 : nrm γ ≠ 0 := by
    rw [hγdef, nrm_mul, nrm_star]; exact mul_ne_zero hδ' hδ
  have hγi := rat_inv γ hγ0
  have hd := rat_inv δ hδ
  have e1 : (nrm γ)⁻¹ • star γ * star δ' = (nrm δ)⁻¹ • star δ := by
    calc (nrm γ)⁻¹ • star γ * star δ' = (nrm γ)⁻¹ • star γ * star δ' * (δ * ((nrm δ)⁻¹ • star δ)) := by
          rw [hd.1, mul_one]
      _ = ((nrm γ)⁻¹ • star γ * γ) * ((nrm δ)⁻¹ • star δ) := by rw [hγdef]; simp only [mul_assoc]
      _ = (nrm δ)⁻¹ • star δ := by rw [hγi.2, one_mul]
  have hc : rat ((nrm γ)⁻¹ • star γ) * star (star z * rat δ') = rat ((nrm δ)⁻¹ • star δ) * z := by
    rw [star_mul, star_star, ← rat_star, ← mul_assoc, ← rat_mul, e1]
  refine ⟨δ, (l : AF F), rat ((nrm γ)⁻¹ • star γ) * star (star z * rat δ'), zi * rat δ, hδ, l.isUnit,
    hC ▸ Or.inr (Set.mem_biUnion hγZ ⟨_, ⟨_, hB' ▸ hc2, rfl⟩, rfl⟩), hC ▸ Or.inl (hB' ▸ hc'), ?_, ?_, ?_⟩
  · rw [mul_assoc, ← hγ, ← rat_mul, hγi.2, rat_one]
  · rw [hc, ← mul_assoc, mul_assoc zi, ← rat_mul, hd.1, rat_one, mul_one, hzi.2]
  · rw [hc, ← mul_assoc, ← rat_mul, hd.1, rat_one, one_mul, hz, smul_smul, Units.mul_inv, one_smul]

end GlobalTheory.QSA.FujisakiQ
