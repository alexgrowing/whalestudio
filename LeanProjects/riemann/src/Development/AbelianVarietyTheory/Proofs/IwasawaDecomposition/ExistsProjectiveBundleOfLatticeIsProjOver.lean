import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValRSpMapFromSpecStalk
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsProjBundleClosure

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlagBundle

open AlgebraicGeometry CategoryTheory ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH GlobalTheory.Cartier

section Generic

variable {Ω : Type} [Field Ω] {J : Type} [Fintype J] [DecidableEq J]

def genPoly (Ω : Type) [Field Ω] (j₀ j : J) : MvPolynomial {j // j ≠ j₀} Ω :=
  if h : j = j₀ then 1 else MvPolynomial.X ⟨j, h⟩

def genPt (Ω : Type) [Field Ω] (j₀ j : J) : FractionRing (MvPolynomial {j // j ≠ j₀} Ω) :=
  algebraMap _ _ (genPoly Ω j₀ j)

omit [Fintype J] in
theorem genPt_self (j₀ : J) : genPt Ω j₀ j₀ = 1 := by simp [genPt, genPoly]

omit [Fintype J] in

theorem eq_top_of_genPt_mem (j₀ : J) (K : Subfield (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)))
    (h1 : ∀ a : Ω, algebraMap Ω _ a ∈ K) (h2 : ∀ j, genPt Ω j₀ j ∈ K) : K = ⊤ := by
  have h : ∀ p : MvPolynomial {j // j ≠ j₀} Ω, algebraMap _ _ p ∈ K := fun p => by
    induction p using MvPolynomial.induction_on with
    | C a => exact h1 a
    | add p q hp hq => rw [map_add]; exact add_mem hp hq
    | mul_X p j hp =>
      rw [map_mul]
      refine mul_mem hp ?_
      simpa [genPt, genPoly, j.2] using h2 j.1
  refine top_unique fun x _ => ?_
  obtain ⟨p, q, -, rfl⟩ := IsFractionRing.div_surjective (A := MvPolynomial {j // j ≠ j₀} Ω) x
  exact div_mem (h p) (h q)

theorem eq_zero_of_sum_genPt (j₀ : J) (b : J → Ω) (h : ∑ j, algebraMap Ω _ (b j) * genPt Ω j₀ j = 0) : b = 0 := by
  have h' : ∑ j, MvPolynomial.C (b j) * genPoly Ω j₀ j = 0 := by
    apply IsFractionRing.injective _ (FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
    rw [map_zero, map_sum, ← h]
    exact Finset.sum_congr rfl fun j _ => by rw [map_mul]; rfl
  have e : ∀ x : J → Ω, x j₀ = 1 → ∑ j, b j * x j = 0 := fun x hx => by
    have := congrArg (MvPolynomial.eval fun j : {j // j ≠ j₀} => x j.1) h'
    rw [map_zero, map_sum] at this
    rw [← this]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : j = j₀
    · subst hj; simp [genPoly, hx]
    · simp [genPoly, hj]
  have h0 : b j₀ = 0 := by simpa [Pi.single_apply] using e (Pi.single j₀ 1) (by simp)
  funext j
  by_cases hj : j = j₀
  · exact hj ▸ h0
  · have := e (fun l => Pi.single (M := fun _ => Ω) j₀ 1 l + Pi.single (M := fun _ => Ω) j 1 l) (by simp [Ne.symm hj])
    simpa [Pi.single_apply, mul_add, Finset.sum_add_distrib, h0] using this

theorem genPt_ratio (j₀ : J) (B : Matrix J J Ω) (hB : B.det ≠ 0) (i : J) :
    (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i ≠ 0 ∧ AlgebraicIndependent Ω fun j : {j // j ≠ i} =>
      (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) j.1 / (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) i := by
  set u := (B.map (algebraMap Ω _)).mulVec (genPt Ω j₀) with hu
  have hi : u i ≠ 0 := fun h => hB (Matrix.det_eq_zero_of_row_eq_zero i
    (congrFun (eq_zero_of_sum_genPt j₀ (B i) h)))
  refine ⟨hi, ?_⟩
  set r : {j // j ≠ i} → _ := fun j => u j.1 / u i
  have hs : (B⁻¹.map (algebraMap Ω _)).mulVec u = genPt Ω j₀ := by
    rw [hu, Matrix.mulVec_mulVec, ← Matrix.map_mul, Matrix.nonsing_inv_mul _ (Ne.isUnit hB),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
  set K := IntermediateField.adjoin Ω (Set.range r)
  have h1 : ∀ j, u j / u i ∈ K := fun j => by
    by_cases hj : j = i
    · rw [hj, div_self hi]; exact one_mem _
    · exact IntermediateField.subset_adjoin _ _ ⟨⟨j, hj⟩, rfl⟩
  have h2 : ∀ j, genPt Ω j₀ j / u i ∈ K := fun j => by
    rw [← hs, Matrix.mulVec, dotProduct, Finset.sum_div]
    refine sum_mem fun l _ => ?_
    rw [mul_div_assoc]
    exact mul_mem (K.algebraMap_mem _) (h1 l)
  have h3 : K.toSubfield = ⊤ := eq_top_of_genPt_mem j₀ _ K.algebraMap_mem fun j => by
    have := div_mem (h2 j) (h2 j₀)
    rwa [div_div_div_cancel_right₀ hi, genPt_self, div_one] at this
  have h4 : Algebra.IsAlgebraic K (FractionRing (MvPolynomial {j // j ≠ j₀} Ω)) := ⟨fun x =>
    isAlgebraic_algebraMap (⟨x, (h3 ▸ Subfield.mem_top x : x ∈ K.toSubfield)⟩ : K)⟩
  have h5 := IntermediateField.isAlgebraic_adjoin_iff_top.1 h4
  refine (Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite Ω r ?_).1
  have h6 := trdeg_add_eq Ω (MvPolynomial {j // j ≠ j₀} Ω) (A := FractionRing (MvPolynomial {j // j ≠ j₀} Ω))
  rw [← h6, MvPolynomial.trdeg_of_isDomain]
  refine le_trans (le_of_eq ?_) le_self_add
  simp [Cardinal.mk_fintype]

end Generic

theorem exists_projBundle : ∀ (F Ω : Type) [Field F] [Field Ω] [Algebra F Ω] (M : RatModel F Ω) (J : Type) [Fintype J] [DecidableEq J] [Nonempty J] (EE : M.Lat J), IsProjOver M.s → ∃ (Ω' : Type) (_ : Field Ω') (_ : Algebra F Ω') (M' : RatModel F Ω') (φ : Ω →ₐ[F] Ω') (f : M'.Z ⟶ M.Z) (s : J → Ω'), ProjBundle M EE M' φ f s ∧ IsProjOver M'.s := by
  intro F Ω _ _ _ M J _ inst ⟨j₀⟩ EE hM
  obtain rfl : inst = fun a b => Classical.propDecidable (a = b) := Subsingleton.elim _ _
  letI : DecidableEq J := fun a b => Classical.propDecidable (a = b)
  let Ω' := FractionRing (MvPolynomial {j // j ≠ j₀} Ω)
  let φ : Ω →ₐ[F] Ω' := IsScalarTower.toAlgHom F Ω Ω'
  obtain ⟨M', f, hf, hp, hc⟩ := RatModel.exists_projBundle_closure F Ω M Ω' φ J EE (genPt Ω j₀) hM
    ⟨j₀, by rw [genPt_self]; exact one_ne_zero⟩
    (eq_top_of_genPt_mem j₀ _ (fun a => Subfield.subset_closure (Or.inl ⟨a, rfl⟩))
      fun j => Subfield.subset_closure (Or.inr ⟨j₀, j, by rw [genPt_self, div_one]⟩))
  refine ⟨Ω', inferInstance, inferInstance, M', φ, f, genPt Ω j₀, ⟨hf, fun B hB i => ?_, hc⟩, hp⟩
  obtain ⟨h1, h2⟩ := genPt_ratio j₀ B hB i
  exact ⟨h1, fun P hP => algebraicIndependent_iff.1 h2 P hP⟩

end GlobalTheory.FlagBundle
