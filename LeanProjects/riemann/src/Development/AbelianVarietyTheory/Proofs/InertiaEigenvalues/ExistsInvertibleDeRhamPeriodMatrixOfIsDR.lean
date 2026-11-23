import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamPeriodRingFieldTPowFiltrationUnitsStatement

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per Matrix

noncomputable section

namespace GlobalTheory.DRMat

theorem exists_fixed_of_stable {F ι : Type} [Field F] [Fintype ι] [DecidableEq ι]
    (S : Set (F →+* F)) (N : Submodule F (ι → F))
    (hN : ∀ σ ∈ S, ∀ v ∈ N, (fun j => σ (v j)) ∈ N) (v₀ : ι → F) (hv₀ : v₀ ∈ N) (h0 : v₀ ≠ 0) :
    ∃ v ∈ N, v ≠ 0 ∧ ∀ σ ∈ S, ∀ j, σ (v j) = v j := by
  classical
  have hex : ∃ k, ∃ v ∈ N, v ≠ 0 ∧ (Finset.univ.filter fun j => v j ≠ 0).card = k :=
    ⟨_, v₀, hv₀, h0, rfl⟩
  obtain ⟨w, hwN, hw0, hwk⟩ := Nat.find_spec hex
  obtain ⟨j₀, hj₀⟩ : ∃ j, w j ≠ 0 := by
    by_contra h; push_neg at h; exact hw0 (funext h)
  set v := (w j₀)⁻¹ • w with hv
  have hvN : v ∈ N := N.smul_mem _ hwN
  have hvj : v j₀ = 1 := by simp [hv, hj₀]
  have hsupp : ∀ j, v j ≠ 0 ↔ w j ≠ 0 := by
    intro j; simp [hv, hj₀]
  refine ⟨v, hvN, fun h => by simp [h] at hvj, fun σ hσ => ?_⟩
  by_contra hne
  push_neg at hne
  set u : ι → F := (fun j => σ (v j)) - v with hu
  have huN : u ∈ N := N.sub_mem (hN σ hσ v hvN) hvN
  have hu0 : u ≠ 0 := by
    obtain ⟨j, hj⟩ := hne
    intro h; apply hj; have := congrFun h j; simpa [hu, sub_eq_zero] using this
  have hlt : (Finset.univ.filter fun j => u j ≠ 0).card < Nat.find hex := by
    rw [← hwk]
    apply Finset.card_lt_card
    rw [Finset.ssubset_iff_of_subset]
    · exact ⟨j₀, by simp [hj₀], by simp [hu, hvj]⟩
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      rw [← hsupp]; intro hvj0; apply hj; simp [hu, hvj0]
  exact Nat.find_min hex hlt ⟨u, huN, hu0, rfl⟩

theorem exists_period_matrix_of_isDR : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Module.Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V), Formalism.MainNotions.N.IsDR (P.PD K) ρ → ∃ Q : GL n P.R.BdR, ∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q := by
  intro l _ P AI T n _ _ K V _ _ b ρ hDR
  set M : ↥(GK K) → Matrix n n P.R.BdR := fun g =>
    (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) with hM
  have hKact : ∀ (g : ↥(GK K)) (k : ↥K.1) (x : P.R.BdR),
      P.actQdR (g : GQ l) (algebraMap ↥K.1 P.R.BdR k * x) = algebraMap ↥K.1 P.R.BdR k * P.actQdR (g : GQ l) x := by
    intro g k x
    rw [← P.PD_actdR, ← P.PD_actdR, map_mul, AlgEquiv.commutes]
  let D : Submodule ↥K.1 (n → P.R.BdR) :=
    { carrier := {c | ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c}
      add_mem' := by
        intro x y hx hy g
        simp only [Set.mem_setOf_eq] at hx hy ⊢
        have : (fun i => P.actQdR (g : GQ l) ((x + y) i)) =
            (fun i => P.actQdR (g : GQ l) (x i)) + (fun i => P.actQdR (g : GQ l) (y i)) := by
          funext i; simp
        rw [this, Matrix.mulVec_add, hx g, hy g]
      zero_mem' := by
        intro g
        simp only [Set.mem_setOf_eq, Pi.zero_apply, map_zero]
        exact Matrix.mulVec_zero _
      smul_mem' := by
        intro k x hx g
        simp only [Set.mem_setOf_eq] at hx ⊢
        have : (fun i => P.actQdR (g : GQ l) ((k • x) i)) = k • (fun i => P.actQdR (g : GQ l) (x i)) := by
          funext i; simp only [Pi.smul_apply, Algebra.smul_def, hKact]
        rw [this, Matrix.mulVec_smul, hx g] }
  have hmemD : ∀ c, c ∈ D ↔ ∀ g : ↥(GK K), M g *ᵥ (fun i => P.actQdR (g : GQ l) (c i)) = c := fun c => Iff.rfl

  let e : V ⊗[ℚ_[l]] P.R.BdR ≃ₗ[ℚ_[l]] (n → P.R.BdR) :=
    TensorProduct.congr b.equivFun (LinearEquiv.refl ℚ_[l] P.R.BdR) ≪≫ₗ
      TensorProduct.comm ℚ_[l] (n → ℚ_[l]) P.R.BdR ≪≫ₗ TensorProduct.piScalarRight ℚ_[l] ℚ_[l] P.R.BdR n
  have he_tmul : ∀ v β, e (v ⊗ₜ β) = fun i => b.repr v i • β := by
    intro v β
    simp [e]
  have he : ∀ (g : ↥(GK K)) x, e (actVdR (P.PD K) ρ g x) = M g *ᵥ fun i => P.actQdR (g : GQ l) (e x i) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp only [map_zero, Pi.zero_apply]; exact (Matrix.mulVec_zero _).symm
    | tmul v β =>
      have h1 : actVdR (P.PD K) ρ g (v ⊗ₜ β) = ρ g v ⊗ₜ P.actQdR (g : GQ l) β := by
        simp [actVdR, P.PD_actdR]
      rw [h1, he_tmul, he_tmul]
      funext i
      rw [← LinearMap.toMatrix_mulVec_repr b b (ρ g) v]
      simp only [hM, Matrix.mulVec, dotProduct, Matrix.map_apply, Algebra.smul_def, map_mul, AlgEquiv.commutes]
      rw [map_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => by rw [map_mul]; ring
    | add x y hx hy =>
      rw [map_add, map_add, hx, hy, ← Matrix.mulVec_add]
      congr 1; funext i; simp
  have hmap : (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) = D.restrictScalars ℚ_[l] := by
    ext y
    rw [Submodule.mem_map_equiv, Submodule.restrictScalars_mem, hmemD]
    simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    refine forall_congr' fun g => ?_
    rw [← e.injective.eq_iff, he, LinearEquiv.apply_symm_apply]
  have hfr : Module.finrank ℚ_[l] ↥D = Module.finrank ℚ_[l] K.1 * Fintype.card n := by
    have h1 := hDR
    unfold Formalism.MainNotions.N.IsDR at h1
    rw [Module.finrank_eq_card_basis b, LinearEquiv.finrank_eq (e.submoduleMap (DdR (P.PD K) ρ)), hmap] at h1
    exact h1

  rcases Nat.eq_zero_or_pos (Fintype.card n) with hn | hn
  · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp hn
    refine ⟨1, fun g => ?_⟩
    ext i; exact isEmptyElim i
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  have hKpos : 0 < Module.finrank ℚ_[l] ↥K.1 := Module.finrank_pos
  haveI : Module.Finite ℚ_[l] ↥D := Module.finite_of_finrank_pos (by rw [hfr]; positivity)
  haveI : Module.Finite ↥K.1 ↥D := Module.Finite.of_restrictScalars_finite ℚ_[l] ↥K.1 ↥D
  have hrank : Module.finrank ↥K.1 ↥D = Fintype.card n := by
    have := Module.finrank_mul_finrank ℚ_[l] ↥K.1 ↥D
    rw [hfr] at this
    exact Nat.eq_of_mul_eq_mul_left hKpos this
  let bK : Module.Basis n ↥K.1 ↥D :=
    (Module.finBasisOfFinrankEq ↥K.1 ↥D hrank).reindex (Fintype.equivFin n).symm
  let Q0 : Matrix n n P.R.BdR := Matrix.of fun i j => (bK j : n → P.R.BdR) i
  have hQ : ∀ g : ↥(GK K), M g * Q0.map (P.actQdR (g : GQ l)) = Q0 := by
    intro g
    ext i j
    have h := congrFun ((hmemD _).1 (bK j).2 g) i
    simpa [Q0, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  have hdet : IsUnit Q0.det := by
    letI : Field P.R.BdR := (GlobalTheory.T.deRhamPeriodRing_field_tPow_filtration_units l P AI T).1.toField
    refine isUnit_iff_ne_zero.mpr fun h0 => ?_
    obtain ⟨v, hv0, hQv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr h0
    let S : Set (P.R.BdR →+* P.R.BdR) :=
      Set.range fun g : ↥(GK K) => ((P.actQdR (g : GQ l)) : P.R.BdR →+* P.R.BdR)
    have hstab : ∀ σ ∈ S, ∀ u ∈ LinearMap.ker (Matrix.mulVecLin Q0), (fun j => σ (u j)) ∈ LinearMap.ker (Matrix.mulVecLin Q0) := by
      rintro σ ⟨g, rfl⟩ u hu
      rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hu ⊢
      rw [← hQ g, ← Matrix.mulVec_mulVec]
      have : (Q0.map (P.actQdR (g : GQ l)) *ᵥ fun j => (P.actQdR (g : GQ l) : P.R.BdR →+* P.R.BdR) (u j)) = 0 := by
        funext i
        have := congrArg (P.actQdR (g : GQ l)) (congrFun hu i)
        simpa [Matrix.mulVec, dotProduct, map_sum, map_mul] using this
      rw [this, Matrix.mulVec_zero]
    obtain ⟨w, hwN, hw0, hwfix⟩ :=
      exists_fixed_of_stable S (LinearMap.ker (Matrix.mulVecLin Q0)) hstab v (by simpa using hQv) hv0
    have hwK : ∀ j, ∃ c : ↥K.1, algebraMap ↥K.1 P.R.BdR c = w j := fun j =>
      (P.PD K).invdR (w j) fun g => by rw [P.PD_actdR]; exact hwfix _ ⟨g, rfl⟩ j
    choose c hc using hwK
    have hQw : Q0 *ᵥ w = 0 := by simpa using hwN
    have hsum : ∑ j, c j • bK j = 0 := by
      apply Subtype.ext
      funext i
      have := congrFun hQw i
      simp only [Matrix.mulVec, dotProduct, Q0, Matrix.of_apply, Pi.zero_apply] at this
      simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply,
        Algebra.smul_def, Submodule.coe_zero, Pi.zero_apply]
      rw [← this]
      refine Finset.sum_congr rfl fun j _ => by rw [← hc j]; exact mul_comm _ _
    have hc0 := Fintype.linearIndependent_iff.mp bK.linearIndependent c hsum
    exact hw0 (funext fun j => by rw [← hc j, hc0 j, map_zero]; rfl)
  refine ⟨((Matrix.isUnit_iff_isUnit_det Q0).mpr hdet).unit, fun g => ?_⟩
  rw [IsUnit.unit_spec]
  exact hQ g

end GlobalTheory.DRMat
