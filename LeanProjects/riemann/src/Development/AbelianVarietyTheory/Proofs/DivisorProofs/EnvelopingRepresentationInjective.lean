import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPlaceRep
import Development.AbelianVarietyTheory.Proofs.HeightProofs.UnitaryLieGeneratorsRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FaithfulOfDerivationsDualFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyFunMemSmoothVectorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RightLieDerivativeRealEntryPolynomialFunctionStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.SmoothForms GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraExponentialFamilies
open scoped TensorProduct

namespace GlobalTheory.CentralOps

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 100] LieRing.ofAssociativeRing

theorem polyFun_mem (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (P : PolyE V) : polyFun θ V P ∈ SmF θ V := GlobalTheory.T.polyFun_mem_smooth_vectors D θ V R P

theorem lieDer_polyFun (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (V : HSp D)
    (R : RealPoints θ V) (τ : D.what₂.Tau) (X : LieAt V τ) (P : PolyE V) :
    lieDer V (expInf θ V) (atPlace V τ X) (polyFun θ V P) = polyFun θ V (matDer τ X.1 P) := GlobalTheory.T.rightLieDerivative_realEntryPolynomialFunction D θ V R τ X P

open Classical in

theorem aeval_matDer_single {T : Type} {n : ℕ} (τ τ' : T) (a b c d : Fin n) :
    MvPolynomial.aeval (fun p : T × Fin n × Fin n => if p.2.1 = p.2.2 then (1 : ℂ) else 0)
      (matDer τ (Matrix.single a b (1 : ℂ)) (MvPolynomial.X (τ', c, d) -
        MvPolynomial.C (if c = d then (1 : ℂ) else 0))) = if (τ, a, b) = (τ', c, d) then 1 else 0 := by
  rw [map_sub, MvPolynomial.derivation_C, sub_zero, matDer_X]
  by_cases h : τ' = τ
  · subst h
    simp only [if_true, map_sum, map_mul, MvPolynomial.aeval_X, MvPolynomial.aeval_C, Matrix.single_apply,
      Algebra.algebraMap_self, RingHom.id_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true, Prod.mk.injEq, true_and]
  · simp only [h, if_false, map_zero]
    rw [if_neg]; intro h'; exact h (congrArg Prod.fst h').symm

variable {D : D7} {θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)} {V : HSp D}

theorem polyFun_add (P Q : PolyE V) : polyFun θ V (P + Q) = polyFun θ V P + polyFun θ V Q := by
  funext g; simp [polyFun]

theorem polyFun_smul (c : ℂ) (P : PolyE V) : polyFun θ V (c • P) = c • polyFun θ V P := by
  funext g; simp [polyFun, MvPolynomial.smul_eval]

open Classical in
theorem envRepAll_ι_of (R : RealPoints θ V) (τ : D.what₂.Tau) (y : ℂ ⊗[ℝ] LieAt V τ) :
    envRepAll R (UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ y)) =
      envRep R τ (UniversalEnvelopingAlgebra.ι ℂ y) := by
  rw [← envIncl_ι, envRepAll_envIncl]

theorem envRepAll_polyFun (R : RealPoints θ V) (u : GlobalTheory.AutFinLit.Env V) (P : PolyE V) :
    (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P) := by
  classical
  let S : Subalgebra ℂ (GlobalTheory.AutFinLit.Env V) :=
    { carrier := {u | ∀ P, (envRepAll R u ⟨polyFun θ V P, polyFun_mem D θ V R P⟩).1 = polyFun θ V (polyRep V u P)}
      mul_mem' := fun {u v} hu hv P => by
        rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, ← hu]
        congr 2
        exact Subtype.ext (hv P)
      add_mem' := fun {u v} hu hv P => by
        rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, Submodule.coe_add, hu, hv, polyFun_add]
      algebraMap_mem' := fun c P => by
        rw [AlgHom.commutes, AlgHom.commutes, Module.algebraMap_end_apply, Module.algebraMap_end_apply,
          Submodule.coe_smul, polyFun_smul] }
  have hι : ∀ x, UniversalEnvelopingAlgebra.ι ℂ x ∈ S := by
    intro x
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact S.zero_mem
      | add y y' hy hy' => rw [map_add, map_add]; exact S.add_mem hy hy'
      | tmul c X =>
        intro P
        rw [envRepAll_ι_of, polyRep_ι_of, placeRep_tmul,
          show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one], map_smul,
          map_smul, envRep_ι, LinearMap.smul_apply, LinearMap.smul_apply, Submodule.coe_smul, opInf_coe,
          polyFun_smul, lieDer_polyFun D θ V R]
        rfl
  exact GlobalTheory.EnvCentre.mem_of_ι_mem (AlgHom.id ℂ _) S hι u P

theorem realEntries_one (R : RealPoints θ V) :
    realEntries θ V 1 = fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0 := by
  funext p
  simp only [realEntries, R.2.2.2.2.1 1 (one_mem _) p.1, Matrix.one_apply]

set_option maxHeartbeats 1000000 in
open Classical in

theorem envRepAll_injective (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)) (_hθ : IsInfFam θ)
    (V : HSp D) (R : RealPoints θ V) : Function.Injective (envRepAll R) := by
  rw [injective_iff_map_eq_zero]
  intro u hu
  let ρ : ∀ τ, LieAt V τ → GlobalTheory.AutFinLit.Env V := fun τ X =>
    UniversalEnvelopingAlgebra.ι ℂ (DirectSum.of (fun τ => ℂ ⊗[ℝ] LieAt V τ) τ ((1 : ℂ) ⊗ₜ[ℝ] X))
  have hadd : ∀ τ (X Y : LieAt V τ), ρ τ (X + Y) = ρ τ X + ρ τ Y := fun τ X Y => by
    simp only [ρ, TensorProduct.tmul_add, map_add]
  have hsmul : ∀ τ (c : ℝ) (X : LieAt V τ), ρ τ (c • X) = (c : ℂ) • ρ τ X := fun τ c X => by
    have e1 : (1 : ℂ) ⊗ₜ[ℝ] (c • X) = (c : ℂ) • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', TensorProduct.smul_tmul', smul_eq_mul, mul_one,
        Complex.real_smul, mul_one]
    simp only [ρ]
    rw [e1, ← DirectSum.lof_eq_of ℂ, map_smul, map_smul, DirectSum.lof_eq_of]
  have hbrk : ∀ τ (X Y Z : LieAt V τ), Z.1 = X.1 * Y.1 - Y.1 * X.1 → ρ τ Z = ρ τ X * ρ τ Y - ρ τ Y * ρ τ X :=
    fun τ X Y Z hZ => by
      have : Z = ⁅X, Y⁆ := Subtype.ext hZ
      simp only [ρ]
      rw [this, ← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of_same, LieAlgebra.ExtendScalars.bracket_tmul, one_mul]
  choose P Q hPQ hrest using fun τ =>
    GlobalTheory.UnitaryLieComplexification.glRel_and_span V.rank (gramAt D V τ) (R.1 τ).1 (R.1 τ).2
  have hgl := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).1
  have hsp := fun τ => (hrest τ (GlobalTheory.AutFinLit.Env V) (ρ τ) (hadd τ) (hsmul τ) (hbrk τ)).2
  let e : D.what₂.Tau × Fin V.rank × Fin V.rank → GlobalTheory.AutFinLit.Env V := fun p =>
    ρ p.1 (P p.1 p.2.1 p.2.2) + Complex.I • ρ p.1 (Q p.1 p.2.1 p.2.2)
  have hρe : ∀ τ X, ρ τ X ∈ Submodule.span ℂ (Set.range e) := fun τ X =>
    Submodule.span_mono (by rintro _ ⟨p, rfl⟩; exact ⟨(τ, p.1, p.2), rfl⟩) (hsp τ X)

  have hgen : Algebra.adjoin ℂ (Set.range e) = ⊤ := by
    refine eq_top_iff.2 ((GlobalTheory.EnvCentre.adjoin_range_ι_eq_top _).symm.le.trans (Algebra.adjoin_le ?_))
    rintro _ ⟨x, rfl⟩
    refine Algebra.span_le_adjoin ℂ _ ?_
    induction x using DirectSum.induction_on with
    | zero => rw [map_zero]; exact zero_mem _
    | add x y hx hy => rw [map_add]; exact add_mem hx hy
    | of τ y =>
      induction y using TensorProduct.induction_on with
      | zero => rw [map_zero, map_zero]; exact zero_mem _
      | add y y' hy hy' => rw [map_add, map_add]; exact add_mem hy hy'
      | tmul c X =>
        rw [show c ⊗ₜ[ℝ] X = c • ((1 : ℂ) ⊗ₜ[ℝ] X) by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
          ← DirectSum.lof_eq_of ℂ, map_smul, map_smul]
        exact Submodule.smul_mem _ c (hρe τ X)

  have hcomm : ∀ τ τ', τ ≠ τ' → ∀ X Y, Commute (ρ τ X) (ρ τ' Y) := fun τ τ' h X Y => by
    have h1 : ρ τ X * ρ τ' Y - ρ τ' Y * ρ τ X = 0 := by
      simp only [ρ]; rw [← Ring.lie_def, ← LieHom.map_lie, DirectSum.lie_of, dif_neg h, map_zero]
    exact sub_eq_zero.1 h1
  have hbr : ∀ p q, e p * e q - e q * e p ∈ Submodule.span ℂ (Set.range e) := by
    rintro ⟨τ, a, b⟩ ⟨τ', c, d⟩
    by_cases h : τ = τ'
    · subst h
      have := hgl τ a b c d
      simp only at this
      change (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) * (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) -
        (ρ τ (P τ c d) + Complex.I • ρ τ (Q τ c d)) * (ρ τ (P τ a b) + Complex.I • ρ τ (Q τ a b)) ∈ _
      rw [this]
      refine sub_mem ?_ ?_
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, a, d), rfl⟩
        · exact zero_mem _
      · split_ifs
        · exact Submodule.subset_span ⟨(τ, c, b), rfl⟩
        · exact zero_mem _
    · have hc : Commute (e (τ, a, b)) (e (τ', c, d)) := by
        simp only [e]
        refine Commute.add_left (Commute.add_right ?_ ?_) (Commute.add_right ?_ ?_)
        · exact hcomm τ τ' h _ _
        · exact (hcomm τ τ' h _ _).smul_right _
        · exact (hcomm τ τ' h _ _).smul_left _
        · exact ((hcomm τ τ' h _ _).smul_left _).smul_right _
      rw [hc.eq, sub_self]; exact zero_mem _

  have hπρ : ∀ τ (X : LieAt V τ), polyRep V (ρ τ X) = (matDer τ X.1 : Module.End ℂ (PolyE V)) := fun τ X => by
    simp only [ρ]; rw [polyRep_ι_of, placeRep_ι]
  have hE : ∀ τ a b, (P τ a b).1 + Complex.I • (Q τ a b).1 = Matrix.single a b (1 : ℂ) := fun τ a b => by
    rw [(hPQ τ a b).1, (hPQ τ a b).2, smul_smul]
    have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
    rw [this]
    module
  have hπe : ∀ p, polyRep V (e p) = (matDer p.1 (Matrix.single p.2.1 p.2.2 (1 : ℂ)) : Module.End ℂ (PolyE V)) :=
    fun p => by
      simp only [e]
      rw [map_add, map_smul, hπρ, hπρ, ← hE, matDer_add, matDer_smul]
      rfl
  have hder : ∀ p (x y : PolyE V), polyRep V (e p) (x * y) = polyRep V (e p) x * y + x * polyRep V (e p) y :=
    fun p x y => by
      rw [hπe]
      change matDer _ _ (x * y) = matDer _ _ x * y + x * matDer _ _ y
      rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul]; ring
  let pt : D.what₂.Tau × Fin V.rank × Fin V.rank → ℂ := fun p => if p.2.1 = p.2.2 then (1 : ℂ) else 0
  let χ : PolyE V →ₐ[ℂ] ℂ := MvPolynomial.aeval pt
  let a : D.what₂.Tau × Fin V.rank × Fin V.rank → PolyE V := fun p => MvPolynomial.X p - MvPolynomial.C (pt p)
  have ha0 : ∀ k, χ (a k) = 0 := fun k => by simp [χ, a]
  have hδ : ∀ i k, χ (polyRep V (e i) (a k)) = if i = k then 1 else 0 := by
    rintro ⟨τ, a', b'⟩ ⟨τ', c, d⟩
    rw [hπe]
    exact aeval_matDer_single τ τ' a' b' c d
  refine GlobalTheory.T.faithful_of_derivations_dualFamily _ _ _ e hgen hbr (polyRep V) hder χ a ha0 hδ u fun x => ?_
  have h1 := congrFun (envRepAll_polyFun R u x) 1
  rw [hu, LinearMap.zero_apply, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  have h2 : polyFun θ V (polyRep V u x) 1 = χ (polyRep V u x) := by
    rw [polyFun, realEntries_one R, MvPolynomial.aeval_eq_eval₂Hom, Algebra.algebraMap_self]; rfl
  rw [← h2, ← h1]

end GlobalTheory.CentralOps
