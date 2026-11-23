import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBimultPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.UniformizationLawsAndExpansionStatements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorPreDataCubicalStructureEqProdPulledBackStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

open ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.TensBimult

theorem alg {U X X' : Type} [CommGroup U] [AddCommGroup X] [AddCommGroup X'] {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ)
    (e : X' ≃+ (Fin r → X)) (Ψ : X → U) (ρ : U) (O ψ' : X' → U) (τ' : X' → X' → U) (t : X → X → U) (c' rig' : U)
    (a a' b : X') (ht : ∀ u v, t u v = Ψ (u + v) * (Ψ u)⁻¹ * (Ψ v)⁻¹ * ρ⁻¹)
    (hψ : ∀ u, ψ' u = O u * ∏ i, ∏ j, t (e u i) (e u j) ^ W i j)
    (hτ : ∀ u v, τ' u v = ψ' (u + v) * (ψ' u)⁻¹ * (ψ' v)⁻¹ * rig'⁻¹) (hr : ψ' 0 * rig' = 1)
    (hc : c' * (O (a + a' + b) * (O (a + a'))⁻¹ * (O (a + b))⁻¹ * (O (a' + b))⁻¹ * O a * O a' * O b * (O 0)⁻¹) =
      ∏ k : (Fin r × Fin r) × Fin 4,
        (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          t (![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2) (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2) *
          (t (![e a k.1.1 + e a k.1.2, e a k.1.1, e a k.1.2, 0] k.2 + ![e a' k.1.1 + e a' k.1.2, e a' k.1.1, e a' k.1.2, 0] k.2)
            (![e b k.1.1 + e b k.1.2, e b k.1.1, e b k.1.2, 0] k.2))⁻¹) ^ tensε W k) :
    τ' (a + a') b * c' = τ' a b * τ' a' b := by
  have hr' : rig'⁻¹ = ψ' 0 := (eq_inv_of_mul_eq_one_right hr).symm ▸ inv_inv _
  rw [eq_mul_inv_of_mul_eq hc, hτ, hτ, hτ, hr']
  simp only [hψ, ht, Fintype.prod_prod_type, Fin.prod_univ_four, tensε, Oε, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, map_add, Pi.add_apply, map_zero, Pi.zero_apply,
    add_zero, zero_add]
  have e1 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1) + (e b x + e b x1)) = Ψ (e a x + e a' x + e b x + (e a x1 + e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e2 : ∀ x x1, Ψ (e a x + e a x1 + (e a' x + e a' x1)) = Ψ (e a x + e a' x + (e a x1 + e a' x1)) := fun x x1 => congrArg Ψ (by abel)
  have e3 : ∀ x x1, Ψ (e a x + e a x1 + (e b x + e b x1)) = Ψ (e a x + e b x + (e a x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  have e4 : ∀ x x1, Ψ (e a' x + e a' x1 + (e b x + e b x1)) = Ψ (e a' x + e b x + (e a' x1 + e b x1)) := fun x x1 => congrArg Ψ (by abel)
  simp only [e1, e2, e3, e4]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_prod, ofMul_zpow, smul_add, smul_neg, Finset.sum_add_distrib,
    Finset.sum_neg_distrib, _root_.mul_one, mul_neg, neg_smul]
  abel

end GlobalTheory.TensBimult

namespace GlobalTheory.TensBimult

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)) (D' : DegPre R) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), Tens D.toPre D' W → (∀ (z : (TK R).left) (J : ((TK R).left ⟶ D'.P.A.left) → D'.P.L.ι), Good D'.P.L z J → val (D'.psi 0) (𝟙 _) z J * val D'.rigK (𝟙 _) z J = 1) → D'.TauBimult := by
  intro R _ _ _ _ D D' r W T hn a a' b
  have hG : GlobalFnsSt := GlobalTheory.lawsAndExpansions.1.1.globalFns
  refine corr_of_val D'.P.isLB fun y J' hJ' => ?_
  obtain ⟨J, hJ⟩ : ∃ J, Good D.toPre.P.L y J :=
    ⟨fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose, fun ψ => (exists_chart D.toPre.P.isLB (ψ y)).choose_spec⟩
  have key := GlobalTheory.T.tensorPreData_cubicalStructure_eq_prod_pulled_back hG R D.toPre D' W T (TK R) y J J' hJ hJ' (cP D' _ a) (cP D' _ a') (cP D' _ b)
  have hψ : ∀ u, val (D'.psi u) (𝟙 _) y J' = gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)) * ∏ i, ∏ j, val (D.toPre.tau (T.xe u i) (T.xe u j)) (𝟙 _) y J ^ W i j :=
    fun u => T.psi u y J J' hJ hJ'
  have vt : ∀ u v, val (D'.tau u v) (𝟙 _) y J' = val (D'.psi (u + v)) (𝟙 _) y J' * (val (D'.psi u) (𝟙 _) y J')⁻¹ * (val (D'.psi v) (𝟙 _) y J')⁻¹ * (val D'.rigK (𝟙 _) y J')⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ', val_inv]
  have vtE : ∀ u v, val (D.toPre.tau u v) (𝟙 _) y J = val (D.toPre.psi (u + v)) (𝟙 _) y J * (val (D.toPre.psi u) (𝟙 _) y J)⁻¹ * (val (D.toPre.psi v) (𝟙 _) y J)⁻¹ * (val D.toPre.rigK (𝟙 _) y J)⁻¹ := by
    intro u v; simp only [DegPre.tau, val_mul hJ, val_inv]
  have hB : ∀ u u' v, val (D.toPre.tau (u + u') v) (𝟙 _) y J * cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J := fun u u' v =>
    (GlobalTheory.TauBimultBox.val_lhs D.toPre hJ u u' v).symm.trans ((val_corr hJ (D.tau_bimult u u' v) (𝟙 _)).trans (val_mul hJ _ _ _))
  have c0 : ∀ (E : DegPre R) (S : Over (Spec (CommRingCat.of R))), cP E S 0 = 1 := fun E S => by
    have := cPoint_add E S 0 0
    rw [add_zero] at this
    exact mul_eq_left.1 this.symm
  have hP : ∀ u (k : (Fin r × Fin r) × Fin 4), cP D' (TK R) u ≫ ![T.pr k.1.1 * T.pr k.1.2, T.pr k.1.1, T.pr k.1.2, 1] k.2 = cP D.toPre (TK R) (![T.xe u k.1.1 + T.xe u k.1.2, T.xe u k.1.1, T.xe u k.1.2, 0] k.2) := by
    intro u k
    have e : ∀ i, cP D' (TK R) u ≫ T.pr i = cP D.toPre (TK R) (T.xe u i) := fun i => by
      rw [cP, Category.assoc, T.c_pr]; rfl
    obtain ⟨⟨i, j⟩, m⟩ := k
    fin_cases m
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero]
      rw [MonObj.comp_mul, e, e, cPoint_add]
    · simpa using e i
    · simpa using e j
    · simp only [Fin.reduceFinMk, Fin.isValue, Matrix.cons_val]
      rw [c0]; simp [Hom.one_def]
  rw [GlobalTheory.TauBimultBox.val_lhs D' hJ' a a' b, val_mul hJ']
  have hC : ∀ u u' v, cubV D.toPre.cub y J (cP D.toPre _ u) (cP D.toPre _ u') (cP D.toPre _ v) = val (D.toPre.tau u v) (𝟙 _) y J * val (D.toPre.tau u' v) (𝟙 _) y J * (val (D.toPre.tau (u + u') v) (𝟙 _) y J)⁻¹ := fun u u' v => by
    rw [← hB u u' v, mul_comm, inv_mul_cancel_left]
  simp only [hP, hC] at key
  have h1 : cP D' (TK R) a * cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a + a' + b) := by rw [cPoint_add, cPoint_add]
  have h2 : cP D' (TK R) a * cP D' (TK R) a' = cP D' (TK R) (a + a') := (cPoint_add _ _ _ _).symm
  have h3 : cP D' (TK R) a * cP D' (TK R) b = cP D' (TK R) (a + b) := (cPoint_add _ _ _ _).symm
  have h4 : cP D' (TK R) a' * cP D' (TK R) b = cP D' (TK R) (a' + b) := (cPoint_add _ _ _ _).symm
  rw [h1, h2, h3, h4, ← c0 D' (TK R)] at key
  refine alg W T.xe (fun u => val (D.toPre.psi u) (𝟙 _) y J) (val D.toPre.rigK (𝟙 _) y J)
    (fun u => gm (cP D' (TK R) u).left y _ (T.w.s (fun k => J ((cP D' (TK R) u).left ≫ tensφ T.pr k), J' (cP D' (TK R) u).left)))
    (fun u => val (D'.psi u) (𝟙 _) y J') (fun u v => val (D'.tau u v) (𝟙 _) y J') (fun u v => val (D.toPre.tau u v) (𝟙 _) y J)
    (cubV D'.cub y J' (cP D' (TK R) a) (cP D' (TK R) a') (cP D' (TK R) b)) (val D'.rigK (𝟙 _) y J') a a' b vtE hψ vt (hn y J' hJ') ?_
  beta_reduce
  exact key

end GlobalTheory.TensBimult
