import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.NilToPhiAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.AdmissibleSequenceExact

noncomputable section

open TensorProduct Module Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Ru.crystallineComparison

section
variable {F G B : Type} [Field F] [Group G] [AddCommGroup B] [Module F B]
  {I : Type} [Fintype I] {V : I → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module F (V i)]

private def prI (B : Type) [AddCommGroup B] [Module F B] (i : I) : (∀ i, V i) ⊗[F] B →ₗ[F] V i ⊗[F] B :=
  AlgebraTensorModule.map (LinearMap.proj i) LinearMap.id

private theorem prI_map (i : I) (a : (∀ i, V i) →ₗ[F] (∀ i, V i)) (b : V i →ₗ[F] V i) (c : B →ₗ[F] B)
    (h : ∀ x, a x i = b (x i)) (x : (∀ i, V i) ⊗[F] B) :
    prI B i (AlgebraTensorModule.map a c x) = AlgebraTensorModule.map b c (prI B i x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, h]
  | add x y hx hy => simp only [map_add, hx, hy]

open Classical in

private def inI (B : Type) [AddCommGroup B] [Module F B] (i : I) : V i ⊗[F] B →ₗ[F] (∀ i, V i) ⊗[F] B :=
  AlgebraTensorModule.map (LinearMap.single F V i) LinearMap.id

private theorem sum_inI_prI (x : (∀ i, V i) ⊗[F] B) : ∑ i, inI B i (prI B i x) = x := by
  classical
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v y =>
    simp only [prI, inI, AlgebraTensorModule.map_tmul, LinearMap.proj_apply, LinearMap.id_apply, LinearMap.coe_single]
    rw [← TensorProduct.sum_tmul, Finset.univ_sum_single]
  | add x y hx hy => simp only [map_add, Finset.sum_add_distrib, hx, hy]

private theorem prI_inI_same (i : I) (y : V i ⊗[F] B) : prI B i (inI B i y) = y := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, inI]
  | add x y hx hy => simp only [map_add, hx, hy]

private theorem prI_inI_ne {i j : I} (h : j ≠ i) (y : V j ⊗[F] B) : prI B i (inI B j y) = 0 := by
  classical
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v y => simp [prI, inI, Pi.single_eq_of_ne (Ne.symm h)]
  | add x y hx hy => simp only [map_add, hx, hy, add_zero]

private theorem ext_prI {x y : (∀ i, V i) ⊗[F] B} (h : ∀ i, prI B i x = prI B i y) : x = y := by
  rw [← sum_inI_prI x, ← sum_inI_prI y]; simp only [h]

variable (σ : G → End F B) (ρ : ∀ i, Representation F G (V i)) (ρ' : Representation F G (∀ i, V i))

private theorem mem_Dinv_pi (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) (x : (∀ i, V i) ⊗[F] B) :
    x ∈ Dinv σ ρ' ↔ ∀ i, prI B i x ∈ Dinv σ (ρ i) := by
  simp only [mem_Dinv]
  constructor
  · intro h i g
    rw [← prI_map i (ρ' g) (ρ i g) (σ g) (fun x => hρ g x i), h]
  · intro h g
    refine ext_prI fun i => ?_
    rw [prI_map i (ρ' g) (ρ i g) (σ g) (fun x => hρ g x i), h]

private def dinvPi (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) : Dinv σ ρ' ≃ₗ[F] ∀ i, Dinv σ (ρ i) :=
  LinearEquiv.ofBijective
    (LinearMap.pi fun i => ((prI B i).comp (Dinv σ ρ').subtype).codRestrict (Dinv σ (ρ i))
      fun x => (mem_Dinv_pi σ ρ ρ' hρ x).1 x.2 i)
    (by
      constructor
      · intro x y h
        exact Subtype.ext (ext_prI fun i => congrArg Subtype.val (congrFun h i))
      · intro y
        classical
        have hc : ∀ i, prI B i (∑ j, inI B j (y j : V j ⊗[F] B)) = y i := by
          intro i
          rw [map_sum, Finset.sum_eq_single i (fun j _ h => prI_inI_ne h _) (by simp), prI_inI_same]
        refine ⟨⟨∑ j, inI B j (y j : V j ⊗[F] B), (mem_Dinv_pi σ ρ ρ' hρ _).2 fun i => ?_⟩, ?_⟩
        · rw [hc]; exact (y i).2
        · funext i
          exact Subtype.ext (hc i))

private theorem adm_pi_rep_of_forall_adm_of_pos [∀ i, Module.Finite F (V i)] (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) {e : ℕ} (he : 0 < e)
    (h : ∀ i, admitted σ e (ρ i)) : admitted σ e ρ' := by
  have hfin : ∀ i, Module.Finite F (Dinv σ (ρ i)) := by
    intro i
    by_cases h0 : finrank F (V i) = 0
    · have : Subsingleton (V i) := Module.finrank_zero_iff.1 h0
      have : Subsingleton (V i ⊗[F] B) := by
        refine ⟨fun a b => ?_⟩
        have hz : ∀ c : V i ⊗[F] B, c = 0 := by
          intro c
          induction c using TensorProduct.induction_on with
          | zero => rfl
          | tmul v y => rw [Subsingleton.elim v 0, TensorProduct.zero_tmul]
          | add x y hx hy => rw [hx, hy, add_zero]
        rw [hz a, hz b]
      infer_instance
    · exact Module.finite_of_finrank_pos (by rw [h i]; exact Nat.mul_pos he (Nat.pos_of_ne_zero h0))
  unfold admitted at *
  rw [(dinvPi σ ρ ρ' hρ).finrank_eq, Module.finrank_pi_fintype, Module.finrank_pi_fintype, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => h i

private theorem annD_pi (ψ : End F B) (q n : ℕ) (T : ∀ i, ℕ → End F (V i)) (T' : ℕ → End F (∀ i, V i))
    (hρ : ∀ g x i, ρ' g x i = ρ i g (x i)) (hT : ∀ j x i, T' j x i = T i j (x i))
    (h : ∀ i, AnnD σ ψ q n (ρ i) (T i)) : AnnD σ ψ q n ρ' T' := by
  intro x hx
  refine ext_prI fun i => ?_
  have := h i _ ((mem_Dinv_pi σ ρ ρ' hρ x).1 hx i)
  rw [map_zero, map_sum, ← this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_zsmul, prI_map i (T' j) (T i j) (ψ ^ (n - j)) (fun x => hT j x i)]

end

end UpperTheory.Ru.crystallineComparison

theorem UpperTheory.Ru.crystallineComparison.annPi :
    UpperTheory.Ru.crystallineComparison.AnnPi := by
  intro l _ P K I _ V _ _ _ ρ f q n T ρ' T' hρ hT
  refine ⟨fun h => ?_, fun h => annD_pi _ ρ ρ' _ q n T T' hρ hT h⟩
  have he : 0 < finrank ℚ_[l] ↥(K0 K) := by
    have := (P.PD K).finK₀
    exact Module.finrank_pos
  exact adm_pi_rep_of_forall_adm_of_pos (fun g => (((P.PD K).actB g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) ρ ρ' hρ he h
