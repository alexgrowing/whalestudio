import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSstResToOfIsPst

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.Published

def DeRhamPotSemistable : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
      [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V),
      (∀ v : V, Continuous fun g => ρ g v) → IsDR (P.PD K) ρ → IsPst P ρ

end GlobalTheory.Published

namespace GlobalTheory.PstCoeff

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
  {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
  (ρ : Representation LL ↥(GK K) V)

def resQ : Representation ℚ_[l] ↥(GK K) V where
  toFun g := (ρ g).restrictScalars ℚ_[l]
  map_one' := by ext; simp
  map_mul' g h := by ext; simp

@[simp] theorem resQ_apply (g : ↥(GK K)) (v : V) : resQ ρ g v = ρ g v := rfl

theorem actVdR_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] P.R.BdR) :
    actVdR (P.PD K) (resQ ρ) g x = actVdR (P.PD K) ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp [actVdR]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem DdR_resQ : DdR (P.PD K) (resQ ρ) = (DdR (P.PD K) ρ).restrictScalars ℚ_[l] := by
  ext x
  simp [DdR, sub_eq_zero, actVdR_resQ]

theorem isDR_resQ_iff [FiniteDimensional ℚ_[l] LL] : IsDR (P.PD K) (resQ ρ) ↔ IsDR (P.PD K) ρ := by
  have e : finrank ℚ_[l] ↥(DdR (P.PD K) (resQ ρ)) = finrank ℚ_[l] LL * finrank LL ↥(DdR (P.PD K) ρ) := by
    rw [DdR_resQ, finrank_mul_finrank]
    rfl
  rw [IsDR, IsDR, e, ← finrank_mul_finrank ℚ_[l] LL V, mul_left_comm]
  exact Nat.mul_right_inj finrank_pos.ne'

theorem stRep_resQ (g : ↥(GK K)) (x : V ⊗[ℚ_[l]] Bst P) : stRep P (resQ ρ) g x = stRep P ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_Dpst_resQ (x : V ⊗[ℚ_[l]] Bst P) : x ∈ Dpst P (resQ ρ) ↔ x ∈ Dpst P ρ := by
  simp only [mem_Dpst, stRep_resQ]

theorem mulV_resQ (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) : mulV P ℚ_[l] V c x = mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

def dpstUrEquiv : DpstUr P (resQ ρ) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ where
  toFun x := toUr P ρ ⟨((toUr P (resQ ρ)).symm x).1, (mem_Dpst_resQ P ρ _).mp ((toUr P (resQ ρ)).symm x).2⟩
  invFun x := toUr P (resQ ρ) ⟨((toUr P ρ).symm x).1, (mem_Dpst_resQ P ρ _).mpr ((toUr P ρ).symm x).2⟩
  map_add' _ _ := rfl
  map_smul' c x := Subtype.ext (mulV_resQ P (LL := LL) c _)
  left_inv _ := rfl
  right_inv _ := rfl

theorem isPst_resQ_iff : IsPst P (resQ ρ) ↔ IsPst P ρ := by
  rw [IsPst, IsPst, (dpstUrEquiv P ρ).rank_eq]

end GlobalTheory.PstCoeff

namespace GlobalTheory.Published.DeRhamPotSemistable

open GlobalTheory.PstCoeff

variable (h : DeRhamPotSemistable) {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
  (T : LocTied l P AI) {K : FinExt l}
include h T

theorem coeff {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V]
    (ρ : Representation LL ↥(GK K) V) (hc : ∀ v : V, Continuous fun g => ρ g v) (hV : IsDR (P.PD K) ρ) :
    IsPst P ρ :=
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans LL V
  (isPst_resQ_iff P ρ).mp (h l P AI ⟨T⟩ K V (resQ ρ) hc ((isDR_resQ_iff P ρ).mpr hV))

theorem of_coords {LL : Type} [Field LL] [Algebra ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]
    [FiniteDimensional LL V] (ρ : Representation LL ↥(GK K) V)
    (hc : ∀ (v : V) (f : Dual ℚ_[l] V), Continuous fun g => f (ρ g v)) (hV : IsDR (P.PD K) ρ) :
    IsPst P ρ := by
  haveI : FiniteDimensional ℚ_[l] V := Module.Finite.trans LL V
  letI : TopologicalSpace V := moduleTopology ℚ_[l] V
  haveI : IsModuleTopology ℚ_[l] V := ⟨rfl⟩
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd ℚ_[l] V
  refine h.coeff T ρ (fun v => ?_) hV
  let b := finBasis ℚ_[l] V
  have e : (fun g => ρ g v) = fun g => ∑ i, b.coord i (ρ g v) • b i :=
    funext fun g => (b.sum_repr _).symm
  rw [e]
  exact continuous_finset_sum _ fun i _ => (hc v _).smul continuous_const

theorem pi {LL : FinExt l} {m : ℕ} (ρ : Representation ↥LL.1 ↥(GK K) (Fin m → ↥LL.1))
    (hc : ∀ v, Continuous fun g => ρ g v) (hV : IsDR (P.PD K) ρ) : IsPst P ρ :=
  haveI := LL.2
  h.of_coords T ρ (fun v f => (LinearMap.continuous_of_finiteDimensional f).comp (hc v)) hV

omit K in

theorem isPstAt {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω] {Gw : Subgroup (Ω ≃ₐ[E] Ω)}
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) {a : ℕ}
    (r : ↥Gw →* GL (Fin a) (Om l))
    (hc : Continuous fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)))
    (hr : IsdRAt P Bw r) : IsPstAt P Bw r := by
  obtain ⟨LL', r', hm, hd⟩ := hr
  refine ⟨LL', r', hm, h.pi T _ (fun v => ?_) (by rw [IsDR, finrank_fin_fun]; exact hd)⟩
  have hc' : Continuous fun g => ((r' g : GL (Fin a) ↥LL'.1) : Matrix (Fin a) (Fin a) ↥LL'.1) := by
    refine continuous_matrix fun i j => continuous_induced_rng.2 ?_
    have := hc.matrix_elem i j
    rw [← hm.2] at this
    exact this
  exact (hc'.comp Bw.e_symm_cont).matrix_mulVec continuous_const

end GlobalTheory.Published.DeRhamPotSemistable
