import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.CasselmanSuffTemp
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TCells
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarProd
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TScalarFull
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSchur
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TSplit
import Development.AutomorphicArithmetic.ThetaCorrespondence.GeneralLinearGroups.TUnitcent

open Filter Topology GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult UpperTheory.Lit.Cas

private theorem jac_equiv_of_equiv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
    [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n)
    {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL n k) V} {τ : Representation ℂ (GL n k) W} (φ : π.Equiv τ) :
    Nonempty ((jac e π).Equiv (jac e τ)) := by
  refine ⟨Representation.Equiv.mk' (jacMap e φ.toIntertwiningMap)
    (jacMap e φ.symm.toIntertwiningMap) ?_ ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ.symm (φ v)) = Submodule.Quotient.mk v
      simp
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H v =>
      change Submodule.Quotient.mk (φ (φ.symm v)) = Submodule.Quotient.mk v
      simp

private theorem cell_exp (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {k : Type} [Field k] [ValuativeRel k]
    [TopologicalSpace k] [IsNonarchimedeanLocalField k] (hC : CasselmanNecSq k) (δ : IrrGL k)
    (h1 : 1 ≤ δ.1) (h2 : IsSqIntCoeff δ.rep) (y : Fin 2 → IrrGL k) (hr : ∑ j, (y j).1 = δ.1)
    (hj : jm y hr δ.rep ≠ 0) (t : kˣ) (ht : Tendsto (fun n : ℕ => (t : k) ^ n) atTop (𝓝 0))
    (a : Fin 2 → ℂ) (ha : ∀ j, ScalarBy (y j) t (a j)) : ‖a 0‖ ≤ 1 ∧ ‖a 0‖ * ‖a 1‖ = 1 := by
  obtain ⟨⟨c, hc⟩, -, -⟩ := schur hA k δ t
  have hu : ‖c‖ = 1 := unitcent k δ.1 _ δ.rep 2 δ.snd.rep.smooth δ.snd.rep.irr h2 t c hc
  have hprod : a 0 * a 1 = c := split k δ.1 _ δ.rep y hr hj t c (a 0) (a 1) hc (ha 0) (ha 1)
  have hnorm : ‖a 0‖ * ‖a 1‖ = 1 := by rw [← norm_mul, hprod, hu]
  refine ⟨?_, hnorm⟩
  by_cases h0 : (y 0).1 = 0
  · rw [(schur hA k (y 0) t).2.2 (a 0) h0 (ha 0), norm_one]
  by_cases h1' : (y 1).1 = 0
  · rw [(schur hA k (y 1) t).2.2 (a 1) h1' (ha 1), norm_one, mul_one] at hnorm
    exact hnorm.le
  have hpos : ∀ j : Fin 2, 0 < (y j).1 :=
    Fin.forall_fin_two.2 ⟨Nat.pos_of_ne_zero h0, Nat.pos_of_ne_zero h1'⟩
  have hE := hC δ.1 δ.rep h1 δ.snd.rep.smooth δ.snd.rep.irr h2 2 y hr hpos hj
  have hlt := (hE t ht a ha).1 0 (by norm_num)
  have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
  rw [hf, Finset.prod_singleton] at hlt
  exact hlt.le

theorem UpperTheory.Lit.Cas.prodExp :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.IrreducibleAdmissibleGL → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k], CasselmanNecSq k → ∀ (h N : ℕ) (δ : Fin h → IrrGL k) (hd : ∑ i, (δ i).1 = N), (∀ i, 1 ≤ (δ i).1 ∧ IsSqIntCoeff (δ i).rep) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), π.IsIrreducible → Nonempty (π.Equiv (prodIrr δ hd)) → UnitaryCentral π ∧ MaxExpWeak π := by
  intro hG hBZ hA k _ _ _ _ hC h N δ hd hδ V _ _ π hirr hφ
  obtain ⟨φ⟩ := hφ
  haveI := nontrivial_of_irreducible hirr
  constructor
  · intro t c hc
    choose b hb using fun i => (schur hA k (δ i) t).1
    have hbn : ∀ i, ‖b i‖ = 1 := fun i =>
      unitcent k (δ i).1 _ (δ i).rep 2 (δ i).snd.rep.smooth (δ i).snd.rep.irr (hδ i).2 t (b i) (hb i)
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have hφv : φ.toLinearEquiv v ≠ 0 := by
      rwa [ne_eq, LinearEquiv.map_eq_zero_iff]
    have e1 : φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v)
        = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) :=
      LinearMap.congr_fun
        (φ.toIntertwiningMap.isIntertwining' (Matrix.GeneralLinearGroup.scalar (Fin N) t)) v
    have e2 : c • φ.toLinearEquiv v = (∏ i, b i) • φ.toLinearEquiv v :=
      calc c • φ.toLinearEquiv v = φ.toLinearEquiv (c • v) :=
            (LinearEquiv.map_smul φ.toLinearEquiv c v).symm
        _ = φ.toLinearEquiv (π (Matrix.GeneralLinearGroup.scalar (Fin N) t) v) :=
            congrArg _ (hc v).symm
        _ = prodIrr δ hd (Matrix.GeneralLinearGroup.scalar (Fin N) t) (φ.toLinearEquiv v) := e1
        _ = (∏ i, b i) • φ.toLinearEquiv v := scalarFull k h N δ hd t b hb _
    have hcb : c = ∏ i, b i := smul_left_injective ℂ hφv e2
    rw [hcb, norm_prod]
    exact Finset.prod_eq_one (fun i _ => hbn i)
  · intro x hx hpos hj
    have hjm : jm x hx (prodIrr δ hd) ≠ 0 := by
      obtain ⟨ψ⟩ := jac_equiv_of_equiv (stdBlocks (fun a => (x a).1) hx) φ
      unfold jm at hj ⊢
      rwa [← jhMult_congr_right _ ψ]
    obtain ⟨y, hr, hcc, hyj, hxj⟩ := cells hG hBZ k h N δ hd x hx hjm
    intro t ht c hcx
    choose a ha using fun i j => (schur hA k (y i j) t).1
    have hcj : ∀ j, c j = ∏ i, a i j := fun j =>
      (schur hA k (x j) t).2.1 _ _ (hcx j)
        (scalarProd k h (fun i => y i j) (x j) (hcc j) t (fun i => a i j) (fun i => ha i j) (hxj j))
    have hcell : ∀ i, ‖a i 0‖ ≤ 1 ∧ ‖a i 0‖ * ‖a i 1‖ = 1 := fun i =>
      cell_exp hA hC (δ i) (hδ i).1 (hδ i).2 (y i) (hr i) (hyj i) t ht (a i) (ha i)
    have n0 : ‖c 0‖ ≤ 1 := by
      rw [hcj 0, norm_prod]
      exact Finset.prod_le_one (fun i _ => norm_nonneg _) (fun i _ => (hcell i).1)
    have n01 : ‖c 0‖ * ‖c 1‖ = 1 := by
      rw [hcj 0, hcj 1, norm_prod, norm_prod, ← Finset.prod_mul_distrib]
      exact Finset.prod_eq_one (fun i _ => (hcell i).2)
    refine ⟨fun j hj' => ?_, by rw [Fin.prod_univ_two]; exact n01⟩
    have hj0 : j = 0 := Fin.ext (by omega)
    subst hj0
    have hf : (Finset.univ.filter fun i : Fin 2 => i ≤ 0) = {0} := by decide
    rw [hf, Finset.prod_singleton]
    exact n0
