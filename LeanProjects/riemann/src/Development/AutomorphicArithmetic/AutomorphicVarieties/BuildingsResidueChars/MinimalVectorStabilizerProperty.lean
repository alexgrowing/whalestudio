import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TupleActions.InstMulActionTup
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped Pointwise

theorem UpperTheory.minimal_vector_stabilizer_property :
    UpperTheory.V.Af.BA.MinStab := by
  intro L _ _ _ N h hv hsp
  classical
  have hfin : (minVec h).Finite := by
    obtain ⟨S, hS, hev⟩ := locfin L N h (rypos L N hv) 1
    refine hS.subset fun y hy => ?_
    by_contra hn
    exact (hev.self_of_nhds y hn).ne' hy
  obtain ⟨A, hA, hcol⟩ := exbasis L N _ hsp
  haveI : Finite (minVec h) := hfin.to_subtype
  have hmem : ∀ (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N),
      (g.1 • (fun i => A i a : Lat L N)) ∈ minVec h := fun g a => by
    have h1 : g.1 • minVec h = minVec h := g.2
    have h2 := Set.smul_mem_smul_set (a := g.1) (hcol a)
    rw [h1] at h2
    exact h2
  refine Finite.of_injective
    (fun (g : MulAction.stabilizer (Gm L N) (minVec h)) (a : Fin N) =>
      (⟨_, hmem g a⟩ : minVec h)) fun g k e => ?_
  have h1 : (g.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      (k.1 : Matrix (Fin N) (Fin N) (𝓞 L)) * A := by
    refine Matrix.ext fun i a => ?_
    exact congrFun (congrArg Subtype.val (congrFun e a)) i
  have h2 := congrArg (· * A.adjugate) h1
  simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
  refine Subtype.ext (Units.ext ?_)
  refine Matrix.ext fun i j => ?_
  exact mul_left_cancel₀ hA (congrFun (congrFun h2 i) j)
