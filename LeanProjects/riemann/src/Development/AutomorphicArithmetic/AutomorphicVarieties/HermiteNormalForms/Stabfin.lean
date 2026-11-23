import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Rypos
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Locfin
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Spanpsd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.Exbasis

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

theorem UpperTheory.V.KT.stabfin :
    ∀ (L : Type) [Field L] [NumberField L] [IsTotallyComplex L] (N : ℕ) (v : Vx L N),
    Finite (MulAction.stabilizer (Gm L N) v) := by
  intro L _ _ _ N v
  classical
  have hpoly : v.1 ∈ Ry L N := by
    rw [← poly_qc]
    exact v.2.1
  obtain ⟨S, hSfin, hev⟩ := locfin L N v.1 (rypos L N hpoly) 1
  have hS : ∀ y, q v.1 y = 1 → y ∈ S := by
    intro y hy
    by_contra hyS
    have := hev.self_of_nhds y hyS
    linarith
  have hspan : Spans (minVec v.1) :=
    spanpsd L N _ (fun k _ hk => v.2.2 k (fun y hy => hk y.1 hy))
  obtain ⟨A, hA, hAcol⟩ := exbasis L N _ hspan
  have hinv : ∀ g ∈ MulAction.stabilizer (Gm L N) v, ∀ y, q v.1 y = 1 → q v.1 (g • y) = 1 := by
    intro g hg y hy
    have hgh : g • v.1 = v.1 := congrArg Subtype.val (MulAction.mem_stabilizer_iff.mp hg)
    have hgh' : g⁻¹ • v.1 = v.1 := inv_smul_eq_iff.2 hgh.symm
    calc q v.1 (g • y) = q v.1 (g⁻¹⁻¹ • y) := by rw [inv_inv]
      _ = q (g⁻¹ • v.1) y := (q_smul g⁻¹ v.1 y).symm
      _ = q v.1 y := by rw [hgh']
      _ = 1 := hy
  haveI : Finite S := hSfin.to_subtype
  let φ : MulAction.stabilizer (Gm L N) v → (Fin N → S) := fun g a =>
    ⟨(g : Gm L N) • (fun i => A i a), hS _ (hinv g.1 g.2 _ (hAcol a))⟩
  refine Finite.of_injective φ ?_
  intro g g' hgg
  have hcol : ∀ a, (g : Gm L N) • (fun i => A i a) = (g' : Gm L N) • (fun i => A i a) :=
    fun a => congrArg Subtype.val (congrFun hgg a)
  have hM : ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A =
      ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) * A :=
    Matrix.ext fun i a => congrFun (hcol a) i
  have hM2 : A.det • ((g : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) =
      A.det • ((g' : Gm L N) : Matrix (Fin N) (Fin N) (𝓞 L)) := by
    have h2 := congrArg (· * A.adjugate) hM
    simp only [Matrix.mul_assoc, Matrix.mul_adjugate, Matrix.mul_smul, Matrix.mul_one] at h2
    exact h2
  exact Subtype.ext (Units.ext (smul_right_injective _ hA hM2))
