import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.EisCellsDefs
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryUnnSubgroupEqTopOfLeviUnipotentWeyl

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.RatGen

open GlobalTheory.StdUnn.Model GlobalTheory.StdUnn.Gen

variable {D : D7} {n : ℕ}

abbrev rm (x : Matrix (Fin n) (Fin n) D.host.E) : Mx D n n := x.map (incA D)

theorem rm_mul (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x * y) = rm x * rm y :=
  Matrix.map_mul

theorem rm_add (x y : Matrix (Fin n) (Fin n) D.host.E) : rm (x + y) = rm x + rm y :=
  Matrix.map_add _ (map_add _) x y

theorem rm_neg (x : Matrix (Fin n) (Fin n) D.host.E) : rm (-x) = -rm x := by
  ext i j; simp [rm]

theorem rm_one : rm (1 : Matrix (Fin n) (Fin n) D.host.E) = 1 := by
  simp [rm]

theorem rm_zero : rm (0 : Matrix (Fin n) (Fin n) D.host.E) = 0 := by
  simp [rm]

theorem blockMatrix_map (a b c d : Matrix (Fin n) (Fin n) D.host.E) :
    (blk4 a b c d).map (incA D) = blk4 (rm a) (rm b) (rm c) (rm d) := by
  ext i j
  simp only [blk4, Matrix.map_apply, Matrix.submatrix_apply]
  rcases finSumFinEquiv.symm i with i | i <;> rcases finSumFinEquiv.symm j with j | j <;> rfl

def ru (u : GL (Fin n) D.host.E) : GL (Fin n) (AE D) := Units.map (incA D).mapMatrix.toMonoidHom u

theorem ru_val (u : GL (Fin n) D.host.E) : (ru u).1 = rm u.1 := rfl

theorem ru_inv_val (u : GL (Fin n) D.host.E) : ((ru u)⁻¹).1 = rm (u⁻¹).1 := rfl

variable {S : Subgroup (G D n)}
  (hm : ∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S)
  (hn : ∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S)
  (hw : ∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S)

include hm hn in
theorem mem_of_upper {g : G D n} {a b d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) (rm b) 0 (rm d))
    (ha : IsUnit a) : g ∈ S := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨m, hmm⟩ := exists_levi (D := D) (n := n) (ru u)⁻¹
  have hmm' : mat m = blk4 (rm (u⁻¹).1) 0 0 (adj (rm u.1)) := by
    rw [hmm, ru_inv_val, inv_inv, ru_val]
  have h1 : (adj (rm u.1) : Mx D n n) * rm d = 1 := by simpa using (rel hg).2.1
  have hmS : m ∈ S := hm m u⁻¹ (by rw [hmm', inv_inv])
  rw [← S.mul_mem_cancel_left hmS]
  refine hn _ ((u⁻¹).1 * b) ?_
  have h2 : rm (u⁻¹).1 * rm u.1 = 1 := by
    rw [← rm_mul, Units.inv_mul, rm_one]
  rw [mat_mul, hmm', hg, submatrix_fromBlocks_mul]
  simp only [h2, mul_zero, zero_mul, add_zero, zero_add, h1]
  change _ = blk4 1 (rm _) 0 1
  rw [rm_mul]

include hm hn hw in
theorem mem_of_lower {g : G D n} {a c d : Matrix (Fin n) (Fin n) D.host.E} (hg : mat g = blk4 (rm a) 0 (rm c) (rm d))
    (hd : IsUnit d) : g ∈ S := by
  obtain ⟨w, hww⟩ := exists_weyl (D := D) (n := n)
  rw [← S.mul_mem_cancel_left (hw w hww), ← S.mul_mem_cancel_right (hw w hww)]
  refine mem_of_upper hm hn (a := -d) (b := c) (d := -a) ?_ hd.neg
  rw [mat_mul, mat_mul, hww, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul, rm_neg, rm_neg]
  simp

include hm hn hw in
theorem mem_of_isUnit {g : G D n} {a b c d : Matrix (Fin n) (Fin n) D.host.E}
    (hg : mat g = blk4 (rm a) (rm b) (rm c) (rm d)) (hd : IsUnit d) : g ∈ S := by
  obtain ⟨u, rfl⟩ := hd
  have h1 : (adj (rm u.1) : Mx D n n) * rm b = adj (rm b) * rm u.1 := neg_add_eq_zero.1 (rel hg).2.2
  have h0 : rm u.1 * rm (u⁻¹).1 = 1 := by rw [← rm_mul, Units.mul_inv, rm_one]
  have h0' : rm (u⁻¹).1 * rm u.1 = 1 := by rw [← rm_mul, Units.inv_mul, rm_one]
  have h2 : (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm u.1) = 1 := by rw [← adj_mul, h0, adj_one]
  have h3 : (adj (-(rm b * rm (u⁻¹).1)) : Mx D n n) = -(rm b * rm (u⁻¹).1) := by
    rw [adj_neg, adj_mul]
    congr 1
    calc (adj (rm (u⁻¹).1) : Mx D n n) * adj (rm b) = adj (rm (u⁻¹).1) * (adj (rm b) * rm u.1) * rm (u⁻¹).1 := by
          rw [mul_assoc, mul_assoc, h0, mul_one]
      _ = rm b * rm (u⁻¹).1 := by rw [← h1, ← mul_assoc, h2, one_mul]
  obtain ⟨x, hx⟩ := (exists_unip _).2 h3
  have hxS : x ∈ S := hn x (-(b * (u⁻¹).1)) (by rw [hx]; change _ = blk4 1 (rm _) 0 1; rw [rm_neg, rm_mul])
  rw [← S.mul_mem_cancel_left hxS]
  refine mem_of_lower hm hn hw (a := a + -(b * (u⁻¹).1) * c) (c := c) (d := u.1) ?_ u.isUnit
  rw [mat_mul, hx, hg, submatrix_fromBlocks_mul, rm_add, rm_mul, rm_neg, rm_mul]
  simp only [one_mul, zero_mul, zero_add, neg_mul, mul_assoc, h0', mul_one, add_neg_cancel]

theorem adj_rm {x : Matrix (Fin n) (Fin n) D.host.E} (hx : ∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) :
    adj (rm x : Mx D n n) = rm x := by
  ext i j
  simp only [adj, Matrix.transpose_apply, Matrix.map_apply]
  rw [GlobalTheory.DualPairCheck.cA_incA]
  exact congrArg _ (hx j i)

theorem exists_herm_isUnit (c d p q : Matrix (Fin n) (Fin n) D.host.E) (h : c * p + d * q = 1) :
    ∃ x : Matrix (Fin n) (Fin n) D.host.E, (∀ i j, (D.sp.cm.sig : D.host.E →+* D.host.E) (x i j) = x j i) ∧
      IsUnit (c * x + d) := by
  obtain ⟨x, hx, hu⟩ := GlobalTheory.HermTransversal.exists_herm_notMem (D.sp.cm.sig : D.host.E →+* D.host.E) D.host.xi0
    (GlobalTheory.DualPairCompare.embedding_xi_zero_ne_zero D) (GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D) (RingHom.id _) (D.sp.cm.sig : D.host.E →+* D.host.E)
    (fun _ => rfl) c d p q h ⊥ Ideal.bot_isMaximal
  refine ⟨x, hx, ?_⟩
  have e : x.map (RingHom.id D.host.E) = x := by ext i j; rfl
  rw [e] at hu
  refine (Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 fun h0 => hu ?_)
  rw [h0, zero_mul]
  exact Ideal.zero_mem _

end GlobalTheory.CompanionTheory.RatGen

namespace GlobalTheory.CompanionTheory

theorem RatGen.GF_le_of_levi_unip_weyl : ∀ (D : D7) (n : ℕ) (S : Subgroup (G D n)),
  (∀ (g : G D n) (a : GL (Fin n) D.host.E), mat g = blk4 (a.1.map (incA D)) 0 0 (adj ((a⁻¹).1.map (incA D))) → g ∈ S) →
  (∀ (g : G D n) (b : Matrix (Fin n) (Fin n) D.host.E), mat g = blk4 1 (b.map (incA D)) 0 1 → g ∈ S) →
  (∀ g : G D n, mat g = blk4 0 1 (-1) 0 → g ∈ S) → GF D n ≤ S := by
  intro D n S hm hn hw γ hγ
  have hrat : ∀ {γ : G D n}, γ ∈ GF D n →
      ∃ x : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E, mat γ = x.map (incA D) := by
    intro γ h
    obtain ⟨x, -, hx⟩ := h
    exact ⟨x.1, (congrArg Units.val hx).symm⟩
  obtain ⟨M, hM⟩ := hrat hγ
  obtain ⟨M', hM'⟩ := hrat ((GF D n).inv_mem hγ)
  obtain ⟨a, b, c, d, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M
  obtain ⟨p', p, q', q, rfl⟩ := GlobalTheory.StdUnn.Gen.exists_blockMatrixTwoByTwoFin_eq M'
  rw [RatGen.blockMatrix_map] at hM hM'
  have h1 : mat γ * mat γ⁻¹ = 1 := by rw [← GlobalTheory.StdUnn.Gen.mat_mul, mul_inv_cancel]; rfl
  rw [hM, hM', Model.submatrix_fromBlocks_mul, ← Model.block_matrix_one] at h1
  have h2 : RatGen.rm (c * p + d * q) = RatGen.rm (1 : Matrix (Fin n) (Fin n) D.host.E) := by
    rw [RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul, RatGen.rm_one]
    exact (Model.blockMatrixTwoByTwoFin_injective h1).2.2.2
  have h3 : c * p + d * q = 1 := Matrix.map_injective GlobalTheory.MixModel.incA_injective h2
  obtain ⟨x, hx, hu⟩ := RatGen.exists_herm_isUnit c d p q h3
  obtain ⟨y, hy⟩ := (Model.exists_unip (RatGen.rm x)).2 (RatGen.adj_rm hx)
  rw [← S.mul_mem_cancel_right (hn y x hy)]
  refine RatGen.mem_of_isUnit hm hn hw (a := a) (b := a * x + b) (c := c) (d := c * x + d) ?_ hu
  rw [GlobalTheory.StdUnn.Gen.mat_mul, hM, hy, Model.submatrix_fromBlocks_mul, RatGen.rm_add, RatGen.rm_add, RatGen.rm_mul, RatGen.rm_mul]
  simp only [mul_one, mul_zero, add_zero]

end GlobalTheory.CompanionTheory
