import Development.AutomorphicArithmetic.AutomorphicVarieties.TensorHomCubes.IsAcyclicSpace

noncomputable section

open CategoryTheory unitInterval Simplicial
open scoped Topology

namespace UpperTheory.V.KL

def cubeSimplex (n : ℕ) (w : Equiv.Perm (Fin n)) : C(stdSimplex ℝ (Fin (n + 1)), Fin n → I) where
  toFun t j := ⟨∑ k with (w.symm j).castSucc < k, t k,
    Finset.sum_nonneg fun k _ => stdSimplex.zero_le t k,
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun k _ _ => stdSimplex.zero_le t k).trans_eq
      (stdSimplex.sum_eq_one t)⟩
  continuous_toFun := continuous_pi fun _ => Continuous.subtype_mk
    (continuous_finset_sum _ fun k _ => (continuous_apply k).comp continuous_subtype_val) _

def sing (X : TopCat.{0}) {n : ℕ} (g : C(stdSimplex ℝ (Fin (n + 1)), X)) : ZZ ⟶ (singC X).X n :=
  (TopCat.toSSet.obj X).ιChainComplex ((X.toSSetObjEquiv (Opposite.op ⦋n⦌)).symm g)

def simplexFace {n : ℕ} (k : Fin (n + 2)) : C(stdSimplex ℝ (Fin (n + 1)), stdSimplex ℝ (Fin (n + 2))) :=
  ⟨stdSimplex.map k.succAbove, stdSimplex.continuous_map _⟩

def cubeChain (X : TopCat.{0}) {n : ℕ} (F : C(Fin n → I, X)) : ZZ ⟶ (singC X).X n :=
  ∑ w : Equiv.Perm (Fin n), ((Equiv.Perm.sign w : ℤˣ) : ℤ) • sing X (F.comp (cubeSimplex n w))

def cubeFace {n : ℕ} (i : Fin (n + 1)) (s : I) : C(Fin n → I, Fin (n + 1) → I) :=
  ⟨fun y => i.insertNth s y, by fun_prop⟩

def IsHurewicz (X : TopCat.{0}) (x : X) (n : ℕ) (h : HomotopyGroup.Pi n X x → singH X n) : Prop :=
  ∀ f : GenLoop (Fin n) X x, ∃ z : ZZ ⟶ (singC X).cycles n,
    z ≫ (singC X).iCycles n = cubeChain X f.1 ∧
      h (Quotient.mk (GenLoop.Homotopic.setoid (Fin n) x) f) = (z ≫ (singC X).homologyπ n).hom (1 : ℤ)

def ArlAdm (p k : ℕ) : Prop :=
  ∃ a : ℕ →₀ ℕ, a 0 % (2 * p - 2) = 0 ∧ (∀ i, a (i + 1) % (2 * p - 2) ≤ 1) ∧ (∀ i, p * a (i + 1) ≤ a i) ∧
    (a.sum fun _ x => x) = k

open Classical in

def arlL (k : ℕ) : ℕ := ∏ p ∈ Finset.range (k + 1) with p.Prime ∧ ArlAdm p k, p

def arlR (j : ℕ) : ℕ := ∏ k ∈ Finset.Icc 1 j, arlL k

end UpperTheory.V.KL

end
