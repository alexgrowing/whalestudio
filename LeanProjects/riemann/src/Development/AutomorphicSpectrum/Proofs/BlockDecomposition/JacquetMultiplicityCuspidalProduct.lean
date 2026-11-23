import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IrreducibleAdmissibleGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GeometricLemma
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.BernsteinZelevinskyFiniteness
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.IsSubquotientCompMulSingle
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalCellMultiplicityOfSizeMatrixStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SizeMatrixPermutationEquivsExistStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg

noncomputable section

namespace GlobalTheory.CompanionTheory.CuspJm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def IsPermCell {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) : Prop :=
  ∃ e : Fin c ≃ Fin l, (∀ a, y a = x (e a)) ∧ ∀ i j, b.1 i j = if e j = i then (x i).1 else 0

def permMatrix {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (e : Fin c ≃ Fin l)
    (h : ∀ a, y a = x (e a)) : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) :=
  ⟨fun i j => if e j = i then (x i).1 else 0, fun i => by
    rw [Finset.sum_eq_single (e.symm i) (fun j _ hj => if_neg fun h' => hj (by rw [← h', e.symm_apply_apply]))
      (by simp)]
    simp, fun j => by
    rw [Finset.sum_ite_eq]
    simp [h j]⟩

set_option maxHeartbeats 2000000 in

theorem exists_choice (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) :
    ∃ (f : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ (b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      ∀ b, IsPermCell x y b →
        jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) = 1 := by
  classical
  have key : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), IsPermCell x y b → ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1)
      (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    rintro b ⟨e, he, hb⟩
    exact GlobalTheory.T.size_matrix_permutation_equivs_exist hA x y e he b hb
  have key' : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), ∃ (f : ∀ i, (Σ j, Fin (b.1 i j)) ≃ Fin (x i).1) (g : ∀ j, (Σ i, Fin (b.1 i j)) ≃ Fin (y j).1),
      IsPermCell x y b → jhMult (piTensor fun j => (y j).rep) (cellFunctor f g (piTensor fun i => (x i).rep)) = 1 := by
    intro b
    by_cases h : IsPermCell x y b
    · obtain ⟨f, g, hfg⟩ := key b h
      exact ⟨f, g, fun _ => hfg⟩
    · exact ⟨b.nonempty_rows.some, b.nonempty_cols.some, fun h' => absurd h' h⟩
  choose f g hfg using key'
  exact ⟨f, g, hfg⟩

theorem card_permCell {l c : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k) (hxc : ∀ a, (x a).IsCusp)
    [Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1))] [DecidablePred (IsPermCell x y)] :
    (Finset.univ.filter (IsPermCell x y)).card = Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} := by
  classical
  rw [Set.ncard_eq_toFinset_card']
  symm
  refine Finset.card_bij (fun e he => permMatrix x y e (Set.mem_toFinset.1 he)) ?_ ?_ ?_
  · intro e he
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, e, Set.mem_toFinset.1 he, fun i j => rfl⟩
  · intro e he e' he' H
    refine Equiv.ext fun j => ?_
    have h2 := congrArg (fun b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1) => b.1 (e j) j) H
    simp only [permMatrix, if_true] at h2
    by_contra hne
    rw [if_neg (Ne.symm hne)] at h2
    exact (hxc (e j)).1.ne' h2
  · intro b hb
    obtain ⟨e, he, hb⟩ := (Finset.mem_filter.1 hb).2
    exact ⟨e, Set.mem_toFinset.2 he, Subtype.ext (funext fun i => funext fun j => (hb i j).symm)⟩

set_option maxHeartbeats 1000000 in

theorem main (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) {l c N : ℕ} (x : Fin l → IrrGL k) (y : Fin c → IrrGL k)
    (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) (hxc : ∀ a, (x a).IsCusp) (hyc : ∀ a, (y a).IsCusp) :
    jm y hy (prodIrr x hx) = (Set.ncard {e : Fin c ≃ Fin l | ∀ a, y a = x (e a)} : ℕ∞) := by
  classical
  haveI : Fintype (SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1)) := Fintype.ofFinite _
  obtain ⟨f, g, hfg⟩ := exists_choice hA x y
  have hτ : (piTensor fun j => (y j).rep).IsIrreducible :=
    GlobalTheory.T.piExteriorTensor_smoothIrreducible_isIrreducible GlobalTheory.CompanionTheory.Published.bernsteinZelevinskyFiniteness k _ _ fun j => (y j).2.rep
  have h1 := (GlobalTheory.CompanionTheory.GeoLink.geometricLemma k).1.jhMult_eq (stdBlocks (fun a => (x a).1) hx)
    (stdBlocks (fun a => (y a).1) hy) (isSmooth_piTensor fun i => (x i).2.rep.smooth) f g hτ
  have hterm : ∀ b : SizeMatrix (fun i => Fin (x i).1) (fun j => Fin (y j).1), jhMult (piTensor fun j => (y j).rep) (cellFunctor (f b) (g b) (piTensor fun i => (x i).rep)) =
      if IsPermCell x y b then 1 else 0 := by
    intro b
    split_ifs with h
    · exact hfg b h
    · by_contra hne
      exact h (GlobalTheory.T.cuspidal_cell_multiplicity_of_size_matrix x y hxc hyc b (f b) (g b) hne)
  have h2 : jm y hy (prodIrr x hx) = jhMult (piTensor fun j => (y j).rep)
      (jac (stdBlocks (fun a => (y a).1) hy) (parInd (stdBlocks (fun a => (x a).1) hx)
        (piTensor fun i => (x i).rep))) := rfl
  rw [h2, h1, Finset.sum_congr rfl fun b _ => hterm b, Finset.sum_boole, card_permCell x y hxc]

end GlobalTheory.CompanionTheory.CuspJm
