import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMono
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactors
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos

namespace GlobalTheory.CompanionTheory.FineProd.ProdDrop

section Blocks

variable (k : Type) [Field k] {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz

theorem mem_parab_drop (g : GL (Fin N) k) :
    g ∈ parab k (stdBlocks d hd) ↔ g ∈ parab k (stdBlocks (fun a => d (o a)) hd') := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  rw [mem_parab_iff, mem_parab_iff]
  constructor
  · intro h a b i j hab
    rw [hE, hE]
    exact h _ _ i j (ho hab)
  · intro h a b i j hab
    obtain ⟨a, rfl⟩ := hz a (Nat.pos_iff_ne_zero.1 (Fin.pos i))
    obtain ⟨b, rfl⟩ := hz b (Nat.pos_iff_ne_zero.1 (Fin.pos j))
    have := h a b i j (ho.lt_iff_lt.1 hab)
    rwa [hE, hE] at this

theorem dropHom_leviProj (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd'))
    (h : (p : GL (Fin N) k) = q) :
    dropHom d o (leviProj k (stdBlocks d hd) p) = leviProj k (stdBlocks (fun a => d (o a)) hd') q := by
  have hE := GlobalTheory.CompanionTheory.StdCompat.stdBlocks_drop_empty d hd o ho hz hd'
  funext a
  ext i j
  show (leviProj k (stdBlocks d hd) p (o a) : Matrix _ _ k) i j = _
  rw [leviProj_apply, leviProj_apply, hE, hE, h]

theorem modExp_drop (a : Fin r') :
    modExp (fun j => Fin (d j)) (o a) = modExp (fun b => Fin (d (o b))) a := by
  have h0 : ∀ j, j ∉ Set.range o → d j = 0 := fun j hj => by_contra fun h => hj (hz j h)
  unfold modExp
  simp only [Fintype.card_fin, Finset.sum_filter]
  congr 1
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]
  · refine (Fintype.sum_of_injective o ho.injective _ _ (fun j hj => ?_) fun b => ?_).symm
    · simp [h0 j hj]
    · simp [ho.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' N : ℕ} (d : Fin r → ℕ) (hd : ∑ a, d a = N) (o : Fin r' → Fin r)
  (ho : StrictMono o) (hz : ∀ j, d j ≠ 0 → j ∈ Set.range o) (hd' : ∑ a, d (o a) = N)

include ho hz in

theorem deltaHalf_drop (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g = deltaHalf k (fun a => Fin (d (o a))) (dropHom d o g) := by
  rw [deltaHalf_apply, deltaHalf_apply]
  refine (Fintype.prod_of_injective o ho.injective _ _ (fun j hj => ?_) fun a => ?_).symm
  · have hj0 : d j = 0 := by_contra fun h => hj (hz j h)
    have : IsEmpty (Fin (d j)) := by rw [hj0]; infer_instance
    have h1 : Matrix.GeneralLinearGroup.det (g j) = 1 := Units.ext (by simp [Matrix.det_isEmpty])
    rw [h1, map_one]
  · rw [modExp_drop d o ho hz]
    rfl

include ho hz in

theorem parInd_comp_dropHom_equiv {W : Type} [AddCommGroup W] [Module ℂ W]
    (τ : Representation ℂ (Levi k fun a => Fin (d (o a))) W) :
    Nonempty ((parInd (stdBlocks d hd) (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W)).Equiv
      (parInd (stdBlocks (fun a => d (o a)) hd') τ)) := by
  have key : ∀ (p : parab k (stdBlocks d hd)) (q : parab k (stdBlocks (fun a => d (o a)) hd')),
      (p : GL (Fin N) k) = q →
      twist (τ.comp (dropHom d o) : Representation ℂ (Levi k fun j => Fin (d j)) W) (deltaHalf k _)
          (leviProj k (stdBlocks d hd) p) =
        twist τ (deltaHalf k _) (leviProj k (stdBlocks (fun a => d (o a)) hd') q) := fun p q h => by
    refine LinearMap.ext fun v => ?_
    rw [twist_apply, twist_apply, deltaHalf_drop d o ho hz, dropHom_leviProj k d hd o ho hz hd' p q h]
    show _ • τ (dropHom d o _) v = _
    rw [dropHom_leviProj k d hd o ho hz hd' p q h]
  refine Placing.smInd_equiv 1
    (fun q => ⟨⟨q.1, (mem_parab_drop k d hd o ho hz hd' q.1).2 q.2⟩, by simp, key _ _ rfl⟩)
    (fun p => ⟨⟨p.1, (mem_parab_drop k d hd o ho hz hd' p.1).1 p.2⟩, by simp, (key _ _ rfl).symm⟩)

end Local

set_option maxHeartbeats 1000000 in

theorem prodIrr_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N), Nonempty ((prodIrr y hd).Equiv (prodIrr (fun a => y (o a)) hd')) := by
  intro k _ _ _ _ r r' N y hd o ho hz hd'
  obtain ⟨φ⟩ := GlobalTheory.CompanionTheory.FineProd.TensorLine.piTensor_drop_equiv y o ho hz
  obtain ⟨χ⟩ := parInd_comp_dropHom_equiv (k := k) (fun j => (y j).1) hd o ho hz hd'
    (piTensor fun a => (y (o a)).rep)
  have e1 := parIndEquiv (stdBlocks (fun j => (y j).1) hd) φ
  have e2 := e1.trans χ
  unfold prodIrr multiProd
  exact ⟨e2⟩

end GlobalTheory.CompanionTheory.FineProd.ProdDrop

end
