import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.ZelevinskyCosocles.LUnlinkedComm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DropHom
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardBlocksReindexStrictMonoStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TensorProductDropZeroFactorsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JordanHolderMultiplicityJacquetEqBorelJacquetOfS

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Cos Matrix

namespace GlobalTheory.CompanionTheory.FineProd.JmDrop

section Blocks

variable {R : Type} [Field R] {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem dropHom_surjective (ho : Function.Injective o) :
    Function.Surjective (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o) := by
  classical
  intro x
  have key : ∀ (j : Fin r) (b : Fin r') (hb : o b = j) (a : Fin r') (ha : o a = j),
      (hb ▸ x b : GL (Fin (d j)) R) = ha ▸ x a := by
    intro j b hb a ha
    obtain rfl : b = a := ho (hb.trans ha.symm)
    rfl
  refine ⟨(fun j => if hj : ∃ a, o a = j then hj.choose_spec ▸ x hj.choose else 1 :
    ∀ j, GL (Fin (d j)) R), ?_⟩
  funext a
  have hj : ∃ b, o b = o a := ⟨a, rfl⟩
  show (if hj : ∃ b, o b = o a then (hj.choose_spec ▸ x hj.choose : GL (Fin (d (o a))) R) else 1) = x a
  rw [dif_pos hj]
  exact key (o a) _ hj.choose_spec a rfl

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}

theorem unipRad_eq (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) : unipRad R e = unipRad R e' := by
  ext g
  rw [GlobalTheory.SmGL.mem_unipRad, GlobalTheory.SmGL.mem_unipRad,
    GlobalTheory.SmGL.mem_parab_iff, GlobalTheory.SmGL.mem_parab_iff]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a b i j hab => ?_, fun a i j => ?_⟩
    · rw [he, he]
      exact h1 _ _ i j (hm hab)
    · rw [he, he]
      exact h2 _ i j
  · rintro ⟨h1, h2⟩
    refine ⟨fun A B i j hBA => ?_, fun A i j => ?_⟩
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      obtain ⟨b, rfl⟩ := hne B (Fin.pos j).ne'
      rw [← he, ← he]
      exact h1 a b i j (hm.lt_iff_lt.1 hBA)
    · obtain ⟨a, rfl⟩ := hne A (Fin.pos i).ne'
      rw [← he, ← he]
      exact h2 a i j

theorem leviEmb_eq (hm : StrictMono o) (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩)
    (g : Levi R fun j => Fin (d j)) :
    leviEmb R e g = leviEmb R e' (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) := by
  apply Units.ext
  ext p q
  obtain ⟨⟨a, i⟩, rfl⟩ := e'.surjective p
  obtain ⟨⟨b, j⟩, rfl⟩ := e'.surjective q
  by_cases hab : a = b
  · subst hab
    have h1 := GlobalTheory.SmGL.leviEmb_apply_same R e g (o a) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_same R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) a i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm
  · have h1 := GlobalTheory.SmGL.leviEmb_apply_ne R e g (hm.injective.ne hab) i j
    have h2 := GlobalTheory.SmGL.leviEmb_apply_ne R e'
      (GlobalTheory.CompanionTheory.FineProd.dropHom (k := R) d o g) hab i j
    rw [← he, ← he] at h1
    exact h1.trans h2.symm

omit [Fintype n] [DecidableEq n] in

theorem modExp_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o) (a : Fin r') :
    modExp (fun b => Fin (d (o b))) a = modExp (fun j => Fin (d j)) (o a) := by
  unfold GlobalTheory.SmGL.modExp
  congr 1
  all_goals
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Fintype.sum_of_injective o hm.injective _ _ (fun j hj => ?_) (fun b => ?_)
    · by_cases hd : d j = 0
      · simp [hd]
      · exact absurd (hne j hd) hj
    · simp [hm.lt_iff_lt]

end Blocks

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r r' : ℕ} {d : Fin r → ℕ} {o : Fin r' → Fin r}

theorem deltaHalf_drop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (g : Levi k fun j => Fin (d j)) :
    deltaHalf k (fun j => Fin (d j)) g =
      deltaHalf k (fun a => Fin (d (o a))) (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) := by
  rw [GlobalTheory.SmGL.deltaHalf_apply, GlobalTheory.SmGL.deltaHalf_apply]
  symm
  refine Fintype.prod_of_injective o hm.injective _ _ (fun j hj => ?_) (fun a => ?_)
  · have hd : d j = 0 := by
      by_contra hd
      exact hj (hne j hd)
    haveI : IsEmpty (Fin (d j)) := by
      rw [hd]
      infer_instance
    have hdet : Matrix.GeneralLinearGroup.det (g j) = 1 := by
      ext
      simp [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_isEmpty]
    rw [hdet, map_one]
  · rw [GlobalTheory.CompanionTheory.FineProd.JmDrop.modExp_drop hm hne a]
    first
    | rfl
    | skip

variable {n : Type} [Fintype n] [DecidableEq n]
  {e : (Σ j, Fin (d j)) ≃ n} {e' : (Σ a, Fin (d (o a))) ≃ n}
  {V : Type} [AddCommGroup V] [Module ℂ V]

def jacDrop (hm : StrictMono o) (hne : ∀ j, d j ≠ 0 → j ∈ Set.range o)
    (he : ∀ a t, e' ⟨a, t⟩ = e ⟨o a, t⟩) (π : Representation ℂ (GL n k) V) :
    (jac e π).Equiv
      ((jac e' π).comp (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o) :
        Representation ℂ (Levi k fun j => Fin (d j)) _) :=
  have h3 : twKer π (unipRad k e) 1 = twKer π (unipRad k e') 1 := by rw [unipRad_eq hm hne he]
  .mk (Submodule.quotEquivOfEq _ _ h3) fun g => by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun v => ?_)
    show Submodule.quotEquivOfEq _ _ h3 (jac e π g (Submodule.Quotient.mk v)) =
      jac e' π (GlobalTheory.CompanionTheory.FineProd.dropHom (k := k) d o g) (Submodule.Quotient.mk v)
    rw [jac_mk, jac_mk, map_smul, deltaHalf_drop hm hne, leviEmb_eq hm he]
    rfl

end Local

theorem jm_drop : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {r r' N : ℕ} (y : Fin r → IrrGL k) (hd : ∑ a, (y a).1 = N) (o : Fin r' → Fin r), StrictMono o → (∀ j, (y j).1 ≠ 0 → j ∈ Set.range o) → ∀ (hd' : ∑ a, (y (o a)).1 = N) {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V), jm y hd π = jm (fun a => y (o a)) hd' π := by
  intro k _ _ _ _ r r' N y hd o hm hne hd' V _ _ π
  have he := GlobalTheory.T.standard_blocks_reindex_strictMono (fun j => (y j).1) hd o hm hne hd'
  obtain ⟨φ⟩ := GlobalTheory.T.tensor_product_drop_zero_factors y o hm hne
  unfold Zc.jm
  rw [GlobalTheory.SmGL.jhMult_congr_left φ,
    GlobalTheory.SmGL.jhMult_congr_right _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.jacDrop (d := fun j => (y j).1) (o := o) hm hne he π),
    GlobalTheory.SmGL.EmptyBlocks.jhMult_comp_surjective _
      (GlobalTheory.CompanionTheory.FineProd.JmDrop.dropHom_surjective (R := k) (d := fun j => (y j).1) hm.injective)]

end GlobalTheory.CompanionTheory.FineProd.JmDrop

end
