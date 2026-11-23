import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductBlockRenamingEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParabolicInductionProductEquivOfNoBlocksStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InductionInStagesTwoFactorsEquivStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LexSumSplitFirstBlockStrictMonoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinSigmaFinEquivSymmStrictMonoToLexStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil

noncomputable section
open ValuativeRel Matrix GlobalTheory.SmGL.MultiIrr GlobalTheory.LocGL
open scoped TensorProduct

namespace GlobalTheory.SmGL.Stages

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem ind₂_equiv_right {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    [AddCommGroup U] [Module ℂ U] (h : a ⊕ b ≃ n) (A : Representation ℂ (GL a k) V)
    {B : Representation ℂ (GL b k) W} {B' : Representation ℂ (GL b k) U} (φ : B.Equiv B') :
    Nonempty ((ind₂ h (extTensor A B)).Equiv (ind₂ h (extTensor A B'))) := by
  refine ⟨parIndEquiv _ (compEquiv (.mk (φ.toLinearEquiv.lTensor V) fun g => ?_) _)⟩
  refine TensorProduct.ext' fun v w => ?_
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.lTensor_tmul, extTensor_tmul]
  congr 1
  exact φ.toIntertwiningMap.isIntertwining _ _ _ _

theorem piTensor_tmulEquivDep {β₀ β₁ : Type} {Γ X : β₀ ⊕ₗ β₁ → Type} [∀ c, Group (Γ c)]
    [∀ c, AddCommGroup (X c)] [∀ c, Module ℂ (X c)] (ρ : ∀ c, Representation ℂ (Γ c) (X c)) (g : ∀ c, Γ c)
    (x : (⨂[ℂ] i, X (toLex (.inl i))) ⊗[ℂ] (⨂[ℂ] j, X (toLex (.inr j)))) :
    piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c)) x) =
      PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
      (TensorProduct.map (piTensor (fun i => ρ (toLex (.inl i))) fun i => g (toLex (.inl i)))
        (piTensor (fun j => ρ (toLex (.inr j))) fun j => g (toLex (.inr j))) x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [map_zero]; exact map_zero (piTensor ρ g)
  | add x y hx hy => simp only [map_add]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hx, hy]; rfl)
  | tmul v w =>
    induction v using PiTensorProduct.induction_on with
    | add v v' hv hv' => simp only [TensorProduct.add_tmul, map_add]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hv, hv']; rfl)
    | smul_tprod c v =>
      induction w using PiTensorProduct.induction_on with
      | add w w' hw hw' => simp only [TensorProduct.tmul_add, map_add]; exact (map_add (piTensor ρ g) _ _).trans (by rw [hw, hw']; rfl)
      | smul_tprod c' w =>
        have key : piTensor ρ g (PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
            (PiTensorProduct.tprod ℂ v ⊗ₜ PiTensorProduct.tprod ℂ w)) =
            PiTensorProduct.tmulEquivDep ℂ (fun c => X (toLex c))
              (PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inl a)) (g (toLex (.inl a))) (v a)) ⊗ₜ
                PiTensorProduct.tprod ℂ (fun a => ρ (toLex (.inr a)) (g (toLex (.inr a))) (w a))) := by
          rw [PiTensorProduct.tmulEquivDep_apply, PiTensorProduct.tmulEquivDep_apply]
          refine (piTensor_tprod ρ g _).trans ?_
          congr 1
          funext i
          rcases i with i | i <;> rfl
        simp only [TensorProduct.smul_tmul', TensorProduct.tmul_smul, map_smul, TensorProduct.map_tmul,
          piTensor_tprod]
        rw [← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul', ← TensorProduct.smul_tmul',
          ← TensorProduct.smul_tmul', map_smul, map_smul, map_smul, map_smul, ← key]
        exact (LinearMap.map_smul _ _ _).trans (congrArg _ (LinearMap.map_smul _ _ _))

def splitEquiv {s : ℕ} (t : Fin (s + 1) → ℕ) :
    (Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ)) ≃ Σₗ a, Fin (t a) where
  toFun c := Sum.elim (fun j => toLex (⟨0, j⟩ : Σ a, Fin (t a)))
    (fun x => toLex (⟨(ofLex x).1.succ, (ofLex x).2⟩ : Σ a, Fin (t a))) (ofLex c)
  invFun c := Fin.cases (motive := fun a => Fin (t a) → Fin (t 0) ⊕ₗ Σₗ i : Fin s, Fin (t i.succ))
    (fun j => toLex (.inl j)) (fun i j => toLex (.inr (toLex ⟨i, j⟩))) (ofLex c).1 (ofLex c).2
  left_inv c := by
    rcases c with j | ⟨i, j⟩ <;> rfl
  right_inv c := by
    obtain ⟨a, j⟩ := c
    induction a using Fin.cases <;> rfl

theorem stages_equiv (s : ℕ) : ∀ (d t : Fin s → ℕ) (d' : ∀ a, Fin (t a) → ℕ)
    (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a))
    (X : ∀ a, Fin (t a) → Type) [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (n : Type) [Fintype n] [DecidableEq n]
    (e : (Σ a, Fin (d a)) ≃ n),
    ∃ E : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n,
      Nonempty ((multiProd e fun a => multiProd (e' a) (ρ a)).Equiv
        (multiProd E fun c => ρ (ofLex c).1 (ofLex c).2)) := by
  induction s with
  | zero =>
    intro d t d' e' X _ _ ρ n _ _ e
    haveI : IsEmpty n := ⟨fun x => (e.symm x).1.elim0⟩
    haveI : IsEmpty (Σₗ a : Fin 0, Fin (t a)) := ⟨fun c => (ofLex c).1.elim0⟩
    haveI : IsEmpty (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) :=
      ⟨fun x => (ofLex x.1).1.elim0⟩
    let E : (Σ c : (Σₗ a : Fin 0, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      Equiv.equivOfIsEmpty _ _
    exact ⟨E, GlobalTheory.T.parabolicInductionProduct_equiv_of_no_blocks (k := k) _ _ _ _⟩
  | succ s ih =>
    intro d t d' e' X _ _ ρ n _ _ e
    have E1 := multiProd_succ_equiv (k := k) (m := fun a => Fin (d a))
      (X := fun a => IndSp (e' a) (piTensor (ρ a))) e fun a => multiProd (e' a) (ρ a)
    obtain ⟨E1⟩ := E1
    have E2 := ih (fun i => d i.succ) (fun i => t i.succ) (fun i => d' i.succ) (fun i => e' i.succ)
      (fun i => X i.succ) (fun i => ρ i.succ) _ (Equiv.refl _)
    obtain ⟨Er, ⟨E2⟩⟩ := E2
    let mS : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)) → Type :=
      fun c => Fin (d' (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
    let Es : (Σ c, mS c) ≃ n := (Equiv.sumSigmaDistrib fun x => mS (toLex x)).trans
      ((Equiv.sumCongr (e' 0) Er).trans ((headTail _).trans e))
    have E4 := GlobalTheory.T.inductionInStages_twoFactors_equiv (k := k) (m := mS)
      (a := Fin (d 0)) (b := Σ i : Fin s, Fin (d i.succ)) (V := ⨂[ℂ] b, X 0 b) (W := ⨂[ℂ] c : Σₗ i : Fin s, Fin (t i.succ), X (ofLex c).1.succ (ofLex c).2)
      (U := ⨂[ℂ] c : Fin (t 0) ⊕ₗ (Σₗ i : Fin s, Fin (t i.succ)), X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) Es ((headTail _).trans e) (e' 0) Er
      (fun _ _ => rfl) (fun _ _ => rfl) (piTensor (ρ 0))
      (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)
      (piTensor fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)

      (PiTensorProduct.tmulEquivDep ℂ fun c => X (ofLex (splitEquiv t (toLex c))).1 (ofLex (splitEquiv t (toLex c))).2)
      fun g x => piTensor_tmulEquivDep (X := fun c => X (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2)
        (fun c => ρ (ofLex (splitEquiv t c)).1 (ofLex (splitEquiv t c)).2) g x
    obtain ⟨E4⟩ := E4
    have E2' : (multiProd (Equiv.refl _) fun i : Fin s => multiProd (e' i.succ) (ρ i.succ)).Equiv
        (parInd (m := fun j => mS (toLex (Sum.inr j))) Er (piTensor fun c : Σₗ i : Fin s, Fin (t i.succ) => ρ (ofLex c).1.succ (ofLex c).2)) := E2
    have E3 := ind₂_equiv_right ((headTail fun i => Fin (d i)).trans e)
      (parInd (α := Fin (t 0)) (m := fun i => mS (toLex (Sum.inl i))) (e' 0) (piTensor (ρ 0))) E2'
    obtain ⟨E3⟩ := E3
    let Esig : (Σ c : (Σₗ a, Fin (t a)), Fin (d' (ofLex c).1 (ofLex c).2)) ≃ n :=
      (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2))
        (splitEquiv t)).symm.trans Es
    have E5 := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) (splitEquiv t) (GlobalTheory.T.lexSum_splitFirstBlock_strictMono s t) (splitEquiv t).surjective
      Esig Es (fun c' x => congrArg Es ((Equiv.sigmaCongrLeft
        (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) (splitEquiv t)).symm_apply_apply ⟨c', x⟩).symm) fun c => ρ (ofLex c).1 (ofLex c).2
    obtain ⟨E5⟩ := E5
    exact ⟨Esig, ⟨E1.symm.trans (E3.trans (E4.trans E5.symm))⟩⟩

theorem isSubquotient_multiProd_multiProd (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s n : ℕ) (d : Fin s → ℕ) (e : (Σ a, Fin (d a)) ≃ Fin n) (t : Fin s → ℕ)
    (d' : ∀ a, Fin (t a) → ℕ) (e' : ∀ a, (Σ b, Fin (d' a b)) ≃ Fin (d a)) (X : ∀ a, Fin (t a) → Type)
    [∀ a b, AddCommGroup (X a b)] [∀ a b, Module ℂ (X a b)]
    (ρ : ∀ a b, Representation ℂ (GL (Fin (d' a b)) k) (X a b)) (_ : ∀ a b, IsSmooth (ρ a b)) :
    ∃ E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n,
      IsSubquotient (multiProd e fun a => multiProd (e' a) (ρ a))
        (multiProd E fun c => ρ (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2) := by
  have hφ := stages_equiv (k := k) s d t d' e' X ρ (Fin n) e
  obtain ⟨E0, ⟨φ⟩⟩ := hφ
  let F : Fin (∑ a, t a) ≃ Σₗ a, Fin (t a) := finSigmaFinEquiv.symm.trans toLex
  let E : (Σ c : Fin (∑ a, t a), Fin (d' (finSigmaFinEquiv.symm c).1 (finSigmaFinEquiv.symm c).2)) ≃ Fin n :=
    (Equiv.sigmaCongrLeft (β := fun c : Σₗ a, Fin (t a) => Fin (d' (ofLex c).1 (ofLex c).2)) F).trans E0
  have hψ := GlobalTheory.T.parabolicInductionProduct_block_renaming_equiv (k := k) F (GlobalTheory.T.finSigmaFinEquiv_symm_strictMono_toLex s t) F.surjective E0 E
    (fun _ _ => rfl) fun c => ρ (ofLex c).1 (ofLex c).2
  obtain ⟨ψ⟩ := hψ
  exact ⟨E, .of_injective (φ.trans ψ).toIntertwiningMap (φ.trans ψ).toLinearEquiv.injective⟩

end GlobalTheory.SmGL.Stages
