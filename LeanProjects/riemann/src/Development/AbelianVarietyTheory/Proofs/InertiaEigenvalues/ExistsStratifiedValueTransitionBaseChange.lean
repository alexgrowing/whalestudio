import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemilinearProjectiveModuleComposeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrismCoverReceivingBreuilKisinStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InjectiveAndRangeOfPrismCoverStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsInjectivePushoutOfPrismCoverStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.BSP

theorem eval_transition_comp_assoc {l : ℕ} {R : Type} [CommRing R] {P P' P'' P''' : Obj l R}
    (c : Hom P'' P''') (b : Hom P' P'') (a : Hom P P') : c.comp (b.comp a) = (c.comp b).comp a :=
  Hom.ext' rfl

theorem eval_transition : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (d : ℕ) (S : Strat bk d)
    (B B' : Obj l ↥(OL K)) (N : Type) [AddCommGroup N] [Module B.A N] (N' : Type) [AddCommGroup N']
    [Module B'.A N'] (V : Eval S B N) (V' : Eval S B' N') (k : Hom B B'),
    ∃ t : N →ₛₗ[k.f] N', SemiBC t ∧ ∀ (Q : Obj l ↥(OL K)) (a : Hom B' Q) (g : Hom bk.prism Q) (x : N),
      V'.v a g (t x) = V.v (a.comp k) g x := by
  intro l _ K bk d S B B' N _ _ N' _ _ V V' k
  obtain ⟨C', h', ⟨f'⟩, hc⟩ := GlobalTheory.T.exists_prism_cover_receiving_breuilKisin l K bk B'
  obtain ⟨hinj, hsurj⟩ := GlobalTheory.T.injective_and_range_of_prism_cover l K bk d S B' C' N' V' h' f' hc
  have hz : ∀ x : N, ∃ y, V'.v h' f' y = V.v (h'.comp k) f' x := by
    intro x
    apply hsurj
    intro Q p q hpq
    have e : p.comp (h'.comp k) = q.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, hpq, ← eval_transition_comp_assoc]
    have hp : (fun i => p.f (V.v (h'.comp k) f' x i)) = V.v (p.comp (h'.comp k)) (p.comp f') x :=
      funext fun i => (V.v_nat p (h'.comp k) f' x i).symm
    have hq : (fun i => q.f (V.v (h'.comp k) f' x i)) = V.v (q.comp (h'.comp k)) (q.comp f') x :=
      funext fun i => (V.v_nat q (h'.comp k) f' x i).symm
    rw [hp, hq, V.v_ε (p.comp (h'.comp k)) (p.comp f') (q.comp f') x, e]
  choose t0 ht0 using hz
  let t : N →ₛₗ[k.f] N' :=
    { toFun := t0
      map_add' := fun x y => hinj <|
        (ht0 (x + y)).trans ((LinearMap.map_add (V.v (h'.comp k) f') x y).trans
          ((congrArg₂ (· + ·) (ht0 x) (ht0 y)).symm.trans (LinearMap.map_add (V'.v h' f') (t0 x) (t0 y)).symm))
      map_smul' := fun c x => hinj <|
        (ht0 (c • x)).trans ((LinearMap.map_smulₛₗ (V.v (h'.comp k) f') c x).trans
          ((congrArg (h'.f (k.f c) • ·) (ht0 x)).symm.trans (LinearMap.map_smulₛₗ (V'.v h' f') (k.f c) (t0 x)).symm)) }
  have hT : ∀ x, V'.v h' f' (t x) = V.v (h'.comp k) f' x := ht0
  refine ⟨t, ?_, ?_⟩
  · haveI := V.fin; haveI := V.proj; haveI := V'.fin; haveI := V'.proj
    exact GlobalTheory.T.semilinear_projective_module_compose l (↥(OL K)) B' C' h' hc B.A k.f N N' (Fin d → C'.A) t (V'.v h' f')
      (V.v (h'.comp k) f') (fun x => (hT x).symm) (V'.bc h' f') (V.bc (h'.comp k) f')
  · intro Q a g x
    obtain ⟨Q'', h'', a', hsq, hinj''⟩ := GlobalTheory.T.exists_injective_pushout_of_prismCover l K bk d S B' C' h' hc Q a
    have e2 : h''.comp (a.comp k) = a'.comp (h'.comp k) := by
      rw [eval_transition_comp_assoc, ← hsq, ← eval_transition_comp_assoc]
    have key : V'.v (a'.comp h') (a'.comp f') (t x) = V.v (a'.comp (h'.comp k)) (a'.comp f') x :=
      funext fun j => (V'.v_nat a' h' f' (t x) j).trans ((congrArg a'.f (congrFun (hT x) j)).trans (V.v_nat a' (h'.comp k) f' x j).symm)
    funext i
    apply hinj''
    calc h''.f (V'.v a g (t x) i) = V'.v (h''.comp a) (h''.comp g) (t x) i := (V'.v_nat h'' a g (t x) i).symm
      _ = V'.v (a'.comp h') (h''.comp g) (t x) i := congrArg (fun c => V'.v c (h''.comp g) (t x) i) hsq.symm
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V'.v (a'.comp h') (a'.comp f') (t x)) i :=
          congrFun (V'.v_ε (a'.comp h') (h''.comp g) (a'.comp f') (t x)) i
      _ = (S.ε (h''.comp g) (a'.comp f')).mulVec (V.v (a'.comp (h'.comp k)) (a'.comp f') x) i :=
          congrArg (fun w => (S.ε (h''.comp g) (a'.comp f')).mulVec w i) key
      _ = V.v (a'.comp (h'.comp k)) (h''.comp g) x i :=
          (congrFun (V.v_ε (a'.comp (h'.comp k)) (h''.comp g) (a'.comp f') x) i).symm
      _ = V.v (h''.comp (a.comp k)) (h''.comp g) x i := congrArg (fun c => V.v c (h''.comp g) x i) e2.symm
      _ = h''.f (V.v (a.comp k) g x i) := V.v_nat h'' (a.comp k) g x i

end GlobalTheory.BSP
