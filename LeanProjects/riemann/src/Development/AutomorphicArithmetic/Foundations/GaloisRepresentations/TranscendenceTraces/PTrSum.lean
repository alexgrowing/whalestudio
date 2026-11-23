import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trSum_of :
    SumEx → SumNat → PtInj → FibFin → TrSum := by
  intro hEx hNat hInj hFin q _ i Z S p _ w hw hq
  have uniq : ∀ (A : Sq p) (a : Sec (tw q i) A.V) (b b' : Sec (tw q i) A.U),
      IsSum w A a b → IsSum w A a b' → b = b' := by
    intro A a b b' hb hb'
    apply hInj q i A.U b b'
    intro Ω _ _ x
    rw [hb Ω x, hb' Ω x]
  have ex : ∃ t : Fam0 p (tw q i) (tw q i),
      ∀ (A : Sq p) (a : Sec (tw q i) A.V), IsSum w A a (t.app A a) := by
    choose f hf using fun (A : Sq p) (a : Sec (tw q i) A.V) => hEx q i p w hw hq A a
    refine ⟨⟨fun A => { toFun := f A, map_zero' := ?_, map_add' := ?_ }, ?_⟩, ?_⟩
    · refine uniq A 0 _ _ (hf A 0) ?_
      intro Ω _ _ x
      simp [Sec.res]
    · intro a a'
      refine uniq A (a + a') _ _ (hf A (a + a')) ?_
      intro Ω _ _ x
      have hfin : (fib A.r x).Finite := by
        haveI := Sq.finite A
        exact hFin A.r Ω x
      rw [show Sec.res x (f A a + f A a') = Sec.res x (f A a) + Sec.res x (f A a') by simp [Sec.res],
        hf A a Ω x, hf A a' Ω x, ← finsum_mem_add_distrib hfin]
      apply finsum_mem_congr rfl
      intro z _
      simp [Sec.res, smul_add]
    · intro A B t a
      exact uniq A (Sec.res t.k a) _ _ (hNat _ (tw q i) w t a (f B a) (hf B a)) (hf A _)
    · intro A a
      exact hf A a
  exact pick_spec ex
