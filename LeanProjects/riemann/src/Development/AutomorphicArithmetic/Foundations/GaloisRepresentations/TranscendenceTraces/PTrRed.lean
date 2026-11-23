import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.IsolateSpec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictScalarsResolutionMapAugmentationSpecStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Gal.TranscendenceTraces

theorem UpperTheory.Gal.TranscendenceTraces.trRed_of :
    GlobalTheory.EtC.A8 → TrChar → TrSum → OpEq → FamSemi → RedZero → RpBasic → RpOp → PtInj → FibFin → TrRed := by
  intro hA8 hChar hSum hOp hFS hRZ hRp hRpOp hPt hFib Q q _ _ hd n i Z S p _ w hw hQ x
  have hq := isUnit_of_dvd_unit (Nat.cast_dvd_cast hd) hQ
  obtain ⟨hovQ, -, -⟩ := hChar Q i p w hw hQ
  obtain ⟨hovq, -, -⟩ := hChar q i p w hw hq
  obtain ⟨f, hfn, hf0⟩ := hRZ Q q hd i
  obtain ⟨σ1, hσ1⟩ := (hFS (ZMod Q) (ZMod Q) (ZMod q)).1 (trFam p w Q i) (redMap Q q i)
  obtain ⟨σ2, hσ2⟩ := (hFS (ZMod Q) (ZMod q) (ZMod q)).2 (redMap Q q i) (trFam p w q i)
  obtain ⟨τ1, hτ1⟩ := (hFS (ZMod Q) (ZMod q) (ZMod Q)).1 σ1
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i))
  obtain ⟨τ2, hτ2⟩ := (hFS (ZMod Q) (ZMod q) (ZMod Q)).1 σ2
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i))
  have key : ∀ (A : Sq p) (a : Sec (tw Q i) A.V),
      ((tr0 p w q i).app A) ((f A.V) a) = (f A.U) (((tr0 p w Q i).app A) a) := by
    intro A a
    haveI := Sq.finite A
    apply hPt q i A.U
    intro Ω _ _ y
    have hfin := hFib A.r Ω y
    rw [hSum q i p w hw hq A ((f A.V) a) Ω y, hfn, hSum Q i p w hw hQ A a Ω y,
      (f (gp Ω)).map_finsum_mem _ hfin]
    refine finsum_mem_congr rfl fun z _ => ?_
    rw [map_zsmul, hfn]
  let t : Fam0 p (tw Q i) ((restr (ZMod.castHom hd (ZMod q))).obj (tw q i)) :=
    { app := fun A => (f A.U).comp ((tr0 p w Q i).app A)
      nat := fun {A B} k a => (hfn _ _ k.g _).trans (congrArg (f A.U) ((tr0 p w Q i).nat k a)) }
  have hov1 : τ1.Over t := by
    intro A a
    rw [hτ1, hσ1, hovQ A a, hf0, GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec]
    rfl
  have hov2 : τ2.Over t := by
    intro A a
    rw [hτ2, hσ2, hf0, hovq A, GlobalTheory.T.restrictScalarsResolutionMap_augmentation_spec, key]
    rfl
  obtain ⟨a, ha⟩ := (hRp (ZMod Q) (res (ZMod Q) (tw Q i)) Z n).1 x
  have r1 := (hRp (ZMod Q) (res (ZMod Q) (tw Q i)) S n).2.2.2.2 (ZMod q) (res (ZMod q) (tw q i))
    (redMap Q q i) _ _ (hRpOp (ZMod Q) (ZMod Q) (trFam p w Q i) n x a ha)
  have r2 := hRpOp (ZMod q) (ZMod q) (trFam p w q i) n _ _
    ((hRp (ZMod Q) (res (ZMod Q) (tw Q i)) Z n).2.2.2.2 (ZMod q) (res (ZMod q) (tw q i))
      (redMap Q q i) x a ha)
  have s1 := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.2.2 (ZMod Q) _
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i)) _ _ r1
  have s2 := (hRp (ZMod q) (res (ZMod q) (tw q i)) S n).2.2.2.2 (ZMod Q) _
    (restrMap (ZMod.castHom hd (ZMod q)) (tw q i)) _ _ r2
  have u1 := hRpOp (ZMod Q) (ZMod Q) τ1 n x a ha
  have u2 := hRpOp (ZMod Q) (ZMod Q) τ2 n x a ha
  have e1 := ((hRp (ZMod Q) _ S n).2.2.1 _ _ _ _ s1 u1).2.1
    ((hτ1 n (Sq.self p) a).trans (congrArg _ (hσ1 n (Sq.self p) a))).symm
  have e2 := ((hRp (ZMod Q) _ S n).2.2.1 _ _ _ _ s2 u2).2.1
    ((hτ2 n (Sq.self p) a).trans (congrArg _ (hσ2 n (Sq.self p) a))).symm
  apply (hA8 (ZMod Q) (ZMod q) (ZMod.castHom hd (ZMod q)) (sch.obj S) (tw q i) n).1
  exact e1.trans ((DFunLike.congr_fun (hOp Q p (tw Q i) _ t τ1 τ2 hov1 hov2 n) x).trans e2.symm)
