import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistableStatement
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

theorem UpperTheory.Gal.TP.Sub.clTw_holds :
    FrobSub → TwLoc → TwJumps → PstOfDR → WDFacts → ContLeft → ClTw := by
  intro hF hL hJ hP hW hC E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m h1 h2
  refine ⟨fun hw => (hF E Ω l ι a w S c μ (h1.1 hw)).2 s (h2.1 hw), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨c1, d1, j1, p1⟩ := h1.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := h2.2 P AI hT A h O Bw hj
  have e1 : (rk1 μ).comp (Dec (F := E) A).subtype = rk1 (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    rfl
  have e2 : (tw s μ).comp (Dec (F := E) A).subtype =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    ext g i j
    simp [UpperTheory.V.Af.tw_val]
  have e3 : Formalism.MainNotions.SumRepresentations.At.twGL (s.comp (Dec (F := E) A).subtype)
      (Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))) =
      tw (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype) := by
    have hdet : Matrix.GeneralLinearGroup.det.comp (rk1 (μ.comp (Dec (F := E) A).subtype))
        = μ.comp (Dec (F := E) A).subtype := by
      ext g
      simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
    rw [hdet]
    ext g i j
    simp [Formalism.MainNotions.SumRepresentations.At.twGL, UpperTheory.V.Af.tw_val, Algebra.algebraMap_eq_smul_one, Matrix.smul_apply]
  rw [e1] at c1 d1 j1 p1
  rw [e2]
  have cs : Continuous (s.comp (Dec (F := E) A).subtype) := hs.comp continuous_subtype_val
  have cμ : Continuous (μ.comp (Dec (F := E) A).subtype) := hμ.comp continuous_subtype_val
  have ck := (hC _ (Qbar l) 1 1).2.2.2 _ cμ
  have ct := (hC _ (Qbar l) a 1).2.2.1 _ _ cs cμ
  obtain ⟨l1, l2⟩ := hL l P AI hT E Ω A O Bw a (s.comp (Dec (F := E) A).subtype) (μ.comp (Dec (F := E) A).subtype)
  have dt := l1 d2 d1
  refine ⟨l2 c2 c1, dt, ?_, ?_⟩
  · intro τ LL' τ' hi
    exact hJ l P AI hT E Ω A O Bw a _ _ cs cμ τ (J τ) (m τ) (j2 τ LL' τ' hi) (j1 τ LL' τ' hi)
  · intro g
    have q1 := hP l P AI hT E Ω A O Bw a _ cs d2
    have q2 := hP l P AI hT E Ω A O Bw 1 _ ck d1
    have q3 := hP l P AI hT E Ω A O Bw a _ ct dt
    have hcs : Continuous fun g : ↥(Dec (F := E) A) =>
        ((s.comp (Dec (F := E) A).subtype g : GL (Fin a) (Loc.Om l)) : Matrix (Fin a) (Fin a) (Loc.Om l)) :=
      Units.continuous_val.comp cs
    have hck : Continuous fun g : ↥(Dec (F := E) A) =>
        ((rk1 (μ.comp (Dec (F := E) A).subtype) g : GL (Fin 1) (Loc.Om l)) : Matrix (Fin 1) (Fin 1) (Loc.Om l)) :=
      Units.continuous_val.comp ck
    rw [← e3] at q3
    have key := GlobalTheory.T.fontaineParameter_twist_potentiallySemistable l P AI hT ι E Ω A w h O Bw hj a _ _ hcs hck q1 q2 q3
    rw [e3] at key
    rw [key]
    exact (hW E Ω A w h _ _).2.2.2 g S c (p2 g) (p1 g)
