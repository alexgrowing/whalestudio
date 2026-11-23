import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem univ_map_snoc {α : Type*} {t : ℕ} (f : Fin (t + 1) → α) :
    Finset.univ.val.map f =
      Finset.univ.val.map (fun i : Fin t => f i.castSucc) + {f (Fin.last t)} := by
  rw [Fin.univ_castSuccEmb]
  simp [Finset.map_val, Multiset.map_map, add_comm, Function.comp_def]

theorem UpperTheory.Gal.TP.Sub.peelAll_holds :
    PeelOne → ContLeft → ClConj → ClSub → PeelAll := by
  intro hP hC hJ hS E Ω _ _ _ _ _ l _ ι n m' t' r' a' hr' t
  induction t with
  | zero =>
    intro r a hc hss _ _ _
    refine ⟨r, hc, hss, ?_⟩
    intro w S c J m _ h
    simpa using h
  | succ t ih =>
    intro r a hc hss ha hne hid
    obtain ⟨s₁, hs₁, hiso, hid₁⟩ :=
      hP (G E Ω) (Qbar l) (n + t) m' t t' r r' a a' hss hr' hne hid
    have hC' := hC (G E Ω) (Qbar l) (n + t) 1
    have hC1 := hC (G E Ω) (Qbar l) (n + t + 1) 1
    have hcl : Continuous (sumRep s₁ (rk1 (a (Fin.last t)))) := hC1.2.1 _ _ hiso hc
    have hcs₁ : Continuous s₁ := hC'.1 _ _ hcl
    obtain ⟨s, hsc, hss', hcl'⟩ := ih s₁ (fun i => a i.castSucc) hcs₁ hs₁
      (fun i => ha _) (fun i j => hne _ _) hid₁
    refine ⟨s, hsc, hss', ?_⟩
    intro w S c J m hcl0 h
    have h2 := hJ E Ω l ι _ r _ hc hiso w _ _ h
    refine hcl' w S (fun i => c i.castSucc) J (fun i => m i.castSucc) (fun i => hcl0 _) ?_
    refine hS E Ω l ι _ s₁ (a (Fin.last t)) hcs₁ (ha _) w _ (c (Fin.last t)) _
      (m (Fin.last t)) (hcl0 _) ?_
    have e1 : S + Finset.univ.val.map c =
        S + Finset.univ.val.map (fun i : Fin t => c i.castSucc) + {c (Fin.last t)} := by
      rw [univ_map_snoc c, add_assoc]
    have e2 : (fun τ => J τ + Finset.univ.val.map fun i => m i τ) =
        fun τ => J τ + Finset.univ.val.map (fun i : Fin t => m i.castSucc τ) +
          {m (Fin.last t) τ} := by
      funext τ
      rw [univ_map_snoc (fun i => m i τ), add_assoc]
    rw [e1, e2] at h2
    exact h2
