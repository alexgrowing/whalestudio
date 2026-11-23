import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TrueColumnSpacesStandardInFrameCoords
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsForgetsFrames
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MoveDownLevelPrimeKeepsChart
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Col2

section SameUp

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))}

theorem SameG.up' {y : Ys X n} (p : PtY ST SG Q y) (P : ST) (hP : MoveHyp ST SG P) (q : 𝓞 X.E) {x : Sp X.E n}
    (hx : x ∈ p.1.1.deco.1.N) : SameG p (p.mv (p.1.1.deco.up P q x)) := by
  classical
  have hs : DecoSet.SameOn SG p.1.1.deco (p.1.1.deco.up P q x) :=
    DecoSet.sameOn_up _ P hP.ne (fun w hw => hP.sg ⟨w, hw⟩) q hx
  have hb : (p.1.1.deco.up P q x).1.be = p.1.1.deco.1.be := by
    unfold DecoSet.up
    split_ifs with h
    · rfl
    · rfl
  by_cases h : (∀ (w : Q) (z : Sp X.E n), p.1.1.1.2 w z ∈ (p.1.1.deco.up P q x).1.at w.1 ↔ z ∈ stdAt X.E n w.1) ∧ p.1.2 ∈ y.ys (p.1.1.deco.up P q x).1.N
  · have e : p.mv (p.1.1.deco.up P q x) = ⟨(⟨(p.1.1.deco.up P q x, p.1.1.1.2), h.1⟩, p.1.2), h.2⟩ := dif_pos h
    rw [e]
    exact ⟨rfl, rfl, fun w => hs w.1 w.2, hb⟩
  · have e : p.mv (p.1.1.deco.up P q x) = p := dif_neg h
    rw [e]
    exact SameG.refl p

end SameUp

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

theorem TC.cosetIn_rep_up (hX : B.fields.Ok) (hPr : (B.primes X).Ok) (u : B.Word) (a : I.ι) (i : ℕ) (v : (B.primes X).vT u)
    (c : (I.stp u a i).Cl) (x : ((I.atIn u a).A i).lv v c) :
    cosetIn ((I.stp u a i).rep ((I.stp u a i).cl c.1 (((I.atIn u a).A i).upPt v c x))) =
      cosetIn ((I.stp u a i).rep c) := by
  by_cases hj : i + 1 = B.R.m
  · refine GStep.prefRep_eq_of_normal (I.stp0 u a i) c.1 (fun q' : (I.stp0 u a i).D c.1 => cosetIn q') (I.pref u a i c.1)
      (GStep.prefRep_normal (I.stp0 u a i) c.1 _ _ (fun p hp => hp.2.1 hj) (I.pref_of_normalFor u a i hj c.1)) c.2 _ fun h => ?_
    exact cosetIn_eq_of_sameG hX hPr (SameG.smul h (SameG.up' ((I.stp u a i).rep c) v (moveHyp_of_ok hPr u v) _
      (Quotient.out x).2))
  · have h0 : ∀ q : PtAt B.R I.sel (I.tup a) (I.cst a) u i, cosetIn q = fun _ => ∅ := by
      intro q
      funext P
      have hq : q.1.2 = ∅ := by
        have := q.2
        rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) hj] at this
        exact this
      ext z
      simp [cosetIn, hq]
    rw [h0, h0]

end GlobalTheory.Mem.Col2

namespace GlobalTheory.Mem.Col2

theorem TC.up_keeps_chart : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι) (i : ℕ) (hi : i ≤ B.R.m), ∀ {bad : Set (HeightOneSpectrum (𝓞 B.host.F))} {Ch : Type} (chOf : (I.stp u a i).Cl → Ch) (K : ∀ β : Ch, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))), I.ReadsK l Z u a i hi chOf K → ∀ (v : (I.atT l u a).vT) (c : (I.chain l u a).cls i) (x : (I.fm l u a).lv i v c), (I.fm l u a).fv i v c x = 1 → chOf ((I.fm l u a).up i v c x) = chOf c := by
  intro B X I _ _ l Z u a i hi bad Ch chOf K hR v c x _
  obtain ⟨k, hk⟩ := hR
  have hX : B.fields.Ok := (base_fields_primes_ok B X).1
  exact (hk.key ((I.fm l u a).up i v c x) c).2 ⟨rfl, I.cosetIn_rep_up hX l.pr u a i v c x⟩

end GlobalTheory.Mem.Col2
