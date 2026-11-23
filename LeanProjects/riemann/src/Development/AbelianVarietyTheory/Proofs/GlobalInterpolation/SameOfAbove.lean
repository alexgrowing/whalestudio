import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.KerIsTerm
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelChainSharpColumnValuationOfPointKernelLiftL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeNotMemOfMemQE
import Formalism.LocalToGlobal.Columns.AtTOwedV

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2 GlobalTheory.LvT GlobalTheory.LvT.Built

noncomputable section

namespace GlobalTheory.LvT.Built.UpLaw

section Gen

variable {X : Fields} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 X.E))} {y : Ys X n} {β : Type} [Fintype β] [DecidableEq β]
  {Λ : β → LevFam X.E X.K n SG} {Θ : β → LevQFam X.E X.K n Q} {pref : DecoF X.E n ST SG Q → Prop} {T : ℕ} {P : ST}
  (hP : MoveHyp ST SG P) (hT : (T : 𝓞 X.E) ∈ P.1.asIdeal ∧ (T : 𝓞 X.E) ∉ P.1.asIdeal ^ 2)
  (hQ : ∀ w : Q, w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1) (hy : y.Off P.1)

include hP hT hQ hy

theorem above_iff (b : β) (p q : PtY ST SG Q y) : Above (tdatY ST T y β Λ Θ pref) b P p q ↔
    p.1.1.deco.1.IsUp P (T : 𝓞 X.E) q.1.1.deco.1 ∧ q.1.1.1.2 = p.1.1.1.2 ∧ q.1.2 = p.1.2 := by
  constructor
  · rintro ⟨x, hx, hf, rfl⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨⟨x, hx, hf, h.1⟩, h.2⟩
  · rintro ⟨⟨x, hx, hf, e⟩, h2, h3⟩
    have h := mv_up T p P hP hT hQ hy hx hf
    exact ⟨x, hx, hf, PtY.ext' (Subtype.ext (e.trans h.1.symm)) (h2.trans h.2.1.symm) (h3.trans h.2.2.symm)⟩

theorem bijOn_up (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P p q} {d | p.1.1.deco.1.IsUp P (T : 𝓞 X.E) d.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b p q).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b p q).1 hq).2
    have h' := ((above_iff hP hT hQ hy b p q').1 hq').2
    exact PtY.ext' e (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)
  · obtain ⟨x, hx, hf, e⟩ := hd
    exact ⟨_, ⟨x, hx, hf, rfl⟩, Subtype.ext ((mv_up T p P hP hT hQ hy hx hf).1.trans e.symm)⟩

theorem bijOn_dn (b : β) (p : PtY ST SG Q y) : Set.BijOn (fun q : PtY ST SG Q y => q.1.1.deco)
    {q | Above (tdatY ST T y β Λ Θ pref) b P q p} {d | d.1.IsUp P (T : 𝓞 X.E) p.1.1.deco.1} := by
  refine ⟨fun q hq => ((above_iff hP hT hQ hy b q p).1 hq).1, fun q hq q' hq' e => ?_, fun d hd => ?_⟩
  · have h := ((above_iff hP hT hQ hy b q p).1 hq).2
    have h' := ((above_iff hP hT hQ hy b q' p).1 hq').2
    exact PtY.ext' e (h.1.symm.trans h'.1) (h.2.symm.trans h'.2)
  · have hs := fun w h1 h2 => (Deco.IsUp.sameAt d.2 hP hd (Q := w) h1 h2).localization_eq.symm
    have h := p.mv_spec d (fun w => hs w.1 (hQ w).1 (hQ w).2) (hy _ _ hs)
    refine ⟨p.mv d, (above_iff hP hT hQ hy b _ p).2 ⟨?_, h.2.1.symm, h.2.2.symm⟩, h.1⟩
    rw [h.1]
    exact hd

theorem same_of_above (b : β) {p q : PtY ST SG Q y} (h : Above (tdatY ST T y β Λ Θ pref) b P p q) :
    SameOff ST p.1.1.deco.1.N q.1.1.deco.1.N ∧ p.1.1.deco.1.be = q.1.1.deco.1.be ∧ p.1.1.fr = q.1.1.fr ∧ p.1.2 = q.1.2 := by
  obtain ⟨h1, h2, h3⟩ := (above_iff hP hT hQ hy b p q).1 h
  exact ⟨fun w hw => (h1.sameAt p.1.1.deco.2 hP (hw P.1 P.2).1 (hw P.1 P.2).2).localization_eq.symm, h1.be_eq.symm,
    funext fun w => (congrFun h2 w).symm, h3.symm⟩

end Gen

theorem kAt_uk : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ) (u : Pr.Word) (i : ℕ), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → L.Ok Ch sel mu cst G m2 → ∀ (Tp : TopLev X Pr R (QE sel (mu : Chr X.F X.E X.K))) (A : Formalism.L2.Ker.Amb X), KerIsTerm W Ch sel mu cst L A u i → GlobalTheory.KerT.UKTerm W Ch sel mu cst A u i (i + 1) → ∀ b b' (d : (stepAt sel mu cst L Tp u i).D b) (d' : (stepAt sel mu cst L Tp u (i + 1)).D b') (P : Pr.vT u) F, (∑ᶠ d₁ ∈ {d₁ | Above (tdatAt sel mu cst L Tp u (i + 1)) b' P d' d₁}, kAt W Ch sel mu cst L A u i b b' d d₁ F) = ((Pr.T u : X.K) ^ ((R.t + 1) / 2)) • ∑ᶠ d₀ ∈ {d₀ | Above (tdatAt sel mu cst L Tp u i) b P d₀ d}, kAt W Ch sel mu cst L A u i b b' d₀ d' F := by
  intro X Pr R W Ch sel S mu cst L G m2 u i hX hPr hsel hS _ Tp A hK hU b b' d d' P F
  obtain ⟨Ξ₀, hb, -, -, -, hk⟩ := hK b b' d d'
  have hP := moveHyp_of_ok hPr u P
  have hT := T_unif hX hPr u P
  have hQ0 := T_notMem_QE sel mu u hPr hsel hS
  have hQ : ∀ w : QE sel (mu : Chr X.F X.E X.K), w.1 ≠ P.1 ∧ w.1 ≠ conjPrime₂ P.1 :=
    fun w => ne_of_T_notMem hPr u P (hQ0 w.1 w.2)
  have hy := fun j => ysAt_off (R := R) sel mu cst hPr u hQ0 j P
  have refl : ∀ {j : ℕ} (p : PtAt R sel mu cst u j), SameOffPt sel mu cst u p p :=
    fun p => ⟨fun _ _ => rfl, rfl, rfl, rfl⟩
  have key := hU d.1.1.deco (frsF sel mu d.1.1) d'.1.1.deco (frsF sel mu d'.1.1) Ξ₀ P F hP hP hb
  refine (finsum_mem_eq_of_bijOn _ (bijOn_up hP hT hQ (hy (i + 1)) b' d') fun q hq => ?_).trans
    (key.trans (congrArg _ (finsum_mem_eq_of_bijOn _ (bijOn_dn hP hT hQ (hy i) b d) fun q hq => ?_).symm))
  · rw [hk d q (refl d) (same_of_above hP hT hQ (hy (i + 1)) b' hq)]
  · obtain ⟨h1, h2, h3, h4⟩ := same_of_above hP hT hQ (hy i) b hq
    rw [hk q d' ⟨fun w hw => (h1 w hw).symm, h2.symm, h3.symm, h4.symm⟩ (refl d')]

end GlobalTheory.LvT.Built.UpLaw
