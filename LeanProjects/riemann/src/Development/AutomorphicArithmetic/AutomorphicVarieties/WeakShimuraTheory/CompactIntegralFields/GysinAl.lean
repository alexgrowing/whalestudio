import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.GysinPsOf
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RamifiedLineCharacters.DataPs

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

theorem UpperTheory.V.Ws.gysinAl :
    CohomologyHyp → ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → ∀ (k : Type) [Field k] (a : c.O →+* k), (∀ x ∈ maximalIdeal c.O, a x = 0) → ∀ W : Finset ℕ, (∀ w ∈ W, w.Prime ∧ T.Splits w) → ∀ p p' : PD T.ι (G T.F Ω) k, (T.fr W).IsRes a p → (T.fr W).IsRes a p' → p.In nP → p'.In nP →
      ∃ (W' : Finset ℕ) (s s' : PD T.ι (G T.F Ω) k), W ⊆ W' ∧ (∀ w ∈ W', w.Prime ∧ T.Splits w) ∧ (T.fr W').IsRes a s ∧ (T.fr W').IsRes a s' ∧
        s.In qQ ∧ s'.In qQ ∧ s.SamePs p ∧ s'.SamePs p' ∧ s.SameAl s' ∧ Ent s.r (-wAl) := by
  intro P Ω _ _ _ l _ c D T hT k _ a ha W hW p p' hp hp' hs hs'
  have ok := fun W => (std P D T hT W c le_rfl).2 k a ha
  obtain ⟨r1, -, r3⟩ := Gys.rootCharacters_ne_one_at_basepoint (T.fr W) a (ok W)
  obtain ⟨y, y1, y2, y3, y4⟩ := Gys.dataPs (T.fr W) a p hp hs.1
  obtain ⟨y', y1', y2', y3', y4'⟩ := Gys.dataPs (T.fr W) a p' hp' hs'.1
  obtain ⟨W', s1, s2, hy, x, m, x1, x2, x3, ⟨g, hg⟩, hz⟩ := Gys.cupEx P D T hT k a ha W hW (-wAl) (-wPs) r1 r3 Bool
    (fun b => cond b y y') fun b => by cases b; exacts [⟨y1', y2'⟩, ⟨y1, y2⟩]
  obtain ⟨z, z1, z2⟩ := hz true
  obtain ⟨z', z1', z2'⟩ := hz false
  have hmu := Gys.mu_of (T.fr W) a hp fun v s hs => hs.1
  obtain ⟨s, a1, a2, a3, a4, a5, a6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y z m _ x1 x2 x3 (hy true) y2 y3 z1 z2
  obtain ⟨s', b1, b2, b3, b4, b5, b6⟩ := Gys.ob (T.fr W') a (ok W') hmu x y' z' m _ x1 x2 x3 (hy false) y2' y3' z1' z2'
  exact ⟨W', s, s', s1, s2, a1, b1, a2, b2, ⟨fun g => (a5 g).trans (y4 g).symm, a6⟩, ⟨fun g => (b5 g).trans (y4' g).symm, b6⟩,
    ⟨fun g => (a3 g).trans (b3 g).symm, fun v => (a4 v).trans (b4 v).symm⟩, g, 1, 0, by decide,
    a3 g ▸ mul_ne_zero hg (((T.fr W').χ 0 g).isUnit.map a).ne_zero⟩
