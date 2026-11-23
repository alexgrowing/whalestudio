import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.v0ok :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → ∀ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) → r.V0ok := by
  intro Ω _ _ _ l _ c D T c' h X Y V hD r hr
  haveI : IsLocalHom (inc h) := (UpperTheory.V.Ws.P1.coefRes c).2.2.1 c' h
  have hres : ∀ x : c.O, residue c'.O (inc h x) = ResidueField.map (inc h) (residue c.O x) := fun x =>
    (ResidueField.map_residue _ x).symm
  refine ⟨?_, ?_, ?_⟩
  · rintro i _ ⟨g, hg, rfl⟩
    exact MonoidHom.mem_ker.2 ((hr i g).trans (MonoidHom.mem_ker.1 ((cbFacts X hD).2.1 i _ Y.away0 hg)))
  · rintro _ ⟨g, hg, rfl⟩ i j
    refine (hr i g).trans (Eq.trans (Units.ext ?_) (hr j g).symm)
    rw [X.cb_val, X.cb_val, map_mul, map_mul, hres, hres]
    exact congrArg (fun x => residue c'.O (X.κ g) * ResidueField.map (inc h) x) (Y.eq0 g hg i j)
  · obtain ⟨g, hg, hne⟩ := Y.om0
    refine ⟨V.pr g, ⟨g, hg, rfl⟩, fun h' => hne ?_⟩
    have h1 := (prFacts l T.L Ω Y.s V).2.2.1 c'.O (ResidueField c'.O) g
    rw [h', Units.val_one] at h1
    have h2 : (chiO T.L Ω l c'.O g : c'.O) = inc h (chiO ℚ Ω l c.O (resQ T.L g)) := rfl
    rw [hD.om_bar]
    apply (ResidueField.map (inc h)).injective
    rw [map_one, Raw.bar, ← hres, ← h2]
    exact h1.symm
