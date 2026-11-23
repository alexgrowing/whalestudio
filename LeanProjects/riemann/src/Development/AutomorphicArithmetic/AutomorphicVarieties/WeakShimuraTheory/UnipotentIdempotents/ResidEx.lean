import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.TCont
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.Descend
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.PrFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.StarOp
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.CbFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.UnipotentIdempotents.WtRoot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp UpperTheory.V.Ws.Lk

theorem UpperTheory.V.Ws.Lk.residEx :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c} {T : Tower D} {c' : Coef l} {h : c.O ≤ c'.O} (X : OCh T c' h) (Y : SetD T) (V : Y.s.Lev), D.Good → T.Ok → V.S' = Y.s.S → ∃ r : W.Resid V.frame c'.O 4, (∀ i (g : G T.L Ω), r.chib i (V.pr g) = X.cb i g) ∧ (∀ (v : W.Vl l T.L) i (g : Dec (F := T.L) (Y.s.A v)), r.psib v i g = r.chib i (V.pr g)) ∧ (∀ v i, r.th v i = 1) := by
  intro Ω _ _ _ l _ c D T c' h X Y V hG hT hS
  have hcb := cbFacts X hG
  have hpr := prFacts l T.L Ω Y.s V
  have hd : ∀ i, ∃ χ : V.η.ker →* (ResidueField c'.O)ˣ, IsOpen (χ.ker : Set V.η.ker) ∧
      ∀ g, χ (V.pr g) = X.cb i g := fun i =>
    descend l T.L Ω Y.s V _ (X.cb i) (hcb.1 i)
      (fun A v hA hv => hcb.2.1 i A (Y.away A v hA (by rwa [hS] at hv)))
  choose χ hχo hχ using hd
  have hinj : Function.Injective χ := by
    intro i j hij
    apply cbInj X hT
    exact MonoidHom.ext fun g => by rw [← hχ, ← hχ, hij]
  have hpol : V.frame.IsPolar c'.O (W.GDet.ofRep (W.diagRep χ)) := by
    apply polar V.frame c'.O (ResidueField c'.O) 4 χ Fin.revPerm
    intro i g
    obtain ⟨g1, rfl⟩ := hpr.1 g
    obtain ⟨g', hg', hconj⟩ := hpr.2.1 g1
    obtain ⟨σ, hσ, hσc⟩ := Y.cc
    have key := hcb.2.2 σ hσ g1 g' (hσc g1 g' hg') i
    have heps := hpr.2.2.1 c'.O (ResidueField c'.O) g1
    rw [hconj]
    apply Units.ext
    simp only [Units.val_mul, Units.val_one, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val,
      Fin.revPerm_apply]
    erw [hχ i g', hχ i.rev g1, heps, IsLocalRing.ResidueField.algebraMap_eq]
    have e3 : ((4 : ℕ) : ℤ) - 1 = ((3 : ℕ) : ℤ) := by norm_num
    rw [e3, zpow_natCast]
    exact key
  refine ⟨W.Resid.mk χ hχo hinj hpol (fun v i => (χ i).comp (V.frame.φ v)) ?_ (fun _ _ => 1)
    (fun _ _ _ _ => rfl), fun i g => hχ i g, fun v i g => rfl, fun v i => rfl⟩
  intro v i
  exact (hχo i).preimage (V.frame.φ_cont v)
