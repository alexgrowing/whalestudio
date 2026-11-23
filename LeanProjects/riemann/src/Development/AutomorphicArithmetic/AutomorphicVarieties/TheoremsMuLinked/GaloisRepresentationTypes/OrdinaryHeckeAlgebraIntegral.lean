import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.ResidualRepOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.PresCnts
import Development.AutomorphicArithmetic.AutomorphicVarieties.TheoremsMuLinked.CyclicReductionCohomology.DOSmall
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.ArPres
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.UnrLoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.AutomorphicDetection.ArPl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.EigenbasisLifts.PsiInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.LocalRingsCompletion.dvrFinite

open IsLocalRing Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa UpperTheory.V.HV UpperTheory.V.Th GlobalTheory.GalOfCusp

private theorem coef_isCoef (l : ℕ) [hl : Fact l.Prime] (c : Coef l) : IsCoef l c.O := by
  obtain ⟨h1, h2, h3, -⟩ := UpperTheory.V.abelian₂.dvr_finite l c.O
  refine ⟨h1, h2, ?_⟩
  rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff]
  exact h3

private theorem eps_ne {l : ℕ} [Fact l.Prime] {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω]
    (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 L)) (h : IsPlaceOver A w) (hw : ((l : ℕ) : 𝓞 L) ∈ w.asIdeal) :
    ∃ g : Dec (F := L) A, cycZ L Ω l g ≠ 1 := by
  by_contra hn
  have hn' : ∀ g : Dec (F := L) A, cycBar L Ω l g = 1 := fun g => by
    have : cycZ L Ω l g = 1 := by
      by_contra h1
      exact hn ⟨g, h1⟩
    rw [cycBar, MonoidHom.comp_apply, this, map_one]
  have := UpperTheory.V.Ws.Eb.psiInj (l := l) A w h hw (n := 2) (fun _ => 1) ![0, 1] 1 (by decide) one_pos
    (fun i g _ => by rw [hn' g]; simp)
  exact absurd (@this 0 1 rfl) (by decide)

theorem UpperTheory.V.Th.b1O : ordinaryHeckeAlgebraIntegral := by
  intro hP l _ L Ω _ _ _ _ _ _ s V0 c n r T P y al hS _ _ hPL h4 heig hdet
  haveI := coef_isCoef l c
  choose a p h1 h2 h3 using arPres l L Ω s V0 c.O n r T P hS
  have S : Sys T (Module.finrank ℚ (Lp L)) V0.frame.D0 :=
    { a := a
      counts := fun N => presCnts hP l _ _ _ _ (a N) (Lp L) Ω (p N) s.odd (unrLoc l L Ω s V0 c.O n r)
      dv := fun v : Vl l L => locDeg v.1
      dv_eq := fun N => funext (h1 N)
      d0 := h2
      ph := fun N j => (h3 N j).1
      ta := fun N j => (h3 N j).2 }
  have hΦ := (arPl hP l L Ω s V0 c.O n r hS).1
  refine b1absO l _ _ T c.O n y al _ _ S s.odd hΦ (fun v => ?_) hPL h4 heig (detO l _ _ c n y _ s.odd hdet)
  have hw : ((l : ℕ) : 𝓞 L) ∈ (s.w v.1).asIdeal := by
    have h1 := (s.hA v.1 ((l : ℕ) : 𝓞 (Lp L))).2 v.2
    exact (s.hw v.1 _).1 (by simpa using h1)
  obtain ⟨g, hg⟩ := eps_ne (s.A v.1) (s.w v.1) (s.hw v.1) hw
  refine ⟨g, fun e => hg (Units.ext ?_)⟩
  have e1 : V0.ε (toGS Ω V0.S' (resP L Ω g)) = cycZ (Lp L) Ω l (resP L Ω g) := DFunLike.congr_fun V0.hε _
  have e2 : algebraMap ℤ_[l] c.O (V0.ε (toGS Ω V0.S' (resP L Ω g)) : ℤ_[l]) = 1 := e
  rw [e1, ← map_one (algebraMap ℤ_[l] c.O)] at e2
  exact (UpperTheory.V.abelian₂.dvr_finite l c.O).2.2.2.1 e2
