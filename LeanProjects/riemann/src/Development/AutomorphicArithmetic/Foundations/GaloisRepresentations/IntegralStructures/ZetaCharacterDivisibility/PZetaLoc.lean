import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.CharOfZeta

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.Int.Div

private theorem map_scalar' {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (a : ℕ) (y : Rˣ) :
    Matrix.GeneralLinearGroup.map f (Matrix.GeneralLinearGroup.scalar (Fin a) y) =
      Matrix.GeneralLinearGroup.scalar (Fin a) (Units.map f.toMonoidHom y) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [Matrix.GeneralLinearGroup.scalar]
  · simp [Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, h]

section

open GlobalTheory.SplitPts

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

private theorem pInf_quo (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map (pInf E).toMonoidHom (quo E (localIdele E w u)) = 1 := by
  have h1 : pInf E ((localIdele E w u : Ideles E) : Ad E) = 1 := by
    change (infEq E).symm (1 : InfiniteAdeleRing E) = 1
    exact map_one _
  have h2 : Units.map (pInf E).toMonoidHom (localIdele E w u) = 1 := Units.ext h1
  have h3 : Units.map (pInf E).toMonoidHom (cj E (localIdele E w u)) = 1 := by
    refine Units.ext ?_
    change pInf E (conjAd E ((localIdele E w u : Ideles E) : Ad E)) = 1
    rw [GlobalTheory.CompanionTheory.OnlyStab.pInf_conj, h1, map_one]
  rw [quo_apply, _root_.map_div, h2, h3, div_one]

private theorem loc_quo (w v : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u)) =
      Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) /
        Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) := by
  rw [quo_apply, _root_.map_div]

private theorem loc_id_ne {w v : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (localIdele E w u) = 1 :=
  Units.ext ((Neutral.B1.localIdele_isSupportedAt E w u).2 v h)

private theorem loc_cj_ne {w v : HeightOneSpectrum (𝓞 E)} (h : conjSrc (conjE E) v ≠ w)
    (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (cj E (localIdele E w u)) = 1 := by
  refine Units.ext ?_
  change conjLoc (conjE E) v (((localIdele E w u : Ideles E) : Ad E).2 (conjSrc (conjE E) v)) = 1
  rw [(Neutral.B1.localIdele_isSupportedAt E w u).2 _ h, map_one]

private theorem loc_id_self (w : HeightOneSpectrum (𝓞 E)) (u : (w.adicCompletion E)ˣ) :
    Units.map ((pLoc E w).comp (pFin E)).toMonoidHom (localIdele E w u) = u :=
  Units.ext (Neutral.B1.localIdele_snd_self E w u)

end

open GlobalTheory.SplitPts in
theorem UpperTheory.Gal.Int.Div.zetaLoc_of :
    ZetaLoc := by
  intro E _ _ _ a ζ hζ w hw u
  obtain ⟨hne, hund, -⟩ := over_split hw
  have hc : ∀ v, cLoc v (ζ (localIdele E w u)) = Matrix.GeneralLinearGroup.scalar (Fin a)
      (Units.map ((pLoc E v).comp (pFin E)).toMonoidHom (quo E (localIdele E w u))) := by
    intro v
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar']
  have hi : cInf (ζ (localIdele E w u)) = 1 := by
    change Matrix.GeneralLinearGroup.map _ ((ζ (localIdele E w u) : UA E a) : GA E a) = _
    rw [hζ, map_scalar', pInf_quo, map_one]
  refine ⟨Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 hi, Subgroup.mem_iInf.2 fun v =>
    Subgroup.mem_iInf.2 fun hv => MonoidHom.mem_ker.2 ?_⟩, ?_⟩
  · have h1 : v ≠ w := fun e => hv (by rw [e])
    have h2 : conjSrc (conjE E) v ≠ w := fun e => hv (by
      rw [← hund, ← e, conjSrc_conjSrc_cm])
    rw [hc, loc_quo, loc_id_ne h1, loc_cj_ne h2, div_one, map_one]
  · rw [hc, loc_quo, loc_id_self, loc_cj_ne hne, div_one]
