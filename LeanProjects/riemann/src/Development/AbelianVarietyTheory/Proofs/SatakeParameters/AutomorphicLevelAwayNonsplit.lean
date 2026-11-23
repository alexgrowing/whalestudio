import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CuspFormLimitTwoPlaces
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.LatticeDataThicknessBound
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ApartAllEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FrobOpsIdx
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsNormMemOfUnderEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsUniqueSplitPlaceComponentDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyLocalIntegralPointsMemOpenSubgroupDefi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsSatUOfUnderEq
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL GlobalTheory.CongL

namespace GlobalTheory.CongL.UnitLim

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem finite_not_sph (a : ℕ) (U : Submodule ℂ (UA E a → ℂ)) (hU : IsAutRepU U) :
    {w : HeightOneSpectrum (𝓞 E) | IsSplitAt w ∧ ¬ ∃ B, SatU U w B}.Finite := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.ne_bot
  let L : Subgroup (finU E a) :=
    { carrier := {k | RU E a k φ = φ}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        simp only [Set.mem_setOf_eq] at *
        rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hy, hx]
      inv_mem' := by
        intro x hx
        simp only [Set.mem_setOf_eq] at *
        conv_lhs => rw [← hx]
        rw [← Module.End.mul_apply, ← map_mul, Subgroup.coe_inv, inv_mul_cancel, map_one, Module.End.one_apply] }
  have hLo : IsOpen (L : Set (finU E a)) := (hU.aut φ hφ).level
  have hev : ∀ᶠ w in Filter.cofinite, IsSplitAt w → ∃ B, SatU U w B := by
    filter_upwards [GlobalTheory.BCT.GlobLev.eventually_locU_mem E a L hLo] with w hw hs
    obtain ⟨σ, B, hc, hB, -⟩ := GlobalTheory.FrameAut.exists_locComp_hasSatGL_heckeVec E a U hU w hs φ hφ hφ0
      fun x hx hxK => hw x hx hxK hx.1
    exact ⟨B, σ, hc, hB⟩
  exact (Filter.eventually_cofinite.1 hev).subset fun w hw h => hw.2 (h hw.1)

theorem dense_frob_usable_off (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] (l : ℕ) (hl : l.Prime) (d : ℕ) (hd : ImQ E d) (X : Finset (HeightOneSpectrum (𝓞 E))) :
    Dense {g : G E Ω | ∃ w : HeightOneSpectrum (𝓞 E), w ∉ X ∧ UsPl d w ∧ ((l : ℕ) : 𝓞 E) ∉ w.asIdeal ∧ ApartAll X w ∧
      ∃ A : ValuationSubring Ω, IsPlaceOver A w ∧ IsFrob A (normV w) g} := by
  classical
  set M : ℕ := l * (2 * d) * ∏ u ∈ X, Ideal.absNorm u.asIdeal with hM
  have hM0 : M ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero hl.ne_zero (mul_ne_zero two_ne_zero hd.1.ne')) ?_
    rw [Finset.prod_ne_zero_iff]
    intro u _
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact u.ne_bot
  have hS1 : {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}}.Finite := by
    refine Ideal.finite_factors ?_
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hM0
  have hS3 := (GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).2
  set S := {w : HeightOneSpectrum (𝓞 E) | w.asIdeal ∣ Ideal.span {((M : ℕ) : 𝓞 E)}} ∪
    {P : HeightOneSpectrum (𝓞 E) | P.asIdeal.ramificationIdx ℤ ≠ 1} with hSdef
  have hS : S.Finite := hS1.union hS3
  have hdense := GlobalTheory.Published.chebotarevDegreeOne'.dense (F := E) (Ω := Ω) hS
  refine hdense.mono ?_
  rintro g ⟨w, hwS, hdeg, A, hA, hg⟩
  simp only [hSdef, Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hwS
  obtain ⟨hM', hram⟩ := hwS
  have hMw : ((M : ℕ) : 𝓞 E) ∉ w.asIdeal := fun h => hM' (Ideal.dvd_span_singleton.2 h)
  have hp := ((GlobalTheory.absNorm_prime_iff_inertiaDeg_eq_one_and_finite_ramified E).1 w).2 hdeg
  have hX : ∀ u ∈ X, ((Ideal.absNorm u.asIdeal : ℕ) : 𝓞 E) ∉ w.asIdeal := fun u hu h =>
    hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ hu) _) h)
  refine ⟨w, fun hwX => hX w hwX (Ideal.absNorm_mem _), ?_, ?_, ?_, A, hA, hg⟩
  · refine GlobalTheory.DenseUsable.usPl_of_absNorm_prime hd w hp hram fun h => hMw ?_
    exact GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_left _ _) _) h
  · exact fun h => hMw (GlobalTheory.DenseUsable.natCast_mem_of_dvd w (Dvd.dvd.mul_right (dvd_mul_right _ _) _) h)
  · intro u hu hwu
    exact hX u hu (GlobalTheory.DenseUsable.absNorm_mem_of_under_eq w u hwu)

end GlobalTheory.CongL.UnitLim
