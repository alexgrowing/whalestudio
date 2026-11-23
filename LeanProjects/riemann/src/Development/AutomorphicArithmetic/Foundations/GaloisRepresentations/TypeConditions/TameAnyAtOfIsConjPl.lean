import Development.DiscreteGroups.GlobalIrreducibility.DzBigDef
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.CardRootsBar
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleResidualTameEigenvalues
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InertiaCharpolyEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameAnyAtPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameOfFrobeniusDense
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImportsBisSide

noncomputable section

namespace GlobalTheory.IneAway
open GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem ineAt' : ∀ D : D7, UpperTheory.GalS.GalAwayN D → FrobDense D → ∀ (i : D.nd.Loc) (π : D.naut.CG D.R.r) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)), D.naut.csd π → D.naut.ralg π → UpperTheory.GalS.FullLabS D [⟨D.R.r, π, 1⟩] → IsRepOfSig D.nd D.naut i [⟨D.R.r, π, 1⟩] ρ → ∀ (k : Fin 2) (v : D.nd.PlG k) (w), w = D.naut.plGw k v → w ∉ placesOver D.host.E (D.nd.l i) → ∀ s ∈ Ine (F := D.host.E) (D.nd.plOm.1 w), ((ρ s : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).charpoly.map (iotaO D.nd D.naut i) = D.naut.inePol (D.naut.locG π w) s := by
  intro D hG hF i π ρ hc ha hfull hρ k v w hwv hw s hs
  have hn : UpperTheory.GalS.Nc D.nd D.naut (D.naut.locG π w) := by
    have := hfull.2 k v
    rwa [isoLoc_cusp, ← hwv] at this
  have hr1 : 1 ≤ D.R.r := by
    have h2 := D.R.two_le_m
    simp only [Ranks.r]
    omega
  obtain ⟨r, hrc, hr⟩ := hG i D.R.r hr1 π hc ha
  obtain ⟨hιc, -⟩ := GlobalTheory.TypeLeaf.iotaOQ_continuous_injective D i
  obtain ⟨hρc, -, hρf⟩ := hρ
  have hcomp : iotaO D.nd D.naut i = (D.naut.iotaQC i).toRingHom.comp (iotaOQ D.nd D.naut i) := rfl
  have hinj : Function.Injective (Polynomial.map (D.naut.iotaQC i).toRingHom) :=
    Polynomial.map_injective _ (D.naut.iotaQC i).injective
  have hfin := placesOver_finite_of_prime D.host.E (D.nd.lPrime i).out
  have hall := (hfin.eventually_cofinite_notMem.and (D.naut.locG_unr_ae π)).and hρf
  have hd := hF _ (Filter.eventually_cofinite.1 hall)
  have key := GlobalTheory.TypeLeaf.charpoly_eq_of_dense _ (Qbar (D.nd.l i)) D.R.r
    (fun g => ((ρ g : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (D.nd.O i)).map (iotaOQ D.nd D.naut i))
    (fun g => ((r g : GL (Fin D.R.r) (Qbar (D.nd.l i))) : Matrix (Fin D.R.r) (Fin D.R.r) (Qbar (D.nd.l i))))
    _ hd (hρc.matrix_map hιc) hrc (by
      rintro g ⟨v, hv, -, B, hB, hg⟩
      obtain ⟨⟨h1, h2⟩, h3⟩ := not_not.1 hv
      apply hinj
      have hu : D.naut.unr (D.naut.wdOf i r v) := by
        rw [(hr v h1).eq_of_unr ((D.naut.unr_tw _ _).2 h2)]; exact (D.naut.unr_tw _ _).2 h2
      rw [Matrix.charpoly_map, Polynomial.map_map, ← hcomp, h3 B g hB hg, isoLoc_cusp,
        D.naut.wdOf_frob i r v h1 hrc hu B g hB hg, (hr v h1).eq_of_unr ((D.naut.unr_tw _ _).2 h2)]
      rfl) s
  rw [hcomp, ← Polynomial.map_map, ← Matrix.charpoly_map, key, D.naut.wdOf_ine i r w hw hrc s hs, (hr w hw).ine ((UpperTheory.GalS.nc_tw _ _).2 hn) s hs,
    D.naut.inePol_tw _ _ _ hs]

end GlobalTheory.IneAway

namespace GlobalTheory.TypeLeaf
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels

end GlobalTheory.TypeLeaf

namespace GlobalTheory.TypeLeaf.ConjPlace
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open GlobalTheory.TameLabels GlobalTheory.AntiRamConj GlobalTheory.TwistDet
open scoped Pointwise

end GlobalTheory.TypeLeaf.ConjPlace

namespace GlobalTheory.AdmTame
open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial

theorem galAwayOfS' {D : D7} (hG : UpperTheory.GalS.AutomorphicGaloisAdmissible D.nd D.naut) : UpperTheory.GalS.GalAwayN D := fun i a ha π hc hr => by
  obtain ⟨ρ, hρc, -, hρw, -⟩ := (hG i).1 a ha π hc hr
  exact ⟨ρ, hρc, hρw⟩

end GlobalTheory.AdmTame
