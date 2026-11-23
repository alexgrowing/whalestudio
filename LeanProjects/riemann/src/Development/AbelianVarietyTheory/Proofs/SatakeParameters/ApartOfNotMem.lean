import Mathlib
import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRationalLocalOperators
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLimitRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LinApproxOfPolyApproxTrc
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KerOfLinApprox
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EquivOfISupRange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong.OffTLimit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem apart_of_not_mem {w₀ w : HeightOneSpectrum (𝓞 E)} (h₀ : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w w₀ := by
  intro h
  apply hw
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (w₀.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h₀
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem z_eq_of_equiv {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (j : J)
    {σ σ' : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))} (e : σ.ρ.Equiv σ'.ρ)
    (hne : PRep.fixed σ.ρ (Kw (O.pl j)) ≠ ⊥) : O.z j σ = O.z j σ' := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have he : ∀ g u, e.toLinearEquiv (σ.ρ g u) = σ'.ρ g (e.toLinearEquiv u) := fun g u =>
    LinearMap.congr_fun (e.isIntertwining' g) u
  have hv' : e.toLinearEquiv v ∈ PRep.fixed σ'.ρ (Kw (O.pl j)) := by
    change ∀ h : Kw (O.pl j), σ'.ρ (h : GL (Fin a) ((O.pl j).adicCompletion E)) (e.toLinearEquiv v) =
      ((1 : Kw (O.pl j) →* ℂˣ) h : ℂ) • e.toLinearEquiv v
    intro h
    have := hv h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
    rw [← he, this]
  have hop : e.toLinearEquiv (opOf σ.ρ (O.f j) v) = opOf σ'.ρ (O.f j) (e.toLinearEquiv v) := by
    simp only [opOf, Finsupp.sum, map_sum, map_smul, he]
  have h2 := O.act j σ' _ hv'
  rw [← hop, O.act j σ v hv, map_smul] at h2
  have hne' : e.toLinearEquiv v ≠ 0 := by simpa using hv0
  exact smul_left_injective ℂ hne' h2

end GlobalTheory.Cong.OffTLimit

namespace GlobalTheory.Cong

end GlobalTheory.Cong
