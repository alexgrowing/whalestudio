import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1DualPairStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CupProductFiniteClassesCoboundaryStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TateDualityDegreeOneContinuousCocyclesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankH1fDeRhamStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFiltrationDualityStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

namespace GlobalTheory.BlochKatoAnn

section Abstract

variable {k Z Z' : Type} [Field k] [AddCommGroup Z] [Module k Z] [AddCommGroup Z'] [Module k Z']
  [FiniteDimensional k Z] [FiniteDimensional k Z']

def rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) : Submodule k Z' :=
  (W.map β).dualCoannihilator

theorem mem_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (b : Z') :
    b ∈ rorth β W ↔ ∀ a ∈ W, β a b = 0 := by
  unfold rorth
  rw [Submodule.mem_dualCoannihilator]
  constructor
  · intro h a ha
    exact h _ ⟨a, ha, rfl⟩
  · rintro h _ ⟨a, ha, rfl⟩
    exact h a ha

theorem finrank_rorth (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (hW : LinearMap.ker β ≤ W) :
    finrank k (rorth β W) + finrank k W = finrank k Z' + finrank k (LinearMap.ker β) := by
  have h1 := Subspace.finrank_add_finrank_dualCoannihilator_eq (W.map β)
  have h2 := LinearMap.finrank_range_add_finrank_ker (β.domRestrict W)
  have h3 : LinearMap.range (β.domRestrict W) = W.map β := by
    rw [LinearMap.range_domRestrict]
  have h4 : LinearMap.ker (β.domRestrict W) = (LinearMap.ker β).comap W.subtype := by
    rw [LinearMap.ker_domRestrict]
  have h5 : finrank k ((LinearMap.ker β).comap W.subtype) = finrank k (LinearMap.ker β) :=
    (Submodule.comapSubtypeEquivOfLe hW).finrank_eq
  rw [h3, h4, h5] at h2
  unfold rorth
  linarith

theorem rorth_top (β : Z →ₗ[k] Z' →ₗ[k] k) : rorth β ⊤ = LinearMap.ker β.flip := by
  ext b
  rw [mem_rorth, LinearMap.mem_ker]
  constructor
  · intro h
    ext a
    exact h a trivial
  · intro h a _
    have := LinearMap.congr_fun h a
    simpa using this

theorem exact_ann (β : Z →ₗ[k] Z' →ₗ[k] k) (W : Submodule k Z) (W' : Submodule k Z')
    (hW : LinearMap.ker β ≤ W) (hW' : LinearMap.ker β.flip ≤ W')
    (hort : ∀ a ∈ W, ∀ b ∈ W', β a b = 0)
    (hdim : finrank k W + finrank k W' = finrank k Z + finrank k (LinearMap.ker β.flip)) :
    rorth β W = W' ∧ rorth β.flip W' = W := by
  have hT := finrank_rorth β ⊤ (le_top)
  rw [rorth_top, finrank_top] at hT
  have hA := finrank_rorth β W hW
  have hB := finrank_rorth β.flip W' hW'
  have l1 : W' ≤ rorth β W := fun b hb => (mem_rorth β W b).2 fun a ha => hort a ha b hb
  have l2 : W ≤ rorth β.flip W' := fun a ha => (mem_rorth β.flip W' a).2 fun b hb => by
    rw [LinearMap.flip_apply]; exact hort a ha b hb
  constructor
  · exact (Submodule.eq_of_le_of_finrank_eq l1 (by omega)).symm
  · exact (Submodule.eq_of_le_of_finrank_eq l2 (by omega)).symm

end Abstract

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

section Concrete

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] {O : Type} [CommRing O]
    [Algebra O LL]

theorem galoisCoboundaries_le_continuousCocycles (A : GRep G Qp LL O) : B1 A.ρ ≤ continuousCocycles A.ρ := by
  rintro _ ⟨x, rfl⟩
  refine ⟨?_, fun g h => ?_⟩
  · have : (cob A.ρ x : G → A.V) = fun g => A.ρ g x + (-x) := by
      funext g
      simp [cob, sub_eq_add_neg]
    rw [this]
    exact (A.cont x).add continuous_const
  · simp only [cob, LinearMap.pi_apply, LinearMap.sub_apply, LinearMap.id_apply, map_mul,
      Module.End.mul_apply, map_sub]
    abel

theorem B1_le_Z1f (A : GRep G Qp LL O) : B1 A.ρ ≤ finiteCocycles PD A.ρ := by
  intro c hc
  refine ⟨galoisCoboundaries_le_continuousCocycles A hc, ?_⟩
  obtain ⟨x, rfl⟩ := hc
  refine ⟨x ⊗ₜ[Qp] (1 : B), fun g => ?_⟩
  simp [cob, actVB, sub_tmul]

theorem blochKatoFiniteCocycles_le_continuousCocycles (A : GRep G Qp LL O) : finiteCocycles PD A.ρ ≤ continuousCocycles A.ρ := fun _ h => h.1

theorem finite_continuous_cocycles_localGaloisRep (A : GRep G Qp LL O) (h : Module.Finite LL (H1V A.ρ)) :
    FiniteDimensional LL (continuousCocycles A.ρ) := by
  haveI : FiniteDimensional LL (B1 A.ρ) := LinearMap.finiteDimensional_range (cob A.ρ)
  have hK : FiniteDimensional LL ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype) :=
    Module.Finite.equiv (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).symm
  show Module.Finite LL (continuousCocycles A.ρ)
  rw [Module.finite_def]
  apply Submodule.fg_of_fg_map_of_fg_inf_ker ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype).mkQ
  · rw [Submodule.map_top, Submodule.range_mkQ]
    exact Module.finite_def.1 h
  · rw [top_inf_eq, Submodule.ker_mkQ]
    exact Module.Finite.iff_fg.1 hK

theorem finrank_H1V (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (H1V A.ρ) + finrank LL (B1 A.ρ) = finrank LL (continuousCocycles A.ρ) := by
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (continuousCocycles A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq] at e
  exact e

theorem finrank_H1fV (A : GRep G Qp LL O) [FiniteDimensional LL (continuousCocycles A.ρ)] :
    finrank LL (FiniteCohomology PD A.ρ) + finrank LL (B1 A.ρ) =
      finrank LL ((finiteCocycles PD A.ρ).comap (continuousCocycles A.ρ).subtype) := by
  have eW := (Submodule.comapSubtypeEquivOfLe (blochKatoFiniteCocycles_le_continuousCocycles PD A))
  haveI : FiniteDimensional LL (finiteCocycles PD A.ρ) := Module.Finite.equiv eW
  have e := Submodule.finrank_quotient_add_finrank ((B1 A.ρ).comap (finiteCocycles PD A.ρ).subtype)
  rw [(Submodule.comapSubtypeEquivOfLe (B1_le_Z1f PD A)).finrank_eq] at e
  rw [eW.finrank_eq]
  exact e

end Concrete

end GlobalTheory.BlochKatoAnn

namespace GlobalTheory.BlochKatoAnn

theorem bkA_exact_annihilators : Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI →
      ∀ K : FinExt l, bkACore (P.PD K) := by
  intro hTD hEC l _ P AI hT K
  intro LL _ _ _ O _ _ hO A A' m hdr hdual
  have hdual' : IsDual1 (P.PD K) A'.ρ A.ρ m.flip := by
    obtain ⟨h1, h2, h3, h4⟩ := hdual
    refine ⟨fun g y x => ?_, fun y hy => h3 y hy, fun x hx => h2 x hx, h4.symm⟩
    simp only [LinearMap.flip_apply]
    exact h1 g x y
  obtain ⟨hdrd, hfd⟩ := GlobalTheory.T.de_rham_filtration_duality l P AI hT K
  have hdr' : IsDR (P.PD K) A'.ρ := hdrd LL O hO A A' m hdr hdual
  have hfil := hfd LL O hO A A' m hdr hdual
  obtain ⟨hH1fin, hH1⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A A' m hdual
  obtain ⟨hH1fin', -⟩ := GlobalTheory.T.finrank_H1_dual_pair hTD hEC l P K LL O hO A' A m.flip hdual'
  obtain ⟨-, hf⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A hdr
  obtain ⟨-, hf'⟩ := GlobalTheory.T.finrank_H1f_de_rham l P AI hT K LL O hO A' hdr'
  have hort := GlobalTheory.T.cup_product_finite_classes_coboundary l P AI hT K LL O hO A A' m hdr hdual
  obtain ⟨β, hβ, hl, hr⟩ := GlobalTheory.T.tateDuality_degreeOne_continuous_cocycles hTD l P K LL O hO A A' m hdual
  haveI := finite_continuous_cocycles_localGaloisRep A hH1fin
  haveI := finite_continuous_cocycles_localGaloisRep A' hH1fin'
  have hkl : LinearMap.ker β = (B1 A.ρ).comap (continuousCocycles A.ρ).subtype := by
    ext a
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hl a]
    constructor
    · intro h b
      rw [h]
      rfl
    · intro h
      ext b
      exact h b
  have hkr : LinearMap.ker β.flip = (B1 A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    ext b
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, ← hr b]
    constructor
    · intro h a
      have := LinearMap.congr_fun h a
      simpa using this
    · intro h
      ext a
      simpa using h a
  have hW : LinearMap.ker β ≤ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype := by
    rw [hkl]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A)
  have hW' : LinearMap.ker β.flip ≤ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype := by
    rw [hkr]
    exact Submodule.comap_mono (B1_le_Z1f (P.PD K) A')
  have horth : ∀ a ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype,
      ∀ b ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype, β a b = 0 := by
    intro a ha b hb
    rw [hβ]
    exact hort a.1 ha b.1 hb
  have eZ := finrank_H1V A
  have eW := finrank_H1fV (P.PD K) A
  have eW' := finrank_H1fV (P.PD K) A'
  have eKl : finrank LL (LinearMap.ker β) = finrank LL (B1 A.ρ) := by
    rw [hkl]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A)).finrank_eq
  have eKr : finrank LL (LinearMap.ker β.flip) = finrank LL (B1 A'.ρ) := by
    rw [hkr]
    exact (Submodule.comapSubtypeEquivOfLe (galoisCoboundaries_le_continuousCocycles A')).finrank_eq
  have hdV := hdual.2.2.2
  unfold IsDR at hdr hdr'
  rw [← hdV] at hdr'
  have hdim : finrank LL ((finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype) +
      finrank LL ((finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype) =
      finrank LL (continuousCocycles A.ρ) + finrank LL (LinearMap.ker β.flip) := by
    rw [eKr]
    zify at eZ eW eW' hH1 hfil hdr hdr' ⊢
    linarith
  obtain ⟨h1, h2⟩ := exact_ann β _ _ hW hW' horth hdim
  constructor
  · intro a ha
    change (⟨a, ha⟩ : continuousCocycles A.ρ) ∈ (finiteCocycles (P.PD K) A.ρ).comap (continuousCocycles A.ρ).subtype ↔ _
    rw [← h2, mem_rorth]
    constructor
    · intro h b hb
      have := h ⟨b, hb.1⟩ hb
      rw [LinearMap.flip_apply, hβ] at this
      exact this
    · intro h b hb
      rw [LinearMap.flip_apply, hβ]
      exact h b.1 hb
  · intro b hb
    change (⟨b, hb⟩ : continuousCocycles A'.ρ) ∈ (finiteCocycles (P.PD K) A'.ρ).comap (continuousCocycles A'.ρ).subtype ↔ _
    rw [← h1, mem_rorth]
    constructor
    · intro h a ha
      have := h ⟨a, ha.1⟩ ha
      rw [hβ] at this
      exact this
    · intro h a ha
      rw [hβ]
      exact h a.1 ha

end GlobalTheory.BlochKatoAnn
