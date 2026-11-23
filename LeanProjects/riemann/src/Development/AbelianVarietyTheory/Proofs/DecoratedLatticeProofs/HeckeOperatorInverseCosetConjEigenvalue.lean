import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSatakeParametersBoundedEigenfunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsHeckeOpFullDualLab
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BoundedAutomorphicRightTranslationUnitarisableBo
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.HeckeAdjEigen

variable {D : D7} {V : HSp D}

open GlobalTheory.FinZeta (bddAut bddRep coe_bddRep)

theorem exists_dual_rep (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (P : HeightOneSpectrum (𝓞 D.host.E)) (d : List ℤ) (R : Finset (GA D V))
    (e f : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (α : GA D V)
    (hS : OffS D Sb P) (hef : IsPrimeIdem P e f) (hϖ : ϖ ∈ P.asIdeal) (hϖ2 : ϖ ∉ P.asIdeal ^ 2)
    (hd : d.Pairwise (fun a b => b ≤ a)) (hJ : ∀ g, SuppF V f g → (g ∈ J ↔ g ∈ KsphC V ∅))
    (hχ : ∀ g ∈ J, SuppF V f g → χ g = 1) (hα : SuppF V f α) (hdiv : DivAt V e (ϖ : D.host.E) d α)
    (hrep : IsCosetRep V {k | k ∈ J ∧ SuppF V f k} α R) :
    ∃ R' : Finset (GA D V), Hecke₂ V J χ Sb P (dualLab d) R' ∧ R'.card = R.card ∧
      ∀ γ ∈ R', ∃ k₁ ∈ {k | k ∈ J ∧ SuppF V f k}, ∃ k₂ ∈ {k | k ∈ J ∧ SuppF V f k}, γ = k₁ * α⁻¹ * k₂ := by
  obtain ⟨he, v, hf⟩ := GlobalTheory.HeckeDual.idem_of_isPrimeIdem hef
  obtain ⟨a, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf α).1 hα
  obtain ⟨δ, hδ, hσδ⟩ := GlobalTheory.HeckeDual.exists_skew D
  haveI := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hK : ∀ g, g ∈ {k | k ∈ J ∧ SuppF V f k} ↔
      ∃ k ∈ GlobalTheory.AdelicU.stabLoc D.sp.cm.sig V.gram (GlobalTheory.AdelicU.frameLat V) v,
        GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v k = g := fun g => by
    constructor
    · rintro ⟨h1, h2⟩
      have h3 := (hJ g h2).1 h1
      obtain ⟨k, rfl⟩ := (GlobalTheory.HeckeDual.suppF_iff V hf g).1 h2
      rw [GlobalTheory.AdelicU.KsphC_eq] at h3
      have h4 := (GlobalTheory.AdelicU.mem_levelOff.1 h3).2.2 v (Finset.notMem_empty v)
      rw [GlobalTheory.AdelicU.proj_emb_self] at h4
      exact ⟨k, h4, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      have h2 := (GlobalTheory.HeckeDual.suppF_iff V hf _).2 ⟨k, rfl⟩
      refine ⟨(hJ _ h2).2 ?_, h2⟩
      rw [GlobalTheory.AdelicU.KsphC_eq]
      exact GlobalTheory.AdelicU.emb_mem_levelOff (Finset.notMem_empty v) hk
  obtain ⟨R', h1, h2, h3⟩ := GlobalTheory.HeckeDual.exists_rep_inv
    (GlobalTheory.HeckeDual.modular_eq_one D.sp.cm.sig V.gram (fun x => star_star x) hδ hσδ
      ((GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V) v)
    (GlobalTheory.AdelicU.emb D.sp.cm.sig V.gram v) (GlobalTheory.AdelicU.emb_injective _ _ v) _
    (GlobalTheory.AdelicU.isOpen_stabLoc _ _ _ v) (GlobalTheory.AdelicU.isCompact_stabLoc _ _ _ v) _ hK a R
    (fun γ hγ => (hrep.1 γ hγ).2) hrep.2
  have hϖ0 : (ϖ : D.host.E) ≠ 0 := fun h => hϖ2 (by
    rw [show ϖ = 0 from RingOfIntegers.ext h]
    exact zero_mem _)
  refine ⟨R', ⟨e, f, ϖ, _, hS, hef, hϖ, hϖ2, ?_, hJ, hχ, (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (inv_mem ⟨a, rfl⟩),
    (GlobalTheory.DivDual.divAt_inv_and_mul V e _ d _ he hϖ0 hdiv).1, fun γ hγ => (GlobalTheory.HeckeDual.suppF_iff V hf _).2 (h1 γ hγ).1,
    fun γ hγ => ⟨?_, (h1 γ hγ).2⟩, h2⟩, h3, fun γ hγ => (h1 γ hγ).2⟩
  · rw [dualLab, List.pairwise_reverse, List.pairwise_map]
    exact hd.imp fun h => neg_le_neg h
  · obtain ⟨x, rfl⟩ := (h1 γ hγ).1
    exact GlobalTheory.AdelicU.mem_finPts.2 (GlobalTheory.AdelicU.projInf_emb _ _ v x)

theorem form_sum (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (K : Set (GA D V)) (F : bddAut V)
    (hF : ∀ k ∈ K, bddRep V k F = F) (α : GA D V) (R : Finset (GA D V))
    (hR : ∀ γ ∈ R, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * α * k₂) :
    B (∑ γ ∈ R, bddRep V γ F) F = (R.card : ℂ) * B (bddRep V α F) F := by
  rw [map_sum, LinearMap.sum_apply]
  rw [Finset.sum_congr rfl (g := fun _ => B (bddRep V α F) F), Finset.sum_const, nsmul_eq_mul]
  intro γ hγ
  obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := hR γ hγ
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hF k₂ hk₂]
  have h := hinv k₁ (bddRep V α F) F
  rwa [hF k₁ hk₁] at h

theorem form_inv (B : bddAut V →ₗ[ℂ] bddAut V →ₛₗ[starRingEnd ℂ] ℂ)
    (hsym : ∀ v w, B w v = starRingEnd ℂ (B v w))
    (hinv : ∀ g v w, B (bddRep V g v) (bddRep V g w) = B v w) (F : bddAut V) (α : GA D V) :
    B (bddRep V α⁻¹ F) F = starRingEnd ℂ (B (bddRep V α F) F) := by
  have h := hinv α⁻¹ F (bddRep V α F)
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h
  rw [h, hsym]

theorem coe_sum_bddRep (f : GA D V → ℂ) (hf : f ∈ bddAut V) (R : Finset (GA D V)) :
    ((∑ γ ∈ R, bddRep V γ ⟨f, hf⟩ : bddAut V) : GA D V → ℂ) = heckeLin V R f := by
  funext g
  rw [Submodule.coe_sum, Finset.sum_apply, heckeLin_apply]
  rfl

theorem heckeLin_eq_conj_of_dualLab : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ f ∈ GlobalTheory.FinZeta.bddAut V, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ e : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = e P (dualLab d) • f) → ∀ P d R, Hecke₂ V J χ Sb P d R → heckeLin V R f = conj (e P d) • f := by
  intro D V J χ Sb _ f hf hJχ ev heig P d R hR
  obtain ⟨e, f', ϖ, α, hS, hef, hϖ, hϖ2, hd, hJ, hχ, hα, hdiv, -, hrep⟩ := id hR
  obtain ⟨R', hR', hcard, hR're⟩ := exists_dual_rep J χ Sb P d R e f' ϖ α hS hef hϖ hϖ2 hd hJ hχ hα hdiv hrep
  obtain ⟨B, hsym, hpos, hinv⟩ := (GlobalTheory.FinZeta.bddRep_unitarisable_and_bounded D V).1
  set F : bddAut V := ⟨f, hf⟩ with hFdef
  have hFK : ∀ k ∈ {k | k ∈ J ∧ SuppF V f' k}, bddRep V k F = F := fun k hk => by
    refine Subtype.ext (funext fun g => ?_)
    rw [coe_bddRep]
    show f (g * k) = f g
    rw [hJχ k hk.1, hχ k hk.1 hk.2, one_mul]
  have e1 := heig P d R hR
  have e2 := heig P (dualLab d) R' hR'
  rw [show dualLab (dualLab d) = d by simp [dualLab, List.map_reverse]] at e2
  have s1 : (∑ γ ∈ R, bddRep V γ F) = ev P (dualLab d) • F := Subtype.ext (by
    rw [coe_sum_bddRep, e1]; rfl)
  have s2 : (∑ γ ∈ R', bddRep V γ F) = ev P d • F := Subtype.ext (by
    rw [coe_sum_bddRep, e2]; rfl)
  have t1 := form_sum B hinv _ F hFK α R (fun γ hγ => (hrep.1 γ hγ).2)
  have t2 := form_sum B hinv _ F hFK α⁻¹ R' hR're
  rw [form_inv B hsym hinv, s2, hcard, map_smul, LinearMap.smul_apply, smul_eq_mul] at t2
  rw [s1, map_smul, LinearMap.smul_apply, smul_eq_mul] at t1
  by_cases h0 : F = 0
  · have : f = 0 := congrArg Subtype.val h0
    subst this
    rw [map_zero, smul_zero]
  · have hb : B F F ≠ 0 := fun h => by
      have := hpos F h0
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    have hbr : starRingEnd ℂ (B F F) = B F F := (hsym F F).symm
    have key : ev P (dualLab d) = starRingEnd ℂ (ev P d) := by
      apply mul_right_cancel₀ hb
      rw [t1, ← hbr, ← map_mul, t2, map_mul, map_natCast, Complex.conj_conj]
    rw [e1, key]

end GlobalTheory.HeckeAdjEigen
