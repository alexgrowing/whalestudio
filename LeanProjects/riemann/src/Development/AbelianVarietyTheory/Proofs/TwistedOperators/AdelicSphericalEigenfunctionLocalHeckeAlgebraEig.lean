import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConstMemBddAut
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsParamFunVIffIsSysParamDOfLevel
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.CommensuratedOfIsOpenIsCompact
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HostPrimeSplitting.FinrankOE
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.LFun GlobalTheory.AdelicU GlobalTheory.PRep GlobalTheory.FinZeta GlobalTheory.AdelicScalar GlobalTheory.IndefiniteRowSideFullHecke.TwistedLevelValues GlobalTheory.LiftRows
open Formalism.IndefR.Lev (levG levChi IsBaseFrame)
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke dosetInd IsCommensurated)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (IsUnitarisable IsIrrSmooth bcParam)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinZeta

variable {D : D7}

theorem isUnram_of_not_isSplit {v : HeightOneSpectrum (𝓞 D.host.F)} (hs : ¬ IsSplit (E := D.host.E) v) :
    Formalism.MainNotions.SchurIrreducible.IsUnram (E := D.host.E) v := by
  intro P hP
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hP
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      Q ∈ Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F)) ↔ Q.under (𝓞 D.host.F) = v := by
    intro Q
    rw [hPv]
    simp only [Formalism.L2.Host.aboveF, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
  have h1 : (Formalism.L2.Host.aboveF (L := D.host.E) D.host.F (P.under (𝓞 D.host.F))).card = 1 := by
    refine Finset.card_eq_one.2 ⟨P, Finset.eq_singleton_iff_unique_mem.2 ⟨(hmem P).2 hPv, fun Q hQ => ?_⟩⟩
    by_contra hne
    exact hs ⟨Q, P, hne, congrArg HeightOneSpectrum.asIdeal ((hmem Q).1 hQ), hP⟩
  exact PI.UnitaryGroupMassFormula.HostPrimeFacts.unram D.R D.host P h1

theorem exists_cartan (V : HSp D) (v : HeightOneSpectrum (𝓞 D.host.F)) :
    ∃ (w : HeightOneSpectrum (𝓞 D.host.E)) (h : w.under (𝓞 D.host.F) = v), ∀ g : Gv V v,
      ∃ k₁ ∈ Kv V v, ∃ k₂ ∈ Kv V v, ∃ (g' : Gv V v) (a : GL (Fin V.rank) (w.adicCompletion D.host.E))
        (d : Fin V.rank → ℤ) (u : Fin V.rank → w.adicCompletion D.host.E),
        IsFrameAt w (frameLat V) a ∧ Antitone d ∧ (∀ i, Valued.v (u i) = WithZero.exp (-d i)) ∧
        (a⁻¹ * locMat D.sp.cm.sig V.gram h g' * a).1 = Matrix.diagonal u ∧ g = k₁ * g' * k₂ := by
  have hL := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hH := (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V
  have hd := GlobalTheory.AdelicU.SelfDual.isSelfDualAt_frameLat D V v
  by_cases hsp : IsSplit (E := D.host.E) v
  · obtain ⟨w, -, -, hw, -⟩ := id hsp
    have h : w.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hw
    obtain ⟨e, ⟨⟨a, ha, e1⟩, e2⟩, -⟩ :=
      GlobalTheory.LFun.SplitChart.exists_isSplitChart (isCMExt_host D) hH hL.fg hL.span_eq_top h hsp hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨ϖ, hϖ⟩ := exists_isUnifV w
    obtain ⟨d, hdA, k₁, h₁, k₂, h₂, eg⟩ := Formalism.UG.Final.CartanDecomp D.host.E w V.rank ϖ (mem_Ov_of_isUnifV hϖ) hϖ (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm (k₁⁻¹ * e g * k₂⁻¹), a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, ?_, ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hϖ, ← WithZero.exp_zsmul]
      simp
    · rw [← e1, e.apply_symm_apply, Units.val_mul, Units.val_mul, eg, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
        Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
      rfl
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply]
      group
  · obtain ⟨w, hw⟩ := ((exists_isInertChart _ (isCMExt_host D) v).1 (isUnram_of_not_isSplit hsp)).resolve_left hsp
    have h : w.under (𝓞 D.host.F) = v := (GlobalTheory.LFun.InertChart.under_eq_iff hw w).2 rfl
    obtain ⟨-, ⟨c, hc, -⟩, -, -, hrest⟩ := (exists_isInertChart _ (isCMExt_host D) v).2 w h hw
    obtain ⟨⟨ϖ, hU⟩, hch⟩ := hrest c hc
    obtain ⟨e, ⟨-, ⟨a, ha, -, e1⟩, e2⟩, -⟩ := hch _ _ _ hH hL.fg hL.span_eq_top hd
    refine ⟨w, h, fun g => ?_⟩
    obtain ⟨d, t, hdA, ht, k₁, h₁, k₂, h₂, eg⟩ := GlobalTheory.LFun.cartanU hU (e g)
    refine ⟨e.symm k₁, (e2 _).2 (by simpa using h₁), e.symm k₂, (e2 _).2 (by simpa using h₂),
      e.symm t, a, d, fun i => ϖ ^ d i, ha, hdA, fun i => ?_, by rw [← e1, e.apply_symm_apply, ht], ?_⟩
    · rw [map_zpow₀, show Valued.v ϖ = WithZero.exp (-1 : ℤ) from hU.2.2.2.1, ← WithZero.exp_zsmul]
      simp
    · apply e.injective
      simp only [map_mul, e.apply_symm_apply, eg]

theorem eigen_heckeAlg : ∀ (D : D7) (V : HSp D) (J : Set (GA D V)) (χ : GA D V → ℂ) (Sb : Finset (HeightOneSpectrum (𝓞 D.host.F))), SphOff J χ Sb → ∀ v ∉ Sb, ∀ f : GA D V → ℂ, (∀ k ∈ J, ∀ g, f (g * k) = χ k * f g) → ∀ c : HeightOneSpectrum (𝓞 D.host.E) → List ℤ → ℂ, (∀ w d R, Hecke₂ V J χ Sb w d R → heckeLin V R f = c w d • f) → f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) ∧ ∀ h ∈ Hecke ℂ (Kv V v), ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f := by
  intro D V J χ Sb hJ v hv f hf c hc
  have hfix : f ∈ fixed ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) :=
    GlobalTheory.LGrp.mem_fixed.2 fun k hk => funext (fixed_of_level hJ hv hf hk)
  refine ⟨hfix, fun x hx => ?_⟩
  obtain ⟨w, h, hcart⟩ := exists_cartan V v
  have hs := isEigenSys_of_heckeLin hJ hv h hfix (hc w)
  have := GlobalTheory.HeckeDual.isLattice_frameLat V
  have hK : IsCommensurated (Kv V v) := PI.UnitaryGroupMassFormula.AdIndexEq.commensurated_of_isOpen_isCompact _
    (isOpen_stabLoc D.sp.cm.sig V.gram (frameLat V) v) (isCompact_stabLoc D.sp.cm.sig V.gram (frameLat V) v)
  have hm := Formalism.UG.Final.DosetIndMem (Gv V v) (Kv V v) ℂ
  refine GlobalTheory.LFun.hecke_induction (K := Kv V v)
    (p := fun h => ∃ a : ℂ, heckeVec ((rightReg ℂ (GA D V) ℂ).comp (embV V v)) (Kv V v) h f = a • f)
    ⟨0, by simp [heckeVec]⟩ ?_ ?_ hx
  · rintro g1 hg1 g2 hg2 ⟨a1, e1⟩ ⟨a2, e2⟩
    exact ⟨a1 + a2, by rw [GlobalTheory.LFun.heckeVec_add hK _ hg1 hg2, e1, e2, add_smul]⟩
  · intro r g
    obtain ⟨k₁, hk₁, k₂, hk₂, g', a, d, u, ha, hd, hu, hg, rfl⟩ := hcart g
    refine ⟨r * c w (List.ofFn d), ?_⟩
    rw [GlobalTheory.LFun.dosetInd_mul hk₁ hk₂, GlobalTheory.LFun.heckeVec_smul hK _ r (hm g'), hs a g' d u ha hd hu hg, smul_smul]

end GlobalTheory.FinZeta
