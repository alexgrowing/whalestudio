import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralUnramifiedOutsideOpenSubsetInsertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PeterssonCoefficientBoundedSphericalUnramifiedStatement
open scoped ComplexConjugate Matrix NNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP

noncomputable section

namespace GlobalTheory.Core.Rk.EulStep

theorem isOpen_openOff {D : D7} (A : HSp D) (L : Lat A) (hL : IsSelfDualC A L) (S : Finset (FinPl D)) :
    IsOpen (openOff A L S) := by
  have := hL.1
  let U : Subgroup (GA D A) :=
    ⨅ k, ⨅ (_ : k ∉ S), (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k)
  have hU : ∀ g, g ∈ U ↔ g ∈ openOff A L S := fun g => by simp [U, Subgroup.mem_iInf, openOff]
  have hUo : IsOpen (U : Set (GA D A)) :=
    Subgroup.isOpen_mono (H₁ := ⨅ k, (stabLoc D.sp.cm.sig A.gram L k).comap (proj D.sp.cm.sig A.gram k))
      (fun g hg => (hU g).2 fun k _ => Subgroup.mem_iInf.1 hg k)
      (by
        convert (isRestrGroup_GAd D.sp.cm.sig A.gram L).isOpen_all using 1
        ext g
        simp [Subgroup.mem_iInf])
  convert hUo using 1
  exact Set.ext fun g => (hU g).symm

theorem sphFun_of_param {D : D7} {V : HSp D} {Λ : Lat V} {Sf : Finset (FinPl D)} {f : GA D V → ℂ}
    {B : GlobalTheory.LFun.Fam D.host.E} (hf : GlobalTheory.LFun.IsParamFun D.sp.cm.sig V.gram Λ (Sf : Set (FinPl D)) f B) :
    SphFun V Λ Sf f := by
  intro v hv k hk g
  obtain ⟨w, hw⟩ : ∃ w : HeightOneSpectrum (𝓞 D.host.E), w.under (𝓞 D.host.F) = v := by
    have := v.isMaximal
    obtain ⟨Q, hQ, hl⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, HeightOneSpectrum.ext hl.over.symm⟩
  have hx := (hf v (by simpa using hv) w hw).mem_fixed
  have := congrFun (hx ⟨k, hk⟩) g
  simpa [GlobalTheory.PRep.rightReg, LinearMap.funLeft] using this

theorem setIntegral_openOff_union : GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, SphFactor D → LocalZetaOn D (fun _ => True) → ∀ (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (A B : HSp D) (χA χB : (AE D)ˣ →* Circle) (sA : RealMat A) (sB : RealMat B) (t : ℕ) (cA : CptF A) (a : GL (Fin A.rank) (AE D)) (om : WRep A B) (ν : Measure (WO A B)) (𝓕 : Set (WO A B)), Pair ψ θ A B χA χB sA sB t cA a om ν 𝓕 → ∀ (LA : Lat A) (LB : Lat B) (Sf : Finset (FinPl D)) (Φ₁ Φ₂ : WO A B → ℂ), IsThetaFunO ψ A B Φ₁ → IsThetaFunO ψ A B Φ₂ → Unram ψ A B χB LA LB Sf Φ₁ Φ₂ → ∀ m : Measure (GA D A), m.IsHaarMeasure → ∀ u₁ ∈ A0 θ A cA, ∀ u₂ ∈ A0 θ A cA, ∀ par : GlobalTheory.LFun.Fam D.host.E, GlobalTheory.LFun.IsParamFun D.sp.cm.sig A.gram LA (Sf : Set (FinPl D)) u₁ par → SphFun A LA Sf u₂ → ∀ s : ℂ, (A.rank : ℝ) < s.re → Integrable (integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s) m → ∀ S₁ S₂ : Finset (FinPl D), Sf ⊆ S₁ → Disjoint S₁ S₂ → ∀ S₃ : Finset (FinPl D), (∀ u, u ∈ S₃ ↔ u ∈ S₁ ∨ u ∈ S₂) → ∫ g in openOff A LA S₃, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m = (∏ v ∈ S₂, GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s) * ∫ g in openOff A LA S₁, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
  intro hP D hSF hLZ ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU m hm u₁ hu₁ u₂ hu₂ par hpar hsph
    s hs hint
  have : BorelSpace (GA D A) := ⟨rfl⟩
  have := hU.sdA.1
  have hsph₁ : SphFun A LA Sf u₁ := sphFun_of_param hpar
  have step : ∀ (S : Finset (FinPl D)) (v : FinPl D), Sf ⊆ S → v ∉ S → ∀ S' : Finset (FinPl D),
      (∀ u, u ∈ S' ↔ u = v ∨ u ∈ S) →
      ∫ g in openOff A LA S', integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m =
        GlobalTheory.LFun.LvTw par (GlobalTheory.LFun.val χB) v (s + 1 / 2) / GlobalTheory.LFun.dv D.host.E A.rank B.rank v s *
          ∫ g in openOff A LA S, integrand om m ν 𝓕 LA a Φ₁ Φ₂ u₁ u₂ s g ∂m := by
    intro S v hS hv S' hS'
    have hvf : v ∉ Sf := fun h => hv (hS h)
    rw [GlobalTheory.T.integral_unramifiedOutsideOpenSubset_insert_place D A LA hU.sdA m hm S v hv (haarLoc D.sp.cm.sig A.gram LA v) inferInstance
      (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) S' hS' _ hint.integrableOn, ← integral_const_mul]
    refine setIntegral_congr_fun (isOpen_openOff A LA hU.sdA S).measurableSet fun x hx => ?_
    obtain ⟨φ, hφ, hfac⟩ := hSF ψ θ A B χA χB sA sB t cA a om ν 𝓕 hpair LA LB Sf Φ₁ Φ₂ hΦ₁ hΦ₂ hU v hvf s
    have hk : proj D.sp.cm.sig A.gram v x ∈ stabLoc D.sp.cm.sig A.gram LA v := hx v hv
    obtain ⟨x', hx'⟩ : ∃ x', x' = x * (emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x))⁻¹ := ⟨_, rfl⟩
    have hx1 : proj D.sp.cm.sig A.gram v x' = 1 := by
      rw [hx', map_mul, map_inv, proj_emb_self, mul_inv_cancel]
    have hxe : x = x' * emb D.sp.cm.sig A.gram v (proj D.sp.cm.sig A.gram v x) := by
      rw [hx', inv_mul_cancel_right]
    have hc := GlobalTheory.T.petersson_coefficient_bounded_spherical_unramified hP D θ A cA LA hpair.setting.2.2.2.1 m hm Sf u₁ hu₁ u₂ hu₂ par hpar hsph v hvf x' hx1
    have hz := (hLZ A LA hU.sdA χB B.rank hpair.weil.hecT hpair.weil.resT v trivial
      (fun w hw => hU.unr w (by
        show ¬ (w.under (𝓞 D.host.F) ∈ (Sf : Set (FinPl D)))
        rw [hw]; simpa using hvf))
      (haarLoc D.sp.cm.sig A.gram LA v) inferInstance (haarLoc_stabLoc D.sp.cm.sig A.gram LA v) s hs φ hφ par _ hc).2
    have hφk : φ (ioAt A v (proj D.sp.cm.sig A.gram v x)) = 1 := by
      have := hφ.2.1 (ioAt A v (proj D.sp.cm.sig A.gram v x))
        ((ioH_mem_KFin (gram_hdbl A)).2 ⟨hk, one_mem _⟩) 1
      rw [one_mul, hφ.2.2] at this
      exact this
    have hr : rcoef m u₁ u₂ x = rcoef m u₁ u₂ x' := by
      have : rTr A x u₁ = rTr A x' u₁ := funext fun g => by
        simp only [rTr]
        conv_lhs => rw [hxe, ← mul_assoc]
        exact hsph₁ v hvf _ hk _
      simp only [rcoef, this]
    have hw := hfac x' hx1 (proj D.sp.cm.sig A.gram v x)
    rw [← hxe, hφk, mul_one] at hw
    simp only [← hx', integrand, hfac x' hx1, hw, hr, mul_assoc]
    rw [integral_const_mul, integral_const_mul, hz, map_one, mul_one]
    ring
  intro S₁ S₂ hS₁
  classical
  induction S₂ using Finset.induction_on with
  | empty =>
    intro _ S₃ h
    obtain rfl : S₃ = S₁ := Finset.ext fun u => by simpa using h u
    simp
  | insert v S₂ hv ih =>
    intro hd S₃ h
    rw [Finset.disjoint_insert_right] at hd
    rw [step (S₁ ∪ S₂) v (hS₁.trans Finset.subset_union_left) (by simp [hd.1, hv]) S₃
      (fun u => by rw [h u, Finset.mem_insert, Finset.mem_union]; tauto),
      ih hd.2 _ (fun u => Finset.mem_union), Finset.prod_insert hv, mul_assoc]

end GlobalTheory.Core.Rk.EulStep

end
