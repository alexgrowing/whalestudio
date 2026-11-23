import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LResCoreA
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoefficientDataExists
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGoodCompatThree
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridHeckeCharactersExist
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L

open PositivityTheory.Rg.Rsw.L.LResCore

theorem resCore : Polar → CfFJ → IdemEx → GoodEv → FixW → WMaj → JPos → CfRel → CfInv → CutLow → CutId → ThBdd → ThCoef →
    IkSch → IkEq → ResCore := by
  classical
  intro hPolar hCfFJ hIdem hGoodEv hFixW hWMaj hJPos hCfRel hCfInv hCutLow hCutId hThBdd hThCoef hIkSch hIkEq
    D n t B W hd hn hbig hlt hpos ψ hψ χ hχ hη θ hθ μB μW hμB hμW ωB ωW hωB hωW H hH hHlev Φ U d E σ hcont ε hrad
  obtain ⟨dd⟩ := hd
  have hBr : B.rank = n + t := by have := dd.rank_add; omega
  have hηB : ResEta D χ B.rank := GlobalTheory.HeckeCharsOfSquare.resEta_of_mod hη (by omega)
  have hφc : Continuous (fun g => (ωB g Φ).1 0) :=
    (hWMaj D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB Φ).1.comp (continuous_id.prodMk continuous_const)
  have hφlaw : IsLaw χ ((t : ℂ) / 2) (fun g => (ωB g Φ).1 0) := isLaw_sw hBr hωB Φ
  obtain ⟨-, hP2, -⟩ := hPolar D n W.rank t hn hbig ψ hψ χ hχ hη (fun h0 => absurd h0 (by omega)) θ hθ H hH _ hφc hφlaw
    U d E σ hcont ε hrad
  obtain ⟨UH, hUHo, hUH⟩ := hHlev
  have : Submodule.IsLattice D.host.E (stdLattice D.host.E (n + n)) := isLattice_stdLattice
  obtain ⟨S₁, hS₁⟩ := GlobalTheory.PlaceGen.exists_levelOff_le D.sp.cm.sig (Jst D n) (stdLattice D.host.E (n + n)) UH hUHo
  obtain ⟨S₂, hS₂⟩ := hFixW D n B ψ hψ χ hχ hηB θ hθ μB hμB ωB hωB
  obtain ⟨S₃, hS₃⟩ := hGoodEv D θ hθ B.rank n Φ.1 Φ.2
  obtain ⟨nb, lam, 𝓖, hnb, hlam⟩ := GlobalTheory.CompanionTheory.SWCoef.coefDataExists D n
  obtain ⟨v, hvS, C, cc, hKill, hcd, hc0, hcut⟩ := hJPos D n W.rank t hn hpos ψ hψ χ hχ hη nb hnb (S₁ ∪ S₂ ∪ S₃)
  obtain ⟨e, he⟩ := (hIdem D (S₁ ∪ S₂ ∪ S₃)).1
  have hsub2 : S₂ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hsub3 : S₃ ⊆ S₁ ∪ S₂ ∪ S₃ := fun x hx => by simp [hx]
  have hv1 : v ∉ S₁ := fun h => hvS (by simp [h])
  have hgood : Good (S₁ ∪ S₂ ∪ S₃) e Φ.1 := hS₃ _ hsub3 e he
  have hKΦ : ∀ k ∈ KAt D n v, ωB k Φ = Φ := fun k hk => hS₂ _ hsub2 e he Φ hgood k (kAt_le_kOff hvS hk)
  have hKH : ∀ k ∈ KAt D n v, ∀ g, H (g * k) = H g := fun k hk g =>
    hUH k (hS₁ (kAt_le_kOff hv1 hk)) (mem_atPts.1 (Subgroup.mem_inf.1 hk).2).1 g
  have hKφ : ∀ k ∈ KAt D n v, ∀ g, (ωB (g * k) Φ).1 0 = (ωB g Φ).1 0 := fun k hk g => by
    rw [map_mul, Module.End.mul_apply, hKΦ k hk]
  obtain ⟨νv, hνH, hνP⟩ := exists_haar_prob (KAt D n v) (isCompact_kAt v)
  have hfam : ∀ z g, ∫ k, cutR nb C (fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z) (g * k) ∂νv =
      cc z * fam H (fun g => (ωB g Φ).1 0) ((t : ℂ) / 2) z g := by
    intro z g
    refine hcut νv hνH hνP z _ (GlobalTheory.CompanionTheory.RswPolar.continuous_fam hH hφc _ z) (GlobalTheory.CompanionTheory.RswPolar.isLaw_fam hH hφlaw z) ?_ g
    intro k hk g'
    simp only [fam, hKH k hk g', hKφ k hk g']
  have hrel := hCfRel D n χ hχ H hH _ _ hφc hφlaw U d E σ hcont ε hrad nb hnb v C cc hcd νv hνP hfam
  obtain ⟨hcfCA, ⟨N, hN⟩, -⟩ := hCfFJ D n H _ _ U d E σ hcont ε hrad
  have hcfK : ∀ k, ∀ u ∈ KAt D n v, ∀ g, cf d E ((t : ℂ) / 2) ε k (g * u) = cf d E ((t : ℂ) / 2) ε k g :=
    fun k u hu g => hCfInv D n H _ _ U d E σ hcont ε hrad u (hKH u hu) (hKφ u hu) k g
  have hhigh : ∀ k, 2 ≤ k → cf d E ((t : ℂ) / 2) ε k = 0 := by
    have key : ∀ m k, 2 ≤ k → N < k + m → cf d E ((t : ℂ) / 2) ε k = 0 := by
      intro m
      induction m with
      | zero => intro k _ hk; exact hN k (by omega)
      | succ m ih =>
        intro k hk2 hkm
        have hj : ∀ j, k < j → cf d E ((t : ℂ) / 2) ε j = 0 := fun j hj => ih j (by omega) (by omega)
        have h1 := hrel k (by omega) hj
        have h2 := (hCutLow D n W.rank ψ hψ nb hnb v C hKill (cf d E ((t : ℂ) / 2) ε k) (hcfCA k).1 (hcfCA k).2
          (fun u hu g => hcfK k u hu g)).1 (hP2 k hk2)
        funext g
        have h3 := h1 g
        simp only [h2, Pi.zero_apply, integral_zero] at h3
        exact (mul_eq_zero.1 h3.symm).resolve_left hc0
    intro k hk
    exact key (N + 1) k hk (by omega)
  refine ⟨hhigh, ?_⟩
  intro X _ π _ cX κ hcX hcomp hκ hkill
  obtain ⟨a, ha⟩ := GlobalTheory.RegSch.exists_good_frameLat D B
  obtain ⟨νK, hνK, hνK1⟩ := exists_haar_prob _ ha.isCompact_K
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t n
  have : LocallyCompactSpace (GA D W) := (GlobalTheory.MemberAdelicTop.locallyCompact_secondCountable_t2 D W).1
  let I : IkD dd n := IkD.mk _ ha νK hνK hνK1 μ₁ ⟨𝓕₁, hμ₁⟩ Measure.haar inferInstance
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_fundDom D W I.m I.haar
  let Ψ : schwartzA θ W.rank n := ⟨ikp I Φ.1, (hIkSch D n t B W dd I θ hθ Φ.1 Φ.2).2⟩
  let Ψ' : schwartzA θ W.rank n := ∑ x ∈ C.s, C.co x • ωW (nb x) Ψ
  have hStg : Stg dd hn ψ χ θ μB μW ωB ωW := ⟨hbig, hlt, hpos, hψ, hχ, hη, hθ, hμB, hμW, hωB, hωW⟩
  obtain ⟨κ', hκ'⟩ := hCutId D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I H hH Φ U d E σ hcont ε hrad nb hnb v C hKill
    (fun k hk => ⟨hKΦ k hk, hKH k hk⟩) 𝓕 h𝓕 Ψ Ψ' rfl rfl
  have hΨinv : ∀ k ∈ KAt D n v, ωW k Ψ = Ψ := fun k hk => Subtype.ext (by
    rw [hIkEq D n t B W dd hn ψ χ θ μB μW ωB ωW hStg I Φ Ψ rfl k, hKΦ k hk])
  obtain ⟨hθc, -, -, hθb, -⟩ := hThBdd D n W ψ hψ χ hχ hη θ hθ μW hμW ωW hωW nb hnb v C hKill Ψ Ψ' hΨinv rfl
  have h𝓕fin : I.m 𝓕 ≠ ⊤ := (hThCoef D n W ψ hψ θ hθ I.m 𝓕 I.haar h𝓕 lam 𝓖 hlam Ψ.1 Ψ.2).1
  have : IsFiniteMeasure (I.m.restrict 𝓕) := isFiniteMeasure_restrict.2 h𝓕fin
  obtain ⟨b, hb⟩ := hθb _ (hcomp.mul (isCompact_kAt (n := n) v))
  have hbound : ∀ x (p : KAt D n v × GA D W), ‖theta ωW Ψ' (cX x * p.1) p.2‖ ≤ b := fun x p =>
    hb _ (Set.mul_mem_mul (subset_closure (Set.mem_range_self x)) p.1.2) p.2
  have hmeas : Measurable (fun q : X × (KAt D n v × GA D W) => theta ωW Ψ' (cX q.1 * q.2.1) q.2.2) :=
    hθc.measurable.comp (((hcX.comp measurable_fst).mul
      (measurable_subtype_coe.comp (measurable_fst.comp measurable_snd))).prodMk (measurable_snd.comp measurable_snd))
  have hintx : ∀ x, Integrable (fun p : KAt D n v × GA D W => theta ωW Ψ' (cX x * p.1) p.2)
      (νv.prod (I.m.restrict 𝓕)) := fun x =>
    Integrable.of_bound (hmeas.comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable b
      (ae_of_all _ (hbound x))
  have hint : Integrable (Function.uncurry fun (x : X) (p : KAt D n v × GA D W) =>
      theta ωW Ψ' (cX x * p.1) p.2 * κ x) (π.prod (νv.prod (I.m.restrict 𝓕))) := by
    refine Integrable.mono' ((hκ.norm.const_mul b).comp_fst (νv.prod (I.m.restrict 𝓕)))
      (hmeas.aestronglyMeasurable.mul hκ.aestronglyMeasurable.comp_fst) (ae_of_all _ fun q => ?_)
    simp only [Function.uncurry, norm_mul]
    exact mul_le_mul_of_nonneg_right (hbound q.1 q.2) (norm_nonneg _)
  have hpt : ∀ x, cf d E ((t : ℂ) / 2) ε 1 (cX x) * κ x =
      (cc ((t : ℂ) / 2))⁻¹ * κ' * ∫ p, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂(νv.prod (I.m.restrict 𝓕)) := by
    intro x
    have h1 := hrel 1 le_rfl (fun j hj => hhigh j hj) (cX x)
    simp only [hκ'] at h1
    rw [integral_const_mul] at h1
    have e2 : ∫ p, theta ωW Ψ' (cX x * p.1) p.2 ∂(νv.prod (I.m.restrict 𝓕)) =
        ∫ u, ∫ h in 𝓕, theta ωW Ψ' (cX x * u) h ∂I.m ∂νv := integral_prod _ (hintx x)
    rw [integral_mul_const, e2, (eq_inv_mul_iff_mul_eq₀ hc0).2 h1.symm]
    ring
  have hzero : ∀ p : KAt D n v × GA D W, ∫ x, theta ωW Ψ' (cX x * p.1) p.2 * κ x ∂π = 0 := by
    intro p
    simp only [theta_mul]
    exact hkill (ωW p.1 Ψ') p.2
  simp only [hpt]
  rw [integral_const_mul, integral_integral_swap hint]
  simp only [hzero, integral_zero, mul_zero]

end PositivityTheory.Rg.Rsw.L

end
