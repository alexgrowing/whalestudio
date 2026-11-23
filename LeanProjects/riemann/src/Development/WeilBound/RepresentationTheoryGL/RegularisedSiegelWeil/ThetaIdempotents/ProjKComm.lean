import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.LIkSch
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasChr
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumDoubledOfSchrodingerFormulas
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CompactAverageProjectionThetaSchrodingerStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IkedaMapSchrodingerPartialIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchrodingerThetaEqSchwartzBruhatStatement

noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS GlobalTheory.RegSW GlobalTheory.IkedaK

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RegSch (ikS projS Lvl)

namespace PositivityTheory.Rg.Rsw.L.LIkEq2

theorem projK_comm {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle} {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}
    (hW : IsWeilDatumO ψ S T χS χT om) (K : Subgroup (GA D T)) (hKc : IsCompact (K : Set (GA D T))) (ν : Measure K)
    [IsProbabilityMeasure ν] (φ : WO S T → ℂ) (hφ : IsThetaFunO ψ S T φ) (hP : IsThetaFunO ψ S T (projK om ν φ)) (g : GA D S) :
    projK om ν (om (g, 1) φ) = om (g, 1) (projK om ν φ) := by
  have : BorelSpace (GA D T) := ⟨rfl⟩
  have : SecondCountableTopology (GA D T) := (GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D T).2.1
  funext x
  have hc := GlobalTheory.Unf.jointCont_all D ψ S T χS χT om hW φ hφ
  obtain ⟨C1, hC1⟩ := bdd_om_compact hW hφ ((isCompact_singleton (x := (1 : GA D S))).prod hKc)
  obtain ⟨C2, hC2⟩ := bdd_om_compact hW hφ ((isCompact_singleton (x := g)).prod hKc)
  have hF2 : (fun q : K × WO S T => om (g, 1) (om (1, (q.1 : GA D T)) φ) q.2) =
      fun q => om (g, (q.1 : GA D T)) φ q.2 := by
    funext q; rw [weilRepUnitaryPair_left_apply_right]
  have key := GlobalTheory.CommIntBdd.om_integral_comm_bdd D ψ S T χS χT om hW K ν
    (fun k : K => om (1, (k : GA D T)) φ) (g, 1)
    (fun k => hW.om_pres _ φ hφ)
    (hc.comp ((continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).prodMk continuous_snd))
    ⟨C1, fun k y => hC1 (1, (k : GA D T)) ⟨Set.mem_singleton _, k.2⟩ y⟩
    (by rw [hF2]; exact hc.comp ((continuous_const.prodMk (continuous_subtype_val.comp continuous_fst)).prodMk
      continuous_snd))
    ⟨C2, fun k y => by rw [weilRepUnitaryPair_left_apply_right]; exact hC2 (g, (k : GA D T)) ⟨Set.mem_singleton _, k.2⟩ y⟩
    hP x
  refine Eq.trans ?_ key.symm
  show ∫ k, om (1, (k : GA D T)) (om (g, 1) φ) x ∂ν = ∫ k, om (g, 1) (om (1, (k : GA D T)) φ) x ∂ν
  simp only [weilRepUnitaryPair_left_apply_right, weilRepUnitaryPair_right_apply_left]

theorem main (D : D7) (A : HSp D) (t : ℕ) (B W : HSp D) (d : HypDec B W t) (ψ : AddChar (AF D.host.F) ℂ)
    (hψ : IsCharAF D.host.F ψ) (χ : (AE D)ˣ →* Circle) (hχ : IsHeckeChar D χ) (hη : ResEta D χ W.rank) (hηB : ResEta D χ B.rank)
    (θ : InfFam D) (hθ : IsInfFam θ) (μB : Measure (Mx D B.rank A.rank)) (μW : Measure (Mx D W.rank A.rank)) 𝓕B 𝓕W
    (hμB : IsCovolOne (ratMx D B.rank A.rank) μB 𝓕B) (hμW : IsCovolOne (ratMx D W.rank A.rank) μW 𝓕W)
    (ωB : G D A.rank →* Module.End ℂ (schwartzA θ B.rank A.rank)) (ωW : G D A.rank →* Module.End ℂ (schwartzA θ W.rank A.rank))
    (hB : IsWeilSch ψ χ θ B μB ωB) (hW : IsWeilSch ψ χ θ W μW ωW) (I : IkD d A.rank) (Φ : schwartzA θ B.rank A.rank)
    (Ψ : schwartzA θ W.rank A.rank) (hΨ : Ψ.1 = ikp I Φ.1) (g : G D A.rank) : (ωW g Ψ).1 = ikp I (ωB g Φ).1 := by
  obtain ⟨ψ₀, μ', lam, κ, omB, h₀, hsk, hl, rfl, hκ, homB, hTB⟩ :=
    GlobalTheory.StdUnn.SchDatum.exists_datum D A B ψ hψ χ hχ hηB θ hθ μB 𝓕B hμB ωB hB
  obtain ⟨hχi, hri⟩ := GlobalTheory.StdUnn.isHeckeChar_resEta_inv D χ W.rank hχ hη
  have hr1 : ResEta D 1 (dblSp A).rank := by
    have := GlobalTheory.Eis.SimplePoleModel.resEta_one_two_mul D A.rank
    convert this using 2
    simp [GlobalTheory.Doubling.dblSp]
    omega
  obtain ⟨omW, homW⟩ := GlobalTheory.weilRepresentationUnitaryPair D ψ₀ (dblSp A) W 1 χ⁻¹ h₀
    ⟨continuous_const, fun _ => rfl⟩ hχi hr1 hri
  obtain ⟨omS, hS⟩ := GlobalTheory.StdUnn.exists_transport_std D ψ₀ A W χ⁻¹ omW homW μW 𝓕W hμW θ hθ κ
  have hWS : IsWeilSch (shift ψ₀ lam) χ θ W μW omS := by
    refine ⟨?_, ?_, ?_⟩
    · intro g a hg Φ x
      have := GlobalTheory.StdUnn.transport_levi D ψ₀ A W χ⁻¹ omW homW μW 𝓕W hμW θ hθ μ' hsk κ hκ omS hS lam hl g a hg Φ x
      rw [inv_inv] at this
      exact this
    · intro g b hg Φ x
      exact GlobalTheory.StdUnn.Unip.transport_unip D ψ₀ A W χ⁻¹ omW homW μW 𝓕W hμW θ hθ μ' hsk κ hκ omS hS lam hl g b hg Φ x
    · intro g hg Φ x
      exact GlobalTheory.StdUnn.WeylStd.main D ψ₀ A W χ⁻¹ omW homW μW 𝓕W hμW θ hθ μ' hsk κ hκ omS hS lam hl g hg Φ x
  obtain rfl := GlobalTheory.SiegelWeilLitCompare.isWeilSch_unique hW hWS
  obtain ⟨g, rfl⟩ := κ.surjective g
  obtain ⟨f, hf, hfΦ⟩ := (GlobalTheory.T.schrodingerTheta_eq_schwartzBruhat D ψ₀ h₀ θ hθ A B μB 𝓕B hμB).2.1 Φ.1 Φ.2
  obtain ⟨μ₁, 𝓕₁, hμ₁⟩ := GlobalTheory.MixModel.exists_isCovolOne D t (dblSp A).rank
  obtain ⟨𝓕₂, hμ₂⟩ := I.cov₁
  have hK := LIkSch.isCompact_K d I.good
  have := I.probK
  have hP := GlobalTheory.T.compactAverageProjection_theta_schrodinger D ψ₀ A B χ⁻¹ omB homB μB 𝓕B hμB I.l.K hK I.νK I.probK
  have hI := GlobalTheory.T.ikedaMap_schrodinger_partialIntegral D ψ₀ h₀ A B W t d μB 𝓕B hμB μW 𝓕W hμW μ₁ 𝓕₁ hμ₁ I.μ₁ 𝓕₂ hμ₂
  have hgf := homB.om_pres (g, 1) f hf
  have e1 : ∀ φ, IsThetaFunO ψ₀ (dblSp A) B φ →
      ikp I (GlobalTheory.Core.Rk.SW.sch ψ₀ A B μB 𝓕B φ) = GlobalTheory.Core.Rk.SW.sch ψ₀ A W μW 𝓕W (ikeda ψ₀ d μ₁ 𝓕₁ (projK omB I.νK φ)) := fun φ hφ => by
    rw [(hI _ (hP φ hφ).1).2, (hP φ hφ).2]; rfl
  have hmix := (GlobalTheory.T.mixedModelFormulas_wittTarget D ψ₀ (dblSp A) B W t d 1 χ⁻¹ omB omW homB homW μ₁ 𝓕₁ hμ₁ _ (hP f hf).1).source g 0
  rw [Matrix.mul_zero] at hmix
  rw [hTB g f hf Φ hfΦ.symm, e1 _ hgf, projK_comm homB _ hK I.νK f hf (hP f hf).1 g,
    hS g _ (hI _ (hP f hf).1).1 Ψ (by rw [hΨ, ← hfΦ, e1 f hf])]
  exact congrArg _ hmix.symm

end PositivityTheory.Rg.Rsw.L.LIkEq2

theorem PositivityTheory.Rg.Rsw.L.ikEq2 : PositivityTheory.Rg.Rsw.L.IkEq := by
  intro D n t B W d hn ψ χ θ μB μW ωB ωW hS I Φ Ψ hΨ g
  obtain ⟨𝓕B, hB⟩ := hS.hμB
  obtain ⟨𝓕W, hW⟩ := hS.hμW
  have hηB : ResEta D χ B.rank := Formalism.L2.Theta.resEta_parity hS.hη (by rw [← d.rank_add]; omega)
  exact PositivityTheory.Rg.Rsw.L.LIkEq2.main D (Formalism.BasicNotions.Examples₂.posSpace (E := D.host.E) Formalism.BasicNotions.Examples₂.star_isIntegral n) t B W d ψ hS.hψ χ hS.hχ
    hS.hη hηB θ hS.hθ μB μW 𝓕B 𝓕W hB hW ωB ωW hS.hB hS.hW I Φ Ψ hΨ g

end
