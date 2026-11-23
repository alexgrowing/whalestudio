import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.MeanLogLeOfBounds
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerDatumAndHalfLevels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexificationBaseChangeLinearOneTmul
import Development.AbelianVarietyTheory.Definitions.Divisors.EigLatLe
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActCCoe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemSmulTopOfLevel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowWeightGramAlgebraic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinalRowGramAlgebraicSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FamPSizesRecord
set_option synthInstance.maxHeartbeats 400000

noncomputable section

section Point

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.DefPt GlobalTheory.FlatLine
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix Formalism.L2.Theta Formalism.IndefR
open scoped TensorProduct

namespace GlobalTheory.NeatOne

set_option maxHeartbeats 1000000 in

theorem eq_one_of_lev_cong {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (g : p.P.Gp)
    (hg : ∀ x : (p.T.Q.Dw ((i : ℕ) + 1)).La, (p.O i).lev g x - x ∈ p.T.Q.l.Mb • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La)) :
    g = 1 := by
  obtain ⟨κ, hlift, happ⟩ := (p.pins i).2.lift.lev g
  have hβ := p.charW.base.lev.βW i
  have hSt := Formalism.L2.DIV.parLev_St hlift.2.1
  have hfc := GlobalTheory.LevelAction.finCong_of_mem_St hβ hSt
  have hι := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hMb : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ p.T.Q.l.Mb := by
    have h0 : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := Ideal.mem_span_singleton_self _
    rw [← p.T.Q.l.prod] at h0
    exact (Ideal.mul_le_inf.trans inf_le_left : p.T.Q.l.Mb * _ ≤ p.T.Q.l.Mb) h0
  have h4 := GlobalTheory.T.levelMove_lift_congruent_mod_ideal (Wc D i) (iotaW p.T i) hι p.T.Q.l.M p.T.Q.l.Mb (Mfr p.T.Q.l) p.T.Q.l.coprime hMb κ hfc
    ((p.O i).lev g) happ hg
  have h3 := GlobalTheory.T.adelicCongruence_selfDual_of_principalLattice (Wc D i) _ _ h4
  rw [← GlobalTheory.PrincInLevel.eq_latC hβ] at h3
  have h2 := GlobalTheory.BaseLevelInj.hatL_cong_of_hat (Wc D i) κ _ _ h3
  have hfr : Formalism.L2.DIV.IsFrame (p.R.βW i) (p.R.ΛW i) := by obtain ⟨c, h, -⟩ := hβ; exact h
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hred : ∀ PP ∈ p.R.Pg, Formalism.L2.DIV.redFn (p.R.βW i) PP (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    intro PP hP
    refine GlobalTheory.T.frameReduction_eq_one_of_congruent_mod_ideal _ _ _ hfr hSt _ h2 PP ?_
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  have hT1 : Formalism.L2.DIV.rTup (p.R.βW i) (p.R.datWp i p.R.triv) (Formalism.IndefR.Lev.finE (Wc D i) κ) = 1 := by
    funext PP
    show Formalism.L2.DIV.upperLeftBlock _ (Formalism.L2.DIV.redFn (p.R.βW i) PP.1 _) = 1
    rw [hred PP.1 PP.2]; exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _
  have he : p.R.eG g = 1 := by rw [← hlift.2.2]; exact hT1
  rw [← map_one p.R.eG] at he; exact p.R.eG.injective he

open Classical in

theorem exists_cofactor {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (P : Pl D.host.E) (hP : P ∈ p.R.Pg) :
    ∃ J : Ideal (𝓞 D.host.E), J ≤ Mfr p.T.Q.l ∧ P.asIdeal ⊔ J = ⊤ ∧
      P.asIdeal * J = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} ∧ p.T.Q.l.Mb ≤ P.asIdeal := by
  have hhalf := ((p.pins i).2.tuple ()).half.1
  have hp : p.T.Q.l.Mb * Mfr p.T.Q.l = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := p.T.Q.l.prod
  have hc : p.T.Q.l.Mb ⊔ Mfr p.T.Q.l = ⊤ := p.T.Q.l.coprime
  have hle : p.T.Q.l.Mb ≤ P.asIdeal := by
    rw [hhalf]
    exact Ideal.prod_le_inf.trans (Finset.inf_le hP)
  refine ⟨(∏ Q ∈ p.R.Pg.erase P, Q.asIdeal) * Mfr p.T.Q.l, Ideal.mul_le_inf.trans inf_le_right, ?_, ?_, hle⟩
  · rw [← Ideal.isCoprime_iff_sup_eq]
    refine IsCoprime.mul_right (IsCoprime.prod_right fun Q hQ => ?_) ?_
    · rw [Ideal.isCoprime_iff_sup_eq]
      exact Ideal.IsMaximal.coprime_of_ne P.isMaximal Q.isMaximal
        (fun e => (Finset.ne_of_mem_erase hQ) (HeightOneSpectrum.ext e).symm)
    · rw [Ideal.isCoprime_iff_sup_eq]
      exact top_le_iff.1 (hc ▸ sup_le_sup_right hle _)
  · rw [← mul_assoc, Finset.mul_prod_erase p.R.Pg (fun Q => Q.asIdeal) hP, ← hp, hhalf]

open GlobalTheory.LevelUnip in

theorem unip_mod_place {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m) (g : p.P.Gp) (P : Pl D.host.E) (hP : P ∈ p.R.Pg)
    (hU : p.R.eG g ⟨P, hP⟩ ∈ unip (kP P) D.R.r) (z : (p.T.Q.Dw ((i : ℕ) + 1)).La) :
    (((p.O i).lev g - 1) ^ D.R.r) z ∈ P.asIdeal • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La) := by
  obtain ⟨κ, hk, hf⟩ := (p.pins i).2.lift.lev g
  have hB := p.charW.base
  have hL := hB.lev
  obtain ⟨J, hJ, hc, hp, hMb⟩ := exists_cofactor p i P hP
  have hemb := GlobalTheory.LevelAction.latEmb_iotaW p.T p.fw.laws i
  have hβ := hL.βW i
  have hr := rank_Wc (D := D) i
  have hkSt := parLev_St hk.2.1
  have hred : ∀ P' ∈ ({P} : Finset (Pl D.host.E)), (((redFn (p.R.βW i) P' (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P')) :
      Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P')) - 1) ^ D.R.r = 0 := by
    intro P' hP'
    obtain rfl : P = P' := (Finset.mem_singleton.1 hP').symm
    have hb := blockTri_blkOf_le _ _ (parLev_g hk.2.1 hP)
    have e : upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) = p.R.eG g ⟨P, hP⟩ :=
      congrFun hk.2.2 ⟨P, hP⟩
    rw [← e] at hU
    have hv := upper_block_val_submatrix (p.R.datWp i p.R.triv).hr hb
    have hent : ∀ a c : Fin (Wc D i).rank,
        ((upperLeftBlock (p.R.datWp i p.R.triv).hr (redFn (p.R.βW i) P (Lev.finE (Wc D i) κ)) : GL (Fin D.R.r) (kP P)) :
          Matrix (Fin D.R.r) (Fin D.R.r) (kP P)) (Fin.cast hr a) (Fin.cast hr c) =
        ((redFn (p.R.βW i) P (Lev.finE (Wc D i) κ) : GL (Fin (Wc D i).rank) (kP P)) :
          Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (kP P)) a c := by
      intro a c
      exact (congrFun (congrFun hv (Fin.cast hr a)) (Fin.cast hr c)).trans rfl
    rw [← hr]
    apply sub_one_pow_eq_zero'
    · intro a c hca
      rw [← hent]
      exact hU.1 (show ((Fin.cast hr c : Fin D.R.r) : ℕ) < (Fin.cast hr a : Fin D.R.r) from hca)
    · intro a
      rw [← hent]
      exact hU.2 _
  have hp' : (∏ P' ∈ ({P} : Finset (Pl D.host.E)), P'.asIdeal) * J = Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := by
    rw [Finset.prod_singleton]; exact hp
  have hI : ((p.T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal :=
    (hp.ge.trans (Ideal.mul_le_inf.trans inf_le_left)) (Ideal.mem_span_singleton_self _)
  have hcong := fun b (hb : b ∈ J) => exists_pow_cong hβ {P} hp' hkSt hred hb
  have hpow := approx_pow hemb (sub_one_mulVec_mem hβ hkSt) (J := J)
    (fun a ha => hf a (Submodule.smul_mono_left hJ ha)) D.R.r
  have h0 : ∀ a ∈ J • (⊤ : Submodule (𝓞 D.host.E) (p.T.Q.Dw ((i : ℕ) + 1)).La),
      ∃ w ∈ latGHat (Wc D i) 1, finVec (Wc D i) (iotaW p.T i ((0 : (p.T.Q.Dw ((i : ℕ) + 1)).La →ₗ[𝓞 D.host.E] _) a)) -
        (0 : Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ
          finVec (Wc D i) (iotaW p.T i a) = p.T.Q.l.M • w := by
    intro a _
    refine ⟨0, zero_mem _, ?_⟩
    funext j
    simp [finVec]
  have := GlobalTheory.LevelUnique.sub_mem_of_approx hemb (lt_of_lt_of_le (by norm_num) p.T.Q.l.three_le) hI hc hcong hpow h0 z
  simpa using this

theorem free_half {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
    {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)
    (hr : ∀ k, D.R.r + 1 < D.host.g k) (k : Fin 2) :
    FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH D k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g D.nd))) := by
  have hM : p.T.Q.l.M = D.host.g 0 * D.host.g 1 := p.fw.laws.pins.2.1.1
  obtain ⟨k', hk'⟩ := exists_ne k
  have hf : 0 < D.R.f := by
    have hn : 0 < D.R.ord := D.R.ord_pos
    show 0 < 2 * D.R.ord
    omega
  obtain ⟨v⟩ : Nonempty (D.nd.PlG k') := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k']; exact hf
  obtain ⟨plg, iso, hplg, -, -, hG⟩ := p.grpRecPin
  obtain ⟨J, -, hc, hp, hMb⟩ := exists_cofactor p i (plg ⟨k', v⟩).1 (plg ⟨k', v⟩).2
  obtain ⟨u, hu, s, hs, hus⟩ := Submodule.mem_sup.1 (hc ▸ Submodule.mem_top : (1 : 𝓞 D.host.E) ∈ (plg ⟨k', v⟩).1.asIdeal ⊔ J)
  have hgI : ((D.host.g k' : ℕ) : 𝓞 D.host.E) ∈ (plg ⟨k', v⟩).1.asIdeal := by
    rw [hplg]; exact D.naut.plGw_over k' v
  have hdvd : D.host.g k' ∣ p.T.Q.l.M := by
    rw [hM]
    fin_cases k'
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
  refine free_of_unip_one D.host.E p.T.Q.H (p.T.Q.Dw ((i : ℕ) + 1)) p.T.Q.l (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
    (GlobalTheory.BadCount.Inh.halfH D k) (fun h => (p.O i).lev ((p.R.eG.trans p.cG).symm (h : G0g D.nd))) D.R.r (D.host.g k')
    (plg ⟨k', v⟩).1.asIdeal s (D.host.g_prime k') (plg ⟨k', v⟩).1.isPrime.ne_top hgI (hr k')
    (by rw [← hus, add_sub_cancel_right]; exact hu) ?_ hMb ?_ ?_
  · intro a ha
    have h1 : a * s ∈ Ideal.span {((p.T.Q.l.M : ℕ) : 𝓞 D.host.E)} := hp ▸ Ideal.mul_mem_mul ha hs
    rw [mul_comm]
    exact (Nat.cast_dvd_cast hdvd).trans (Ideal.mem_span_singleton.1 h1)
  · intro h x
    refine unip_mod_place p i _ _ (plg ⟨k', v⟩).2 ?_ x
    have hU := GlobalTheory.BadCount.Inh.isHalf_halfH D k (h : G0g D.nd)
    have hU' : Formalism.MainNotions.ArithmeticCylinders.IsUniUp (((h : G0g D.nd) ⟨k', v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k'))) :=
      (Subgroup.mem_pi _).1 h.2 ⟨k', v⟩ hk'
    have e := hG ((p.R.eG.trans p.cG).symm (h : G0g D.nd)) ⟨k', v⟩
    rw [MulEquiv.apply_symm_apply] at e
    have e' : p.R.eG ((p.R.eG.trans p.cG).symm (h : G0g D.nd)) ⟨(plg ⟨k', v⟩).1, (plg ⟨k', v⟩).2⟩ = _ := e
    rw [e']
    refine ⟨fun a b hab => ?_, fun a => ?_⟩
    · show iso ⟨k', v⟩ ((((h : G0g D.nd) ⟨k', v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k'))) a b) = 0
      rw [(hU' a b).1 hab, map_zero]
    · show iso ⟨k', v⟩ ((((h : G0g D.nd) ⟨k', v⟩ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (ZMod (D.host.g k'))) a a) = 1
      rw [(hU' a a).2 rfl, map_one]
  · intro h hh
    have := eq_one_of_lev_cong p i _ hh
    exact Subtype.ext ((MulEquiv.map_eq_one_iff _).1 this)

end GlobalTheory.NeatOne

end Point

section Family

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open Formalism.IndefR.FWT

namespace GlobalTheory.NeatOne

theorem rank_add_one_lt {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (x : ℝ) (hx : Fm.x1 < x) (ι : Fm.Ix x) (PP C : ℝ)
    (hN : HostNum (Fm.D x ι) (Fm.L x ι) PP C 6) : ∀ k, (Fm.D x ι).R.r + 1 < (Fm.D x ι).host.g k := by
  have hL10 : 10 ≤ (Fm.L x ι).sc.L := hN.big.2.1
  have hx1 := (Fm.L x ι).sc.one_lt_alt
  have he0 := (Fm.L x ι).sc.eps_pos
  have he1 := (Fm.L x ι).sc.eps_lt

  have hx16 : (16 : ℝ) ≤ (Fm.L x ι).sc.x := by
    have h1 : (Fm.L x ι).sc.L ≤ (Fm.L x ι).sc.x ^ ((1 : ℝ) / 52) :=
      Real.rpow_le_rpow_of_exponent_le hx1.le he1.le
    have h2 : ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) = (Fm.L x ι).sc.x := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have h3 : (10 : ℝ) ^ (52 : ℕ) ≤ ((Fm.L x ι).sc.x ^ ((1 : ℝ) / 52)) ^ (52 : ℕ) :=
      pow_le_pow_left₀ (by norm_num) (hL10.trans h1) _
    rw [h2] at h3
    linarith [show (16 : ℝ) ≤ 10 ^ (52 : ℕ) by norm_num]
  have hrec := fun j => GlobalTheory.sizes_record_at (Fm.L x ι) (Fm.sizes x hx ι) 5 (by norm_num) hx16 j
  obtain ⟨-, -, -, -, h100, hr5, -⟩ := hrec 0
  have hg : ∀ k, Real.exp (8 * (Fm.L x ι).sc.L) ≤ ((Fm.D x ι).host.g k : ℝ) := fun k => by
    have := (hrec k).1; unfold Formalism.BasicNotions.Scale.L; exact this
  intro k
  have hA := hN.poly.1
  have hxA : (Fm.L x ι).sc.x ≤ (Fm.L x ι).sc.x ^ C := by
    calc (Fm.L x ι).sc.x = (Fm.L x ι).sc.x ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (Fm.L x ι).sc.x ^ C := Real.rpow_le_rpow_of_exponent_le hx1.le hA
  have hroom : ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) ≤ (Fm.L x ι).sc.b := by
    have := hN.room
    rwa [show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have h6 : (Fm.L x ι).sc.x ^ (6 : ℕ) ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := pow_le_pow_left₀ (by linarith) hxA 6
  have h5 : (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 < (Fm.L x ι).sc.x ^ (6 : ℕ) := by
    have h1 : (1 : ℝ) ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) := one_le_pow₀ (by linarith)
    have h2 := mul_le_mul_of_nonneg_right hx16 (zero_le_one.trans h1)
    have e : (Fm.L x ι).sc.x ^ (6 : ℕ) = (Fm.L x ι).sc.x * (Fm.L x ι).sc.x ^ (5 : ℕ) := by ring
    rw [e]
    linarith
  have hb : (Fm.L x ι).sc.b ≤ Real.exp (8 * (Fm.L x ι).sc.L) := by
    unfold Formalism.BasicNotions.Scale.b; exact Real.exp_le_exp.2 (by linarith)
  have hr5' : ((Fm.D x ι).R.r : ℝ) ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) := by
    have e : (Fm.L x ι).sc.x ^ (5 : ℕ) = (Fm.L x ι).sc.x ^ (5 : ℝ) := by exact_mod_cast (Real.rpow_natCast _ 5).symm
    first | exact hr5 | (rw [e]; exact hr5)
  have : ((Fm.D x ι).R.r : ℝ) + 1 < (Fm.D x ι).host.g k :=
    calc ((Fm.D x ι).R.r : ℝ) + 1 ≤ (Fm.L x ι).sc.x ^ (5 : ℕ) + 1 := add_le_add hr5' le_rfl
      _ < (Fm.L x ι).sc.x ^ (6 : ℕ) := h5
      _ ≤ ((Fm.L x ι).sc.x ^ C) ^ (6 : ℕ) := h6
      _ ≤ (Fm.L x ι).sc.b := hroom
      _ ≤ Real.exp (8 * (Fm.L x ι).sc.L) := hb
      _ ≤ (Fm.D x ι).host.g k := hg k
  exact_mod_cast this

theorem free_half_lifts : Hypotheses2 → Gram → Lifts fun Fm x _ ι p i _ _ => (i : ℕ) + 1 = (Fm.D x ι).R.m → ∀ k : Fin 2,
    GlobalTheory.DefPt.FreePt (p.T.Q.Xo ((i : ℕ) + 1)) p.T.Q.c
      (fun h : GlobalTheory.BadCount.Inh.halfH (Fm.D x ι) k => (p.O i).lev2 ((p.R.eG.trans p.cG).symm (h : G0g (Fm.D x ι).nd))) := by
  intro _ _
  refine Formalism.MainNotions.Closed.imp (GlobalTheory.CovTop.Sizes.hostN 6) fun Fm CH _ hh => ?_
  obtain ⟨C, hC, a, ha⟩ := hh
  exact ⟨C, hC, a, fun x hx hle ι p hp i _ k => free_half p i (rank_add_one_lt Fm x hx ι _ C (ha x hx hle ι p hp i)) k⟩

end GlobalTheory.NeatOne

end Family

end
