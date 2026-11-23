import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhaseScaleThetaConj
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RowAtOfRatStep
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LowAtHolds
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TwAdm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.RatHyp0AtPoint
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.InGeoGeoHalf

set_option synthInstance.maxHeartbeats 200000

section
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
section CorePart
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open GlobalTheory.SeriesTie GlobalTheory.SeriesTie.BaseRat GlobalTheory.BigOn.Exp
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
namespace GlobalTheory.SerSmall
variable {D : D7}
section Comb
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
  (j : Fin D.R.m)
variable {YS v₀ j}
end Comb
section Main
variable {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
  {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
  {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
end Main
end GlobalTheory.SerSmall
end CorePart
section PointPart
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
namespace GlobalTheory.SerSmall
section Core
variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}
end Core
section Level
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz}
end Level
open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt
set_option maxHeartbeats 3200000 in
theorem fw_eq_zero_or_exists_norm_algComb (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.PointConditions')
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ)
    (hχ : ∀ q, (((ρ.B t j b).G.P.chi q : ℂˣ) : ℂ) ∈ (Formalism.L2.Host.embLL0 (Fm.D x i)).fieldRange) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → SmallComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (_root_.GlobalTheory.UnframePt.inGeo_geoHalf_of_ratHyp0 hP Fm x hx i p hR hM t j h0)
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w).toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w hw h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w).toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w).toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w).phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w) (F2 p) B'.κ B'.v₀ B'.O t j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  have hpin' : RealPin (fullHeckeRealDatMovedReadings p.R w) p.cG ρ :=
    ⟨h.psi, h.inf, h.cartT, h.onbS, h.onbT, h.latS, h.latT, h.frS, h.frT, h.vac, h.Pg, h.grp, h.mu0, h.eta, h.delta, h.deltaPl,
      h.ap, h.am⟩
  have hsp : (Fm.D x i).host.cls (Fm.D x i).host.pde = PrimeClass.splitK ∧
      (Fm.D x i).host.cls (Fm.D x i).host.pde' = PrimeClass.splitK :=
    ⟨(Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.1, (Fm.params x hx i).level_split _ (Fm.D x i).host.pde_level.2⟩
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp hχ
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => smallComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩
theorem norm_smul_theta_alt (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) : _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp → RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ ν' : ℂ, IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν' →
    ∃ (a : ℂ) (φ : GA (Fm.D x i) (Wc (Fm.D x i) j) → ℂ), (∃ m : ℕ, m ≠ 0 ∧ a ^ m = 1) ∧ SmallComb p.nexp p.v₀ j φ ∧
      ν' • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = a • φ := by
  have hL := _root_.GlobalTheory.BigOn.Exp.lowAt_holds_alt
  have hT := _root_.GlobalTheory.BigOn.Exp.twAdm_alt
  unfold _root_.GlobalTheory.BigOn.Exp.LowerBoundAtPlace at hL
  unfold _root_.GlobalTheory.BigOn.Exp.TwAdmAlt at hT
  refine (_root_.GlobalTheory.BigOn.Exp.TwistConditions.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hlev hR0 s g P hd hl ν' hN
  rcases _root_.GlobalTheory.SerSmall.fw_eq_zero_or_exists_norm_algComb hP hA hRF hS Fm x hx i p hp hM _ j
    (_root_.GlobalTheory.BigOn.Exp.ratHyp0_at_point_alt Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin (chi_mem_small hM.2.2 hρ hlev _ j _) with H | ⟨ν₁, hN₁, H⟩
  · have h0 := GlobalTheory.SerRefPt.theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    exact ⟨1, 0, ⟨1, one_ne_zero, one_pow 1⟩, SmallComb.zero, by rw [h0, smul_zero, smul_zero]⟩
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    exact ⟨ζ, _, hζ, H s g P hd hl, by rw [e, mul_smul]⟩
theorem one_expansion_alt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.SerStd.SeriesRatS → _root_.GlobalTheory.BigOn.Exp.TwistConditions fun Fm x hx i p w j => ∀ (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (ν : ℂ),
  RealPin p.R p.cG ρ → ρ.LevelOf (Fm.D x i).nexp →
  IsNorm p.R p.v₀ (ρ.B ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w)) ν →
  RatBase (rdAt p w j hρ ν) →
  ∀ s h P, ρ.IsDatum ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) s h P →
    P ∈ ρ.lat ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) (smallInt (Fm.D x i)) h →
    ∀ τ : ℂ ≃+* ℂ, (∀ y, τ (Formalism.L2.Host.embLL0 (Fm.D x i) y) = Formalism.L2.Host.embLL0 (Fm.D x i) y) →
      ∃ c : ℂ, (∃ m : ℕ, m ≠ 0 ∧ c ^ m = 1) ∧
        ∃ (n : ℕ) (b : Fin n → ℂ) (g : Fin n → NX.FmK p.Sx ((j : ℕ) + 1)),
          ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P = ∑ k, b k • evW p.nexp p.v₀ j (g k).val ∧
          ∑ k, τ (b k) • evW p.nexp p.v₀ j (g k).val =
            c • (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) h P) := by
  intro hP hA hRF hS
  refine (_root_.GlobalTheory.SerSmall.norm_smul_theta_alt hP hA hRF hS).imp fun Fm x hx i p _ _ w _ j H => ?_
  intro ρ hρ ν hpin hlev hN hR0 s h P hd hl τ hτ
  obtain ⟨a, φ, ⟨m, hm, ha⟩, ⟨n, z, g, hz, rfl⟩, e⟩ := H ρ hρ ν hpin hlev hR0 s h P hd hl ν hN
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [zero_pow hm] at ha
    exact zero_ne_one ha
  have hz' : ∀ k, τ (z k) = z k := fun k => by
    obtain ⟨y, hy⟩ := hz k
    rw [← hy]
    exact hτ y
  refine ⟨τ a / a, ⟨m, hm, by rw [div_pow, ← map_pow, ha, map_one, div_one]⟩, n, fun k => a * z k, g, ?_, ?_⟩
  · rw [e, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => smul_smul _ _ _
  · rw [e, smul_smul, div_mul_cancel₀ _ ha0, Finset.smul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_mul, hz', smul_smul]
end GlobalTheory.SerSmall
end PointPart
end
end
