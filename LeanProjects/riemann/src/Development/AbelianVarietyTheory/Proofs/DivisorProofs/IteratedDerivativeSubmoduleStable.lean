import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullHeckeRealDatMovedReadings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHypothesisInHalfGeometryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdelicFormEqRationalPhaseKernelSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitModulusRationalPhaseMemCoefficientFieldStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem eq_zero_of_cuspA_bot {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} (fw : FWTie T R κ v₀) (j : Fin D.R.m)
    (hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥) (x : Fin (R.nW j) → D.what₂.LL) : x = 0 := by
  obtain ⟨n, b, hb, -, -, -, hsp⟩ := fw.ks j
  have hWK : ∀ z ∈ (R.FW j).WK, z = 0 := fun z hz => by
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨z, hz⟩
    have hf0 : f = 0 := by
      have h1 : (f : T.R ((j : ℕ) + 1)) ∈ (⊥ : Submodule T.Q.c.F (T.R ((j : ℕ) + 1))) := hc ▸ f.2
      exact Subtype.ext ((Submodule.mem_bot _).1 h1)
    have := congrArg Subtype.val hf
    rw [hf0, map_zero] at this
    exact this.symm
  have h0 : Set.range b ⊆ {0} := by
    rintro _ ⟨k, rfl⟩; exact hWK _ (hb k)
  have : x ∈ Submodule.span D.what₂.LL (Set.range b) := by rw [hsp]; trivial
  have h2 := Submodule.span_mono h0 this
  simpa using h2

theorem adForm_smul {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
    (c : D.what₂.LL) (x : Fin (R.nW i) → D.what₂.LL) : adForm R i (c • x) = sg0 D A c • adForm R i x := by
  unfold adForm
  rw [LinearMap.map_smulₛₗ, map_smul]

theorem adForm_zero {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) :
    adForm R i 0 = 0 := by
  unfold adForm
  rw [map_zero, map_zero]

theorem kerRat_framed (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hR : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type}
    {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m} {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A}
    {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)} {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {t : D.ntw.Tw} {j : Fin D.R.m}
    {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hH : RatHyp T Rl F κ v₀ O t j hV) (hph : ∀ k, Rl.phs k = 1)
    (v : HeightOneSpectrum (𝓞 D.what₂.LL)) {χ ξR ω φ}
    (hK : KerDat Rl.toRealDat j (Rl.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)) χ ξR (placesOver Rl.toRealDat (Rl.mu v) (ownAt D v)) ω φ)
    {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {y : (Rl.cV j).W} (hy : InCoefLat Rl.toRealDat j h y)
    (u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ) (hu : ∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) :
    ∃ x, adForm Rl.toRealDat j x (fun τ => u τ) = singleSeries Rl.toRealDat j ω φ h y u := by
  obtain ⟨gramR, c0R, c0L, hFT, P, hPm, rfl⟩ := hy
  obtain ⟨ph, hph1, hphC⟩ := hS D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hH.laws hH.core.lev hH.core.grp hH.core.fam
    hH.core.models hH.core.thP hH.tieIn j hV hH.frame hH.std gramR c0R c0L hFT u hu
  have hRP : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph := fun C hC _ => hphC C hC
  obtain ⟨x, hx⟩ := GlobalTheory.T.exists_adelicForm_eq_rationalPhase_kernelSeries hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu ph hRP v χ ξR ω φ hK
    h hh P hPm
  have hph0 : ph ≠ 0 := fun e => by rw [e, norm_zero] at hph1; exact zero_ne_one hph1
  by_cases hc : T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine ⟨0, ?_⟩
    rw [eq_zero_of_cuspA_bot hH.fw.some j hc x, adForm_zero] at hx
    rw [adForm_zero]
    funext g
    have e := congrFun hx.symm g
    have e2 : ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g = 0 := e
    exact ((mul_eq_zero.1 e2).resolve_left hph0).symm
  · obtain ⟨c, hcph⟩ := GlobalTheory.T.unit_modulus_rational_phase_mem_coefficient_field hP hA hR D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O t j hV hH gramR c0R c0L hFT u hu hph hc ph
      hph1 hRP
    refine ⟨c⁻¹ • x, ?_⟩
    rw [adForm_smul]
    funext g
    have e := congrFun hx g
    have e2 : adForm Rl.toRealDat j x (fun τ => u τ) g = ph * singleSeries Rl.toRealDat j ω φ h (c0L j P) u g := e
    show sg0 D A3.A c⁻¹ * adForm Rl.toRealDat j x (fun τ => u τ) g = _
    rw [e2, map_inv₀, hcph, ← mul_assoc, inv_mul_cancel₀ hph0, one_mul]

open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt in

theorem kerRatAt : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → KerRatAt := by
  intro hP hA hR hS
  refine (lowAt_holds.and twAdm).imp fun Fm x hx i p hp hM w hw j hLT => ?_
  obtain ⟨l1, l2⟩ := hLT
  have h0 := GlobalTheory.T.bad_prime_mem_exceptional_set Fm x hx i p hp hM _ l2.2.2 l1 j
  obtain ⟨c', w', hw', hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (GlobalTheory.T.rational_hypothesis_in_half_geometry hP Fm x hx i p hp hM _ j h0)
  obtain ⟨S', YS', -⟩ := GlobalTheory.T.seriesRationality_back_from_movedReadings p.R p.cG p.Sx p.nexp w' hw'
  letI iA : Algebra (setCE p.T c').Q.c.F (Fm.D x i).what₂.LL := p.alg
  have hV' : (setCE p.T c').V ((j : ℕ) + 1) (setCE p.T c').σ₀ = Wc (Fm.D x i) j :=
    B'.fw.laws.spaceW _ ⟨Nat.le_add_left _ _, j.2⟩ _ (setCE p.T c').toCore.good_σ₀
  have hU' : (fullHeckeRealDatMovedReadings p.R w').toRealDat.LUnif := GlobalTheory.T.uniformisationLaws_centralMovedReadings p.R.toRealDat w' hw' h0.unif
  have hG : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsGrp (F2 p) :=
    ⟨h0.core.grp.red_R, h0.core.grp.red_L, h0.core.grp.levels, h0.core.grp.record, h0.core.grp.chiW⟩
  have c := h0.core
  have hF : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsFam := { c.fam with }
  have hMo : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsModels := { c.models with }
  have hCh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsChain := { c.chain with }
  have hTh : (fullHeckeRealDatMovedReadings p.R w').toRealDat.IsThP := { c.thP with }
  have hC : GlobalTheory.Hk3.Core (fullHeckeRealDatMovedReadings p.R w').toRealDat (F2 p) := ⟨c.lev, hG, hF, hMo, hCh, hTh⟩
  have hph : (fun k => cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) ((fullHeckeRealDatMovedReadings p.R w').phs k)) = fun _ => (1 : ℂ) :=
    funext fun k => by
      show cj (twAt (Fm.D x i).what₂.embLL p.P.A3.A.v0) (p.R.phs k) = 1
      rw [p.phsOne k, map_one]
  have hRat : RatHyp (setCE p.T c') (fullHeckeRealDatMovedReadings p.R w') (F2 p) B'.κ B'.v₀ B'.O ((Fm.ex x hx i).nch.twI w) j hV' := by
    refine ⟨h0.size, h0.host, h0.std, B'.fw.laws, hC, hU', ⟨B'.fw⟩,
      ⟨B'.fw.laws, B'.fw.alg_eq, B'.fw.kap, B'.fw.hv₀, B'.fw.chiR, B'.fw.x0⟩, h0.io, h0.guard, h0.fin, B'.pins j, ?_,
      hfr j hV', h0.galois, h0.small, h0.inUse, h0.low⟩
    rw [hph]
    exact B'.phase j hU'
  intro χ ξR ω φ hK h hh y hy u hu
  have hK' : KerDat (fullHeckeRealDatMovedReadings p.R w').toRealDat j ((fullHeckeRealDatMovedReadings p.R w').C.delAt (Formalism.EigenvalueLevelCeiling.plc ((Fm.D x i).plEq w))) χ ξR
      (placesOver (fullHeckeRealDatMovedReadings p.R w').toRealDat ((fullHeckeRealDatMovedReadings p.R w').mu ((Fm.D x i).plEq w)) (ownAt (Fm.D x i) ((Fm.D x i).plEq w)))
      ω φ := ⟨hK.chr, hK.fin, hK.triv, hK.tame, hK.pl, hK.off, hK.ram, hK.res, hK.weil, hK.vec⟩
  have hy' : InCoefLat (fullHeckeRealDatMovedReadings p.R w').toRealDat j h y := hy
  obtain ⟨x', hx'⟩ := kerRat_framed (T := setCE p.T c') hP hA hR hS YS' hRat (fun k => p.phsOne k) ((Fm.D x i).plEq w) hK' hh
    hy' u (by rw [hv]; exact hu)
  exact ⟨(p.R.FW j).ρ (w' j (sg0 _ p.P.A3.A)) x', hx'⟩

end GlobalTheory.BigOn.Exp.SerBase
