import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfPowEqOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfSmallInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalScalarNormalisedStandardFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPrimeMemExceptionalSet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiAtComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowWeightStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalHypothesisInHalfGeometry
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationLawsCentralMovedReadingsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeriesRationalityBackFromMovedReadings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaleRootOfPrint

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.SerRefCore
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SerRefPt

section Core

variable {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T0 : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m}

theorem exists_root_of_isNorm {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {ν ν' : ℂ}
    (hN : IsNorm Rl v₀ B ν) (hN' : IsNorm Rl v₀ B ν') : ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ ν' = ζ * ν := by
  obtain ⟨h0, c, hc, n, hn, hνn⟩ := hN
  obtain ⟨-, c', hc', m, hm, hν'm⟩ := hN'
  obtain ⟨k, hk, hkk⟩ := isScale_pow_eq Rl v₀ _ hc hc'
  have e1 : ν' ^ (n * m * k) = (ν' ^ m) ^ (n * k) := by rw [← pow_mul]; ring_nf
  have e2 : ν ^ (n * m * k) = (ν ^ n) ^ (m * k) := by rw [← pow_mul]; ring_nf
  have e3 : c' ^ (n * m * k) = c ^ (n * m * k) := by
    rw [show n * m * k = k * (n * m) by ring, pow_mul c', pow_mul c, hkk]
  have e4 : ν' ^ (n * m * k) = ν ^ (n * m * k) := by
    rw [e1, e2, hν'm, hνn, ← pow_mul, ← pow_mul, mul_pow, mul_pow,
      show m * (n * k) = n * m * k by ring, show n * (m * k) = n * m * k by ring, e3]
  refine ⟨ν' / ν, isAlgebraic_of_pow_eq_one (Nat.mul_ne_zero (Nat.mul_ne_zero hn hm) hk) ?_, (div_mul_cancel₀ ν' h0).symm⟩
  rw [div_pow, e4, div_self (pow_ne_zero _ h0)]

theorem theta_eq_zero {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw)
    (j : Fin D.R.m) (b : Bool) {ν : ℂ} (h0 : ∀ x ∈ (Rl.FW j).WK, x = 0) (hR : RatBase (realRd YS v₀ hρ i j b ν))
    {s : Finset (Pl D.host.E)} {h : GA D (Vc D j)} {P : PolF D (Wc D j).rank (Vc D j).rank} (hd : ρ.IsDatum i j b s h P) :
    ρ.theta i j b h P = 0 := by
  have hW : ∀ g : NX.FmK S ((j : ℕ) + 1), evW YS v₀ j g.val = 0 := fun g => by
    have h1 : (YS.fi j).e g.val = 0 := h0 _ (((YS.fi j).wk _).1 g.2)
    have h2 : g.val = 0 := (YS.fi j).e.injective (h1.trans (map_zero _).symm)
    rw [h2, map_zero]
  have hK : ∀ x, evK YS v₀ hρ i j b x = 0 := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => exact map_zero _
    | add x y hx hy => rw [map_add, hx, hy, add_zero]
    | tmul a g => rw [evK_tmul, hW, smul_zero]
  obtain ⟨f, hf⟩ := hR s h P hd
  rw [← hf]
  change ν⁻¹ • evK YS v₀ hρ i j b _ = 0
  exact (congrArg (ν⁻¹ • ·) (hK _)).trans (smul_zero _)

theorem algComb_of_moved {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {Rl : RealDat3 D A3 Ks}
    {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd} {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S)
    (w : Fin D.R.m → (D.what₂.LL →+* ℂ) → Γ) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (j : Fin D.R.m)
    {φ : GA D (Wc D j) → ℂ} (h : AlgComb (GlobalTheory.UnframeForms.movedYS YS w) v₀ j φ) : AlgComb YS v₀ j φ := by
  obtain ⟨n, z, g, hz, e⟩ := h
  refine ⟨n, z, fun k => (⟨(S.A ((j : ℕ) + 1)).ρ ((YS.fi j).eG.symm (w j (sg0 D A3.A)))
      (show ↥(S.A ((j : ℕ) + 1)).WK from g k).1,
    YS.rho _ (Nat.le_add_left _ _) j.2 _ _ (show ↥(S.A ((j : ℕ) + 1)).WK from g k).2⟩ : ↥(S.A ((j : ℕ) + 1)).WK), hz, ?_⟩
  rw [e]
  exact Finset.sum_congr rfl fun k _ => congrArg (z k • ·) (GlobalTheory.UnframeForms.evW_moved YS w v₀ j _)

theorem core_cases (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt) (hS : GlobalTheory.SerStd.SeriesRatS)
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {Rl : RealDat3 D A3 T.Q.c.F} {cG : G0 Rl.Pg D.R.r ≃* G0g D.nd}
    {S : NX.RatDat D.ntw} (YS : NX.NExpRealS Rl cG S) {F : Face D A3.A} {κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)}
    {v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec}
    {O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)} {ρ : Setup D.ntw} (hρ : ρ.Good) {i : D.ntw.Tw}
    {j : Fin D.R.m} (b : Bool) {hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j} (hpin : RealPin Rl cG ρ) (H : RatHyp T Rl F κ v₀ O i j hV)
    (hsp : D.host.cls D.host.pde = PrimeClass.splitK ∧ D.host.cls D.host.pde' = PrimeClass.splitK) :
    (∀ x ∈ (Rl.FW j).WK, x = 0) ∨ ∃ ν, IsNorm Rl v₀ (ρ.B i j b) ν ∧ ∀ s h P, ρ.IsDatum i j b s h P →
      P ∈ ρ.lat i j b (smallInt D) h → AlgComb YS v₀ j (ν • ρ.theta i j b h P) := by
  obtain ⟨fw⟩ := H.fw
  by_cases hc : T.toCore.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n = ⊥
  · refine Or.inl fun x hx => ?_
    obtain ⟨f, hf⟩ := (fw.e j).surjective ⟨x, hx⟩
    have h0 : f = 0 := Subtype.ext ((Submodule.eq_bot_iff _).1 hc f.1 f.2)
    rw [h0, map_zero] at hf
    exact (congrArg Subtype.val hf).symm
  · obtain ⟨ν, hN, hν⟩ := GlobalTheory.T.exists_rationalScalar_normalised_standardFrame hA hRF hS D Γ Pl0 I0 T0 A3 T Rl cG S YS F κ v₀ O ρ hρ i j b hV hpin H hc
    exact Or.inr ⟨ν, hN, algComb_of_ratScalar YS hRF fw (fw.evaluates_of_lUnif H.unif) H.core H.io
      (GlobalTheory.CoverHalf.primes_eq_of_halfIs T.toCore Rl.toRealDat H.laws.toLawsM H.core.lev (H.pins.2.tuple ()).half)
      H.size H.galois H.small.val H.small.ray H.small.roots hsp hρ hpin i j b hV hν⟩

end Core

end GlobalTheory.SerRefPt

namespace GlobalTheory.SerRefPt

open GlobalTheory.RealGeo GlobalTheory.Unframe GlobalTheory.UnframePt

set_option maxHeartbeats 3200000 in

theorem point_cases (hP : GlobalTheory.Published.CuspRapidDecay) (hA : GlobalTheory.Published.GlobalArtinReciprocity) (hRF : GlobalTheory.Published.RayClassFieldSt)
    (hS : GlobalTheory.SerStd.SeriesRatS) {eps : ℝ} (Fm : FamP eps) (x : ℝ) (hx : Fm.x1 < x) (i : Fm.Ix x) (p : Pt Fm x hx i) (hR : p.Rows)
    (hM : More p) (t : (Fm.D x i).ntw.Tw) (j : Fin (Fm.D x i).R.m) (h0 : RatHyp0 p.T p.R (F2 p) p.κ p.v₀ p.O t j)
    (ρ : Setup (Fm.D x i).ntw) (hρ : ρ.Good) (b : Bool) (h : RealPin p.R p.cG ρ) :
    (∀ y ∈ (p.R.FW j).WK, y = 0) ∨ ∃ ν, IsNorm p.R p.v₀ (ρ.B t j b) ν ∧ ∀ s g P, ρ.IsDatum t j b s g P →
      P ∈ ρ.lat t j b (smallInt (Fm.D x i)) g → AlgComb p.nexp p.v₀ j (ν • ρ.theta t j b g P) := by
  obtain ⟨c', w, hw, hfr, B', hv⟩ := exists_framed_half hP h0.size (GlobalTheory.Core5.of_core h0.core) (geoHalf p) h0.unif
    (inGeo_geoHalf hP Fm x hx i p hR hM t j h0)
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
  have H := core_cases (T := setCE p.T c') (Rl := fullHeckeRealDatMovedReadings p.R w) hA hRF hS (GlobalTheory.UnframeForms.movedYS p.nexp w) hρ b hpin' hRat hsp
  rw [hv] at H
  rcases H with H | ⟨ν, hN, H⟩
  · exact Or.inl H
  · exact Or.inr ⟨ν, hN, fun s g P hd hl => algComb_of_moved p.nexp w p.v₀ j (H s g P hd hl)⟩

theorem serRef : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → GlobalTheory.BigOn.Exp.SerRef := by
  intro hP hA hRF hS
  have hL := lowAt_holds
  have hT := twAdm
  unfold LowAt at hL
  unfold TwAdm at hT
  unfold SerRef
  refine (AtTw.and hL hT).imp fun Fm x hx i p hp hM w _ j h => ?_
  intro ρ hρ ν hpin hN hR0
  refine ⟨ν, hN, hR0, fun s g P hd hl => ?_⟩
  rcases point_cases hP hA hRF (GlobalTheory.SerStd.seriesRatS_of hS) Fm x hx i p hp hM _ j
    (ratHyp0_at_point Fm x hx i p hp hM _ h.2.2.2 h.1 j) ρ hρ _ hpin with H | ⟨ν₁, hN₁, H⟩
  · have h0 := theta_eq_zero p.nexp p.v₀ hρ _ j _ H hR0 hd
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [h0, smul_zero]
      exact AlgComb.zero
    exact h1
  · obtain ⟨ζ, hζ, e⟩ := exists_root_of_isNorm p.R p.v₀ _ hN₁ hN
    have h1 : AlgComb p.nexp p.v₀ j (ν • ρ.theta ((Fm.ex x hx i).nch.twI w) j ((Fm.ex x hx i).nch.sd w) g P) := by
      rw [e, mul_smul]
      exact (H s g P hd hl).smul hζ
    exact h1

end GlobalTheory.SerRefPt
