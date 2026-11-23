import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteDimensionalCuspSectionsVanishingOffDomain
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegralityStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRingStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
import Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory

section IntWeight

open Formalism.L2.Pj

variable {K : Type} [Field K] {ι : Type}
  {pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type}
  {mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T], (S →ₐ[K] T) → pts S → pts T → Prop}
  {borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop}

theorem evalAt_borR_of_borChart_int [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℤ) {f : Rules pts}
    (hf : IsNatural pts mapR f)
    (hw : ∀ (p : TRing K) (t : ι → (p.R)ˣ) (y y' : pts p.R), borR t y y' →
      f p y' = ((∏ i, t i ^ e i : (p.R)ˣ) : p.R) * f p y)
    (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evalAt pts mapR f y := by
  unfold evalAt
  rw [dif_pos hy, dif_pos hy']
  apply eq_of_locM (K := K)
  intro m hm
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hy'.choose_spec.choose_spec.choose_spec,
    chartAt_val hf hc hy.choose_spec.choose_spec.choose_spec, ← e1, ← e2, AlgHom.comp_apply, AlgHom.comp_apply,
    ← hf A B π u uB hπ, ← hf A B π' u uB' hπ', hw B tB uB uB' hbB, map_mul]
  congr 1
  have key : ∀ i, Units.map cB.toRingHom.toMonoidHom (tB i) = Units.map (locM K m).toRingHom.toMonoidHom (t i) :=
    fun i => Units.ext (by simpa using e3 i)
  have h1 : cB ((∏ i, tB i ^ e i : (B.R)ˣ) : B.R) =
      ((Units.map cB.toRingHom.toMonoidHom (∏ i, tB i ^ e i) : (Localization.AtPrime m)ˣ) : Localization.AtPrime m) := rfl
  have h2 : locM K m ((∏ i, t i ^ e i : Sˣ) : S) =
      ((Units.map (locM K m).toRingHom.toMonoidHom (∏ i, t i ^ e i) : (Localization.AtPrime m)ˣ) :
        Localization.AtPrime m) := rfl
  rw [h1, h2, map_prod, map_prod]
  simp_rw [map_zpow, key]

end IntWeight

open Formalism.L2.Pj AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H}

theorem evR_frBor_of_mem_secZ (hS : Out.SecBaseChangeSt) (Xo : Moduli Dw l) (c : Coeff l) (e : Ix Dw → ℤ)
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (S : Type) [CommRing S] [IsReduced S] [Algebra c.F S]
    (t : Ix Dw → Sˣ) (y y' : FrPt Xo c S) (hb : FrBor t y y') :
    evR Xo c f y' = ((∏ i, t i ^ e i : Sˣ) : S) * evR Xo c f y := by
  have hB := (GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c).2.1
  have hall := GlobalTheory.T.framedPoint_reduced_from_testRing hS E H Dw l Xo c
  exact evalAt_borR_of_borChart_int hB e hf.1 hf.2 S t y y' (hall S y) (hall S y') hb

theorem test_value_eq_const_mul_reading_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (p : TRing c.F)
    (y : FrPt Xo c p.R) (ψ : p.R →ₐ[c.F] CAt σ) :
    ∃ (k : U.Comp) (x : (U.X k).dom) (u : ℂ), ∀ f ∈ secZ Xo c e,
      Formalism.L2.Pj.toC (ψ (f p y)) = u * rdU U f k x.1 := by
  obtain ⟨-, -, hW, -, -, -, -⟩ := GlobalTheory.T.framedModuli_algebraicLaws_chart_weight_integrality hS E H Dw l Xo c
  obtain ⟨z, hz⟩ := GlobalTheory.Frames.FramedBaseChange.exists_frMap hS E H Dw l Xo c p.R (CAt σ) ψ y
  obtain ⟨k, x, t, ht⟩ := hU.2.2.1 z
  haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ)
  refine ⟨k, x, Formalism.L2.Pj.toC ((∏ i, t i ^ e i : (CAt σ)ˣ) : CAt σ), fun f hf => ?_⟩
  have hft : FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) z := ⟨p, ψ, y, hz⟩
  have hev : evR Xo c f z = ψ (f p y) := by
    unfold evR evalAt
    rw [dif_pos hft]
    exact hW f hf.1 (CAt σ) _ p _ ψ _ y z hft.choose_spec.choose_spec.choose_spec hz
  have hw := evR_frBor_of_mem_secZ hS Xo c e hf (CAt σ) t _ _ ht
  rw [← hev, hw]
  classical
  show _ = _ * (if h : x.1 ∈ (U.X k).dom then Formalism.L2.Pj.toC (evR Xo c f (U.un k ⟨x.1, h⟩)) else 0)
  rw [dif_pos x.2]
  rfl

theorem reading_linearIndependent_secZ (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l}
    {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r) (hU : IsUnf U) (e : Ix Dw → ℤ) (m : ℕ) (b : Fin m → Rul Xo c)
    (hb : ∀ i, b i ∈ secZ Xo c e) (hli : LinearIndependent c.F b) :
    LinearIndependent ℂ (fun i => rdU U (b i)) := by
  have h := fun p y ψ => test_value_eq_const_mul_reading_secZ hS U hU e p y ψ
  have : CharZero c.F := RingHom.charZero σ
  rw [Fintype.linearIndependent_iff]
  intro w hw
  have hθ : ∀ θ : Module.Dual c.F (CAt σ), ∀ i, θ (toCAt σ (w i)) = 0 := by
    intro θ
    have hz : ∑ i, θ (toCAt σ (w i)) • b i = 0 := by
      funext p y
      have hpt := descend_cpts σ p (fun i => b i p y) w (fun ψ => by
        obtain ⟨k', x, u, hk⟩ := h p y ψ
        have e1 : ∀ i, w i * cvalR σ (ψ (b i p y)) = u * (w i * rdU U (b i) k' x.1) := by
          intro i; rw [show cvalR σ (ψ (b i p y)) = Formalism.L2.Pj.toC (ψ (b i p y)) from rfl, hk (b i) (hb i)]; ring
        have e2 := congrFun (congrFun hw k') x.1
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at e2
        simp_rw [e1]
        rw [← Finset.mul_sum, e2, mul_zero]) θ
      simpa [Finset.sum_apply] using hpt
    exact fun i => Fintype.linearIndependent_iff.1 hli _ hz i
  intro i
  exact (Module.forall_dual_apply_eq_zero_iff c.F (toCAt σ (w i))).1 fun θ => hθ θ i

theorem cuspW_finiteDimensional_of_isUnf (hS : Out.SecBaseChangeSt) {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}
    (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ : c.F →+* ℂ) (hσ : GoodEmb c σ) (hU : IsUnf (U σ)) (G : WTZ E) :
    FiniteDimensional c.F (cuspW Xo c U G) := by
  classical
  let W : Submodule ℂ (FDSec (U σ).X) :=
    { carrier := {P | P ∈ holSub (U σ).X (modelWt (U σ) G) ∧ ∀ k, ∀ x ∉ ((U σ).X k).dom, P k x = 0}
      add_mem' := fun {P Q} hP hQ => ⟨add_mem hP.1 hQ.1, fun k x hx => by
        change P k x + Q k x = 0
        rw [hP.2 k x hx, hQ.2 k x hx, add_zero]⟩
      zero_mem' := ⟨zero_mem _, fun k x hx => rfl⟩
      smul_mem' := fun t P hP => ⟨Submodule.smul_mem _ t hP.1, fun k x hx => by
        change t • P k x = 0
        rw [hP.2 k x hx, smul_zero]⟩ }
  haveI : FiniteDimensional ℂ W :=
    GlobalTheory.T.finiteDimensional_cuspSections_vanishing_offDomain E r (U σ).Comp (U σ).X (modelWt (U σ) G) W (fun P hP => hP.1) (fun P hP => hP.2)
  have key : ∀ s : Finset (cuspW Xo c U G),
      LinearIndependent c.F (fun i : s => (i : cuspW Xo c U G)) → s.card ≤ Module.finrank ℂ W := by
    intro s hs
    let e := s.equivFin
    have h0 : LinearIndependent c.F (fun j : Fin s.card => ((e.symm j : s) : cuspW Xo c U G)) :=
      hs.comp (fun j => e.symm j) e.symm.injective
    have hb : LinearIndependent c.F
        (fun j : Fin s.card => (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c)) :=
      h0.map' (cuspW Xo c U G).subtype (Submodule.ker_subtype _)
    have hc := reading_linearIndependent_secZ hS (U σ) hU (exZ Dw G) s.card _
      (fun j => cuspW_le_secZ G ((e.symm j : s) : cuspW Xo c U G).2) hb
    have hmem : ∀ j : Fin s.card,
        rdU (U σ) (((e.symm j : s) : cuspW Xo c U G) : Rul Xo c) ∈ W :=
      fun j => ⟨(mem_cuspW.1 ((e.symm j : s) : cuspW Xo c U G).2).2 σ hσ, fun k x hx => by
        simp [rdU, hx]⟩
    let b' : Fin s.card → W := fun j => ⟨_, hmem j⟩
    have hc' : LinearIndependent ℂ b' := LinearIndependent.of_comp W.subtype hc
    have := hc'.fintype_card_le_finrank
    simpa using this
  haveI : Module.Free c.F ↥(cuspW Xo c U G) := Module.Free.of_divisionRing _ _
  exact Module.rank_lt_aleph0_iff.mp ((rank_le key).trans_lt (Cardinal.natCast_lt_aleph0))

end GlobalTheory

theorem GlobalTheory.Deep.finiteDimensional_V_of_good : ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ G : WTZ D.host.E, FiniteDimensional Y.d.c₂.F (Y.V G) := by
  intro D T j Y e o hY G
  have hσ : Formalism.L2.Pj.GoodEmb Y.d.c₂ (Formalism.L2.Pj.goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom) :=
    Formalism.L2.Pj.goodEmb_goodOf _ _
  exact GlobalTheory.cuspW_finiteDimensional_of_isUnf GlobalTheory.abelianSchemeLaws_all.1.secBaseChange Y.U _ hσ (hY.unf _ hσ) G
