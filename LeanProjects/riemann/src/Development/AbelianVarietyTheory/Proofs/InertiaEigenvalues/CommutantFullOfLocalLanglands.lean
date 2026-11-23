import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CommutationFullnessOfReads
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateSplitPlaceOffStableSet
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AtMemAnd
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CommFullLayer

open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.IndefR.Cx Formalism.L2.Pj
  GlobalTheory.TwInputs GlobalTheory.CommFullAll
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section Raw

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}
  {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
  (Rl : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) {S : RatDat D.ntw}
  (YS : NExpRealS Rl cG S) (H : NExpRealH Rl cG S YS)

theorem hL_comm_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id) (i' : Fin D.R.m) (k : ℕ) (P : PlE D.host)
    (hsp : IsSplitPl D.host P) (hso : Bridge.SplitOff P (Rl.Sb : Set (Pl D.host.E))) (hi : ∃ i, P ∉ D.ntw.S0 i)
    (h2 : ((2 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal)
    (hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal) (hkr : k ≤ D.R.r)
    (g : S.G) (x : S.WL ((i' : ℕ) + 1)) :
    H.hL ((i' : ℕ) + 1) k P ((S.A ((i' : ℕ) + 1)).ρ g x) = (S.A ((i' : ℕ) + 1)).ρ g (H.hL ((i' : ℕ) + 1) k P x) := by
  obtain ⟨α, Rc, ha, hRc⟩ := GlobalTheory.HeckeSupSt.exists_heckeElt hR.lev hR.fam i' hso hkr
  have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData Rl.toRealDat i' P k α Rc := ⟨hso, hg, hkr, ha, hRc⟩
  let hL' : (Fin (Rl.nW i') → D.what₂.LL) →ₗ[D.what₂.LL] (Fin (Rl.nW i') → D.what₂.LL) :=
    (YS.fi i').e.toLinearMap ∘ₗ H.hL ((i' : ℕ) + 1) k P ∘ₗ (YS.fi i').e.symm.toLinearMap
  have hH : Formalism.L2.Pj.HeckeJ.IsHkJ (sg0 D A3.A) ((Rl.FW i').j (sg0 D A3.A)) (Rl.HW i' (sg0 D A3.A)).e
      (heckeOn (Rl.MW i' (sg0 D A3.A)) Rc)
      ((((Rl.C.mu0 i').val P : ℂˣ) : ℂ)⁻¹ ^ k * (((Nat.card (Formalism.L2.DIV.kP P) : ℕ) : ℂ) ^ (k * (D.R.nV / 2)))⁻¹) hL' := by
    intro y
    have h := hX.tie i' k P hsp hso hi h2 hkr α Rc ha hRc ((YS.fi i').e.symm y) rfl
    simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply] at h ⊢
    exact h
  have hc := GlobalTheory.HeckeSup.comm_rho_cl (hR.lev.βW i') hR.fam.Sb hR.models.HW hR.models.gW (sg0 D A3.A) hd
    (GlobalTheory.ExportPin.Model.j_injective Rl hU i' _) (hU i' (sg0 D A3.A)).2.2 hH ((YS.fi i').eG g)
  apply (YS.fi i').e.injective
  have h := LinearMap.congr_fun hc ((YS.fi i').e x)
  simp only [hL', LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply] at h
  rw [(YS.fi i').rho, ← h, ← (YS.fi i').rho, LinearEquiv.symm_apply_apply]

theorem commAll_fullAll_raw (hR : Rl.Char3 F) (hU : Rl.toRealDat.LUnif) (hI : Rl.toRealDat.LIntegral)
    (hX : NExpHeckeRowX Rl cG S YS H fun _ => LinearMap.id)
    (hS0c : ∀ i P P', P ∈ D.ntw.S0 i → IsConjPl D.host P P' → P' ∈ D.ntw.S0 i)
    (hS02 : ∀ i, placesOver D.host.E 2 ⊆ (D.ntw.S0 i : Set (PlE D.host)))
    (hS0b : ∀ i, ∀ Q ∈ Rl.Sb, Q ∈ D.ntw.S0 i) : CommAll D ∧ FullAll D := by
  have hidx : ∀ j, 1 ≤ j → j ≤ D.R.m → ∃ i' : Fin D.R.m, (i' : ℕ) + 1 = j := fun j h1 h2 =>
    ⟨⟨j - 1, by omega⟩, by simp only; omega⟩
  refine ⟨?_, ?_⟩
  · intro i j hj b k P hk g x
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    obtain ⟨-, hkr, hsp, hS0⟩ := hk
    obtain ⟨-, -, -, -, hso, -, h2P, -⟩ :=
      GlobalTheory.ConjPlaceOff.exists_conj_off D (D.ntw.S0 i) Rl.Sb P (hS0c i) (hS02 i) (hS0b i) hsp hS0
    have hg : ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
      intro h
      rw [Nat.cast_mul] at h
      rcases P.isPrime.mem_or_mem h with h | h
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 0 h)
      · exact hS0 (D.ntw.placesOver_subset_exceptional i 1 h)
    have hc := hL_comm_raw Rl F cG YS H hR hU hX i' k P hsp hso ⟨i, hS0⟩ h2P hg hkr
    refine (YS.eF i _ b h1 h2).injective ?_
    rw [YS.act, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, H.hkEq i _ b h1 h2 k P _ hS0 hsp hkr, YS.act, map_smul,
      hkFR_act S i _ b (H.hL _) (H.hs _ h1 h2) k P (YS.rho _ h1 h2) (YS.chi _ h1 h2) hc]
  · intro i j hj b
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hj
    obtain ⟨i', rfl⟩ := hidx j h1 h2
    have hF := iso_span (YS.fi i') (hI i').2.1.2
    have hB := Bsup_span S i ((i' : ℕ) + 1) b hF
    obtain ⟨c, hc0, -, hc2⟩ := YS.bsup i ((i' : ℕ) + 1) b h1 h2
    let e := YS.eF i ((i' : ℕ) + 1) b h1 h2
    have hc0' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c ≠ 0 := by
      intro h0
      apply hc0
      apply IsFractionRing.injective (D.ntw.O i) (FractionRing (D.ntw.O i))
      rw [h0, map_zero]
    have hle : Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) ≤
        (Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b))).comap e.symm.toLinearMap := by
      refine Submodule.span_le.2 fun z hz => ?_
      have hm : c • e.symm z ∈ D.nexp.Bsup i ((i' : ℕ) + 1) b := hc2 _ (by simpa [e] using hz)
      have hm' : algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c • e.symm z ∈
          Submodule.span (FractionRing (D.ntw.O i)) (D.nexp.Bsup i ((i' : ℕ) + 1) b : Set (D.nexp.Fm i ((i' : ℕ) + 1) b)) := by
        rw [algebraMap_smul]
        exact Submodule.subset_span hm
      have := Submodule.smul_mem _ (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) c)⁻¹ hm'
      rw [inv_smul_smul₀ hc0'] at this
      exact this
    refine eq_top_iff.2 fun t _ => ?_
    have ht : e t ∈ Submodule.span (FractionRing (D.ntw.O i)) (Bsup S i ((i' : ℕ) + 1) b : Set (Fm S i ((i' : ℕ) + 1) b)) := by
      rw [hB]; exact Submodule.mem_top
    have := hle ht
    simpa using this

end Raw

theorem commAll_fullAll_layer : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL fun _ _ _ _ w Z _ _ t nch n c =>
    GlobalTheory.TwInputs.CommAll (w.D Z) ∧ GlobalTheory.TwInputs.FullAll (w.D Z) := by
  intro _ _ hL
  refine ⟨1, one_pos, fun eps C8 C5 c6 Cb _ _ _ _ => ⟨⟨0, fun _ => 0, fun _ => 0, fun _ => 0⟩, fun C _ _ _ =>
    ⟨0, fun cD _ => ⟨0, fun ch _ => ⟨0, fun K _ _ _ _ _ _ => ?_⟩⟩⟩⟩⟩
  refine ⟨fun _ _ _ => ∅, fun _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, fun _ _ _ _ _ => ∅, by simp, by simp, fun B f T _ _ _ _ => ?_⟩
  intro _ w Z Wt p0 t nch n xd c ⟨e⟩ _ _
  have hS0b : ∀ i, ∀ Q ∈ t.r.z.R.Sb, Q ∈ (w.st Z).toD7.ntw.S0 i := by
    intro i P hP
    have hA : t.r.z.R.Sb = t.r.z.R.Pg := t.r.z.pins.char.allPl
    obtain ⟨k, hk⟩ := e.ser.ex.good.Pg i ⟨0, lt_of_lt_of_le two_pos B.R.two_le_m⟩ true P
      (by rw [e.ser.ex.pin.Pg]; exact hA ▸ hP)
    exact (w.st Z).toD7.ntw.placesOver_subset_exceptional i k hk
  exact commAll_fullAll_raw (D := (w.st Z).toD7) t.r.z.R t.r.z.F t.r.z.cG c.row.nexp c.row.hecke
    (RealDat3.characterisation_of_weak t.r.z.pins.char t.exAt) t.r.intersectionNumber_baseChange.prim.unif t.r.intersectionNumber_baseChange.aux.integral e.hecke
    (fun i P P' hP hc => e.ser.ex.good.goodSetup_badPlaces_conj i P hP P' hc) (fun i => e.ser.ex.good.goodSetup_placesOverTwo_subset i) hS0b

end GlobalTheory.CommFullLayer
