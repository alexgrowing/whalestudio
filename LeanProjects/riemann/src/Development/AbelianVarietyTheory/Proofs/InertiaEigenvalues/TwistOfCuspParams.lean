import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsEmptyOfNotAll
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HeckeReadOfDeltaFrob
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsHeckeDatum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AuxiliaryPrimeNeTypePrime
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyDefiniteSpacesStandardAndLarge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsRationalHeckeOperatorsAdelicReadingStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisSideStatement

noncomputable section

namespace GlobalTheory.TwInputs.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2 Formalism.L2.Host Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.NX
  NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.Col2 GlobalTheory.HeightCounting GlobalTheory.SeriesTie GlobalTheory.TwInputs.JoinModel
open Formalism.MainNotions.IntegralHeckeForms (HkIdx)
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

section General

variable {D : D7}

theorem injective_of_cellTie {ρ : Setup D.ntw} {hρ : ρ.Good} {i : D.ntw.Tw} {j : Fin D.R.m} {b : Bool} {rd : Rd ρ D.nexp i j b}
    (T : CellTie hρ D.nexp rd) : Function.Injective rd := by
  refine (injective_iff_map_eq_zero rd).2 fun x hx => ?_
  have h1 : ((1 : D.ntw.Ok i 0) ⊗ₜ[D.ntw.O i] x : D.ntw.Ok i 0 ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 :=
    T.injective_rdK 0 (by rw [rdK_tmul, hx, smul_zero, map_zero])
  haveI : Module.Flat (D.ntw.O i) (FractionRing (D.ntw.O i)) := IsLocalization.flat _ (nonZeroDivisors (D.ntw.O i))
  haveI : Module.Flat (D.ntw.O i) (D.nexp.Fm i ((j : ℕ) + 1) b) :=
    Module.Flat.trans (D.ntw.O i) (FractionRing (D.ntw.O i)) _
  have h2 := Module.Flat.rTensor_preserves_injective_linearMap (M := D.nexp.Fm i ((j : ℕ) + 1) b)
    (Algebra.linearMap (D.ntw.O i) (D.ntw.Ok i 0)) (D.ntw.Ok_inj i 0)
  have h3 : ((1 : D.ntw.O i) ⊗ₜ[D.ntw.O i] x : D.ntw.O i ⊗[D.ntw.O i] D.nexp.Fm i ((j : ℕ) + 1) b) = 0 := h2 (by
    rw [LinearMap.rTensor_tmul, Algebra.linearMap_apply, map_one, h1, map_zero])
  simpa using congrArg (TensorProduct.lid (D.ntw.O i) _) h3

def IsFrobUnit (D : D7) (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) : Prop :=
  ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
    u i b P = Units.map (algebraMap (D.ntw.O0 i) (D.ntw.O i)).toMonoidHom (if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹)

theorem exists_hecke (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S) (Z : ExportTie YS X.geo.v₀)
    (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (hs : ∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j))
    (h0 : ∀ j P, hL j 0 P = 1) (hr : GlobalTheory.ExportPin.Reads X.R X.cG S YS hL)
    (u : ∀ i : D.ntw.Tw, Bool → PlE D.host → (D.ntw.O i)ˣ) (hu : IsFrobUnit D u)
    (hz : ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x) :
    ∃ H : NExpRealH X.R X.cG S YS, GlobalTheory.ExportPin.Reads X.R X.cG S YS H.hL ∧
      ∀ i b P, P ∉ D.ntw.S0 i → ∀ σ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om, IsFrob (F := D.host.E) (D.nd.plOm.1 P) (normV P) σ →
        H.cHk i b 1 P = algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (algebraMap (D.ntw.O0 i) (D.ntw.O i)
          ((if b then D.ntw.delta i σ else (D.ntw.delta i σ)⁻¹ : (D.ntw.O0 i)ˣ) : D.ntw.O0 i)) := by
  have hδ : IsDeltaInv Z.ρ u := by
    intro i j b k P hk α z hα hz
    have e : u i b P = HeckePinRead.uD D i b P := by
      rw [hu i b P hk.2.2.2 _ (HeckePinRead.frobU_spec D P)]
      cases b <;> rfl
    rw [e]
    exact HeckePinRead.isDeltaInv_uD Z.good Z.pin i j b k P hk α z hα hz
  refine ⟨⟨hL, hs, fun i b k P => (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ k,
    fun _ _ _ => pow_zero _, fun i b P => ((u i b P).isUnit.map _).pow 1, fun i b k P => by rw [pow_one], ?_⟩, hr, ?_⟩
  · intro i j b h1 h2 k P x hP hsp hk
    rcases Nat.eq_zero_or_pos k with rfl | k1
    · rw [hz i j b P x h1 h2 hP hsp, pow_zero, one_smul,
        (GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (hs j h1 h2) 0 P).2 (h0 j P)]
      rfl
    · obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      let j' : Fin D.R.m := ⟨n, h2⟩
      have hk' : HkIdx i k P := ⟨k1, hk, hsp, hP⟩
      obtain ⟨α, R, z, d⟩ := GlobalTheory.HeckeDatumExists.exists_isHeckeDatum D _ _ Z.ρ Z.good i j' b k P hk'
      have e := (Z.hecke i j' b).eq (injective_of_cellTie (Z.tie i j' b)) hk' d
        (heckeAt_of_scaled YS X.geo.v₀ Z.pin X.char.lev X.char.allPl Z.good hr hδ i j' b (Z.ν i j' b)
          (hs _ (Nat.le_add_left _ _) j'.2) hk' (f := x) ((YS.eF i _ b (Nat.le_add_left _ _) j'.2).apply_symm_apply _))
      exact (congrArg (YS.eF i _ b h1 h2) e).trans ((YS.eF i _ b h1 h2).apply_symm_apply _)
  · intro i b P hP σ hσ
    change (algebraMap (D.ntw.O i) (FractionRing (D.ntw.O i)) (u i b P)) ^ 1 = _
    rw [pow_one, hu i b P hP σ hσ, Units.coe_map]
    rfl

theorem hkF_zero_of_sideB {cf Rw low Pq S hL eig θ} (Bs : SideB D cf Rw low Pq S hL eig θ) (h0 : ∀ j P, hL j 0 P = 1) :
    ∀ i j b P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j b 0 P x = x := by
  intro i j b P x h1 h2 hP hsp
  refine (Bs.eF i j b h1 h2).injective ?_
  rw [Bs.hkEq i j b h1 h2 0 P x hP hsp (Nat.zero_le _), pow_zero, one_smul]
  exact LinearMap.congr_fun ((GlobalTheory.ExportPin.Model.hkFR_of_smul S i j b (Bs.hs j h1 h2) 0 P).2 (h0 j P)) _

theorem exists_frobUnit_and_hkF_trivial {hL : GlobalTheory.Published.LocalLanglandsGL} (b : NBuilt hL D) (h0 : ∀ j P, b.hL j 0 P = 1) :
    (∃ u, IsFrobUnit D u) ∧
      ∀ i j s P x, 1 ≤ j → j ≤ D.R.m → P ∉ D.ntw.S0 i → IsSplitPl D.host P → D.nexp.hkF i j s 0 P x = x := by
  obtain ⟨D0, cf, jE, A, cg, au, rep, row, low, Pq, S, hl, eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, rfl⟩ := b
  have h := hkF_zero_of_sideB (D := D0) Bs h0
  exact ⟨⟨Bs.cHk, Bs.cHk_del⟩, fun i j s P x => h i j s P x⟩

end General

section Rows

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} {w : ColW B f T} {Z : w.Lt}
  {Wt : Set B.places.Pl} {p0 : BaseLevelRowSide (w.D Z)} {t : RowsT K w Z Wt p0} {nch : NChoice (w.D Z)} {n : NchT w Z Wt nch}
  {xd : ThData (w.D Z)} {c : NCore hL t n}

theorem nonempty_twOf {hH hV hs} (e : NE hL K B f T w Z Wt p0 t nch n xd c) (hF : FieldOk (realOf t hH hV hs))
    (hG : ∃ G : GalSide (w.st Z).toD7, G.cf = TC.cf w.I w.l Z ∧ G.lam.C = TC.cf w.I w.l Z ∧ Nonempty (CGTrue hL _ G.wd))
    (hR : ∀ (D : D7) (X : RealSide D) (S : RatDat D.ntw) (YS : NExpRealS X.R X.cG S),
      ∃ hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j), (∀ j, 1 ≤ j → j ≤ D.R.m → HeckeStabR S j (hL j)) ∧
        (∀ j P, hL j 0 P = 1) ∧ GlobalTheory.ExportPin.Reads X.R X.cG S YS hL) :
    Nonempty (TwOf hL K B f T w Z Wt p0 t nch n xd c) := by
  obtain ⟨g, h1, h2, ⟨cg⟩⟩ := hG
  obtain ⟨k1, k2⟩ := hk_of_built c.a.nt.toNBuilt
  obtain ⟨⟨u, hu⟩, hz⟩ := exists_frobUnit_and_hkF_trivial c.a.nt.toNBuilt (c.a.ratIn_hL ▸ c.a.ratIn.hL_zero)
  obtain ⟨f', s1, s2, s3⟩ := hR _ (realOf t hH hV hs) _ c.row.nexp
  obtain ⟨H, r1, r2⟩ := exists_hecke (realOf t hH hV hs) _ c.row.nexp e.ser.ex f' s1 s2 s3 u hu hz
  exact ⟨twOf (serOf e H r1 r2 k1 k2) rfl HEq.rfl g h1 h2 hF cg fun hT v hv => base_of_untw _ hT v hv⟩

end Rows

end GlobalTheory.TwInputs.AtLayer

namespace GlobalTheory.TwInputs.AtLayer

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

theorem twOf_of_layer : PrN → SerN → ∀ hL : GlobalTheory.Published.LocalLanglandsGL, AtMem hL (fun _ _ _ _ w Z _ _ _ _ _ c => ∀ Rw : RowSide (w.D Z), HEq Rw.locR c.a.nt.A.row.locR → GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings.GoodRowCuspParam (w.D Z) Rw) → EvLgG fun K B f T => KPx B f → T = TwDat.untw B T.pl → ∀ w Z Wt p0 t nch n xd c, Nonempty (NEb hL K B f T w Z Wt p0 t nch n xd c) → Nonempty (RX K B f T w Z Wt p0 t) → ColPin w → Nonempty (GlobalTheory.TwInputs.TwOf hL K B f T w Z Wt p0 t nch n xd c) := by
  intro hP hS hL _
  have e1 := (evG_of_ev GlobalTheory.Mem.StdSize.vstd_size_ev).inter (evG_of_ev GlobalTheory.Mem.HostFrames.hostHyp_frames_ev)
  have e2 := EvG.inter (GlobalTheory.T.exists_galois_side hP hS hL) (GlobalTheory.TwInputs.SmallField.evLgG_fieldOk hP)
  refine (e1.inter e2).imp fun K _ _ _ _ H => ?_
  obtain ⟨⟨hV, hH⟩, hG, hF⟩ := H
  refine (hG.inter hF).imp fun B f T hO G hK _ w Z Wt p0 t nch n xd c ⟨e⟩ hR hC => ?_
  exact nonempty_twOf (hH := (hH (w.st Z) hO).1) (hV := (hV (w.st Z) hO).1) (hs := (hV (w.st Z) hO).2) e.1
    ((G.2 hK T w Z).1 _ t.r.z.lev.C) (G.1 hK w Z Wt p0 t nch n xd c ⟨e.1⟩ hR hC) (GlobalTheory.T.exists_rationalHeckeOperators_adelicReading hP.decay hS.hkTr hS.hkRead)

end GlobalTheory.TwInputs.AtLayer

end
