import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatTranslateOfPrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoefficientBoundTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRows
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceBoundTupleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawLeftRestrictionGlobalStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSupportedUnitaryAdjointAction
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwCx

open GlobalTheory.ExportSeries Formalism.IndefR.Datum GlobalTheory.BigOn.Exp.TupLe GlobalTheory.BigOn.Exp.SerBase
open GlobalTheory.ConjTwist (BaseOf UnitOff ser)
open GlobalTheory.FlatVecSum (princ)

def TwQ : Prop := ∀ (D : D7) (i : D.ntw.Tw) (k : ℕ) (Q : Finset (Pl D.host.E))
  (ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), IntegralHeckeForms.TwOK i k Q ψ → ∀ P ∈ Q, ((D.ntw.l i : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal

theorem twQ : TwQ := by
  intro D i k Q ψ hok P hP hl
  obtain ⟨-, -, -, -, -, hram, htriv⟩ := hok
  obtain ⟨A, hA⟩ := ReciprocityTheory.Gal.exists_isPlaceOver D.nd.Om P
  obtain ⟨σ, hσ, hne⟩ := (hram P A hA).2 hP
  exact hne (htriv P hl A hA σ (ReciprocityTheory.Gal.Ine_le_Dec A hσ))

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl} {j : Fin D.R.m}

theorem cx_at (s1 : PlacesSt) (s2 : FlatSt) (s3 : TraceSt) (s6 : TwQ) (hr : p.Rows) (hm : More p)
    (hw : D.plEq w ∈ p.R.twPl)
    (hok : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) {ν : ℂ} (hfit : Fit p w j hρ ν)
    (hLS : ∀ h, ∀ P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h,
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hLI : LatIo p w j)
    (c1 : ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w))
    (c2 : p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).de.chi *
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi)
    (e : FractionRing (ex.nch.Oe w) →+* ℂ)
    (h2 : ∀ a : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w),
      e (algebraMap (ex.nch.Oe w) _ (algebraMap _ (ex.nch.Oe w) a)) = ρ.eOk (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) a)
    (z : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w) ⊗[D.ntw.O (ex.nch.twI w)] D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w))
    (hz : z ∈ twSet hρ (rdAt p w j hρ ν) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)) :
    ∃ (n : ℕ) (h : Fin n → GA D (Vc D j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → ex.nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : ex.nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc D j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → D.what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 D p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) =
        levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
          ((R2 p).vP j ((R2 p).mu (D.plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ (ex.nch.k' w) z = κ • ∑ k, (e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (a k)) * ν⁻¹) •
        adForm (R2 p) j (y k) (p.v₀ j (sg0 D p.P.A3.A)) := by
  obtain ⟨hadapt, hν, -, hlev⟩ := hfit
  have hpin := hadapt.1
  have hL := GlobalTheory.BigOn.links2_of_rows _ _ _ _ _ _ _ _ _ _ p hr hm.1
  have hC : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hB0 : BaseOf (R2 p) j (ρ.B (ex.nch.twI w) j (ex.nch.sd w)) :=
    { baseOf_of_realPin_at (cG := p.cG) hC.lev hρ hpin (ex.nch.twI w) j (ex.nch.sd w) with }
  obtain ⟨p1, p2, p3⟩ := s1 _ _ _ _ _ _ _ _ _ _ p j hr hm w hw hok ρ hρ hpin c1 c2
  obtain ⟨ht, hadm, hval⟩ := GlobalTheory.TwistGood.tw_good _ _ _ ρ hρ _ j (ex.nch.sd w) _ _ _ hok
  have hB := hρ.base (ex.nch.twI w) j (ex.nch.sd w)
  obtain ⟨z0, cz, hz0, hcz, hfl⟩ := s2 _ _ _ _ _ _ _ _ _ _ p j hr hm _ _ ((R2 p).mu (D.plEq w)) hB hB0 ht hadm c2 p3
  have hzf : z0 ∈ GfC (Vc D j) := GlobalTheory.TwTraceCx.mem_GfC_of_suppAt p1 hz0
  have hω : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).IsWeil
      (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi
      ((R2 p).ωP j ((R2 p).mu (D.plEq w))) := by
    have e0 : (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).mu *
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi =
        (R2 p).toLevCh.mu ((R2 p).mu (D.plEq w)) ((j : ℕ) + 1) := by
      rw [Base.mu, hB0.mu0, mul_assoc, ← c2]
      rfl
    rw [Base.IsWeil, e0, hB0.ψ, hB0.eta]
    exact hC.thP.ωP j _
  have hN : IsUnit ((GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w)) : ℕ) : ex.nch.Oe w) := by
    have hcop : Nat.Coprime (D.ntw.l (ex.nch.twI w)) (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hq
      have := GlobalTheory.NormUnit.coprime_absNorm _ (D.ntw.lPrime _).out P (p2 P hP)
      rwa [Ideal.absNorm_apply, Submodule.cardQuot_apply] at this
    simpa using (GlobalTheory.NormUnit.isUnit_natCast_of_coprime (D.ntw.O_l _) hcop).map (algebraMap _ (ex.nch.Oe w))
  obtain ⟨ν0, c, hs, n, hn, hνc⟩ := hν
  rw [p.phsOne j, map_one, one_mul] at hνc
  have c0 : c ≠ 0 := fun h => ν0 (by rw [h, zero_pow hn] at hνc; exact pow_eq_zero_iff hn |>.1 hνc)
  obtain ⟨u, hu, hio⟩ := hLI ρ hρ hpin c c0 hs
  obtain ⟨s, h, P, hd, hQ, hsupp, hgen⟩ := hz
  have hq1 := ht.split
  have hq2 : ∀ P' ∈ (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).Q,
      ((D.ntw.l (ex.nch.twI w) : ℕ) : 𝓞 D.host.E) ∉ P'.asIdeal :=
    fun P' hP' => s6 D _ _ _ _ hok P' (mem_half.1 hP').1
  have hP1 := lat_translate_of_prime hρ _ j _ hq1 hq2 hsupp hd.mem
  have hP2 := lat_translate_of_prime hρ _ j _ p1 p2 (GlobalTheory.DownLift.SplitCoef.suppAt_inv_of hz0) hP1
  have hh2 : h * hQ * z0⁻¹ ∈ GfC (Vc D j) :=
    mul_mem (mul_mem hd.fin (GlobalTheory.TwTraceCx.mem_GfC_of_suppAt hq1 hsupp)) (inv_mem hzf)
  obtain ⟨n', f, g, hsum⟩ := Submodule.mem_span_set'.1 (hLS _ P hP2)
  choose y hy hyio using fun k => hio _ hh2 (g k).1 (g k).2
  choose o ho using fun k => RingHom.mem_range.1 (f k).2
  obtain ⟨uu, huu⟩ := hval (detRoot (Vc D j) (h * hQ))
  have hcu : UnitOff (GlobalTheory.TwistField.tupPrime (R2 p) ((R2 p).mu (D.plEq w))) (cz * (c⁻¹ * ν)) :=
    unitOff_mul hcz (unitOff_root hn (by rw [mul_pow, inv_pow, hνc, inv_mul_cancel₀ (pow_ne_zero _ c0)]))
  obtain ⟨-, m, hm1, -⟩ := hcu
  refine ⟨n', fun _ => h * hQ * z0⁻¹, y,
    fun k => algebraMap _ (ex.nch.Oe w) ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)),
    cz * (c⁻¹ * ν), _, hN, ⟨m, hm1⟩, fun k => ⟨hh2, hy k⟩, ?_⟩
  intro yy hyy
  have eA : ∀ k, adForm (R2 p) j (yy k) (p.v₀ j (sg0 D p.P.A3.A)) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹
      (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u) := fun k =>
    (congrArg (adForm (R2 p) j (yy k)) (funext hu)).symm.trans (hyy k u)
  have eE : ∀ k, e (algebraMap (ex.nch.Oe w) (FractionRing (ex.nch.Oe w)) (algebraMap _ (ex.nch.Oe w)
      ((uu : D.ntw.Ok (ex.nch.twI w) (ex.nch.k' w)) * algebraMap _ _ (o k)))) =
      ((detChar (Vc D j) (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w)
        (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (h * hQ) : Circle) : ℂ) * (f k : ℂ) := fun k => by
    rw [h2, map_mul, hρ.ek_e, ho k, ← huu]
    rfl
  have eS : ∀ k, series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F ((R2 p).ωP j ((R2 p).mu (D.plEq w)))
      ((princ (ρ.B (ex.nch.twI w) j (ex.nch.sd w))).vecFlat
        (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)))
      (h * hQ) (g k : PolF D (Wc D j).rank (Vc D j).rank) = (c⁻¹ * cz) •
      singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu (D.plEq w))) ((R2 p).vP j ((R2 p).mu (D.plEq w)))
        (h * hQ * z0⁻¹) (y k) u := fun k => by
    have e1 : (g k : PolF D (Wc D j).rank (Vc D j).rank) = c⁻¹ • (R2 p).ioP j (PiTensorProduct.tprod ℂ u) (y k) := by
      rw [hyio k, smul_smul, inv_mul_cancel₀ c0, one_smul]
    rw [e1, map_smul, hB0.series_eq_ser, hfl]
    funext g'
    have e3 := GlobalTheory.Adopt.thetaSeries_translated_datum_at_translated_class _ _ _ _ _ _ (R2 p) _ hC j ((R2 p).mu (D.plEq w)) z0⁻¹ cz (inv_mem hzf) u (h * hQ) (y k) g'
    simp only [Pi.smul_apply, smul_eq_mul] at e3 ⊢
    rw [e3]
    simp only [GlobalTheory.ConjTwist.ser, singleSeries]
    ring
  rw [hgen, GlobalTheory.TwTraceCx.gen_eq_smul hB ht hadm (hρ.weil_base _ _ _) hω,
    ← s3 _ _ _ _ _ _ _ _ _ _ p j hr hm ρ hρ hpin hlev _ _ _ _ ht hadm hω, ← hsum, map_sum, map_sum]
  simp only [Subring.smul_def, map_smul, eS, eA, eE, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  field_simp

end Point

theorem twGen_cx : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.SeriesRat → TwAdm → TwChr → AtFit fun Fm x hx i p w j ρ hρ ν _ => ∀ e : FractionRing ((Fm.ex x hx i).nch.Oe w) →+* ℂ, (∀ y, e ((Fm.ex x hx i).nch.embW w y) = (Fm.D x i).what₂.embLL y) → (∀ a : (Fm.D x i).ntw.Ok ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.k' w), e (algebraMap ((Fm.ex x hx i).nch.Oe w) _ (algebraMap _ ((Fm.ex x hx i).nch.Oe w) a)) = ρ.eOk ((Fm.ex x hx i).nch.twI w) ((Fm.ex x hx i).nch.sd w) ((Fm.ex x hx i).nch.k' w) a) →
  ∀ z ∈ twSet hρ (rdAt p w j hρ ν) ((Fm.ex x hx i).nch.k' w) ((Fm.ex x hx i).nch.Q w) (GlobalTheory.TwistIndex.chosenChar (Fm.ex x hx i).nch w),
  ∃ (n : ℕ) (h : Fin n → GA (Fm.D x i) (Vc (Fm.D x i) j)) (w' : Fin n → ((R2 p).cV j).W) (a : Fin n → (Fm.ex x hx i).nch.Oe w) (κ : ℂ) (N : ℕ),
    IsUnit ((N : ℕ) : (Fm.ex x hx i).nch.Oe w) ∧ (∃ m : ℕ, IsIntegral ℤ ((N : ℂ) ^ m * κ)) ∧
    (∀ k, h k ∈ GfC (Vc (Fm.D x i) j) ∧ InCoefLat (R2 p) j (h k) (w' k)) ∧
    ∀ y : Fin n → Fin ((R2 p).nW j) → (Fm.D x i).what₂.LL,
      (∀ k, ∀ v : ∀ τ, lowT ((R2 p).MW j (sg0 (Fm.D x i) p.P.A3.A)) τ, adForm (R2 p) j (y k) (fun τ => v τ) = levelTrace (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ (singleSeries (R2 p) j ((R2 p).ωP j ((R2 p).mu ((Fm.D x i).plEq w))) ((R2 p).vP j ((R2 p).mu ((Fm.D x i).plEq w))) (h k) (w' k) v)) →
      rdK (rdAt p w j hρ ν) hρ ((Fm.ex x hx i).nch.k' w) z = κ • ∑ k, (e (algebraMap ((Fm.ex x hx i).nch.Oe w) (FractionRing ((Fm.ex x hx i).nch.Oe w)) (a k)) * ν⁻¹) • adForm (R2 p) j (y k) (p.v₀ j (sg0 (Fm.D x i) p.P.A3.A)) := fun _ _ _ _ hAdm hChr =>
  AtTw.imp (AtTw.and hAdm (AtTw.and hChr (AtTw.and GlobalTheory.T.LatticeSmallGeneration GlobalTheory.T.lattice_intersection_at_place))) fun Fm x hx i p hr hm w hw j ⟨a1, a2, a4, a5⟩ ρ hρ ν _ hfit _ e _ h2 z hz =>
    let ⟨c1, c2⟩ := a2 ρ hρ hfit.1
    cx_at GlobalTheory.T.places_bound_tuple GlobalTheory.T.flat_bound_tuple GlobalTheory.T.trace_bound_tuple twQ hr hm hw a1.1 hρ hfit (a4 ρ hρ hfit.1.1) a5 c1 c2 e h2 z hz

end GlobalTheory.BigOn.Exp.TwCx
