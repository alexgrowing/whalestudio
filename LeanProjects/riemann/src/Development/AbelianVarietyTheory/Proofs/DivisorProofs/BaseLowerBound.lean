import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondLinkOfWeightRowsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGenerationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelRationalityAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceRationalityAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDatumSeriesUnitTimesKernelSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CentralElementMovesCoefficientLatticeByPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KernelTraceAlgebraicAtLowestTypesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIntersectionAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComparisonReadableAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OwnPrimeIsUnitAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IteratedDerivativeSubmoduleStableStatement

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.SerBase

theorem exists_of_integral {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (e : FractionRing O →+* ℂ) {N : ℕ}
    (hN : IsUnit (N : O)) {b : FractionRing O} {k : ℕ} (h : IsIntegral ℤ ((N : ℂ) ^ k * e b)) :
    ∃ o : O, algebraMap O (FractionRing O) o = b := by
  have h1 : IsIntegral O ((N : FractionRing O) ^ k * b) := by
    obtain ⟨f, hf, h0⟩ := h
    refine ⟨f.map (Int.castRingHom O), hf.map _, e.injective ?_⟩
    rw [Polynomial.eval₂_map, Polynomial.hom_eval₂, map_zero, map_mul, map_pow, map_natCast, ← h0]
    congr 1
    exact RingHom.ext_int _ _
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h1
  obtain ⟨u, hu⟩ := hN.pow k
  refine ⟨(u⁻¹ : Oˣ) * y, ?_⟩
  have e2 : algebraMap O (FractionRing O) (u⁻¹ : Oˣ) * (N : FractionRing O) ^ k = 1 := by
    rw [← map_natCast (algebraMap O (FractionRing O)), ← map_pow, ← hu, ← map_mul, Units.inv_mul, map_one]
  rw [map_mul, hy, ← mul_assoc, e2, one_mul]

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (w : D.what₂.places.Pl) (j : Fin D.R.m)

theorem tmul_mem_realBase (hL : Links2 p) (h1 : KerOf p w j) (h2 : TraceOf p w j) (h3 : KerRat p w j) (h4 : LatIo p w j)
    (h5 : ReadCmp p w j) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ}
    {rd : Can p w j} (hfit : Fit p w j hρ ν) (hcan : IsCan p rd) {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j))
    {Q : PolF D (Wc D j).rank (Vc D j).rank} (hQ : Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h)
    {g : D.nexp.Fm (ex.nch.twI w) ((j : ℕ) + 1) (ex.nch.sd w)}
    (hg : rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q) :
    ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd := by
  classical
  have hcore : GlobalTheory.Hk3.Core (R2 p) (F2 p) := ⟨hL.1.lev, hL.1.grp, hL.1.fam, hL.1.models, hL.1.chain, hL.1.thP⟩
  have hguard : QGuard (R2 p) := p.qGuard
  obtain ⟨hpin, e, he1, he2⟩ := hfit.adapted
  obtain ⟨hν, c, hsc, n, hn, hνc⟩ := hfit.norm
  rw [p.phsOne j, map_one, one_mul] at hνc
  have hc : c ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at hνc
    exact hν ((pow_eq_zero_iff hn).1 hνc)
  obtain ⟨hBo, hQ', ξR, φ, hk⟩ := h1 ρ hρ hpin
  obtain ⟨u, hu, hio⟩ := h4 ρ hρ hpin c hc hsc
  obtain ⟨y, hy, hyio⟩ := hio h hh Q hQ
  have hU := hO D ex.nch w
  have hN0 : ownAt D (D.plEq w) ≠ 0 := fun h0 => by
    rw [h0, Nat.cast_zero] at hU
    exact not_isUnit_zero hU
  have hNC : ((ownAt D (D.plEq w) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hN0
  have hpl : ∀ PP ∈ plW p w, ((ownAt D (D.plEq w) : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := fun PP hPP => (Finset.mem_filter.1 hPP).2
  obtain ⟨z, cA, hz, hcA, hser⟩ := hF D _ _ _ _ _ (R2 p) (F2 p) hcore hguard j (p.pins j).2.lift.std _ (hρ.base _ j _) hBo _ ξR _ φ
    (by rw [hQ']; exact hk) ⟨_, by rw [hQ']; exact Finset.filter_subset _ _⟩ _ hN0 (by rw [hQ']; exact hpl)
  obtain ⟨m, hm⟩ := hC D _ _ _ _ _ (R2 p) j _ z hz _ hN0 (by rw [hQ']; exact hpl)
  have hhz : h * z ∈ GfC (Vc D j) := mul_mem hh hz.2.1
  have hy' := (hm h hh y).1 hy
  obtain ⟨x, hx⟩ := h3 _ _ _ _ hk (h * z) hhz _ hy' u hu
  obtain ⟨x', hx'⟩ := hTr D _ _ _ _ _ (R2 p) (F2 p) hcore hL.2.2.1 j (p.v₀ j _) ((fw2 p).hv₀ j _).1 _ _ _ _ _ _ hk
    (F2 p).P0 (F2 p).ψ0⁻¹ (h * z) _ u hu x hx
  have hmem : x' ∈ thetaBase (R2 p) j (F2 p).P0 (F2 p).ψ0⁻¹ 1 (D.plEq w) (ownAt D (D.plEq w)) :=
    Submodule.subset_span ⟨_, φ, hk.isKernel, h * z, hhz, _, hy', fun v => by rw [one_smul]; exact hx' v⟩
  have hs0 : ∀ y', series (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).F (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z)
      ((R2 p).ioP j (PiTensorProduct.tprod ℂ u) y') =
        singleSeries (R2 p) j (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) φ (h * z) y' u := fun y' => by
    funext g'
    rw [series_apply, hBo.fock_eq]
    rfl
  have hs := hs0 (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m • y)
  rw [map_smul, hyio, map_smul, map_smul, smul_smul] at hs
  have key : rdAt p w j hρ ν g = (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) • ν⁻¹ •
      adForm (R2 p) j x' (fun τ => u τ) := by
    rw [hg, h2 ρ hρ hpin hfit.level h Q, hser, map_smul, hx' u, ← hs, map_smul, smul_smul, smul_smul]
    congr 1
    field_simp
  rcases h5 ρ hρ e he1 he2 ν hν rd hcan u hu g x' _ key with rfl | ⟨b, hb, hgb⟩
  · rw [TensorProduct.tmul_zero]
    exact zero_mem _
  · obtain ⟨-, k, hk1, -⟩ := hcA
    have hζ : IsIntegral ℤ (ν / c) := IsIntegral.of_pow (Nat.pos_of_ne_zero hn) (by
      rw [div_pow, hνc, div_self (pow_ne_zero _ hc)]
      exact isIntegral_one)
    obtain ⟨o, ho⟩ := exists_of_integral e hU (b := b) (k := k + m) (by
      have e3 : ((ownAt D (D.plEq w) : ℕ) : ℂ) ^ (k + m) * (cA * (ν / c) * (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ m)⁻¹) =
          (((ownAt D (D.plEq w) : ℕ) : ℂ) ^ k * cA) * (ν / c) := by
        rw [pow_add]
        field_simp
      rw [hb, e3]
      exact hk1.mul hζ)
    rw [hgb, ← ho, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨x', hmem, rfl⟩)

theorem baseLat_le_realBase {ρ : Setup D.ntw} {hρ : ρ.Good} {ν : ℂ} {rd : Can p w j} (hfit : Fit p w j hρ ν)
    (hinj : Function.Injective (rdAt p w j hρ ν))
    (hgen : ∀ (h : GA D (Vc D j)) (P : PolF D (Wc D j).rank (Vc D j).rank),
      P ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range h →
      P ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
        (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)))
    (hsm : ∀ h ∈ GfC (Vc D j), ∀ Q ∈ ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h, ∀ g,
      rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q →
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g : Tgt ex w j) ∈ realBase p rd) :
    baseLat p w j hρ ν ≤ realBase p rd := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, ⟨s, h, P, hd, hf⟩, rfl⟩
  have key : ∀ Q ∈ Submodule.span (ρ.eO (ex.nch.twI w) (ex.nch.sd w)).range
      (ρ.lat (ex.nch.twI w) j (ex.nch.sd w) (smallInt D) h : Set (PolF D (Wc D j).rank (Vc D j).rank)),
      ∃ g, rdAt p w j hρ ν g = ρ.theta (ex.nch.twI w) j (ex.nch.sd w) h Q ∧
        ((1 : FractionRing (ex.nch.Oe w)) ⊗ₜ[D.ntw.O (ex.nch.twI w)] g) ∈ realBase p rd := by
    intro Q hQ
    induction hQ using Submodule.span_induction with
    | mem Q hQ =>
      obtain ⟨g, hg⟩ := hfit.rat.1 s h Q ⟨hd.split, hd.off, hd.fin, hd.supp, lat_mono ρ _ j _ (smallInt_le hρ _ _) h hQ⟩
      exact ⟨g, hg, hsm h hd.fin Q hQ g hg⟩
    | zero =>
      refine ⟨0, ?_, by rw [TensorProduct.tmul_zero]; exact zero_mem _⟩
      rw [map_zero]
      exact (map_zero _).symm
    | add Q1 Q2 _ _ h1 h2 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨g2, e2, m2⟩ := h2
      refine ⟨g1 + g2, ?_, by rw [TensorProduct.tmul_add]; exact add_mem m1 m2⟩
      rw [map_add, e1, e2]
      exact (map_add _ _ _).symm
    | smul a Q _ h1 =>
      obtain ⟨g1, e1, m1⟩ := h1
      obtain ⟨o, ho⟩ := a.2
      refine ⟨o • g1, ?_, by rw [TensorProduct.tmul_smul]; exact Submodule.smul_of_tower_mem _ o m1⟩
      rw [rd_smul, e1]
      change _ = (ρ.B (ex.nch.twI w) j (ex.nch.sd w)).theta (ρ.om (ex.nch.twI w) j (ex.nch.sd w) 1) h ((a : ℂ) • Q)
      rw [map_smul, ← ho]
  obtain ⟨g, hg, hm⟩ := key P (hgen h P hd.mem)
  have e : f = g := hinj (hf.trans hg.symm)
  rw [e]
  exact hm

end Point

theorem baseGe_of_steps (hI : ReadInj) (hG : LatSmallGen) (h1 : KerOfAt) (h2 : TraceOfAt) (h3 : KerRatAt) (h4 : LatIoAt)
    (h5 : ReadCmpAt) (hF : FlatKer) (hC : CentLat) (hTr : TraceRat) (hO : OwnUnit) : BaseGe := by
  unfold BaseGe AtFit ReadInj LatSmallGen KerOfAt TraceOfAt KerRatAt LatIoAt ReadCmpAt AtTw AtPts at *
  refine ((((((Formalism.MainNotions.Closed.and hI hG).and h1).and h2).and h3).and h4).and h5).imp fun Fm CH _ H => ?_
  obtain ⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩ := H
  obtain ⟨x0, hx0⟩ := (((((a1.and a2).and a3).and a4).and a5).and a6).and a7
  refine ⟨x0, fun x hx hle i p hp hm w hw j ρ hρ ν rd hfit hcan => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨b1, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := hx0 x hx hle i p hp
  exact baseLat_le_realBase p w j hfit (b1 hm w hw j ρ hρ ν hfit.norm.1) (b2 hm w hw j ρ hρ hfit.pin) fun h hh Q hQ g hg =>
    tmul_mem_realBase p w j (GlobalTheory.T.second_link_of_weight_rows _ _ _ _ _ _ _ _ _ _ p hp hm.1) (b3 hm w hw j) (b4 hm w hw j) (b5 hm w hw j)
      (b6 hm w hw j) (b7 hm w hw j) hF hC hTr hO hfit hcan hh hQ hg

end GlobalTheory.BigOn.Exp.SerBase

namespace GlobalTheory.BigOn.Exp

theorem baseGe_of : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
    GlobalTheory.SerStd.SeriesRatS → BaseGe := fun hP hA hR hS =>
  SerBase.baseGe_of_steps GlobalTheory.T.ReadInjective GlobalTheory.T.LatticeSmallGeneration GlobalTheory.T.kernel_rationality_at_place GlobalTheory.T.trace_rationality_at_place (GlobalTheory.T.kernel_rationality_of_reciprocity hP hA hR hS) GlobalTheory.T.lattice_intersection_at_place GlobalTheory.T.lagrangian_set_additive_subgroup
    GlobalTheory.T.flatDatum_series_unit_times_kernel_series GlobalTheory.T.central_element_moves_coefficient_lattice_by_prime_pow GlobalTheory.T.kernelTrace_algebraic_at_lowestTypes GlobalTheory.T.ownPrime_isUnit_at_place

end GlobalTheory.BigOn.Exp
