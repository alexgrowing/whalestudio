import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConjTupRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisConjDefiniteFormsSemilinearEquivStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOpOfTranslates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntValuationEqOfMem
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ConjDesc

set_option maxHeartbeats 1600000 in

theorem vals : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (a : Tp) (x₀ : A.fam.amb.FL i (tup a)) (h : GA D (Vc D i)), ∃ x : VsV D i M.c'.F, (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC i Tp tup M hP a x₀ h
  obtain ⟨_, _, _, hT, hc⟩ := hP.lift.c0
  obtain ⟨x, hx⟩ := GlobalTheory.RationalValues.placeEx R i M.jL (inC M.c') (tup a) (fun _ : Unit => h) M.c0' hC.models.jV hT hc hC.lev
    hC.grp.chiW hC.fam.pl_onto hC.fam.muVal x₀
  exact ⟨x (), hx ()⟩

set_option maxHeartbeats 1600000 in

theorem c_inj : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → Function.Injective c := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ i Tp tup M hP c hc
  obtain ⟨gramR, c0R, c0L, hFT, hC0⟩ := hP.lift.c0
  have hfield : (inC M.c').comp M.jL = D.what₂.embLL := hP.lift.field
  have hbas : ∀ j, c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) =
      c0L i (bVV D.what₂.LL (lamV D i) j) := fun j => by
    obtain ⟨v', hv', hcv'⟩ := hC0 (bVV D.what₂.LL (lamV D i) j)
    refine (hc v' _ ?_).trans hcv'
    rw [GlobalTheory.CoefModel.mapVV_coe, hv', MvPolynomial.map_map, hfield]
  have hli : LinearIndependent ℂ fun j => c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) := by
    have h := (hFT.mapL i).2.1
    simp only [← hbas] at h
    exact h
  have hli0 := GlobalTheory.CoefModel.linearIndependent_mapVV D.what₂.embLL (lamV D i)
  have hsp0 := GlobalTheory.CoefModel.span_mapVV D.what₂.embLL (lamV D i)
  let B := Module.Basis.mk hli0 hsp0.ge
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro z hz
  have hs := B.sum_repr z
  have h0 : ∑ j, B.repr z j • c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) (bVV D.what₂.LL (lamV D i) j)) = 0 := by
    calc _ = c (∑ j, B.repr z j • B j) := by
            rw [map_sum]
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [map_smul, Module.Basis.mk_apply]
      _ = 0 := by rw [hs, hz]
  have hc0 := Fintype.linearIndependent_iff.1 hli _ h0
  rw [← hs]
  exact Finset.sum_eq_zero fun j _ => by rw [hc0 j, zero_smul]

set_option maxHeartbeats 4000000 in

theorem conj_desc : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), GlobalTheory.Hk3.Core R F → Nonempty (FWTie T R κ v₀) → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (M : OMDat T.toCore R i Tp tup), M.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) M.s0) → ∀ (τ : ℂ ≃+* ℂ) (ta : M.c'.F ≃+* M.c'.F), (∀ a : M.c'.F, ((ta a : M.c'.F) : ℂ) = τ (a : ℂ)) → FixBase T R i τ → ∀ (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W), ExtC R i (inC M.c') M.c0' c → (∀ t x, ((R.xi (tup t) x : Circle) : ℂ) ∈ M.c'.F) → ∀ a b : Tp, ConjTup R τ (tup a) (tup b) → ∀ (y : (R.HV i (tup a)).H) (y' : (R.HV i (tup b)).H), ConjForm R i τ c (tup a) (tup b) y y' → ∃ (n : ℕ) (α : Fin n → ℂ) (ys : Fin n → (R.HV i (tup a)).H) (ys' : Fin n → (R.HV i (tup b)).H), y = ∑ k, α k • ys k ∧ y' = ∑ k, τ (α k) • ys' k ∧ ∀ k (h : GA D (Vc D i)), ∃ x x' : VsV D i M.c'.F, (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank) ∧ (R.HV i (tup a)).e (ys k) (fin _ h) = M.c0' x ∧ (R.HV i (tup b)).e (ys' k) (fin _ h) = M.c0' x' := by
  intro D G _ _ Pl0 T0 A T _ R F κ v₀ hC hFW i Tp tup M hP τ ta hta hFix c hc hxi a b hab y y' hy
  obtain ⟨φ, hφs, hφ⟩ := GlobalTheory.T.exists_galoisConj_definiteForms_semilinearEquiv D G Pl0 T0 A T R F κ v₀ hC hFW i Tp tup M hP c hc τ (tup a) (tup b) hFix hab
  have hy' : y' = φ y := (hφ y y').1 hy
  have hmem : y ∈ Submodule.span ℂ (Set.range (R.jV i (tup a))) := by
    rw [GlobalTheory.HeckeClassSums.span_jV hC.models.HV hC.models.jV i (tup a)]; exact Submodule.mem_top
  obtain ⟨n, α, g, hg⟩ := Submodule.mem_span_set'.1 hmem
  have hinj := c_inj D G Pl0 T0 A T R κ v₀ i Tp tup M hP c hc
  refine ⟨n, α, fun k => (g k : (R.HV i (tup a)).H), fun k => φ (g k : (R.HV i (tup a)).H), hg.symm, ?_, ?_⟩
  · subst hy' hg
    exact (map_sum φ _ _).trans (Finset.sum_congr rfl fun k _ => hφs _ _)
  · intro k h
    have hk : ∃ x₀ : A.fam.amb.FL i (tup a), R.jV i (tup a) x₀ = (g k : (R.HV i (tup a)).H) := (g k).2
    obtain ⟨x₀, hx₀⟩ := hk
    have hv := vals D G Pl0 T0 A T R F κ v₀ hC i Tp tup M hP
    have hv2 := hv a x₀ h
    let x := hv2.choose
    have hx : (R.HV i (tup a)).e (jVx R i (tup a) x₀) (fin _ h) = M.c0' x := hv2.choose_spec
    have hx' : ((g k : (R.HV i (tup a)).H)) = jVx R i (tup a) x₀ := hx₀.symm
    have hcf := (hφ (g k : (R.HV i (tup a)).H) (φ (g k))).2 rfl h
    let x1 := hcf.choose
    let x1' := hcf.choose_spec.choose
    have hcv : ConjVec i τ x1 x1' := hcf.choose_spec.choose_spec.1
    have h1 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = c x1 := hcf.choose_spec.choose_spec.2.1
    have h1' : (R.HV i (tup b)).e (φ (g k : (R.HV i (tup a)).H)) (fin _ h) = c x1' := hcf.choose_spec.choose_spec.2.2
    let xC : VsV D i ℂ := GlobalTheory.CoefModel.mapVV (inC M.c') (lamV D i) x
    have hxC : c xC = M.c0' x := hc x xC rfl
    have e0 : (R.HV i (tup a)).e (g k : (R.HV i (tup a)).H) (fin _ h) = M.c0' x := by rw [hx']; exact hx
    have e1 : c x1 = c xC := h1.symm.trans (e0.trans hxC.symm)
    have hx1 : x1 = xC := hinj e1
    let x' : VsV D i M.c'.F := ⟨MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank),
      GlobalTheory.Proof.TensorMapDescent.map_mem_VV (ta : M.c'.F →+* M.c'.F) (lamV D i) _ x.2⟩
    have hcomp : (τ : ℂ →+* ℂ).comp (inC M.c') = (inC M.c').comp (ta : M.c'.F →+* M.c'.F) := by
      ext z; exact (hta z).symm
    have hx1' : (x1' : Pol ℂ D.what₂.Tau (Vc D i).rank) = MvPolynomial.map (inC M.c') (x' : Pol M.c'.F D.what₂.Tau (Vc D i).rank) := by
      rw [hcv, hx1]
      show MvPolynomial.map (τ : ℂ →+* ℂ) (MvPolynomial.map (inC M.c') (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank)) =
        MvPolynomial.map (inC M.c') (MvPolynomial.map (ta : M.c'.F →+* M.c'.F) (x : Pol M.c'.F D.what₂.Tau (Vc D i).rank))
      rw [MvPolynomial.map_map, MvPolynomial.map_map, hcomp]
    exact ⟨x, x', rfl, e0, h1'.trans (hc x' x1' hx1')⟩

end GlobalTheory.ConjDesc
