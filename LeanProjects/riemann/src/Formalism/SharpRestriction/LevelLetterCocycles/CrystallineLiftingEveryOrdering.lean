import Formalism.SharpRestriction.LevelLetterCocycles.ThmELiftAtOf
import Formalism.SharpRestriction.LevelLetterCocycles.SecondComparisonInCoordinates
import Formalism.SharpRestriction.LevelLetterCocycles.RingConditionOfDeltaInvariants
import Formalism.SharpRestriction.LevelLetterCocycles.FinrankEqOneOfBijective
import Formalism.SharpRestriction.LevelLetterCocycles.PhiItSmul
import Formalism.SharpRestriction.LevelLetterCocycles.FrobeniusCocycleOfRhoData
import Formalism.SharpRestriction.LevelLetterCocycles.RealExtOfExact
import Formalism.SharpRestriction.LevelLetterCocycles.ArcParametersShiftInvariant

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}

structure BrData2 (hR : Ring9 W) (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L) where
  C₁ : Coord W (baseIdOf hR) T₁
  C₂ : Coord W (baseIdOf hR) T₂
  C₀ : Coord W (baseIdOf hR) W.one
  h : CoordHom C₁ C₂ F
  e₀ : C₀.V
  Ks : ℕ → Type
  [ksRing : ∀ s, CommRing (Ks s)]
  [ksAlg : ∀ s, Algebra LL (Ks s)]
  Δ : Type

attribute [instance] BrData2.ksRing BrData2.ksAlg

structure BrProps2 {hR : Ring9 W} {T₁ T₂ : LocLat G Qp LL O} {F : LatHom T₁.L T₂.L}
    (D : BrData2 hR T₁ T₂ F) (e : W.DD W.one) (Cu : Formalism.ExponentWindows.E.Cuts n) (kd : ZMod n → Formalism.ExponentWindows.Kind)
    (bb : ZMod n → ℕ) (j g G₀ Sz η hh : ℕ) : Prop where

  he₀ : ∀ i, D.C₀.t i D.e₀ = (letE i : LetA O n) • e

  arcs : ∀ ϖ : O, Irreducible ϖ → ∀ c ∈ Cu.cuts, Formalism.ExponentWindows.E.FinalArc (latHomOf D.h) c (Cu.ell c)
    (Formalism.ExponentWindows.E.HArc g G₀ Sz η kd bb c) LL D.Ks D.Δ ϖ (W.χΓ W.gam) j
    (Formalism.ExponentWindows.E.parM (baseIdOf hR).Bs.ℓ hh g) g G₀ Sz η (Formalism.ExponentWindows.E.kindAt kd c)
    (Formalism.ExponentWindows.E.sizeAt bb c)

variable [Fintype (K →ₐ[Qp] LL)]

def Realised2 (hR : Ring9 W) (e : W.DD W.one) : Prop :=
  ∀ (T₁ T₂ : LocLat G Qp LL O) (F : LatHom T₁.L T₂.L),
    GoodCoeffs (K := K) (Qp := Qp) (LL := LL) (O := O) (V := T₁.V) →
    CrysLat PD T₁ → CrysLat PD T₂ → F.Onto →
    ∀ (j Gp S η h : ℕ) (ty : ZMod n → LT) (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ)
      (hC : CutsOK n j ty cuts arcLen),
      KindJumps PD T₁ W.emb Gp S η ty →
      (∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₁.ρ τ (Set.Icc (-(h : ℤ)) h)) →
      gPar Gp S η ≤ h → SizesOK (gPar Gp S η) S h ty → ThickLe2 ty cuts arcLen →
      ∃ D : BrData2 hR T₁ T₂ F,
        BrProps2 D e (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h

variable (W) in

structure BrHyp2 (Cc : ℝ) : Prop where

  s_one : W.s = 1

  unram : Function.Bijective (algebraMap K₀ K)

  five_le : 5 ≤ PD.p

  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W

  P6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W

  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W

  herr : Formalism.MainNotions.DeltaInvariantLattices.HerrComplexFirstProperty W

  wx : Formalism.MainNotions.LiftingTheory.coreWX W

  wr : Formalism.MainNotions.LiftingTheory.coreWR W Cc

  tools : ToolsAlg W

  f1 : F1 W

  f2 : F2 W

  hodge : HodgeExact PD LL O

  valRing : ValRing O v

  complete : IsAdicComplete (Ideal.span {(((PD.p : ℕ) : O))}) O

  real : ∃ e : W.DD W.one, UnitGen W e ∧ BKExt W e ∧ ∀ hR : Ring9 W, Realised2 hR e

theorem realised_of {Cc : ℝ} (H : BrHyp2 W Cc) : Realised W := by
    intro T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK hJ hg hS hT hb1 hb2 _
    obtain ⟨e, he, hbk, hreal⟩ := H.real
    have h5 := H.five_le
    have hp2 : PD.p ≠ 2 := by omega
    have hR : Ring9 W := ring_condition_of_delta_invariants (H.P9 T₁ hc₁.2.2.2) H.s_one hp2 (unram_of H.unram)
    obtain ⟨D, P⟩ := hreal hR T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen hC hK hJ hg hS hT
    obtain ⟨-, -, hO, hD, -⟩ := hG
    have := hO
    have := hD
    obtain ⟨ϖ, eO, x, hϖ, hprim, hu⟩ :=
      ground_of hR H.s_one (by omega) H.valRing H.complete
    have hcard : IsUnit ((W.DelF.card : ℕ) : O) :=
      cardΔ_of (not_isUnit_p W H.valRing)
        (card_DelF H.s_one hp2 (unram_of H.unram) (H.P9 T₁ hc₁.2.2.2))
    have Q : LocalWachInputs W (baseIdOf hR) :=
      { s_one := H.s_one
        p_ne_two := hp2
        unram := unram_of H.unram
        P9 := H.P9
        P5 := H.P5
        P6 := H.P6
        tools := H.tools
        p_ne_zero := p_ne_zero_of W
        cardΔ := hcard
        inj := baseIdOf_inj hR
        full := baseIdOf_full hR }
    have hK₂ : ∀ i, JumpsAtE PD T₂ W.emb i ((ty i).win Gp S η) := fun i =>
      kind_quot H.hodge F hc₁ hc₂ hon (hK i)
    have hl₁ := finalLat_of Q hc₁.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK i) Set.subset_union_left) D.C₁
    have hl₂ := finalLat_of Q hc₂.2.2.2 hC hg hS
      (fun i => jumpsAtE_mono (hK₂ i) Set.subset_union_left) D.C₂
    have hunit := primUnit_of (baseIdOf_inj hR) (baseIdOf_full hR) he D.C₀ D.e₀ P.he₀
    refine ⟨{ I := baseIdOf hR, C₁ := D.C₁, C₂ := D.C₂, C₀ := D.C₀, h := D.h, e₀ := D.e₀, ϖ := ϖ,
              eO := eO, u := W.χΓ W.gam, x := x, Ks := D.Ks, Δ := D.Δ }, ?_⟩
    exact
      { irr := hϖ
        prim := hprim
        u_eq := hu
        lat₁ := hl₁
        lat₂ := hl₂
        unit := hunit
        rho := rho_field H.f1 H.f2 hc₁.2.2.2 h hJ (by omega) D.C₁ hl₁.prim.p5M (cutsOf hC) _ j _ _
        ext := fun κ hκ => by
          obtain ⟨R, hE, hses, hY, hrep⟩ :=
            ext_of' he H.hodge hbk hc₂.2.2.2 D.C₂ D.C₀ D.e₀ P.he₀ κ hκ
          exact ⟨R.ext hE, hrep, primExt_of Q H.hodge hC hS hK₂ R hE hses hY D.e₀
            (lift_of' H.unram H.s_one hp2 H.wr H.wx H.hodge R hE hcard hses hY (Mb₁ + hb₁) Mb₂ hb₂ hb2
              D.e₀ (fun i => by rw [hunit.N_eq i]; exact Submodule.mem_span_singleton_self _) hC)⟩
        wprime := wprimeCuts_of' H.unram H.s_one hp2 H.wr H.wx D.h hcard hc₁ hc₂ hon Mb₁ hb₁
          (Mb₂ + hb₂) hb1 hC
        arcs := P.arcs ϖ hϖ }

theorem brHyp_of {Cc : ℝ} (H : BrHyp2 W Cc) (hnat : W.ClKNat) : BrHyp W where
  s_one := H.s_one
  herr := fun T hT => (H.herr T hT).2
  nat := hnat
  real := realised_of H

theorem crystalline_lifting_second_form {Cc : ℝ} (H : BrHyp2 W Cc) : ThmELiftAt PD (O := O) n W.emb v := by
  intro _ h5 T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hK hJ hg hS hC hT hb1 hb2
    hW
  obtain ⟨D, P⟩ := realised_of H T₁ T₂ F hG hc₁ hc₂ hon j Gp S η h ty cuts arcLen Mb₁ hb₁ Mb₂ hb₂ hC hK
    hJ hg hS hT hb1 hb2 hW
  obtain ⟨-, -, hO, hD, hF⟩ := hG
  have := hO
  have := hD
  have hnum := finalNum_of PD.p (by omega) n j Gp S η h ty cuts arcLen (Mb₁ + hb₁) (Mb₂ + hb₂) hC hg hS
    hT hW
  have hnum' : Formalism.ExponentWindows.E.FinalNum D.I.Bs.ℓ (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
      (sigPar PD.p (gPar Gp S η) h j) (rrPar PD.p n (Mb₁ + hb₁) (Mb₂ + hb₂) cuts)
      (kapPar PD.p (gPar Gp S η) h (ellMax cuts arcLen)) (ellMax cuts arcLen) := by
    rw [D.I.ℓ_eq]
    exact hnum
  have hJ₂ : ∀ τ : K →ₐ[Qp] LL, JumpsInV PD T₂.ρ τ (Set.Icc (-(h : ℤ)) h) := fun τ a ha =>
    hJ τ a (H.hodge.1 T₁ T₂ F hc₁ hc₂ hon τ a ha)
  have key := Formalism.ExponentWindows.E.theorem_E_final_form O D.ϖ P.irr D.I.Bs D.eO n (cutsOf hC) (kdOf ty) (bbOf ty) j
    (gPar Gp S η) Gp S η h _ _ _ _ D.u D.x LL D.Ks D.Δ D.C₁.V D.C₂.V D.C₀.V (latOf D.C₁) (latOf D.C₂)
    (latOf D.C₀) D.e₀ (latHomOf D.h) (ZfN D.C₁ F) (Zf D.C₂) ⟨P.prim, P.u_eq, hF⟩ hnum'
    P.lat₁ P.lat₂ P.unit
    ⟨fun m κ hκ => ZfN_smul D.C₁ F m κ hκ,
      rho_fieldN H.f1 H.f2 F hc₁.2.2.2 hc₂.2.2.2 h hJ hJ₂ (by omega) D.C₁ P.lat₁.prim.p5M (cutsOf hC) _ j
        _ _, P.ext⟩ P.wprime P.arcs
  rw [parE_eq_ePar] at key
  exact liftF_ofN D.h H.s_one (by omega) (H.herr T₂ hc₂.2.2.2).2 _ key

theorem crystalline_lifting_every_ordering {Cc : ℝ} (H : BrHyp2 W Cc) (emb : ZMod n → (K₀ →ₐ[Qp] LL)) :
    ThmELiftAt PD (O := O) n emb v := by
  intro hL
  obtain ⟨a, rfl⟩ := exists_rot (PD := PD) W.emb_bij.2 hL.2.2.2.2.1 W.emb_σ
  exact thmELiftAt_rot W.emb a (crystalline_lifting_second_form H) hL

end Formalism.MainNotions.WachCoordinates.Br
