import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckeSupportLattices
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RealPoints
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeSupSt

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def HkSupSized : Prop :=
  ∀ (D : D7), GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.SizeOK D → ∀ (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type)
    (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A),
    R.Char F → ∀ (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec)
      (_fw : FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.ReadAt0 T R κ v₀ i → GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSupAt T R i

def HeckeReadTie : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A)
    (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec),
    R.toLevCh.Is A.μ0 → R.IsGrp F → R.IsFam → R.IsModels → R.IsThP → TieIn T R κ v₀ →
    ∀ (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ), σ = T.σ₀ → ∀ hV : T.V ((i : ℕ) + 1) σ = Wc D i,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T R i σ hV → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.ReadsAt T R i σ hV (κ i)

theorem HeckeReadTie.heckeRead (h : HeckeReadTie) : GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.HeckeRead :=
  fun D G _ _ Pl0 T0 A T _ R F κ v₀ hC t =>
    h D G Pl0 T0 A T R F κ v₀ hC.lev hC.grp hC.fam hC.models hC.thP ⟨t.laws, t.alg_eq, t.kap, t.hv₀, t.chiR, t.x0⟩

def ThetaSpanAll : Prop :=
  ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A),
    GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.ThetaSpan R F

theorem hkSupSized_of_hkSup (h : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.HkSup) : HkSupSized := fun D _ => h D

section Checks

open GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [iA : Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}
  {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem pinned (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (ht : TieIn T R κ v₀) (i : Fin D.R.m) :
    Datum.IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).1
        (Lift.chrTh (R.toLevCh.mu A.μ0) R.eta ((i : ℕ) + 1)).2 (R.ωP i A.μ0) ∧
      Datum.IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) ∧
      T.chiW ((i : ℕ) + 1) T.σ₀ = R.mu0 ((i : ℕ) + 1) ∧ ChrEq (R.mu0 ((i : ℕ) + 1)) (R.C.mu0 i) ∧ R.xiH A.μ0 = 1 ∧
      T.V ((i : ℕ) + 1) T.σ₀ = Wc D i :=
  ⟨hP.ωP i _, (hP.vP i A.μ0).1, chiTie_of_chiR T R ht.alg ht.laws.pins.2.2.1 ht.chiR i, hL.mu0 i, hL.xi_base,
    ht.laws.spaceW _ ⟨Nat.le_add_left _ _, i.2⟩ _ T.toCore.good_σ₀⟩

theorem pin_reads_congr (nW : Fin D.R.m → ℕ)
    (FW : ∀ i, Arith.FormsL D.what₂.LL T.Q.c.F (Fin (nW i) → D.what₂.LL) (fun σ => (R.HW i σ).H) G)
    (mu : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL) → T0)
    (twPl : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers D.what₂.LL))) (kap : ℝ)
    (lam : Fin D.R.m → T0 → A.fam.base.Ix → NumberField.InfinitePlace D.what₂.LL → ℝ)
    (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (w : WeightFamilies.Wt D ((i : ℕ) + 1)) :
    (FramePin T { R with nW := nW, FW := FW, mu := mu, twPl := twPl, kap := kap, lam := lam } i σ hV ↔ FramePin T R i σ hV) ∧
    (ReadsAt T { R with nW := nW, FW := FW, mu := mu, twPl := twPl, kap := kap, lam := lam } i σ hV w ↔ ReadsAt T R i σ hV w) :=
  ⟨Iff.rfl, Iff.rfl⟩

theorem tieIn_const (ht : TieIn T R κ v₀) (c' : ∀ (j : ℕ) (σ : T.Q.c.F →+* ℂ), (T.U j σ).Comp → ℂ)
    (h : ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → CUnit (c' j σ)) :
    @TieIn D G _ _ Pl0 T0 A { T with cE := c' } iA R κ v₀ :=
  @TieIn.mk D G _ _ Pl0 T0 A { T with cE := c' } iA R κ v₀
    ⟨ht.laws.toLawsM, h, ht.laws.muVal, ht.laws.muConj, ht.laws.intAll, ht.laws.modelW, ht.laws.familyUniformisationBasePointOrthogonal, ht.laws.kfHalf,
      ht.laws.adPin⟩ ht.alg ht.kap ht.hv₀ ht.chiR ht.x0

omit iA in

theorem phiW_eq_zero (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {P : Ideal (NumberField.RingOfIntegers D.host.E)} {p k : ℕ} {f g : T.R ((i : ℕ) + 1)}
    {s : T.Q.c.F} (hr : GeoHecke T ((i : ℕ) + 1) P p k s f g) (h0 : s = 0 ∨ f = 0) (h : GA D (Wc D i)) :
    phiW T i σ hV a g h = 0 := by
  have h1 : rdU (T.U ((i : ℕ) + 1) σ) g = 0 := by
    funext c x
    show (open Classical in if hx : x ∈ ((T.U ((i : ℕ) + 1) σ).X c).dom then
      toC (evR _ _ g ((T.U ((i : ℕ) + 1) σ).un c ⟨x, hx⟩)) else 0) = 0
    split_ifs with hx
    · letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
      haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
      refine (hr (CAt σ) ((T.U ((i : ℕ) + 1) σ).un c ⟨x, hx⟩)).trans ?_
      rcases h0 with rfl | rfl
      · rw [map_zero, zero_mul]; rfl
      · rw [← zero_smul T.Q.c.F (0 : T.R ((i : ℕ) + 1)), hkVal_smul, map_zero, zero_mul, mul_zero]; rfl
    · rfl
  show T.phiJ _ σ a g _ = 0
  rw [CoreJ.phiJ, h1, map_zero, smul_zero, Pi.zero_apply]

theorem reads_zero (i : Fin D.R.m) (σ : T.Q.c.F →+* ℂ) (hV : T.V ((i : ℕ) + 1) σ = Wc D i) (w : WeightFamilies.Wt D ((i : ℕ) + 1))
    (P : Formalism.L2.DIV.Pl D.host.E) (p k : ℕ) (Rc : Finset (GA D (Wc D i))) (cq : T.Q.c.F) (f g : T.R ((i : ℕ) + 1))
    (hr : GeoHecke T ((i : ℕ) + 1) P.asIdeal p k (hkScal T.Q.c cq P.asIdeal k D.R.nV) f g) (h0 : cq = 0 ∨ f = 0)
    (h : GA D (Wc D i)) :
    phiW T i σ hV (wtA w) g h = σ cq * (muAt T R i P)⁻¹ ^ k * ∑ a ∈ Rc, phiW T i σ hV (wtA w) f (h * a) := by
  rw [phiW_eq_zero i σ hV _ hr (h0.imp (fun e => by rw [hkScal, e, zero_mul]) id)]
  rcases h0 with rfl | rfl
  · rw [map_zero, zero_mul, zero_mul]
  · have e : ∀ x, phiW T i σ hV (wtA w) 0 x = 0 := fun x => by
      show T.phiJ _ σ _ 0 _ = 0
      rw [CoreJ.phiJ, map_zero, map_zero, smul_zero, Pi.zero_apply]
    simp [e]

end Checks

end GlobalTheory.HeckeSupSt
