import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist Formalism.IndefR.Lev
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

section Lev

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

structure TwLev (R : RealDat D A Ks) (χ : Formalism.L2.Host.HChar D.host.E) (xi : (AE D)ˣ →* Circle) (Q : Finset (Pl D.host.E))
    (xiR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) : Prop where
  xi : ChrEq xi χ
  xi_fin : ∃ n : ℕ, 0 < n ∧ χ.OrderDvd n
  xi_triv : χ.TrivOn D.host.F
  xi_tame : ∀ v, χ.TameAt v
  Q_pl : IsTwistPlaces D.host.g Q
  Q_off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  Q_de : ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    (∀ t, ∀ PP ∈ R.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭) ∧
      ∀ PP ∈ Q, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭
  Q_ram : ∀ PP, ¬ χ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, Formalism.IndefR.Lev.IsConjPl PP' PP
  xiR : ∀ PP ∈ Q, IsRes χ PP (xiR PP)
  roots : ∀ PP ∈ Q, ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  muVal : ∀ (i : Fin D.R.m) (P : Pl0), Bridge.SplitOff (R.pl P) ((R.Sb : Set (Pl D.host.E)) ∪ (Q : Set (Pl D.host.E))) →
    ∃ a : D.what₂.LLˣ, D.what₂.embLL (a : D.what₂.LL) = (((R.C.mu0 i * χ).val (R.pl P) : ℂˣ) : ℂ)
  half : ∀ PP ∈ Q, ∀ PP' ∈ Q, (∃ p : ℕ, p.Prime ∧ (p : 𝓞 D.host.E) ∈ PP.asIdeal ∧ (p : 𝓞 D.host.E) ∈ PP'.asIdeal) →
    PP.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = PP'.asIdeal.comap (algebraMap (𝓞 D.host.K) (𝓞 D.host.E))
  guard : ∀ PP ∈ Q, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

theorem twLev_of_core {R : RealDat D A Ks} {F : Face D A} (hC : GlobalTheory.Hk3.Core R F) (hG : QGuard R) (t : T0) :
    TwLev R (R.xiH t) (R.xi t) (R.Q t) (R.xiR t) where
  xi := hC.lev.xi t
  xi_fin := hC.lev.xi_fin t
  xi_triv := hC.lev.xi_triv t
  xi_tame := hC.lev.xi_tame t
  Q_pl := hC.lev.Q_pl t
  Q_off := hC.lev.Q_off t
  Q_de p hp := by
    obtain ⟨𝔭, h𝔭⟩ := hC.lev.Q_de p hp
    exact ⟨𝔭, h𝔭, h𝔭 t⟩
  Q_ram := hC.lev.Q_ram t
  xiR := hC.lev.xiR t
  roots PP hPP := hC.fam.roots t PP (Or.inr hPP)
  muVal i P hP := by
    obtain ⟨g, c0R, c0L, ht⟩ := hC.fam.tie
    exact ⟨A.muVal i t P, hC.fam.muVal i t P ((ht.ok t P).2 hP)⟩
  half := hG.1 t
  guard := hG.2 t

end Lev

section Laws

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

def Laws (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0))
    (ph : Fin D.R.m → ℂ) (j : Fin D.R.m) (B : Base (Vc D j) (Wc D j)) : Prop :=
  GlobalTheory.Hk3.Core R F ∧ Finite T0 ∧ Nonempty (FWTie T R κ v₀) ∧ IoExt R ∧ QGuard R ∧ OMPins T R κ v₀ O j ∧ PhaseTie T R κ v₀ O ph j ∧
    BaseOf R j B

def Ext (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))
    (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (j : Fin D.R.m)
    {T0' : Type} {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} (R' : RealDat D A' T.Q.c.F)
    (v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec) (O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)) : Prop :=
  (∀ τ, FixBase T R j τ → FixBase T R' j τ) ∧
    (∀ τ ζ Φ Φ', ConjFun (O' j) (κ j) τ ζ Φ Φ' → ConjFun (O j) (κ j) τ ζ Φ Φ') ∧
    (∀ (c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W) (u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ), ExtC R j (inC (O j).c') (O j).c0' c →
      (∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) →
      ∃ (c' : VsV D j ℂ →ₗ[ℂ] (R'.cV j).W) (u' : ∀ ρ, lowT (R'.MW j (sg0 D A')) ρ), ExtC R' j (inC (O' j).c') (O' j).c0' c' ∧
        (∀ ρ, (u' ρ : (R'.MW j (sg0 D A')).sm ρ) = v₀' j (sg0 D A') ρ) ∧
        ∀ x, R'.ioP j (PiTensorProduct.tprod ℂ u') (c' x) = R.ioP j (PiTensorProduct.tprod ℂ u) (c x))

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)} {j : Fin D.R.m}

theorem Ext.refl : Ext T R κ v₀ O j R v₀ O :=
  ⟨fun _ h => h, fun _ _ _ _ h => h, fun c u hc hu => ⟨c, u, hc, hu, fun _ => rfl⟩⟩

theorem Ext.trans {T1 T2 : Type} {A1 : FamIn D.what₂.LL G Pl0 T1 D.R.m} {A2 : FamIn D.what₂.LL G Pl0 T2 D.R.m}
    {R1 : RealDat D A1 T.Q.c.F} {R2 : RealDat D A2 T.Q.c.F} {v1 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R1.MW i σ).Vec}
    {v2 : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R2.MW i σ).Vec} {O1 : ∀ i, OMDat T.toCore R1 i Unit (fun _ => A1.μ0)}
    {O2 : ∀ i, OMDat T.toCore R2 i Unit (fun _ => A2.μ0)} (h1 : Ext T R κ v₀ O j R1 v1 O1) (h2 : Ext T R1 κ v1 O1 j R2 v2 O2) :
    Ext T R κ v₀ O j R2 v2 O2 := by
  refine ⟨fun τ h => h2.1 τ (h1.1 τ h), fun τ ζ Φ Φ' h => h1.2.1 τ ζ Φ Φ' (h2.2.1 τ ζ Φ Φ' h), fun c u hc hu => ?_⟩
  obtain ⟨c1, u1, hc1, hu1, e1⟩ := h1.2.2 c u hc hu
  obtain ⟨c2, u2, hc2, hu2, e2⟩ := h2.2.2 c1 u1 hc1 hu1
  exact ⟨c2, u2, hc2, hu2, fun x => (e2 x).trans (e1 x)⟩

theorem hasTuples_of_laws {ph : Fin D.R.m → ℂ} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle} {T0' : Type}
    {A' : FamIn D.what₂.LL G Pl0 T0' D.R.m} {R' : RealDat D A' T.Q.c.F} {F' : Face D A'}
    {v₀' : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R'.MW i σ).Vec} {O' : ∀ i, OMDat T.toCore R' i Unit (fun _ => A'.μ0)}
    (hL : Laws T R' F' κ v₀' O' ph j B) (hE : Ext T R κ v₀ O j R' v₀' O') {t t' : T0'} (ht : IsTupOf R' B ψ t)
    (ht' : IsTupOf R' B ψ' t') : HasTuples T R κ v₀ O ph j B ψ ψ' :=
  ⟨T0', A', R', F', v₀', O', hL.1, hL.2.1, hL.2.2.1, hL.2.2.2.1, hL.2.2.2.2.1, hL.2.2.2.2.2.1, hL.2.2.2.2.2.2.1, hL.2.2.2.2.2.2.2,
    hE.1, hE.2.1, hE.2.2, t, t', ht, ht'⟩

end Laws

section Point

open Classical in

def TwLevAt : Prop := AtTw fun Fm x hx i p w j => ∀ ρ ρ' : Setup (Fm.D x i).ntw, ρ.Good → ρ'.Good → RealPin p.R p.cG ρ →
  SameBut ρ ρ' → (Adapted p w ρ ∨ Adapted p w ρ') →
  ∃ (χ χ' : Formalism.L2.Host.HChar (Fm.D x i).host.E) (xiR xiR' : ∀ PP : Pl (Fm.D x i).host.E, (kP PP)ˣ →* ℂˣ),
    TwLev p.R.toRealDat χ ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ).Q) xiR ∧
    TwLev p.R.toRealDat χ' ((baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)
      ((baseW (Fm.ex x hx i) w j ρ).de.Q ∪ (twW (Fm.ex x hx i) w ρ').Q) xiR' ∧
    χ ≠ 1 ∧ χ' ≠ 1 ∧ (χ ≠ χ' ∨ (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ).chi =
      (baseW (Fm.ex x hx i) w j ρ).de.chi * (twW (Fm.ex x hx i) w ρ').chi)

end Point

end GlobalTheory.BigOn.Exp.TwConj
