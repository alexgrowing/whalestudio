import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TraceLatticeLeThetaLatticeAtPlace
import Formalism.LocalToGlobal.IndefiniteReal.ThPinsR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.OnCmp

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)

abbrev DatFn (D : D7) (i : Fin D.R.m) : Type :=
  (∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) → ℂ

abbrev IsWeilTw (χ : (AE D)ˣ →* Circle) (ω : WeilRep D i) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).1
    (Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 ω

open Classical in

def VecOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop :=
  IsVacO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.vacP i) ∧
    ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧
      IsThetaAt R.ψ (symplO (Vc D i) (Wc D i)) (heisO R.ψ (Vc D i) (Wc D i)) (cA D e)
        (latO (Vc D i) (Wc D i) (R.ΛV i) (R.ΛW i) fun _ => True) 1 (R.vacP i)
        (fun x => if IsHalf (cA D e) x ∧ IsIntM (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x) then
          Ω (fun PP => redM PP (frMapAdj (Vc D i) (Wc D i) (R.βV i) (R.βW i) x)) else 0) φ

open Classical in

def PhiOf (Q : Finset (Pl D.host.E)) (Ω : DatFn D i) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La]
    (ι : La →ₗ[𝓞 D.host.E] (Fin (Wc D i).rank → D.host.E)) (N : Submodule (𝓞 D.host.E) La)
    (φ : (Fin (Vc D i).rank → La ⧸ N) → ℂ) : Prop :=
  ∃ e : AE D, IsIdemSum e (R.Pg ∪ Q) ∧ ∀ x : Fin (Vc D i).rank → La,
    IsIntM (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)) ∧
    φ (fun b => Submodule.Quotient.mk (x b)) =
      Ω (fun PP => redM PP (uMat (Vc D i) (Wc D i) (R.βV i) (R.βW i) e fun b => ι (x b)))

def ReadsOnly {i : Fin D.R.m} (S : Finset (Pl D.host.E)) (Ω : DatFn D i) : Prop :=
  ∀ y y', (∀ PP ∈ S, y PP = y' PP) → Ω y = Ω y'

open Classical in

def omegaFree (Q : Finset (Pl D.host.E)) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (y₀ : ∀ PP : Pl D.host.E, Matrix (Fin (Vc D i).rank) (Fin (Wc D i).rank) (kP PP)) : DatFn D i := fun y =>
  (if ∀ PP ∈ R.Pg, y PP = y₀ PP then 1 else 0) *
    if h : ∀ PP ∈ Q, IsUnit (topL (Wc D i).rank (y PP)).det then ∏ PP ∈ Q.attach, (((ξR PP.1 (h PP.1 PP.2).unit)⁻¹ : ℂˣ) : ℂ) else 0

structure KerDat (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ)
    (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ) : Prop where
  chr : ChrEq χ ξ
  fin : ∃ n : ℕ, 0 < n ∧ ξ.OrderDvd n
  triv : ξ.TrivOn D.host.F
  tame : ∀ v, ξ.TameAt v
  pl : IsTwistPlaces D.host.g Q
  off : ∀ PP ∈ Q, ((D.host.QS * D.host.q * D.host.d * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal
  ram : ∀ PP, ¬ ξ.UnrAt PP ↔ PP ∈ Q ∨ ∃ PP' ∈ Q, IsConjPl PP' PP
  res : ∀ PP ∈ Q, IsRes ξ PP (ξR PP)
  weil : IsWeilTw R i χ ω
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
    R.Pg Q ξR (R.vacP i) φ

variable {R i}

theorem KerDat.isKernel {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) : IsKernel R i ξ Q ω φ :=
  ⟨χ, ξR, h.chr, h.res, h.weil, h.vec⟩

theorem KerDat.vecOf {ξ χ ξR Q ω φ} (h : KerDat R i ξ χ ξR Q ω φ) :
    VecOf R i Q (fun y => omegaK R.Pg y * omegaQ Q (Wc D i).rank ξR (-1) y) φ := h.vec

theorem kerDat_tuple (hL : R.toLevCh.Is A.μ0) (hP : R.IsThP) (t : T0) :
    KerDat R i (R.xiH t) (R.xi t) (R.xiR t) (R.Q t) (R.ωP i t) (R.vP i t) :=
  ⟨hL.xi t, hL.xi_fin t, hL.xi_triv t, hL.xi_tame t, hL.Q_pl t, fun PP h => (hL.Q_off t PP h).1, hL.Q_ram t, hL.xiR t,
    hP.ωP i t, hP.vP i t⟩

end GlobalTheory.OnCmp

end
