import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadingInjective

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwInputs.Move
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open Formalism.L2.Host (embLL0 CharFrame)
open GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.L2 (NExpTied)
open Formalism.AUTREP (GAf)
open GlobalTheory.HeightCounting GlobalTheory.HeightCounting.SideCopy GlobalTheory.TwInputs.Move.Forms

namespace GlobalTheory.HeightCounting.SerCarry

variable {D D' : D7} {ι : D.what₂.LL →+* D'.what₂.LL} {e : ↥D'.LL0 ≃+* ↥D.LL0}

def KeepsMat {D : D7} (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) : Prop :=
  ∃ hF : D.host.F = maximalRealSubfield D.host.E, ∀ i : Fin D.R.m, ∃ hn : (Vc D i).rank = D.R.nV, ∀ κ a b,
    finMat D.sp.cm.sig (Vc D i).gram (p i κ) a b = (GlobalTheory.Mem.R3.swapCast hF).symm
      ((κ.1 : Matrix (Fin D.R.nV) (Fin D.R.nV) (ReciprocityTheory.Aut.AL D.host.E)) (Fin.cast hn a) (Fin.cast hn b))

theorem keepsMat_heq_refl (D : D7) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D j')).rangeRestrict (p' j' g) := by
  rintro p p' ⟨hF, hp⟩ ⟨hF', hp'⟩ j j' hj
  cases Fin.ext hj
  obtain ⟨hn, hp⟩ := hp j
  obtain ⟨hn', hp'⟩ := hp' j
  exact heq_of_eq (funext fun g => Subtype.ext (Units.ext (Matrix.ext fun a b => (hp g a b).trans (hp' g a b).symm)))

theorem keepsMat_heq (h : CopyTw D D' ι e) : ∀ (p : ∀ i : Fin D.R.m, GAf D.host.E D.R.nV → GA D (Vc D i)) (p' : ∀ i : Fin D'.R.m, GAf D'.host.E D'.R.nV → GA D' (Vc D' i)),
    KeepsMat p → KeepsMat p' → ∀ (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' →
    HEq (fun g => (finHom (Vc D j)).rangeRestrict (p j g)) fun g => (finHom (Vc D' j')).rangeRestrict (p' j' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((keepsMat_heq_refl D) :))

theorem low_copy_refl (D : D7) : (LowIn D → LowIn D) ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) := by
  refine ⟨id, fun _ _ hb H => ?_, id⟩
  subst hb; exact H

theorem low_copy (h : CopyTw D D' ι e) : (LowIn D → LowIn D') ∧
    (∀ (bad : D.ntw.Tw → ℕ) (bad' : D'.ntw.Tw → ℕ), HEq bad bad' → (∀ i, bad i = normProd (D.ntw.S0 i)) →
      ∀ i, bad' i = normProd (D'.ntw.S0 i)) ∧
    ((∀ i j b, ¬ (1 ≤ j ∧ j ≤ D.R.m) → Subsingleton (D.nexp.Fm i j b)) →
      ∀ i j b, ¬ (1 ≤ j ∧ j ≤ D'.R.m) → Subsingleton (D'.nexp.Fm i j b)) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((low_copy_refl D) :))

theorem pq_copy_refl (D : D7) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D.ntw.Tw → Set (Pl D.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D Pq' (D.ntw.pD i')) := by
  refine fun Pq Pq' hPq => ⟨fun _ _ hc H => ?_, fun i k Q ψ => ?_⟩
  · subst hPq; subst hc; exact H
  · subst hPq; exact ⟨i, Q, ψ, .rfl, .rfl, .rfl, .rfl, .rfl⟩

theorem pq_copy (h : CopyTw D D' ι e) : ∀ (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host)
      (Pq' : HeightOneSpectrum (𝓞 (maximalRealSubfield D'.host.E)) → PlE D'.host), HEq Pq Pq' →
      (∀ (ch : D.ntw.Tw → Set (Pl D.host.E)) (ch' : D'.ntw.Tw → Set (Pl D'.host.E)), HEq ch ch' →
        (∀ i P, IsSplitPl D.host P → (P ∈ ch i ↔ P ∈ Set.range Pq)) → ∀ i P, IsSplitPl D'.host P → (P ∈ ch' i ↔ P ∈ Set.range Pq')) ∧
      ∀ (i' : D'.ntw.Tw) (k : ℕ) (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ),
        ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
          HEq (NX.qpOf D Pq Q) (NX.qpOf D' Pq' Q') ∧ HEq (NX.qpOf D Pq (D.ntw.pD i)) (NX.qpOf D' Pq' (D'.ntw.pD i')) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((pq_copy_refl D) :))

theorem join_copy_refl (D : D7) : ∀ (i' : D.ntw.Tw) (j : Fin D.R.m) (j' : Fin D.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D.host)) (ψ' : G D.host.E D.nd.Om →* (D.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D (Wc D j').rank (Vc D j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D (Wc D j').rank (Vc D j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D j') → PolF D (Wc D j').rank (Vc D j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  intro i j j' hj b k Q ψ hT
  cases Fin.ext hj
  refine ⟨i, Q, ψ, .rfl, .rfl, .rfl, hT, rfl, .rfl, .rfl, fun _ _ hek => ?_⟩
  subst hek
  refine ⟨.rfl, fun _ _ hr _ _ hp => ?_⟩
  subst hr; subst hp
  rfl

theorem join_copy (h : CopyTw D D' ι e) : ∀ (i' : D'.ntw.Tw) (j : Fin D.R.m) (j' : Fin D'.R.m), (j : ℕ) = j' → ∀ (b : Bool) (k : ℕ)
    (Q' : Finset (PlE D'.host)) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), TwOK i' k Q' ψ' →
    ∃ (i : D.ntw.Tw) (Q : Finset (PlE D.host)) (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ), HEq i i' ∧ HEq Q Q' ∧ HEq ψ ψ' ∧
      TwOK i k Q ψ ∧ PolF D (Wc D j).rank (Vc D j).rank = PolF D' (Wc D' j').rank (Vc D' j').rank ∧
      HEq (inferInstance : AddCommGroup (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : AddCommGroup (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      HEq (inferInstance : Module ℂ (PolF D (Wc D j).rank (Vc D j).rank))
        (inferInstance : Module ℂ (PolF D' (Wc D' j').rank (Vc D' j').rank)) ∧
      ∀ (ek : ∀ i, Bool → ∀ k, FractionRing (D.ntw.Ok i k) →+* ℂ) (ek' : ∀ i, Bool → ∀ k, FractionRing (D'.ntw.Ok i k) →+* ℂ),
        HEq ek ek' → HEq (ek i b k) (ek' i' b k) ∧
        ∀ (r : ∀ k Q ψ, D.nexp.MtV i ((j : ℕ) + 1) b k Q ψ →ₛₗ[ek i b k] (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank))
          (r' : ∀ k Q ψ, D'.nexp.MtV i' ((j' : ℕ) + 1) b k Q ψ →ₛₗ[ek' i' b k]
            (Bridge.Gf (Vc D' j') → PolF D' (Wc D' j').rank (Vc D' j').rank)), HEq r r' →
          ∀ (p : GAf D.host.E D.R.nV → Bridge.Gf (Vc D j)) (p' : GAf D'.host.E D'.R.nV → Bridge.Gf (Vc D' j')), HEq p p' →
            HEq (fun f g => r k Q ψ f (p g)) fun f g => r' k Q' ψ' f (p' g) := by
  obtain ⟨r, rfl⟩ := h.exists_rest
  exact (by with_unfolding_all exact ((join_copy_refl D) :))

def ExpMove (X : NExpTied D) (X' : NExpTied D') : Prop :=
  ∀ (i : D.ntw.Tw) (i' : D'.ntw.Tw), HEq i i' → ∀ (j : ℕ) (b : Bool) (k : ℕ) (Q : Finset (PlE D.host)) (Q' : Finset (PlE D'.host)),
    HEq Q Q' → ∀ (ψ : G D.host.E D.nd.Om →* (D.ntw.Ok i k)ˣ) (ψ' : G D'.host.E D'.nd.Om →* (D'.ntw.Ok i' k)ˣ), HEq ψ ψ' →
    ∀ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (h2' : j ≤ D'.R.m) (hA' : Formalism.L2.NX.AdmTw D' i' k Q' ψ'), ∃ hA : Formalism.L2.NX.AdmTw D i k Q ψ,
      HEq (X.mtV i j b k Q ψ h1 h2 hA).QP (X'.mtV i' j b k Q' ψ' h1 h2' hA').QP ∧
      HEq (X.mtV i j b k Q ψ h1 h2 hA).DP (X'.mtV i' j b k Q' ψ' h1 h2' hA').DP ∧
      ∀ (ε : FractionRing (D.ntw.Ok i k) →+* ℂ) (ε' : FractionRing (D'.ntw.Ok i' k) →+* ℂ), HEq ε ε' →
        ∀ (V V' : Type) [aV : AddCommGroup V] [mV : Module ℂ V] [aV' : AddCommGroup V'] [mV' : Module ℂ V'], V = V' → HEq aV aV' →
          HEq mV mV' → ∀ (r : D.nexp.MtV i j b k Q ψ → GAf D.host.E D.R.nV → V) (r' : D'.nexp.MtV i' j b k Q' ψ' → GAf D'.host.E D'.R.nV → V'),
            HEq r r' → GlobalTheory.HeightCounting.Reads X i j b k Q ψ h1 h2 hA ε V r → GlobalTheory.HeightCounting.Reads X' i' j b k Q' ψ' h1 h2' hA' ε' V' r'

def PqLaw (X : NExpTied D) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) : Prop :=
  ∀ i j b k Q ψ (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (hadm : Formalism.L2.NX.AdmTw D i k Q ψ),
    (X.mtV i j b k Q ψ h1 h2 hadm).QP = NX.qpOf D Pq Q ∧ (X.mtV i j b k Q ψ h1 h2 hadm).DP = NX.qpOf D Pq (D.ntw.pD i)

theorem pqLaw_move (h : CopyTw D D' ι e) {X : NExpTied D} {X' : NExpTied D'} (hX : ExpMove X X') {Pq Pq'} (hPq : HEq Pq Pq')
    (L : PqLaw X Pq) : PqLaw X' Pq' := by
  intro i' j b k Q' ψ' h1 h2' hA'
  have h2 : j ≤ D.R.m := by rw [h.gal.R]; exact h2'
  obtain ⟨i, Q, ψ, hi, hQ, hψ, e1, e2⟩ := (pq_copy h Pq Pq' hPq).2 i' k Q' ψ'
  obtain ⟨hA, q1, q2, -⟩ := hX i i' hi j b k Q Q' hQ ψ ψ' hψ h1 h2 h2' hA'
  obtain ⟨l1, l2⟩ := L i j b k Q ψ h1 h2 hA
  exact ⟨eq_of_heq (q1.symm.trans ((heq_of_eq l1).trans e1)), eq_of_heq (q2.symm.trans ((heq_of_eq l2).trans e2))⟩

end GlobalTheory.HeightCounting.SerCarry

end
