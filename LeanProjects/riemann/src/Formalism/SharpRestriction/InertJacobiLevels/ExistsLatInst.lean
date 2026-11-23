import Formalism.SharpRestriction.InertJacobiLevels.LambdaRealEqShiftedWeight
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGatC

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.BasicNotions.Examples₂

section Base

variable {N : ℕ} [NeZero N]

theorem bsC_add_nsmul (h t : ZMod N) (i : ℕ) : bsC h (t + i • h) = bsC h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, bsC_step, ih]

theorem bsC_idem (h t : ZMod N) : bsC h (bsC h t) = bsC h t := by
  obtain ⟨i, hi⟩ := bsC_eq h t
  rw [hi, bsC_add_nsmul, ← hi]

theorem bsC_unique (h x x' : ZMod N) (i : ℕ) (e : bsC h x' = bsC h x + i • h) : bsC h x' = bsC h x := by
  rw [← bsC_idem h x', e, bsC_add_nsmul, bsC_idem]

end Base

section BaseA

variable {φ : Formalism.HC.Frame}

theorem bsA_add_nsmul (h t : φ.A) (i : ℕ) : bsA h (t + i • h) = bsA h t := by
  induction i with
  | zero => simp
  | succ i ih => rw [succ_nsmul, ← add_assoc, bsA_step, ih]

theorem bsA_idem (h t : φ.A) : bsA h (bsA h t) = bsA h t := by
  obtain ⟨i, hi⟩ := bsA_eq h t
  rw [hi, bsA_add_nsmul, ← hi]

theorem bsA_unique (h x x' : φ.A) (i : ℕ) (e : bsA h x' = bsA h x + i • h) : bsA h x' = bsA h x := by
  rw [← bsA_idem h x', e, bsA_add_nsmul, bsA_idem]

end BaseA

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (sc : Scale) (eOf : ℕ → ℕ)

def baseB : D.what₂.Word → ℕ → Set (G.HH D) := fun _ p => {t | ∃ x, bsA (G.stepP D p) x = t}

def rOfB : D.what₂.Word → ℕ → ℕ := fun _ p => if (p : ℝ) < sc.p0 D.R.k then G.rG sc else 1

def recB : D7 := withGatCB D h0 (rOfB D sc) eOf (baseB D)

def tiesB : GatTies (recB D h0 sc eOf) := gatTiesCB D h0 (rOfB D sc) eOf (baseB D)

theorem stepP_of_gidx {T p : ℕ} (hg : GIdx D.host T p) : G.stepP D p = G.hP D p := by
  unfold G.stepP
  rw [if_neg]
  intro h
  have h1 : D.host.cls p = PrimeClass.inertClass := hg.2.2.1
  have h2 : D.host.cls p = PrimeClass.signal := h
  rw [h1] at h2
  exact PrimeClass.noConfusion h2

theorem baseB_sep (u : D.what₂.Word) {T p : ℕ} (hg : GIdx D.host T p) :
    ∀ t ∈ baseB D u p, ∀ t' ∈ baseB D u p, ∀ i : ℕ, t' = t + i • G.hP D p → t' = t := by
  rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩ i e
  rw [stepP_of_gidx D hg] at e ⊢
  exact bsA_unique _ _ _ i e

def posHypB {L : SizeData₂ (recB D h0 sc eOf)} (X : G.Inst (recB D h0 sc eOf) L) (hbs : X.bs = bsA) (hsc : L.sc = sc) :
    PosHyp (tiesB D h0 sc eOf) X where
  vOf := vOfCB D h0 (rOfB D sc) eOf (baseB D)
  inj := fun u w hg => by
    have h := vOfCB_injOn D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg)
    intro t ht t' ht' e
    have m : ∀ y, y ∈ G.reps X (D.what₂.places.resChar w) → y ∈ baseB D u (D.what₂.places.resChar w) := by
      intro y hy
      unfold G.reps at hy
      rw [hbs] at hy
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 hy
      exact ⟨x, hx⟩
    exact h (m t ht) (m t' ht') e
  n_eq := fun u w hg t0 _ => withGatCB_n' D h0 (rOfB D sc) eOf (baseB D) u w hg _
  pos := fun u w hg t0 ht0 s => by
    have m : t0 ∈ baseB D u (D.what₂.places.resChar w) := by
      unfold G.reps at ht0
      rw [hbs] at ht0
      obtain ⟨x, -, hx⟩ := Finset.mem_image.1 ht0
      exact ⟨x, hx⟩
    exact gatTiesCB_pos D h0 (rOfB D sc) eOf (baseB D) u w hg (baseB_sep D u hg) m s
  r_eq := fun u w hg => by
    rw [hsc]
    rfl

theorem recB_M (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) : ((recB D h0 sc eOf).gat u w hg).M = ⊥ :=
  withGatC_M D h0 (rOfB D sc) eOf (fun u p => tau1P D.R.toFrame '' baseB D u p) u w hg

theorem recB_e (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (hg : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((recB D h0 sc eOf).gat u w hg).e = eOf (D.what₂.places.resChar w) := rfl

theorem exists_latInst {L : SizeData₂ (recB D h0 sc eOf)} (X : G.Inst (recB D h0 sc eOf) L) (K : G.Consts) (hbs : X.bs = bsA)
    (hsc : L.sc = sc)
    (hf : ∀ j ∈ SizeData₂.lifts (recB D h0 sc eOf), ∀ (τ : (recB D h0 sc eOf).what₂.Tau) (z : Bool × G.HH (recB D h0 sc eOf)),
      ((recB D h0 sc eOf).eTau τ : (recB D h0 sc eOf).R.GG) = G.plGG (recB D h0 sc eOf) z →
        G.fill X (G.bL L) j z = wj (recB D h0 sc eOf) j τ)
    (hl : ∀ u w, L.lenMN u w = 0)
    (c : ℕ) (c_le : (c : ℝ) ≤ G.cG L) (hcl : L.Sc + (((recB D h0 sc eOf).R.k : ℝ) - 1) / 2 ≤ c)
    (hoff : ∀ u τ, ((recB D h0 sc eOf).eTau τ : (recB D h0 sc eOf).R.GG) ∉ (recB D h0 sc eOf).host.topPlaces →
      ∀ i : Fin (recB D h0 sc eOf).R.k,
        |((((recB D h0 sc eOf).hcW u τ).u i : ℚ) : ℝ) - ((((recB D h0 sc eOf).R.k : ℝ) - 1) / 2 - (i.1 : ℝ))| ≤ c)
    (hw1 : ∀ τ, (c : ℝ) ≤ wj (recB D h0 sc eOf) 1 τ - G.kaJ (recB D h0 sc eOf) 1) :
    ∃ Y : G.LatInst (recB D h0 sc eOf), G.LatTied (tiesB D h0 sc eOf) X Y ∧ ∀ w, G.LatticeLengthsAtPlace X Y K w :=
  ⟨(latHypOf (tiesB D h0 sc eOf) X (posHypB D h0 sc eOf X hbs hsc) c c_le hcl hoff hw1).latInst,
    (latHypOf (tiesB D h0 sc eOf) X (posHypB D h0 sc eOf X hbs hsc) c c_le hcl hoff hw1).latTied hf,
    fun w => sizeDataLat_of_M_bot X _ K (recB_M D h0 sc eOf) hl w⟩

end Formalism.MainNotions.Inhab

end
