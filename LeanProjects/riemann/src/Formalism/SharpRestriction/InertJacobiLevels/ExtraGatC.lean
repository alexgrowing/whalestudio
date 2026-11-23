import Formalism.LocalRingCardinality.SpanPowerMembership.GatAdd
import Formalism.SharpRestriction.InertJacobiLevels.ExtraGat

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.LevelValuationRings Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField

theorem two_ne_Kn (p : ℕ) [Fact p.Prime] (h5 : 5 ≤ p) (n : ℕ) : (2 : Kn p n) ≠ 0 := by
  intro h
  have h1 : ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 2 =
      ((algebraMap (On p n) (Kn p n)).comp (algebraMap (Wn p n) (On p n))) 0 := by
    rw [map_ofNat, map_zero, h]
  have h2 : (2 : Wn p n) = 0 := inj_WK p n h1
  have h3 : ((2 : ℕ) : GaloisField p n) = 0 := by
    have := congrArg (WittVector.constantCoeff (p := p) (R := GaloisField p n)) h2
    rw [map_ofNat, map_zero] at this
    exact_mod_cast this
  have h4 := (CharP.cast_eq_zero_iff (GaloisField p n) p 2).1 h3
  have := Nat.le_of_dvd (by norm_num) h4
  omega

section One

variable {R : Ranks} {H : Host R} {p : ℕ}

def gatOfC (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : GAtP p :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  { O := On p (orderOf (gPsi S))
    Kf := Kn p (orderOf (gPsi S))
    P := placesOf S T r lam
    comp := comp
    lev := fun _ => levAll _
    e := e }

theorem gatOfC_M (S : Served H p) (T : Set ↥(R.Psi)) (r : ℕ) (lam : ↥(R.Psi) → DomWeight (R.N 0))
    (comp : Type) [Fintype comp] (e : ℕ) : (gatOfC S T r lam comp e).M = ⊥ :=
  haveI : Fact p.Prime := ⟨S.prime⟩
  gat_M_bot _ fun _ => levAll_M _ (two_ne_Kn p S.five_le _)

end One

variable (D : D7) (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0)
  (rOf : D.what₂.Word → ℕ → ℕ) (eOf : ℕ → ℕ) (bs : D.what₂.Word → ℕ → Set ↥(D.R.Psi))

def withGatC : D7 :=
  { D with
    gat := fun u w h => gatOfC (served_of h) (bs u (D.what₂.places.resChar w))
      (rOf u (D.what₂.places.resChar w)) (fun ψ => (D.fm u).lam 0 (D.eTau.symm ψ)) ((D.mem u).C.cls 0)
      (eOf (D.what₂.places.resChar w))
    gat_d := fun u _ _ => (gat_d_zero _ (gatOfC_M _ _ _ _ _ _)).trans (h0 u).symm }

def gatTiesC : GatTies (withGatC D h0 rOf eOf bs) where
  gat_k := fun _ _ _ => k_pos D.R
  gat_n := fun _ _ h _ P hP hL σ hσ => @orderOf_frobenius_image_eq _ D.host _ (served_of h) P hP hL σ hσ
  gat_pos := fun u w h => (posPsi (served_of h) (bs u (D.what₂.places.resChar w))).trans D.eTau.symm
  gat_step := fun u w h v s P hP hL σ hσ =>
    @position_succ_eq_mul_frobenius _ D.host _ (served_of h) (bs u (D.what₂.places.resChar w)) _ D.eTau v s P hP hL σ hσ
  gat_lam := fun _ _ _ _ _ _ => rfl

theorem withGatC_M (u w h) : ((withGatC D h0 rOf eOf bs).gat u w h).M = ⊥ := gatOfC_M _ _ _ _ _ _

theorem withGatC_e (u w h) : ((withGatC D h0 rOf eOf bs).gat u w h).e = eOf (D.what₂.places.resChar w) := rfl

theorem withGatC_trans (u w h) (c : ((withGatC D h0 rOf eOf bs).gat u w h).comp)
    (L L' : ((withGatC D h0 rOf eOf bs).gat u w h).P.Tup) (hL : ((withGatC D h0 rOf eOf bs).gat u w h).P.IsLatTup L)
    (hL' : ((withGatC D h0 rOf eOf bs).gat u w h).P.IsLatTup L') :
    ∃ γ : (((withGatC D h0 rOf eOf bs).gat u w h).lev c).Γ, L' = (((withGatC D h0 rOf eOf bs).gat u w h).lev c).smul γ L :=
  levAll_trans _ L L' hL hL'

def withGatC_comp (u w h) : ((withGatC D h0 rOf eOf bs).gat u w h).comp ≃ ((withGatC D h0 rOf eOf bs).mem u).C.cls 0 :=
  Equiv.refl _

theorem gatTiesC_pos_base (u) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))
    (hT : Set.InjOn (fun x => (QuotientGroup.mk x : Quo (gPsi (H := D.host) (served_of h))))
      (bs u (D.what₂.places.resChar w)))
    {x : ↥(D.R.Psi)} (hx : x ∈ bs u (D.what₂.places.resChar w))
    (s : Fin (orderOf (gPsi (H := D.host) (served_of h)))) :
    D.eTau ((gatTiesC D h0 rOf eOf bs).gat_pos u w h ⟨orbIdx (gPsi (served_of h)) x, s⟩) =
      x * gPsi (served_of h) ^ (s : ℕ) :=
  (D.eTau.apply_symm_apply _).trans (orbEquiv_idx _ _ hT hx s)

variable (B : D.what₂.Word → ℕ → Set (HH D))

def withGatCB : D7 := withGatC D h0 rOf eOf (fun u p => tau1P D.R.toFrame '' B u p)

def gatTiesCB : GatTies (withGatCB D h0 rOf eOf B) := gatTiesC D h0 rOf eOf (fun u p => tau1P D.R.toFrame '' B u p)

def vOfCB (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : HH D) :
    Fin ((withGatCB D h0 rOf eOf B).gat u w h).P.nV :=
  orbIdx (gPsi (H := D.host) (served_of h)) (tau1P D.R.toFrame t0)

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem vOfCB_injOn
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t) :
    Set.InjOn (vOfCB D h0 rOf eOf B u w h) (B u (D.what₂.places.resChar w)) := fun t ht t' ht' e =>
  tau1P_injective _ (orbIdx_injOn _ _ (injOn_tau1P D (served_of h) _ hB) ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩ e)

theorem withGatCB_n' (v) :
    ((withGatCB D h0 rOf eOf B).gat u w h).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) :=
  order_gPsi D (served_of h)

theorem withGatCB_r : ((withGatCB D h0 rOf eOf B).gat u w h).P.r = rOf u (D.what₂.places.resChar w) := rfl

theorem gatTiesCB_pos
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t)
    {t0 : HH D} (ht0 : t0 ∈ B u (D.what₂.places.resChar w))
    (s : Fin (((withGatCB D h0 rOf eOf B).gat u w h).P.n' (vOfCB D h0 rOf eOf B u w h t0))) :
    ((D.eTau ((gatTiesCB D h0 rOf eOf B).gat_pos u w h ⟨vOfCB D h0 rOf eOf B u w h t0, s⟩) : D.R.Psi) :
      D.R.GG) = D.R.tau1 (t0 + s.val • hP D (D.what₂.places.resChar w)) := by
  have h1 := gatTiesC_pos_base D h0 rOf eOf (fun u p => tau1P D.R.toFrame '' B u p) u w h
    (injOn_tau1P D (served_of h) _ hB) ⟨t0, ht0, rfl⟩ s
  exact congrArg (fun x : ↥(D.R.Psi) => (x : D.R.GG))
    (h1.trans (tau1P_mul_gPsi_pow D (served_of h) t0 s.val))

theorem hP_withGatCB (p : ℕ) : hP (withGatCB D h0 rOf eOf B) p = hP D p := rfl

end Formalism.MainNotions.Inhab

end
