import Formalism.SharpRestriction.GrowthBounds.IsResidueClassZero
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies

noncomputable section

namespace Formalism.BasicNotions.Examples₂

open Formalism.MainNotions.G Formalism.FrobeniusOrbits NumberField LevelValuationRings

def tau1P (φ : Formalism.HC.Frame) (t : φ.A) : ↥φ.Psi := ⟨φ.tau1 t, rfl⟩

theorem tau1P_injective (φ : Formalism.HC.Frame) : Function.Injective (tau1P φ) := fun _ _ h =>
  φ.tau1_injective (congrArg Subtype.val h)

theorem iotaH_nsmul (φ : Formalism.HC.Frame) (t h : φ.A) (s : ℕ) :
    φ.iota (t + s • h) = φ.iota t * φ.iota h ^ s := rfl

def iotaHom (φ : Formalism.HC.Frame) : Multiplicative φ.A →* φ.MA where
  toFun x := φ.iota x.toAdd
  map_one' := φ.iota_zero
  map_mul' x y := φ.iota_add x.toAdd y.toAdd

theorem orderOf_iotaH (φ : Formalism.HC.Frame) (h : φ.A) : orderOf (φ.iota h) = addOrderOf h := φ.orderOf_iota h

variable (D : D7) {p : ℕ}

theorem iotaH_hP (S : Served D.host p) :
    D.R.iota (hP D p) = hOf D.host p := by
  obtain ⟨P, hP', hL, σ, hσ⟩ := exists_frob D.host p S.prime S.cls
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hP', hL, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have hv := @frob_val _ D.host p S.prime S.cls P₂ h1 h2 σ₂ hσ₂
  unfold hP
  rw [Formalism.HC.Frame.iota_iotaInv, ← he, hv]

theorem tau1P_mul_gPsi_pow (S : Served D.host p) (t0 : HH D) (s : ℕ) :
    tau1P D.R.toFrame t0 * gPsi S ^ s = tau1P D.R.toFrame (t0 + s • hP D p) := by
  apply Subtype.ext
  have hg : ((gPsi S ^ s : ↥(D.R.Psi)) : D.R.GG) =
      (1, hOf D.host p ^ s) := by
    unfold gPsi
    rw [← map_pow]
    rfl
  show D.R.tau1 t0 * ((gPsi S ^ s : ↥(D.R.Psi)) : D.R.GG) = D.R.tau1 (t0 + s • hP D p)
  unfold Formalism.HC.Frame.tau1
  rw [hg, Prod.mk_mul_mk, mul_one, iotaH_nsmul, iotaH_hP D S]

theorem order_gPsi (S : Served D.host p) : orderOf (gPsi S) = addOrderOf (hP D p) := by
  rw [(ord_spec S).1, ← iotaH_hP D S, orderOf_iotaH]

theorem injOn_tau1P (S : Served D.host p) (B : Set (HH D))
    (hB : ∀ t ∈ B, ∀ t' ∈ B, ∀ i : ℕ, t' = t + i • hP D p → t' = t) :
    Set.InjOn (fun x => (QuotientGroup.mk x : Quo (gPsi S))) (tau1P D.R.toFrame '' B) := by
  rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩ h
  have h1 : (tau1P D.R.toFrame t)⁻¹ * tau1P D.R.toFrame t' ∈ Subgroup.zpowers (gPsi S) := QuotientGroup.eq.mp h
  rw [← mem_powers_iff_mem_zpowers] at h1
  obtain ⟨i, hi⟩ := h1
  have h2 : tau1P D.R.toFrame t' = tau1P D.R.toFrame t * gPsi S ^ i := by
    have hi' : gPsi S ^ i = (tau1P D.R.toFrame t)⁻¹ * tau1P D.R.toFrame t' := hi
    rw [hi', mul_inv_cancel_left]
  rw [tau1P_mul_gPsi_pow] at h2
  rw [hB t ht t' ht' i (tau1P_injective _ h2)]

variable (h0 : ∀ u, Module.finrank ℂ (D.mem u).A.Mu0 = 0) (rOf : D.what₂.Word → ℕ → ℕ)
  (B : D.what₂.Word → ℕ → Set (HH D))

def withGatB : D7 := withGat D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p)

def gatTiesB : GatTies (withGatB D h0 rOf B) := gatTies D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p)

def vOfB (u : D.what₂.Word) (w : D.what₂.places.Pl)
    (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) (t0 : HH D) :
    Fin ((withGatB D h0 rOf B).gat u w h).P.nV :=
  orbIdx (gPsi (H := D.host) (served_of h)) (tau1P D.R.toFrame t0)

variable (u : D.what₂.Word) (w : D.what₂.places.Pl)
  (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w))

theorem vOfB_injOn
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t) :
    Set.InjOn (vOfB D h0 rOf B u w h) (B u (D.what₂.places.resChar w)) := fun t ht t' ht' e =>
  tau1P_injective _ (orbIdx_injOn _ _ (injOn_tau1P D (served_of h) _ hB) ⟨t, ht, rfl⟩ ⟨t', ht', rfl⟩ e)

theorem withGatB_n' (v) :
    ((withGatB D h0 rOf B).gat u w h).P.n' v = addOrderOf (hP D (D.what₂.places.resChar w)) :=
  order_gPsi D (served_of h)

theorem withGatB_r : ((withGatB D h0 rOf B).gat u w h).P.r = rOf u (D.what₂.places.resChar w) := rfl

theorem gatTiesB_pos
    (hB : ∀ t ∈ B u (D.what₂.places.resChar w), ∀ t' ∈ B u (D.what₂.places.resChar w), ∀ i : ℕ,
      t' = t + i • hP D (D.what₂.places.resChar w) → t' = t)
    {t0 : HH D} (ht0 : t0 ∈ B u (D.what₂.places.resChar w))
    (s : Fin (((withGatB D h0 rOf B).gat u w h).P.n' (vOfB D h0 rOf B u w h t0))) :
    ((D.eTau ((gatTiesB D h0 rOf B).gat_pos u w h ⟨vOfB D h0 rOf B u w h t0, s⟩) : D.R.Psi) :
      D.R.GG) = D.R.tau1 (t0 + s.val • hP D (D.what₂.places.resChar w)) := by
  have h1 := gatTies_pos_base D h0 rOf (fun u p => tau1P D.R.toFrame '' B u p) u w h
    (injOn_tau1P D (served_of h) _ hB) ⟨t0, ht0, rfl⟩ s
  exact congrArg (fun x : ↥(D.R.Psi) => (x : D.R.GG))
    (h1.trans (tau1P_mul_gPsi_pow D (served_of h) t0 s.val))

theorem hP_withGatB (p : ℕ) : hP (withGatB D h0 rOf B) p = hP D p := rfl

end Formalism.BasicNotions.Examples₂
