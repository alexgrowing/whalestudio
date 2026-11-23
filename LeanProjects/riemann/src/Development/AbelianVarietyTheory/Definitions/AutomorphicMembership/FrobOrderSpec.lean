import Mathlib
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.FillInstRecEqWj
import Formalism.LocalToGlobal.GroupLattices.PerfectRings.ExtWRec
import Formalism.LocalRingCardinality.SpanPowerMembership.GatTies
import Formalism.LocalRingCardinality.HostCls

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.G Formalism.L2.G NumberField

namespace GlobalTheory.Mem.LocalPack

attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.BasicNotions.factResChar

abbrev frobOrder (D : D7) (p : ℕ) : ℕ := orderOf (zH D.R.toFrame (hP D p))

theorem frobOrder_spec (D : D7) {T p : ℕ} (hg : GIdx D.host T p) : 2 ≤ frobOrder D p ∧ Even (frobOrder D p) := by
  obtain ⟨hp, -, hc, hn, -⟩ := hg
  haveI : Fact p.Prime := ⟨hp⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 hp
  have hpI : (Ideal.span {(p : ℤ)}).IsPrime := (Ideal.span_singleton_prime hpZ.ne_zero).2 hpZ
  obtain ⟨⟨P, hPp, hL⟩⟩ : Nonempty ((Ideal.span {(p : ℤ)}).primesOver (𝓞 D.host.E)) := inferInstance
  obtain ⟨⟨σ, hσ⟩, -⟩ := D.host.der.frob p (not_dvd_conductor_of_inert hp hc) P
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, hPp, hL, σ, hσ, rfl⟩
  obtain ⟨P', hP', hL', σ', hσ', heq⟩ := Classical.epsilon_spec hne
  have hnF : frobOrder D p = orderOf (D.R.iota (hP D p)) := by
    unfold frobOrder
    rw [← Subgroup.orderOf_coe]
    exact orderOf_injective (MonoidHom.inr Formalism.FrobeniusOrbits.G0 D.R.MA) (fun a b hab => (Prod.ext_iff.1 hab).2) _
  have hev : Even (orderOf (D.R.iota (hP D p))) := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← heq]
    exact @hn P' hP' hL' σ' hσ'
  have hpos : 0 < orderOf (D.R.iota (hP D p)) := orderOf_pos _
  rw [hnF]
  obtain ⟨k, hk⟩ := hev
  exact ⟨by omega, k, hk⟩

section Pack

variable (D : D7) (u : D.what₂.Word)
  (Lc : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)) (w : D.what₂.places.Pl)
  (h5 : 5 ≤ D.what₂.places.resChar w) (h2 : 2 ≤ frobOrder D (D.what₂.places.resChar w))
  (he : Even (frobOrder D (D.what₂.places.resChar w)))
  (I : LocId Lc (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
    (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
    (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : Formalism.L2.Herm.awayFrom₂ Lc (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def pack : LocPack D u Lc (D.what₂.places.resChar w) where
  W := WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  Qq := QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  O := ORec D w (frobOrder D (D.what₂.places.resChar w))
  Kf := KfRec D w (frobOrder D (D.what₂.places.resChar w))
  ι := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φK.comp
    (iota (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  σ := sig (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))
  j := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ.comp
    (jO (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  w := (extRec D w (frobOrder D (D.what₂.places.resChar w))).φ
    (wU (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
  hS := setting_ext (settingStd (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)) h5 h2 he)
    (extRec D w (frobOrder D (D.what₂.places.resChar w)))
  I := I
  ψ := ψ

theorem pack_ψ : (pack D u Lc w h5 h2 he I ψ).ψ = ψ := rfl

end Pack

section Record

variable (D : D7) (sc : Scale) (Ce : ℝ)
  (Lc : ∀ u, ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
  (I : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    LocId (Lc u) (D.what₂.places.resChar w) (nOrb (zH D.R.toFrame (hP D (D.what₂.places.resChar w))))
      (WQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w)))
      (QQ (D.what₂.places.resChar w) (frobOrder D (D.what₂.places.resChar w))))
  (ψ : ∀ u (w : D.what₂.places.Pl), GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w) →
    Formalism.L2.Herm.awayFrom₂ (Lc u) (D.what₂.places.resChar w) →* (ORec D w (frobOrder D (D.what₂.places.resChar w)))ˣ)

def packAll : ∀ u (w : D.what₂.places.Pl) (_h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)),
    LocPack D u (Lc u) (D.what₂.places.resChar w) :=
  fun u w h => pack D u (Lc u) w h.2.1 (frobOrder_spec D h).1 (frobOrder_spec D h).2 (I u w h) (ψ u w h)

variable (hd : ∀ u w h, ((packAll D Lc I ψ u w h).gat (rSc sc D.R.k (D.what₂.places.resChar w))
    (epSc D.R sc Ce (D.what₂.places.resChar w))).d = Module.finrank ℂ (D.mem u).A.Mu0)

abbrev record : D7 := recG D sc Ce Lc (packAll D Lc I ψ) hd

abbrev recordTies : GatTies (record D sc Ce Lc I ψ hd) := gatTiesG D sc Ce Lc (packAll D Lc I ψ) hd

example : (record D sc Ce Lc I ψ hd).host = D.host := rfl

example : (record D sc Ce Lc I ψ hd).R = D.R := rfl

example (u : D.what₂.Word) (w : D.what₂.places.Pl) (h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)) :
    ((record D sc Ce Lc I ψ hd).gat u w h).O = ORec D w (frobOrder D (D.what₂.places.resChar w)) := rfl

end Record

example (D : D7) {T p : ℕ} (hg : GIdx D.host T p) : frobOrder D p ≠ 1 ∧ frobOrder D p ≠ 3 := by
  obtain ⟨h2, k, hk⟩ := frobOrder_spec D hg
  omega

end GlobalTheory.Mem.LocalPack
