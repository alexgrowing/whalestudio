import Formalism.LocalToGlobal.GroupLattices.CloudFilling.LamMEqLamZero

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits Classical
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure CloudBound (D : D7) (u : D.what₂.Word) (c : ℕ) : Prop where
  top : ∀ g : D.R.Psi, (g : D.R.GG) ∈ D.host.topPlaces → ∀ i : Fin (D.R.k - 1 + 1), 0 < i.val → i.val < D.R.k - 1 →
    |lamRec D u g i| ≤ c
  off : ∀ g : D.R.Psi, (g : D.R.GG) ∉ D.host.topPlaces → ∀ i, |lamRec D u g i| ≤ c
  fill : ∀ g : D.R.Psi, (c : ℤ) ≤ wRec D u g 1

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

def fillsRec (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c) :
    Fills (gatRec D u h hS r L I ψ y e) :=
  fillsMk (gatRec D u h hS r L I ψ y e)
    (fun v => Finset.univ.filter fun s => ((posG (zPsi D.R.toFrame h) ⟨v, s⟩ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces)
    (fun v s => if ((posG (zPsi D.R.toFrame h) ⟨v, s⟩ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
      lamRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩) 0 else 0)
    (fun v s => if ((posG (zPsi D.R.toFrame h) ⟨v, s⟩ : D.R.Psi) : D.R.GG) ∈ D.host.topPlaces then
      -lamRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩) (Fin.last (D.R.k - 1)) else 0)
    c
    (fun v s => ⟨fun hs => ⟨(if_pos (Finset.mem_filter.1 hs).2).symm,
        ((congrArg Neg.neg (if_pos (Finset.mem_filter.1 hs).2)).trans (neg_neg _)).symm, fun i h0 h1 =>
        hc.top _ (Finset.mem_filter.1 hs).2 i h0 h1⟩,
      fun hs i => hc.off _ (fun ht => hs (Finset.mem_filter.2 ⟨Finset.mem_univ _, ht⟩)) i⟩)
    D.R.t D.R.m
    (fun v jj s => wRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩) jj)
    (fun v s => max_le (hc.fill _) (neg_last_le_wRec D u _))
    (fun v s jj _ => wRec_mono D u _ jj)

end Formalism.L2.G
