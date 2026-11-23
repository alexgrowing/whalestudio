import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.LevelGatherings
import Formalism.LocalRingCardinality.SpanPowerMembership.GatAdd

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frob_eq (D : D7) {T p : ℕ} (hg : GIdx D.host T p) (P : Ideal (𝓞 D.host.E)) [P.IsPrime]
    [P.LiesOver (Ideal.span {(p : ℤ)})] (σ : D.host.E ≃ₐ[ℚ] D.host.E) (hσ : IsArithFrobAt ℤ σ P) :
    D.host.galE σ = (c0, D.R.iota (hP D p)) := by
  have hne : ∃ g, g ∈ frobSet D p := ⟨_, P, inferInstance, inferInstance, σ, hσ, rfl⟩
  obtain ⟨P₂, h1, h2, σ₂, hσ₂, he⟩ := Classical.epsilon_spec hne
  have hv := @Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val _ D.host p hg.1 hg.2.2.1 P₂ h1 h2 σ₂ hσ₂
  have hh : D.R.iota (hP D p) = Formalism.BasicNotions.Examples₂.LevelValuationRings.hOf D.host p := by
    unfold hP
    rw [Formalism.HC.Frame.iota_iotaInv, ← he, hv]
  rw [hh]
  exact Formalism.BasicNotions.Examples₂.LevelValuationRings.frob_val D.host p hg.1 hg.2.2.1 P σ hσ

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

variable (D : D7) (u : D.what₂.Word) {T : ℕ} (hg : GIdx D.host T p)
    (hS : HidaSetting p (orderOf (zH D.R.toFrame (hP D p))) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zH D.R.toFrame (hP D p))) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ)

include hg in

theorem gatRec_n_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v =
      orderOf (D.host.galE τ).2 := by
  rw [frob_eq D hg P τ hτ]
  show orderOf (zPsi D.R.toFrame (D.R.iota (hP D p))) = orderOf (D.R.iota (hP D p))
  rw [← Subgroup.orderOf_coe]
  first
  | (rw [show (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = MonoidHom.inr _ _ (D.R.iota (hP D p)) from rfl]
     exact orderOf_injective _ (fun a b h => congrArg Prod.snd h) _)
  | simp [zPsi, Prod.orderOf]
  | simp [zPsi, Prod.orderOf_mk]

include hg in

theorem gatRec_step_frob (v : Fin (gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.nV)
    (s : Fin ((gatRec D u (D.R.iota (hP D p)) hS r L I ψ y e).P.n' v))
    (P : Ideal (𝓞 D.host.E)) [P.IsPrime] [P.LiesOver (Ideal.span {(p : ℤ)})] (τ : D.host.E ≃ₐ[ℚ] D.host.E)
    (hτ : IsArithFrobAt ℤ τ P) :
    ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, posAdd s 1⟩) : D.R.Psi) : D.R.GG) =
      ((D.eTau (gatRec_pos D u _ hS r L I ψ y e ⟨v, s⟩) : D.R.Psi) : D.R.GG) *
        D.host.galE τ * D.R.cc := by
  have hz : (((zPsi D.R.toFrame (D.R.iota (hP D p))) : D.R.Psi) : D.R.GG) = D.host.galE τ * D.R.cc := by
    rw [frob_eq D hg P τ hτ]
    refine Prod.ext ?_ ?_
    · show ((1, 1) : G0) = c0 * c0
      first
      | rfl
      | decide
      | simp [c0]
    · show D.R.iota (hP D p) = D.R.iota (hP D p) * 1
      rw [mul_one]
  rw [mul_assoc, ← hz]
  simp only [gatRec_pos, Equiv.trans_apply, Equiv.apply_symm_apply]
  first
  | exact congrArg Subtype.val (posG_step (zPsi D.R.toFrame (D.R.iota (hP D p))) v s)
  | exact congrArg Subtype.val (posG_step v s)
  | exact congrArg Subtype.val (posG_step (z := (zPsi D.R.toFrame (D.R.iota (hP D p)))) v s)

end Formalism.L2.G
