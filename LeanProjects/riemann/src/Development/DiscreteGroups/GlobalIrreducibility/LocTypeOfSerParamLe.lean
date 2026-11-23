import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.DetCharacterMemPrincipalCongruenceFixedVectors

noncomputable section

namespace DiscreteGroups.sglob.DzType.Rt

open Polynomial GlobalTheory.GLq GlobalTheory.GLp Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.ArithmeticCylinders GlobalTheory.SerSys
open scoped Classical

attribute [local instance] GlobalTheory.SerSys.factTypePrime

variable {g : ℕ} [Fact g.Prime]

def SerParamLe (b : ℕ) (e : ∀ n : ℕ, (ZMod g)[X] → MonoidAlgebra ℂ (Gn g n)) (τ : Formalism.CyclotomicNorms.Fbar g →* ℂ)
    (ine : ∀ n, QRep g n → ℂ[X]) : Prop :=
  ∀ n, n ≤ b → ∀ (π : QRep g n), IrrSm π → ∀ f, (∃ v ∈ fixK1 π.ρ, actK π.ρ (e n f) v ≠ 0) →
    ine n π = ((Formalism.CyclotomicNorms.rootsBar f).map fun x => X - C (τ x)).prod

def LabParamLe (b : ℕ) (D : D7) (L : ∀ k, LabelDatum (D.host.g k)) (rc : Corr D) : Prop :=
  ∀ k v, SerParamLe b (eSerC (L k)) (L k).teich fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)

theorem one_le_nV (D : D7) : 1 ≤ D.R.nV := by
  have ht : 0 < D.R.t := D.R.t_odd.pos
  unfold Formalism.BasicNotions.Ranks.nV
  omega

theorem r_le_nV (D : D7) : D.R.r ≤ D.R.nV := by
  unfold Formalism.BasicNotions.Ranks.nV
  omega

theorem locType_of_serParamLe {D : D7} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D} (hC : LocComp D rc)
    (hP : ∀ k v, SerParamLe D.R.nV (S k).e (D.ntypes.teichC k) fun n π => D.naut.inePol (rc k v n π) (D.ntypes.tg k v)) :
    LocType D S := by
  intro i P k v
  obtain ⟨μ, χ, hμ, h1, h2⟩ := hC.2 i k v
  obtain ⟨π, hπ, h3, h4⟩ := h2 P
  obtain ⟨f, hf, hm, hd, -⟩ := Loc.exists_charIn (S k) χ 1
  obtain ⟨c, rfl⟩ : ∃ c, f = X - C c := ⟨-f.coeff 0, by rw [C_neg, sub_neg_eq_add]; exact hm.eq_X_add_C hd⟩
  refine ⟨π, χ, c, fun F hF a ha h0 => h4.exists_parVec hF ha h0, Loc.charIn_pow _ χ hf _, ?_,
    fun f' hf' => h3 ▸ hP k v _ le_rfl π hπ f' hf'⟩
  rw [h1, ← Loc.prod_linear]
  exact hP k v 1 (one_le_nV D) _ (Loc.irrSm_det hμ) _ ((Loc.has_det hμ (S k) _).2 hf)

theorem locType_of_tiesLe {D : D7} {L : ∀ k, LabelDatum (D.host.g k)} {S : ∀ k, Sys (D.host.g k)} {rc : Corr D}
    (hL : LabTie D L) (hS : ∀ k, (S k).IsOf (L k)) (hC : LocComp D rc) (hP : LabParamLe D.R.nV D L rc) :
    LocType D S :=
  locType_of_serParamLe hC fun k v => by
    rw [← (hL k).1, show (S k).e = eSerC (L k) from funext fun n => funext (hS k n)]
    exact hP k v

end DiscreteGroups.sglob.DzType.Rt

end
