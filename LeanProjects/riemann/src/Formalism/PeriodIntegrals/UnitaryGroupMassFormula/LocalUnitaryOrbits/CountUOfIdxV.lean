import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalUnitaryOrbits.CountUOfOpen

noncomputable section

namespace PI.OmLocU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain MeasureTheory
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (ψ : AddChar (AF F) ℂ)
  (v : HeightOneSpectrum (𝓞 F)) (Λ : Set (Fin n → E))

abbrev latA : AddSubgroup (Fin n → Fv F v ⊗[F] E) := (latLoc (E := E) v Λ).toAddSubgroup

def lattice₂ (ϖ : Fv F v) : AddSubgroup (Fin n → Fv F v ⊗[F] E) :=
  (latA v Λ).map (DistribMulAction.toAddMonoidHom (Fin n → Fv F v ⊗[F] E) (sc (E := E) v ϖ))

def IdxV (a : ℕ) (Y : TupV (E := E) v n a) : Prop :=
  GoodY σ J ψ v Λ a Y → ∀ ϖ : Fv F v, IsUnif v ϖ →
    (lattice₂ v Λ ϖ).relIndex (latA v Λ) = (Ideal.absNorm v.asIdeal) ^ (2 * n)

def redT (a : ℕ) (ϖ : Fv F v) :
    lamA v Λ a →+ (Fin a → latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) where
  toFun X i := QuotientAddGroup.mk ⟨(X : TupV (E := E) v n a) i, X.2 i⟩
  map_zero' := by
    funext i
    rw [Pi.zero_apply, ← QuotientAddGroup.mk_zero]
    rfl
  map_add' X Y := by
    funext i
    rw [Pi.add_apply, ← QuotientAddGroup.mk_add]
    rfl

theorem redT_surj (a : ℕ) (ϖ : Fv F v) : Function.Surjective (redT v Λ a ϖ) := by
  intro c
  refine ⟨⟨fun i => ((c i).out : Fin n → Fv F v ⊗[F] E), fun i => (c i).out.2⟩, ?_⟩
  funext i
  show QuotientAddGroup.mk ⟨((c i).out : Fin n → Fv F v ⊗[F] E), (c i).out.2⟩ = c i
  exact QuotientAddGroup.out_eq' (c i)

theorem redT_ker (a : ℕ) (ϖ : Fv F v) :
    (redT v Λ a ϖ).ker = (lamP v Λ a ϖ).addSubgroupOf (lamA v Λ a) := by
  ext X
  rw [AddMonoidHom.mem_ker, AddSubgroup.mem_addSubgroupOf]
  constructor
  · intro h
    have hi : ∀ i, ∃ z ∈ latLoc (E := E) v Λ, sc (E := E) v ϖ • z = (X : TupV (E := E) v n a) i := by
      intro i
      have h1 := congrFun h i
      change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0 at h1
      rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
      obtain ⟨z, hz, hze⟩ := h1
      exact ⟨z, hz, hze⟩
    choose Z hZ hZe using hi
    exact ⟨Z, hZ, funext hZe⟩
  · rintro ⟨Z, hZ, hZe⟩
    funext i
    change (QuotientAddGroup.mk _ : latA v Λ ⧸ _) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact ⟨Z i, hZ i, congrFun hZe i⟩

theorem idxU_of (a : ℕ) (Y : TupV (E := E) v n a) (h : IdxV σ J ψ v Λ a Y) : IdxU σ J ψ v Λ a Y := by
  intro hG ϖ hϖ
  have hV := h hG ϖ hϖ
  rw [AddSubgroup.relIndex, ← redT_ker, AddSubgroup.index_ker,
    AddMonoidHom.range_eq_top.2 (redT_surj v Λ a ϖ), AddSubgroup.card_top, Nat.card_fun, Nat.card_eq_fintype_card (α := Fin a),
    Fintype.card_fin]
  have hq : Nat.card (latA v Λ ⧸ (lattice₂ v Λ ϖ).addSubgroupOf (latA v Λ)) =
      (Ideal.absNorm v.asIdeal) ^ (2 * n) := by
    rw [← hV, AddSubgroup.relIndex, AddSubgroup.index]
  rw [hq, ← pow_mul]

theorem countU_of_idxV (a : ℕ) (Y : TupV (E := E) v n a) (hO : LamOpen v Λ a)
    (hI : IdxV σ J ψ v Λ a Y) (hR : RedU σ J ψ v Λ a Y) : CountU σ J ψ v Λ a Y :=
  countU_of_open σ J ψ v Λ a Y hO (idxU_of σ J ψ v Λ a Y hI) hR

end PI.OmLocU
