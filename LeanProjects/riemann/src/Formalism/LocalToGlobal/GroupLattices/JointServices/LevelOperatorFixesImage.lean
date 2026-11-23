import Formalism.LocalToGlobal.Divisibility.RowSideTie
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

open Module NumberField IsDedekindDomain
open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV
open scoped ComplexOrder

noncomputable section

namespace Formalism.L2.G.ServJoint

section CSD

variable {K : Type} [Field K] [NumberField K] [StarRing K] (S : CSD K) {G : Type} [Group G] [Fintype G]
  (r : Representation K G S.Forms) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ)

theorem level_subspace_image_mem (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (F : Fin (S.BaseDimension r X P ψ) → K) :
    (S.V0E r X P ψ).mulVec F ∈ LinearMap.range (S.gaMat r (idemOf X)).mulVecLin ⊓ S.lvlPart r P ψ := by
  rw [← range_V0E S r X P ψ (idemOf_mul_self X hX) (idemOf_central X hX _)]
  exact ⟨F, rfl⟩

theorem lvlE_lvlPr_V0E {v0 : InfinitePlace K} (h0 : IsConjAt v0) (hpos : (S.H.map v0.embedding).PosDef) (hr : S.ActGood r)
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (F : Fin (S.BaseDimension r X P ψ) → K) :
    (S.lvlE r P ψ).mulVec ((S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F) = (S.V0E r X P ψ).mulVec F := by
  have hl := (level_idempotent_spec K v0 h0 G P ψ).1
  have h1 : S.lvlE r P ψ * S.lvlPr r P ψ = S.gaMat r (lvlIdem P ψ) :=
    (orthogonal_projection_spec K v0 h0 S hpos G r hr (lvlIdem P ψ) hl.idem hl.selfAdj).2
  rw [← Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, h1]
  exact CSD.lvlIdem_mulVec_of_mem S r P ψ _ (level_subspace_image_mem S r X P ψ hX F).2

theorem lvlOp_V0E {v0 : InfinitePlace K} (h0 : IsConjAt v0) (hpos : (S.H.map v0.embedding).PosDef) (hr : S.ActGood r)
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (F : Fin (S.BaseDimension r X P ψ) → K) :
    (S.lvlOp r P ψ (idemOf X)).mulVec ((S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F) =
      (S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F := by
  obtain ⟨y, hy⟩ := (level_subspace_image_mem S r X P ψ hX F).1
  have hfix : (S.gaMat r (idemOf X)).mulVec ((S.V0E r X P ψ).mulVec F) = (S.V0E r X P ψ).mulVec F := by
    rw [← hy, Matrix.mulVecLin_apply, Matrix.mulVec_mulVec, ← (group_action_matrix_hom K S G r).2, idemOf_mul_self X hX]
  unfold CSD.lvlOp
  rw [← Matrix.mulVec_mulVec, lvlE_lvlPr_V0E S r X P ψ h0 hpos hr hX F, ← Matrix.mulVec_mulVec, hfix,
    ← Matrix.mulVec_mulVec]

theorem lvlNab_V0E {v0 : InfinitePlace K} (h0 : IsConjAt v0) (hpos : (S.H.map v0.embedding).PosDef) (hr : S.ActGood r)
    (hX : ∀ χ ∈ X, IsAbsIrrChar χ) (F : Fin (S.BaseDimension r X P ψ) → K) :
    (S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F ∈ S.lvlNab r P ψ ↔ F ∈ S.Mt r X P ψ := by
  show (S.lvlE r P ψ).mulVec ((S.lvlPr r P ψ * S.V0E r X P ψ).mulVec F) ∈ S.nabLat ↔ (S.V0E r X P ψ).mulVec F ∈ S.nabLat
  rw [lvlE_lvlPr_V0E S r X P ψ h0 hpos hr hX F]

end CSD

section Fam

variable {D : Formalism.BasicNotions.D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}
  {A : FamIn D.what₂.LL G Pl0 T m}

theorem level_operator_fixes_image {s : ℕ} (hOk : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (t : T)
    (F : Fin ((A.side P ψ Zs).nV t) → D.what₂.LL) :
    (rE D A P ψ t).mulVec ((rV0 D A P ψ t).mulVec F) = (rV0 D A P ψ t).mulVec F :=
  lvlOp_V0E (A.fam.R t).S (A.fam.R t).r A.fam.X P ψ hOk.conj ((hOk.what₂ t).hpos _) (hOk.what₂ t).act hOk.irr F

theorem image_mem_nabla_iff {s : ℕ} (hOk : A.fam.Ok s) (P : Subgroup G) (ψ : P →* D.what₂.LLˣ) (Zs : DefSub A.fam.amb) (t : T)
    (F : Fin ((A.side P ψ Zs).nV t) → D.what₂.LL) :
    (rV0 D A P ψ t).mulVec F ∈ rNab D A P ψ t ↔ F ∈ (A.side P ψ Zs).Mt t :=
  lvlNab_V0E (A.fam.R t).S (A.fam.R t).r A.fam.X P ψ hOk.conj ((hOk.what₂ t).hpos _) (hOk.what₂ t).act hOk.irr F

end Fam

end Formalism.L2.G.ServJoint

end
