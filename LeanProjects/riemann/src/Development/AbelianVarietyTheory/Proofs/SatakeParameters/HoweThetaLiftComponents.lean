import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.HeckeSplitOne
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaGramMatrix
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.ThetaLiftUniqueness

noncomputable section

namespace GlobalTheory.Proof.HoweThetaLiftComponents

open Formalism.BasicNotions Formalism.MainNotions.N GlobalTheory.ThetaExh

theorem mem_of_orthogonal_others {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (p : ι) (horth : ∀ k, k ≠ p → U k ⟂ U p)
    (x : V) (hx : ∀ k, k ≠ p → ∀ y ∈ U k, inner ℂ y x = 0) : x ∈ U p := by
  have hsup : U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k) = ⊤ := by
    rw [eq_top_iff, ← htop]
    refine iSup_le fun k => ?_
    by_cases hk : k = p
    · subst hk; exact le_sup_left
    · exact le_sup_of_le_right (le_iSup₂_of_le (f := fun k (_ : k ∈ {k | k ≠ p}) => U k) k hk le_rfl)
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 (hsup.symm ▸ Submodule.mem_top : x ∈ U p ⊔ (⨆ k ∈ {k | k ≠ p}, U k))
  have hle : (⨆ k ∈ {k | k ≠ p}, U k) ≤ (ℂ ∙ v)ᗮ := by
    refine iSup₂_le fun k hk y hy => ?_
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    have hv' : v = x - u := by rw [← huv]; abel
    rw [hv', inner_sub_right, hx k hk y hy, (horth k hk).inner_eq hy hu, sub_zero]
  have h0 : inner ℂ v v = 0 := Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle hv)
  rw [inner_self_eq_zero] at h0
  rw [← huv, h0, add_zero]
  exact hu

theorem exists_inner_ne_zero {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (U : ι → Submodule ℂ V) (htop : ⨆ k, U k = ⊤) (x : V) (hx : x ≠ 0) :
    ∃ k, ∃ y ∈ U k, inner ℂ y x ≠ 0 := by
  by_contra h
  push Not at h
  have hle : (⨆ k, U k) ≤ (ℂ ∙ x)ᗮ := iSup_le fun k y hy =>
    Submodule.mem_orthogonal_singleton_iff_inner_left.2 (h k y hy)
  rw [htop] at hle
  exact hx (inner_self_eq_zero.1
    (Submodule.mem_orthogonal_singleton_iff_inner_left.1 (hle (Submodule.mem_top : x ∈ ⊤))))

theorem eachRowHasThetaLift_of_howe :
    ∀ (R : Ranks) (H : Host R) (what₂ : Rows.Data R) (N : NData R H what₂) (A : NAut N),
      GlobalTheory.IndefiniteRowSideFullHecke.ThetaGramMatrix.ThetaGramPositiveScalar N A → (∀ i, HoweUp N A i) →
      (∀ i, TypeOrth N A i) → GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.EachRowHasThetaLift N A := by
  intro R H what₂ N A hpos hhowe horth
  rw [GlobalTheory.IndefiniteRowSideFullHecke.ThetaLiftUniqueness.eachRowHasThetaLift_iff]
  rintro i σ ⟨f, hf, hf0⟩
  have hθ : what₂.thetaT (N.mu i) (N.j i) f ≠ 0 := fun h => hf0 (hpos.eq_zero i σ f hf h)
  obtain ⟨P, F, hF, hFf⟩ := exists_inner_ne_zero (A.typeV i) (A.typeV_top i) _ hθ
  refine ⟨P, ⟨f, hf, hθ⟩, fun g hg => ?_⟩
  refine mem_of_orthogonal_others (A.typeV i) (A.typeV_top i) P (fun k hk => horth i k P hk) _
    fun k hk y hy => ?_
  by_contra hne
  exact hk (hhowe i σ k P ⟨g, hg, y, hy, hne⟩ ⟨f, hf, F, hF, hFf⟩)

def HasComponent {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) (σ : what₂.FT) (P : A.AV i) : Prop :=
  ∃ f ∈ what₂.isot (N.j i) σ,
    what₂.thetaT (N.mu i) (N.j i) f ∉ ⨆ P', ⨆ _ : P' ≠ P, A.typeV i P'

def HoweComponent {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N)
    (i : N.Loc) : Prop :=
  ∀ σ P P', HasComponent N A i σ P → HasComponent N A i σ P' → P = P'

end GlobalTheory.Proof.HoweThetaLiftComponents
