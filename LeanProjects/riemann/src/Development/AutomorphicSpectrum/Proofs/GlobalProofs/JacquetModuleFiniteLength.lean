import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InductionFiniteLength
import GroundTheory.AutomorphicForms.FiniteLength

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.JacquetBlocks

namespace GlobalTheory.CompanionTheory.JacquetBridge

section Bridge

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {α : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
  [∀ a, DecidableEq (m a)] {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem eq_iff_of_lt_iff {ι A B : Type} [LinearOrder A] [LinearOrder B] {f : ι → A} {g : ι → B}
    (h : ∀ i j, f i < f j ↔ g i < g j) (i j : ι) : f i = f j ↔ g i = g j := by
  constructor
  · intro hf
    refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
    · exact (lt_irrefl (f i)) (by simpa [hf] using (h j i).2 hlt)
    · exact (lt_irrefl (f i)) (by simpa [hf] using (h i j).2 hlt)
  · intro hg
    refine le_antisymm (not_lt.1 fun hlt => ?_) (not_lt.1 fun hlt => ?_)
    · exact (lt_irrefl (g i)) (by simpa [hg] using (h j i).1 hlt)
    · exact (lt_irrefl (g i)) (by simpa [hg] using (h i j).1 hlt)

theorem mem_blockUpper_iff (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (g : GL (Fin N) k) :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper k N β ↔ g ∈ parab k e := by
  show (g : Matrix (Fin N) (Fin N) k).BlockTriangular β ↔ (g : Matrix (Fin N) (Fin N) k).BlockTriangular (blk e)
  exact ⟨fun h i j hij => h ((hβ j i).2 hij), fun h i j hij => h ((hβ j i).1 hij)⟩

theorem mem_unipotentRadical_iff (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (g : GL (Fin N) k) :
    g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β ↔ g ∈ unipRad k e := by
  rw [GroundTheory.Automorphic.Parabolic.mem_unipotentRadical, mem_unipRad_iff_blk, mem_blockUpper_iff e hβ]
  exact and_congr Iff.rfl (forall_congr' fun i => forall_congr' fun j =>
    imp_congr_left (eq_iff_of_lt_iff hβ i j))

def leviMap (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) :
    Levi k m →* GroundTheory.Automorphic.Parabolic.levi k N β :=
  (leviEmb k e).codRestrict _ fun g => GroundTheory.Automorphic.Parabolic.mem_levi.2 fun i j hij =>
    leviEmb_apply_of_blk_ne e g fun h => hij ((eq_iff_of_lt_iff hβ i j).2 h)

theorem leviMap_surjective (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) :
    Function.Surjective (leviMap (k := k) e hβ) := by
  intro x
  let p : parab k e :=
    ⟨x, (mem_blockUpper_iff e hβ _).1 (GroundTheory.Automorphic.Parabolic.levi_le_blockUpper x.2)⟩
  have hoff : ∀ i j, blk e i ≠ blk e j → ((p : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) i j = 0 :=
    fun i j hij => GroundTheory.Automorphic.Parabolic.mem_levi.1 x.2 i j
      (fun h => hij ((eq_iff_of_lt_iff hβ i j).1 h))
  exact ⟨leviProj k e p, Subtype.ext (leviEmb_leviProj_of_blk e p hoff)⟩

theorem hasFiniteLength_of_twist {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (χ : G →* ℂ) (σ : Representation ℂ G W)
    (h : HasFiniteLength (GroundTheory.Automorphic.Parabolic.twist χ σ)) : HasFiniteLength σ := by
  have heq : GroundTheory.Automorphic.Parabolic.twist χ σ = GlobalTheory.SmGL.twist σ χ.toHomUnits := by
    ext g v
    rfl
  rw [heq] at h
  exact (hasFiniteLength_twist_iff σ χ.toHomUnits).1 h

theorem hasFiniteLength_jacU_of_labelling (e : (Σ a, m a) ≃ Fin N) {β : Fin N → ℕ}
    (hβ : ∀ i j, β i < β j ↔ blk e i < blk e j) (π : Representation ℂ (GL (Fin N) k) V)
    (h : HasFiniteLength (GroundTheory.Automorphic.Parabolic.jacquetRep k N β π)) :
    HasFiniteLength (jacU e π) := by
  have h1 : HasFiniteLength (GroundTheory.Automorphic.Parabolic.jacquetAction k N β π) :=
    hasFiniteLength_of_twist
      ((GroundTheory.Automorphic.Parabolic.invSqrtModular k N β).comp GroundTheory.Automorphic.Parabolic.leviIncl) _ h
  have h2 : HasFiniteLength ((GroundTheory.Automorphic.Parabolic.jacquetAction k N β π).comp (leviMap e hβ)) :=
    (hasFiniteLength_comp_iff _ _ (leviMap_surjective e hβ)).2 h1
  have hU : ∀ u : GL (Fin N) k, u ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N β → u ∈ unipRad k e :=
    fun u hu => (mem_unipotentRadical_iff e hβ u).1 hu
  let f : GroundTheory.Automorphic.Parabolic.JacquetModule k N β π →ₗ[ℂ] V ⧸ twKer π (unipRad k e) 1 :=
    Representation.Coinvariants.lift _ (twKer π (unipRad k e) 1).mkQ (fun u => by
      ext v
      simp only [LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype, Submodule.mkQ_apply]
      rw [Submodule.Quotient.eq]
      apply Submodule.subset_span
      exact ⟨⟨u, hU u u.2⟩, v, by simp⟩)
  let Φ : Representation.IntertwiningMap ((GroundTheory.Automorphic.Parabolic.jacquetAction k N β π).comp (leviMap e hβ))
      (jacU e π) :=
    ⟨f, fun g => by
      refine Representation.Coinvariants.hom_ext ?_
      ext v
      rfl⟩
  refine hasFiniteLength_of_surjective Φ ?_ h2
  intro y
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective (twKer π (unipRad k e) 1) y
  exact ⟨Representation.Coinvariants.mk _ v, rfl⟩

end Bridge

theorem jacquetFiniteLength : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k], GlobalTheory.SmGL.JacquetFiniteLength k := by
  intro k _ _ _ _ α n m _ _ _ _ _ _ e V _ _ π hπ hfl
  show HasFiniteLength (GlobalTheory.SmGL.twist (jacU e π) (deltaHalf k m)⁻¹)
  rw [hasFiniteLength_twist_iff]
  let ψ : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
  let e0 : (Σ a, m a) ≃ Fin (Fintype.card n) := e.trans ψ.symm
  have he : e0.trans ψ = e := by
    ext x
    simp [e0]
  rw [← he]
  refine hasFiniteLength_jacU_reindex e0 ψ π ?_
  let o : α ≃o Fin (Fintype.card α) := (Fintype.orderIsoFinOfCardEq α rfl).symm
  let β : Fin (Fintype.card n) → ℕ := fun i => (o (blk e0 i) : ℕ)
  have hβ : ∀ i j, β i < β j ↔ blk e0 i < blk e0 j := fun i j => by
    show (o (blk e0 i) : ℕ) < (o (blk e0 j) : ℕ) ↔ _
    rw [← Fin.lt_def]
    exact o.lt_iff_lt
  refine hasFiniteLength_jacU_of_labelling e0 hβ _ ?_
  refine GroundTheory.Automorphic.Parabolic.hasFiniteLength_jacquetRep ?_ ?_ β
  · intro v
    have hcont : Continuous (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv) := by
      show Continuous (Units.map (Matrix.reindexAlgEquiv k k ψ).toMulEquiv.toMonoidHom)
      exact Units.continuous_map (continuous_id.matrix_reindex ψ ψ)
    have hset : (GroundTheory.Automorphic.stabilizerOf
        (π.comp (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv).toMonoidHom) v :
          Set (GL (Fin (Fintype.card n)) k)) =
        (Units.mapEquiv (Matrix.reindexAlgEquiv k k ψ).toMulEquiv) ⁻¹' {g | π g v = v} := by
      ext g
      exact GroundTheory.Automorphic.mem_stabilizerOf
    rw [hset]
    exact (hπ v).preimage hcont
  · exact (hasFiniteLength_comp_iff π _ (MulEquiv.surjective _)).2 hfl

end GlobalTheory.CompanionTheory.JacquetBridge

end
