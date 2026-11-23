import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocFreeMapMkQIff
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SmulMemSpanOver
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LatticeGoodBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeBaseChangeSummandStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeSummandCriterionStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

theorem mem_annSub_iff {n k : ℕ} {v : Fin n → Ω} :
    v ∈ annSub Ω n k ↔ ∀ j : Fin n, (j : ℕ) < k → v j = 0 := by
  simp [annSub, Submodule.mem_pi]

def stepCoord (Ω : Type) [Field Ω] {n : ℕ} (i : Fin n) : annSub Ω n i →ₗ[Ω] Ω :=
  (LinearMap.proj i).comp (annSub Ω n i).subtype

theorem stepCoord_apply {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    stepCoord Ω i v = (v : Fin n → Ω) i := rfl

theorem stepCoord_surjective {n : ℕ} (i : Fin n) : Function.Surjective (stepCoord Ω i) := by
  classical
  intro c
  refine ⟨⟨Pi.single i c, mem_annSub_iff.2 fun j hj => ?_⟩, by simp [stepCoord_apply]⟩
  have : j ≠ i := by rintro rfl; exact lt_irrefl _ hj
  simp [Pi.single_apply, this]

theorem mem_ker_stepCoord {n : ℕ} (i : Fin n) (v : annSub Ω n i) :
    v ∈ LinearMap.ker (stepCoord Ω i) ↔ (v : Fin n → Ω) ∈ annSub Ω n ((i : ℕ) + 1) := by
  rw [LinearMap.mem_ker, stepCoord_apply, mem_annSub_iff]
  constructor
  · intro h j hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · exact mem_annSub_iff.1 v.2 j hj
    · rw [Fin.ext hj]; exact h
  · intro h
    exact h i (Nat.lt_succ_self _)

theorem summand_step {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (i : Fin n)
    (h : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    Summand (L.comap (annSub Ω n i).subtype.toAddMonoidHom) (LinearMap.ker (stepCoord Ω i)) := by
  obtain ⟨ρ, h1, h2, h3⟩ := h
  have hle : ∀ v, ρ v ∈ annSub Ω n i := fun v =>
    mem_annSub_iff.2 fun j hj => mem_annSub_iff.1 (h1 v) j (Nat.lt_succ_of_lt hj)
  refine ⟨(ρ.comp (annSub Ω n i).subtype).codRestrict _ fun v => hle _, fun v => ?_, fun u hu => ?_,
    fun v hv => ?_⟩
  · rw [mem_ker_stepCoord]
    exact h1 _
  · apply Subtype.ext
    exact h2 _ ((mem_ker_stepCoord i u).1 hu)
  · exact h3 _ hv

theorem locFree_step (R : Subalgebra o Ω) {n : ℕ} {L : AddSubgroup (Fin n → Ω)} (hL : LocFree R n L)
    (i : Fin n) (h₀ : Summand L (annSub Ω n i)) (h₁ : Summand L (annSub Ω n ((i : ℕ) + 1))) :
    LocFree R 1 ((L ⊓ (annSub Ω n i).toAddSubgroup).map (Pi.evalAddMonoidHom (fun _ => Ω) i)) := by
  have hA := ((GlobalTheory.T.locally_free_summand_criterion R (annSub Ω n i) n 0 L hL).2 h₀).1
  have hB := ((GlobalTheory.T.locally_free_summand_criterion R (LinearMap.ker (stepCoord Ω i)) _ 0 _ hA).2 (summand_step i h₁)).2
  have hr : Module.finrank Ω (annSub Ω n i) - Module.finrank Ω (LinearMap.ker (stepCoord Ω i)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (stepCoord Ω i)
    rw [LinearMap.range_eq_top.2 (stepCoord_surjective i), finrank_top, Module.finrank_self] at h
    omega
  rw [hr] at hB
  have hC := (locFree_map_mkQ_iff R (stepCoord Ω i) (stepCoord_surjective i) _).1 hB
  convert hC using 1
  ext c
  constructor
  · rintro ⟨v, ⟨hv, hv'⟩, rfl⟩
    exact ⟨⟨v, hv'⟩, hv, rfl⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, ⟨hv, v.2⟩, rfl⟩

theorem main : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → D.Good₁ R p χ → D.Good₂ R p χ → (∀ τ i, LocFree R 1 (D.dId R p (χ τ) i)) ∧ ∀ (C : Type) [Field C] [Algebra o C] [Algebra Ω C] [IsScalarTower o Ω C] (RC : Subalgebra o C), (∀ a ∈ R, algebraMap Ω C a ∈ RC) → ∀ τ i, (D.bc RC).dId RC p (fun a => algebraMap Ω C (χ τ a)) i = spanOver RC (algebraMap Ω C '' D.dId R p (χ τ) i) := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hB h1 h2
  obtain ⟨hg, hbc⟩ := GlobalTheory.T.lattice_good_base_change D R p w χ hc hB h1
  refine ⟨fun τ i => locFree_step R (hg τ).1 i (h2.ann τ i) (h2.ann τ ((i : ℕ) + 1)), ?_⟩
  intro C _ _ _ _ RC hRC τ i
  have haf := ((hbc C RC hRC).2 τ).1
  have hs := (GlobalTheory.T.locally_free_base_change_summand R RC hRC (bcMap Ω C (Fin n)) (isBaseChange_bcMap Ω C _)
    (D.af R p (χ τ)) (annSub Ω n i) (hg τ).1.1 (h2.ann τ i)).2
  rw [span_bcMap_annSub] at hs
  unfold LieLatticeData.dId
  rw [haf, hs]
  have hm := SpanExact.map_spanOver RC
    (bcMap Ω C (Fin n) '' ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω)))
    (LinearMap.proj i : (Fin n → C) →ₗ[C] C)
  have himg : algebraMap Ω C '' (((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _).map
      (Pi.evalAddMonoidHom (fun _ => Ω) i) : AddSubgroup Ω) : Set Ω) =
      (LinearMap.proj i : (Fin n → C) →ₗ[C] C) '' (bcMap Ω C (Fin n) ''
        ((D.af R p (χ τ) ⊓ (annSub Ω n i).toAddSubgroup : AddSubgroup _) : Set (Fin n → Ω))) := by
    ext c
    constructor
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
      exact ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  rw [himg, ← hm]
  rfl

end GlobalTheory.CompanionTheory.Ar.Num.LatticeGoodness.StepIdeal
