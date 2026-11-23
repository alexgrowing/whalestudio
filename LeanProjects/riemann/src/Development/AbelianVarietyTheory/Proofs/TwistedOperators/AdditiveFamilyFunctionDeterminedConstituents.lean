import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SmRep

noncomputable section

open scoped TensorProduct
open GlobalTheory.PRep GlobalTheory.JHMult

namespace GlobalTheory.SmGL

namespace AdditiveExpand

variable {G : Type} [Group G] [TopologicalSpace G]

open Classical in

theorem jhMult_rep_rep (c d : IrrCl G) : jhMult c.rep.ρ d.rep.ρ = if c = d then 1 else 0 := by
  split_ifs with h
  · subst h; exact jhMult_self c.rep.irr
  · by_contra h0
    obtain ⟨φ⟩ := (jhMult_ne_zero_iff.1 h0).nonempty_equiv c.rep.irr d.rep.irr
    exact h (c.cl_rep.symm.trans ((IrrRep.cl_eq_iff.2 ⟨φ.symm⟩).trans d.cl_rep))

variable (φ : SmRep G → ℕ∞) (h0 : ∀ B : SmRep G, Subsingleton B.V → φ B = 0)
  (hadd : ∀ (B B₁ B₂ : SmRep G) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ),
    Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) →
      (∀ v, p v = 0 → ∃ u, ι u = v) → φ B = φ B₁ + φ B₂)

variable [IsTopologicalGroup G]

def sub (B : SmRep G) (S : Subrepresentation B.ρ) : SmRep G :=
  ⟨S.toSubmodule, S.toRepresentation,
    IsSubquotient.isSmooth ⟨S, .id _, Function.surjective_id⟩ B.smooth⟩

def quo (B : SmRep G) (S T : Subrepresentation B.ρ) : SmRep G :=
  ⟨_, subQuot S T, IsSubquotient.isSmooth
    ⟨S, ⟨Submodule.mkQ _, fun _ => rfl⟩, Submodule.Quotient.mk_surjective _⟩ B.smooth⟩

include h0 hadd

theorem congr_equiv {B B' : SmRep G} (e : B.ρ.Equiv B'.ρ) : φ B = φ B' := by
  have hs : Subsingleton (sub B ⊥).V := inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
  have := hadd B (sub B ⊥) B' ⟨Submodule.subtype _, fun _ => rfl⟩ e.toIntertwiningMap
    Subtype.val_injective e.surjective
    (fun u => by rw [Subsingleton.elim u 0, map_zero, map_zero])
    (fun v hv => ⟨0, by
      rw [map_zero]
      exact (e.injective (hv.trans (map_zero e).symm)).symm⟩)
  rw [this, h0 _ hs, zero_add]

theorem one_coord₂ (B : SmRep G) (h : HasFiniteLength B.ρ) (T : Finset (IrrCl G))
    (hT : ∀ c ∉ T, jhMult c.rep.ρ B.ρ = 0) :
    φ B = ∑ c ∈ T, jhMult c.rep.ρ B.ρ * φ (SmRep.ofIrr c.rep) := by
  classical
  have ψ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := B.ρ)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation B.ρ) := ψ.toOrderEmbedding.wellFoundedLT
  have key : ∀ S : Subrepresentation B.ρ, (∀ c ∉ T, jhMult c.rep.ρ S.toRepresentation = 0) →
      φ (sub B S) = ∑ c ∈ T, jhMult c.rep.ρ S.toRepresentation * φ (SmRep.ofIrr c.rep) := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    intro hS'
    rcases eq_or_ne S ⊥ with rfl | hS
    · have hs : Subsingleton (⊥ : Subrepresentation B.ρ).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ B.V))
      rw [h0 _ hs]
      exact (Finset.sum_eq_zero fun c _ => by
        rw [jhMult_of_subsingleton c.rep.irr, zero_mul]).symm
    obtain ⟨R, -, hR⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let σ : IrrRep G := ⟨_, subQuot S R, (quo B S R).smooth, isIrreducible_subQuot hR⟩
    obtain ⟨e⟩ := σ.nonempty_equiv_rep
    have hm : ∀ c : IrrCl G, jhMult c.rep.ρ S.toRepresentation =
        jhMult c.rep.ρ R.toRepresentation + if c = σ.cl then 1 else 0 := fun c => by
      rw [jhMult_of_le c.rep.irr hR.le, ← jhMult_rep_rep, jhMult_congr_right _ e]
    have hp : ∀ v : S.toSubmodule, (Submodule.Quotient.mk v : (quo B S R).V) = 0 ↔
        v.1 ∈ R.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have h1 := hadd (sub B S) (sub B R) (quo B S R) ⟨Submodule.inclusion hR.le, fun _ => rfl⟩
      ⟨Submodule.mkQ _, fun _ => rfl⟩ (Submodule.inclusion_injective hR.le)
      (Submodule.Quotient.mk_surjective _) (fun u => (hp _).2 u.2)
      fun v hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩
    have h2 : φ (quo B S R) = φ (SmRep.ofIrr σ.cl.rep) :=
      (congr_equiv φ h0 hadd (B := SmRep.ofIrr σ.cl.rep) (B' := quo B S R) e).symm
    have h3 : σ.cl ∈ T := by
      by_contra hn
      have := hS' _ hn
      rw [hm] at this
      simp at this
    rw [h1, h2, ih R hR.lt fun c hc => (add_eq_zero.1 ((hm c).symm.trans (hS' c hc))).1]
    simp only [hm, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', if_pos h3]
  have h4 := key ⊤ (by simpa only [jhMult_congr_right _ (topEquiv B.ρ)] using hT)
  rw [← congr_equiv φ h0 hadd (B := sub B ⊤) (B' := B) (topEquiv B.ρ), h4]
  simp only [jhMult_congr_right _ (topEquiv B.ρ)]

end AdditiveExpand

open AdditiveExpand in

theorem additive_family_expand : ∀ (α : Type) [Fintype α] [DecidableEq α] (Γ : α → Type) [∀ i, Group (Γ i)] [∀ i, TopologicalSpace (Γ i)] [∀ i, IsTopologicalGroup (Γ i)] (Φ : (∀ i, GlobalTheory.SmGL.SmRep (Γ i)) → ℕ∞), (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α), Subsingleton (A i).V → Φ A = 0) → (∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)) (i : α) (B B₁ B₂ : GlobalTheory.SmGL.SmRep (Γ i)) (ι : B₁.ρ.IntertwiningMap B.ρ) (p : B.ρ.IntertwiningMap B₂.ρ), Function.Injective ι → Function.Surjective p → (∀ u, p (ι u) = 0) → (∀ v, p v = 0 → ∃ u, ι u = v) → Φ (Function.update A i B) = Φ (Function.update A i B₁) + Φ (Function.update A i B₂)) → ∀ (A : ∀ i, GlobalTheory.SmGL.SmRep (Γ i)), (∀ i, GlobalTheory.SmGL.HasFiniteLength (A i).ρ) → ∀ T : Finset (∀ i, GlobalTheory.SmGL.IrrCl (Γ i)), (∀ t ∉ T, ∃ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ = 0) → Φ A = ∑ t ∈ T, (∏ i, GlobalTheory.SmGL.jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => GlobalTheory.SmGL.SmRep.ofIrr (t i).rep) := by
  intro α _ _ Γ _ _ _ Φ h0 hadd
  classical
  have key : ∀ s : Finset α, ∀ A : ∀ i, SmRep (Γ i),
      (∀ i ∉ s, ∃ c : IrrCl (Γ i), A i = SmRep.ofIrr c.rep) → (∀ i, HasFiniteLength (A i).ρ) →
      ∀ T : Finset (∀ i, IrrCl (Γ i)), (∀ t ∉ T, ∃ i, jhMult (t i).rep.ρ (A i).ρ = 0) →
      Φ A = ∑ t ∈ T, (∏ i, jhMult (t i).rep.ρ (A i).ρ) * Φ (fun i => SmRep.ofIrr (t i).rep) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro A hA _ T hT
      choose c hc using fun i => hA i (Finset.notMem_empty i)
      obtain rfl : A = fun i => SmRep.ofIrr (c i).rep := funext hc
      have hm : ∀ t : ∀ i, IrrCl (Γ i),
          (∏ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ) = if t = c then 1 else 0 := fun t => by
        have : ∀ i, jhMult (t i).rep.ρ (SmRep.ofIrr (c i).rep).ρ = if t i = c i then 1 else 0 :=
          fun i => jhMult_rep_rep _ _
        simp only [this, Finset.prod_ite_zero, Finset.prod_const_one, Finset.mem_univ,
          forall_const, funext_iff]
      have h3 : c ∈ T := by
        by_contra hn
        obtain ⟨i, hi⟩ := hT c hn
        exact one_ne_zero ((jhMult_self (c i).rep.irr).symm.trans hi)
      simp only [hm, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', if_pos h3]
    | insert i s his ih =>
      intro A hA hl T hT
      let μ : ∀ j, IrrCl (Γ j) → SmRep (Γ j) → ℕ∞ := fun j c B => jhMult c.rep.ρ B.ρ
      have hC := finite_constituents (hl i)
      have h1 := one_coord₂ (fun B => Φ (Function.update A i B))
        (fun B hB => h0 _ i (by rw [Function.update_self]; exact hB)) (hadd A i) (A i) (hl i)
        hC.toFinset (fun c hc => by simpa using hc)
      simp only [Function.update_eq_self] at h1
      have h2 : ∀ c ∈ hC.toFinset, Φ (Function.update A i (SmRep.ofIrr c.rep)) =
          ∑ t ∈ T, ((if t i = c then 1 else 0) * ∏ j ∈ Finset.univ.erase i, μ j (t j) (A j)) *
            Φ (fun i => SmRep.ofIrr (t i).rep) := by
        intro c hc
        rw [ih (Function.update A i (SmRep.ofIrr c.rep)) ?_ ?_ T ?_]
        · refine Finset.sum_congr rfl fun t _ => ?_
          congr 1
          change ∏ j, μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = _
          rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i), Function.update_self]
          congr 1
          · exact jhMult_rep_rep _ _
          · exact Finset.prod_congr rfl fun j hj => by
              rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
        · intro j hj
          rcases eq_or_ne j i with rfl | hji
          · exact ⟨c, Function.update_self ..⟩
          · rw [Function.update_of_ne hji]
            exact hA j (by simp [hji, hj])
        · intro j
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]; exact c.rep.hasFiniteLength
          · rw [Function.update_of_ne hji]; exact hl j
        · intro t ht
          obtain ⟨j, hj⟩ := hT t ht
          refine ⟨j, ?_⟩
          change μ j (t j) (Function.update A i (SmRep.ofIrr c.rep) j) = 0
          rcases eq_or_ne j i with rfl | hji
          · rw [Function.update_self]
            refine (jhMult_rep_rep _ _).trans (if_neg ?_)
            rintro rfl
            exact (hC.mem_toFinset.1 hc) hj
          · rw [Function.update_of_ne hji]; exact hj
      rw [h1, Finset.sum_congr rfl fun c hc => by rw [h2 c hc, Finset.mul_sum], Finset.sum_comm]
      refine Finset.sum_congr rfl fun t _ => ?_
      change _ = (∏ j, μ j (t j) (A j)) * _
      rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
      simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq]
      split_ifs with h
      · exact (mul_assoc _ _ _).symm
      · have : μ i (t i) (A i) = 0 := by simpa using h
        rw [this, zero_mul, zero_mul]
  exact fun A hl T hT => key Finset.univ A (fun i hi => absurd (Finset.mem_univ i) hi) hl T hT

end GlobalTheory.SmGL
