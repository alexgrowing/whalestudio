import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InstAddCommGroupTwo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.JacquetModuleMapInjectiveOfInjectiveStatement

noncomputable section

open GlobalTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SmGL.Exponents GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.SmGL.Exponents.Additive

section General

variable {F G V W : Type} [Field F] [Group G] [AddCommGroup V] [Module F V]
  [AddCommGroup W] [Module F W]

theorem exists_mem_twKer {ρ : Representation F G V} {σ : Representation F G W}
    (p : ρ.IntertwiningMap σ) (hp : Function.Surjective p) (N : Subgroup G) {w : W}
    (hw : w ∈ twKer σ N 1) : ∃ v ∈ twKer ρ N 1, p v = w := by
  have : twKer σ N 1 ≤ (twKer ρ N 1).map p.toLinearMap := Submodule.span_le.2 (by
    rintro _ ⟨n, w, rfl⟩
    obtain ⟨v, rfl⟩ := hp w
    refine ⟨_, Submodule.subset_span ⟨n, v, rfl⟩, ?_⟩
    simp [p.isIntertwining])
  exact this hw

end General

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : ℕ} {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup U] [Module ℂ U]

theorem wordMult_exact {π : Representation ℂ (GL (Fin n) k) V}
    {π₁ : Representation ℂ (GL (Fin n) k) W} {π₂ : Representation ℂ (GL (Fin n) k) U}
    (ι : π₁.IntertwiningMap π) (p : π.IntertwiningMap π₂) (hπ : IsSmooth π)
    (hι : Function.Injective ι) (hp : Function.Surjective p) (he : Function.Exact ι p)
    (w : List ℂˣ) : wordMult π w = wordMult π₁ w + wordMult π₂ w := by
  unfold wordMult
  split_ifs
  swap
  · simp
  refine jhMult_exact (compMap (jacMap (points _) ι) _) (compMap (jacMap (points _) p) _)
    (isIrreducible_ofChar _) (GlobalTheory.T.jacquetModule_map_injective_of_injective k _ _ _ (points _) W V π₁ π ι hπ hι) (fun x => ?_)
    (fun x => ?_) (fun x hx => ?_)
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨v, rfl⟩ := hp u
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    show Submodule.Quotient.mk (p (ι u)) = 0
    rw [he.apply_apply_eq_zero]
    rfl
  · obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : p v ∈ twKer π₂ (unipRad k (points (Fin n))) 1 :=
      (Submodule.Quotient.mk_eq_zero _).1 hx
    obtain ⟨v', hv', h2⟩ := exists_mem_twKer p hp _ h1
    obtain ⟨u, hu⟩ := (he (v - v')).1 (by rw [map_sub, h2, sub_self])
    refine ⟨Submodule.Quotient.mk u, ?_⟩
    show Submodule.Quotient.mk (ι u) = Submodule.Quotient.mk v
    rw [hu]
    exact (Submodule.Quotient.eq _).2 (by simpa using hv')

theorem wordMult_of_subsingleton [Subsingleton V] (π : Representation ℂ (GL (Fin n) k) V)
    (w : List ℂˣ) : wordMult π w = 0 := by
  unfold wordMult
  split_ifs
  · have : Subsingleton (Jacquet π (unipB k (Fin n))) :=
      (Submodule.Quotient.mk_surjective _).subsingleton
    exact jhMult_of_subsingleton (isIrreducible_ofChar _) _
  · rfl

theorem sum_add {I : Type 1} (f : I → ℕ∞) (x y : I →₀ ℤ) (hx : ∀ c, 0 ≤ x c) (hy : ∀ c, 0 ≤ y c) :
    ((x + y).sum fun c a => (a.toNat : ℕ∞) * f c) =
      (x.sum fun c a => (a.toNat : ℕ∞) * f c) + y.sum fun c a => (a.toNat : ℕ∞) * f c := by
  classical
  rw [Finsupp.sum_of_support_subset (x + y) Finsupp.support_add _ (by simp),
    Finsupp.sum_of_support_subset x Finset.subset_union_left _ (by simp),
    Finsupp.sum_of_support_subset y Finset.subset_union_right _ (by simp),
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finsupp.add_apply, Int.toNat_add (hx c) (hy c), Nat.cast_add, add_mul]

theorem wordMult_eq_sum (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π)
    (hπ : IsSmooth π) (w : List ℂˣ) :
    wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
  have φ := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := π)
  obtain ⟨_, _⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have : WellFoundedGT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedGT
  have : WellFoundedLT (Subrepresentation π) := φ.toOrderEmbedding.wellFoundedLT
  have hfl : ∀ S : Subrepresentation π, HasFiniteLength S.toRepresentation := fun S =>
    IsFiniteLength.of_injective h
      (f := Representation.IntertwiningMap.equivLinearMapAsModule S.toRepresentation π
        ⟨S.toSubmodule.subtype, fun _ => rfl⟩) Subtype.val_injective
  have hsm : ∀ S : Subrepresentation π, IsSmooth S.toRepresentation := fun S =>
    (IsSubquotient.of_injective (σ := S.toRepresentation) (ρ := π)
      ⟨S.toSubmodule.subtype, fun _ => rfl⟩ Subtype.val_injective).isSmooth hπ
  have key : ∀ S : Subrepresentation π, wordMult S.toRepresentation w =
      (cls S.toRepresentation (hfl S)).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w := by
    intro S
    induction S using WellFoundedLT.induction with
    | ind S ih =>
    rcases eq_or_ne S ⊥ with rfl | hS
    · have : Subsingleton (⊥ : Subrepresentation π).toSubmodule :=
        inferInstanceAs (Subsingleton (⊥ : Submodule ℂ V))
      have h0 : cls (⊥ : Subrepresentation π).toRepresentation (hfl ⊥) = 0 := by
        ext c
        simp [cls_apply, jhMult_of_subsingleton (IrrRep.irr _)]
      rw [h0, wordMult_of_subsingleton, Finsupp.sum_zero_index]
    obtain ⟨T, -, hT⟩ := exists_le_covBy_of_lt (bot_lt_iff_ne_bot.2 hS)
    let ι : T.toRepresentation.IntertwiningMap S.toRepresentation :=
      ⟨Submodule.inclusion hT.le, fun _ => rfl⟩
    let p : S.toRepresentation.IntertwiningMap (subQuot S T) := ⟨Submodule.mkQ _, fun _ => rfl⟩
    have hp : ∀ v, p v = 0 ↔ v.1 ∈ T.toSubmodule := fun v => Submodule.Quotient.mk_eq_zero _
    have hι : Function.Injective ι := Submodule.inclusion_injective hT.le
    have hps : Function.Surjective p := Submodule.Quotient.mk_surjective _
    have he : Function.Exact ι p := fun v =>
      ⟨fun hv => ⟨⟨v.1, (hp v).1 hv⟩, rfl⟩, by
        rintro ⟨u, rfl⟩
        exact (hp _).2 u.2⟩
    let σ : IrrRep (GL (Fin n) k) :=
      ⟨_, subQuot S T, (IsSubquotient.of_surjective p hps).isSmooth (hsm S),
        isIrreducible_subQuot hT⟩
    have hσ : cls (subQuot S T) σ.hasFiniteLength = Finsupp.single σ.cl 1 := cls_irr σ _
    obtain ⟨ψ⟩ := σ.nonempty_equiv_rep
    rw [wordMult_exact ι p (hsm S) hι hps he, cls_exact ι p hι hps he _ (hfl T) σ.hasFiniteLength,
      sum_add _ _ _ (fun c => by simp [cls_apply]) (fun c => by simp [cls_apply]), ih T hT.lt, hσ,
      Finsupp.sum_single_index (by simp), wordMult_congr ψ]
    simp [σ]
  rw [← wordMult_congr (topEquiv π), key ⊤, cls_congr (topEquiv π) _ h]

theorem wordMult_additive : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (h : HasFiniteLength π), IsSmooth π → ∀ w : List ℂˣ, wordMult π w = (cls π h).sum fun c a => (a.toNat : ℕ∞) * wordMult c.rep.ρ w :=
  fun _ _ _ _ _ _ _ _ _ π h hπ w => wordMult_eq_sum π h hπ w

end GlobalTheory.SmGL.Exponents.Additive
