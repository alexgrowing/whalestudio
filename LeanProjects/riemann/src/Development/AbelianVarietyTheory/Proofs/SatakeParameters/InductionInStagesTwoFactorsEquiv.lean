import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

section Mid

variable (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {β : Type} [Fintype β] [LinearOrder β] {m : β → Type} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def blocks (h : a ⊕ b ≃ n) : parab k (two h) →* GL a k × GL b k :=
  (leviTwo k a b).symm.toMonoidHom.comp (leviProj k (two h))

theorem blocks_fst (h : a ⊕ b ≃ n) (q : parab k (two h)) (x y : a) :
    ((blocks k h q).1 : Matrix a a k) x y = (q : GL n k).val (h (.inl x)) (h (.inl y)) := rfl

theorem blocks_snd (h : a ⊕ b ≃ n) (q : parab k (two h)) (x y : b) :
    ((blocks k h q).2 : Matrix b b k) x y = (q : GL n k).val (h (.inr x)) (h (.inr y)) := rfl

def mid (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : Subgroup (GL n k) :=
  ((parab k ψ).comap ((MonoidHom.snd _ _).comp (blocks k h))).map (parab k (two h)).subtype

theorem mid_le (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ ≤ parab k (two h) :=
  Subgroup.map_subtype_le _

theorem coe_mem_mid (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (q : parab k (two h)) :
    (q : GL n k) ∈ mid k h ψ ↔ (blocks k h q).2 ∈ parab k ψ :=
  Subgroup.mem_map_iff_mem Subtype.val_injective

def midIncl (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* parab k (two h) :=
  Subgroup.inclusion (mid_le k h ψ)

def midSnd (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* parab k ψ :=
  ((MonoidHom.snd _ _).comp ((blocks k h).comp (midIncl k h ψ))).codRestrict (parab k ψ)
    fun q => (coe_mem_mid k h ψ (midIncl k h ψ q)).1 q.2

def midProj (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) : mid k h ψ →* Levi k m × GL a k :=
  ((leviProj k ψ).comp (midSnd k h ψ)).prod ((MonoidHom.fst _ _).comp ((blocks k h).comp (midIncl k h ψ)))

def midChar (ψ : (Σ j, m j) ≃ b) : Levi k m × GL a k →* ℂˣ :=
  (deltaHalf k (Two a b)).comp ((leviTwo k a b).toMonoidHom.comp
      ((MonoidHom.snd _ _).prod ((leviEmb k ψ).comp (MonoidHom.fst _ _)))) *
    (deltaHalf k m).comp (MonoidHom.fst _ _)

def midRep (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (ρ : Representation ℂ (Levi k m) W)
    (π : Representation ℂ (GL a k) V) : Representation ℂ (mid k h ψ) (W ⊗[ℂ] V) :=
  twist ((extTensor ρ π).comp (midProj k h ψ)) ((midChar k ψ).comp (midProj k h ψ))

end Mid

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b n : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  {β : Type} [Fintype β] [LinearOrder β] {m : β → Type} [∀ j, Fintype (m j)] [∀ j, DecidableEq (m j)]
  {V W U : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem stage_one (h : a ⊕ b ≃ n) (ψ : (Σ j, m j) ≃ b) (σ₀ : Representation ℂ (GL a k) V)
    (ρ : Representation ℂ (Levi k m) W) (σ : Representation ℂ (mid k h ψ) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hσ : ∀ (q : parab k (two h)) (hq : (q : GL n k) ∈ mid k h ψ) (hb : (blocks k h q).2 ∈ parab k ψ) x,
      σ ⟨q, hq⟩ (κ x) = ((deltaHalf k (Two a b) (leviProj k (two h) q) *
        deltaHalf k m (leviProj k ψ ⟨_, hb⟩) : ℂˣ) : ℂ) •
        κ (TensorProduct.map (σ₀ (blocks k h q).1) (ρ (leviProj k ψ ⟨_, hb⟩)) x)) :
    Nonempty ((ind₂ h (extTensor σ₀ (parInd ψ ρ))).Equiv (smInd (mid k h ψ) σ)) := by
  let j := ((emb₂ k h).comp (MonoidHom.inr _ _)).codRestrict (parab k (two h))
    fun _ => leviEmb_mem_parab k _ _
  refine smInd_stages (P' := parab k ψ) (mid_le k h ψ) (blocks k h) j ?_ (fun x => ?_)
    (fun q => coe_mem_mid k h ψ q) SplitFlip.isCompact_KO (fun x => exists_parab_mul _ x)
    ((deltaHalf k _).comp (leviTwo k _ _).toMonoidHom) ?_ σ₀ _ σ κ (fun q h1 h2 x => ?_) _ fun q x => rfl
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_right 1))
  · exact (leviTwo k _ _).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  · have h1' : IsSmoothChar (((deltaHalf k _).comp
        (leviTwo k a b).toMonoidHom).comp (MonoidHom.inr _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_right 1)
    filter_upwards [h1'.mem_nhds (one_mem _)] with u hu
    exact MonoidHom.mem_ker.1 hu
  · rw [hσ q h1 h2 x]
    show _ = (deltaHalf k _ (leviTwo k _ _ ((leviTwo k a b).symm (leviProj k (two h) q))) : ℂ) •
      κ (TensorProduct.map (σ₀ (blocks k h q).1) ((deltaHalf k _ (leviProj k ψ ⟨_, h2⟩) : ℂ) •
        ρ (leviProj k ψ ⟨_, h2⟩)) x)
    rw [MulEquiv.apply_symm_apply, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, smul_smul,
      Units.val_mul]

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

section Lex

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]

theorem sum_lex {M : Type} [AddCommMonoid M] (f : β₀ ⊕ₗ β₁ → M) :
    ∑ c, f c = ∑ i, f (toLex (Sum.inl i)) + ∑ j, f (toLex (Sum.inr j)) :=
  (toLex.sum_comp f).symm.trans (Fintype.sum_sum_type _)

theorem prod_lex {M : Type} [CommMonoid M] (f : β₀ ⊕ₗ β₁ → M) :
    ∏ c, f c = (∏ i, f (toLex (Sum.inl i))) * ∏ j, f (toLex (Sum.inr j)) :=
  (toLex.prod_comp f).symm.trans (Fintype.prod_sum_type _)

omit [∀ c, DecidableEq (m c)] in
theorem modExp_inl (i : β₀) : modExp m (toLex (Sum.inl i)) =
    modExp (fun i => m (toLex (Sum.inl i))) i + Fintype.card (Σ j, m (toLex (Sum.inr j))) := by
  simp only [modExp, Finset.sum_filter, Fintype.card_sigma, Nat.cast_sum]
  rw [sum_lex, sum_lex]
  simp [Sum.Lex.inl_lt_inl_iff, Sum.Lex.not_inr_lt_inl]
  ring

omit [∀ c, DecidableEq (m c)] in
theorem modExp_inr (j : β₁) : modExp m (toLex (Sum.inr j)) =
    modExp (fun j => m (toLex (Sum.inr j))) j - Fintype.card (Σ i, m (toLex (Sum.inl i))) := by
  simp only [modExp, Finset.sum_filter, Fintype.card_sigma, Nat.cast_sum]
  rw [sum_lex, sum_lex]
  simp [Sum.Lex.inr_lt_inr_iff, Sum.Lex.not_inr_lt_inl]
  ring

end Lex

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem deltaHalf_lex (g : Levi k m) :
    deltaHalf k m g = absPow k ((Fintype.card (Σ j, m (toLex (Sum.inr j))) : ℂ) / 2)
        (∏ i, GeneralLinearGroup.det (g (toLex (Sum.inl i)))) *
      absPow k (-(Fintype.card (Σ i, m (toLex (Sum.inl i))) : ℂ) / 2)
        (∏ j, GeneralLinearGroup.det (g (toLex (Sum.inr j)))) *
      deltaHalf k (fun i => m (toLex (Sum.inl i))) (fun i => g (toLex (Sum.inl i))) *
      deltaHalf k (fun j => m (toLex (Sum.inr j))) (fun j => g (toLex (Sum.inr j))) := by
  have A : ∀ i, absPow k ((modExp m (toLex (Sum.inl i)) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) =
      absPow k ((modExp (fun i => m (toLex (Sum.inl i))) i : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) *
      absPow k ((Fintype.card (Σ j, m (toLex (Sum.inr j))) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inl i)))) := by
    intro i
    rw [modExp_inl, ← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    push_cast
    ring
  have B : ∀ j, absPow k ((modExp m (toLex (Sum.inr j)) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) =
      absPow k ((modExp (fun j => m (toLex (Sum.inr j))) j : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) *
      absPow k (-(Fintype.card (Σ i, m (toLex (Sum.inl i))) : ℂ) / 2) (GeneralLinearGroup.det (g (toLex (Sum.inr j)))) := by
    intro j
    rw [modExp_inr, ← MonoidHom.mul_apply, ← absPow_add]
    congr 2
    push_cast
    ring
  rw [deltaHalf_apply, deltaHalf_apply, deltaHalf_apply, prod_lex, Finset.prod_congr rfl fun i _ => A i,
    Finset.prod_congr rfl fun j _ => B j, Finset.prod_mul_distrib, Finset.prod_mul_distrib, map_prod, map_prod]
  ac_rfl

variable (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a)
  (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)

theorem parab_lex_le (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) : parab k E ≤ parab k (two h) :=
  fun g hg => (mem_parab_two k).2 fun j' i' => by
    obtain ⟨⟨j, y⟩, rfl⟩ := ψ₁.surjective j'
    obtain ⟨⟨i, x⟩, rfl⟩ := ψ₀.surjective i'
    rw [h1, h0]
    exact mem_parab_iff.1 hg _ _ y x (Sum.Lex.inl_lt_inr _ _)

theorem mem_parab_lex_iff (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) (q : parab k (two h)) :
    (q : GL n k) ∈ parab k E ↔ (blocks k h q).1 ∈ parab k ψ₀ ∧ (blocks k h q).2 ∈ parab k ψ₁ := by
  constructor
  · intro hq
    refine ⟨mem_parab_iff.2 fun i i' x y hlt => ?_, mem_parab_iff.2 fun j j' x y hlt => ?_⟩
    · rw [blocks_fst, h0, h0]
      exact mem_parab_iff.1 hq _ _ x y (Sum.Lex.inl_lt_inl_iff.2 hlt)
    · rw [blocks_snd, h1, h1]
      exact mem_parab_iff.1 hq _ _ x y (Sum.Lex.inr_lt_inr_iff.2 hlt)
  · rintro ⟨hA, hB⟩
    refine mem_parab_iff.2 fun c c' u v hlt => ?_
    obtain ⟨c, rfl⟩ := toLex.surjective c
    obtain ⟨c', rfl⟩ := toLex.surjective c'
    rcases c with i | j <;> rcases c' with i' | j'
    · rw [← h0, ← h0]
      exact mem_parab_iff.1 hA i i' u v (Sum.Lex.inl_lt_inl_iff.1 hlt)
    · exact absurd hlt Sum.Lex.not_inr_lt_inl
    · rw [← h1, ← h0]
      exact (mem_parab_two k).1 q.2 _ _
    · rw [← h1, ← h1]
      exact mem_parab_iff.1 hB j j' u v (Sum.Lex.inr_lt_inr_iff.1 hlt)

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

open GlobalTheory.SmGL.MultiIrr

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

omit [Fintype n] in
theorem midChar_midProj {β : Type} [Fintype β] [LinearOrder β] {m' : β → Type} [∀ j, Fintype (m' j)]
    [∀ j, DecidableEq (m' j)] [Fintype n] (h : a ⊕ b ≃ n) (ψ : (Σ j, m' j) ≃ b) (q : mid k h ψ) :
    midChar k ψ (midProj k h ψ q) =
      deltaHalf k (Two a b) (leviProj k (two h) (midIncl k h ψ q)) * deltaHalf k m' (leviProj k ψ (midSnd k h ψ q)) := by
  show deltaHalf k (Two a b) (leviTwo k a b ((blocks k h (midIncl k h ψ q)).1,
    leviEmb k ψ (leviProj k ψ (midSnd k h ψ q)))) * _ = _
  have e : leviProj k (two h) (midIncl k h ψ q) = leviTwo k a b (blocks k h (midIncl k h ψ q)) :=
    (MulEquiv.apply_symm_apply _ _).symm
  rw [e, deltaHalf_two, deltaHalf_two, det_leviEmb, ← det_parab k ψ (midSnd k h ψ q)]
  rfl

theorem stage_two (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a)
    (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)
    (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩)
    (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V)
    (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hκ : ∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i)))
      (ρ₁ fun j => g (toLex (.inr j))) x)) :
    Nonempty ((smInd (mid k h ψ₁) (midRep k h ψ₁ ρ₁ (parInd ψ₀ ρ₀))).Equiv (parInd E σ)) := by
  have hle := parab_lex_le (k := k) E h ψ₀ ψ₁ h0 h1
  have hmem := mem_parab_lex_iff (k := k) E h ψ₀ ψ₁ h0 h1
  have eb : ∀ x : GL a k, blocks k h ⟨emb₂ k h (x, 1), leviEmb_mem_parab k _ _⟩ = (x, 1) := fun x =>
    (leviTwo k a b).symm_apply_eq.2 (leviProj_leviEmb k _ _)
  have hj : ∀ x : GL a k, (emb₂ k h).comp (MonoidHom.inl _ _) x ∈ mid k h ψ₁ := fun x =>
    (coe_mem_mid k h ψ₁ ⟨_, leviEmb_mem_parab k _ _⟩).2 (by
      show (blocks k h ⟨emb₂ k h (x, 1), leviEmb_mem_parab k _ _⟩).2 ∈ parab k ψ₁
      rw [eb]; exact one_mem _)
  let j := ((emb₂ k h).comp (MonoidHom.inl _ _)).codRestrict (mid k h ψ₁) hj
  refine smInd_stages (P' := parab k ψ₀) (ρ := (twist ρ₀ (deltaHalf k _)).comp (leviProj k ψ₀))
    (fun g hg => (coe_mem_mid k h ψ₁ ⟨g, hle hg⟩).2 ((hmem ⟨g, hle hg⟩).1 hg).2) (midProj k h ψ₁) j ?_
    (fun x => ?_) (fun q => ?_) SplitFlip.isCompact_KO (fun x => exists_parab_mul _ x) (midChar k ψ₁) ?_ ρ₁ _
    ((TensorProduct.comm ℂ W V).trans κ) (fun q h1' h2 x => ?_) _ fun q x => rfl
  · exact (continuous_leviEmb k _).comp ((continuous_leviTwo k).comp (Continuous.prodMk_left 1))
  · have e := eb x
    refine Prod.ext ?_ ?_
    · show leviProj k ψ₁ (midSnd k h ψ₁ (j x)) = 1
      have : midSnd k h ψ₁ (j x) = 1 := Subtype.ext (congrArg Prod.snd e)
      rw [this, map_one]
    · exact congrArg Prod.fst e
  · exact (hmem (midIncl k h ψ₁ q)).trans (and_iff_left ((coe_mem_mid k h ψ₁ _).1 q.2))
  · have hs : IsSmoothChar (((deltaHalf k _).comp (leviTwo k a b).toMonoidHom).comp (MonoidHom.inl _ _)) :=
      ((isSmoothChar_deltaHalf k).comp _ (continuous_leviTwo k)).comp _ (Continuous.prodMk_left 1)
    filter_upwards [hs.mem_nhds (one_mem _)] with u hu
    have := MonoidHom.mem_ker.1 hu
    show deltaHalf k _ (leviTwo k a b (u, leviEmb k ψ₁ 1)) * deltaHalf k _ 1 = 1
    rw [map_one, map_one, mul_one]
    exact this
  · let g := leviProj k E ⟨q, h1'⟩
    have e0 : leviProj k ψ₀ ⟨(midProj k h ψ₁ q).2, h2⟩ = fun i => g (toLex (.inl i)) :=
      funext fun i => Units.ext (Matrix.ext fun x y => by
        show (q : GL n k).val (h (.inl (ψ₀ ⟨i, x⟩))) (h (.inl (ψ₀ ⟨i, y⟩))) = (q : GL n k).val (E ⟨_, x⟩) (E ⟨_, y⟩)
        rw [h0, h0])
    have e1 : (midProj k h ψ₁ q).1 = fun j => g (toLex (.inr j)) :=
      funext fun j => Units.ext (Matrix.ext fun x y => by
        show (q : GL n k).val (h (.inr (ψ₁ ⟨j, x⟩))) (h (.inr (ψ₁ ⟨j, y⟩))) = (q : GL n k).val (E ⟨_, x⟩) (E ⟨_, y⟩)
        rw [h1, h1])
    have e2 : GeneralLinearGroup.det (midProj k h ψ₁ q).2 = ∏ i, GeneralLinearGroup.det (g (toLex (.inl i))) := by
      have := det_parab k ψ₀ ⟨_, h2⟩
      rwa [e0] at this
    have e3 : midChar k ψ₁ (midProj k h ψ₁ q) =
        absPow k ((Fintype.card b : ℂ) / 2) (GeneralLinearGroup.det (midProj k h ψ₁ q).2) *
        absPow k (-(Fintype.card a : ℂ) / 2) (GeneralLinearGroup.det (leviEmb k ψ₁ (midProj k h ψ₁ q).1)) *
        deltaHalf k _ (midProj k h ψ₁ q).1 := by
      show deltaHalf k (Two a b) (leviTwo k a b ((midProj k h ψ₁ q).2, leviEmb k ψ₁ (midProj k h ψ₁ q).1)) * _ = _
      rw [deltaHalf_two] <;> rfl
    have e4 : deltaHalf k m g = midChar k ψ₁ (midProj k h ψ₁ q) *
        deltaHalf k (fun i => m (toLex (Sum.inl i))) (fun i => g (toLex (.inl i))) := by
      rw [e3, e2, det_leviEmb, e1, deltaHalf_lex, ← Fintype.card_congr ψ₀, ← Fintype.card_congr ψ₁]
      ac_rfl
    have hc := TensorProduct.map_comm (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x
    show (deltaHalf k m g : ℂ) • σ g (κ (TensorProduct.comm ℂ W V x)) = (midChar k ψ₁ (midProj k h ψ₁ q) : ℂ) •
      κ (TensorProduct.comm ℂ W V (TensorProduct.map (ρ₁ (midProj k h ψ₁ q).1)
        ((deltaHalf k _ (leviProj k ψ₀ ⟨_, h2⟩) : ℂ) • ρ₀ (leviProj k ψ₀ ⟨_, h2⟩)) x))
    rw [hκ, e4, e0, e1, TensorProduct.map_smul_right, LinearMap.smul_apply, map_smul, map_smul, smul_smul,
      Units.val_mul, hc]

end GlobalTheory.SmGL.StagesTwo

namespace GlobalTheory.SmGL.StagesTwo

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {β₀ β₁ : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁]
  {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)]
  {a b n V W U : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U]

theorem ind₂_parInd_parInd_equiv_of (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n)
    (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b)
    (h0 : ∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩)
    (h1 : ∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩)
    (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V)
    (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U)
    (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U)
    (hκ : ∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i)))
      (ρ₁ fun j => g (toLex (.inr j))) x)) :
    Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  have hA := stage_one h ψ₁ (parInd ψ₀ ρ₀) ρ₁ (midRep k h ψ₁ ρ₁ (parInd ψ₀ ρ₀))
    (TensorProduct.comm ℂ _ _) fun q hq hb x => by
      have e := midChar_midProj h ψ₁ (⟨q, hq⟩ : mid k h ψ₁)
      show (midChar k ψ₁ (midProj k h ψ₁ ⟨q, hq⟩) : ℂ) • TensorProduct.map (ρ₁ (leviProj k ψ₁ ⟨_, hb⟩))
        (parInd ψ₀ ρ₀ (blocks k h q).1) (TensorProduct.comm ℂ _ _ x) = _
      rw [e, TensorProduct.map_comm]
      rfl
  have hB := stage_two E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ
  exact ⟨hA.some.trans hB.some⟩

theorem ind₂_parInd_parInd_equiv : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {β₀ β₁ a b n V W U : Type} [Fintype β₀] [LinearOrder β₀] [Fintype β₁] [LinearOrder β₁] [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype n] [DecidableEq n] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [AddCommGroup U] [Module ℂ U] {m : β₀ ⊕ₗ β₁ → Type} [∀ c, Fintype (m c)] [∀ c, DecidableEq (m c)] (E : (Σ c, m c) ≃ n) (h : a ⊕ b ≃ n) (ψ₀ : (Σ i, m (toLex (Sum.inl i))) ≃ a) (ψ₁ : (Σ j, m (toLex (Sum.inr j))) ≃ b), (∀ i x, h (.inl (ψ₀ ⟨i, x⟩)) = E ⟨toLex (.inl i), x⟩) → (∀ j x, h (.inr (ψ₁ ⟨j, x⟩)) = E ⟨toLex (.inr j), x⟩) → ∀ (ρ₀ : Representation ℂ (Levi k fun i => m (toLex (Sum.inl i))) V) (ρ₁ : Representation ℂ (Levi k fun j => m (toLex (Sum.inr j))) W) (σ : Representation ℂ (Levi k m) U) (κ : V ⊗[ℂ] W ≃ₗ[ℂ] U), (∀ g x, σ g (κ x) = κ (TensorProduct.map (ρ₀ fun i => g (toLex (.inl i))) (ρ₁ fun j => g (toLex (.inr j))) x)) → Nonempty ((ind₂ h (extTensor (parInd ψ₀ ρ₀) (parInd ψ₁ ρ₁))).Equiv (parInd E σ)) := by
  intro k _ _ _ _ β₀ β₁ a b n V W U _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m _ _ E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ
  exact ind₂_parInd_parInd_equiv_of E h ψ₀ ψ₁ h0 h1 ρ₀ ρ₁ σ κ hκ

end GlobalTheory.SmGL.StagesTwo
