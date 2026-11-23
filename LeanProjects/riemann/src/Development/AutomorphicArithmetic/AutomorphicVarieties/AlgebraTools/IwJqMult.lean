import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameParahoricRepSplitsAsProduct
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools GlobalTheory.PRep

namespace UpperTheory.V.AlgebraTools.JqMult

section Lin

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private def Tri (ρ : Representation ℂ G V) {N : ℕ} (χ : Fin N → G →* ℂˣ) : Prop :=
  ∃ S : Fin (N + 1) → Submodule ℂ V, Monotone S ∧ S 0 = ⊥ ∧ S (Fin.last N) = ⊤ ∧ ∀ t : Fin N,
    (∀ x ∈ S t.succ, ∀ y ∈ S t.succ, y ∈ S t.castSucc ∨ ∃ a : ℂ, x - a • y ∈ S t.castSucc) ∧
      ∀ g, ∀ x ∈ S t.succ, ρ g x - (χ t g : ℂ) • x ∈ S t.castSucc

private theorem Tri.sq {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {N : ℕ} {χ : Fin N → G →* ℂˣ}
    (h : Tri ρ χ) (hs : IsSubquotient σ ρ) : Tri σ χ := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  obtain ⟨U, f, hf⟩ := hs
  refine ⟨fun i => ((S i).comap U.toSubmodule.subtype).map f.toLinearMap,
    fun i j hij => Submodule.map_mono (Submodule.comap_mono (h1 hij)), ?_, ?_, fun t => ⟨?_, ?_⟩⟩
  · simp [h2]
  · simp only [h3, Submodule.comap_top, Submodule.map_top]
    exact LinearMap.range_eq_top.2 hf
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rcases (h4 t).1 _ hx _ hy with h | ⟨a, h⟩
    · exact Or.inl ⟨y, h, rfl⟩
    · exact Or.inr ⟨a, x - a • y, h, by simp⟩
  · rintro g _ ⟨x, hx, rfl⟩
    refine ⟨U.toRepresentation g x - (χ t g : ℂ) • x, (h4 t).2 g _ hx, ?_⟩
    rw [map_sub, map_smul]
    congr 1
    exact f.isIntertwining _ _ g x

private theorem bound {N : ℕ} (S : Fin (N + 1) → Submodule ℂ V) (h1 : Monotone S) (h2 : S 0 = ⊥)
    (h4 : ∀ t : Fin N, ∀ x ∈ S t.succ, ∀ y ∈ S t.succ, y ∈ S t.castSucc ∨ ∃ a : ℂ, x - a • y ∈ S t.castSucc)
    (E : Submodule ℂ V) (p : Fin N → Prop) [DecidablePred p]
    (hp : ∀ t, ¬ p t → E ⊓ S t.succ ≤ S t.castSucc) (i : Fin (N + 1)) :
    FiniteDimensional ℂ (E ⊓ S i : Submodule ℂ V) ∧ Module.finrank ℂ (E ⊓ S i : Submodule ℂ V) ≤
      (Finset.univ.filter fun t : Fin N => t.val < i.val ∧ p t).card := by
  induction i using Fin.induction with
  | zero => rw [h2, inf_bot_eq]; exact ⟨inferInstance, by simp⟩
  | succ t ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hsub : (Finset.univ.filter fun s : Fin N => s.val < t.castSucc.val ∧ p s) ⊆
        (Finset.univ.filter fun s : Fin N => s.val < t.succ.val ∧ p s) := by
      intro s
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc, Fin.val_succ]
      exact fun h => ⟨by omega, h.2⟩
    by_cases hle : E ⊓ S t.succ ≤ S t.castSucc
    · have : E ⊓ S t.succ = E ⊓ S t.castSucc :=
        le_antisymm (le_inf inf_le_left hle) (inf_le_inf_left _ (h1 t.castSucc_le_succ))
      rw [this]
      exact ⟨ih1, ih2.trans (Finset.card_le_card hsub)⟩
    · have hpt : p t := by_contra fun h => hle (hp t h)
      obtain ⟨y, hy, hy'⟩ := SetLike.not_le_iff_exists.1 hle
      have hle2 : E ⊓ S t.succ ≤ (E ⊓ S t.castSucc) ⊔ Submodule.span ℂ {y} := by
        intro x hx
        obtain ⟨a, ha⟩ := (h4 t x hx.2 y hy.2).resolve_left hy'
        have : x = (x - a • y) + a • y := by simp
        rw [this]
        exact Submodule.add_mem_sup ⟨sub_mem hx.1 (E.smul_mem a hy.1), ha⟩
          (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self y))
      refine ⟨Submodule.finiteDimensional_of_le hle2, (Submodule.finrank_mono hle2).trans ?_⟩
      refine (Submodule.finrank_add_le_finrank_add_finrank _ _).trans ?_
      have h5 : Module.finrank ℂ (Submodule.span ℂ {y}) ≤ 1 := by
        simpa using finrank_span_le_card (R := ℂ) ({y} : Set V)
      have h6 := Finset.card_lt_card (Finset.ssubset_iff_of_subset hsub |>.2 ⟨t, by simp [hpt], by simp⟩)
      omega

private theorem Tri.fin {ρ : Representation ℂ G V} {N : ℕ} {χ : Fin N → G →* ℂˣ} (h : Tri ρ χ) :
    FiniteDimensional ℂ V ∧ Module.finrank ℂ V ≤ N := by
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  have := bound S h1 h2 (fun t => (h4 t).1) ⊤ (fun _ => True) (fun t h => (h trivial).elim) (Fin.last N)
  rw [h3, inf_top_eq] at this
  obtain ⟨a, b⟩ := this
  refine ⟨Module.Finite.equiv Submodule.topEquiv, ?_⟩
  rw [finrank_top] at b
  exact b.trans ((Finset.card_le_univ _).trans (by simp))

private theorem Tri.eig {ρ : Representation ℂ G V} {N : ℕ} {χ : Fin N → G →* ℂˣ} (h : Tri ρ χ) (μ : G →* ℂˣ) :
    Module.finrank ℂ (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ) : Submodule ℂ V) ≤
      Nat.card {t // μ = χ t} := by
  classical
  obtain ⟨S, h1, h2, h3, h4⟩ := h
  have := (bound S h1 h2 (fun t => (h4 t).1) (⨅ t, Module.End.maxGenEigenspace (ρ t) (μ t : ℂ))
    (fun t => μ = χ t) (fun t h => ?_) (Fin.last N)).2
  · rw [h3, inf_top_eq] at this
    refine this.trans ?_
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    exact Finset.card_le_card fun s => by simp
  · obtain ⟨g, hg⟩ : ∃ g, μ g ≠ χ t g := by
      by_contra! hh
      exact h (MonoidHom.ext hh)
    rintro x ⟨hx, hx'⟩
    obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace _ _ _).1 ((Submodule.mem_iInf _).1 hx g)
    have key : ∀ (m : ℕ), ∀ x ∈ S t.succ, ((ρ g - (μ g : ℂ) • (1 : Module.End ℂ V)) ^ m) x -
        ((χ t g : ℂ) - μ g) ^ m • x ∈ S t.castSucc := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
        intro x hx
        have a1 := (h4 t).2 g x hx
        have a2 : (ρ g - (μ g : ℂ) • (1 : Module.End ℂ V)) x ∈ S t.succ := by
          have := add_mem (h1 t.castSucc_le_succ a1) ((S t.succ).smul_mem ((χ t g : ℂ) - μ g) hx)
          convert this using 1
          simp [sub_smul]
        have := add_mem (ih _ a2) ((S t.castSucc).smul_mem (((χ t g : ℂ) - μ g) ^ m) a1)
        convert this using 1
        rw [pow_succ, Module.End.mul_apply]
        simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
        module
    have h5 := key m x hx'
    rw [hm, zero_sub, neg_mem_iff] at h5
    refine (Submodule.smul_mem_iff _ (pow_ne_zero m (sub_ne_zero.2 fun h => hg (Units.ext h.symm)))).1 h5

end Lin

section Cell

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem deltaHalf_one {α : Type} [Fintype α] [LinearOrder α] {c : α → Type} [∀ a, Fintype (c a)]
    [∀ a, DecidableEq (c a)] (a : α) (ha : ∀ b, b ≠ a → IsEmpty (c b)) (g : Levi k c) : deltaHalf k c g = 1 := by
  have h2 : modExp c a = 0 := by
    unfold modExp
    rw [Finset.sum_eq_zero, Finset.sum_eq_zero, sub_zero]
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne
      simp
    · intro b hb
      have := ha b (Finset.mem_filter.1 hb).2.ne'
      simp
  rw [deltaHalf_apply]
  refine Finset.prod_eq_one fun b _ => ?_
  by_cases hb : b = a
  · subst hb
    simp [h2]
  · have := ha b hb
    rw [Subsingleton.elim (g b) 1, map_one, map_one]

private theorem row {n : ℕ} {c : Fin n → Fin n → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (w : Equiv.Perm (Fin n)) (hw : ∀ i j, i ≠ w j → IsEmpty (c i j))
    (f : ∀ i, (Σ j, c i j) ≃ Unit) (ψ : Fin n → kˣ →* ℂˣ)
    (ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ)
    (hρ : ∀ t v, ρ t v = (torusChar ψ ((leviTorus k (Fin n)).symm t) : ℂ) * v)
    (p : ∀ i, Levi k (c i)) (y : Jacquet ρ (relUnip k f)) :
    relJac f ρ p y = ((∏ j, ψ (w j) (GeneralLinearGroup.det (p (w j) j)) : ℂˣ) : ℂ) • y := by
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  have d2 : relDeltaHalf k c p = 1 := by
    rw [relDeltaHalf_apply]
    exact Finset.prod_eq_one fun i _ => deltaHalf_one (w.symm i) (fun j hj => hw i j fun h => hj (by simp [h])) _
  have e : torusChar ψ ((leviTorus k (Fin n)).symm (relEmb k f p)) =
      ∏ j, ψ (w j) (GeneralLinearGroup.det (p (w j) j)) := by
    rw [torusChar_apply, ← Equiv.prod_comp w]
    refine Finset.prod_congr rfl fun j _ => congrArg _ ?_
    refine (det_leviEmb k (f (w j)) (p (w j))).trans (Finset.prod_eq_single j (fun i _ hi => ?_) (by simp))
    have := hw (w j) i (fun h => hi (w.injective h).symm)
    rw [Subsingleton.elim (p (w j) i) 1, map_one]
  rw [relJac_mk, d2, inv_one, Units.val_one, one_smul, hρ, e, ← smul_eq_mul, Submodule.Quotient.mk_smul]

private theorem col {n : ℕ} {c : Fin n → Fin n → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (w : Fin n → Fin n) (hw : ∀ j i, i ≠ w j → IsEmpty (c j i))
    (g : ∀ j, (Σ i, c j i) ≃ Unit) (ψ : Fin n → kˣ →* ℂˣ) {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (τ : Representation ℂ (∀ j, Levi k (c j)) Y)
    (hτ : ∀ p y, τ p y = ((∏ j, ψ j (GeneralLinearGroup.det (p j (w j))) : ℂˣ) : ℂ) • y)
    (hY : ∀ x y : Y, y = 0 ∨ ∃ a : ℂ, x = a • y) :
    (∀ t x, relInd (m := fun _ => Unit) g τ t x = (torusChar ψ ((leviTorus k (Fin n)).symm t) : ℂ) • x) ∧
      ∀ x y : smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g))),
        y = 0 ∨ ∃ a : ℂ, x = a • y := by
  have hP : ∀ t : Levi k (fun _ : Fin n => Unit), t ∈ relParab k g := fun t j _ =>
    mem_parab.2 fun a b h => absurd h (by rw [Subsingleton.elim a b]; exact lt_irrefl _)
  have law : ∀ (x : smoothPart (ind (relParab k g) ((twist τ (relDeltaHalf k c)).comp (relProj k g)))) t s,
      x.1.1 (t * s) = (torusChar ψ ((leviTorus k (Fin n)).symm t) : ℂ) • x.1.1 s := by
    intro x t s
    refine (x.1.2 ⟨t, hP t⟩ s).trans ?_
    generalize x.1.1 s = y
    have d1 : relDeltaHalf k c (relProj k g ⟨t, hP t⟩) = 1 := by
      rw [relDeltaHalf_apply]
      exact Finset.prod_eq_one fun j _ => deltaHalf_one (w j) (fun i hi => hw j i hi) _
    have e : ∏ j, ψ j (GeneralLinearGroup.det (relProj k g ⟨t, hP t⟩ j (w j))) =
        torusChar ψ ((leviTorus k (Fin n)).symm t) := by
      rw [torusChar_apply]
      refine Finset.prod_congr rfl fun j _ => congrArg _ (Eq.symm ?_)
      refine (det_parab k (g j) ⟨t j, hP t j trivial⟩).trans
        (Finset.prod_eq_single (w j) (fun i _ hi => ?_) (by simp))
      have := hw j i hi
      rw [Subsingleton.elim (leviProj k (g j) _ i) 1, map_one]
    rw [MonoidHom.comp_apply, twist_apply, d1, hτ, e, Units.val_one, one_smul]
  refine ⟨fun t x => Subtype.ext (Subtype.ext (funext fun s => ?_)), fun x y => ?_⟩
  · show x.1.1 (s * t) = (torusChar ψ ((leviTorus k (Fin n)).symm t) : ℂ) • x.1.1 s
    have : s * t = t * s := by
      apply (leviTorus k (Fin n)).symm.injective
      rw [map_mul, map_mul, mul_comm]
    rw [this, law]
  · have h1 := fun s => law x s 1
    have h2 := fun s => law y s 1
    simp only [mul_one] at h1 h2
    rcases hY (x.1.1 1) (y.1.1 1) with h | ⟨a, h⟩
    · refine Or.inl (Subtype.ext (Subtype.ext (funext fun s => ?_)))
      have := h2 s
      rw [h, smul_zero] at this
      exact this
    · refine Or.inr ⟨a, Subtype.ext (Subtype.ext (funext fun s => ?_))⟩
      show x.1.1 s = a • y.1.1 s
      rw [h1 s, h2 s, h, smul_comm]

private theorem quot_line (U : Submodule ℂ ℂ) (x y : ℂ ⧸ U) : y = 0 ∨ ∃ a : ℂ, x = a • y := by
  obtain ⟨u, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  by_cases h0 : v = 0
  · exact Or.inl (by rw [h0, Submodule.Quotient.mk_zero])
  · exact Or.inr ⟨u / v, by rw [← Submodule.Quotient.mk_smul, smul_eq_mul, div_mul_cancel₀ _ h0]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
private theorem step {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} {S T : Subrepresentation ρ} (φ : (subQuot S T).Equiv σ)
    (χ : G →* ℂˣ) (c1 : ∀ t x, σ t x = (χ t : ℂ) • x) (c2 : ∀ x y : W, y = 0 ∨ ∃ a : ℂ, x = a • y) :
    (∀ x ∈ S.toSubmodule, ∀ y ∈ S.toSubmodule, y ∈ T.toSubmodule ∨ ∃ a : ℂ, x - a • y ∈ T.toSubmodule) ∧
      ∀ g, ∀ x ∈ S.toSubmodule, ρ g x - (χ g : ℂ) • x ∈ T.toSubmodule := by
  have key : ∀ x : S.toSubmodule, φ (Submodule.Quotient.mk x) = 0 → x.1 ∈ T.toSubmodule :=
    fun x hx => (Submodule.Quotient.mk_eq_zero (T.toSubmodule.comap S.toSubmodule.subtype)).1 (φ.injective (hx.trans (map_zero φ).symm))
  refine ⟨fun x hx y hy => ?_, fun g x hx => ?_⟩
  · rcases c2 (φ (Submodule.Quotient.mk ⟨x, hx⟩)) (φ (Submodule.Quotient.mk ⟨y, hy⟩)) with h | ⟨a, h⟩
    · exact Or.inl (key _ h)
    · refine Or.inr ⟨a, key (⟨x, hx⟩ - a • ⟨y, hy⟩) ?_⟩
      rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, h, sub_self]
  · refine key (S.toRepresentation g ⟨x, hx⟩ - (χ g : ℂ) • ⟨x, hx⟩) ?_
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul, map_sub, map_smul, sub_eq_zero]
    exact (φ.toIntertwiningMap.isIntertwining _ _ g (Submodule.Quotient.mk ⟨x, hx⟩)).trans (c1 g _)

private theorem cell {n : ℕ} {c : Fin n → Fin n → Type} [∀ i j, Fintype (c i j)] [∀ i j, DecidableEq (c i j)]
    (w : Equiv.Perm (Fin n)) (hw : ∀ i j, i ≠ w j → IsEmpty (c i j))
    (f : ∀ i, (Σ j, c i j) ≃ Unit) (g : ∀ j, (Σ i, c i j) ≃ Unit) (ψ : Fin n → kˣ →* ℂˣ)
    (ρ : Representation ℂ (Levi k fun _ : Fin n => Unit) ℂ)
    (hρ : ∀ t v, ρ t v = (torusChar ψ ((leviTorus k (Fin n)).symm t) : ℂ) * v)
    {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (Levi k fun _ : Fin n => Unit) V}
    {S T : Subrepresentation π}
    (φ : (subQuot S T).Equiv (cellFunctor (m := fun _ => Unit) (m' := fun _ => Unit) f g ρ)) :
    (∀ x ∈ S.toSubmodule, ∀ y ∈ S.toSubmodule, y ∈ T.toSubmodule ∨ ∃ a : ℂ, x - a • y ∈ T.toSubmodule) ∧
      ∀ t, ∀ x ∈ S.toSubmodule, π t x - (((torusChar (ψ ∘ w)).comp (leviTorus k (Fin n)).symm.toMonoidHom) t : ℂ) • x ∈
        T.toSubmodule := by
  have h := col (k := k) (c := fun j i => c i j) w (fun j i => hw i j) g (ψ ∘ w)
    ((relJac (m := fun _ => Unit) f ρ).comp (swapBlocks k c))
    (fun p y => row w hw f ψ ρ hρ (swapBlocks k c p) y) (quot_line _)
  exact step φ _ h.1 h.2

private theorem exists_perm {n : ℕ} (b : SizeMatrix (fun _ : Fin n => Unit) (fun _ : Fin n => Unit)) :
    ∃ w : Equiv.Perm (Fin n), ∀ i j, b.1 i j = if i = w j then 1 else 0 := by
  have col : ∀ j, ∃ i, ∀ i', b.1 i' j = if i' = i then 1 else 0 := fun j => by
    have hsum : ∑ i, b.1 i j = 1 := by simpa using b.2.2 j
    obtain ⟨i, -, hi0⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    have hsplit := Finset.add_sum_erase Finset.univ (fun i => b.1 i j) (Finset.mem_univ i)
    refine ⟨i, fun i' => ?_⟩
    split_ifs with h
    · subst h; simp only at hsplit; omega
    · have h0 : ∑ i ∈ Finset.univ.erase i, b.1 i j = 0 := by simp only at hsplit; omega
      exact Finset.sum_eq_zero_iff.1 h0 i' (Finset.mem_erase.2 ⟨h, Finset.mem_univ _⟩)
  choose w hw using col
  have hs : Function.Surjective w := fun i => by
    have hsum : ∑ j, b.1 i j = 1 := by simpa using b.2.1 i
    obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.trans_ne one_ne_zero)
    refine ⟨j, by_contra fun h => hj ?_⟩
    rw [hw, if_neg (Ne.symm h)]
  exact ⟨Equiv.ofBijective w ⟨Finite.injective_iff_surjective.2 hs, hs⟩, fun i j => hw j i⟩

private theorem tri_prin (hG : JacquetOfInducedFiltration k) {n : ℕ} {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) : ∃ (N : ℕ) (w : Fin N → Equiv.Perm (Fin n)), Function.Injective w ∧
      Tri (jac (points (Fin n)) (prinSeries ψ))
        fun t => (torusChar (ψ ∘ w t)).comp (leviTorus k (Fin n)).symm.toMonoidHom := by
  obtain ⟨N, b, hb⟩ := hG (Fin n) (Fin n) (Fin n) (fun _ => Unit) (fun _ => Unit) (points _) (points _)
  have hs : IsSmoothChar (torusChar ψ) := by
    unfold torusChar
    refine Finset.prod_induction _ IsSmoothChar (fun _ _ => IsSmoothChar.mul) isSmoothChar_one fun a _ => ?_
    exact (hψ a).comp _ (continuous_apply a)
  obtain ⟨S, h1, h2, h3, h4⟩ := hb ℂ ((ofChar (torusChar ψ)).comp (leviTorus k (Fin n)).symm.toMonoidHom)
    (isSmooth_comp ((isSmooth_ofChar_iff _).2 hs) _ (continuous_pi fun i =>
      continuous_glDet.comp (continuous_apply i)))
  choose w hw using exists_perm (n := n)
  refine ⟨N, fun t => w (b t), fun s t h => b.injective (Subtype.ext (funext fun i => funext fun j => ?_)),
    fun i => (S i).toSubmodule, fun i j hij => h1 hij, by simp only [h2]; rfl, by simp only [h3]; rfl, fun t => ?_⟩
  · rw [hw, hw]
    simp only at h
    rw [h]
  · obtain ⟨φ⟩ := h4 t (b t).nonempty_rows.some (b t).nonempty_cols.some
    have he : ∀ i j, i ≠ w (b t) j → IsEmpty (Fin ((b t).1 i j)) := fun i j h => by
      rw [hw, if_neg h]; infer_instance
    exact cell (w (b t)) he _ _ ψ _ (fun t v => ofChar_apply _ _ _) φ

private theorem sq_jac {n : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {π : Representation ℂ (GL (Fin n) k) V} {τ : Representation ℂ (GL (Fin n) k) W} (hτ : IsSmooth τ)
    (h : IsSubquotient π τ) : IsSubquotient (jac (points (Fin n)) π) (jac (points (Fin n)) τ) := by
  obtain ⟨S, f, hf⟩ := h
  let ι : S.toRepresentation.IntertwiningMap τ := ⟨S.toSubmodule.subtype, fun _ => rfl⟩
  refine (IsSubquotient.of_surjective (jacMap _ f) fun y => ?_).trans (.of_injective (jacMap _ ι) ?_)
  · obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨v, rfl⟩ := hf w
    exact ⟨Submodule.Quotient.mk v, rfl⟩
  · refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h1 : ι v ∈ twKer τ (unipRad k (points (Fin n))) 1 := (Submodule.Quotient.mk_eq_zero _).1 hx
    have hN := GlobalTheory.InertSupp.unipRad_eq_unipOf k (e := points (Fin n))
      (c := fun i => ((blk (points (Fin n)) i).val : ℤ)) fun i j => by simp
    obtain ⟨T, hT, h2⟩ := GlobalTheory.JacquetExact.exists_finset_of_mem_twKer h1
    obtain ⟨H, hle, hH, hSH⟩ := GlobalTheory.UnipCompact.exists_compact_subgroup k _ _ T (hN ▸ hT)
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    exact GlobalTheory.IwahoriInj.twKer_mono (hle.trans hN.ge)
      (GlobalTheory.JacquetExact.mem_twKer_of_compact hτ ι Subtype.val_injective hH (h2 H hSH))

private theorem tri_jacB (hG : JacquetOfInducedFiltration k) {n : ℕ} {ψ : Fin n → kˣ →* ℂˣ}
    (hψ : ∀ i, IsSmoothChar (ψ i)) {V : Type} [AddCommGroup V] [Module ℂ V] {π : Representation ℂ (GL (Fin n) k) V}
    (h : IsSubquotient π (prinSeries ψ)) : ∃ (N : ℕ) (w : Fin N → Equiv.Perm (Fin n)), Function.Injective w ∧
      Tri (jacB π) fun t => torusChar (ψ ∘ w t) := by
  obtain ⟨N, w, hw, hT⟩ := tri_prin hG hψ
  obtain ⟨S, h1, h2, h3, h4⟩ := hT.sq (sq_jac (isSmooth_parInd _ _) h)
  refine ⟨N, w, hw, S, h1, h2, h3, fun t => ⟨(h4 t).1, fun g x hx => ?_⟩⟩
  have := (h4 t).2 (leviTorus k (Fin n) g) x hx
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply] at this
  exact this

end Cell

end UpperTheory.V.AlgebraTools.JqMult

theorem UpperTheory.V.AlgebraTools.jqMult :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin n) k) V) (ψ : Fin n → kˣ →* ℂˣ), IsSmooth π → (∀ i, IsSmoothChar (ψ i)) → IsSubquotient π (prinSeries ψ) → FiniteDimensional ℂ (Jacquet π (unipB k (Fin n))) ∧ Module.finrank ℂ (Jacquet π (unipB k (Fin n))) ≤ n.factorial ∧ ∀ μ : (Fin n → kˣ) →* ℂˣ, Module.finrank ℂ (⨅ t, Module.End.maxGenEigenspace (jacB π t) (μ t : ℂ) : Submodule ℂ (Jacquet π (unipB k (Fin n)))) ≤ Nat.card {w : Equiv.Perm (Fin n) // μ = torusChar (ψ ∘ w)} := by
  intro hG _ k _ _ _ _ n V _ _ π ψ _ hψ h
  obtain ⟨N, w, hw, hT⟩ := JqMult.tri_jacB (hG k).1 hψ h
  refine ⟨hT.fin.1, hT.fin.2.trans ?_, fun μ => (hT.eig μ).trans ?_⟩
  · simpa [Fintype.card_perm] using Fintype.card_le_of_injective w hw
  · exact Nat.card_le_card_of_injective (fun t => ⟨w t.1, t.2⟩)
      fun s t h => Subtype.ext (hw (congrArg Subtype.val h))
