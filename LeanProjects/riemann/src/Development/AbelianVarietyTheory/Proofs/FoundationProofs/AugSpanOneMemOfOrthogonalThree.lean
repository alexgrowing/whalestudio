import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAugmentationSpanEqIdOnIrreducibleStatement
open scoped Matrix

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ] {m : ℕ}

abbrev augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) : Submodule K (Matrix (Fin m) (Fin m) K) :=
  Submodule.span K (Set.range fun g => S g - 1)

def Stable (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∀ g, ∀ v ∈ P, S g *ᵥ v ∈ P

theorem mul_mem_augSpan (S : Γ →* Matrix (Fin m) (Fin m) K) {A C : Matrix (Fin m) (Fin m) K}
    (hA : A ∈ augSpan S) (hC : C ∈ augSpan S) : A * C ∈ augSpan S := by
  induction hA using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    induction hC using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨h, rfl⟩ := hy
      have e : (S g - 1) * (S h - 1) = (S (g * h) - 1) - (S g - 1) - (S h - 1) := by
        rw [map_mul]; noncomm_ring
      rw [e]
      exact Submodule.sub_mem _ (Submodule.sub_mem _ (Submodule.subset_span ⟨_, rfl⟩)
        (Submodule.subset_span ⟨_, rfl⟩)) (Submodule.subset_span ⟨_, rfl⟩)
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul a y _ hy => rw [Matrix.mul_smul]; exact Submodule.smul_mem _ a hy
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx => rw [Matrix.smul_mul]; exact Submodule.smul_mem _ a hx

theorem augSpan_preserves (S : Γ →* Matrix (Fin m) (Fin m) K) {P : Submodule K (Fin m → K)}
    (hP : Stable S P) {T : Matrix (Fin m) (Fin m) K} (hT : T ∈ augSpan S) :
    ∀ v ∈ P, T *ᵥ v ∈ P := by
  induction hT using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨g, rfl⟩ := hx
    intro v hv
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact P.sub_mem (hP g v hv) hv
  | zero => intro v _; rw [Matrix.zero_mulVec]; exact P.zero_mem
  | add x y _ _ hx hy => intro v hv; rw [Matrix.add_mulVec]; exact P.add_mem (hx v hv) (hy v hv)
  | smul a x _ hx => intro v hv; rw [Matrix.smul_mulVec]; exact P.smul_mem a (hx v hv)

def Good (S : Γ →* Matrix (Fin m) (Fin m) K) (P : Submodule K (Fin m → K)) : Prop :=
  ∃ T ∈ augSpan S, ∀ v ∈ P, T *ᵥ v = v

theorem good_sup (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) (gL : Good S L) (gP : Good S P) : Good S (L ⊔ P) := by
  obtain ⟨T₁, h₁, e₁⟩ := gL
  obtain ⟨T₂, h₂, e₂⟩ := gP
  refine ⟨T₁ + T₂ - T₁ * T₂, Submodule.sub_mem _ (Submodule.add_mem _ h₁ h₂)
    (mul_mem_augSpan S h₁ h₂), ?_⟩
  intro v hv
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  have hTa : T₂ *ᵥ a ∈ L := augSpan_preserves S hL h₂ a ha
  simp only [Matrix.sub_mulVec, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, Matrix.mulVec_add,
    e₁ a ha, e₂ b hb, e₁ _ hTa]
  abel

theorem good_bot (S : Γ →* Matrix (Fin m) (Fin m) K) : Good S ⊥ :=
  ⟨0, Submodule.zero_mem _, fun v hv => by
    rw [(Submodule.mem_bot K).mp hv, Matrix.mulVec_zero]⟩

theorem stable_inf (S : Γ →* Matrix (Fin m) (Fin m) K) {L P : Submodule K (Fin m → K)}
    (hL : Stable S L) (hP : Stable S P) : Stable S (L ⊓ P) :=
  fun g v hv => ⟨hL g v hv.1, hP g v hv.2⟩

theorem stable_orthogonal (S : Γ →* Matrix (Fin m) (Fin m) K)
    (B : LinearMap.BilinForm K (Fin m → K))
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) {Q : Submodule K (Fin m → K)}
    (hQ : Stable S Q) : Stable S (B.orthogonal Q) := by
  intro g v hv
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hv ⊢
  intro n hn
  have e : S g *ᵥ (S g⁻¹ *ᵥ n) = n := by
    rw [Matrix.mulVec_mulVec, ← map_mul, mul_inv_cancel, map_one, Matrix.one_mulVec]
  have := hv _ (hQ g⁻¹ n hn)
  rw [← e, hinv]
  exact this

end GlobalTheory.AugCore

namespace GlobalTheory.AugCore

variable {K : Type} [Field K] {Γ : Type} [Group Γ]

theorem inf_orthogonal_eq_bot (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊓ B.orthogonal Q = ⊥ := by
  set Z := Q ⊓ B.orthogonal Q with hZ
  have hZs : Stable S Z := stable_inf S hQ hQo
  have hZle : Z ≤ B.orthogonal Z := by
    intro z hz
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hz.2) n hn.1
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have hfo : Module.finrank K (B.orthogonal Z) = 3 - Module.finrank K Z := by
    rw [LinearMap.BilinForm.finrank_orthogonal hB, h3]
  have hmono := Submodule.finrank_mono hZle
  by_contra hne
  obtain ⟨y, hyZ, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  have hsp : (K ∙ y) ≤ Z := (Submodule.span_singleton_le_iff_mem y Z).mpr hyZ
  have h1 : Module.finrank K (K ∙ y) = 1 := finrank_span_singleton hy0
  have hspm := Submodule.finrank_mono hsp
  have hZ1 : Module.finrank K Z = 1 := by omega
  have heq : (K ∙ y) = Z := Submodule.eq_of_le_of_finrank_eq hsp (by rw [h1, hZ1])
  apply hiso y hy0
  · intro g
    have : S g *ᵥ y ∈ (K ∙ y) := by rw [heq]; exact hZs g y hyZ
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp this
    exact ⟨c, hc.symm⟩
  · exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hyZ.2) y hyZ.1

theorem sup_orthogonal_eq_top (S : Γ →* Matrix (Fin 3) (Fin 3) K)
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0)
    {Q : Submodule K (Fin 3 → K)} (hQ : Stable S Q) (hQo : Stable S (B.orthogonal Q)) :
    Q ⊔ B.orthogonal Q = ⊤ := by
  have h3 : Module.finrank K (Fin 3 → K) = 3 := Module.finrank_fin_fun K
  have key := Submodule.finrank_sup_add_finrank_inf_eq Q (B.orthogonal Q)
  rw [inf_orthogonal_eq_bot S B hB hiso hQ hQo, finrank_bot,
    LinearMap.BilinForm.finrank_orthogonal hB, h3] at key
  have hle := Submodule.finrank_le Q
  rw [h3] at hle
  apply Submodule.eq_top_of_finrank_eq
  rw [h3]; omega

theorem good_of_stable (S : Γ →* Matrix (Fin 3) (Fin 3) K) [IsAlgClosed K]
    (B : LinearMap.BilinForm K (Fin 3 → K)) (hB : B.Nondegenerate)
    (hinv : ∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w)
    (hfix : ∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0)
    (hiso : ∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) :
    ∀ n, ∀ P : Submodule K (Fin 3 → K), Stable S P → Module.finrank K P = n → Good S P := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro P hP hn
  by_cases hirr : ∀ Q : Submodule K (Fin 3 → K), Q ≤ P → Stable S Q → Q = ⊥ ∨ Q = P
  · by_cases hbot : P = ⊥
    · rw [hbot]; exact good_bot S
    · have hnt : ∃ g, ∃ v ∈ P, S g *ᵥ v ≠ v := by
        by_contra hc
        push_neg at hc
        apply hbot
        rw [Submodule.eq_bot_iff]
        intro v hv
        exact hfix v (fun g => hc g v hv)
      exact GlobalTheory.T.exists_augmentationSpan_eq_id_on_irreducible S P hP hirr hnt
  · push_neg at hirr
    obtain ⟨Q, hQP, hQs, hQ0, hQne⟩ := hirr
    have hQo : Stable S (B.orthogonal Q) := stable_orthogonal S B hinv hQs
    set R := P ⊓ B.orthogonal Q with hR
    have hRs : Stable S R := stable_inf S hP hQo
    have htop := sup_orthogonal_eq_top S B hB hiso hQs hQo
    have hinf := inf_orthogonal_eq_bot S B hB hiso hQs hQo
    have hQR : Q ⊔ R = P := by
      apply le_antisymm (sup_le hQP inf_le_left)
      intro v hv
      have hvt : v ∈ Q ⊔ B.orthogonal Q := by rw [htop]; trivial
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hvt
      have hbP : b ∈ P := by
        have := P.sub_mem hv (hQP ha)
        simpa using this
      exact Submodule.mem_sup.mpr ⟨a, ha, b, ⟨hbP, hb⟩, rfl⟩
    have hQlt : Module.finrank K Q < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne hQP hQne)
    have hRne : R ≠ P := by
      intro hRP
      apply hQ0
      rw [eq_bot_iff, ← hinf]
      intro x hx
      have : x ∈ R := by rw [hRP]; exact hQP hx
      exact ⟨hx, this.2⟩
    have hRlt : Module.finrank K R < n := by
      rw [← hn]; exact Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hRne)
    have g := good_sup S hQs hRs (ih _ hQlt Q hQs rfl) (ih _ hRlt R hRs rfl)
    rwa [hQR] at g

end GlobalTheory.AugCore

theorem GlobalTheory.augSpan_one_mem_of_orthogonal_three : ∀ {K : Type} [Field K] [IsAlgClosed K] [CharZero K] {Γ : Type} [Group Γ] (S : Γ →* Matrix (Fin 3) (Fin 3) K) (B : LinearMap.BilinForm K (Fin 3 → K)), B.Nondegenerate → B.IsSymm → (∀ g v w, B (S g *ᵥ v) (S g *ᵥ w) = B v w) → (∀ v : Fin 3 → K, (∀ g, S g *ᵥ v = v) → v = 0) → (∀ y : Fin 3 → K, y ≠ 0 → (∀ g, ∃ c : K, S g *ᵥ y = c • y) → B y y ≠ 0) → (1 : Matrix (Fin 3) (Fin 3) K) ∈ Submodule.span K (Set.range fun g => S g - 1) := by
  intro K _ _ _ Γ _ S B hB _ hinv hfix hiso
  obtain ⟨T, hT, hTv⟩ := GlobalTheory.AugCore.good_of_stable S B hB hinv hfix hiso _ ⊤
    (fun _ _ _ => trivial) rfl
  have e : T = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro v
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.one_mulVec]
    exact hTv v trivial
  exact (congrArg (· ∈ Submodule.span K (Set.range fun g => S g - 1)) e).mp hT
