import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private noncomputable def gbEquiv (k : Type) [Field k] (j : ℤ) :
    Gb k j ≃ₗ[k] ({p : Fin 3 × Fin 3 // wt p.1 p.2 = j} → k) where
  toFun X p := X.val p.1.1 p.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := (⟨Matrix.of fun a b => if h : wt a b = j then f ⟨(a, b), h⟩ else 0,
    fun a b h => by simp [h]⟩ : gw k j)
  left_inv X := by
    apply Subtype.ext
    ext a b
    show (if h : wt a b = j then X.val a b else 0) = X.val a b
    split_ifs with h
    · rfl
    · exact (X.2 a b h).symm
  right_inv f := by
    ext ⟨⟨a, b⟩, h⟩
    show (if h : wt a b = j then f ⟨(a, b), h⟩ else 0) = _
    rw [dif_pos h]

private theorem card_wt (j : ℤ) : Fintype.card {p : Fin 3 × Fin 3 // wt p.1 p.2 = j} = (3 - |j|).toNat := by
  rcases (show j ≤ -3 ∨ j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega)
    with h | rfl | rfl | rfl | rfl | rfl | h
  · rw [show (3 - |j|).toNat = 0 by rw [abs_of_neg (by omega)]; omega]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨⟨a, b⟩, hp⟩ => ?_⟩
    simp only [wt, wt1] at hp
    have := a.isLt
    have := b.isLt
    omega
  · decide
  · decide
  · decide
  · decide
  · decide
  · rw [show (3 - |j|).toNat = 0 by rw [abs_of_pos (by omega)]; omega]
    rw [Fintype.card_eq_zero_iff]
    refine ⟨fun ⟨⟨a, b⟩, hp⟩ => ?_⟩
    simp only [wt, wt1] at hp
    have := a.isLt
    have := b.isLt
    omega

private theorem mem_ker_iff {k D : Type} [Field k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (c : D)
    (hη : η c = -1) (hΨ : Ψ c = 1) (j : ℤ) (X : Gb k j) :
    X ∈ LinearMap.ker (gRep η Ψ j c - LinearMap.id) ↔ ∀ a b, X.val a b = -X.val b.rev a.rev := by
  have hne : η c ≠ 1 := by rw [hη]; decide
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  constructor
  · intro h a b
    have h1 := congrArg (fun Y : Gb k j => Y.val a b) h
    simp only [gRep_val, adRep_baseLift_apply, hΨ, _root_.one_zpow, Units.val_one, one_mul, if_neg hne] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    ext a b
    show ((gRep η Ψ j c) X).val a b = X.val a b
    rw [gRep_val, adRep_baseLift_apply, hΨ, _root_.one_zpow, Units.val_one, one_mul, if_neg hne]
    exact (h a b).symm

private theorem ker_one {k : Type} [Field k] (j : ℤ) (K : Submodule k (Gb k j))
    (hK : ∀ X, X ∈ K ↔ ∀ a b, X.val a b = -X.val b.rev a.rev) (M : Matrix (Fin 3) (Fin 3) k)
    (hM : M ∈ gw k j) (hM' : ∀ a b, M a b = -M b.rev a.rev) (a₀ b₀ : Fin 3) (h1 : M a₀ b₀ = 1)
    (hall : ∀ X : Matrix (Fin 3) (Fin 3) k, X ∈ gw k j → (∀ a b, X a b = -X b.rev a.rev) →
      ∀ a b, X a₀ b₀ * M a b = X a b) : finrank k K = 1 := by
  rw [finrank_eq_one_iff']
  refine ⟨⟨(⟨M, hM⟩ : gw k j), (hK _).2 hM'⟩, ?_, ?_⟩
  · intro h
    have : M a₀ b₀ = 0 := congrArg (fun Y : K => Y.1.val a₀ b₀) h
    rw [h1] at this
    exact one_ne_zero this
  · intro w
    refine ⟨w.1.val a₀ b₀, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    ext a b
    exact hall w.1.val w.1.2 ((hK _).1 w.2) a b

private theorem half {k : Type} [Field k] (h2 : (2 : k) ≠ 0) {x : k} (h : x = -x) : x = 0 := by
  have h' : (2 : k) * x = 0 := by rw [two_mul]; nth_rewrite 1 [h]; ring
  rcases mul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' h2
  · exact h''

theorem UpperTheory.finrank_gradedPiece_and_complexConjugation_invariants :
    ∀ {k D : Type} [Field k] [Group D] (η : D →* ℤˣ) (Ψ : D →* kˣ) (c : D), (2 : k) ≠ 0 → η c = -1 → Ψ c = 1 → ∀ j : ℤ,
        Module.Finite k (Gb k j) ∧ finrank k (Gb k j) = (3 - |j|).toNat ∧
          finrank k (LinearMap.ker (gRep η Ψ j c - LinearMap.id)) = if |j| ≤ 1 then 1 else 0 := by
  intro k D _ _ η Ψ c h2 hη hΨ j
  classical
  have e := gbEquiv k j
  haveI : Module.Finite k (Gb k j) := Module.Finite.equiv e.symm
  have hdim : finrank k (Gb k j) = (3 - |j|).toNat := by
    rw [e.finrank_eq, Module.finrank_fintype_fun_eq_card, card_wt]
  refine ⟨inferInstance, hdim, ?_⟩
  have hK := mem_ker_iff η Ψ c hη hΨ j
  have zero_case : (∀ X : Gb k j, (∀ a b, X.val a b = -X.val b.rev a.rev) → X = 0) →
      finrank k (LinearMap.ker (gRep η Ψ j c - LinearMap.id)) = 0 := by
    intro hz
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro X hX
    exact hz X ((hK X).1 hX)
  rcases (show j ≤ -3 ∨ j = -2 ∨ j = -1 ∨ j = 0 ∨ j = 1 ∨ j = 2 ∨ 3 ≤ j by omega)
    with h | rfl | rfl | rfl | rfl | rfl | h
  · rw [if_neg (by rw [abs_le]; omega)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ j → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    apply hZ
    simp only [wt, wt1]
    have := a.isLt
    have := b.isLt
    omega
  · rw [if_neg (by norm_num)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ -2 → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    fin_cases a <;> fin_cases b <;> first
      | exact hZ _ _ (by decide)
      | exact half h2 (hA _ _)
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![0, 0, 0; 1, 0, 0; 0, -1, 0]) ?_ ?_ 1 0 (by simp) ?_
    · show ∀ a b, wt a b ≠ -1 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ -1 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![1, 0, 0; 0, 0, 0; 0, 0, -1]) ?_ ?_ 0 0 (by simp) ?_
    · show ∀ a b, wt a b ≠ 0 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ 0 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_pos (by norm_num)]
    refine ker_one _ _ hK (!![0, 1, 0; 0, 0, -1; 0, 0, 0]) ?_ ?_ 0 1 (by simp) ?_
    · show ∀ a b, wt a b ≠ 1 → _ = 0
      intro a b hab
      fin_cases a <;> fin_cases b <;> first
        | exact absurd (by decide) hab
        | simp
    · intro a b
      fin_cases a <;> fin_cases b <;> simp [Fin.rev]
    · intro X hX hXa a b
      have hZ : ∀ a b, wt a b ≠ 1 → X a b = 0 := hX
      fin_cases a <;> fin_cases b <;> simp <;> first
        | exact (hZ _ _ (by decide)).symm
        | exact (half h2 (hXa 1 1)).symm
        | exact (hXa 2 1).symm
        | exact (hXa 2 2).symm
        | exact (hXa 1 2).symm
  · rw [if_neg (by norm_num)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ 2 → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    fin_cases a <;> fin_cases b <;> first
      | exact hZ _ _ (by decide)
      | exact half h2 (hA _ _)
  · rw [if_neg (by rw [abs_le]; omega)]
    apply zero_case
    intro X hA
    have hZ : ∀ a b, wt a b ≠ j → X.val a b = 0 := X.2
    apply Subtype.ext
    ext a b
    show X.val a b = 0
    apply hZ
    simp only [wt, wt1]
    have := a.isLt
    have := b.isLt
    omega
