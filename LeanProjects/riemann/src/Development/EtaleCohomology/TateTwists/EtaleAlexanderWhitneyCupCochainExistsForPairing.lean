import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleCupCompatibleWithCoefficientMapsOfSpec

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleAlexanderWhitneyCupCochainExistsForPairing : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m),
    ∃ γ : Cochain ((chains R).obj E) K k, μ.IsAW hk α β γ

def EtaleAlexanderWhitneyCupUniqueBiadditive : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k),
    (∀ (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ') ∧
    (∀ (α α' : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α' β γ' → μ.IsAW hk (α + α') β (γ + γ')) ∧
    (∀ (α : Cochain ((chains R).obj E) I n) (β β' : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β' γ' → μ.IsAW hk α (β + β') (γ + γ')) ∧
    (∀ (β : Cochain ((chains R).obj E) J m), μ.IsAW hk 0 β 0) ∧
    (∀ (α : Cochain ((chains R).obj E) I n), μ.IsAW hk α 0 0)

def EtaleAlexanderWhitneyCupLeibnizRule : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ → δ k k₁ γ = γ₁ + n.negOnePow • γ₂

theorem ev_add' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (α β : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x := by
  unfold ev
  rw [Cochain.add_v, Preadditive.comp_add]
  rfl

theorem ev_zero' {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 := by
  unfold ev
  rw [Cochain.zero_v, Limits.comp_zero]
  rfl

def EtaleAlexanderWhitneyCupCochainUnique : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ γ' : Cochain ((chains R).obj E) K k),
      μ.IsAW hk α β γ → μ.IsAW hk α β γ' → γ = γ'

theorem awalg_of (hu : EtaleAlexanderWhitneyCupCochainUnique) : EtaleAlexanderWhitneyCupUniqueBiadditive := by
  intro R _ I J K μ E n m k hk
  refine ⟨hu R μ hk, ?_, ?_, ?_, ?_⟩
  · intro α α' β γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add, LinearMap.add_apply, smul_add]
  · intro α β β' γ γ' h h' N w hw U x
    rw [ev_add', h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [ev_add', map_add, smul_add]
  · intro β N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, LinearMap.zero_apply, smul_zero]
  · intro α N w hw U x
    rw [ev_zero']
    symm
    refine Finset.sum_eq_zero fun p _ => ?_
    rw [ev_zero', map_zero, smul_zero]

theorem cup_spec_part1 (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
    (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    ∃ γ : Cocycle ((chains R).obj E) K k, μ.IsAW hk α.1 β.1 γ.1 := by
  obtain ⟨γ, hγ⟩ := h1 R μ hk α.1 β.1
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m = k + 1 by omega) (δ n (n + 1) α.1) β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show n + (m + 1) = k + 1 by omega) α.1 (δ m (m + 1) β.1)
  have hd := h3 R μ hk rfl rfl _ _ α.1 β.1 γ γ₁ γ₂ hγ hγ₁ hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₁
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e1, e2, smul_zero, add_zero] at hd
  exact ⟨Cocycle.mk γ (k + 1) rfl hd, hγ⟩

def EtaleAlexanderWhitneyCupDescendsToCohomology : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k),
    ∃ c : CohomologyClass ((chains R).obj E) I n →+ CohomologyClass ((chains R).obj E) J m →+
        CohomologyClass ((chains R).obj E) K k,
      ∀ (α : Cocycle _ I n) (β : Cocycle _ J m) (γ : Cocycle _ K k), μ.IsAW hk α.1 β.1 γ.1 →
        c (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ

section Desc
variable (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule)
  {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (E : Spc) {n m k : ℤ} (hk : n + m = k)

noncomputable def chZ (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    Cocycle ((chains R).obj E) K k :=
  Classical.choose (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_spec (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    μ.IsAW hk α.1 β.1 (chZ h1 h2 h3 μ E hk α β).1 :=
  Classical.choose_spec (cup_spec_part1 h1 h2 h3 R μ hk α β)

theorem chZ_eq (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) : chZ h1 h2 h3 μ E hk α β = γ :=
  Cocycle.ext ((h2 R μ hk).1 _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) h)

theorem chZ_add_left (α α' : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk (α + α') β = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α' β :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α' β))

theorem chZ_add_right (α : Cocycle ((chains R).obj E) I n) (β β' : Cocycle ((chains R).obj E) J m) :
    chZ h1 h2 h3 μ E hk α (β + β') = chZ h1 h2 h3 μ E hk α β + chZ h1 h2 h3 μ E hk α β' :=
  chZ_eq h1 h2 h3 μ E hk _ _ _ ((h2 R μ hk).2.2.1 _ _ _ _ _ (chZ_spec h1 h2 h3 μ E hk α β) (chZ_spec h1 h2 h3 μ E hk α β'))

theorem chZ_cob_left (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hα : α ∈ coboundaries _ _ n) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', η, hη⟩ := hα
  obtain ⟨γ, hγ⟩ := h1 R μ (show m' + m = m' + m from rfl) η β.1
  obtain ⟨γ₂, hγ₂⟩ := h1 R μ (show m' + (m + 1) = k by omega) η (δ m (m + 1) β.1)
  have hd := h3 R μ rfl hm' rfl (show n + m = k from hk) (show m' + (m + 1) = k by omega) η β.1 γ
    (chZ h1 h2 h3 μ E hk α β).1 γ₂ hγ (by rw [hη]; exact chZ_spec h1 h2 h3 μ E hk α β) hγ₂
  rw [Cocycle.δ_eq_zero] at hγ₂
  have e2 : γ₂ = 0 := (h2 R μ _).1 _ _ _ _ hγ₂ ((h2 R μ _).2.2.2.2 _)
  rw [e2, smul_zero, add_zero] at hd
  exact ⟨m' + m, by omega, γ, hd⟩

theorem chZ_cob_right (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (hβ : β ∈ coboundaries _ _ m) : chZ h1 h2 h3 μ E hk α β ∈ coboundaries _ _ k := by
  obtain ⟨m', hm', θ, hθ⟩ := hβ
  obtain ⟨γ, hγ⟩ := h1 R μ (show n + m' = n + m' from rfl) α.1 θ
  obtain ⟨γ₁, hγ₁⟩ := h1 R μ (show (n + 1) + m' = k by omega) (δ n (n + 1) α.1) θ
  have hd := h3 R μ rfl rfl hm' (show (n + 1) + m' = k by omega) (show n + m = k from hk) α.1 θ γ
    γ₁ (chZ h1 h2 h3 μ E hk α β).1 hγ hγ₁ (by rw [hθ]; exact chZ_spec h1 h2 h3 μ E hk α β)
  rw [Cocycle.δ_eq_zero] at hγ₁
  have e1 : γ₁ = 0 := (h2 R μ _).1 _ _ _ _ hγ₁ ((h2 R μ _).2.2.2.1 _)
  rw [e1, zero_add] at hd
  refine ⟨n + m', by omega, n.negOnePow • γ, ?_⟩
  rw [δ_units_smul, hd, smul_smul, Int.units_mul_self, one_smul]

end Desc

theorem desc_of (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (h2 : EtaleAlexanderWhitneyCupUniqueBiadditive) (h3 : EtaleAlexanderWhitneyCupLeibnizRule) :
    EtaleAlexanderWhitneyCupDescendsToCohomology := by
  intro R _ I J K μ E n m k hk
  let G : Cocycle ((chains R).obj E) I n → (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    fun α => QuotientAddGroup.lift _
      (AddMonoidHom.mk' (fun β => CohomologyClass.mk (chZ h1 h2 h3 μ E hk α β))
        (fun β β' => by rw [chZ_add_right, CohomologyClass.mk_add]))
      (fun β hβ => by
        simp only [AddMonoidHom.mem_ker, AddMonoidHom.mk'_apply]
        exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_right h1 h2 h3 μ E hk α β hβ))
  let F : Cocycle ((chains R).obj E) I n →+ (CohomologyClass ((chains R).obj E) J m →+ CohomologyClass ((chains R).obj E) K k) :=
    AddMonoidHom.mk' G (fun α α' => by
      refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
      show CohomologyClass.mk _ = CohomologyClass.mk _ + CohomologyClass.mk _
      rw [chZ_add_left, CohomologyClass.mk_add])
  refine ⟨QuotientAddGroup.lift _ F (fun α hα => ?_), ?_⟩
  · rw [AddMonoidHom.mem_ker]
    refine QuotientAddGroup.addMonoidHom_ext _ (AddMonoidHom.ext fun β => ?_)
    show CohomologyClass.mk _ = 0
    exact (QuotientAddGroup.eq_zero_iff _).2 (chZ_cob_left h1 h2 h3 μ E hk α β hα)
  · intro α β γ hγ
    show CohomologyClass.mk _ = _
    rw [chZ_eq h1 h2 h3 μ E hk α β γ hγ]

theorem etale_cup_compat_spec_of_alexander_whitney_exists_unique_leibniz (h1 : EtaleAlexanderWhitneyCupCochainExistsForPairing) (hu : EtaleAlexanderWhitneyCupCochainUnique)
    (h3 : EtaleAlexanderWhitneyCupLeibnizRule) : EtaleCupCompatAlexanderWhitneyCocycleSpec := by
  have h2 := awalg_of hu
  have h4 := desc_of h1 h2 h3
  intro R _ I J K μ E n m k hk
  refine ⟨fun α β => cup_spec_part1 h1 h2 h3 R μ hk α β, ?_⟩
  intro α β γ hγ
  exact pick_spec (h4 R μ E hk) α β γ hγ
end LateralTheory.EtaleFoundations
