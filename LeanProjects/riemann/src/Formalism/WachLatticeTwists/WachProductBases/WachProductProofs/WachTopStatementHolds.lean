import Formalism.WachLatticeTwists.WachProductBases.StatementTop
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.LemmaThreeTameExponent
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.AffineLineLocalAcyclicityOfStrictHenselianPoints
import Formalism.WachLatticeTwists.WachProductBases.WachProductProofs.ToWachModuleHolds

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.N1

open Formalism.CoboundaryTransfers Finset

variable {O A : Type} [CommRing O] [CommRing A] [Algebra O A]

def NHom.killIdeal {S : HidaSetting O A} {ι : Type} {pr : Equiv.Perm ι} {D₁ D₂ : Type}
    [AddCommGroup D₁] [Module A D₁] [Module O D₁] [IsScalarTower O A D₁]
    [AddCommGroup D₂] [Module A D₂] [Module O D₂] [IsScalarTower O A D₂]
    {W₁ : NData S ι pr D₁} {W₂ : NData S ι pr D₂} (F : NHom W₁ W₂) (i : ι) : Ideal A where
  carrier := {a | F.Kills i a}
  add_mem' := by
    intro a b ha hb n hn
    obtain ⟨x, hx, hfx⟩ := ha n hn
    obtain ⟨y, hy, hfy⟩ := hb n hn
    exact ⟨x + y, (W₁.N i).add_mem hx hy, by rw [map_add, hfx, hfy, add_smul]⟩
  zero_mem' := fun n _ => ⟨0, (W₁.N i).zero_mem, by simp⟩
  smul_mem' := by
    intro r a ha n hn
    obtain ⟨x, hx, hfx⟩ := ha n hn
    exact ⟨r • x, (W₁.N i).smul_mem r hx, by rw [map_smul, hfx, smul_smul, smul_eq_mul]⟩

theorem wach_top_statement_holds : WachProductBasisTheorem := by
  intro O A _ _ _ S ι _ pr D₀ D₁ D₂ _ _ _ _ _ _ _ _ _ _ _ _ W₀ W₁ W₂ E M h M₀ h₀ H hrad hdec
    hP20 hP21 hP22 hP50 hP51 hP52 hL0 hL1 hL2 hP6 hM hh hH
  classical
  cases nonempty_fintype ι
  obtain ⟨⟨a, hka⟩, hker⟩ := hP6
  have hpi : ∀ i, ∃ c : ℕ, E.π.Kills i (S.π ^ c) := fun i =>
    cokernel_killed_holds A D₁ D₂ (E.π.f i) (W₁.N i) (W₂.N i) S.π (S.ℓ : A) a (E.surj i) (E.π.N_le i) (hka i)
      (hL1.2.1 i a) (hL2.2.2.2 i) (hL2.1 i)
  choose c hc using hpi
  have hcu : ∀ i, E.π.Kills i (S.π ^ (univ.sup c)) := by
    intro i n hn
    obtain ⟨n₁, h1, h2⟩ := hc i n hn
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (Finset.le_sup (f := c) (mem_univ i))
    exact ⟨S.π ^ k • n₁, (W₁.N i).smul_mem _ h1, by
      rw [map_smul, h2, hk, pow_add, mul_comm, mul_smul]⟩
  have hL3 := lemma_three_a_holds O A S ι pr D₁ D₂ W₁ W₂ E.π M h H _ hdec hP51 hP52 hH hcu
  have hsat : ∀ i x, E.ι.f i x ∈ W₁.N i → x ∈ W₀.N i := fun i =>
    kernel_intersection_holds A D₀ D₁ (E.ι.f i) (W₀.N i) (W₁.N i) (S.ℓ : A) (hker i) (hL0.2.2.1 i)
  have htame : ∀ (π' w : A) (e s' : ℕ), S.s = 1 → e * s' = S.ℓ - 1 → π' = w * S.π ^ s' →
      ∀ i, E.π.Kills i (π' ^ ⌈((e * H : ℕ) : ℚ) / ((S.ℓ - 1 : ℕ) : ℚ)⌉₊) := by
    intro π' w e s' hs hes hπ' i
    have hX : S.X = S.π := by simp [HidaSetting.X, hs]
    exact lemma_three_tame_exponent A (E.π.killIdeal i) S.π π' w S.ℓ e s' H S.hℓ.two_le hes hπ'
      (by rw [← hX]; exact hL3 i)
  have htameΔ : ∀ (π' w : A) (e s' : ℕ) (Δ : Type) [Group Δ] [Fintype Δ]
      (ρ₁ : ι → Δ →* Module.End O D₁) (ρ₂ : ι → Δ →* Module.End O D₂),
      S.s = 1 → e * s' = S.ℓ - 1 → π' = w * S.π ^ s' → IsUnit ((Fintype.card Δ : ℕ) : O) →
      (∀ i d, ∀ x ∈ W₁.N i, ρ₁ i d x ∈ W₁.N i) →
      (∀ i d x, E.π.f i (ρ₁ i d x) = ρ₂ i d (E.π.f i x)) →
      (∀ i d x, ρ₂ i d (π' • x) = π' • ρ₂ i d x) →
      ∀ i, ∀ n ∈ W₂.N i, (∀ d, ρ₂ i d n = n) → ∃ n₁ ∈ W₁.N i, (∀ d, ρ₁ i d n₁ = n₁) ∧
        E.π.f i n₁ = π' ^ ⌈((e * H : ℕ) : ℚ) / ((S.ℓ - 1 : ℕ) : ℚ)⌉₊ • n := by
    intro π' w e s' Δ _ _ ρ₁ ρ₂ hs hes hπ' hunit hN hf hcomm i n hn hinv
    have hpow : ∀ (m : ℕ) (d : Δ) (x : D₂), ρ₂ i d (π' ^ m • x) = π' ^ m • ρ₂ i d x := by
      intro m
      induction m with
      | zero => intro d x; simp
      | succ m ih => intro d x; rw [pow_succ', mul_smul, hcomm, ih, mul_smul]
    exact lemma_three_invariants O A Δ D₁ D₂ (ρ₁ i) (ρ₂ i) (E.π.f i) (W₁.N i) (W₂.N i) _ hunit (hN i) (hf i)
      (hpow _) (htame π' w e s' hs hes hπ' i) n hn hinv
  obtain ⟨V₀, hN0, hφ0, hγ0, hH0⟩ := to_wach_module_holds O A S ι pr D₀ W₀ M h M₀ h₀ hrad hP20 hP50 hM hh
  obtain ⟨V₁, hN1, hφ1, hγ1, hH1⟩ := to_wach_module_holds O A S ι pr D₁ W₁ M h M₀ h₀ hrad hP21 hP51 hM hh
  obtain ⟨V₂, hN2, hφ2, hγ2, hH2⟩ := to_wach_module_holds O A S ι pr D₂ W₂ M h M₀ h₀ hrad hP22 hP52 hM hh
  have hm0 : ∀ x : ι → D₀, x ∈ V₀.N ↔ ∀ i, x i ∈ W₀.N i := by
    intro x; rw [hN0]; simp [Submodule.mem_pi]
  have hm1 : ∀ x : ι → D₁, x ∈ V₁.N ↔ ∀ i, x i ∈ W₁.N i := by
    intro x; rw [hN1]; simp [Submodule.mem_pi]
  have hm2 : ∀ x : ι → D₂, x ∈ V₂.N ↔ ∀ i, x i ∈ W₂.N i := by
    intro x; rw [hN2]; simp [Submodule.mem_pi]
  let fι : (ι → D₀) →ₗ[A] (ι → D₁) := LinearMap.pi (fun i => (E.ι.f i).comp (LinearMap.proj i))
  let fπ : (ι → D₁) →ₗ[A] (ι → D₂) := LinearMap.pi (fun i => (E.π.f i).comp (LinearMap.proj i))
  have hfι : ∀ x i, fι x i = E.ι.f i (x i) := fun _ _ => rfl
  have hfπ : ∀ x i, fπ x i = E.π.f i (x i) := fun _ _ => rfl
  let Hι : Hom V₀ V₁ :=
    { f := fι
      φ_comm := by
        intro x; funext i
        rw [hφ1, hfι, hφ0, E.ι.φ_comm, hfι]
      γ_comm := by
        intro x; funext i
        rw [hγ1, hfι, hγ0, E.ι.γ_comm, hfι]
      N_le := by
        intro x hx
        rw [hm1]; intro i
        exact E.ι.N_le i _ ((hm0 x).1 hx i) }
  let Hπ : Hom V₁ V₂ :=
    { f := fπ
      φ_comm := by
        intro x; funext i
        rw [hφ2, hfπ, hφ1, E.π.φ_comm, hfπ]
      γ_comm := by
        intro x; funext i
        rw [hγ2, hfπ, hγ1, E.π.γ_comm, hfπ]
      N_le := by
        intro x hx
        rw [hm2]; intro i
        exact E.π.N_le i _ ((hm1 x).1 hx i) }
  let Sq : SES V₀ V₁ V₂ :=
    { ι := Hι
      π := Hπ
      ι_inj := by
        intro x y hxy
        funext i
        exact E.ι_inj i (congrFun hxy i)
      exact := by
        intro x
        constructor
        · intro hx
          choose x₀ hx₀ using fun i => (E.exact i (x i)).1 (congrFun hx i)
          exact ⟨x₀, funext hx₀⟩
        · rintro ⟨x₀, rfl⟩
          funext i
          exact (E.exact i _).2 ⟨x₀ i, rfl⟩
      sat := by
        intro x₀ hx
        rw [hm0]; intro i
        exact hsat i _ ((hm1 _).1 hx i) }
  refine ⟨hL3, htame, htameΔ, hsat, V₀, V₁, V₂, Sq, hN0, hN1, hN2, hφ0, hγ0, hφ1, hγ1, hφ2, hγ2,
    fun _ _ => rfl, fun _ _ => rfl, ?_, ?_, ⟨a, ?_⟩, hH0, hH1, hH2⟩
  · intro y
    choose x hx using fun i => E.surj i (y i)
    exact ⟨x, funext hx⟩
  · intro n hn
    choose n₁ h1 h2 using fun i => hL3 i (n i) ((hm2 n).1 hn i)
    exact ⟨n₁, (hm1 n₁).2 h1, funext h2⟩
  · intro n hn
    choose n₁ h1 h2 using fun i => hka i (n i) ((hm2 n).1 hn i)
    refine ⟨n₁, (hm1 n₁).2 h1, funext fun i => ?_⟩
    show E.π.f i (n₁ i) = ((S.ℓ : O) ^ a) • n i
    rw [h2, ← algebraMap_smul A ((S.ℓ : O) ^ a) (n i)]
    simp

end Formalism.RepresentationBoundsCohomology.N1
