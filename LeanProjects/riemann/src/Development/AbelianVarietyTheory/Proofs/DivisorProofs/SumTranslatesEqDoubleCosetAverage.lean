import Mathlib

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem orbit_sum {H X M : Type*} [Group H] [Fintype H] [MulAction H X] [AddCommGroup M]
    [Module ℂ M] (y : X) [Fintype (orbit H y)] (F : X → M) :
    (Fintype.card (orbit H y) : ℂ) • ∑ h : H, F (h • y) =
      (Fintype.card H : ℂ) • ∑ z : orbit H y, F z := by
  have h1 : ∀ z : orbit H y, ∑ h : H, F (h • (z : X)) = ∑ h : H, F (h • y) := by
    rintro ⟨z, g, rfl⟩
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun h => by simp [mul_smul])
  have h2 : ∀ h : H, ∑ z : orbit H y, F (h • (z : X)) = ∑ z : orbit H y, F z := by
    intro h
    exact Fintype.sum_equiv (MulAction.toPerm h) _ _ (fun z => rfl)
  rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, ← Finset.card_univ, ← Finset.card_univ,
    ← Finset.sum_const, ← Finset.sum_const]
  calc ∑ _z : orbit H y, ∑ h : H, F (h • y) = ∑ z : orbit H y, ∑ h : H, F (h • (z : X)) :=
        Finset.sum_congr rfl (fun z _ => (h1 z).symm)
    _ = ∑ h : H, ∑ z : orbit H y, F (h • (z : X)) := Finset.sum_comm
    _ = ∑ _h : H, ∑ z : orbit H y, F z := Finset.sum_congr rfl (fun h _ => h2 h)

theorem avg_of_invariant {H X M ι : Type*} [Group H] [Fintype H] [MulAction H X]
    [AddCommGroup M] [Module ℂ M] (s : Finset ι) (y : ι → X) [∀ i, Fintype (orbit H (y i))]
    (F : ι → X → M) (hinv : ∀ h : H, ∑ i ∈ s, F i (h • y i) = ∑ i ∈ s, F i (y i)) :
    ∑ i ∈ s, F i (y i) =
      ∑ i ∈ s, ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
  have hH : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hO : ∀ i, (Fintype.card (orbit H (y i)) : ℂ) ≠ 0 := fun i => by
    haveI : Nonempty (orbit H (y i)) := ⟨⟨y i, mem_orbit_self _⟩⟩
    exact_mod_cast Fintype.card_ne_zero
  have key : ∀ i, ∑ h : H, F i (h • y i) = (Fintype.card H : ℂ) •
      ((Fintype.card (orbit H (y i)) : ℂ)⁻¹ • ∑ z : orbit H (y i), F i z) := by
    intro i
    rw [smul_comm (Fintype.card H : ℂ), ← orbit_sum, smul_smul, inv_mul_cancel₀ (hO i), one_smul]
  apply smul_right_injective M hH
  simp only
  calc (Fintype.card H : ℂ) • ∑ i ∈ s, F i (y i) = ∑ _h : H, ∑ i ∈ s, F i (y i) := by
        rw [Finset.sum_const, Finset.card_univ, Nat.cast_smul_eq_nsmul]
    _ = ∑ h : H, ∑ i ∈ s, F i (h • y i) := Finset.sum_congr rfl (fun h _ => (hinv h).symm)
    _ = ∑ i ∈ s, ∑ h : H, F i (h • y i) := Finset.sum_comm
    _ = _ := by rw [Finset.smul_sum]; exact Finset.sum_congr rfl (fun i _ => key i)

end CosetAvg
end GlobalTheory

namespace GlobalTheory
namespace CosetAvg

open MulAction

theorem sum_translates_eq_avg : ∀ {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : G →* Module.End ℂ M) (K : Subgroup G) {ι : Type} (s : Finset ι) (a : ι → G) (R : ι → Finset G) (w : ι → M), (∀ i ∈ s, (∀ γ ∈ R i, ∃ k₁ ∈ K, ∃ k₂ ∈ K, γ = k₁ * a i * k₂) ∧ ∀ x : G, (∃ k₁ ∈ K, ∃ k₂ ∈ K, x = k₁ * a i * k₂) → ∃! γ, γ ∈ R i ∧ γ⁻¹ * x ∈ K) → (∀ i ∈ s, ∀ k ∈ K, ρ k (w i) = w i) → (∀ k ∈ K, ρ k (∑ i ∈ s, ρ (a i) (w i)) = ∑ i ∈ s, ρ (a i) (w i)) → ∑ i ∈ s, ρ (a i) (w i) = ∑ i ∈ s, ((R i).card : ℂ)⁻¹ • ∑ γ ∈ R i, ρ γ (w i) := by
  intro G M _ _ _ ρ K ι s a R w hR hw hm
  classical
  have hsm : ∀ (k : K) (g : G), k • ((g : G) : G ⧸ K) = ((k * g : G) : G ⧸ K) := fun k g => rfl
  let Y : SubMulAction K (G ⧸ K) :=
    { carrier := {q | ∃ i ∈ s, ∃ k : K, q = k • ((a i : G) : G ⧸ K)}
      smul_mem' := by
        rintro c q ⟨i, hi, k, rfl⟩
        exact ⟨i, hi, c * k, (mul_smul c k _).symm⟩ }
  have hYsub : (Y : Set (G ⧸ K)) ⊆
      ((s.biUnion fun i => (R i).image (QuotientGroup.mk : G → G ⧸ K) : Finset (G ⧸ K)) :
        Set (G ⧸ K)) := by
    rintro q ⟨i, hi, k, rfl⟩
    obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i hi).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
    refine Finset.mem_coe.mpr (Finset.mem_biUnion.mpr ⟨i, hi, Finset.mem_image.mpr ⟨γ, hγ, ?_⟩⟩)
    rw [hsm, QuotientGroup.eq]
    exact hγk
  haveI : Finite Y := (Set.Finite.subset (Finset.finite_toSet _) hYsub).to_subtype
  letI : Fintype Y := Fintype.ofFinite Y
  let φ := MulAction.toPermHom K Y
  let H := φ.range
  letI : Fintype H := Fintype.ofFinite H
  have hy : ∀ i ∈ s, ((a i : G) : G ⧸ K) ∈ Y := fun i hi => ⟨i, hi, 1, by simp⟩
  let y : s → Y := fun i => ⟨((a i : G) : G ⧸ K), hy i i.2⟩
  letI : ∀ i, Fintype (orbit H (y i)) := fun i => Fintype.ofFinite _
  let F : s → Y → M := fun i q => ρ (q : G ⧸ K).out (w i)
  have hF : ∀ (i : s) (q : Y) (g : G), (q : G ⧸ K) = (g : G ⧸ K) → F i q = ρ g (w i) := by
    intro i q g hq
    obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul K g
    simp only [F, hq, hk, map_mul, Module.End.mul_apply, hw i i.2 k k.2]
  have hval : ∀ (k : K) (i : s),
      ((((⟨φ k, k, rfl⟩ : H) • y i : Y)) : G ⧸ K) = ((k * a i : G) : G ⧸ K) := fun k i => rfl
  have hinv : ∀ h : H, ∑ i ∈ Finset.univ, F i (h • y i) = ∑ i ∈ Finset.univ, F i (y i) := by
    rintro ⟨_, k, rfl⟩
    rw [Finset.sum_congr rfl (fun i _ => hF i _ _ (hval k i)),
      Finset.sum_congr rfl (fun i _ => hF i (y i) (a i) rfl)]
    simp only [map_mul, Module.End.mul_apply]
    rw [← map_sum, Finset.sum_coe_sort s (fun i => ρ (a i) (w i)), hm k k.2]
  have hmain := avg_of_invariant (H := H) Finset.univ y F hinv

  have horb : ∀ i : s, ∃ e : (R i) ≃ orbit H (y i),
      ∀ γ : R i, ((e γ : Y) : G ⧸ K) = ((γ : G) : G ⧸ K) := by
    intro i
    have hmemY : ∀ γ ∈ R i, ((γ : G) : G ⧸ K) ∈ Y := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := (hR i i.2).1 γ hγ
      exact ⟨i, i.2, ⟨k₁, hk₁⟩, by rw [hsm, QuotientGroup.mk_mul_of_mem _ hk₂]⟩
    have hmemO : ∀ (γ : G) (hγ : γ ∈ R i), (⟨(γ : G ⧸ K), hmemY γ hγ⟩ : Y) ∈ orbit H (y i) := by
      intro γ hγ
      obtain ⟨k₁, hk₁, k₂, hk₂, hγe⟩ := (hR i i.2).1 γ hγ
      refine ⟨⟨φ ⟨k₁, hk₁⟩, ⟨k₁, hk₁⟩, rfl⟩, Subtype.ext ?_⟩
      exact (hval _ _).trans ((QuotientGroup.mk_mul_of_mem _ hk₂).symm.trans (congrArg _ hγe.symm))
    let f : R i → orbit H (y i) := fun γ => ⟨⟨(γ : G ⧸ K), hmemY γ γ.2⟩, hmemO γ γ.2⟩
    have hbij : Function.Bijective f := by
      constructor
      · rintro ⟨γ, hγ⟩ ⟨γ', hγ'⟩ he
        have he' : ((γ : G) : G ⧸ K) = ((γ' : G) : G ⧸ K) :=
          congrArg (fun z : orbit H (y i) => ((z : Y) : G ⧸ K)) he
        rw [QuotientGroup.eq] at he'
        have hu := (hR i i.2).2 γ' ((hR i i.2).1 γ' hγ')
        exact Subtype.ext (hu.unique ⟨hγ, he'⟩ ⟨hγ', by simp⟩)
      · rintro ⟨z, ⟨⟨_, k, rfl⟩, hz⟩⟩
        obtain ⟨γ, ⟨hγ, hγk⟩, -⟩ := (hR i i.2).2 (k * a i) ⟨k, k.2, 1, K.one_mem, by simp⟩
        refine ⟨⟨γ, hγ⟩, Subtype.ext (Subtype.ext ?_)⟩
        exact (QuotientGroup.eq.mpr hγk).trans ((hval k i).symm.trans (congrArg Subtype.val hz))
    exact ⟨Equiv.ofBijective f hbij, fun γ => rfl⟩
  rw [← Finset.sum_coe_sort s, ← Finset.sum_coe_sort s, Finset.sum_congr rfl
    (fun i _ => (hF i (y i) (a i) rfl).symm), hmain]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  obtain ⟨e, he⟩ := horb i
  rw [← Fintype.card_congr e, Fintype.card_coe]
  congr 1
  rw [← Finset.sum_coe_sort (R i)]
  exact (Fintype.sum_equiv e _ _ (fun γ => (hF i _ _ (he γ)).symm)).symm

end CosetAvg
end GlobalTheory
