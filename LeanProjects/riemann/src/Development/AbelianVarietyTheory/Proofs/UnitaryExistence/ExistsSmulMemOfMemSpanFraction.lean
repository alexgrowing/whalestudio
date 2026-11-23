import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Imports
open NumberField Matrix
open scoped nonZeroDivisors
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

section PseudoBasis

variable {R K : Type} [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

theorem exists_smul_mem_of_mem_span_fraction {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (v : V) (hv : v ∈ Submodule.span K (Λ : Set V)) :
    ∃ d : R, d ≠ 0 ∧ d • v ∈ Λ := by
  first
  | (rename_i h_2 h_3 h_4 h_5 h_6 h_8 h_9 h_10 h_11; revert R K h_2 h_3 h_4 h_5 h_6 V h_8 h_9 h_10 h_11 Λ v hv; exact @_root_.GlobalTheory.LatticeBoundedAction.main)
  | exact @_root_.GlobalTheory.LatticeBoundedAction.main
  | exact _root_.GlobalTheory.LatticeBoundedAction.main
  | (apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.LatticeBoundedAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.LatticeBoundedAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.LatticeBoundedAction.main ..)

theorem exists_splitting_vector {V : Type} [AddCommGroup V] [Module K V] [Module R V]
    [IsScalarTower R K V] (Λ : Submodule R V) (hfg : Λ.FG)
    (hsp : Submodule.span K (Λ : Set V) = ⊤) (l : V →ₗ[K] K) (hl : l ≠ 0) :
    ∃ (c : FractionalIdeal R⁰ K) (e : V), c ≠ 0 ∧ l e = 1 ∧ (∀ v ∈ Λ, l v ∈ c) ∧
      ∀ x ∈ c, x • e ∈ Λ := by
  have hfg' : (Λ.map (l.restrictScalars R)).FG := hfg.map _
  let c : FractionalIdeal R⁰ K := ⟨Λ.map (l.restrictScalars R), FractionalIdeal.isFractional_of_fg hfg'⟩
  have hc : ∀ x, x ∈ c ↔ ∃ v ∈ Λ, l v = x := fun x => Iff.rfl
  have hc0 : c ≠ 0 := by
    intro h
    apply hl
    refine LinearMap.ext_on hsp ?_
    intro v hv
    have : l v ∈ c := (hc _).2 ⟨v, hv, rfl⟩
    rw [h] at this
    simpa using this
  have h1 : (1 : K) ∈ c * c⁻¹ := by
    rw [mul_inv_cancel₀ hc0]
    exact FractionalIdeal.one_mem_one _
  have key : ∀ y ∈ c * c⁻¹, ∃ e : V, l e = y ∧ ∀ x ∈ c, x • e ∈ Λ := by
    intro y hy
    refine FractionalIdeal.mul_induction_on hy ?_ ?_
    · intro a ha b hb
      obtain ⟨v, hv, rfl⟩ := (hc _).1 ha
      refine ⟨b • v, by simp [mul_comm], ?_⟩
      intro x hx
      have : x * b ∈ c * c⁻¹ := FractionalIdeal.mul_mem_mul hx hb
      rw [mul_inv_cancel₀ hc0, FractionalIdeal.mem_one_iff] at this
      obtain ⟨t, ht⟩ := this
      rw [smul_smul, ← ht, algebraMap_smul]
      exact Λ.smul_mem _ hv
    · rintro a b ⟨e, he, he'⟩ ⟨f, hf, hf'⟩
      refine ⟨e + f, by simp [he, hf], ?_⟩
      intro x hx
      rw [smul_add]
      exact Λ.add_mem (he' x hx) (hf' x hx)
  obtain ⟨e, he, he'⟩ := key 1 h1
  exact ⟨c, e, hc0, he, fun v hv => (hc _).2 ⟨v, hv, rfl⟩, he'⟩

theorem exists_pseudoCoords (n : ℕ) :
    ∀ (V : Type) [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]
      [FiniteDimensional K V], Module.finrank K V = n →
      ∀ (Λ : Submodule R V) (I : Submodule K V), Λ.FG → Submodule.span K (Λ : Set V) = ⊤ →
      ∃ (s : ℕ) (f : Fin n → (V →ₗ[K] K)) (c : Fin n → FractionalIdeal R⁰ K),
        (∀ v, (∀ a, f a v = 0) → v = 0) ∧ (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, f a v ∈ c a) ∧
        ∀ v, v ∈ I ↔ ∀ a : Fin n, s ≤ (a : ℕ) → f a v = 0 := by
  induction n with
  | zero =>
    intro V _ _ _ _ _ hV Λ I _ _
    have : Subsingleton V := Module.finrank_zero_iff.1 hV
    refine ⟨0, Fin.elim0, Fin.elim0, fun v _ => Subsingleton.elim _ _, fun a => a.elim0, ?_, ?_⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => Λ.zero_mem⟩
    · intro v
      rw [Subsingleton.elim v 0]
      exact ⟨fun _ a => a.elim0, fun _ => I.zero_mem⟩
  | succ n ih =>
    intro V _ _ _ _ _ hV Λ I hfg hsp
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV
    obtain ⟨l, hl, hI⟩ : ∃ l : V →ₗ[K] K, l ≠ 0 ∧ (I = ⊤ ∨ I ≤ LinearMap.ker l) := by
      by_cases h : I = ⊤
      · obtain ⟨l, hl, -⟩ := Submodule.exists_le_ker_of_lt_top (⊥ : Submodule K V) bot_lt_top
        exact ⟨l, hl, Or.inl h⟩
      · obtain ⟨l, hl, h2⟩ := Submodule.exists_le_ker_of_lt_top I (lt_top_iff_ne_top.2 h)
        exact ⟨l, hl, Or.inr h2⟩
    obtain ⟨c0, e, hc0, he, hΛc, hce⟩ := exists_splitting_vector Λ hfg hsp l hl
    set W := LinearMap.ker l with hW
    have hWn : Module.finrank K W = n := by
      have h1 := LinearMap.finrank_range_add_finrank_ker l
      have h2 : LinearMap.range l = ⊤ := by
        rw [eq_top_iff]
        intro x _
        exact ⟨x • e, by simp [he]⟩
      rw [h2, finrank_top, Module.finrank_self, hV] at h1
      rw [hW]; omega
    let ι : W →ₗ[R] V := W.subtype.restrictScalars R
    have hι : Function.Injective ι := Subtype.val_injective
    let Λ' : Submodule R W := Λ.comap ι
    have hΛ' : ∀ w : W, w ∈ Λ' ↔ (w : V) ∈ Λ := fun w => Iff.rfl
    have hfg' : Λ'.FG := by
      apply Submodule.fg_of_fg_map_injective ι hι
      exact Submodule.FG.of_le hfg (Submodule.map_comap_le _ _)
    have hsp' : Submodule.span K (Λ' : Set W) = ⊤ := by
      rw [eq_top_iff]
      intro w _
      obtain ⟨d, hd, hdw⟩ := exists_smul_mem_of_mem_span_fraction (K := K) Λ (w : V)
        (by rw [hsp]; trivial)
      have hd1 : algebraMap R K d ≠ 0 := by simpa using hd
      have hm : algebraMap R K d • w ∈ Λ' := by
        rw [hΛ']
        simpa using hdw
      have : w = (algebraMap R K d)⁻¹ • (algebraMap R K d • w) := by
        rw [smul_smul, inv_mul_cancel₀ hd1, one_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.subset_span hm)
    obtain ⟨s, f, c, hf, hc, hfΛ, hfI⟩ := ih W hWn Λ' (I.comap W.subtype) hfg' hsp'
    let p : V →ₗ[K] W := LinearMap.codRestrict W (LinearMap.id - l.smulRight e) (by
      intro v
      simp [hW, he])
    have hp : ∀ v, (p v : V) = v - l v • e := fun v => rfl
    let F : Fin (n + 1) → (V →ₗ[K] K) := Fin.snoc (fun a => f a ∘ₗ p) l
    let C : Fin (n + 1) → FractionalIdeal R⁰ K := Fin.snoc c c0
    have hF1 : ∀ a v, F (Fin.castSucc a) v = f a (p v) := by
      intro a v; simp [F]
    have hF2 : ∀ v, F (Fin.last n) v = l v := by
      intro v; simp [F]
    have hC1 : ∀ a, C (Fin.castSucc a) = c a := by
      intro a; simp [C]
    have hC2 : C (Fin.last n) = c0 := by
      simp [C]
    have A1 : ∀ v, (∀ a, F a v = 0) → v = 0 := by
      intro v hv
      have h1 : l v = 0 := by rw [← hF2]; exact hv _
      have h2 : p v = 0 := hf _ fun a => by rw [← hF1]; exact hv _
      have h3 := hp v
      rw [h2, h1] at h3
      simpa using h3.symm
    have A2 : ∀ a, C a ≠ 0 := by
      intro a
      refine Fin.lastCases ?_ (fun a => ?_) a
      · rwa [hC2]
      · rw [hC1]; exact hc a
    have A3 : ∀ v, v ∈ Λ ↔ ∀ a, F a v ∈ C a := by
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2, hC1, hC2]
      rw [← hfΛ, hΛ', hp]
      constructor
      · intro hv
        exact ⟨Λ.sub_mem hv (hce _ (hΛc v hv)), hΛc v hv⟩
      · rintro ⟨h1, h2⟩
        have := Λ.add_mem h1 (hce _ h2)
        simpa using this
    rcases hI with hI | hI
    · refine ⟨n + 1, F, C, A1, A2, A3, ?_⟩
      intro v
      refine ⟨fun _ a ha => absurd a.2 (not_lt.2 ha), fun _ => ?_⟩
      rw [hI]; trivial
    · refine ⟨min s n, F, C, A1, A2, A3, ?_⟩
      intro v
      rw [Fin.forall_fin_succ']
      simp only [hF1, hF2]
      have hh : (∀ a : Fin n, min s n ≤ ((Fin.castSucc a : Fin (n + 1)) : ℕ) → f a (p v) = 0) ↔
          (p v : V) ∈ I := by
        rw [show ((p v : V) ∈ I) ↔ p v ∈ I.comap W.subtype from Iff.rfl, hfI]
        refine forall_congr' fun a => imp_congr_left ?_
        have := a.2
        simp only [Fin.val_castSucc]
        omega
      rw [hh, hp]
      constructor
      · intro hv
        have h0 : l v = 0 := hI hv
        refine ⟨by simpa [h0] using hv, fun _ => h0⟩
      · rintro ⟨h1, h2⟩
        have h0 : l v = 0 := h2 (by simp)
        simpa [h0] using h1

end PseudoBasis

theorem exists_pseudoBasis_adapted :
    ∀ (E : Type) [Field E] [NumberField E] (r : ℕ) (Λ : Submodule (𝓞 E) (Fin r → E)) (I : Submodule E (Fin r → E)), Λ.FG → Submodule.span E (Λ : Set (Fin r → E)) = ⊤ → ∃ (s : ℕ) (e : Module.Basis (Fin r) E (Fin r → E)) (c : Fin r → FractionalIdeal (𝓞 E)⁰ E), (∀ a, c a ≠ 0) ∧ (∀ v, v ∈ Λ ↔ ∀ a, e.repr v a ∈ c a) ∧ ∀ v, v ∈ I ↔ ∀ a : Fin r, s ≤ (a : ℕ) → e.repr v a = 0 := by
  intro E _ _ r Λ I hfg hsp
  obtain ⟨s, f, c, hf, hc, hΛ, hI⟩ :=
    exists_pseudoCoords (R := 𝓞 E) (K := E) r (Fin r → E) (by simp) Λ I hfg hsp
  have hinj : Function.Injective (LinearMap.pi f) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hf v fun a => congrFun hv a
  let φ : (Fin r → E) ≃ₗ[E] (Fin r → E) := LinearEquiv.ofInjectiveEndo _ hinj
  have hφ : ∀ v a, (Module.Basis.ofEquivFun φ).repr v a = f a v := by
    intro v a
    rw [Module.Basis.ofEquivFun_repr_apply]
    rfl
  refine ⟨s, Module.Basis.ofEquivFun φ, c, hc, ?_, ?_⟩
  · simpa only [hφ] using hΛ
  · simpa only [hφ] using hI

end GlobalTheory
