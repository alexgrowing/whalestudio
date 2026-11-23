import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticHeightTensorAdditiveOnCurves
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.CoverNorm

namespace GlobalTheory.HtNefAbel

theorem sum_mul_le (N : ℕ) : ∀ (g n : Fin N → ℤ) (c : ℤ),
    (∀ i : ℕ, i ≤ N → ∑ a : Fin N, (if a.val < i then g a else 0) ≤ 0) → Antitone n → (∀ a, c ≤ n a) →
    ∑ a, n a * g a ≤ c * ∑ a, g a := by
  induction N with
  | zero => intro g n c _ _ _; simp
  | succ N ih =>
    intro g n c hS hn hc
    have h1 := ih (fun a => g a.castSucc) (fun a => n a.castSucc) (n (Fin.last N)) (fun i hi => by
        have := hS i (hi.trans (Nat.le_succ N))
        rw [Fin.sum_univ_castSucc, if_neg (by simpa using hi), add_zero] at this
        simpa using this)
      (fun a b hab => hn (by simpa using hab)) (fun a => hn (Fin.le_last _))
    have h2 : ∑ a, g a ≤ 0 := by
      have := hS (N + 1) le_rfl
      simpa only [Fin.is_lt, if_true] using this
    have h3 := mul_le_mul_of_nonpos_right (hc (Fin.last N)) h2
    rw [Fin.sum_univ_castSucc]
    refine le_trans ?_ h3
    rw [Fin.sum_univ_castSucc (f := g), mul_add]
    exact add_le_add h1 le_rfl

theorem sum_neg_mul_nonneg (T : Type) [Fintype T] (N : ℕ) (g : T × Fin N → ℤ)
    (h₁ : ∀ τ : T, ∀ i : ℕ, i < N → 0 ≤ ∑ x : T × Fin N, (if x.1 = τ ∧ x.2.val < i then -1 else 0 : ℤ) * g x)
    (h₂ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then 1 else 0 : ℤ) * g x)
    (h₃ : ∀ τ : T, 0 ≤ ∑ x : T × Fin N, (if x.1 = τ then -1 else 0 : ℤ) * g x)
    (n : T → Fin N → ℤ) (hn : ∀ τ, Antitone (n τ)) : 0 ≤ ∑ x : T × Fin N, -n x.1 x.2 * g x := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_nonneg fun τ _ => ?_
  have e₂ : 0 ≤ ∑ a, g (τ, a) := by
    have := h₂ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  have e₃ : ∑ a, g (τ, a) ≤ 0 := by
    have := h₃ τ
    rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
    simpa using this
  obtain ⟨c, hc⟩ := (Set.finite_range (n τ)).bddBelow
  have := sum_mul_le N (fun a => g (τ, a)) (n τ) c (fun i hi => by
      rcases hi.lt_or_eq with hi | rfl
      · have := h₁ τ i hi
        rw [Fintype.sum_prod_type, Finset.sum_eq_single τ (fun b _ hb => by simp [hb]) (by simp)] at this
        rw [← neg_nonneg, ← Finset.sum_neg_distrib]
        refine this.trans_eq (Finset.sum_congr rfl fun a _ => ?_)
        by_cases h : a.val < i <;> simp [h]
      · simpa only [Fin.is_lt, if_true] using e₃) (hn τ) (fun a => hc ⟨a, rfl⟩)
  rw [le_antisymm e₃ e₂, mul_zero] at this
  simp only [neg_mul, Finset.sum_neg_distrib, neg_nonneg]
  exact this

theorem nefOver_comb_of_antitone : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {d : ℕ}, IsArithVar p d → ∀ (T : Type) [Fintype T] (N : ℕ) (M : T × Fin N → HermLB p) (l : ℕ), (∀ τ : T, ∀ i : ℕ, i < N → NefOver (ArInt.comb M fun x => if x.1 = τ ∧ x.2.val < i then -1 else 0) l) → (∀ τ : T, NefOver (ArInt.comb M fun x => if x.1 = τ then 1 else 0) l ∧ NefOver (ArInt.comb M fun x => if x.1 = τ then -1 else 0) l) → ∀ n : T → Fin N → ℤ, (∀ τ, Antitone (n τ)) → NefOver (ArInt.comb M fun x => -n x.1 x.2) l := by
  intro k _ X p d hX T _ N M l h₁ h₂ n hn Z i _ _ κ _ _ _ _ hd
  have : Module.Finite ℤ k := hX.finite
  have : IsProper p := (isProper_and_exists_isAmpleLB_of_isProjOver hX.isProjOver).1
  have hproj : IsProjOver (strHom κ Z) := by
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) =
        i ≫ p ≫ spMap (Int.castRingHom k) := specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by
      rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    exact ProperCurve.isProjOver_of_isProper _ hd
  let F₀ : HermLB.IsomClass p → ℤ :=
    Quotient.lift (s := HermLB.isometrySetoid p) (fun L => topSelfIntersection κ (L.B.pull i) 1) fun L L' e => by
      have ⟨w, hw, _⟩ := HermLB.Isometric.pull e i rfl
      exact interNum_congr_lbIso κ _ (fun _ => (L.restr i).isLB) (fun _ => (L'.restr i).isLB) fun _ => ⟨w, hw⟩
  let F : HermLB.IsomClass p →+ ℤ := AddMonoidHom.mk' F₀ (by
    rintro ⟨L⟩ ⟨L'⟩
    exact HtTensCurve.topSelf_one_pull_tens hproj hd i L.isLB L'.isLB)
  have key (e : T × Fin N → ℤ) : topSelfIntersection κ ((ArInt.comb M e).B.pull i) 1 = ∑ x, e x * F (M x).icls := by
    change F (ArInt.comb M e).icls = _
    rw [icls_comb, map_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [map_zsmul, smul_eq_mul]
  rw [key]
  exact sum_neg_mul_nonneg T N _ (fun τ j hj => key _ ▸ h₁ τ j hj Z i κ hd) (fun τ => key _ ▸ (h₂ τ).1 Z i κ hd)
    (fun τ => key _ ▸ (h₂ τ).2 Z i κ hd) n hn

end GlobalTheory.HtNefAbel
