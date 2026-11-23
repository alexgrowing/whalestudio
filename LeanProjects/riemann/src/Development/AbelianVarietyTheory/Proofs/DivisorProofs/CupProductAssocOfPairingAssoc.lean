import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupEqClassOfIsAWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCochainEvalOnSimplexBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceSimplicesOverSubCompositeStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem sum_range_triangle {A : Type*} [AddCommMonoid A] (G : ℕ → ℕ → A) (N : ℕ) :
    ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r := by
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_bij' (fun x _ => ⟨x.2, x.1 - x.2⟩) (fun y _ => ⟨y.1 + y.2, y.1⟩) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    simp at h ⊢ <;> omega
  · rintro ⟨a, b⟩ h
    rfl

theorem Sx.sub_congr {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {j j' l : ℕ} (hj : j = j') (h : j + l ≤ N)
    (h' : j' + l ≤ N) : x.sub j l h = x.sub j' l h' := by
  subst hj
  rfl

theorem Pair.mul_ev_congr {R : Type} [CommRing R] {J K M : Cx R} (μ : Pair J K M) {E : Spc} {k : ℤ}
    (γ : Cochain ((chains R).obj E) K k) {U : Scheme.{0}} {N : ℕ} (x : Sx E N U) (t tu : ℤ) (b : Sec (J.X t) U)
    {a a' j j' : ℕ} (ha : a = a') (hj : j = j') (hx : j + a ≤ N) (hx' : j' + a' ≤ N)
    (h : t + (-(a : ℤ) + k) = tu) (h' : t + (-(a' : ℤ) + k) = tu) :
    μ.mul U t (-(a : ℤ) + k) tu h b (ev γ a _ rfl U (x.sub j a hx)) =
      μ.mul U t (-(a' : ℤ) + k) tu h' b (ev γ a' _ rfl U (x.sub j' a' hx')) := by
  subst ha hj
  rfl

end GlobalTheory.EtC

theorem GlobalTheory.EtC.Pair.cup_assoc_of_mul_assoc : ∀ (R : Type) [CommRing R] {I J K M M' L : Cx R} (μ : Pair I J M) (ν : Pair M K L) (μ' : Pair J K M') (ν' : Pair I M' L), (∀ (U : Scheme.{0}) (s t u st tu w : ℤ) (h1 : s + t = st) (h2 : st + u = w) (h3 : t + u = tu) (h4 : s + tu = w) a b c, ν.mul U st u w h2 (μ.mul U s t st h1 a b) c = ν'.mul U s tu w h4 a (μ'.mul U t u tu h3 b c)) → ∀ (E : Spc) {n m k nm mk w : ℤ} (h1 : n + m = nm) (h2 : nm + k = w) (h3 : m + k = mk) (h4 : n + mk = w) a b c, ν.cup E h2 (μ.cup E h1 a b) c = ν'.cup E h4 a (μ'.cup E h3 b c) := by
  intro R _ I J K M M' L μ ν μ' ν' hA E n m k nm mk w h1 h2 h3 h4 a b c
  obtain ⟨α, rfl⟩ := CohomologyClass.mk_surjective a
  obtain ⟨β, rfl⟩ := CohomologyClass.mk_surjective b
  obtain ⟨γ, rfl⟩ := CohomologyClass.mk_surjective c
  obtain ⟨δ, hδ⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ h1).1 α β
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ h1).2 α β δ hδ]
  obtain ⟨ε, hε⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν h2).1 δ γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν h2).2 δ γ ε hε]
  obtain ⟨δ', hδ'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).1 β γ
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R μ' h3).2 β γ δ' hδ']
  obtain ⟨ε', hε'⟩ := (GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).1 α δ'
  rw [(GlobalTheory.T.cup_eq_class_of_isAW R ν' h4).2 α δ' ε' hε']
  suffices hh : ε.1 = ε'.1 by rw [show ε = ε' from Subtype.ext hh]
  apply (GlobalTheory.T.etaleCochainEvalOnSimplex_basic_properties R (E := E) (I := L) (n := w)).2.2.1
  intro N s hs U x
  rw [hε N s hs U x, hε' N s hs U x]
  have ss := fun {N' : ℕ} (y : Sx E N' U) => (GlobalTheory.T.etaleSpaceSimplicesOver_sub_composite y).1
  let G : ℕ → ℕ → Sec (L.X s) U := fun p r => if hpr : p + r ≤ N then
    (((mk * (p : ℤ) + k * (r : ℤ)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α.1 p _ rfl U (x.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β.1 r _ rfl U (x.sub p r hpr)) (ev γ.1 (N - p - r) _ rfl U (x.sub (p + r) (N - p - r) (by omega))))
    else 0
  trans ∑ P ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (P + 1), G p (P - p)
  · rw [← Fin.sum_univ_eq_sum_range (fun P => ∑ p ∈ Finset.range (P + 1), G p (P - p)) (N + 1)]
    refine Finset.sum_congr rfl fun P _ => ?_
    have hP := P.isLt
    rw [hδ (P : ℕ) _ _ U (x.sub 0 (P : ℕ) (by omega)), map_sum, LinearMap.sum_apply, Finset.smul_sum,
      ← Fin.sum_univ_eq_sum_range (fun p => G p ((P : ℕ) - p)) ((P : ℕ) + 1)]
    refine Finset.sum_congr rfl fun p _ => ?_
    have hp := p.isLt
    simp only [G]
    rw [dif_pos (by omega), Units.smul_def, Units.smul_def, map_zsmul, LinearMap.smul_apply, smul_smul,
      ← Units.val_mul, ← Int.negOnePow_add]
    rw [hA (tu := -((N - (p : ℕ) : ℕ) : ℤ) + mk)]
    rotate_left
    · omega
    · omega
    rw [ss, ss, GlobalTheory.EtC.Sx.sub_congr x (show 0 + 0 = 0 from rfl) _ (by omega),
      GlobalTheory.EtC.Sx.sub_congr x (show 0 + (p : ℕ) = p by omega) _ (by omega)]
    rw [GlobalTheory.EtC.Pair.mul_ev_congr μ' γ.1 x _ _ _ (a' := N - (p : ℕ) - ((P : ℕ) - (p : ℕ)))
      (j' := (p : ℕ) + ((P : ℕ) - (p : ℕ))) (by omega) (by omega) _ (by omega) _ (by omega)]
    have hsg : (k * ((P : ℕ) : ℤ) + m * ((p : ℕ) : ℤ)).negOnePow =
        (mk * ((p : ℕ) : ℤ) + k * (((P : ℕ) - (p : ℕ) : ℕ) : ℤ)).negOnePow := by
      congr 1
      rw [Nat.cast_sub (by omega), ← h3]
      ring
    rw [hsg]
  trans ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), G p r
  · exact GlobalTheory.EtC.sum_range_triangle G N
  rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), G p r) (N + 1)]
  refine Finset.sum_congr rfl fun p _ => ?_
  have hp := p.isLt
  rw [hδ' (N - (p : ℕ)) _ _ U (x.sub (p : ℕ) (N - (p : ℕ)) (by omega)), map_sum, Finset.smul_sum,
    ← Fin.sum_univ_eq_sum_range (fun r => G p r) (N - (p : ℕ) + 1)]
  refine Finset.sum_congr rfl fun r _ => ?_
  have hr := r.isLt
  simp only [G]
  rw [dif_pos (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul, ← Units.val_mul,
    ← Int.negOnePow_add, ss, ss]
  rfl
