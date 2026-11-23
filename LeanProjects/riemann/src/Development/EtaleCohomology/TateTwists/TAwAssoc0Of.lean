import Development.EtaleCohomology.TateTwists.EtaleCochainCupAssocOfCupSpecAndAlexanderWhitney
import Development.EtaleCohomology.TateTwists.EtaleCochainEvaluationLinear
import Development.EtaleCohomology.TateTwists.EtaleSimplexSubfaceComposition

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

lemma aw_diag {M : Type*} [AddCommMonoid M] (N : ℕ) (Φ : ℕ → ℕ → M) :
    ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) =
      ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := by
  rw [Finset.sum_range_diag_flip]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_range] at hp
  rw [show N + 1 - p = N - p + 1 by omega]

lemma bil_zsmul_left {S A B C : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (c : ℤ) (a : A) (b : B) :
    f (c • a) b = c • f a b := by
  have := map_zsmul (f.flip b) c a
  simpa using this

lemma bil_sum_left {S A B C ι : Type*} [CommRing S] [AddCommGroup A] [Module S A] [AddCommGroup B] [Module S B]
    [AddCommGroup C] [Module S C] (f : A →ₗ[S] B →ₗ[S] C) (s : Finset ι) (a : ι → A) (b : B) :
    f (∑ i ∈ s, a i) b = ∑ i ∈ s, f (a i) b := by
  have := map_sum (f.flip b) a s
  simpa using this

variable {R : Type} [CommRing R]

lemma mul_ev_right {A B C : Cx R} (P : Pair A B C) {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) {s k w : ℤ}
    (a : Sec (A.X s) U) (γ : Cochain ((chains R).obj E) B k) (t t' j j' : ℕ) (ht : t = t') (hj : j = j')
    (h : s + (-(t : ℤ) + k) = w) (h' : s + (-(t' : ℤ) + k) = w) (hl : j + t ≤ N) (hl' : j' + t' ≤ N) :
    P.mul U s (-(t : ℤ) + k) w h a (ev γ t _ rfl U (x.sub j t hl)) =
      P.mul U s (-(t' : ℤ) + k) w h' a (ev γ t' _ rfl U (x.sub j' t' hl')) := by
  subst ht hj; rfl

theorem t_aw_assoc0_of (hev : EtaleCochainEvaluationLinear) (hsub : EtaleSimplexSubfaceComposition) : t_aw_assoc0 := by
  intro R _ I J K M M' L μ ν μ' ν' hass E n m k nm mk w h1 h2 h3 h4 α β γ ab bc x y hab hx hbc hy
  refine (hev R).2.2.1 x y fun N s hs U z => ?_
  rw [hx N s hs U z, hy N s hs U z]
  let Φ : ℕ → ℕ → Sec (L.X s) U := fun p r => if h : p + r ≤ N then
    (((m * (p : ℤ) + k * ((p : ℤ) + r)).negOnePow : ℤˣ) : ℤ) •
      ν'.mul U (-(p : ℤ) + n) (-((N - p : ℕ) : ℤ) + mk) s (by omega) (ev α p _ rfl U (z.sub 0 p (by omega)))
        (μ'.mul U (-(r : ℤ) + m) (-((N - p - r : ℕ) : ℤ) + k) (-((N - p : ℕ) : ℤ) + mk) (by omega)
          (ev β r _ rfl U (z.sub p r (by omega))) (ev γ (N - p - r) _ rfl U (z.sub (p + r) (N - p - r) (by omega))))
    else 0
  have hsg : ∀ a b c : ℤ, a + b = c → ((a.negOnePow : ℤˣ) : ℤ) * ((b.negOnePow : ℤˣ) : ℤ) = ((c.negOnePow : ℤˣ) : ℤ) := by
    intro a b c h; rw [← Units.val_mul, ← Int.negOnePow_add, h]
  calc _ = ∑ q : Fin (N + 1), ∑ p : Fin ((q : ℕ) + 1), Φ p ((q : ℕ) - p) := by
          refine Finset.sum_congr rfl fun q _ => ?_
          rw [hab, bil_sum_left, Finset.smul_sum]
          refine Finset.sum_congr rfl fun p _ => ?_
          have hp := p.is_lt
          have hq := q.is_lt
          simp only [Φ]
          rw [dif_pos (by omega), Units.smul_def, Units.smul_def, bil_zsmul_left, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + (((q : ℕ) - (p : ℕ) : ℕ) : ℤ)))
              (by push_cast [Nat.cast_sub (show (p : ℕ) ≤ q by omega)]; ring)]
          congr 1
          rw [hass U _ _ _ _ (-((N - p : ℕ) : ℤ) + mk) s _ _ (by omega) (by omega)]
          rw [(hsub z).1 0 q 0 p, (hsub z).1 0 q p (q - p)]
          simp only [Nat.zero_add]
          congr 1
          exact mul_ev_right _ z _ γ (N - q) (N - p - (q - p)) q (p + (q - p)) (by omega) (by omega) _ _ _ _
    _ = ∑ q ∈ Finset.range (N + 1), ∑ p ∈ Finset.range (q + 1), Φ p (q - p) := by
          rw [← Fin.sum_univ_eq_sum_range (fun q => ∑ p ∈ Finset.range (q + 1), Φ p (q - p))]
          exact Finset.sum_congr rfl fun q _ => Fin.sum_univ_eq_sum_range (fun p => Φ p (q - p)) _
    _ = ∑ p ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N - p + 1), Φ p r := aw_diag N Φ
    _ = ∑ p : Fin (N + 1), ∑ r : Fin (N - (p : ℕ) + 1), Φ p r := by
          rw [← Fin.sum_univ_eq_sum_range (fun p => ∑ r ∈ Finset.range (N - p + 1), Φ p r)]
          exact Finset.sum_congr rfl fun p _ => (Fin.sum_univ_eq_sum_range (fun r => Φ p r) _).symm
    _ = _ := by
          refine Finset.sum_congr rfl fun p _ => ?_
          rw [hbc, map_sum, Finset.smul_sum]
          refine Finset.sum_congr rfl fun r _ => ?_
          have hp := p.is_lt
          have hr := r.is_lt
          simp only [Φ]
          rw [dif_pos (by omega), Units.smul_def, Units.smul_def, map_zsmul, smul_smul,
            hsg _ _ (m * ((p : ℕ) : ℤ) + k * (((p : ℕ) : ℤ) + ((r : ℕ) : ℤ))) (by subst h3; ring)]
          rw [(hsub z).1 p (N - p) 0 r, (hsub z).1 p (N - p) r (N - p - r)]
          simp only [Nat.add_zero]

end LateralTheory.EtaleFoundations
