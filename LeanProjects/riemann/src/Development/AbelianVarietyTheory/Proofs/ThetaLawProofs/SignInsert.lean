import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.IsSquareDeterminantComparison
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.MemNonzeroLocusVia
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.IsPluriharmonicSiegel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.OneEqSpTranslZero
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw
open GlobalTheory.KeyKa
noncomputable section
namespace GlobalTheory.KeyKa.KoszulCx
section Alg
variable {R : Type} [CommRing R] {g d : ℕ} {N : ℕ → ℕ}

theorem sign_insert (I : Finset (Fin g)) {i i' : Fin g} (hi : i ∉ I) :
    ((-1 : R)) ^ ((insert i I).filter (· < i')).card =
      (if i < i' then -1 else 1) * (-1) ^ (I.filter (· < i')).card := by
  rw [Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (fun h' => hi (Finset.mem_filter.1 h').1), pow_succ']
  · rw [_root_.one_mul]

theorem kosD_deg (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (p q : KIx g d N) (h : kdeg q ≠ kdeg p + 1) : kosD m ev p q = 0 := by
  rcases p with p | p <;> rcases q with q | q
  · simp only [kosD]
    refine Finset.sum_eq_zero fun i _ => if_neg ?_
    rintro ⟨hi, hq⟩
    apply h
    simp [kdeg, hq, Finset.card_insert_of_notMem hi]
  · rfl
  · simp only [kosD]
    refine if_neg fun hq => h ?_
    simp [kdeg, hq]
  · rfl

theorem isCx_kosD (m : Fin g → ∀ j j', Matrix (Fin (N j)) (Fin (N j')) R) (ev : ∀ j, Matrix (Fin d) (Fin (N j)) R)
    (hc : ∀ i i' j, j + 2 ≤ g → m i j (j + 1) * m i' (j + 1) (j + 2) = m i' j (j + 1) * m i (j + 1) (j + 2))
    (he : ∀ i, ev 0 * m i 0 (0 + 1) = 0) : IsCx kdeg (kosD m ev) := by
  have hc' : ∀ i i' j j₁ j₁' j₂, j₁ = j + 1 → j₁' = j + 1 → j₂ = j + 2 → j₂ ≤ g →
      m i j j₁ * m i' j₁ j₂ = m i' j j₁' * m i j₁' j₂ := by
    rintro i i' j _ _ _ rfl rfl rfl h
    exact hc i i' j h
  have he' : ∀ i j j₁, j = 0 → j₁ = 0 + 1 → ev j * m i j j₁ = 0 := by
    rintro i _ _ rfl rfl
    exact he i
  refine ⟨kosD_deg m ev, ?_⟩
  ext p r
  rw [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.zero_apply]
  rcases r with ⟨K, c⟩ | r
  swap
  · rcases p with p | p <;> simp [kosD]
  rcases p with ⟨I, a⟩ | a
  · have h2 : ∑ q : Fin d, kosD m ev (.inl ⟨I, a⟩) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    let T : Fin g → Fin g → R := fun i i' =>
      if i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I) then
        (-1) ^ (I.filter (· < i)).card * (-1) ^ ((insert i I).filter (· < i')).card *
          (m i I.card (insert i I).card * m i' (insert i I).card K.card) a c else 0
    have h3 : ∀ J : Finset (Fin g), ∑ k : Fin (N J.card),
        kosD m ev (.inl ⟨I, a⟩) (.inl ⟨J, k⟩) * kosD m ev (.inl ⟨J, k⟩) (.inl ⟨K, c⟩) =
        ∑ i, if J = insert i I then ∑ i', T i i' else 0 := by
      intro J
      simp only [kosD, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hJ : J = insert i I
      · subst hJ
        rw [if_pos rfl]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun i' _ => ?_
        by_cases hi : i ∉ I
        · by_cases hi' : i' ∉ insert i I ∧ K = insert i' (insert i I)
          · simp only [T]
            rw [if_pos ⟨hi, hi'⟩, Matrix.mul_apply, Finset.mul_sum]
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [if_pos ⟨hi, trivial⟩, if_pos hi']
            ring
          · simp only [T]
            rw [if_neg (fun h => hi' h.2)]
            exact Finset.sum_eq_zero fun k _ => by rw [if_neg hi', mul_zero]
        · simp only [T]
          rw [if_neg (fun h => hi h.1)]
          exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hi h.1), zero_mul]
      · rw [if_neg hJ]
        exact Finset.sum_eq_zero fun k _ => by rw [if_neg (fun h => hJ h.2), zero_mul]
    rw [Finset.sum_congr rfl fun J _ => h3 J, Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rw [← Fintype.sum_prod_type']
    have hT : ∀ i i', T i i' + T i' i = 0 := by
      intro i i'
      by_cases h : i ∉ I ∧ i' ∉ insert i I ∧ K = insert i' (insert i I)
      · obtain ⟨h1, h2, h3⟩ := h
        have hne : i' ≠ i := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
        have h4 : i' ∉ I := fun e => h2 (Finset.mem_insert_of_mem e)
        have h5 : i ∉ insert i' I := by simp [h1, hne.symm]
        have h6 : K = insert i (insert i' I) := h3.trans (Finset.insert_comm _ _ _)
        have hK : K.card = I.card + 2 := by
          rw [h3, Finset.card_insert_of_notMem h2, Finset.card_insert_of_notMem h1]
        have hg : K.card ≤ g := by simpa using Finset.card_le_univ K
        simp only [T]
        rw [if_pos ⟨h1, h2, h3⟩, if_pos ⟨h4, h5, h6⟩, sign_insert I h1, sign_insert I h4,
          hc' i i' _ _ _ _ (Finset.card_insert_of_notMem h1) (Finset.card_insert_of_notMem h4) hK hg]
        rcases lt_or_gt_of_ne hne with hlt | hlt
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
        · rw [if_pos hlt, if_neg hlt.not_gt]; ring
      · have h' : ¬ (i' ∉ I ∧ i ∉ insert i' I ∧ K = insert i (insert i' I)) := by
          rintro ⟨h1, h2, h3⟩
          have hne : i ≠ i' := fun e => h2 (e ▸ Finset.mem_insert_self _ _)
          exact h ⟨fun e => h2 (Finset.mem_insert_of_mem e), by simp [h1, hne.symm],
            h3.trans (Finset.insert_comm _ _ _)⟩
        simp only [T]
        rw [if_neg h, if_neg h', add_zero]
    refine Finset.sum_involution (fun p _ => p.swap) (fun p _ => hT p.1 p.2) ?_ (fun _ _ => Finset.mem_univ _)
      (fun p _ => Prod.swap_swap p)
    rintro ⟨i, i'⟩ _ h e
    apply h
    obtain rfl : i' = i := congrArg Prod.fst e
    exact if_neg fun h => h.2.1 (Finset.mem_insert_self _ _)
  · have h2 : ∑ q : Fin d, kosD m ev (.inr a) (.inr q) * kosD m ev (.inr q) (.inl ⟨K, c⟩) = 0 := by
      simp [kosD]
    rw [h2, add_zero, Fintype.sum_sigma]
    refine Finset.sum_eq_zero fun J _ => ?_
    simp only [kosD]
    by_cases hJ : J = ∅
    · simp only [if_pos hJ, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      by_cases h : i ∉ J ∧ K = insert i J
      · simp only [if_pos h]
        have e := congrFun (congrFun (he' i J.card K.card (by simp [hJ]) (by simp [h.2, hJ])) a) c
        rw [Matrix.mul_apply, Matrix.zero_apply] at e
        rw [← mul_zero ((-1 : R) ^ (J.filter (· < i)).card), ← e, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      · simp only [if_neg h, mul_zero, Finset.sum_const_zero]
    · simp only [if_neg hJ, zero_mul, Finset.sum_const_zero]

end Alg

section Geo
variable {R : Type} [CommRing R]

def mulSec {X : Scheme.{0}} (L : LB X) {a b c : ℤ} (h : c = a + b) (s : LB.Sec (pw L a)) (t : LB.Sec (pw L b)) :
    LB.Sec (pw L c) where
  f := fun i => (show Γ(X, L.U i) from s.f i) * (show Γ(X, L.U i) from t.f i)
  compat := fun i j => by
    have hs : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (s.f i) =
      ((L.g i j ^ a : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (s.f j) := s.compat i j
    have ht : rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.f i) =
      ((L.g i j ^ b : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X inf_le_right (t.f j) := t.compat i j
    change rs X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (_ * _) =
      ((L.g i j ^ c : Γ(X, L.U i ⊓ L.U j)ˣ) : Γ(X, L.U i ⊓ L.U j)) * rs X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (_ * _)
    rw [map_mul, map_mul]
    erw [hs, ht]
    rw [h, zpow_add, Units.val_mul]
    exact mul_mul_mul_comm _ _ _ _

theorem valH_cst (x : KeyIn R) (z : Pt x) (U : x.P.A.left.Opens) (h : ⊤ ≤ z.left ⁻¹ᵁ U) (c : R) :
    valT (T := R) z.left U (cst x.P.A.hom U c) = c := by
  have h0 : valT (T := R) z.left U (cst x.P.A.hom U c) =
      valT (T := R) z.left U ((x.P.A.hom.appLE ⊤ U le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom c)) := rfl
  refine h0.trans ((EtBaseChange.valT_appLE (T := R) z.left x.P.A.hom (U := ⊤) le_top h _).trans ?_)
  have hz : z.left ≫ x.P.A.hom = 𝟙 (Sp R) := Over.w z
  erw [hz]
  rw [EtBaseChange.valT_eq _ _ le_top]
  have e3 : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_top = 𝟙 _ := by
    rw [← Scheme.Hom.id_appTop]; exact Scheme.Hom.appLE_eq_app _
  unfold EtBaseChange.valH
  erw [e3]
  simp

theorem cast_step {g n l j : ℕ} (h : g * n < l) (hj : j < g) :
    ((l - j * n : ℕ) : ℤ) = (n : ℤ) + ((l - (j + 1) * n : ℕ) : ℤ) := by
  have : (j + 1) * n ≤ g * n := Nat.mul_le_mul_right _ hj
  have h2 : (j + 1) * n = j * n + n := Nat.succ_mul _ _
  omega

theorem ring_coords {A S₀ S₁ : Type} [CommRing A] [Fintype S₀] [Fintype S₁] (φ : R →+* A) (b₀ : S₀ → A) (b₁ : S₁ → A)
    (M : Matrix S₀ S₁ R) (u f : A) (c : S₁ → R) (h2 : ∀ k, u * b₁ k = ∑ k', φ (M k' k) * b₀ k')
    (h1 : f = ∑ k, φ (c k) * b₁ k) : u * f = ∑ k', φ (∑ k, M k' k * c k) * b₀ k' := by
  rw [h1, Finset.mul_sum]
  simp only [map_sum, map_mul, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [mul_left_comm, h2 k, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k' _ => by ring

theorem ring_eval {A S : Type} [CommRing A] [Fintype S] (φ : R →+* A) (v : A → R) (ψ : A →+* R) (hv : ∀ a, v a = ψ a)
    (hc : ∀ c, v (φ c) = c) (b : S → A) (u f : A) (c : S → R) (hu : v u = 0) (h : u * f = ∑ k, φ (c k) * b k) :
    ∑ k, v (b k) * c k = 0 := by
  obtain rfl : v = ψ := funext hv
  have e := congrArg ψ h
  rw [map_mul, map_sum, hu, zero_mul] at e
  simp only [map_mul, hc] at e
  exact Eq.trans (Finset.sum_congr rfl fun k' _ => mul_comm _ _) e.symm

theorem coords_mul (x : KeyIn R) {l₀ l₁ N₀ N₁ : ℕ} (b₀ : Fin N₀ → RR x l₀) (b₁ : Fin N₁ → RR x l₁)
    (M : Matrix (Fin N₀) (Fin N₁) R) (u f : ∀ i, Γ(x.P.A.left, x.P.L.U i)) (c : Fin N₁ → R)
    (hM : ∀ k, Coords x b₀ (fun k' => M k' k) (fun i => u i * (show Γ(x.P.A.left, x.P.L.U i) from (b₁ k).f i)))
    (hc : Coords x b₁ c f) : Coords x b₀ (fun k' => ∑ k, M k' k * c k) (fun i => u i * f i) := by
  exact fun i => ring_coords (cst x.P.A.hom (x.P.L.U i)) _ _ M (u i) (f i) c (fun k => hM k i) (hc i)

theorem koszul_isCx : ∀ (R : Type) [CommRing R] (x : KeyIn R) (n l d : ℕ) (s : Fin x.P.g → RR x n) (b : ∀ j, Fin ((l - j * n) ^ x.P.g) → RR x (l - j * n)) (z : Fin d → Pt x) (ch : Fin d → x.P.L.ι), x.P.g * n < l → (∀ j ≤ x.P.g, IsBasis x (b j)) → (∃ m, IsMul x l s b m) ∧ ∀ m, IsMul x l s b m → (∀ a, ⊤ ≤ (z a).left ⁻¹ᵁ x.P.L.U (ch a)) → (∀ a i, valT (T := R) (z a).left (x.P.L.U (ch a)) ((s i).f (ch a)) = 0) → IsCx kdeg (kosD (N := fun j => (l - j * n) ^ x.P.g) m (fun j => Matrix.of fun a k => valT (T := R) (z a).left (x.P.L.U (ch a)) ((b j k).f (ch a)))) := by
  intro R _ x n l d s b z ch hl hb
  refine ⟨?_, fun m hm hz hs => ?_⟩
  · have h1 : ∀ i j, ∀ k : Fin ((l - (j + 1) * n) ^ x.P.g), ∃ c : Fin ((l - j * n) ^ x.P.g) → R, j < x.P.g →
        Coords x (b j) c (fun c => (show Γ(x.P.A.left, x.P.L.U c) from (s i).f c) *
          (show Γ(x.P.A.left, x.P.L.U c) from (b (j + 1) k).f c)) := by
      intro i j k
      by_cases hj : j < x.P.g
      · obtain ⟨c, hc, -⟩ := hb j hj.le (mulSec x.P.L (cast_step hl hj) (s i) (b (j + 1) k))
        exact ⟨c, fun _ => hc⟩
      · exact ⟨0, fun h => absurd h hj⟩
    choose c hc using h1
    refine ⟨fun i j j' => if h : j' = j + 1 then Matrix.of fun k' k => c i j (h ▸ k) k' else 0, fun i j hj k => ?_⟩
    simp only [dif_pos, Matrix.of_apply]
    exact hc i j k hj
  · refine isCx_kosD (N := fun j => (l - j * n) ^ x.P.g) m _ (fun i i' j hj => ?_) (fun i => ?_)
    · ext k' k
      have hj0 : j < x.P.g := by omega
      have hj1 : j + 1 < x.P.g := by omega
      have e₁ := coords_mul x (b j) (b (j + 1)) (m i j (j + 1)) _ _ _ (hm i j hj0) (hm i' (j + 1) hj1 k)
      have e₂ := coords_mul x (b j) (b (j + 1)) (m i' j (j + 1)) _ _ _ (hm i' j hj0) (hm i (j + 1) hj1 k)
      have hu := hb j hj0.le (mulSec x.P.L (cast_step hl hj0) (s i)
        (mulSec x.P.L (cast_step hl hj1) (s i') (b (j + 2) k)))
      have e₃ := hu.unique e₁ (fun c => (mul_left_comm _ _ _).trans (e₂ c))
      exact congrFun e₃ k'
    · ext a k
      exact ring_eval (cst x.P.A.hom (x.P.L.U (ch a))) (valT (T := R) (z a).left (x.P.L.U (ch a))) _
        (EtBaseChange.valT_eq (T := R) (z a).left _ (hz a)) (valH_cst x (z a) _ (hz a)) _ _ _ _ (hs a i)
        (hm i 0 i.pos k (ch a))

end Geo
end GlobalTheory.KeyKa.KoszulCx
end
