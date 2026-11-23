import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleAlexanderWhitneyCupCochainExistsForPairing

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

theorem awleib_ev_smul {R : Type} [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (u : ℤˣ)
    (α : Cochain ((chains R).obj E) I n)
    (p : ℕ) (s : ℤ) (h : -(p : ℤ) + n = s) (U : Scheme.{0}) (x : Sx E p U) :
    ev (u • α) p s h U x = u • ev α p s h U x := by
  rcases Int.units_eq_one_or u with rfl | rfl
  · rw [one_smul, one_smul]
  · rw [Units.neg_smul, Units.neg_smul, one_smul, one_smul]
    unfold ev
    rw [Cochain.neg_v, Preadditive.comp_neg]
    rfl

def EtaleSimplicialCochainEqOfEvaluationsAgree : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {K : Cx R} {k : ℤ} (γ γ' : Cochain ((chains R).obj E) K k),
    (∀ (N : ℕ) (w : ℤ) (h : -(N : ℤ) + k = w) (U : Scheme.{0}) (x : Sx E N U), ev γ N w h U x = ev γ' N w h U x) →
    γ = γ'

def EtaleAlexanderWhitneyLeibnizZeroSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (w : ℤ) (h : -((0 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E 0 U),
      ev (δ k k₁ γ) 0 w h U x = ev γ₁ 0 w h U x + n.negOnePow • ev γ₂ 0 w h U x

def EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k n₁ m₁ k₁ : ℤ} (hk : n + m = k)
    (hn : n + 1 = n₁) (hm : m + 1 = m₁) (hk₁ : n₁ + m = k₁) (hk₂ : n + m₁ = k₁)
    (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (γ : Cochain ((chains R).obj E) K k) (γ₁ γ₂ : Cochain ((chains R).obj E) K k₁),
    μ.IsAW hk α β γ → μ.IsAW hk₁ (δ n n₁ α) β γ₁ → μ.IsAW hk₂ α (δ m m₁ β) γ₂ →
    ∀ (P : ℕ) (w : ℤ) (h : -((P + 1 : ℕ) : ℤ) + k₁ = w) (U : Scheme.{0}) (x : Sx E (P + 1) U),
      ev (δ k k₁ γ) (P + 1) w h U x = ev γ₁ (P + 1) w h U x + n.negOnePow • ev γ₂ (P + 1) w h U x

theorem etale_zero_simplex_subface_zero_zero_eq_self {E : Spc} {U : Scheme.{0}} (x : Sx E 0 U) (h : 0 + 0 ≤ 0) : x.sub 0 0 h = x := by
  unfold Sx.sub
  have e : SimplexCategory.subinterval 0 0 h = 𝟙 _ := by
    ext i
    exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)
  rw [e, op_id, E.map_id]
  rfl

theorem etale_alexander_whitney_cup_evaluation_degree_zero {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) {E : Spc} {n m k : ℤ} (hk : n + m = k)
    {α : Cochain ((chains R).obj E) I n} {β : Cochain ((chains R).obj E) J m} {γ : Cochain ((chains R).obj E) K k}
    (ha : μ.IsAW hk α β γ) (s t w : ℤ) (hs : -((0 : ℕ) : ℤ) + n = s) (ht : -((0 : ℕ) : ℤ) + m = t)
    (hw : -((0 : ℕ) : ℤ) + k = w) (h : s + t = w) (U : Scheme.{0}) (x : Sx E 0 U) :
    ev γ 0 w hw U x = μ.mul U s t w h (ev α 0 s hs U x) (ev β 0 t ht U x) := by
  subst hs ht hw
  rw [ha 0 _ _ U x, Fin.sum_univ_one]
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, Int.negOnePow_zero, one_smul]
  rw [etale_zero_simplex_subface_zero_zero_eq_self]

theorem awleib_leib' {R : Type} [CommRing R] {I J K : Cx R} (μ : Pair I J K) (U : Scheme.{0})
    (s t w s' t' w' : ℤ) (h : s + t = w) (hs : s + 1 = s') (ht : t + 1 = t') (hw : w + 1 = w')
    (h1 : s' + t = w') (h2 : s + t' = w') (a : Sec (I.X s) U) (b : Sec (J.X t) U) :
    Sec.map (K.d w w') (μ.mul U s t w h a b) = μ.mul U s' t w' h1 (Sec.map (I.d s s') a) b +
      s.negOnePow • μ.mul U s t' w' h2 a (Sec.map (J.d t t') b) := by
  subst hs ht hw
  exact μ.leibniz U s t w h a b

def EtaleCochainDifferentialEvaluationDegreeZero : Prop :=
  ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n)
    (U : Scheme.{0}) (x : Sx E 0 U) (w w' : ℤ) (h : -((0 : ℕ) : ℤ) + n = w) (h' : -((0 : ℕ) : ℤ) + m = w'),
    ev (δ n m α) 0 w' h' U x = Sec.map (I.d w w') (ev α 0 w h U x)

theorem awleib_zero_of (hd : EtaleCochainDifferentialEvaluationDegreeZero) : EtaleAlexanderWhitneyLeibnizZeroSimplexDegree := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  rw [hd R (by omega) γ U x (-((0 : ℕ) : ℤ) + k) w rfl h,
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk ha (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m) _ rfl rfl rfl (by omega),
    awleib_leib' μ U _ _ _ (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m₁) w _ (by omega) (by omega) (by omega)
      (by omega) (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₁ h1 (-((0 : ℕ) : ℤ) + n₁) (-((0 : ℕ) : ℤ) + m) w rfl rfl h (by omega),
    etale_alexander_whitney_cup_evaluation_degree_zero μ hk₂ h2 (-((0 : ℕ) : ℤ) + n) (-((0 : ℕ) : ℤ) + m₁) w rfl rfl h (by omega),
    hd R hn α U x _ _ rfl rfl, hd R hm β U x _ _ rfl rfl]
  simp

theorem etale_alexander_whitney_leibniz_of_ext_degree_zero_succ (h0 : EtaleSimplicialCochainEqOfEvaluationsAgree) (hd : EtaleCochainDifferentialEvaluationDegreeZero)
    (hs : EtaleAlexanderWhitneyLeibnizPositiveSimplexDegree) : EtaleAlexanderWhitneyCupLeibnizRule := by
  intro R _ I J K μ E n m k n₁ m₁ k₁ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2
  apply h0 R
  intro N w h U x
  rw [ev_add', awleib_ev_smul]
  cases N with
  | zero => exact awleib_zero_of hd R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 w h U x
  | succ P => exact hs R μ hk hn hm hk₁ hk₂ α β γ γ₁ γ₂ ha h1 h2 P w h U x

end LateralTheory.EtaleFoundations
