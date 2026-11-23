import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.PhiPow
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.UT.PhiOrder

section Alg

variable {A U : Type} [CommGroup A] [CommGroup U] {θ : A → A → A → U}

def pot (θ : A → A → A → U) (b : A) (n : ℕ) : U := ∏ j ∈ Finset.range n, cubN θ j 1 b b

theorem pot_zero (b : A) : Additive.ofMul (pot θ b 0) = 0 := by simp [pot]

theorem pot_one (b : A) : Additive.ofMul (pot θ b 1) = 0 := by simp [pot, cubN]

theorem pot_two (h : IsCub θ) (b : A) : Additive.ofMul (pot θ b 2) = 0 := by
  simp [pot, cubN, Finset.prod_range_succ, h.face]

theorem cub_eq_pot (h : IsCub θ) (b : A) (i j l : ℕ) :
    Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) = Additive.ofMul (pot θ b (i + j + l)) - Additive.ofMul (pot θ b (i + j)) -
      Additive.ofMul (pot θ b (i + l)) - Additive.ofMul (pot θ b (j + l)) + Additive.ofMul (pot θ b i) +
      Additive.ofMul (pot θ b j) + Additive.ofMul (pot θ b l) := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have P2 : P 2 = 0 := pot_two h b
  show _ = P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l
  have step : ∀ l : ℕ, (∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ l)) =
      P (i + 1 + l) - P (i + 1) - P (i + l) - P (1 + l) + P i + P 1 + P l) → ∀ j i,
      Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
        P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := by
    intro l H j
    induction j with
    | zero => intro i; rw [pow_zero, h.face₂, ofMul_one, add_zero, zero_add, P0]; abel
    | succ j ih =>
      intro i
      have c := congrArg Additive.ofMul (h.coc (b ^ i) (b ^ j) (b ^ 1) (b ^ l))
      rw [← pow_add, ← pow_add, ofMul_mul, ofMul_mul, H, H, ih] at c
      rw [← add_assoc i j 1]
      linear_combination (norm := abel) -c
  have base : ∀ i, Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) =
      P (i + 1 + 1) - P (i + 1) - P (i + 1) - P (1 + 1) + P i + P 1 + P 1 := by
    intro i
    have e₁ : P (i + 1 + 1) = P (i + 1) + Additive.ofMul (cubN θ (i + 1) 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ (i + 1), ofMul_mul]
    have e₂ : P (i + 1) = P i + Additive.ofMul (cubN θ i 1 b b) := by
      simp only [hP, pot, Finset.prod_range_succ _ i, ofMul_mul]
    have e₃ : Additive.ofMul (cubN θ (i + 1) 1 b b) = Additive.ofMul (cubN θ i 1 b b) +
        Additive.ofMul (θ (b ^ i) (b ^ 1) (b ^ 1)) := by
      simp only [cubN, Finset.prod_range_succ _ i, ofMul_mul, _root_.one_mul, pow_one]
    rw [show 1 + 1 = 2 from rfl, P2, P1]
    linear_combination (norm := abel) - e₁ + e₂ - e₃
  refine step l (fun i => ?_) j i
  rw [h.s12, step 1 base l i, add_right_comm i l 1, add_comm l 1]
  abel

theorem cubN_eq_pot (h : IsCub θ) (b : A) (n a c x : ℕ) :
    Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = Additive.ofMul (pot θ b (a + c * n + x)) -
      Additive.ofMul (pot θ b (a + x)) - Additive.ofMul (pot θ b (a + c * n)) + Additive.ofMul (pot θ b a) -
      n • (Additive.ofMul (pot θ b (c + x)) - Additive.ofMul (pot θ b c) - Additive.ofMul (pot θ b x)) := by
  induction n with
  | zero => simp [cubN]
  | succ n ih =>
    rw [cubN, Finset.prod_range_succ, ofMul_mul, ← cubN, ih, ← pow_mul, ← pow_add, cub_eq_pot h, mul_add c n 1,
      _root_.mul_one, ← add_assoc a, succ_nsmul]
    abel

theorem const_eq_one (h : IsCub θ) (b : A) (m k : ℕ) (hk : k = 2 * m + 1) (S : ℕ → U) (s w ψ ρ τ E : U)
    (hS : ∀ i, S i * cubN θ i 1 (b ^ k) b = s ^ i) (hτ : τ * cubN θ k 1 b (b ^ k) = s ^ k)
    (hE : τ = E * ψ ^ 2 * ρ ^ 2)
    (hw : w ^ k * ((E * pot θ b (2 * k)) ^ m * (pot θ b k ^ (k + 2 * m))⁻¹) = ψ * ρ) :
    (∏ i ∈ Finset.range k, H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) * (ψ ^ k * ρ ^ k)⁻¹ = 1 := by
  set P : ℕ → Additive U := fun n => Additive.ofMul (pot θ b n) with hP
  have P0 : P 0 = 0 := pot_zero b
  have P1 : P 1 = 0 := pot_one b
  have cN : ∀ n a c x, Additive.ofMul (cubN θ n (b ^ a) (b ^ c) (b ^ x)) = P (a + c * n + x) - P (a + x) - P (a + c * n) +
    P a - n • (P (c + x) - P c - P x) := cubN_eq_pot h b
  have cT : ∀ i j l, Additive.ofMul (θ (b ^ i) (b ^ j) (b ^ l)) =
    P (i + j + l) - P (i + j) - P (i + l) - P (j + l) + P i + P j + P l := cub_eq_pot h b
  let f : ℕ → Additive U := fun i => P (k * i + (k - i)) + k • P (k - i) - P (k - i) - P (k * i)
  let d : Additive U := Additive.ofMul s + P (k + 1) - P k
  have term : ∀ i ∈ Finset.range k, Additive.ofMul (H1.hv θ k ((b ^ k) ^ i) b (b ^ (k - 1 - i)) * (S i * w)) =
      (f (i + 1) - f i) + (i • d + Additive.ofMul w) := by
    intro i hi
    obtain ⟨x, hx⟩ : ∃ x, k = i + 1 + x := ⟨k - (i + 1), by have := Finset.mem_range.1 hi; omega⟩
    have x₁ : k - 1 - i = x := by omega
    have x₂ : k - (i + 1) = x := by omega
    have x₃ : k - i = 1 + x := by omega
    have a₁ := cN k (k * i) 1 x
    have a₂ := cT (k * i) x 1
    have a₃ := cN i 0 k 1
    have a₄ := congrArg Additive.ofMul (hS i)
    rw [pow_one] at a₁ a₂ a₃
    rw [pow_zero, zero_add, zero_add, P0, P1] at a₃
    rw [_root_.one_mul, P1, ← Nat.mul_succ] at a₁
    rw [P1, add_assoc (k * i), add_comm x 1] at a₂
    rw [ofMul_mul, a₃, ofMul_pow] at a₄
    simp only [f, d, H1.hv, ofMul_mul, ofMul_inv, x₁, x₂, x₃, ← pow_mul, a₁, a₂, Nat.succ_eq_add_one]
    linear_combination (norm := module) a₄
  have gauss : ∑ i ∈ Finset.range k, i = m * k := by
    have := Finset.sum_range_id_mul_two k
    rw [show k - 1 = 2 * m by omega] at this
    nlinarith
  apply Additive.ofMul.injective
  rw [ofMul_mul, ofMul_prod, Finset.sum_congr rfl term, Finset.sum_add_distrib, Finset.sum_range_sub,
    Finset.sum_add_distrib, Finset.sum_nsmul_assoc, gauss, Finset.sum_const, Finset.card_range]
  have a₁ := cN k 0 1 k
  rw [pow_zero, pow_one, zero_add, zero_add, _root_.one_mul, ← two_mul, add_comm 1 k, P0, P1] at a₁
  have a₂ := congrArg Additive.ofMul hτ
  have a₃ := congrArg Additive.ofMul hw
  rw [ofMul_mul, a₁, hE] at a₂
  simp only [ofMul_mul, ofMul_pow, ofMul_inv, ofMul_one, f, d, Nat.sub_self, add_zero, mul_zero, zero_add, Nat.sub_zero,
    P0] at a₂ a₃ ⊢
  change k • _ + (m • (_ + P (2 * k)) + -((k + 2 * m) • P k)) = _ at a₃
  subst hk
  linear_combination (norm := module) a₃ - m • a₂

end Alg

section Formal

variable {A U : Type} [CommGroup A] [CommGroup U]

def wN (h : A → U) (x : A) (j : ℕ) : U :=
  h (x ^ (j + 1)) * (h (x ^ j))⁻¹ * (h (x ^ 2) ^ j)⁻¹ * h x ^ (2 * j) * (h x)⁻¹ * h 1 * (h 1 ^ j)⁻¹

theorem prod_wN (h : A → U) (x : A) (n : ℕ) (T : ℤ) (hT : 2 * T = n * (n - 1)) :
    Additive.ofMul (∏ j ∈ Finset.range n, wN h x j) = Additive.ofMul (h (x ^ n)) - T • Additive.ofMul (h (x ^ 2)) +
      (2 * T - n) • Additive.ofMul (h x) + (n - 1 - T) • Additive.ofMul (h 1) := by
  induction n generalizing T with
  | zero =>
    obtain rfl : T = 0 := by simpa using hT
    simp
  | succ n ih =>
    rw [Finset.prod_range_succ, ofMul_mul, ih (T - n) (by push_cast at hT; linear_combination hT)]
    simp only [wN, ofMul_mul, ofMul_inv, ofMul_pow]
    push_cast
    module

theorem weight_eq (h : A → U) (x : A) (m k : ℕ) (hk : k = 2 * m + 1) :
    ((h (x ^ k * (x ^ k)⁻¹ * x ^ k) * (h (x ^ k * (x ^ k)⁻¹))⁻¹ * (h (x ^ k * x ^ k))⁻¹ * (h ((x ^ k)⁻¹ * x ^ k))⁻¹ *
        h (x ^ k) * h (x ^ k)⁻¹ * h (x ^ k) * (h 1)⁻¹ * (h (x ^ k)⁻¹ * (h (x ^ k))⁻¹)⁻¹) *
        ∏ j ∈ Finset.range (2 * k), wN h x j) ^ m * ((∏ j ∈ Finset.range k, wN h x j) ^ (k + 2 * m))⁻¹ =
      h x ^ ((k ^ 2 : ℕ) : ℤ) * h (x ^ k) ^ (-((1 : ℕ) : ℤ)) * h 1 ^ (((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)) := by
  have a₁ := prod_wN h x (2 * k) (k * (2 * k - 1)) (by push_cast; ring)
  have a₂ := prod_wN h x k (m * k) (by rw [hk]; push_cast; ring)
  rw [mul_inv_cancel, inv_mul_cancel, _root_.one_mul, ← pow_add, ← two_mul]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow, a₁, a₂]
  subst hk
  push_cast
  module

end Formal

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

def Rep (V : ∀ (T : Over (Spec (CommRingCat.of R))) (_ : T ⟶ D.P.A) (z : T.left),
      ((T.left ⟶ D.P.A.left) → D.P.L.ι) → (T.left.presheaf.stalk z)ˣ)
    (W : ∀ (U : Type) [CommGroup U], ((D.P.A ⟶ D.P.A) → U) → U) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (φ : K → (D.P.A.left ⟶ D.P.A.left)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb D.P.L φ ε)),
    t.IsGen ∧ (∀ (U : Type) [CommGroup U] (h : (D.P.A.left ⟶ D.P.A.left) → U),
      ∏ k, h (φ k) ^ ε k = W U (fun a => h a.left)) ∧
    ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val t x.left z J = V T x z J

variable {D}

theorem Rep.mul {V V' W W'} (h : Rep D V W) (h' : Rep D V' W') :
    Rep D (fun T x z J => V T x z J * V' T x z J) (fun U _ g => W U g * W' U g) := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := h
  obtain ⟨K', _, φ', ε', t', ht', hw', hv'⟩ := h'
  exact ⟨K ⊕ K', inferInstance, _, _, LB.mulGen D.P.L _ _ _ _ t t', mulGen_isGen _ _ _ _ _ _ _ ht ht',
    fun U _ g => prod_sum₂ _ (hw U g) (hw' U g),
    fun T x z J hJ => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hv T x z J hJ) (hv' T x z J hJ))⟩

theorem Rep.inv {V W} (h : Rep D V W) : Rep D (fun T x z J => (V T x z J)⁻¹) (fun U _ g => (W U g)⁻¹) := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := h
  exact ⟨K, inferInstance, _, _, LB.invGen D.P.L _ _ t, invGen_isGen _ _ _ _ ht,
    fun U _ g => prod_neg _ _ (hw U g),
    fun T x z J hJ => (val_inv _ _).trans (congrArg (·⁻¹) (hv T x z J hJ))⟩

theorem Rep.one : Rep D (fun _ _ _ _ => 1) (fun _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen D.P.L, fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    fun _ _ _ => Fintype.prod_empty _, fun _ _ _ _ _ => val_one _⟩

theorem Rep.prod {V : ℕ → _} {W : ℕ → _} (h : ∀ j, Rep D (V j) (W j)) (n : ℕ) :
    Rep D (fun T x z J => ∏ j ∈ Finset.range n, V j T x z J) (fun U _ g => ∏ j ∈ Finset.range n, W j U g) := by
  induction n with
  | zero => exact Rep.one
  | succ n ih => simpa only [Finset.prod_range_succ] using ih.mul (h n)

theorem Rep.pow {V W} (h : Rep D V W) (n : ℕ) : Rep D (fun T x z J => V T x z J ^ n) (fun U _ g => W U g ^ n) := by
  simpa only [Finset.prod_const, Finset.card_range] using Rep.prod (fun _ => h) n

theorem comp_idPow {T : Over (Spec (CommRingCat.of R))} (x : T ⟶ D.P.A) (k : ℕ) : x ≫ (𝟙 D.P.A ^ k) = x ^ k :=
  (map_pow (preHom x) _ _).trans (congrArg (· ^ k) (Category.comp_id x))

theorem rep_cubN (j : ℕ) : Rep D (fun _ x z J => cubN (th D z J) j 1 x x) (fun _ _ g => wN g (𝟙 _) j) := by
  obtain ⟨t, ht, hv⟩ := exists_cubN D.cub (1 : D.P.A ⟶ D.P.A) (𝟙 _) (𝟙 _) j
  refine ⟨_, inferInstance, _, _, t, ht, fun U _ h => ?_, fun T x z J hJ => ?_⟩
  · rw [_root_.one_mul, _root_.one_mul, ← pow_succ, ← sq]
    apply Additive.ofMul.injective
    simp [wN, Fin.prod_univ_succ, ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  · rw [hv T x z J hJ, MonObj.comp_one, Category.comp_id]

theorem rep_cub (k : ℕ) : Rep D (fun _ x z J => th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k))
    (fun _ _ h => h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k) * (h (𝟙 _ ^ k * (𝟙 _ ^ k)⁻¹))⁻¹ * (h (𝟙 _ ^ k * 𝟙 _ ^ k))⁻¹ *
      (h ((𝟙 _ ^ k)⁻¹ * 𝟙 _ ^ k))⁻¹ * h (𝟙 _ ^ k) * h (𝟙 _ ^ k)⁻¹ * h (𝟙 _ ^ k) * (h 1)⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
    (lift (𝟙 D.P.A ^ k) (lift (𝟙 D.P.A ^ k)⁻¹ (𝟙 D.P.A ^ k))).left, pullGen_isGen _ _ _ _ D.cub.isGen _,
    fun U _ h => prod_cub _ _ _ h, fun T x z J hJ => ?_⟩
  rw [val_cub D.cub x hJ, show x ≫ (𝟙 D.P.A ^ k)⁻¹ = (x ≫ (𝟙 D.P.A ^ k))⁻¹ from map_inv (preHom x) _, comp_idPow]

theorem rep_sym (k : ℕ) : Rep D (fun _ x z J => val D.sym (x ^ k).left z J)
    (fun _ _ h => h (𝟙 _ ^ k)⁻¹ * (h (𝟙 _ ^ k))⁻¹) := by
  refine ⟨_, inferInstance, _, _, LB.pullGen D.P.L _ _ D.sym (𝟙 D.P.A ^ k).left, pullGen_isGen _ _ _ _ D.sym_gen _,
    fun U _ h => ?_, fun T x z J hJ => ?_⟩
  · rw [Fin.prod_univ_two]
    show h ((𝟙 D.P.A ^ k) ≫ ι[D.P.A]).left ^ (1 : ℤ) * h ((𝟙 D.P.A ^ k).left ≫ 𝟙 _) ^ (-1 : ℤ) = _
    rw [zpow_one, zpow_neg_one, Category.comp_id]; rfl
  · rw [val_pull hJ, ← Over.comp_left, comp_idPow]

theorem exists_kap (m k : ℕ) (hk : k = 2 * m + 1) :
    ∃ κ : LB.Gen (kapLB D (𝟙 D.P.A ^ k) (k ^ 2) 1), Normd κ ∧
      ∀ T (x : T ⟶ D.P.A) z J, Good D.P.L z J → val κ x.left z J =
        (th D z J (x ^ k) (x ^ k)⁻¹ (x ^ k) * (val D.sym (x ^ k).left z J)⁻¹ * pot (th D z J) x (2 * k)) ^ m *
          (pot (th D z J) x k ^ (k + 2 * m))⁻¹ := by
  obtain ⟨K, _, φ, ε, t, ht, hw, hv⟩ := ((((rep_cub (D := D) k).mul (rep_sym k).inv).mul
    (Rep.prod rep_cubN (2 * k))).pow m).mul ((Rep.prod rep_cubN k).pow (k + 2 * m)).inv
  obtain ⟨κ, hκ, vκ⟩ := exists_gen D.P.isLB (K' := Fin 3)
    (φ' := ![𝟙 _, (𝟙 D.P.A ^ k).left, (1 : D.P.A ⟶ D.P.A).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ), ((1 : ℕ) : ℤ) - (k ^ 2 : ℕ)]) (fun U _ h => by
      rw [hw U h, Fin.prod_univ_three]
      exact weight_eq (fun a : D.P.A ⟶ D.P.A => h a.left) (𝟙 _) m k hk) t ht
  refine ⟨κ, ⟨hκ, corr_of_val D.P.isLB fun y J hJ => ?_⟩, fun T x z J hJ => (vκ _ _ z J hJ).trans (hv T x z J hJ)⟩
  have C : IsCub (th D (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) y J) := isCub_cubV D.cub hJ
  have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A).left = eSec D.P.A := by
    rw [Hom.one_def, toUnit_unit, Category.id_comp]; rfl
  have e := (vκ _ _ y J hJ).trans (hv (𝟙_ (Over (Spec (CommRingCat.of R)))) 1 y J hJ)
  have s₁ := val_corr hJ D.sym_rig (𝟙 _)
  rw [val_pull hJ, Category.id_comp, val_one] at s₁
  simp only [one_pow, C.face, C.N_one, Finset.prod_const_one, inv_one, _root_.mul_one, _root_.one_mul] at e
  rw [o, s₁, inv_one, one_pow] at e
  rw [val_pull hJ, Category.id_comp, val_one]
  exact e

variable {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem tau_diag (hB : D.TauBimult) (hE : D.PsiEven) {T : Over (Spec (CommRingCat.of R))} (σ : T ⟶ TF (R := R) F)
    {z : T.left} {J : (T.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J) (y : D.X) :
    val (D.tau y y) (σ.left ≫ jFK (R := R) F) z J =
      th D z J (cP D T y) (cP D T y)⁻¹ (cP D T y) * (val D.sym (cP D T y).left z J)⁻¹ *
        val (D.psi y) (σ.left ≫ jFK (R := R) F) z J ^ 2 * val D.rigK (σ.left ≫ jFK (R := R) F) z J ^ 2 := by
  have C : IsCub (th D z J) := isCub_cubV D.cub hJ
  have e : ∀ a b : D.X, val (D.tau a b) (σ.left ≫ jFK (R := R) F) z J =
      val (D.psi (a + b)) (σ.left ≫ jFK (R := R) F) z J * (val (D.psi a) (σ.left ≫ jFK (R := R) F) z J)⁻¹ *
        (val (D.psi b) (σ.left ≫ jFK (R := R) F) z J)⁻¹ * (val D.rigK (σ.left ≫ jFK (R := R) F) z J)⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))
  have c0 : cP D T 0 = 1 := by simpa using cPoint_nsmul D T 0 y
  have cn : cP D T (-y) = (cP D T y)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← cPoint_add, neg_add_cancel, c0]
  have t₀ := tau_mul σ hJ hB 0 0 y
  rw [c0, C.face, add_zero, e, zero_add] at t₀
  have t₁ := tau_mul σ hJ hB y (-y) y
  rw [add_neg_cancel, cn, e 0 y, e (-y) y, zero_add, neg_add_cancel] at t₁
  have t₂ := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_pull hJ _ _ _))).symm.trans
    (val_corr hJ (hE y) (σ.left ≫ jFK (R := R) F))
  have a₁ : (σ.left ≫ jFK (R := R) F) ≫ D.xK y = (cP D T y).left := by
    rw [← comp_cP D σ, Category.assoc]
    exact congrArg (σ.left ≫ ·) (Category.assoc _ _ _).symm
  rw [a₁] at t₂
  apply Additive.ofMul.injective
  have b₀ := congrArg Additive.ofMul t₀
  have b₁ := congrArg Additive.ofMul t₁
  have b₂ := congrArg Additive.ofMul t₂
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_one] at b₀ b₁ b₂ ⊢
  linear_combination (norm := module) -b₁ - 2 • b₀ + b₂

theorem const_one (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k) (w : Frm D F k p.g.b)
    (hw : TXFrame k p w) (z : (TF (R := R) F).left) (J : ((TF (R := R) F).left ⟶ D.P.A.left) → D.P.L.ι)
    (hJ : Good D.P.L z J) :
    (∏ i ∈ Finset.range k, H1.hv (th D z J) k ((p.g.b ^ k) ^ i) p.g.b (p.g.b ^ (k - 1 - i)) *
        (val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J * val w (Over.Hom.left (𝟙 (TF (R := R) F))) z J)) *
      (val (GeneratorPullback.powGen D.P.L _ _ (D.psi p.y) k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J *
        val (GeneratorPullback.powGen D.P.L _ _ D.rigK k) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J)⁻¹ = 1 := by
  obtain ⟨m, hm⟩ := hk
  have C : IsCub (th D (T := TF (R := R) F) z J) := isCub_cubV D.cub hJ
  obtain ⟨κ, hκ, vκ⟩ := exists_kap (D := D) m k hm
  have h₁ := hw.2.2 κ hκ z J hJ
  rw [vκ _ p.g.b z J hJ] at h₁
  have c0 : cP D (TF (R := R) F) 0 = 1 := by simpa using cPoint_nsmul D (TF (R := R) F) 0 p.y
  have s0 : val (p.g.s 0) (Over.Hom.left (𝟙 (TF (R := R) F))) z J = 1 := by
    have := gt_mul (𝟙 (TF (R := R) F)) hJ p.g 0 0
    rw [c0, C.face, add_zero] at this
    exact (mul_left_cancel this).symm
  have hS : ∀ i : ℕ, val (p.g.s (i • p.y)) (Over.Hom.left (𝟙 (TF (R := R) F))) z J *
      cubN (th D z J) i 1 (p.g.b ^ k) p.g.b = val (p.g.s p.y) (Over.Hom.left (𝟙 (TF (R := R) F))) z J ^ i := fun i => by
    have := gt_nsmul (𝟙 (TF (R := R) F)) hJ p.g 0 p.y i
    rwa [zero_add, c0, s0, _root_.one_mul, cPoint_y, Category.id_comp] at this
  have hτ := chain_val (𝟙 (TF (R := R) F)) hJ p p.y
  rw [Category.id_comp, cPoint_y] at hτ
  have hd := tau_diag hB hE (𝟙 (TF (R := R) F)) hJ p.y
  rw [cPoint_y] at hd
  have r₁ : rigV D (TF (R := R) F).hom z J =
      val D.rigK ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J := by
    refine Eq.trans ?_ (val_pull hJ _ _ _).symm
    refine congrArg (fun q => rigV D q z J) ?_
    rw [Over.id_left, Category.id_comp]; rfl
  have r₂ : val (D.psi p.y) (jFK (R := R) F) z J =
      val (D.psi p.y) ((Over.Hom.left (𝟙 (TF (R := R) F))) ≫ jFK (R := R) F) z J :=
    congrArg (fun q => val (D.psi p.y) q z J) (Category.id_comp _).symm
  have key := const_eq_one C p.g.b m k hm _ _ _ _ _ _ _ hS hτ hd (h₁.trans (congrArg₂ (· * ·) r₂ r₁))
  refine Eq.trans ?_ key
  exact congrArg₂ (· * ·) rfl (congrArg (·⁻¹) (congrArg₂ (· * ·) (map_pow _ _ _) (map_pow _ _ _)))

theorem phiPow_eq_one (hG : GlobalFnsSt) (hB : D.TauBimult) (hE : D.PsiEven) {k : ℕ} (hk : Odd k) (p : QkPt D F k)
    (w : Frm D F k p.g.b) (hX : TXFrame k p w) (ss : Fin (k + 1) → Fam D F k)
    (H : ∀ i : Fin k, PhiRel D F k p w (ss i.castSucc) (ss i.succ)) : ss (Fin.last k) = ss 0 := by
  have hw : w.IsGen := hX.1
  choose u hu hc using fun α => (gen_phi hG p w hw α).1
  choose v hv hcv using fun α => (gen_fe (D := D) (F := F) hG k p.y α).1
  have hb : DegPre.trF D F p.y = DegPre.trPt D F (p.g.b ^ k) := by rw [trF_eq, cPoint_y]
  have hV : ∀ α, ∃ a : Γ((TF (R := R) F).left, ⊤), ∀ (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D F).left) (z : Z) (J),
      Good D.P.L z J → ((∏ i ∈ Finset.range k,
        val (u (α + i • p.y)) (r ≫ (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left) z J) * (val (v α) r z J)⁻¹).val =
        gs (r ≫ (fst (TF (R := R) F) D.P.A).left) z ⊤ a := by
    intro α
    obtain ⟨K', _, φ', ε', t', ht', hf, hvt⟩ := H1.exists_gen_prod D.P.L (fun _ => Fin 4 ⊕ Fin 4)
      (fun i j => (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left ≫ DegPre.phiφ D F p.y (α + i • p.y) p.g.b j)
      (fun _ => DegPre.deltaε k)
      (fun i => LB.pullGen D.P.L _ _ (u (α + i • p.y)) (DegPre.trPt D F (p.g.b ^ (k - 1 - i))).left)
      (fun i => pullGen_isGen _ _ _ _ (hu _) _) k
    obtain ⟨a, ha⟩ := H1.exists_const D.P.L D.P.isLB (fst (TF (R := R) F) D.P.A).left (surj_appTop D F hG)
      (LB.mulGen D.P.L _ _ _ _ t' (LB.invGen D.P.L _ _ (v α)))
      (mulGen_isGen _ _ _ _ _ _ _ ht' (invGen_isGen _ _ _ _ (hv α))) (fun U _ h => by
        rw [Fintype.prod_sum_type]
        simp only [Sum.elim_inl, Sum.elim_inr]
        rw [hf U h]
        exact H1.tel_formal p.g.b p.y α hb h)
    refine ⟨a, fun Z r z J hJ => ?_⟩
    rw [← ha Z r z J hJ, val_mul hJ, val_inv, hvt Z r z J hJ]
    exact congrArg Units.val (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => (val_pull hJ _ _ _).symm) rfl)
  choose a ha using hV
  have hz : (DegPre.zF D F).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left, show DegPre.zF D F ≫ fst _ _ = 𝟙 _ from lift_fst _ _]; rfl
  have hconst : ∀ α, a α = 1 := by
    intro α
    refine fn_ext fun z _ => ?_
    choose I hI using fun χ : (TF (R := R) F).left ⟶ D.P.A.left => exists_chart D.P.isLB (χ z)
    have e₁ := ha α _ (DegPre.zF D F).left z I hI
    rw [hz] at e₁
    rw [← e₁, H1.const_at_zero hG p w hw u hu hc v hcv α z I hI, const_one hB hE hk p w hX z I hI,
      gs_eq _ z ⊤ trivial, map_one, map_one, Units.val_one]
  refine DVR.fam_ext fun β j => sec_ext_val D.P.isLB (fun y J hJ => ?_) j
  obtain ⟨α, rfl⟩ : ∃ α, α + k • p.y = β := ⟨β - k • p.y, sub_add_cancel _ _⟩
  have e₁ := H1.iter p w u hu hc ss H k (Nat.lt_succ_self k) α _ (𝟙 _) y J hJ
  have e₂ := (secRel_iff D.P.isLB _ _ _ _ _ _ _ _ _ (v α)).1 ((ss 0).fe p.y α (v α) (hv α) (hcv α)) _ (𝟙 _) y J hJ
  have e₃ := ha α _ (𝟙 _) y J hJ
  rw [hconst α, gs_eq _ y ⊤ trivial, map_one, map_one] at e₃
  rw [e₂, hb]
  refine e₁.trans ?_
  rw [mul_inv_eq_one.1 (Units.ext e₃)]

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (N : ℕ), Odd N → ∀ (p : QkPt D.toPre F N) (w : Frm D.toPre F N p.g.b), TXFrame N p w → ∀ ss : Fin (N + 1) → Fam D.toPre F N, (∀ i : Fin N, PhiRel D.toPre F N p w (ss i.castSucc) (ss i.succ)) → ss (Fin.last N) = ss 0 :=
  fun hL _ _ _ _ _ _ D _ _ _ _ _ hN p w hX ss H =>
    phiPow_eq_one hL.1.globalFns D.tau_bimult D.psi_even hN p w hX ss H

end GlobalTheory.UT.PhiOrder

end
