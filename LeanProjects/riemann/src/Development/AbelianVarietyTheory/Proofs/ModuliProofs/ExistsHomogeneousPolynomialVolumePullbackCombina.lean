import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.SectionsHaveFiniteDimension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EventuallySectionAndRelAmplePowDivStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SectionsGrowthBasicPropertiesAbelianVarietyStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PolarizedAbelianAmpleExistsPositiveVolumeStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHomogeneousVolumeVeryAmpleProductsStatement
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFinAffineCover

namespace GlobalTheory.VolPoly
section Algebra
open Filter Topology MvPolynomial
variable {I κ : Type} [Fintype I] [Fintype κ]

omit [Fintype κ] in
theorem cast_eval (x : κ → ℚ) (Φ : MvPolynomial κ ℚ) :
    ((eval x Φ : ℚ) : ℝ) = eval (fun k => (x k : ℝ)) (map (Rat.castHom ℝ) Φ) := by
  rw [eval_map]
  exact (eval₂_comp_left (Rat.castHom ℝ) (RingHom.id ℚ) x Φ).trans (by rw [RingHom.comp_id]; rfl)

theorem eval_mul_of_isHomogeneous {R : Type} [CommRing R] {Φ : MvPolynomial κ R} {g : ℕ} (h : Φ.IsHomogeneous g)
    (c : R) (x : κ → R) : eval (fun k => c * x k) Φ = c ^ g * eval x Φ := by
  rw [eval_eq', eval_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have e : ∑ k, d k = g := by
    rw [← h (mem_support_iff.1 hd), Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, e]
  ring

theorem poly_eval_aeval {σ : Type} (f : σ → Polynomial ℚ) (t : ℚ) (Ψ : MvPolynomial σ ℚ) :
    (aeval f Ψ).eval t = eval (fun o => (f o).eval t) Ψ := by
  induction Ψ using MvPolynomial.induction_on <;> simp [*]

theorem eval_aeval {σ τ : Type} (f : σ → MvPolynomial τ ℚ) (x : τ → ℚ) (Ψ : MvPolynomial σ ℚ) :
    eval x (aeval f Ψ) = eval (fun o => eval x (f o)) Ψ := by
  induction Ψ using MvPolynomial.induction_on <;> simp [*, -aeval_eq_bind₁]

omit [Fintype κ] in
theorem eval_shift (Ψ : MvPolynomial (Option κ) ℚ) (Φ : MvPolynomial κ ℚ) (b : ℚ) (m : κ → ℚ)
    (h : ∀ᶠ t : ℕ in atTop, eval (fun o => Option.elim o b fun _ => (t : ℚ)) Ψ = eval (fun k => m k + t) Φ) :
    eval (fun o => Option.elim o b fun _ => (1 : ℚ)) Ψ = eval (fun k => m k + 1) Φ := by
  let p : Polynomial ℚ := aeval (fun o => Option.elim o (Polynomial.C b) fun _ => Polynomial.X) Ψ
  let q : Polynomial ℚ := aeval (fun k => Polynomial.C (m k) + Polynomial.X) Φ
  have hp : ∀ t : ℚ, p.eval t = eval (fun o => Option.elim o b fun _ => t) Ψ := fun t => by
    rw [poly_eval_aeval]
    refine congrArg (fun x => eval x Ψ) (funext ?_)
    rintro (_ | k) <;> simp
  have hq : ∀ t : ℚ, q.eval t = eval (fun k => m k + t) Φ := fun t => by
    rw [poly_eval_aeval]
    simp
  have : p = q := by
    refine Polynomial.eq_of_infinite_eval_eq _ _ ?_
    obtain ⟨T, hT⟩ := eventually_atTop.1 h
    refine Set.infinite_of_injective_forall_mem (f := fun n : ℕ => ((n + T : ℕ) : ℚ))
      (fun a b hab => by simpa using hab) fun n => ?_
    show p.eval _ = q.eval _
    rw [hp, hq]
    exact hT _ (Nat.le_add_left _ _)
  rw [← hp, ← hq, this]

theorem squeeze {Φ : MvPolynomial κ ℝ} {g : ℕ} (hΦ : Φ.IsHomogeneous g) (m : κ → ℝ) (N c δ : ℝ) (d : ℕ) (hd : 1 ≤ d)
    (h : ∀ᶠ a : ℕ in atTop, (a * d * N - c) ^ g * δ ≤ eval (fun k => a * d * m k + 1) Φ ∧
      eval (fun k => a * d * m k + 1) Φ ≤ (a * d * N + c) ^ g * δ) : eval m Φ = N ^ g * δ := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have ht : Tendsto (fun a : ℕ => ((a : ℝ) * d)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.atTop_mul_const hd').inv_tendsto_atTop
  have t₀ : Tendsto (fun a : ℕ => eval (fun k => m k + ((a : ℝ) * d)⁻¹) Φ) atTop (𝓝 (eval m Φ)) :=
    ((MvPolynomial.continuous_eval Φ).tendsto m).comp (tendsto_pi_nhds.2 fun k => by simpa using ht.const_add (m k))
  have t₁ : ∀ c : ℝ, Tendsto (fun a : ℕ => (N + c * ((a : ℝ) * d)⁻¹) ^ g * δ) atTop (𝓝 (N ^ g * δ)) := fun c => by
    simpa using (((ht.const_mul c).const_add N).pow g).mul_const δ
  have key : ∀ᶠ a : ℕ in atTop, (N + -c * ((a : ℝ) * d)⁻¹) ^ g * δ ≤ eval (fun k => m k + ((a : ℝ) * d)⁻¹) Φ ∧
      eval (fun k => m k + ((a : ℝ) * d)⁻¹) Φ ≤ (N + c * ((a : ℝ) * d)⁻¹) ^ g * δ := by
    filter_upwards [h, eventually_ge_atTop 1] with a ha ha₁
    have hs : (0 : ℝ) < (a : ℝ) * d := mul_pos (by exact_mod_cast ha₁) hd'
    generalize (a : ℝ) * d = s at ha hs ⊢
    have e₀ : (fun k => s * m k + 1) = fun k => s * (m k + s⁻¹) := funext fun k => by field_simp
    have e₁ : s * N - c = s * (N + -c * s⁻¹) := by field_simp; ring
    have e₂ : s * N + c = s * (N + c * s⁻¹) := by field_simp
    rw [e₀, e₁, e₂, eval_mul_of_isHomogeneous hΦ, mul_pow, mul_pow, mul_assoc, mul_assoc] at ha
    exact ⟨le_of_mul_le_mul_left ha.1 (pow_pos hs g), le_of_mul_le_mul_left ha.2 (pow_pos hs g)⟩
  exact le_antisymm (le_of_tendsto_of_tendsto t₀ (t₁ c) (key.mono fun _ h => h.2))
    (le_of_tendsto_of_tendsto (t₁ (-c)) t₀ (key.mono fun _ h => h.1))

variable {g : ℕ} {V : (I → ℤ) → ℝ → Prop} {Am VA Eff : (I → ℤ) → Prop}

omit [Fintype I] in

theorem eval_eq_of_ample
    (dom : ∀ x y, Am x → ∀ᶠ t : ℕ in atTop, Eff (t • x - y) ∧ Am (t • x - y))
    (va : ∀ x, Am x → ∃ d : ℕ, 1 ≤ d ∧ VA (d • x))
    (uniq : ∀ x δ δ', V x δ → V x δ' → δ = δ')
    (mono : ∀ x x' δ δ', Eff (x' - x) → V x δ → V x' δ' → δ ≤ δ')
    (pow : ∀ x δ (a : ℕ), 1 ≤ a → V x δ → V (a • x) ((a : ℝ) ^ g * δ))
    (poly : ∀ η : Option κ → I → ℤ, (∀ k, VA (η k)) → ∃ Φ : MvPolynomial (Option κ) ℚ,
      ∀ n : Option κ → ℕ, (∀ k, 1 ≤ n k) → V (∑ k, (n k : ℤ) • η k) ((eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ))
    {η : κ → I → ℤ} (hη : ∀ k, VA (η k)) {Φ : MvPolynomial κ ℚ} (hΦ : Φ.IsHomogeneous g)
    (hV : ∀ n : κ → ℕ, (∀ k, 1 ≤ n k) → V (∑ k, (n k : ℤ) • η k) ((eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ))
    {ε : I → ℤ} (hε : Am ε) {δ : ℝ} (hδ : V ε δ) {N : ℕ} (hN : 1 ≤ N) {m : κ → ℤ}
    (hm : N • ε = ∑ k, m k • η k) : ((eval (fun k => (m k : ℚ)) Φ : ℚ) : ℝ) = (N : ℝ) ^ g * δ := by
  obtain ⟨d, hd, hva⟩ := va ε hε
  obtain ⟨Ψ, hΨ⟩ := poly (fun o => Option.elim o (d • ε) η) (by rintro (_ | k); exacts [hva, hη k])
  have hΨ' : ∀ a t : ℕ, 1 ≤ a → 1 ≤ t → V ((a * d * N) • ε + t • ∑ k, η k)
      ((eval (fun o => Option.elim o ((a * N : ℕ) : ℚ) fun _ => (t : ℚ)) Ψ : ℚ) : ℝ) := fun a t ha ht => by
    have := hΨ (fun o => Option.elim o (a * N) fun _ => t) (by rintro (_ | k); exacts [Nat.mul_pos ha hN, ht])
    convert this using 1
    · rw [Fintype.sum_option, Finset.smul_sum]
      simp only [Option.elim, natCast_zsmul, smul_smul]
      rw [mul_right_comm]
    · refine congrArg (fun x => ((eval x Ψ : ℚ) : ℝ)) (funext ?_)
      rintro (_ | k) <;> rfl
  have hsh : ∀ a : ℕ, 1 ≤ a → V ((a * d * N) • ε + ∑ k, η k)
      ((eval (fun k => ((a * d * m k : ℤ) : ℚ) + 1) Φ : ℚ) : ℝ) := fun a ha => by
    have h₁ := hΨ' a 1 ha le_rfl
    rw [one_smul, Nat.cast_one, eval_shift Ψ Φ _ (fun k => ((a * d * m k : ℤ) : ℚ))] at h₁
    · exact h₁
    have ev : ∀ᶠ t : ℕ in atTop, ∀ k, 1 ≤ a * d * m k + (t : ℤ) := eventually_all.2 fun k =>
      (tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
    filter_upwards [ev, eventually_ge_atTop 1] with t ht ht₁
    have hn : ∀ k, (((a * d * m k + (t : ℤ)).toNat : ℕ) : ℤ) = a * d * m k + t := fun k =>
      Int.toNat_of_nonneg (zero_le_one.trans (ht k))
    have h₂ := hV (fun k => (a * d * m k + (t : ℤ)).toNat) fun k => by have := hn k; have := ht k; omega
    have e₁ : ∑ k, (((a * d * m k + (t : ℤ)).toNat : ℕ) : ℤ) • η k = (a * d * N) • ε + t • ∑ k, η k := by
      rw [mul_smul, hm, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hn, add_smul, natCast_zsmul, ← natCast_zsmul (m k • η k), smul_smul, Nat.cast_mul]
    have e₂ : (fun k => (((a * d * m k + (t : ℤ)).toNat : ℕ) : ℚ)) = fun k => ((a * d * m k : ℤ) : ℚ) + t :=
      funext fun k => by exact_mod_cast congrArg (Int.cast : ℤ → ℚ) (hn k)
    rw [e₁, e₂] at h₂
    exact_mod_cast uniq _ _ _ (hΨ' a t ha ht₁) h₂
  obtain ⟨c, ⟨hc₁, -⟩, hc₂, -⟩ := ((dom ε (∑ k, η k) hε).and (dom ε (-∑ k, η k) hε)).exists
  rw [cast_eval]
  refine squeeze (hΦ.map _) _ N c δ d hd ?_
  filter_upwards [eventually_ge_atTop (c + 1)] with a ha
  have ha₁ : 1 ≤ a := by omega
  have hle : a ≤ a * d * N := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_pos hd hN)
  obtain ⟨u, hu⟩ : ∃ u, a * d * N = u + c := ⟨a * d * N - c, by omega⟩
  have h₀ := hsh a ha₁
  rw [cast_eval] at h₀
  push_cast at h₀ ⊢
  have hu' : (a : ℝ) * d * N - c = u := by
    have : ((a * d * N : ℕ) : ℝ) = ((u + c : ℕ) : ℝ) := by rw [hu]
    push_cast at this; linarith
  constructor
  · rw [hu']
    refine mono _ _ _ _ ?_ (pow ε δ u (by omega) hδ) h₀
    convert hc₂ using 1
    rw [hu, add_smul]; abel
  · have := mono _ _ _ _ ?_ h₀ (pow ε δ (a * d * N + c) (by omega) hδ)
    · push_cast at this; exact this
    convert hc₁ using 1
    rw [add_smul]; abel

theorem exists_poly
    (dom : ∀ x y, Am x → ∀ᶠ t : ℕ in atTop, Eff (t • x - y) ∧ Am (t • x - y))
    (va : ∀ x, Am x → ∃ d : ℕ, 1 ≤ d ∧ VA (d • x))
    (uniq : ∀ x δ δ', V x δ → V x δ' → δ = δ')
    (mono : ∀ x x' δ δ', Eff (x' - x) → V x δ → V x' δ' → δ ≤ δ')
    (pow : ∀ x δ (a : ℕ), 1 ≤ a → V x δ → V (a • x) ((a : ℝ) ^ g * δ))
    (ex : ∀ x, Am x → ∃ δ, V x δ)
    (poly : ∀ (κ : Type) [Fintype κ] (η : Option κ → I → ℤ), (∀ k, VA (η k)) →
      ∃ Φ : MvPolynomial (Option κ) ℚ, Φ.IsHomogeneous g ∧
      ∀ n : Option κ → ℕ, (∀ k, 1 ≤ n k) → V (∑ k, (n k : ℤ) • η k) ((eval (fun k => (n k : ℚ)) Φ : ℚ) : ℝ)) :
    ∃ Φ : MvPolynomial I ℚ, Φ.IsHomogeneous g ∧ ∀ ε, Am ε → V ε ((eval (fun i => (ε i : ℚ)) Φ : ℚ) : ℝ) := by
  classical
  by_cases h : ∃ ε₀, Am ε₀
  swap
  · exact ⟨0, isHomogeneous_zero _ _ _, fun ε hε => (h ⟨ε, hε⟩).elim⟩
  obtain ⟨ε₀, h₀⟩ := h
  obtain ⟨d₀, hd₀, hv₀⟩ := va ε₀ h₀
  choose t ht using fun i : I => (dom ε₀ (-Pi.single i 1) h₀).exists
  choose d hd hv using fun i : I => va _ (ht i).2
  let η : Option I → I → ℤ := fun o => Option.elim o (d₀ • ε₀) fun i => d i • (t i • ε₀ - -Pi.single i 1)
  have hη : ∀ o, VA (η o) := by rintro (_ | i); exacts [hv₀, hv i]
  obtain ⟨Φ, hΦ, hV⟩ := poly I η hη
  let y : Option I → MvPolynomial I ℚ := fun o =>
    Option.elim o (∑ i, C (-(t i : ℚ) / d₀) * X i) fun i => C (1 / (d i : ℚ)) * X i
  have hy : ∀ o, (y o).IsHomogeneous 1 := by
    rintro (_ | i)
    · exact IsHomogeneous.sum _ _ _ fun i _ => (isHomogeneous_X _ _).C_mul _
    · exact (isHomogeneous_X _ _).C_mul _
  refine ⟨aeval y Φ, by simpa using hΦ.aeval y hy, fun ε hε => ?_⟩
  obtain ⟨δ, hδ⟩ := ex ε hε
  have hdv : ∀ i, ∃ e : ℕ, ∏ j, d j = d i * e := fun i => Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  choose e he using hdv
  have hD : 1 ≤ ∏ j, d j := Nat.succ_le_of_lt (Finset.prod_pos fun j _ => hd j)
  generalize ∏ j, d j = D at he hD
  let m : Option I → ℤ := fun o => Option.elim o (-(D * ∑ i, t i * ε i)) fun i => d₀ * e i * ε i
  have hN : 1 ≤ d₀ * D := Nat.mul_pos hd₀ hD
  have hm : (d₀ * D) • ε = ∑ o, m o • η o := by
    rw [Fintype.sum_option]
    funext j
    have s : ∀ i, (m (some i) • η (some i)) j =
        d₀ * D * ε₀ j * (t i * ε i) + (if j = i then (d₀ * D * ε i : ℤ) else 0) := fun i => by
      have he' : (D : ℤ) = d i * e i := by exact_mod_cast he i
      simp only [m, η, Option.elim, Pi.smul_apply, sub_neg_eq_add, Pi.add_apply, Pi.single_apply, smul_eq_mul,
        nsmul_eq_mul, he', Pi.mul_apply, Pi.natCast_apply]
      split_ifs <;> ring
    rw [Pi.add_apply, Finset.sum_apply, Finset.sum_congr rfl fun i _ => s i, Finset.sum_add_distrib,
      ← Finset.mul_sum, Finset.sum_ite_eq, if_pos (Finset.mem_univ _)]
    simp only [m, η, Option.elim, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply]
    push_cast
    ring
  have key := eval_eq_of_ample dom va uniq mono pow
    (fun η' h' => (poly (Option I) η' h').imp fun _ h => h.2) hη hΦ hV hε hδ hN hm
  have e₁ : (fun o => (m o : ℚ)) = fun o => ((d₀ * D : ℕ) : ℚ) * eval (fun i => (ε i : ℚ)) (y o) := by
    have n₀ : (d₀ : ℚ) ≠ 0 := by exact_mod_cast (by omega : d₀ ≠ 0)
    funext o
    rcases o with _ | i
    · simp only [m, y, Option.elim, map_sum, map_mul, eval_C, eval_X]
      push_cast
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by field_simp
    · have n₁ : (d i : ℚ) ≠ 0 := by exact_mod_cast (by have := hd i; omega : d i ≠ 0)
      simp only [m, y, Option.elim, map_mul, eval_C, eval_X, he i]
      push_cast
      field_simp
  rw [e₁, eval_mul_of_isHomogeneous hΦ, ← eval_aeval, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast] at key
  have hpos : (0 : ℝ) < ((d₀ * D : ℕ) : ℝ) ^ g := pow_pos (by exact_mod_cast hN) g
  rwa [mul_left_cancel₀ hpos.ne' key]

end Algebra

section Geometry
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZV GlobalTheory.CechPic

variable {X : Scheme.{0}} {L : LB X} {I : Type} [Fintype I]

theorem lbIso_pow (hL : L.IsLB) (φ : I → (X ⟶ X)) (x : I → ℤ) (a : ℕ) :
    LBIso (lbPow (LB.LinComb L φ x) a) (LB.LinComb L φ (a • x)) := by
  have h := LB.isLB_linComb hL φ
  refine (cls_eq_iff (LB.isLB_linComb (h x) _ _) (h _)).1 ?_
  rw [cls_lbPow (h x), cls_linComb hL, cls_linComb hL, Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.smul_apply, smul_assoc]

theorem lbIso_div (hL : L.IsLB) (φ : I → (X ⟶ X)) (x y : I → ℤ) :
    LBIso (LB.div (LB.LinComb L φ x) (LB.LinComb L φ y)) (LB.LinComb L φ (x - y)) := by
  have h := LB.isLB_linComb hL φ
  refine (cls_eq_iff (LB.isLB_div (h x) (h y)) (h _)).1 ?_
  rw [cls_div (h x) (h y), cls_linComb hL, cls_linComb hL, cls_linComb hL, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by rw [Pi.sub_apply, sub_smul]

theorem lbIso_div_pow (hL : L.IsLB) (φ : I → (X ⟶ X)) (x y : I → ℤ) (a : ℕ) :
    LBIso (LB.div (lbPow (LB.LinComb L φ x) a) (LB.LinComb L φ y)) (LB.LinComb L φ (a • x - y)) := by
  have h := LB.isLB_linComb hL φ
  have hp : (lbPow (LB.LinComb L φ x) a).IsLB := LB.isLB_linComb (h x) _ _
  refine (cls_eq_iff (LB.isLB_div hp (h y)) (h _)).1 ?_
  rw [cls_div hp (h y), (cls_eq_iff hp (h _)).2 (lbIso_pow hL φ x a), ← cls_div (h _) (h y) (LB.isLB_div (h _) (h y))]
  exact (cls_eq_iff _ _).2 (lbIso_div hL φ _ _)

theorem vAmp_of_veryAmpleBy {K : Type} [Field K] {p : X ⟶ Sp K} {m : ℕ} {s : Fin (m + 1) → L.Sec}
    (h : AbLaw.VeryAmpleBy p L s) : VAmp p L s := by
  refine ⟨h.1, fun i => ⟨(h.2 i).1, ?_⟩⟩
  obtain ⟨r, hr, hs⟩ := (h.2 i).2
  refine ⟨r, hr, fun f => ?_⟩
  obtain ⟨F, hF⟩ := hs f
  exact ⟨F, hF.symm⟩

theorem exists_vol_linComb_poly : Out.Laws → Out.Laws2 → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (I : Type) [Fintype I] (φ : I → (P.A.left ⟶ P.A.left)), ∃ Φ : MvPolynomial I ℚ, Φ.IsHomogeneous P.g ∧ ∀ ε : I → ℤ, Out.RelAmple P.A (LB.LinComb P.L φ ε) → Vol P.A.hom (LB.LinComb P.L φ ε) P.g ((MvPolynomial.eval (fun i => (ε i : ℚ)) Φ : ℚ) : ℝ) := by
  intro h₁ h₂ K _ _ P I _ φ
  have := P.isAb.proper
  have h := LB.isLB_linComb P.isLB φ
  have vb := fun x => GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P (LB.LinComb P.L φ x) P.g (h x)
  refine exists_poly (V := fun x δ => Vol P.A.hom (LB.LinComb P.L φ x) P.g δ)
    (Am := fun x => Out.RelAmple P.A (LB.LinComb P.L φ x))
    (VA := fun x => ∃ (m : ℕ) (th : Fin (m + 1) → (LB.LinComb P.L φ x).Sec), VAmp P.A.hom _ th)
    (Eff := fun x => Nontrivial (LB.LinComb P.L φ x).Sec)
    (fun x y hx => ?_) (fun x hx => ?_) (fun x => (vb x).2.1) (fun x x' δ δ' he => ?_) (fun x δ a ha hδ => ?_)
    (fun x hx => (GlobalTheory.T.polarizedAbelian_ample_exists_positive_volume h₁ h₂ K P _ (h x) hx).imp fun _ h => h.2) (fun κ _ w hw => ?_)
  · filter_upwards [GlobalTheory.T.eventually_section_and_relAmple_pow_div K P _ _ (h x) (h y) hx] with t ht
    have hl : (LB.div (lbPow (LB.LinComb P.L φ x) t) (LB.LinComb P.L φ y)).IsLB :=
      LB.isLB_div (LB.isLB_linComb (h x) _ _) (h y)
    have iso := lbIso_div_pow P.isLB φ x y t
    exact ⟨PrimVan.nontrivial_sec_of_lbIso hl (h _) iso ((TrivLocus.nontrivial_sec_iff _).2 ht.1),
      (relAmple_iff_isAmpleLB_of_isAffine P.A (h _)).2 ((isAmpleLB_congr hl (h _) iso).1
        ((relAmple_iff_isAmpleLB_of_isAffine P.A hl).1 ht.2))⟩
  · obtain ⟨d, hd, m, s, hs⟩ := ((relAmple_iff_isAmpleLB_of_isAffine P.A (h _)).1 hx).exists_veryAmpleBy P.A.hom
    obtain ⟨t, ht⟩ := exists_veryAmpleBy_of_lbIso (LB.isLB_linComb (h x) _ _) (h _) (lbIso_pow P.isLB φ x d) hs
    exact ⟨d, hd, m, t, vAmp_of_veryAmpleBy ht⟩
  · obtain ⟨s, hs⟩ := (TrivLocus.nontrivial_sec_iff _).1 (PrimVan.nontrivial_sec_of_lbIso (h _)
      (LB.isLB_div (h x') (h x)) (lbIso_div P.isLB φ x' x).symm he)
    exact ((vb x).2.2.2.2.2 _ s (h x') hs).2 δ δ'
  · exact (GlobalTheory.T.sectionsGrowth_basic_properties_abelianVariety K P _ P.g (LB.isLB_linComb (h x) _ _)).2.2.1 _ _ (h _) (lbIso_pow P.isLB φ x a)
      ((vb x).2.2.2.1 a δ ha hδ)
  · let e := (Fintype.equivFin (Option κ)).symm
    obtain ⟨Φ, hΦ, hV⟩ := GlobalTheory.T.exists_homogeneous_volume_veryAmple_products h₁ h₂ K P I φ _ (fun k => w (e k)) Fintype.card_pos fun k => hw (e k)
    refine ⟨MvPolynomial.rename e Φ, hΦ.rename_isHomogeneous, fun n hn => ?_⟩
    have := hV (fun k => n (e k)) fun k => hn (e k)
    have e₁ : ∑ k, (n k : ℤ) • w k = fun i => ∑ k, (n (e k) : ℤ) * w (e k) i := by
      funext i
      rw [Finset.sum_apply]
      exact (e.sum_comp fun k => (n k : ℤ) * w k i).symm
    rw [e₁, MvPolynomial.eval_rename]
    exact this

end Geometry
end GlobalTheory.VolPoly
