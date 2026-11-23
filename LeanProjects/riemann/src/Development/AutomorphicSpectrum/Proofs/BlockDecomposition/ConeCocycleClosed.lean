import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.ConeSectionRestriction.Precomp
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TruncatedLogMultiplicativeStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConeLiftRatioMemIdealStatement
set_option backward.isDefEq.respectTransparency false
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb
open GlobalTheory.CatH (face toLast)

namespace GlobalTheory.CompanionTheory.ConeZcoc

theorem plogK_map {B B' : Type} [CommRing B] [CommRing B'] {J : Ideal B} {J' : Ideal B'}
    {δ : DividedPowers J} {δ' : DividedPowers J'} {f : B →+* B'} (hf : IsDPMorphism δ δ' f) (s : ℕ)
    {x : B} (hx : x ∈ J) : f (plogK δ s x) = plogK δ' s (f x) := by
  unfold plogK
  rw [map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, map_mul, map_pow, map_neg, map_one, map_natCast, ← hf.2 x hx]

theorem units_cancel {G : Type} [CommGroup G] (a b c d e f : G) :
    (a * b * c⁻¹) * (c * d * e⁻¹) = (b * d * f⁻¹) * (a * f * e⁻¹) := by
  have h1 : (a * b * c⁻¹) * (c * d * e⁻¹) = a * b * d * e⁻¹ := by
    simp only [mul_assoc, inv_mul_cancel_left]
  have h2 : (b * d * f⁻¹) * (a * f * e⁻¹) = (a * b * d) * e⁻¹ * (f⁻¹ * f) := by
    simp only [mul_assoc, mul_left_comm, mul_comm]
  rw [h1, h2, inv_mul_cancel, mul_one]

theorem plogK_four {B : Type} [CommRing B] {J : Ideal B} (δ : DividedPowers J) (s : ℕ) (hs : pdP δ s = ⊥)
    (hu : ∀ n : ℕ, n ≠ 0 → IsUnit (n : B)) {a b c d : B} (ha : a - 1 ∈ J) (hb : b - 1 ∈ J) (hc : c - 1 ∈ J)
    (hd : d - 1 ∈ J) (h : a * b = c * d) :
    plogK δ s (a - 1) + plogK δ s (b - 1) = plogK δ s (c - 1) + plogK δ s (d - 1) := by
  rw [← GlobalTheory.T.truncated_log_multiplicative δ s hs hu ha hb, ← GlobalTheory.T.truncated_log_multiplicative δ s hs hu hc hd]
  simp only [add_sub_cancel]
  rw [h]

theorem add_eq {B : Type} [CommRing B] {a c d b a' c' d' b' : B} (h₁ : a = a') (h₂ : c = c') (h₃ : d = d')
    (h₄ : b = b') (h : a' + c' = d' + b') : a + c = d + b := by
  rw [h₁, h₂, h₃, h₄, h]

variable {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}
  {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X}

def rr (Λ : CLiftK g D) {a b c : C} (φ : a ⟶ b) (ψ : b ⟶ c) (χ : a ⟶ c) : (g.obj c).Bˣ :=
  Units.map (g.map ψ).φ.toMonoidHom (Λ.w φ) * Λ.w ψ * (Λ.w χ)⁻¹

theorem r_eq (Λ : CLiftK g D) (σ : ComposableArrows C 2) :
    Λ.r σ = rr Λ (σ.map' 0 1) (σ.map' 1 2) (σ.map' 0 2) := rfl

theorem rr_coboundary (Λ : CLiftK g D) {c₀ c₁ c₂ c₃ : C} (f₀₁ : c₀ ⟶ c₁) (f₁₂ : c₁ ⟶ c₂) (f₂₃ : c₂ ⟶ c₃)
    (f₀₂ : c₀ ⟶ c₂) (f₁₃ : c₁ ⟶ c₃) (f₀₃ : c₀ ⟶ c₃) (h₀₂ : f₀₂ = f₀₁ ≫ f₁₂) (h₁₃ : f₁₃ = f₁₂ ≫ f₂₃) :
    Units.map (g.map f₂₃).φ.toMonoidHom (rr Λ f₀₁ f₁₂ f₀₂) * rr Λ f₀₂ f₂₃ f₀₃ =
      rr Λ f₁₂ f₂₃ f₁₃ * rr Λ f₀₁ f₁₃ f₀₃ := by
  subst h₀₂ h₁₃
  have e : Units.map (g.map (f₁₂ ≫ f₂₃)).φ.toMonoidHom (Λ.w f₀₁) =
      Units.map (g.map f₂₃).φ.toMonoidHom (Units.map (g.map f₁₂).φ.toMonoidHom (Λ.w f₀₁)) := by
    rw [g.map_comp]; rfl
  unfold rr
  rw [e, map_mul, map_mul, map_inv]
  exact units_cancel _ _ _ _ _ _

theorem map_zK (Λ : CLiftK g D) (s : ℕ) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    (show (g.obj c).B from ((g ⋙ O (smFun X q)).map ρ).hom (zK Λ s σ)) =
      plogK (g.obj c).δ s (((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1) := by
  change (g.map ρ).φ (plogK (g.obj (σ.obj (Fin.last 2))).δ s ((Λ.r σ : (g.obj (σ.obj (Fin.last 2))).B) - 1)) = _
  rw [plogK_map (g.map ρ).dp s (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ), map_sub, map_one]
  rfl

theorem mem_J (Λ : CLiftK g D) (σ : ComposableArrows C 2) {c : C} (ρ : σ.obj (Fin.last 2) ⟶ c) :
    ((Units.map (g.map ρ).φ.toMonoidHom (Λ.r σ) : (g.obj c).Bˣ) : (g.obj c).B) - 1 ∈ (g.obj c).J := by
  have := (g.map ρ).hle (GlobalTheory.T.cone_lift_ratio_mem_ideal Λ σ)
  rw [Ideal.mem_comap, map_sub, map_one] at this
  exact this

theorem map_id_unit {c : C} (ρ : c ⟶ c) (h : ρ = 𝟙 c) (u : (g.obj c).Bˣ) :
    Units.map (g.map ρ).φ.toMonoidHom u = u := by
  subst h
  rw [g.map_id]
  ext; rfl

theorem nat_isUnit (T : Thick (smFun X q)) (n : ℕ) (hn : n ≠ 0) : IsUnit (n : T.B) := by
  have h : IsUnit (n : K) := (Nat.cast_ne_zero.2 hn).isUnit
  have := h.map T.i
  rwa [map_natCast] at this

theorem main : ∀ {K : Type} [Field K] [CharZero K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)} {C : Type 1} [Category.{0} C] {g : C ⥤ Thick (smFun X q)} {D : E.LineData X} (Λ : CLiftK g D) (s : ℕ), (∀ c, (g.obj c).pdPow s = ⊥) → CH.d _ 2 (zK Λ s) = 0 := by
  intro K _ _ X q C _ g D Λ s hs
  funext τ
  change ∑ i : Fin 4, (-1 : ℤ) ^ (i : ℕ) • ((g ⋙ O (smFun X q)).map (toLast i τ)).hom (zK Λ s (face i τ)) = 0
  rw [Fin.sum_univ_four]
  have h0 := map_zK Λ s (face 0 τ) (toLast 0 τ)
  have h1 := map_zK Λ s (face 1 τ) (toLast 1 τ)
  have h2 := map_zK Λ s (face 2 τ) (toLast 2 τ)
  have h3 := map_zK Λ s (face 3 τ) (toLast 3 τ)
  have m0 := mem_J Λ (face 0 τ) (toLast 0 τ)
  have m1 := mem_J Λ (face 1 τ) (toLast 1 τ)
  have m2 := mem_J Λ (face 2 τ) (toLast 2 τ)
  have m3 := mem_J Λ (face 3 τ) (toLast 3 τ)
  have e0 : Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) = Λ.r (face 0 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 0 τ) (τ.map_id _) _
  have e1 : Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) = Λ.r (face 1 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 1 τ) (τ.map_id _) _
  have e2 : Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) = Λ.r (face 2 τ) :=
    map_id_unit (g := g) (c := τ.obj (Fin.last 3)) (toLast 2 τ) (τ.map_id _) _
  have key : Units.map (g.map (toLast 3 τ)).φ.toMonoidHom (Λ.r (face 3 τ)) *
      Units.map (g.map (toLast 1 τ)).φ.toMonoidHom (Λ.r (face 1 τ)) =
      Units.map (g.map (toLast 0 τ)).φ.toMonoidHom (Λ.r (face 0 τ)) *
      Units.map (g.map (toLast 2 τ)).φ.toMonoidHom (Λ.r (face 2 τ)) := by
    rw [e0, e1, e2]
    exact rr_coboundary Λ (τ.map' 0 1) (τ.map' 1 2) (τ.map' 2 3) (τ.map' 0 2) (τ.map' 1 3) (τ.map' 0 3)
      (τ.map'_comp 0 1 2) (τ.map'_comp 1 2 3)
  have hval := congrArg (Units.val) key
  rw [Units.val_mul, Units.val_mul] at hval
  have p := plogK_four (g.obj (τ.obj (Fin.last 3))).δ s (hs _) (nat_isUnit (g.obj (τ.obj (Fin.last 3)))) m3 m1 m0 m2 hval
  have fin : ∀ a b c d : (g ⋙ O (smFun X q)).obj (τ.obj (Fin.last 3)), a + c = d + b →
      (-1 : ℤ) ^ ((0 : Fin 4) : ℕ) • a + (-1 : ℤ) ^ ((1 : Fin 4) : ℕ) • b + (-1 : ℤ) ^ ((2 : Fin 4) : ℕ) • c +
        (-1 : ℤ) ^ ((3 : Fin 4) : ℕ) • d = 0 := by
    intro a b c d h
    have e3 : ((3 : Fin 4) : ℕ) = 3 := rfl
    have e2 : ((2 : Fin 4) : ℕ) = 2 := rfl
    have e1 : ((1 : Fin 4) : ℕ) = 1 := rfl
    have e0 : ((0 : Fin 4) : ℕ) = 0 := rfl
    rw [e0, e1, e2, e3]
    have : (-1 : ℤ) ^ 3 = -1 := by norm_num
    rw [this, pow_zero, pow_one, show (-1 : ℤ) ^ 2 = 1 by norm_num, one_smul, one_smul, neg_one_smul, neg_one_smul]
    calc a + -b + c + -d = (a + c) - (d + b) := by abel
      _ = 0 := by rw [h, sub_self]
  refine fin _ _ _ _ ?_
  exact add_eq (B := (g.obj (τ.obj (Fin.last 3))).B) h0 h2 h3 h1 p.symm

end GlobalTheory.CompanionTheory.ConeZcoc
