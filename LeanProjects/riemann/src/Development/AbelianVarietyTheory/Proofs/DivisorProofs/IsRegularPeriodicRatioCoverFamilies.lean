import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationPreimageValueRulesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfValEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicHolomorphicSectionsRegularAbelianVarietyStatement
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechDR GlobalTheory.CechPer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechPer

theorem isUnit_res_of_le_basicOpen {X : Scheme.{0}} {U V : X.Opens} (f : Γ(X, U)) (hVU : V ≤ U)
    (h : V ≤ X.basicOpen f) : IsUnit ((X.presheaf.map (homOfLE hVU).op).hom f) := by
  have hu := (X.toRingedSpace.isUnit_res_basicOpen f).map (X.presheaf.map (homOfLE h).op).hom
  have e : X.presheaf.map (homOfLE hVU).op =
      X.presheaf.map (homOfLE (X.basicOpen_le f)).op ≫ X.presheaf.map (homOfLE h).op := by
    rw [← Functor.map_comp]; rfl
  rw [e]
  exact hu

theorem ratio_periodic_isReg : ∀ (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (L : LB A.left) (u : HolUnif A L g), IsAbelianScheme A → ∀ (n : ℕ) (W : Fin n → A.left.Opens) (r : ∀ k, Fin n → Γ(A.left, W k)), IsRatioCover u.ex W r → ∀ (N : ℕ) (σ : Fin n → (Fin g → ℂ) → ℂ), (∀ k, DifferentiableOn ℂ (σ k) (pre u.ex (W k))) → (∀ k (l : u.Λ), ∀ z ∈ pre u.ex (W k), σ k (z + l) = σ k z) → (∀ k j, ∀ z ∈ pre u.ex (W k), z ∈ pre u.ex (W j) → σ k z = val u.ex _ (r k j) z ^ N * σ j z) → ∀ k, IsReg u.ex (W k) (σ k) := by
  intro A _ g L u hA n W r hR N σ hhol hper htr
  obtain ⟨-, -, -, -, hinf, hmono, -, -, hres, hev, -, -⟩ := GlobalTheory.T.uniformisation_preimage_value_rules A g L u
  obtain ⟨-, hcov, hbasic, hself, hcoc⟩ := hR
  have hv : ∀ (U V : A.left.Opens) (h : V ≤ U) (b : Γ(A.left, U)), ∀ z ∈ pre u.ex V,
      val u.ex V ((A.left.presheaf.map (homOfLE h).op).hom b) z = val u.ex U b z :=
    fun U V h b z hz => hres U V h b z hz
  have hmul : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a * b) z = val u.ex U a z * val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_mul e (a : Sec (str A) U) b
  have hsub : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ a b : Γ(A.left, U),
      val u.ex U (a - b) z = val u.ex U a z - val u.ex U b z := by
    intro U z hz a b
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he, he]; exact map_sub e (a : Sec (str A) U) b
  have hpow : ∀ (U : A.left.Opens), ∀ z ∈ pre u.ex U, ∀ (a : Γ(A.left, U)) (m : ℕ),
      val u.ex U (a ^ m) z = val u.ex U a z ^ m := by
    intro U z hz a m
    obtain ⟨e, he⟩ := hev U z hz
    rw [he, he]; exact map_pow e (a : Sec (str A) U) m
  have hunit : ∀ k j, IsUnit ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) :=
    fun k j => isUnit_res_of_le_basicOpen _ _ (hbasic k j).ge
  let M : LB A.left := ⟨Fin n, W, fun k j => (hunit k j).unit ^ N⟩
  have hMg : ∀ k j, ((M.g k j : Γ(A.left, W k ⊓ W j))) =
      ((A.left.presheaf.map (homOfLE (inf_le_left : W k ⊓ W j ≤ W k)).op).hom (r k j)) ^ N := by
    intro k j
    change (((hunit k j).unit ^ N : Γ(A.left, W k ⊓ W j)ˣ) : Γ(A.left, W k ⊓ W j)) = _
    rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec]

  have hval : ∀ k j (V : A.left.Opens) (h : V ≤ W k ⊓ W j), ∀ z ∈ pre u.ex V,
      val u.ex V ((res h (M.g k j) : Γ(A.left, V))) z = val u.ex (W k) (r k j) z ^ N := by
    intro k j V h z hz
    have hz' : z ∈ pre u.ex (W k ⊓ W j) := hmono _ _ h hz
    have e1 : ((res h (M.g k j) : Γ(A.left, V))) =
        (A.left.presheaf.map (homOfLE h).op).hom (M.g k j : Γ(A.left, W k ⊓ W j)) := rfl
    rw [e1, hv _ _ h _ z hz, hMg, hpow _ z hz', hv _ _ _ _ z hz']
  have hM : M.IsLB := by
    refine ⟨hcov, fun k => ?_, fun k j l => ?_⟩
    · apply Units.ext
      change (A.left.presheaf.map _).hom (M.g k k : Γ(A.left, W k ⊓ W k)) = 1
      rw [hMg, hself k, map_one, one_pow, map_one]
    · apply Units.ext
      rw [Units.val_mul]
      apply sub_eq_zero.mp
      apply GlobalTheory.T.eq_zero_of_val_eq_zero_abelian A g L u hA
      intro z hz
      have hk : z ∈ pre u.ex (W k) := hmono _ _ (inf_le_left.trans inf_le_left) hz
      have hj : z ∈ pre u.ex (W j) := hmono _ _ (inf_le_left.trans inf_le_right) hz
      rw [hsub _ z hz, hmul _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz, hval _ _ _ _ z hz,
        hcoc k j l z hk hj, mul_pow, sub_self]
  have htrans : ∀ i j, ∀ z ∈ pre u.ex (M.U i ⊓ M.U j),
      σ i z = val u.ex _ (M.g i j).val z * σ j z := by
    intro i j z hz
    have hz' : z ∈ pre u.ex (W i ⊓ W j) := hz
    rw [hinf] at hz'
    have e := hval i j (W i ⊓ W j) le_rfl z hz
    have e2 : ((res (le_rfl : W i ⊓ W j ≤ W i ⊓ W j) (M.g i j) : Γ(A.left, W i ⊓ W j))) = (M.g i j).val := by
      change (A.left.presheaf.map (homOfLE le_rfl).op).hom _ = _
      have : (homOfLE (le_rfl : W i ⊓ W j ≤ W i ⊓ W j)).op = 𝟙 _ := rfl
      rw [this, CategoryTheory.Functor.map_id]; rfl
    rw [e2] at e
    change σ i z = val u.ex (W i ⊓ W j) (M.g i j).val z * σ j z
    rw [e]
    exact htr i j z hz'.1 hz'.2
  exact GlobalTheory.T.periodic_holomorphic_sections_regular_abelianVariety A g L u hA M hM σ hhol hper htrans

end GlobalTheory.CechPer
