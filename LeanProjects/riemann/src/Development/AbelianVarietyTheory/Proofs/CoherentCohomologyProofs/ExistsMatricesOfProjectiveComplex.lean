import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.ExistsAwayFracOfMemHomLoc
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory

namespace GlobalTheory

theorem projMatrix_abstract {S : Type} [CommRing S] {P₀ P₁ P₂ F₀ F₁ G₁ G₂ : Type}
    [AddCommGroup P₀] [Module S P₀] [AddCommGroup P₁] [Module S P₁] [AddCommGroup P₂] [Module S P₂]
    [AddCommGroup F₀] [Module S F₀] [AddCommGroup F₁] [Module S F₁]
    [AddCommGroup G₁] [Module S G₁] [AddCommGroup G₂] [Module S G₂]
    (d₀ : P₀ →ₗ[S] P₁) (d₁ : P₁ →ₗ[S] P₂) (p₀ : F₀ →ₗ[S] P₀) (s₀ : P₀ →ₗ[S] F₀)
    (p₁ : F₁ →ₗ[S] P₁) (s₁ : P₁ →ₗ[S] F₁) (D₀ : F₀ →ₗ[S] G₁) (D₁ : G₁ →ₗ[S] G₂)
    (q₁ : G₁ →ₗ[S] F₁) (q₀ : G₁ →ₗ[S] F₀) (i₁ : F₁ →ₗ[S] G₁) (i₀ : F₀ →ₗ[S] G₁)
    (r₂ : G₂ →ₗ[S] P₂) (r₁ : G₂ →ₗ[S] F₁) (r₀ : G₂ →ₗ[S] P₀)
    (h₀ : p₀ ∘ₗ s₀ = LinearMap.id) (h₁ : p₁ ∘ₗ s₁ = LinearMap.id)
    (hq₁ : q₁ ∘ₗ D₀ = s₁ ∘ₗ d₀ ∘ₗ p₀) (hq₀ : q₀ ∘ₗ D₀ = LinearMap.id - s₀ ∘ₗ p₀)
    (hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id)
    (hr₂ : r₂ ∘ₗ D₁ = d₁ ∘ₗ p₁ ∘ₗ q₁) (hr₁ : r₁ ∘ₗ D₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁)
    (hr₀ : r₀ ∘ₗ D₁ = p₀ ∘ₗ q₀) :
    Set.BijOn p₀ {v | D₀ v = 0} (LinearMap.ker d₀) ∧
      (Function.Exact d₀ d₁ → ∀ w, D₁ w = 0 → ∃ v, D₀ v = w) := by
  have h₀ : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁ : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have hq₁ : ∀ x, q₁ (D₀ x) = s₁ (d₀ (p₀ x)) := fun x => LinearMap.congr_fun hq₁ x
  have hq₀ : ∀ x, q₀ (D₀ x) = x - s₀ (p₀ x) := fun x => LinearMap.congr_fun hq₀ x
  have hi : ∀ x, i₁ (q₁ x) + i₀ (q₀ x) = x := fun x => LinearMap.congr_fun hi x
  have hr₂ : ∀ x, r₂ (D₁ x) = d₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₂ x
  have hr₁ : ∀ x, r₁ (D₁ x) = q₁ x - s₁ (p₁ (q₁ x)) := fun x => LinearMap.congr_fun hr₁ x
  have hr₀ : ∀ x, r₀ (D₁ x) = p₀ (q₀ x) := fun x => LinearMap.congr_fun hr₀ x
  have key : ∀ v, D₀ v = 0 → s₀ (p₀ v) = v := fun v hv => by
    have := hq₀ v
    rw [hv, map_zero] at this
    exact (sub_eq_zero.mp this.symm).symm
  refine ⟨⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun x hx => ⟨s₀ x, ?_, h₀ x⟩⟩, ?_⟩
  · have hv : D₀ v = 0 := hv
    have := congrArg p₁ (hq₁ v)
    rw [hv, map_zero, map_zero, h₁] at this
    exact this.symm
  · rw [← key v hv, ← key v' hv', h]
  · have hx : d₀ x = 0 := hx
    show D₀ (s₀ x) = 0
    rw [← hi (D₀ (s₀ x)), hq₁, hq₀, h₀, hx]
    simp
  · intro hex w hw
    have e₂ := hr₂ w
    have e₁ := hr₁ w
    have e₀ := hr₀ w
    rw [hw, map_zero] at e₂ e₁ e₀
    obtain ⟨x, hx⟩ := (hex _).mp e₂.symm
    refine ⟨s₀ x + q₀ w, ?_⟩
    have hp : p₀ (s₀ x + q₀ w) = x := by rw [map_add, h₀, ← e₀, add_zero]
    rw [← hi (D₀ _), hq₁, hq₀, hp, hx, ← sub_eq_zero.mp e₁.symm, add_sub_cancel_left, hi]

theorem projMatrix_mulVec {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a b : ℕ} (f : (Fin a → R) →ₗ[R] (Fin b → R)) (x : R' ⊗[R] (Fin a → R)) :
    ((LinearMap.toMatrix' f).map (algebraMap R R')).mulVec
        (TensorProduct.piScalarRight R R' R' (Fin a) x) =
      TensorProduct.piScalarRight R R' R' (Fin b) (f.baseChange R' x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, Matrix.mulVec_add, hx, hy]
  | tmul r y =>
    ext i
    have hy : f y = (LinearMap.toMatrix' f).mulVec y := by
      rw [LinearMap.toMatrix'_mulVec]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      Matrix.mulVec, dotProduct, Matrix.map_apply, Finset.sum_smul, Algebra.smul_def, map_mul,
      map_sum, Finset.sum_mul, mul_assoc]

theorem projMatrix_sum {R : Type} [CommRing R] (R' : Type) [CommRing R'] [Algebra R R']
    {a : ℕ} {P : Type} [AddCommGroup P] [Module R P] (p : (Fin a → R) →ₗ[R] P)
    (x : R' ⊗[R] (Fin a → R)) :
    ∑ k, TensorProduct.piScalarRight R R' R' (Fin a) x k ⊗ₜ[R] p (Pi.single k 1) =
      p.baseChange R' x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy =>
    simp only [map_add, Pi.add_apply, TensorProduct.add_tmul, Finset.sum_add_distrib, hx, hy]
  | tmul r y =>
    have hy : p y = ∑ k, y k • p (Pi.single k 1) := by
      simp only [← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [LinearMap.baseChange_tmul, hy]
    simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
      TensorProduct.tmul_sum, TensorProduct.smul_tmul]

theorem exists_matrices_of_projective_complex :
    ∀ (R : Type) [CommRing R] (P₀ P₁ P₂ : Type) [AddCommGroup P₀] [Module R P₀] [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂] [Module.Finite R P₀] [Module.Projective R P₀] [Module.Finite R P₁] [Module.Projective R P₁] [Module.Finite R P₂] [Module.Projective R P₂] (d₀ : P₀ →ₗ[R] P₁) (d₁ : P₁ →ₗ[R] P₂), d₁ ∘ₗ d₀ = 0 → ∃ (a b c : ℕ) (D₀ : Matrix (Fin b) (Fin a) R) (D₁ : Matrix (Fin c) (Fin b) R) (u : Fin a → P₀), D₁ * D₀ = 0 ∧ ∀ (R' : Type) [CommRing R'] [Algebra R R'], Set.BijOn (fun v : Fin a → R' => ∑ k, v k ⊗ₜ[R] u k) {v | (D₀.map (algebraMap R R')).mulVec v = 0} (LinearMap.ker (d₀.baseChange R')) ∧ (Function.Exact (d₀.baseChange R') (d₁.baseChange R') → ∀ w : Fin b → R', (D₁.map (algebraMap R R')).mulVec w = 0 → ∃ v, (D₀.map (algebraMap R R')).mulVec v = w) := by
  intro R _ P₀ P₁ P₂ _ _ _ _ _ _ _ _ _ _ _ _ d₀ d₁ hd
  obtain ⟨n₀, p₀, s₀, -, -, h₀⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₀
  obtain ⟨n₁, p₁, s₁, -, -, h₁⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₁
  obtain ⟨n₂, p₂, s₂, -, -, h₂⟩ := Module.Finite.exists_comp_eq_id_of_projective R P₂
  have hE : ∀ n m : ℕ, Nonempty ((Fin (n + m) → R) ≃ₗ[R] (Fin n → R) × (Fin m → R)) :=
    fun n m => ⟨(LinearEquiv.funCongrLeft R R finSumFinEquiv).trans
      (LinearEquiv.sumArrowLequivProdArrow _ _ R R)⟩
  obtain ⟨E⟩ := hE n₁ n₀
  obtain ⟨E'⟩ := hE n₂ (n₁ + n₀)
  have h₀' : ∀ x, p₀ (s₀ x) = x := fun x => LinearMap.congr_fun h₀ x
  have h₁' : ∀ x, p₁ (s₁ x) = x := fun x => LinearMap.congr_fun h₁ x
  have h₂' : ∀ x, p₂ (s₂ x) = x := fun x => LinearMap.congr_fun h₂ x
  have hd' : ∀ x, d₁ (d₀ x) = 0 := fun x => LinearMap.congr_fun hd x
  let q₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₁ → R) := LinearMap.fst R _ _ ∘ₗ E.toLinearMap
  let q₀ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin n₀ → R) := LinearMap.snd R _ _ ∘ₗ E.toLinearMap
  let i₁ : (Fin n₁ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inl R _ _
  let i₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) := E.symm.toLinearMap ∘ₗ LinearMap.inr R _ _
  let f₀ : (Fin n₀ → R) →ₗ[R] (Fin (n₁ + n₀) → R) :=
    E.symm.toLinearMap ∘ₗ LinearMap.prod (s₁ ∘ₗ d₀ ∘ₗ p₀) (LinearMap.id - s₀ ∘ₗ p₀)
  let f₁ : (Fin (n₁ + n₀) → R) →ₗ[R] (Fin (n₂ + (n₁ + n₀)) → R) :=
    E'.symm.toLinearMap ∘ₗ LinearMap.prod (s₂ ∘ₗ d₁ ∘ₗ p₁ ∘ₗ q₁)
      (E.symm.toLinearMap ∘ₗ LinearMap.prod (q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁) (s₀ ∘ₗ p₀ ∘ₗ q₀))
  let r₂ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₂ := p₂ ∘ₗ LinearMap.fst R _ _ ∘ₗ E'.toLinearMap
  let r₁ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] (Fin n₁ → R) :=
    q₁ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  let r₀ : (Fin (n₂ + (n₁ + n₀)) → R) →ₗ[R] P₀ :=
    p₀ ∘ₗ q₀ ∘ₗ LinearMap.snd R _ _ ∘ₗ E'.toLinearMap
  have hq₁ : q₁ ∘ₗ f₀ = s₁ ∘ₗ d₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₁, f₀]
  have hq₀ : q₀ ∘ₗ f₀ = LinearMap.id - s₀ ∘ₗ p₀ := LinearMap.ext fun x => by simp [q₀, f₀]
  have hi : i₁ ∘ₗ q₁ + i₀ ∘ₗ q₀ = LinearMap.id := LinearMap.ext fun x => by
    simp [q₀, q₁, i₀, i₁, ← map_add]
  have hr₂ : r₂ ∘ₗ f₁ = d₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₂, f₁, h₂']
  have hr₁ : r₁ ∘ₗ f₁ = q₁ - s₁ ∘ₗ p₁ ∘ₗ q₁ := LinearMap.ext fun x => by simp [r₁, f₁, q₁]
  have hr₀ : r₀ ∘ₗ f₁ = p₀ ∘ₗ q₀ := LinearMap.ext fun x => by simp [r₀, f₁, q₀, h₀']
  have hf : f₁ ∘ₗ f₀ = 0 := LinearMap.ext fun x => by
    have e₁ : q₁ (f₀ x) = s₁ (d₀ (p₀ x)) := LinearMap.congr_fun hq₁ x
    have e₀ : q₀ (f₀ x) = x - s₀ (p₀ x) := LinearMap.congr_fun hq₀ x
    simp [f₁, e₁, e₀, h₀', h₁', hd']
  refine ⟨n₀, n₁ + n₀, n₂ + (n₁ + n₀), LinearMap.toMatrix' f₀, LinearMap.toMatrix' f₁,
    fun k => p₀ (Pi.single k 1), ?_, ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hf, map_zero]
  intro R' _ _
  obtain ⟨hB, hX⟩ := projMatrix_abstract (d₀.baseChange R') (d₁.baseChange R')
    (p₀.baseChange R') (s₀.baseChange R') (p₁.baseChange R') (s₁.baseChange R')
    (f₀.baseChange R') (f₁.baseChange R') (q₁.baseChange R') (q₀.baseChange R')
    (i₁.baseChange R') (i₀.baseChange R') (r₂.baseChange R') (r₁.baseChange R')
    (r₀.baseChange R')
    (by rw [← LinearMap.baseChange_comp, h₀, LinearMap.baseChange_id])
    (by rw [← LinearMap.baseChange_comp, h₁, LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hq₁])
    (by simp only [← LinearMap.baseChange_comp, hq₀, LinearMap.baseChange_sub,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, ← LinearMap.baseChange_add, hi,
      LinearMap.baseChange_id])
    (by simp only [← LinearMap.baseChange_comp, hr₂])
    (by simp only [← LinearMap.baseChange_comp, hr₁, LinearMap.baseChange_sub])
    (by simp only [← LinearMap.baseChange_comp, hr₀])
  constructor
  · let e := TensorProduct.piScalarRight R R' R' (Fin n₀)
    have hmem : ∀ x, (((LinearMap.toMatrix' f₀).map (algebraMap R R')).mulVec (e x) = 0) ↔
        f₀.baseChange R' x = 0 := fun x => by
      rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff]
    refine ⟨fun v hv => ?_, fun v hv v' hv' h => ?_, fun y hy => ?_⟩
    · obtain ⟨x, rfl⟩ := e.surjective v
      have := hB.mapsTo ((hmem x).mp hv)
      rwa [← projMatrix_sum] at this
    · obtain ⟨x, rfl⟩ := e.surjective v
      obtain ⟨x', rfl⟩ := e.surjective v'
      congr 1
      refine hB.injOn ((hmem x).mp hv) ((hmem x').mp hv') ?_
      rw [← projMatrix_sum, ← projMatrix_sum]
      exact h
    · obtain ⟨x, hx, rfl⟩ := hB.surjOn hy
      exact ⟨e x, (hmem x).mpr hx, projMatrix_sum R' p₀ x⟩
  · intro hex w hw
    obtain ⟨x, rfl⟩ := (TensorProduct.piScalarRight R R' R' (Fin (n₁ + n₀))).surjective w
    rw [projMatrix_mulVec, LinearEquiv.map_eq_zero_iff] at hw
    obtain ⟨v, rfl⟩ := hX hex x hw
    exact ⟨_, projMatrix_mulVec R' f₀ v⟩

end GlobalTheory
