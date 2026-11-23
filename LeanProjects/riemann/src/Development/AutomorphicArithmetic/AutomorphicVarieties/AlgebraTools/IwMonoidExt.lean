import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop

open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

theorem UpperTheory.V.AlgebraTools.monoidExt :
    ∀ (T H : Type) [CommGroup T] [Monoid H] (P : Submonoid T) (f : T → H), (∀ t : T, ∃ a ∈ P, ∃ b ∈ P, t = a * b⁻¹) → f 1 = 1 → (∀ a ∈ P, ∀ b ∈ P, f (a * b) = f a * f b) → (∀ a ∈ P, IsUnit (f a)) → ∃! θ : T →* Hˣ, ∀ a ∈ P, (θ a : H) = f a := by
  intro T H _ _ P f hgen h1 hmul hunit
  classical
  let U : T → Hˣ := fun a => if h : a ∈ P then (hunit a h).unit else 1
  have hU : ∀ a ∈ P, (U a : H) = f a := by
    intro a ha
    simp [U, ha]
  have hUmul : ∀ a ∈ P, ∀ b ∈ P, U (a * b) = U a * U b := by
    intro a ha b hb
    ext
    rw [Units.val_mul, hU _ (P.mul_mem ha hb), hU a ha, hU b hb, hmul a ha b hb]
  have hcomm : ∀ a ∈ P, ∀ b ∈ P, Commute (U a) (U b) := by
    intro a ha b hb
    show U a * U b = U b * U a
    rw [← hUmul a ha b hb, ← hUmul b hb a ha, mul_comm a b]
  have hU1 : U 1 = 1 := Units.ext (by rw [hU 1 P.one_mem, h1]; rfl)
  have hwd : ∀ a ∈ P, ∀ b ∈ P, ∀ c ∈ P, ∀ d ∈ P, a * b⁻¹ = c * d⁻¹ →
      U a * (U b)⁻¹ = U c * (U d)⁻¹ := by
    intro a ha b hb c hc d hd h
    have h' : a * d = c * b := by
      calc a * d = (a * b⁻¹) * (b * d) := by rw [mul_assoc, inv_mul_cancel_left]
        _ = (c * d⁻¹) * (b * d) := by rw [h]
        _ = c * b := by rw [mul_comm b d, mul_assoc, inv_mul_cancel_left]
    have hU' : U a * U d = U c * U b := by
      rw [← hUmul a ha d hd, ← hUmul c hc b hb, h']
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, (hcomm d hd b hb).inv_left.eq, ← mul_assoc,
      eq_mul_inv_iff_mul_eq, hU']
  choose A hA B hB hAB using hgen
  let θ : T →* Hˣ :=
    { toFun := fun t => U (A t) * (U (B t))⁻¹
      map_one' := by
        show U (A 1) * (U (B 1))⁻¹ = 1
        rw [hwd (A 1) (hA 1) (B 1) (hB 1) 1 P.one_mem 1 P.one_mem (by rw [← hAB 1]; simp), hU1]
        simp
      map_mul' := fun t s => by
        show U (A (t * s)) * (U (B (t * s)))⁻¹ = U (A t) * (U (B t))⁻¹ * (U (A s) * (U (B s))⁻¹)
        have he : A (t * s) * (B (t * s))⁻¹ = (A t * A s) * (B t * B s)⁻¹ := by
          rw [← hAB (t * s)]
          calc t * s = A t * (B t)⁻¹ * (A s * (B s)⁻¹) := by rw [← hAB t, ← hAB s]
            _ = A t * A s * (B t * B s)⁻¹ := by
              rw [_root_.mul_inv_rev]
              ac_rfl
        rw [hwd _ (hA _) _ (hB _) _ (P.mul_mem (hA t) (hA s)) _ (P.mul_mem (hB t) (hB s)) he,
          hUmul _ (hA t) _ (hA s), hUmul _ (hB t) _ (hB s), _root_.mul_inv_rev]
        have c1 : Commute (U (B t))⁻¹ (U (A s)) := (hcomm _ (hB t) _ (hA s)).inv_left
        have c2 : Commute (U (B t))⁻¹ (U (B s))⁻¹ := (hcomm _ (hB t) _ (hB s)).inv_inv
        simp only [mul_assoc]
        rw [← mul_assoc (U (B t))⁻¹, c1.eq, mul_assoc, c2.eq] }
  have hθ : ∀ a ∈ P, (θ a : H) = f a := by
    intro a ha
    show ((U (A a) * (U (B a))⁻¹ : Hˣ) : H) = f a
    rw [hwd (A a) (hA a) (B a) (hB a) a ha 1 P.one_mem (by rw [← hAB a]; simp), hU1, inv_one,
      mul_one, hU a ha]
  refine ⟨θ, hθ, fun θ' h' => ?_⟩
  have agree : ∀ a ∈ P, θ' a = θ a := fun a ha => Units.ext ((h' a ha).trans (hθ a ha).symm)
  apply MonoidHom.ext
  intro t
  rw [hAB t, map_mul, map_mul, map_inv, map_inv, agree _ (hA t), agree _ (hB t)]
