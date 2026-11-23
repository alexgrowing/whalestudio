import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CupSurjectivity.CupK

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.LogCris

namespace CrystallineSemistableComparison.Onto

open Pb HT

variable {l : ℕ} [Fact l.Prime] {K : IntermediateField ℚ_[l] (PadicAlgCl l)}

theorem castT_rfl {M : Model l K} {i : ℕ} (x : M.T i) : castT rfl x = x := rfl

theorem dfac {C : Type*} [CommRing C] {m m' : ℕ} (f : Fin m → C) (g : Fin m' → C) (F : Fin m → C) (G : Fin m' → C)
    (z : ℤ) : ∑ s, ∑ s', f s * g s' * (z • (F s * G s')) = (z • ∑ s, f s * F s) * ∑ s', g s' * G s' := by
  rw [Finset.smul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' _ => ?_
  simp only [zsmul_eq_mul]
  ring

theorem r1 (hC : CupLaws) {M : Model l K} {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n) {A β T : ℕ}
    (sl : Hdg S.P.q (A + a') (T + n) →ₗ[K] Hdg M.q β n) (ψ : Module.Dual K (Hdg M.q β n))
    {e f i j : ℕ} (hp : e + f = A) (hT : i + j = T) (u : Hdg M.q e i) (v : Hdg M.q f j)
    {a₁₂ ij : ℕ} (h₁ : e + a' = a₁₂) (g₁ : i + n = ij) (h₂ : a₁₂ + f = A + a') (g₂ : ij + j = T + n) :
    th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q hp hT (S.pl₁ e i u) (S.pl₂ f j v)) =
      ((-1 : ℤ) ^ (j * n)) • ψ (sl (cupH S.P.q h₂ g₂ (S.pl₁ a₁₂ ij (cupH M.q h₁ g₁ u x)) (S.pl₂ f j v))) := by
  have L := hC K S.P.gen S.P.q
  have LM := hC K M.gen M.q
  simp only [th, LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
  rw [L.2.1 hp rfl (rfl : f + a' = f + a') (by omega : e + (f + a') = A + a') hT rfl (rfl : j + n = j + n)
    (by omega : i + (j + n) = T + n)]
  rw [L.2.2.1 (rfl : f + a' = f + a') (add_comm a' f) (rfl : j + n = j + n) (add_comm n j)]
  rw [← cupL_apply hC S.P.q (by omega : e + (f + a') = A + a') (by omega : i + (j + n) = T + n), map_zsmul, cupL_apply]
  rw [← L.2.1 h₁ h₂ (add_comm a' f) (by omega) g₁ g₂ (add_comm n j) (by omega)]
  rw [← LM.2.2.2.2.1 S.P.gen S.P.q (Model.genMap S.p₁ S.h₁) (Model.genMap_q S.p₁ S.h₁) h₁ g₁ u x]
  rw [map_zsmul, map_zsmul]

theorem t1 (hC : CupLaws) (P : HTPre l K) {M : Model l K} (hM : M.Sm) {D : ℕ} (S : Sq M D) {a' n : ℕ} (x : Hdg M.q a' n)
    {α β A t : ℕ} (hA : α + β = A + a') (φ' : Module.Dual K (Hdg M.q α t)) (ψ : Module.Dual K (Hdg M.q β n))
    (sl : Hdg S.P.q (A + a') (t + n) →ₗ[K] Hdg M.q β n) (hsl : IsSl S hA φ' sl)
    {i j : ℕ} (X : M.T i) (Y : M.T j) (Z : S.P.T (i + j))
    (hZ : S.P.CupT (Model.pullT S.p₁ S.h₁ i X) (Model.pullT S.p₂ S.h₂ j Y) Z) (hij : i + j = t) :
    P.h S.P A t (S.P.toV t (castT hij Z)) (th hC S sl ψ (S.pl₁ a' n x)) =
      if hj : j = n then kap hC P x φ' X * P.h M β n (M.toV n (castT hj Y)) ψ else 0 := by
  subst hij
  have hfin : ∀ a k, FiniteDimensional K (Hdg M.q a k) := fun a k => (P.fin M hM a k).1
  let b : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg M.q a i))) K (Hdg M.q a i) := fun a => Module.finBasis K _
  let b' : ∀ a, Module.Basis (Fin (Module.finrank K (Hdg M.q a j))) K (Hdg M.q a j) := fun a => Module.finBasis K _
  rw [castT_rfl, cupK P hM S X Y Z hZ b b' A]
  have tz : ∀ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), (p.1.1 + a', i + n) ≠ (α, i + j) → ∀ s s',
      th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl
        (S.pl₁ p.1.1 i (b p.1.1 s)) (S.pl₂ p.1.2 j (b' p.1.2 s'))) = 0 := by
    intro p hne s s'
    have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
    rw [r1 hC S x sl ψ _ rfl _ _ rfl rfl (by omega) (by omega), hsl.2 _ _ _ _ _ _ hne, map_zero, smul_zero]
  have allz : (∀ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), (p.1.1 + a', i + n) ≠ (α, i + j)) →
      ∑ p : (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)), ∑ s, ∑ s',
        P.h M p.1.1 i (M.toV _ X) ((b p.1.1).coord s) * P.h M p.1.2 j (M.toV _ Y) ((b' p.1.2).coord s') *
        kC K (th hC S sl ψ (S.pl₁ a' n x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 p.2) rfl
          (S.pl₁ p.1.1 i (b p.1.1 s)) (S.pl₂ p.1.2 j (b' p.1.2 s')))) = 0 := fun h =>
    Finset.sum_eq_zero fun p _ => Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => by
      rw [tz p (h p) s s', map_zero, mul_zero]
  by_cases hj : j = n
  · subst hj
    rw [dif_pos rfl, castT_rfl]
    by_cases hα : a' ≤ α
    · have hmem : (α - a', β) ∈ (Finset.HasAntidiagonal.antidiagonal A : Finset (ℕ × ℕ)) :=
        Finset.HasAntidiagonal.mem_antidiagonal.2 (by simp only; omega)
      rw [Finset.sum_eq_single ⟨(α - a', β), hmem⟩]
      · have key : ∀ s s', th hC S sl ψ (S.pl₁ a' j x) (cupH S.P.q (Finset.HasAntidiagonal.mem_antidiagonal.1 hmem) rfl
            (S.pl₁ (α - a') i (b (α - a') s)) (S.pl₂ β j (b' β s'))) =
            ((-1 : ℤ) ^ (j * j)) • (Fx hC x φ' i (b (α - a') s) * ψ (b' β s')) := by
          intro s s'
          rw [r1 hC S x sl ψ _ rfl _ _ (Nat.sub_add_cancel hα) rfl hA rfl, hsl.1, map_smul, smul_eq_mul]
          rw [Fx, dif_pos (And.intro hα rfl)]
          simp only [LinearMap.comp_apply, LinearMap.flip_apply, cupL_apply]
        simp only [key, map_zsmul, map_mul]
        rw [dfac, kap, bsum (kC K) _ (fun k φ => P.lin' M _ _ k _ φ) (b (α - a')), bsum (kC K) _ (fun k φ => P.lin' M _ _ k _ φ) (b' β)]
      · intro p _ hne
        refine Finset.sum_eq_zero fun s _ => Finset.sum_eq_zero fun s' _ => ?_
        rw [tz p ?_ s s', map_zero, mul_zero]
        intro h
        have hp := Finset.HasAntidiagonal.mem_antidiagonal.1 p.2
        have h1 : p.1.1 + a' = α := (Prod.ext_iff.1 h).1
        exact hne (Subtype.ext (Prod.ext (by simp only; omega) (by simp only; omega)))
      · intro h; exact absurd (Finset.mem_univ _) h
    · rw [allz fun p h => hα (by have := (Prod.ext_iff.1 h).1; simp only at this; omega)]
      simp [kap, Fx, hα]
  · rw [dif_neg hj]
    exact allz fun p h => hj (by have := (Prod.ext_iff.1 h).2; simp only at this; omega)

end CrystallineSemistableComparison.Onto

end
