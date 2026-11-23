import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.HeckePairTop
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwBernDom
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwSimpleQuad
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwDomMul
open ValuativeRel Matrix GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools

private theorem group_identity_commuting {G : Type*} [Group G] (s a u v : G) (h : s⁻¹ * (a * u) * (s⁻¹ * (a * u)) = a * (a * u * v))
    (hs : Commute s a) (hv : Commute (a * u) v) : u = s * v * s := by
  rw [hv.eq, ← mul_assoc, ← mul_assoc a v] at h
  have h1 := mul_right_cancel h
  rw [← mul_assoc, hs.inv_left.eq, mul_assoc a, mul_assoc a] at h1
  have h2 := mul_left_cancel h1
  rw [← h2]; group

private theorem fund_succ {k : Type} [Field k] {n : ℕ} (x : kˣ) (l : Fin n) :
    (fun m => x ^ fund n ((l : ℕ) + 1) m) = (fun m => x ^ fund n (l : ℕ) m) * Pi.mulSingle l x := by
  funext m
  simp only [fund, Pi.mul_apply]
  by_cases h : m = l
  · subst h; simp
  · have h' : (m : ℕ) ≠ l := fun e => h (Fin.ext e)
    rw [Pi.mulSingle_eq_of_ne h, mul_one]
    congr 1
    by_cases h2 : (m : ℕ) < l
    · rw [if_pos h2, if_pos (by omega)]
    · rw [if_neg h2, if_neg (by omega)]

private theorem dom_fund {k : Type} [Field k] [ValuativeRel k] {n : ℕ} {x : kˣ} (hx : IsUnif x) (m : ℕ) :
    Dom (fun l => x ^ fund n m l) := by
  obtain ⟨p, -, hp⟩ := hx
  have h1 : valuation k (x : k) ≤ 1 := by rw [← hp]; exact p.2
  intro a b hab
  have hab' : (a : ℕ) ≤ b := hab
  simp only [fund]
  by_cases hb : (b : ℕ) < m
  · rw [if_pos hb, if_pos (by omega)]
  · rw [if_neg hb]
    by_cases ha : (a : ℕ) < m
    · rw [if_pos ha]; simpa using h1
    · rw [if_neg ha]

theorem UpperTheory.V.AlgebraTools.bernRel :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] (ρ : Representation A (GL (Fin n) k) M) (x : kˣ), IsUnif x → IsUnit (resCard k : A) → ∀ θ : (Fin n → kˣ) →* (Module.End A (fixd ρ (iwC k n ⊤)))ˣ, (∀ t, Dom t → (θ t : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (diagT k (Fin n) t)) → ∀ (i j : Fin n), (j : ℕ) = i + 1 → (θ (Pi.mulSingle i x) : Module.End A (fixd ρ (iwC k n ⊤))) = hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) * (θ (Pi.mulSingle j x) : Module.End A (fixd ρ (iwC k n ⊤))) * hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j)) ∧ ∀ l : Fin n, l ≠ i → l ≠ j → Commute (hk ρ (iwC k n ⊤) (pm k n (Equiv.swap i j))) (θ (Pi.mulSingle l x) : Module.End A (fixd ρ (iwC k n ⊤))) := by
  intro k _ _ _ _ n A M _ _ _ ρ x hx hq θ hθ i j hij
  obtain ⟨hc, y, hy1, hy2⟩ := bernDom k n A M ρ x hx i j hij
  obtain ⟨s, hs⟩ := (simpleQuad k n ⊤ A M ρ i j hij).1 hq
  rw [← hs] at hc hy1 ⊢
  set f : ℕ → Fin n → kˣ := fun m l => x ^ fund n m l with hf
  have hT : ∀ m, hk ρ (iwC k n ⊤) (pw x (fund n m)) = (θ (f m) : Module.End A (fixd ρ (iwC k n ⊤))) :=
    fun m => (hθ _ (dom_fund hx m)).symm
  have hS : ∀ l : Fin n, θ (f ((l : ℕ) + 1)) = θ (f l) * θ (Pi.mulSingle l x) := fun l => by
    rw [← map_mul]; exact congrArg θ (fund_succ x l)
  have hcm : ∀ m : ℕ, m ≠ j → Commute s (θ (f m)) := fun m hm => by
    have h := hc (f m) (dom_fund hx m) (by
      simp only [hf, fund]
      by_cases h2 : (j : ℕ) < m
      · rw [if_pos h2, if_pos (by omega)]
      · rw [if_neg h2, if_neg (by omega)])
    rw [← hθ _ (dom_fund hx m)] at h
    exact Commute.units_of_val h
  rw [hT] at hy1
  rw [hT, hT] at hy2
  refine ⟨?_, fun l hi hj => ?_⟩
  · have hj : θ (f j) = θ (f i) * θ (Pi.mulSingle i x) := by rw [hij]; exact hS i
    have hy : y = ((s⁻¹ * θ (f j) : (Module.End A (fixd ρ (iwC k n ⊤)))ˣ) : Module.End A (fixd ρ (iwC k n ⊤))) := by
      rw [Units.val_mul, hy1, Units.inv_mul_cancel_left]
    rw [hy, ← Units.val_mul, ← Units.val_mul] at hy2
    have h3 := Units.val_injective hy2
    rw [hS j, hj] at h3
    have h4 := group_identity_commuting s _ _ _ h3 (hcm i (by omega)) (by
      rw [← map_mul]; exact (Commute.all _ _).map θ)
    rw [h4, Units.val_mul, Units.val_mul]
  · have hi' : (l : ℕ) ≠ i := fun e => hi (Fin.ext e)
    have hj' : (l : ℕ) ≠ j := fun e => hj (Fin.ext e)
    have h1 := hcm l hj'
    have h2 := hcm ((l : ℕ) + 1) (by omega)
    have h3 : θ (Pi.mulSingle l x) = (θ (f l))⁻¹ * θ (f ((l : ℕ) + 1)) := by
      rw [hS, inv_mul_cancel_left]
    have h4 : Commute s (θ (Pi.mulSingle l x)) := by
      rw [h3]; exact h1.inv_right.mul_right h2
    exact h4.units_val
