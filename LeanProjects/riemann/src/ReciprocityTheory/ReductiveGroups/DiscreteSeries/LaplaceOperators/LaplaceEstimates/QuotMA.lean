import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.PsiDatumStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.RightDerivativeToL2
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.KTypeLemma.ExistsCommutingProjectionImage

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear

open ReciprocityTheory.ChartRestriction.DS

section Cls

variable {n : ℕ}

theorem toL2_congr_on_unitary_bis (ε : Fin n → Bool) {F G : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ g ∈ UJset ε, F g = G g) : toL2 ε F = toL2 ε G := by
  have e : (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) = fun g => G (Formalism.MainNotions.S.umat g) :=
    funext fun g => h _ (unitary_matrix_mem_set ε g)
  by_cases hF : MemLp (fun g : Formalism.REAL.UJ ε => F (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε)
  · have hG : MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_memLp_toLp ε hF, toL2_eq_memLp_toLp ε hG, MemLp.toLp_eq_toLp_iff]
    exact Filter.EventuallyEq.of_eq e
  · have hG : ¬ MemLp (fun g : Formalism.REAL.UJ ε => G (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) := e ▸ hF
    rw [toL2_eq_zero_of_not_memLp ε hF, toL2_eq_zero_of_not_memLp ε hG]

theorem exists_lin {Y : Type*} [AddCommGroup Y] [Module ℂ Y] (ε : Fin n → Bool)
    (A : Fin n → Fin n → Module.End ℂ Y) (G : Submodule ℂ Y)
    (L : Y →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ)) (hsm : ∀ f ∈ G, IsSmoothL2 ε (L f))
    (hG : ∀ a b, ∀ f ∈ G, A a b f ∈ G)
    (hder : ∀ f ∈ G, ∀ a b, ∀ g ∈ UJset ε, Formalism.REAL.Eab ε a b (L f) g = L (A a b f) g) :
    ∃ T : Y →ₗ[ℂ] smD ε (rreg ε), (∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f)) ∧
      ∀ a b, ∀ f ∈ G, T (A a b f) = smE ε (rreg ε) a b (T f) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl G
  let p := G.projectionOnto q hq
  have hpG : ∀ f ∈ G, ((p f : G) : Y) = f := fun f hf => by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨f, hf⟩)
  have hmem : ∀ f : Y, toL2 ε (L (p f)) ∈ smD ε (rreg ε) := fun f => toL2_mem_smD_of_isSmoothL2 (hsm _ (p f).2)
  have hL2 : ∀ f : Y, MemLp (fun g : Formalism.REAL.UJ ε => L (p f) (Formalism.MainNotions.S.umat g)) 2 (Formalism.REAL.muG ε) :=
    fun f => (hsm _ (p f).2).2 []
  let T : Y →ₗ[ℂ] smD ε (rreg ε) :=
    { toFun := fun f => ⟨toL2 ε (L (p f)), hmem f⟩
      map_add' := fun f g => by
        apply Subtype.ext
        simp only [Submodule.coe_add]
        rw [map_add, Submodule.coe_add, map_add]
        exact toL2_add_smooth ε (hL2 f) (hL2 g)
      map_smul' := fun c f => by
        apply Subtype.ext
        simp only [Submodule.coe_smul, RingHom.id_apply]
        rw [map_smul, Submodule.coe_smul, map_smul]
        exact toL2_smul_smooth ε c _ }
  have hT : ∀ f ∈ G, (T f : L2 ε) = toL2 ε (L f) := fun f hf => by
    show toL2 ε (L (p f)) = _
    rw [hpG f hf]
  refine ⟨T, hT, fun a b f hf => ?_⟩
  have e1 : T f = ⟨toL2 ε (L f), toL2_mem_smD_of_isSmoothL2 (hsm f hf)⟩ := Subtype.ext (hT f hf)
  apply Subtype.ext
  rw [hT _ (hG a b f hf), e1, rightDerivative_toL2 (hsm f hf) a b]
  exact toL2_congr_on_unitary_bis ε fun g hg => (hder f hf a b g hg).symm

end Cls

section Lin

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {D : Submodule ℂ H}

def tMapDL (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H) :
    (Fin (2 * r + k + 1) → D) →ₗ[ℂ] (Mat k r → ℂ) where
  toFun f := tMapD σ x₁ x₀ w (fun c => ((f c : D) : H))
  map_add' f g := by
    funext x
    simp only [tMapD, coefX, Pi.add_apply, Submodule.coe_add, map_add, inner_add_right, mul_add,
      Finset.sum_add_distrib]
  map_smul' c f := by
    funext x
    simp only [tMapD, coefX, Pi.smul_apply, Submodule.coe_smul, map_smul, inner_smul_right,
      RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => by ring

theorem tMapDL_apply (σ : Mat k r → (H →L[ℂ] H)) (x₁ : Fin (2 * r + k + 1) → ℂ) (x₀ : Mat k r) (w : H)
    (f : Fin (2 * r + k + 1) → D) : tMapDL σ x₁ x₀ w f = tMapD σ x₁ x₀ w (fun c => ((f c : D) : H)) := rfl

end Lin

section Line

universe u

variable {n : ℕ} {D : Type*} [NormedAddCommGroup D] [InnerProductSpace ℂ D] {ε : Fin n → Bool}
  {E : Fin n → Fin n → Module.End ℂ D}

theorem line (hU : IsKUnitary ε E) (X : Submodule ℂ (Fin n → D)) (Λ : Fin n → ℝ)
    (hXk : ∀ y ∈ X, ∃ S : Submodule ℂ (Fin n → D), S ≤ X ∧ FiniteDimensional ℂ S ∧
      IsKStableSub ε (LemK.tensVd E) S ∧ y ∈ S)
    (hK2 : ∀ f₁ f₂ : Fin n → D, f₁ ∈ X → f₂ ∈ X → IsKHWVec ε (LemK.tensVd E) Λ f₁ →
      IsKHWVec ε (LemK.tensVd E) Λ f₂ → ∃ c₁ c₂ : ℂ, (c₁ ≠ 0 ∨ c₂ ≠ 0) ∧ c₁ • f₁ + c₂ • f₂ = 0) :
    ∃ ys ∈ X, ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ c : ℂ, y = c • ψ ys := by
  classical

  have hlift : ∀ (Y : Type u) [AddCommGroup Y] [Module ℂ Y] (B : Fin n → Fin n → Module.End ℂ Y)
      (ψ : (Fin n → D) →ₗ[ℂ] Y), (∀ a b, ε a = ε b → ∀ x ∈ X, ψ (LemK.tensVd E a b x) = B a b (ψ x)) →
      ∀ y ∈ X.map ψ, IsKHWVec ε B Λ y → ∃ x ∈ X, IsKHWVec ε (LemK.tensVd E) Λ x ∧ ψ x = y := by
    intro Y _ _ B ψ hψ y hy hyK
    obtain ⟨x₀, hx₀, rfl⟩ := Submodule.mem_map.1 hy
    obtain ⟨S, hSX, hfd, hSk, hx₀S⟩ := hXk x₀ hx₀
    obtain ⟨x, hxS, hxK, hx⟩ := LemK.exists_highest_weight_lift_pi hU ψ hfd hSk
      (fun a b hab z hz => hψ a b hab z (hSX hz)) hx₀S hyK
    exact ⟨x, hSX hxS, hxK, hx⟩
  by_cases hex : ∃ ys ∈ X, ys ≠ 0 ∧ IsKHWVec ε (LemK.tensVd E) Λ ys
  · obtain ⟨ys, hys, hys0, hysK⟩ := hex
    refine ⟨ys, hys, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    obtain ⟨c₁, c₂, hc, hsum⟩ := hK2 x ys hx hys hxK hysK
    by_cases h1 : c₁ = 0
    · exfalso
      have h2 : c₂ ≠ 0 := hc.resolve_left (not_not.2 h1)
      rw [h1, zero_smul, zero_add] at hsum
      exact hys0 ((smul_eq_zero.1 hsum).resolve_left h2)
    · refine ⟨-(c₂ / c₁), ?_⟩
      have : x = -(c₂ / c₁) • ys := by
        have h3 : c₁ • x = -(c₂ • ys) := eq_neg_of_add_eq_zero_left hsum
        calc x = c₁⁻¹ • (c₁ • x) := by rw [smul_smul, inv_mul_cancel₀ h1, one_smul]
          _ = -(c₂ / c₁) • ys := by rw [h3, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
      rw [this, map_smul]
  · refine ⟨0, zero_mem _, fun Y _ _ B ψ hψ y hy hyK => ?_⟩
    obtain ⟨x, hx, hxK, rfl⟩ := hlift Y B ψ hψ y hy hyK
    have : x = 0 := by
      by_contra h0
      exact hex ⟨x, hx, h0, hxK⟩
    exact ⟨0, by rw [this, map_zero, zero_smul]⟩

end Line

end ReciprocityTheory.ChartRestriction.DS.Lap.TransportMapLinear
