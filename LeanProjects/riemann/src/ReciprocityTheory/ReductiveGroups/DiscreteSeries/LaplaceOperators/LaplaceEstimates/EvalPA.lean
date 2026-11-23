import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HaarRightStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.HasDerivAtExp
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.TMapSpec
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.LaplaceEstimates.SmoothMatrixMaps.IntOfBound

noncomputable section

open Matrix

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

theorem cminor_reindex {n n' p : ℕ} (E : Fin n' → Fin n' → Module.End ℂ M) (e : Fin n → Fin n')
    (he : Function.Injective e) (R C : Fin p → Fin n) (x : ℂ) :
    Capelli.cminor (fun a b => E (e a) (e b)) R C x = Capelli.cminor E (e ∘ R) (e ∘ C) x := by
  unfold Capelli.cminor
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 2
  refine List.ofFn_inj.mpr (funext fun j => ?_)
  simp only [Capelli.capEntry, Function.comp_apply, he.eq_iff]

theorem cminor_cast {n p p' : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (h : p = p')
    (R C : Fin p' → Fin n) (x : ℂ) :
    Capelli.cminor E (R ∘ Fin.cast h) (C ∘ Fin.cast h) x = Capelli.cminor E R C x := by
  subst h
  rfl

theorem ofFn_prod_intertwine (S : Submodule ℂ M) :
    ∀ (p : ℕ) (f : Fin p → Module.End ℂ S) (g : Fin p → Module.End ℂ M),
      (∀ j, S.subtype ∘ₗ f j = g j ∘ₗ S.subtype) →
      S.subtype ∘ₗ (List.ofFn f).prod = (List.ofFn g).prod ∘ₗ S.subtype
  | 0, f, g, _ => by ext; simp
  | p + 1, f, g, h => by
    rw [List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons, Module.End.mul_eq_comp,
      Module.End.mul_eq_comp, ← LinearMap.comp_assoc, h 0, LinearMap.comp_assoc,
      ofFn_prod_intertwine S p (fun j => f j.succ) (fun j => g j.succ) (fun j => h j.succ),
      LinearMap.comp_assoc]

def resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (a b : Fin n) : Module.End ℂ S :=
  (E a b).restrict (hS a b)

theorem capEntry_resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (t : ℂ) (a b : Fin n) :
    S.subtype ∘ₗ Capelli.capEntry (resE E S hS) t a b = Capelli.capEntry E t a b ∘ₗ S.subtype := by
  ext m
  simp only [Capelli.capEntry, LinearMap.comp_apply, LinearMap.add_apply, map_add, resE,
    Submodule.subtype_apply, LinearMap.coe_restrict_apply]
  split_ifs <;> simp

theorem cminor_resE {n p : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (R C : Fin p → Fin n) (x : ℂ) (m : S) :
    ((Capelli.cminor (resE E S hS) R C x m : S) : M) = Capelli.cminor E R C x (m : M) := by
  unfold Capelli.cminor
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.smul_apply,
    Submodule.coe_smul_of_tower]
  refine Finset.sum_congr rfl fun σ _ => ?_
  congr 1
  exact congrArg (fun f => f m) (ofFn_prod_intertwine S p _ _ (fun j => capEntry_resE E S hS _ _ _))

theorem isGlRep_resE {n : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (S : Submodule ℂ M)
    (hS : ∀ a b, ∀ x ∈ S, E a b x ∈ S) (hE : IsGlRep E) : IsGlRep (resE E S hS) := by
  intro a b c d
  ext m
  have := congrArg (fun f => f (m : M)) (hE a b c d)
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at this
  simp only [LinearMap.sub_apply, Module.End.mul_apply, resE, Submodule.coe_sub,
    LinearMap.coe_restrict_apply]
  rw [this]
  split_ifs <;> simp [resE, LinearMap.coe_restrict_apply]

theorem frameE_eq_actM {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ) (E : Fin n → Fin n → Module.End ℂ M)
    (i j : Fin n) : frameE Q E i j = actM E (Q⁻¹ * Matrix.single i j 1 * Q) := by
  unfold frameE actM
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  congr 1
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap

noncomputable section

open Matrix MeasureTheory
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

namespace CapelliMinorRestriction

section
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem cont_of_smoothOnG {n : ℕ} {ε : Fin n → Bool} {f : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (hf : Formalism.REAL.SmoothOnG ε f) : ContinuousOn f (UJset ε) := by
  intro g₀ hg₀
  obtain ⟨U, F, hU, hgU, hF, hfF⟩ := hf g₀ hg₀
  have hFc : ContinuousAt F g₀ := (hF.continuousOn).continuousAt (hU.mem_nhds hgU)
  refine (hFc.continuousWithinAt (s := UJset ε)).congr_of_eventuallyEq ?_ (hfF g₀ hgU hg₀)
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (hU.mem_nhds hgU)] with g hg hgU'
  exact hfF g hgU' hg

end

variable {k r : ℕ}

theorem cJ_transport (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (x1 y : Fin (2 * r + k + 1) → ℂ) (G : Mat k r) :
    cJ ε (P *ᵥ x1) y (P * G * P⁻¹) = star x1 ⬝ᵥ (Formalism.QuantumDeterminants.Hpk k r *ᵥ (G *ᵥ (P⁻¹ *ᵥ y))) := by
  have e1 : (P * G * P⁻¹) *ᵥ y = P *ᵥ (G *ᵥ (P⁻¹ *ᵥ y)) := by
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  unfold cJ Formalism.QuantumDeterminants.herm
  rw [e1, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [← hP]
  rfl

theorem cJ_sinv (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (z y : Fin (2 * r + k + 1) → ℂ) (s x : Mat k r)
    (hs : s ∈ Formalism.QuantumDeterminants.Sset k r z) :
    cJ ε (xJ P z) y (P * (s * x) * P⁻¹) = cJ ε (xJ P z) y (P * x * P⁻¹) := by
  obtain ⟨hsU, hsx⟩ := ExponentialSlopeDerivatives.s_fix k r z s hs
  have hsU' : sᴴ * Formalism.QuantumDeterminants.Hpk k r * s = Formalism.QuantumDeterminants.Hpk k r := hsU
  unfold xJ
  rw [cJ_transport ε P hP, cJ_transport ε P hP, ← Matrix.mulVec_mulVec]
  have := ExponentialSlopeDerivatives.herm_UH hsU' (xOne k r z) (x *ᵥ (P⁻¹ *ᵥ y))
  rwa [hsx] at this

theorem ae_S {z : Fin (2 * r + k + 1) → ℂ} {μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)}
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN) :
    ∀ᵐ p ∂(μW.prod μN), Matrix.of p.1 * Matrix.of p.2 ∈ Formalism.QuantumDeterminants.Sset k r z := by
  have := hW.1
  have := hN.1
  have h1 : ∀ᵐ x ∂μW, Matrix.of x ∈ Formalism.QuantumDeterminants.UWset k r z :=
    (measure_eq_zero_iff_ae_notMem.mp hW.2.2.1).mono fun x hx => not_not.mp hx
  have h2 : ∀ᵐ x ∂μN, Matrix.of x ∈ Formalism.QuantumDeterminants.Nset k r :=
    (measure_eq_zero_iff_ae_notMem.mp hN.2.2.1).mono fun x hx => not_not.mp hx
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae h1, Measure.quasiMeasurePreserving_snd.ae h2]
    with p hp1 hp2
  exact ⟨_, hp1, _, hp2, rfl⟩

theorem tMap_single {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H) (G : Mat k r) :
    tMap ε σ x1 x₀ w (Pi.single d m) G = cJ ε x1 (Pi.single d 1) G * coefX σ x₀ w m G := by
  unfold tMap
  rw [Finset.sum_eq_single d]
  · simp
  · intro c _ hc
    simp [Pi.single_eq_of_ne hc, coefX]
  · simp

theorem tMap_sum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ε : Fin (2 * r + k + 1) → Bool) (σ : Mat k r → (H →L[ℂ] H)) (x1 : Fin (2 * r + k + 1) → ℂ)
    (x₀ : Mat k r) (w : H) (f : Fin (2 * r + k + 1) → H) (G : Mat k r) :
    tMap ε σ x1 x₀ w f G = ∑ d, tMap ε σ x1 x₀ w (Pi.single d (f d)) G := by
  rw [Finset.sum_congr rfl fun d _ => tMap_single ε σ x1 x₀ w d (f d) G]
  rfl

theorem coefX_add {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H))
    (x₀ : Mat k r) (w m₁ m₂ : H) (G : Mat k r) :
    coefX σ x₀ w (m₁ + m₂) G = coefX σ x₀ w m₁ G + coefX σ x₀ w m₂ G := by
  simp [coefX, inner_add_right]

theorem coefX_smul {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mat k r → (H →L[ℂ] H))
    (x₀ : Mat k r) (w m : H) (a : ℂ) (G : Mat k r) :
    coefX σ x₀ w (a • m) G = a * coefX σ x₀ w m G := by
  simp [coefX, inner_smul_right]

variable {Vp : Type*} [NormedAddCommGroup Vp] [InnerProductSpace ℂ Vp] [CompleteSpace Vp]

def perI (P : Mat k r) (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (ξ : Vp)
    (x : Mat k r) (p : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r) : Vp :=
  F (P * (Matrix.of p.1 * Matrix.of p.2 * x) * P⁻¹) • chiInv ψ π (Matrix.of p.1) (Matrix.of p.2) ξ

theorem per_eq (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π F ξ x = ∫ p, perI P ψ π F ξ x p ∂(μW.prod μN) := rfl

theorem per_smul (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) (F : Mat k r → ℂ) (a : ℂ) (ξ : Vp) (x : Mat k r) :
    per P μW μN ψ π (fun G => a * F G) ξ x = a • per P μW μN ψ π F ξ x := by
  rw [per_eq, per_eq, ← integral_smul]
  congr 1
  funext p
  simp [perI, mul_smul]

theorem per_sum (P : Mat k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r)) (ψ : Mat k r → ℂ)
    (π : Mat k r → (Vp →L[ℂ] Vp)) {ι : Type*} (s : Finset ι) (F : ι → Mat k r → ℂ) (ξ : Vp) (x : Mat k r)
    (hF : ∀ i ∈ s, Integrable (perI P ψ π (F i) ξ x) (μW.prod μN)) :
    per P μW μN ψ π (fun G => ∑ i ∈ s, F i G) ξ x = ∑ i ∈ s, per P μW μN ψ π (F i) ξ x := by
  simp only [per_eq]
  rw [← integral_finsetSum s hF]
  congr 1
  funext p
  simp [perI, Finset.sum_smul]

theorem per_tMap_single (ε : Fin (2 * r + k + 1) → Bool) {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Mat k r → (H →L[ℂ] H)) (z : Fin (2 * r + k + 1) → ℂ) (P : Mat k r)
    (hP : Pᴴ * Formalism.REAL.Jm ε * P = Formalism.QuantumDeterminants.Hpk k r) (μW μN : Measure (Formalism.QuantumDeterminants.Mt k r))
    (hW : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW) (hN : Formalism.MainNotions.S.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN)
    (ψ : Mat k r → ℂ) (π : Mat k r → (Vp →L[ℂ] Vp)) (x₀ : Mat k r) (w : H) (d : Fin (2 * r + k + 1)) (m : H)
    (ξ : Vp) (g : Mat k r) :
    per P μW μN ψ π (tMap ε σ (xJ P z) x₀ w (Pi.single d m)) ξ g =
      cJ ε (xJ P z) (Pi.single d 1) (P * g * P⁻¹) • per P μW μN ψ π (coefX σ x₀ w m) ξ g := by
  rw [per_eq, per_eq, ← integral_smul]
  refine integral_congr_ae ?_
  filter_upwards [ae_S hW hN] with p hp
  simp only [perI]
  rw [tMap_single, cJ_sinv ε P hP z _ _ g hp, mul_smul]

end CapelliMinorRestriction

end ReciprocityTheory.ChartRestriction.DS.Lap
