import CompanionTheory.RealGroups.DiscreteSeries.DiscreteSeriesClassification.DiscreteSeriesExhaustion.MatrixCoefficientDecay.HilbertSchmidtDecay.RightKTypes.CoefFam

noncomputable section

open Finset Matrix
open scoped InnerProductSpace

namespace CompanionTheory.RgExh.Dec.L.WyKR

open CompanionTheory.RgExh CompanionTheory.RgExh.Dec ReciprocityTheory.ChartRestriction.DS

variable {n : ℕ}

section

variable {ε : Fin n → Bool} {X : GMod n}

theorem kr_unit (k : S7.KG ε) : (S7.toMK k)ᴴ * S7.toMK k = 1 ∧ S7.toMK k * (S7.toMK k)ᴴ = 1 := by
  have hu : S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (show S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ _ from k.2).1
  exact ⟨by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff'.mp hu,
    by simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp hu⟩

theorem kr_entry (k : S7.KG ε) (a b : Fin n) : ‖S7.toMK k a b‖ ≤ 1 := by
  have hu : S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ :=
    (show S7.toMK k ∈ Matrix.unitaryGroup (Fin n) ℂ ∧ _ from k.2).1
  exact entry_norm_bound_of_unitary hu a b

def tensRho (A : KAct ε X) (k : S7.KG ε) : Module.End ℂ (Fin n → X.V) where
  toFun u := fun b => ∑ i, S7.toMK k b i • A.ρ k (u i)
  map_add' u v := by funext b; simp [smul_add, sum_add_distrib]
  map_smul' c u := by
    funext b
    simp only [Pi.smul_apply, map_smul, smul_sum, RingHom.id_apply]
    exact sum_congr rfl fun i _ => smul_comm _ _ _

theorem tensRho_apply (A : KAct ε X) (k : S7.KG ε) (u : Fin n → X.V) (b : Fin n) :
    tensRho A k u b = ∑ i, S7.toMK k b i • A.ρ k (u i) := rfl

theorem kr_one_apply (k : S7.KG ε) (b d : Fin n) :
    ∑ i, S7.toMK k b i * (S7.toMK k)ᴴ i d = if b = d then 1 else 0 := by
  have h := congrFun (congrFun (kr_unit k).2 b) d
  rwa [Matrix.mul_apply, Matrix.one_apply] at h

theorem kr_one_apply' (k : S7.KG ε) (b d : Fin n) :
    ∑ i, (S7.toMK k)ᴴ b i * S7.toMK k i d = if b = d then 1 else 0 := by
  have h := congrFun (congrFun (kr_unit k).1 b) d
  rwa [Matrix.mul_apply, Matrix.one_apply] at h

private theorem sum_toMK_mul_conjTranspose_smul_eq_smul {M : Type} [AddCommGroup M] [Module ℂ M] (k : S7.KG ε) (b : Fin n)
    (α : ℂ) (w : Fin n → M) :
    ∑ i, ∑ d, (S7.toMK k b i * (α * (S7.toMK k)ᴴ i d)) • w d = α • w b := by
  rw [Finset.sum_comm]
  have h : ∀ d, ∑ i, (S7.toMK k b i * (α * (S7.toMK k)ᴴ i d)) • w d =
      (α * ∑ i, S7.toMK k b i * (S7.toMK k)ᴴ i d) • w d := by
    intro d
    rw [← Finset.sum_smul, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [h, kr_one_apply, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true]

theorem commute_om_tensRho (A : KAct ε X) (k : S7.KG ε) : Commute (om X) (tensRho A k) := by
  refine LinearMap.ext fun u => funext fun b => ?_
  rw [Module.End.mul_apply, Module.End.mul_apply]
  simp only [om_apply, tensRho_apply, map_sum, map_smul, A.compat, Finset.smul_sum, smul_smul]
  conv_rhs =>
    rw [Finset.sum_comm]
    enter [2, a]
    rw [Finset.sum_comm]
  simp only [sum_toMK_mul_conjTranspose_smul_eq_smul]
  exact Finset.sum_comm

private theorem sum_conjTranspose_toMK_smul_tensRho_eq (A : KAct ε X) (k : S7.KG ε) (u : Fin n → X.V) (b : Fin n) (α : ℂ) :
    ∑ d, (α * (S7.toMK k)ᴴ b d) • tensRho A k u d = α • A.ρ k (u b) := by
  simp only [tensRho_apply, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  have h : ∀ i, ∑ d, (α * (S7.toMK k)ᴴ b d * S7.toMK k d i) • A.ρ k (u i) =
      (α * if b = i then 1 else 0) • A.ρ k (u i) := by
    intro i
    rw [← Finset.sum_smul, ← kr_one_apply' k b i, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun d _ => by ring
  simp only [h, mul_ite, mul_one, mul_zero, ite_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

theorem tensRho_compat (A : KAct ε X) (k : S7.KG ε) (a b : Fin n) (u : Fin n → X.V) :
    tensRho A k (tensE X a b u) =
      ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • tensE X c d (tensRho A k u) := by
  funext j
  have e1 : tensRho A k (tensE X a b u) j =
      ∑ i, S7.toMK k j i • A.ρ k (X.E a b (u i)) + S7.toMK k j a • A.ρ k (u b) := by
    rw [tensRho_apply]
    simp only [tensE_apply, map_add, smul_add, Finset.sum_add_distrib]
    congr 1
    simp [apply_ite (A.ρ k)]
  have e2 : (∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • tensE X c d (tensRho A k u)) j =
      ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • X.E c d (tensRho A k u j) +
        S7.toMK k j a • A.ρ k (u b) := by
    simp only [Finset.sum_apply, Pi.smul_apply, tensE_apply, smul_add, Finset.sum_add_distrib]
    congr 1
    simp only [smul_ite, smul_zero]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact sum_conjTranspose_toMK_smul_tensRho_eq A k u b _
  rw [e1, e2]
  congr 1
  simp only [A.compat, Finset.smul_sum, smul_smul, tensRho_apply, map_sum, map_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun i _ => by congr 1; ring

def sv {z : ℂ} (u : (step X z).V) : Fin n → X.V := (show stepSub X z from u).1

theorem sv_smul {z : ℂ} (c : ℂ) (u : (step X z).V) : sv (c • u) = c • sv u := rfl

theorem sv_sum {z : ℂ} {ι : Type} (s : Finset ι) (f : ι → (step X z).V) : sv (∑ i ∈ s, f i) = ∑ i ∈ s, sv (f i) := by
  exact Submodule.coe_sum (stepSub X z) f s

theorem sv_E {z : ℂ} (a b : Fin n) (u : (step X z).V) : sv ((step X z).E a b u) = tensE X a b (sv u) := rfl

theorem sv_inj {z : ℂ} {u v : (step X z).V} (h : sv u = sv v) : u = v := by
  exact Subtype.ext h

def stepRho (A : KAct ε X) (z : ℂ) (k : S7.KG ε) : Module.End ℂ (step X z).V :=
  (tensRho A k).restrict (fun _ hx => Module.End.mapsTo_maxGenEigenspace_of_comm (commute_om_tensRho A k) _ hx)

theorem stepRho_coe (A : KAct ε X) (z : ℂ) (k : S7.KG ε) (u : (step X z).V) :
    sv (stepRho A z k u) = tensRho A k (sv u) := rfl

def stepEmb (A : KAct ε X) (z : ℂ) : (step X z).V →ₗ[ℂ] (Fin n → A.N) :=
  (LinearMap.pi fun i => A.emb ∘ₗ LinearMap.proj i) ∘ₗ (stepSub X z).subtype

theorem stepEmb_apply (A : KAct ε X) (z : ℂ) (u : (step X z).V) (i : Fin n) :
    stepEmb A z u i = A.emb ((sv u) i) := rfl

theorem stepEmb_inj (A : KAct ε X) (z : ℂ) : Function.Injective (stepEmb A z) := by
  intro u v h
  apply sv_inj
  funext i
  apply A.inj
  have h' := congrFun h i
  rwa [stepEmb_apply, stepEmb_apply] at h'

theorem stepRho_compat (A : KAct ε X) (z : ℂ) (k : S7.KG ε) (a b : Fin n) (x : (step X z).V) :
    stepRho A z k ((step X z).E a b x) =
      ∑ c, ∑ d, (S7.toMK k c a * (S7.toMK k)ᴴ b d) • (step X z).E c d (stepRho A z k x) := by
  apply sv_inj
  simp only [stepRho_coe, sv_E, sv_sum, sv_smul]
  exact tensRho_compat A k a b (sv x)

end

end CompanionTheory.RgExh.Dec.L.WyKR
