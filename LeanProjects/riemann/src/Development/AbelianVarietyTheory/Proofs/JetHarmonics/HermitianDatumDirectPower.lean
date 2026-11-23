import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCSt
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj
open scoped TensorProduct

namespace GlobalTheory

noncomputable section

def diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) : U →ₗ[ℝ] U :=
  e.symm.toLinearMap ∘ₗ (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) ∘ₗ e.toLinearMap

theorem diagEnd_apply {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) (x : U) (i : Fin n) : e (diagEnd e f x) i = f (e x i) := by
  simp [diagEnd]

theorem diagEnd_comp {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (e : U ≃ₗ[ℝ] (Fin n → V)) (f g : V →ₗ[ℝ] V) : diagEnd e f ∘ₗ diagEnd e g = diagEnd e (f ∘ₗ g) := by
  ext x
  apply e.injective
  funext i
  simp [diagEnd_apply]

theorem trace_diagEnd {U V : Type} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    [Module.Finite ℝ V] {n : ℕ} (e : U ≃ₗ[ℝ] (Fin n → V)) (f : V →ₗ[ℝ] V) :
    LinearMap.trace ℝ U (diagEnd e f) = n * LinearMap.trace ℝ V f := by
  have h1 : diagEnd e f = e.symm.conj (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i) := by
    ext x; simp [diagEnd, LinearEquiv.conj_apply]
  have h2 : (LinearMap.pi fun i => f ∘ₗ LinearMap.proj i : (Fin n → V) →ₗ[ℝ] (Fin n → V)) =
      ∑ i, LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i) := by
    apply LinearMap.ext; intro x
    funext j
    simp [LinearMap.sum_apply, Finset.sum_apply, Pi.single_apply]
  rw [h1, LinearMap.trace_conj', h2, map_sum]
  have h3 : ∀ i : Fin n, LinearMap.trace ℝ _ (LinearMap.single ℝ (fun _ : Fin n => V) i ∘ₗ (f ∘ₗ LinearMap.proj i)) =
      LinearMap.trace ℝ V f := by
    intro i
    rw [LinearMap.trace_comp_comm']
    congr 1
    ext x; simp
  simp [h3]

def powForm {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) :
    LinearMap.BilinForm ℤ (Fin n → L) :=
  ∑ i, B.compl₁₂ (LinearMap.proj i) (LinearMap.proj i)

theorem powForm_apply {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x y : Fin n → L) :
    powForm B n x y = ∑ i, B (x i) (y i) := by
  simp [powForm, LinearMap.sum_apply]

theorem powForm_single {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ) (x : Fin n → L)
    (i : Fin n) (y : L) : powForm B n x (Pi.single i y) = B (x i) y := by
  rw [powForm_apply, Finset.sum_eq_single i]
  · simp
  · intro j _ hj; simp [Pi.single_eq_of_ne hj]
  · simp

theorem powForm_bijective {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (hB : Function.Bijective B)
    (n : ℕ) : Function.Bijective (powForm B n) := by
  constructor
  · intro x y h
    funext i
    apply hB.1
    ext z
    rw [← powForm_single, ← powForm_single, h]
  · intro φ
    choose x hx using fun i : Fin n => hB.2 (φ ∘ₗ LinearMap.single ℤ (fun _ : Fin n => L) i)
    refine ⟨x, ?_⟩
    apply LinearMap.pi_ext
    intro i z
    rw [powForm_single, hx]
    rfl

theorem powForm_baseChange {L : Type} [AddCommGroup L] (B : LinearMap.BilinForm ℤ L) (n : ℕ)
    (x y : ℝ ⊗[ℤ] (Fin n → L)) :
    (powForm B n).baseChange ℝ x y =
      ∑ i, B.baseChange ℝ (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) x i)
        (TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => L) y i) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
  | tmul r u =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb, Finset.sum_add_distrib]
    | tmul s v => simp [powForm_apply, Finset.sum_smul, Finset.sum_mul]

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def powDatum (D : Datum H) (n : ℕ) : Datum H where
  La := Fin n → D.La
  fin := by haveI := D.fin; infer_instance
  proj := by
    haveI := D.proj
    exact Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 E) (M := fun _ : Fin n => D.La))
  EF := powForm D.EF n
  alt := fun x => by simp [powForm_apply, D.alt]
  unimod := powForm_bijective D.EF D.unimod n
  adj := fun a x y => by simp [powForm_apply, D.adj]
  p := n * D.p
  q := n * D.q
  rank := by
    haveI := D.fin
    haveI := D.proj
    have h1 := (TensorProduct.isBaseChange (𝓞 E) (Fin n → D.La) E).finrank_eq
    have h2 := (TensorProduct.isBaseChange (𝓞 E) D.La E).finrank_eq
    have h3 := (TensorProduct.piRight (𝓞 E) E E (fun _ : Fin n => D.La)).finrank_eq
    rw [← h1, h3, Module.finrank_pi_fintype]
    simp [h2, D.rank, mul_add]
  dom := by
    haveI := D.fin
    haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) D.La
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    set e := TensorProduct.piRight ℤ ℝ ℝ (fun _ : Fin n => D.La) with he
    refine ⟨diagEnd e J, ?_, ?_, ?_, ?_⟩
    · intro x
      apply e.injective
      funext i
      simp [diagEnd_apply, h1]
    · intro x y
      simp only [powForm_baseChange, ← he, diagEnd_apply, h2]
    · intro x hx
      simp only [powForm_baseChange, ← he, diagEnd_apply]
      have : ∃ i, e x i ≠ 0 := by
        by_contra hc
        push_neg at hc
        exact hx (e.injective (by rw [map_zero]; exact funext hc))
      obtain ⟨i, hi⟩ := this
      refine Finset.sum_pos' (fun j _ => ?_) ⟨i, Finset.mem_univ _, h3 _ hi⟩
      by_cases hj : e x j = 0
      · simp [hj]
      · exact (h3 _ hj).le
    · intro a A t hA ht
      let A0 : ℝ ⊗[ℤ] D.La →ₗ[ℝ] ℝ ⊗[ℤ] D.La :=
        ((DistribMulAction.toAddMonoidHom D.La a).toIntLinearMap).baseChange ℝ
      obtain ⟨k1, k2, k3⟩ := h4 a A0 _ (fun x => by simp [A0]) rfl
      have hAA : A = diagEnd e A0 := by
        apply LinearMap.ext
        intro x
        induction x using TensorProduct.induction_on with
        | zero => simp
        | add a b ha hb => simp only [map_add, ha, hb]
        | tmul r u =>
          have : r ⊗ₜ[ℤ] u = r • ((1 : ℝ) ⊗ₜ[ℤ] u) := by simp [TensorProduct.smul_tmul']
          rw [this, map_smul, map_smul, hA]
          congr 1
          apply e.injective
          funext i
          simp [diagEnd_apply, he, A0]
      have ht' : t = n * ∑ τ ∈ Finset.univ.filter (fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0),
        ((D.p : ℂ) * τ (a : E) + (D.q : ℂ) * starRingEnd ℂ (τ (a : E))) := by
        rw [ht, Finset.mul_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        push_cast; ring
      rw [hAA, diagEnd_comp, diagEnd_comp, trace_diagEnd, trace_diagEnd, k1, ← k1, k2, k3, ht']
      refine ⟨rfl, ?_, ?_⟩
      · rw [Complex.mul_re, Complex.natCast_re, Complex.natCast_im]; ring
      · rw [Complex.mul_im, Complex.natCast_re, Complex.natCast_im]; ring

theorem exists_datum_pow : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (n : ℕ),
    ∃ (Dw' : Datum H) (e : Dw'.La ≃ₗ[𝓞 E] (Fin n → Dw.La)),
      (∀ x y, Dw'.EF x y = ∑ i, Dw.EF (e x i) (e y i)) ∧ Dw'.p = n * Dw.p ∧ Dw'.q = n * Dw.q :=
  fun E _ _ _ _ Dw n => ⟨powDatum Dw n, LinearEquiv.refl (𝓞 E) (Fin n → Dw.La),
    fun x y => powForm_apply Dw.EF n x y, rfl, rfl⟩

end
end GlobalTheory
