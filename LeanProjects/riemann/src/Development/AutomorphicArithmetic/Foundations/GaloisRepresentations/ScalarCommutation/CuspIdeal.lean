import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCuspSpaceBot
import GroundTheory.AutomorphicForms.MeasuresModulus

set_option autoImplicit false

noncomputable section

open MeasureTheory Matrix

namespace UpperTheory.Gal.Spc

section Abstract

variable {Γ A H : Type} [Group Γ] [Group A] [Group H] [TopologicalSpace A] [TopologicalSpace H]
  [IsTopologicalGroup A] [IsTopologicalGroup H]
  (e : Γ ≃* A × H) {K : Subgroup Γ} {K₀ : Subgroup A} {K' : Subgroup H}

private theorem mem_K (hK : K.map e.toMonoidHom = K₀.prod K') (x : Γ) : x ∈ K ↔ e x ∈ K₀.prod K' := by
  rw [← hK, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]

private theorem compact_hull (hK : K.map e.toMonoidHom = K₀.prod K') (c₀ : IsCompact (K₀ : Set A))
    (c' : IsCompact (K' : Set H)) {f : Γ → ℂ} (hf : f ∈ Formalism.UG.Hecke ℂ K) :
    ∃ D : Set (A × H), IsCompact D ∧ ∀ x, f x ≠ 0 → e x ∈ D := by
  obtain ⟨-, S, hS⟩ := hf
  have hC : IsCompact ((K₀ : Set A) ×ˢ (K' : Set H)) := c₀.prod c'
  refine ⟨⋃ s ∈ S, (fun p : (A × H) × (A × H) => p.1 * e s * p.2) ''
    (((K₀ : Set A) ×ˢ (K' : Set H)) ×ˢ ((K₀ : Set A) ×ˢ (K' : Set H))), ?_, ?_⟩
  · exact S.isCompact_biUnion fun s _ => (hC.prod hC).image (by fun_prop)
  · intro x hx
    obtain ⟨s, hs, u, v, rfl⟩ := hS x hx
    refine Set.mem_iUnion₂.2 ⟨s, hs, ⟨(e u, e v), ⟨?_, ?_⟩, by simp [map_mul]⟩⟩
    · exact Subgroup.mem_prod.1 ((mem_K e hK u).1 u.2)
    · exact Subgroup.mem_prod.1 ((mem_K e hK v).1 v.2)

private theorem finite_cosets (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set A))
    (o' : IsOpen (K' : Set H)) (c₀ : IsCompact (K₀ : Set A)) (c' : IsCompact (K' : Set H)) {a : Γ → ℂ}
    (ha : a ∈ Formalism.UG.Hecke ℂ K) : {q : Γ ⧸ K | a q.out ≠ 0}.Finite := by
  have oU : IsOpen ((K₀.prod K' : Subgroup (A × H)) : Set (A × H)) := by
    rw [Subgroup.coe_prod]
    exact o₀.prod o'
  haveI := QuotientGroup.discreteTopology oU
  obtain ⟨D, hD, hsupp⟩ := compact_hull e hK c₀ c' ha
  have hT : (((↑) : A × H → (A × H) ⧸ K₀.prod K') '' D).Finite :=
    (hD.image QuotientGroup.continuous_mk).finite_of_discrete
  let φ : Γ ⧸ K → (A × H) ⧸ K₀.prod K' := fun q => ((e q.out : A × H) : (A × H) ⧸ K₀.prod K')
  have hφ : Function.Injective φ := by
    intro q₁ q₂ h
    have h' : (e q₁.out)⁻¹ * e q₂.out ∈ K₀.prod K' := QuotientGroup.eq.1 h
    rw [← map_inv, ← map_mul, ← mem_K e hK] at h'
    rw [← QuotientGroup.out_eq' q₁, ← QuotientGroup.out_eq' q₂]
    exact QuotientGroup.eq.2 h'
  refine (hT.preimage hφ.injOn).subset ?_
  intro q hq
  exact ⟨e q.out, hsupp _ hq, rfl⟩

private theorem slice_right (hK : K.map e.toMonoidHom = K₀.prod K') {f : Γ → ℂ} (hf : Formalism.UG.IsBiInv K f)
    (h' : H) (g : A) {c : A} (hc : c ∈ K₀) : f (e.symm (g * c, h')) = f (e.symm (g, h')) := by
  have hm : e.symm (c, 1) ∈ K := (mem_K e hK _).2 (by simpa using Subgroup.mem_prod.2 ⟨hc, K'.one_mem⟩)
  have hsplit : e.symm (g * c, h') = e.symm (g, h') * e.symm (c, 1) := by
    rw [← map_mul]
    simp
  rw [hsplit]
  simpa using hf 1 ⟨_, hm⟩ (e.symm (g, h'))

private theorem slice_cont (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set A)) {f : Γ → ℂ}
    (hf : Formalism.UG.IsBiInv K f) (h' : H) : Continuous fun g : A => f (e.symm (g, h')) := by
  refine continuous_iff_continuousAt.2 fun g => ?_
  have hev : ∀ᶠ x in nhds g, g⁻¹ * x ∈ K₀ := by
    have hc : Continuous fun x : A => g⁻¹ * x := continuous_const.mul continuous_id
    exact (o₀.preimage hc).mem_nhds (by simp [K₀.one_mem])
  refine (continuousAt_const (y := f (e.symm (g, h')))).congr ?_
  filter_upwards [hev] with x hx
  have hx' := slice_right e hK hf h' g hx
  rw [mul_inv_cancel_left] at hx'
  exact hx'.symm

end Abstract

section Unipotent

variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] {n a b : ℕ} (ε : Fin n ≃ Fin a ⊕ Fin b)

private def blk (X : Fin a → Fin b → k) : Matrix (Fin n) (Fin n) k :=
  Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1)

private theorem blk_neg (X : Fin a → Fin b → k) : blk ε X * blk ε (-X) = 1 := by
  simp [blk, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]

private theorem blk_cont : Continuous (blk ε : (Fin a → Fin b → k) → Matrix (Fin n) (Fin n) k) := by
  unfold blk
  fun_prop

private theorem integrable_slice {F : GL (Fin n) k → ℂ} (hc : Continuous F) {C : Set (GL (Fin n) k)}
    (hC : IsCompact C) (hs : ∀ y, F y ≠ 0 → y ∈ C) (μ : Measure (Fin a → Fin b → k)) [μ.IsAddHaarMeasure]
    (u : (Fin a → Fin b → k) → GL (Fin n) k) (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) = blk ε X)
    (g h : GL (Fin n) k) : Integrable (fun X => F (g * (h⁻¹ * u X * h))) μ := by
  have hinv : ∀ X, (((u X)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) = blk ε (-X) := by
    intro X
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hu X]
    exact blk_neg ε X
  have hcu : Continuous u := by
    refine Units.continuous_iff.2 ⟨?_, ?_⟩
    · have hv : (Units.val ∘ u) = blk ε := funext hu
      rw [hv]
      exact blk_cont ε
    · have hv : (fun X => (((u X)⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k)) = fun X => blk ε (-X) :=
        funext hinv
      rw [hv]
      exact (blk_cont ε).comp continuous_neg
  have hcont : Continuous fun X => g * (h⁻¹ * u X * h) :=
    continuous_const.mul ((continuous_const.mul hcu).mul continuous_const)
  let π : GL (Fin n) k → (Fin a → Fin b → k) := fun y i j =>
    (y : Matrix (Fin n) (Fin n) k) (ε.symm (Sum.inl i)) (ε.symm (Sum.inr j))
  have hπ : Continuous π :=
    continuous_pi fun i => continuous_pi fun j => Units.continuous_val.matrix_elem _ _
  have hπu : ∀ X, π (u X) = X := by
    intro X
    funext i j
    simp [π, hu, blk, Matrix.reindex_apply]
  have hπ' : Continuous fun y : GL (Fin n) k => π (h * (g⁻¹ * y) * h⁻¹) := by
    exact hπ.comp ((continuous_const.mul (continuous_const.mul continuous_id)).mul continuous_const)
  refine (hc.comp hcont).integrable_of_hasCompactSupport ?_
  refine HasCompactSupport.intro (hC.image hπ') ?_
  intro X hX
  by_contra hne
  apply hX
  refine ⟨g * (h⁻¹ * u X * h), hs _ hne, ?_⟩
  dsimp only
  rw [show h * (g⁻¹ * (g * (h⁻¹ * u X * h))) * h⁻¹ = u X by group]
  exact hπu X

end Unipotent

section Main

variable {Γ H : Type} [Group Γ] [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalRing k] [T2Space k] [MeasurableSpace k]
  [BorelSpace k] [SecondCountableTopology k] {n : ℕ}
  (e : Γ ≃* GL (Fin n) k × H) {K : Subgroup Γ} {K₀ : Subgroup (GL (Fin n) k)} {K' : Subgroup H}

private theorem hecke_integrable (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H)) {f : Γ → ℂ}
    (hf : f ∈ Formalism.UG.Hecke ℂ K) (h' : H) {a b : ℕ} (ε : Fin n ≃ Fin a ⊕ Fin b)
    (μ : Measure (Fin a → Fin b → k)) [μ.IsAddHaarMeasure] (u : (Fin a → Fin b → k) → GL (Fin n) k)
    (hu : ∀ X, (u X : Matrix (Fin n) (Fin n) k) =
      Matrix.reindex ε.symm ε.symm (Matrix.fromBlocks 1 (Matrix.of X) 0 1))
    (g h : GL (Fin n) k) : Integrable (fun X => f (e.symm (g * (h⁻¹ * u X * h), h'))) μ := by
  obtain ⟨D, hD, hsupp⟩ := compact_hull e hK c₀ c' hf
  have hbi : Formalism.UG.IsBiInv K f := hf.1
  refine integrable_slice ε (slice_cont e hK o₀ hbi h') (hD.image continuous_fst) ?_ μ u
    (fun X => (hu X).trans rfl) g h
  intro y hy
  exact ⟨(y, h'), by simpa using hsupp _ hy, rfl⟩

private theorem left_mul (w : Γ) (y : GL (Fin n) k) (h' : H) :
    w * e.symm (y, h') = e.symm ((e w).1 * y, (e w).2 * h') := by
  apply e.injective
  rw [map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
  rfl

private theorem noConst_lin (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H)) {f f' : Γ → ℂ}
    (hf : f ∈ Formalism.UG.Hecke ℂ K) (hf' : f' ∈ Formalism.UG.Hecke ℂ K) (c : ℂ)
    (Cf : ∀ h : H, NoConst fun g => f (e.symm (g, h))) (Cf' : ∀ h : H, NoConst fun g => f' (e.symm (g, h)))
    (h' : H) : NoConst fun g => (c • f + f') (e.symm (g, h')) := by
  intro a b ε ha hb μ hμ u hu g h
  haveI := hμ
  have i1 := hecke_integrable e hK o₀ c₀ c' hf h' ε μ u hu g h
  have i2 := hecke_integrable e hK o₀ c₀ c' hf' h' ε μ u hu g h
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [integral_add (i1.const_mul c) i2, integral_const_mul, Cf h' a b ε ha hb μ hμ u hu g h,
    Cf' h' a b ε ha hb μ hμ u hu g h]
  simp

private theorem noConst_conv (hK : K.map e.toMonoidHom = K₀.prod K') (o₀ : IsOpen (K₀ : Set (GL (Fin n) k)))
    (o' : IsOpen (K' : Set H)) (c₀ : IsCompact (K₀ : Set (GL (Fin n) k))) (c' : IsCompact (K' : Set H))
    {α f : Γ → ℂ} (hα : α ∈ Formalism.UG.Hecke ℂ K) (hf : f ∈ Formalism.UG.Hecke ℂ K)
    (Cf : ∀ h : H, NoConst fun g => f (e.symm (g, h))) (h' : H) :
    NoConst fun g => Formalism.UG.conv K α f (e.symm (g, h')) := by
  intro a b ε ha hb μ hμ u hu g h
  haveI := hμ
  have hS := finite_cosets e hK o₀ o' c₀ c' hα
  have key : ∀ y : GL (Fin n) k, Formalism.UG.conv K α f (e.symm (y, h')) =
      ∑ q ∈ hS.toFinset, α q.out * f (e.symm ((e q.out⁻¹).1 * y, (e q.out⁻¹).2 * h')) := by
    intro y
    unfold Formalism.UG.conv
    rw [finsum_eq_sum_of_support_subset _ (s := hS.toFinset)]
    · refine Finset.sum_congr rfl fun q _ => ?_
      rw [left_mul e]
    · intro q hq
      simp only [Function.mem_support, Set.Finite.coe_toFinset, Set.mem_setOf_eq] at hq ⊢
      exact left_ne_zero_of_mul hq
  simp only [key]
  rw [integral_finset_sum]
  · refine Finset.sum_eq_zero fun q _ => ?_
    rw [integral_const_mul]
    have hz := Cf ((e q.out⁻¹).2 * h') a b ε ha hb μ hμ u hu ((e q.out⁻¹).1 * g) h
    simp only [mul_assoc] at hz ⊢
    rw [hz, mul_zero]
  · intro q _
    refine Integrable.const_mul ?_ _
    have hi := hecke_integrable e hK o₀ c₀ c' hf ((e q.out⁻¹).2 * h') ε μ u hu ((e q.out⁻¹).1 * g) h
    simpa only [mul_assoc] using hi

end Main

theorem cuspIdeal : CuspIdeal := by
  intro p _ G _ Lv k _ _ _ _ _ _ _ P H _ _ _ _ S k₁ _ _ P₁
  haveI : SecondCountableTopology k := GlobalTheory.SplitWeil.secondCountable k
  refine ⟨fun a ha f hf Cf h' => ?_, fun h' => ?_, fun f hf f' hf' c Cf Cf' h' => ?_⟩
  · exact noConst_conv S.e S.map_eq S.open₀ S.open' S.cpt₀ S.cpt' ha hf Cf h'
  · intro a b ε ha hb μ hμ u hu g h
    simp
  · exact noConst_lin S.e S.map_eq S.open₀ S.cpt₀ S.cpt' hf hf' c Cf Cf' h'

end UpperTheory.Gal.Spc
