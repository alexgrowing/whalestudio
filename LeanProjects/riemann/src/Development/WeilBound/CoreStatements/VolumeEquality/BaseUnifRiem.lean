import Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsEigenComponentPolynomial

open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped TensorProduct

noncomputable section

namespace SheetDecomposition.Riem

open GlobalTheory.CompanionTheory.Ar.Cusp.EigCoef

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

def imB (M : Matrix (Fin g) (Fin g) ℂ) : (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun z w => (z ⬝ᵥ M *ᵥ star w).im)
    (fun z z' w => by rw [add_dotProduct, Complex.add_im])
    (fun r z w => by rw [smul_dotProduct, Complex.smul_im])
    (fun z w w' => by rw [star_add, mulVec_add, dotProduct_add, Complex.add_im])
    (fun r z w => by
      have h : star (r • w) = (r : ℂ) • star w := by
        ext i
        simp
      rw [h, mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul, smul_eq_mul])

theorem imB_P (R : RiemLat E g Λ) (x y : Λ) : imB R.Hm (R.P x) (R.P y) = R.form x y := R.im x y

theorem inj (R : RiemLat E g Λ) : Function.Injective R.P := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => R.unimod.1 ?_
  ext y
  have h := imB_P R x y
  rw [hx] at h
  simpa using h.symm

theorem span_top (R : RiemLat E g Λ) : Submodule.span ℝ (Set.range R.P) = ⊤ := by
  classical
  have := R.free
  have := R.fin
  let b : Module.Basis (Fin (2 * g)) ℤ Λ := Module.finBasisOfFinrankEq ℤ Λ R.rank
  have hli : LinearIndependent ℝ fun k => R.P (b k) := by
    refine Fintype.linearIndependent_iff.2 fun r hr l => ?_
    obtain ⟨y, hy⟩ := R.unimod.2 (b.coord l)
    have h := congrArg (imB R.Hm (R.P y)) hr
    simp only [map_sum, map_smul, map_zero, imB_P, hy, Module.Basis.coord_apply, Module.Basis.repr_self,
      smul_eq_mul] at h
    rw [Finset.sum_eq_single l (fun k _ hk => by simp [Finsupp.single_apply, hk]) (by simp)] at h
    simpa using h
  have hcard : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  have h := hli.span_eq_top_of_card_eq_finrank' hcard
  rw [eq_top_iff, ← h]
  exact Submodule.span_mono (by
    rintro _ ⟨k, rfl⟩
    exact ⟨b k, rfl⟩)

omit [IsCMField E] in
theorem exists_decomp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (x : V) :
    ∃ y : (E →+* ℂ) → V, (∀ s, y s ∈ eigSp ρ (s.comp (algebraMap (𝓞 E) E))) ∧ ∑ s, y s = x := by
  classical
  choose cs hcs using exists_coeff (E := E)
  have hsum : ∑ s, combo (cs s) = 1 := by
    apply evalHom_injective
    rw [map_sum, map_one]
    simp only [hcs]
    funext s'
    simp [Finset.sum_apply, Pi.single_apply]
  have hmul : ∀ (s : E →+* ℂ) (b : 𝓞 E),
      ((1 : ℂ) ⊗ₜ[ℤ] b) * combo (cs s) = s (algebraMap (𝓞 E) E b) • combo (cs s) := by
    intro s b
    apply evalHom_injective
    rw [map_mul, map_smul, hcs]
    funext s'
    by_cases h : s' = s
    · subst h
      simp [evalHom_tmul]
    · simp [evalHom_tmul, h]
  refine ⟨fun s => actHom ρ (combo (cs s)) x, fun s => mem_eigSp_iff.2 fun b => ?_, ?_⟩
  · have h := congrArg (actHom ρ) (hmul s b)
    rw [map_mul, map_smul, actHom_tmul, one_smul] at h
    exact LinearMap.congr_fun h x
  · have h := congrArg (actHom ρ) hsum
    rw [map_sum, map_one] at h
    have h2 := LinearMap.congr_fun h x
    simpa [LinearMap.sum_apply] using h2

omit [IsCMField E] in
theorem exists_proj {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (s : 𝓞 E →+* ℂ) :
    ∃ p : V →ₗ[ℂ] V, (∀ x, eigComp ρ s x = p x) ∧ (∀ x, p x ∈ eigSp ρ s) ∧ (∀ x ∈ eigSp ρ s, p x = x) ∧
      ∀ a x, p (ρ a x) = s a • p x := by
  obtain ⟨c, hc⟩ := eigComp_eq_combination E s
  obtain ⟨h₁, h₂, h₃⟩ := hc V ρ
  have e : ∀ x, eigComp ρ s x = (∑ a ∈ c.support, c a • ρ a : V →ₗ[ℂ] V) x := fun x => by
    rw [h₁]
    simp [LinearMap.sum_apply]
  refine ⟨_, e, fun x => e x ▸ h₂ x, fun x hx => e x ▸ h₃ x hx, fun a x => ?_⟩
  rw [← e, ← e, ← mem_eigSp_iff.1 (h₂ x) a, h₁, h₁, map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul, ← Module.End.mul_apply, ← map_mul, mul_comm, map_mul, Module.End.mul_apply]

omit [IsCMField E] in
theorem sum_eigComp {V : Type} [AddCommGroup V] [Module ℂ V] (ρ : 𝓞 E →+* Module.End ℂ V) (x : V) :
    ∑ s : E →+* ℂ, eigComp ρ (s.comp (algebraMap (𝓞 E) E)) x = x := by
  classical
  obtain ⟨y, hy, hs⟩ := exists_decomp ρ x
  conv_rhs => rw [← hs]
  refine Finset.sum_congr rfl fun s _ => ?_
  obtain ⟨p, h₁, -, h₃, h₄⟩ := exists_proj ρ (s.comp (algebraMap (𝓞 E) E))
  rw [h₁, ← hs, map_sum, Finset.sum_eq_single s (fun s' _ hne => ?_) (by simp), h₃ _ (hy s)]
  by_contra h0
  refine hne (comp_injective (RingHom.ext fun a => ?_))
  have e := h₄ a (y s')
  rw [mem_eigSp_iff.1 (hy s') a, map_smul] at e
  exact smul_left_injective ℂ h0 e

theorem adj_herm (R : RiemLat E g Λ) (a a' : 𝓞 E) (ha : (a' : E) = IsCMField.complexConj E (a : E)) (z w : Fin g → ℂ) :
    R.B a z ⬝ᵥ R.Hm *ᵥ star w = z ⬝ᵥ R.Hm *ᵥ star (R.B a' w) := by
  have h : (imB R.Hm).comp ((R.B a).restrictScalars ℝ) = (imB R.Hm).compl₂ ((R.B a').restrictScalars ℝ) := by
    refine LinearMap.ext_on (span_top R) ?_
    rintro _ ⟨x, rfl⟩
    refine LinearMap.ext_on (span_top R) ?_
    rintro _ ⟨y, rfl⟩
    show imB R.Hm (R.B a (R.P x)) (R.P y) = imB R.Hm (R.P x) (R.B a' (R.P y))
    rw [← R.act, ← R.act, imB_P, imB_P, R.adj a a' ha]
  have him : ∀ z, (R.B a z ⬝ᵥ R.Hm *ᵥ star w).im = (z ⬝ᵥ R.Hm *ᵥ star (R.B a' w)).im := fun z =>
    LinearMap.congr_fun₂ h z w
  refine Complex.ext ?_ (him z)
  have h2 := him (Complex.I • z)
  rw [map_smul, smul_dotProduct, smul_dotProduct] at h2
  simpa using h2

theorem orth (R : RiemLat E g Λ) (s s' : 𝓞 E →+* ℂ) (hne : s ≠ s') (x : Fin g → ℂ) (hx : x ∈ eigSp R.B s)
    (y : Fin g → ℂ) (hy : y ∈ eigSp R.B s') : R.ip x y = 0 := by
  by_contra h0
  refine hne (RingHom.ext fun a => ?_)
  let a' : 𝓞 E := IsCMField.ringOfIntegersComplexConj E a
  have ha : (a' : E) = IsCMField.complexConj E (a : E) := rfl
  have e := adj_herm R a a' ha y x
  rw [mem_eigSp_iff.1 hy a, mem_eigSp_iff.1 hx a', star_smul, mulVec_smul, smul_dotProduct, dotProduct_smul] at e
  have e2 : s a' = starRingEnd ℂ (s a) := by
    rw [← extEmb_apply s a', ← extEmb_apply s a]
    show extEmb s (a' : E) = starRingEnd ℂ (extEmb s (a : E))
    rw [ha, IsCMField.complexEmbedding_complexConj]
  have e3 : star (s a') = s a := by rw [e2]; exact Complex.conj_conj _
  rw [e3] at e
  exact (mul_right_cancel₀ h0 e).symm

end SheetDecomposition.Riem

namespace SheetDecomposition

theorem riemBasic : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (Ψ : Type) [Fintype Ψ] (R : RiemLat E g Λ), Function.Injective R.P ∧ Submodule.span ℝ (Set.range R.P) = ⊤ ∧ (∀ s : 𝓞 E →+* ℂ, (∀ x, eigComp R.B s x ∈ eigSp R.B s) ∧ (∀ x ∈ eigSp R.B s, eigComp R.B s x = x) ∧ (∀ (c : ℂ) x y, eigComp R.B s (c • x + y) = c • eigComp R.B s x + eigComp R.B s y) ∧ ∀ a x, eigComp R.B s (R.B a x) = s a • eigComp R.B s x) ∧ (∀ x, ∑ s : E →+* ℂ, eigComp R.B (s.comp (algebraMap (𝓞 E) E)) x = x) ∧ ∀ s s' : 𝓞 E →+* ℂ, s ≠ s' → ∀ x ∈ eigSp R.B s, ∀ y ∈ eigSp R.B s', R.ip x y = 0 := by
  intro E _ _ _ g Λ _ _ Ψ _ R
  refine ⟨Riem.inj R, Riem.span_top R, fun s => ?_, Riem.sum_eigComp R.B, Riem.orth R⟩
  obtain ⟨p, h₁, h₂, h₃, h₄⟩ := Riem.exists_proj R.B s
  simp only [h₁]
  exact ⟨h₂, h₃, fun c x y => by rw [map_add, map_smul], h₄⟩

end SheetDecomposition
