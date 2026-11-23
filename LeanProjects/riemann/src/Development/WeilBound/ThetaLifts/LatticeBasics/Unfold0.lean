import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldB

noncomputable section

namespace GlobalTheory.ThK.Dbl

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

def Law (χ : Chr F E) (z : ℂ) (f : G2 σ Y → ℂ) : Prop :=
  ∀ p t x, IsPar p t → f (p * x) = (χ (Matrix.GeneralLinearGroup.det t) : ℂ) *
    ((absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) : ℂ) ^ z * f x

variable {χ : Chr F E} {z : ℂ} {f : G2 σ Y → ℂ} {e : UA σ Y.J × UA σ Y.J →* G2 σ Y}

theorem Law.rat (h : Law χ z f) (hχ : IsHecke F E χ) {p : G2 σ Y} (a : p ∈ par2 σ Y) (b : p ∈ rat2 σ Y) (x) : f (p * x) = f x := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 a
  obtain ⟨T, hT⟩ := par_rat ht b
  obtain ⟨u, hu⟩ := det_rat hT
  rw [h p t x ht, hu, hχ.2, GlobalTheory.Doubling.absE_inclR]; simp

theorem Law.diag (h : Law χ z f) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) (g : UA σ Y.J) (x) :
    f (e (g, g) * x) * detInv χ g = f x := by
  rw [h _ _ x (he g g).par, absE_det hJ, detInv, mul_right_comm]; simp

theorem Law.hasSum (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h'))) {x v}
    (hs : HasSum (eisTerm f x) v) : HasSum (fun δ : ratU σ Y.J => f (e (1, δ) * x)) v := by
  let i : ratU σ Y.J → Quotient (QuotientGroup.rightRel ((par2 σ Y).subgroupOf (rat2 σ Y))) :=
    fun δ => Quotient.mk _ ⟨e (1, δ), (he _ _).rat (one_mem _) δ.2⟩
  have hi : Function.Bijective i := by
    refine ⟨fun δ δ' h => ?_, fun q => ?_⟩
    · obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 (Subgroup.mem_subgroupOf.1 (QuotientGroup.rightRel_apply.1 (Quotient.exact (s := QuotientGroup.rightRel
        ((par2 σ Y).subgroupOf (rat2 σ Y))) h)))
      change IsPar (e (1, δ') * (e (1, δ))⁻¹) t at ht
      rw [← map_inv, ← map_mul, isPar_iff, he] at ht
      simp only [diagCols, Matrix.fromBlocks_mul_fromRows, Matrix.fromRows_mul, Matrix.mul_one, Matrix.zero_mul, add_zero, zero_add,
        Matrix.one_mul] at ht
      obtain ⟨a, b⟩ := Matrix.fromRows_inj ht
      have : (1 : UA σ Y.J) * 1⁻¹ = δ'.1 * δ.1⁻¹ := Subtype.ext (Units.ext (a.trans b.symm))
      rw [inv_one, mul_one, eq_mul_inv_iff_mul_eq, one_mul] at this
      exact Subtype.ext this
    · obtain ⟨γ, rfl⟩ := Quotient.exists_rep q
      obtain ⟨δ, hδ, hp⟩ := orbit hJ (γ⁻¹).2
      refine ⟨⟨δ, hδ⟩, (Quotient.sound (QuotientGroup.rightRel_apply.2 (Subgroup.mem_subgroupOf.2 ?_))).symm⟩
      exact hp _ (he _ _)
  convert (Equiv.ofBijective i hi).hasSum_iff.2 hs using 2 with δ
  have := QuotientGroup.rightRel_apply.1 (Quotient.exact (i δ).out_eq)
  exact Eq.trans (by simp [mul_assoc]) (h.rat hχ this (mul_mem ((he _ _).rat (one_mem _) δ.2) (inv_mem (i δ).out.2)) _)

theorem Law.eis_inv (h : Law χ z f) (hχ : IsHecke F E χ) (hJ : Aniso σ Y.J) (he : ∀ h h', IsEmb h h' (e (h, h')))
    {Ê : G2 σ Y → ℂ} (hs : ∀ x, HasSum (eisTerm f x) (Ê x)) {γ δ : UA σ Y.J} (hγ : γ ∈ ratU σ Y.J) (hδ : δ ∈ ratU σ Y.J) (x) :
    Ê (e (γ, δ) * x) = Ê x := by
  refine (h.hasSum hχ hJ he (hs _)).unique ?_
  have := ((Equiv.mulLeft (⟨γ, hγ⟩ : ratU σ Y.J)⁻¹).trans (Equiv.mulRight ⟨δ, hδ⟩)).hasSum_iff.2 (h.hasSum hχ hJ he (hs x))
  convert this using 2 with η
  have := h.diag hJ he γ (e (1, γ⁻¹ * η * δ) * x)
  rw [detInv_rat hχ hγ, mul_one, ← mul_assoc, ← map_mul] at this
  rw [← mul_assoc, ← map_mul]
  simpa [mul_assoc] using this

theorem countable_ratU : Countable (ratU σ Y.J) := by
  haveI : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin n) (Fin n) E) := inferInstanceAs (Countable (Fin n → Fin n → E))
  haveI : Countable (GL (Fin n) E) := Units.val_injective.countable
  exact (Set.countable_range (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)))).preimage
    Subtype.val_injective

theorem unfold0 : Unfold0 := by
  intro F E _ _ _ _ _ σ B n Y r s hB hY h0 χ e hχ he f Ê z _ _ hs hf μ D hμ hD hi φ hφ h
  have hJ := aniso_of hB hY h0
  haveI := countable_ratU (σ := σ) (Y := Y)
  haveI : BorelSpace (UA σ Y.J) := ⟨rfl⟩
  haveI := GlobalTheory.Doubling.isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  obtain ⟨C, hC⟩ := hφ.2.2 0
  let k : UA σ Y.J → ℂ := fun g => f (e (1, g)) * (detInv χ g * φ (h * g))
  have ik : Integrable k μ := hi.mul_bdd (c := C)
    ((continuous_detInv hχ).mul (hφ.1.comp (continuous_const_mul h))).aestronglyMeasurable
    (.of_forall fun g => by simpa [norm_detInv] using hC (h * g))
  have := An.unfold hD (ik.comp_mul_left h⁻¹)
  rw [integral_mul_left_eq_self k] at this
  simp only [mul_assoc]
  refine Eq.trans (integral_congr_ae (.of_forall fun g => ?_)) this
  refine (((Law.hasSum hf hχ hJ he (hs _)).mul_right _).tsum_eq.symm).trans (tsum_congr fun δ => ?_)
  simp only [k]
  rw [← Law.diag hf hJ he h (e _), ← map_mul, ← map_mul, detInv_mul, detInv_mul, detInv_rat hχ δ.2, mul_inv_cancel_left, hφ.2.1 _ δ.2]
  have : detInv χ h * detInv χ h⁻¹ = 1 := by rw [← detInv_mul, mul_inv_cancel, detInv_rat hχ (one_mem _)]
  simp only [Prod.mk_mul_mk, one_mul, mul_one, mul_inv_cancel_left]
  linear_combination (-(f (e (h, δ * g)) * detInv χ g * φ g)) * this

end GlobalTheory.ThK.Dbl

end
