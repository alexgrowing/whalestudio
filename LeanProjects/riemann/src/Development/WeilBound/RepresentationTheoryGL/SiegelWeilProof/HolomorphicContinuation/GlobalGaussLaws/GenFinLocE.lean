import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GenFinLocD

noncomputable section

set_option linter.unusedSectionVars false

open scoped TensorProduct
open IsDedekindDomain NumberField GlobalTheory.AdelicU Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace PositivityTheory.Rg.Sw.Glob.GenFinLocAH

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def sigI (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) : intLoc F E v →+* intLoc F E v :=
  (sigR (Fv F v) σ).restrict (intLoc F E v) (intLoc F E v) (fun _ hx => sigR_mem_intLoc σ hx)

theorem sigI_coe (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    ((sigI σ v z : intLoc F E v) : Fv F v ⊗[F] E) = sigR (Fv F v) σ z := rfl

theorem sigR_sigR (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (R : Type) [CommRing R] [Algebra F R] (z : R ⊗[F] E) :
    sigR R σ (sigR R σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add y z hy hz => simp only [map_add, hy, hz]

theorem sigI_sigI (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (v : HeightOneSpectrum (𝓞 F)) (z : intLoc F E v) :
    sigI σ v (sigI σ v z) = z := Subtype.ext (sigR_sigR σ hσ (Fv F v) (z : Fv F v ⊗[F] E))

theorem fixed_eq_tmul (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : Fv F v ⊗[F] E) (hz : sigR (Fv F v) σ z = z) : ∃ a : Fv F v, z = a ⊗ₜ[F] (1 : E) := by
  let φ : E →ₗ[F] E := σ.toLinearMap - LinearMap.id
  have hex : Function.Exact (Algebra.linearMap F E) φ := by
    intro y
    constructor
    · intro hy
      have : σ y = y := by have := hy; simp only [φ, LinearMap.sub_apply, AlgHom.toLinearMap_apply, LinearMap.id_apply,
        sub_eq_zero] at this; exact this
      obtain ⟨c, hc⟩ := (hfix y).1 this
      exact ⟨c, hc⟩
    · rintro ⟨c, rfl⟩
      simp [φ]
  have hex' := Module.Flat.lTensor_exact (Fv F v) hex
  have hφ : φ.lTensor (Fv F v) z = 0 := by
    have key : ∀ w : Fv F v ⊗[F] E, φ.lTensor (Fv F v) w = sigR (Fv F v) σ w - w := by
      intro w
      induction w using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => simp [φ, sigR, TensorProduct.tmul_sub]
      | add y w hy hw => rw [map_add, hy, hw, map_add]; abel
    rw [key, hz, sub_self]
  obtain ⟨w, hw⟩ := (hex' z).1 hφ
  refine ⟨TensorProduct.rid F (Fv F v) w, ?_⟩
  rw [← hw]
  clear hw
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul a c =>
    simp only [LinearMap.lTensor_tmul, Algebra.linearMap_apply, TensorProduct.rid_tmul]
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
  | add y w hy hw => rw [map_add, hy, hw, map_add, TensorProduct.add_tmul]

theorem mem_of_tmul_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ⊗ₜ[F] (1 : E) ∈ intLoc F E v) :
    a ∈ v.adicCompletionIntegers F := by
  have h1 := absFin_le_one_of_mem_intLoc h
  rw [absFin_tmul_one] at h1
  exact (Valued.toNormedField.norm_le_one_iff).1 (by exact_mod_cast h1)

theorem tmul_one_mem (v : HeightOneSpectrum (𝓞 F)) (a : Fv F v) (h : a ∈ v.adicCompletionIntegers F) :
    a ⊗ₜ[F] (1 : E) ∈ intLoc F E v := by
  simpa using tmul_mem_intLoc (E := E) h (1 : 𝓞 E)

theorem nontrivial_intLoc (v : HeightOneSpectrum (𝓞 F)) : Nontrivial (intLoc F E v) := by
  refine ⟨⟨0, 1, fun h => ?_⟩⟩
  have h' : ((0 : intLoc F E v) : Fv F v ⊗[F] E) = ((1 : intLoc F E v) : Fv F v ⊗[F] E) := congrArg Subtype.val h
  have := congrArg (absFin F v) h'
  rw [ZeroMemClass.coe_zero, OneMemClass.coe_one, absFin_zero, absFin_one] at this
  exact zero_ne_one this

theorem orbit_abs {R : Type} [CommRing R] (s : R →+* R) (hss : ∀ z, s (s z) = z)
    (hloc : ∀ z, s z = z → IsUnit z ∨ IsUnit (1 - z)) (𝔪 𝔫 : Ideal R) (h𝔪 : 𝔪.IsMaximal) (h𝔫 : 𝔫.IsMaximal) :
    𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap s := by
  by_contra hne
  rw [not_or] at hne
  obtain ⟨hn1, hn2⟩ := hne
  have hsurj : Function.Surjective s := fun y => ⟨s y, hss y⟩
  have hcc : ∀ I : Ideal R, (I.comap s).comap s = I := by
    intro I; ext z; rw [Ideal.mem_comap, Ideal.mem_comap, hss]
  have hm' : (𝔪.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn' : (𝔫.comap s).IsMaximal := Ideal.comap_isMaximal_of_surjective s hsurj
  have hn3 : 𝔫.comap s ≠ 𝔪 := by
    intro h; apply hn2; rw [← h, hcc]
  have hn4 : 𝔫.comap s ≠ 𝔪.comap s := by
    intro h; apply hn1; rw [← hcc 𝔫, h, hcc]
  have c1 : 𝔪 ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 h𝔫 (Ne.symm hn1)
  have c2 : 𝔪 ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne h𝔪 hn' (Ne.symm hn3)
  have c3 : 𝔪.comap s ⊔ 𝔫 = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' h𝔫 (Ne.symm hn2)
  have c4 : 𝔪.comap s ⊔ 𝔫.comap s = ⊤ := Ideal.IsMaximal.coprime_of_ne hm' hn' (Ne.symm hn4)
  have d1 : 𝔪 ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c1).trans c2
  have d2 : 𝔪.comap s ⊔ 𝔫 * 𝔫.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left c3).trans c4
  have e1 : 𝔫 * 𝔫.comap s ⊔ 𝔪 = ⊤ := by rw [sup_comm]; exact d1
  have e2 : 𝔫 * 𝔫.comap s ⊔ 𝔪.comap s = ⊤ := by rw [sup_comm]; exact d2
  have d3 : 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s = ⊤ := (Ideal.sup_mul_eq_of_coprime_left e1).trans e2
  have h1 : (1 : R) ∈ 𝔫 * 𝔫.comap s ⊔ 𝔪 * 𝔪.comap s := by rw [d3]; exact Submodule.mem_top
  obtain ⟨y, hy, x, hx, hxy⟩ := Submodule.mem_sup.1 h1
  have hxm : x ∈ 𝔪 := (Ideal.mul_le_left : 𝔪 * 𝔪.comap s ≤ 𝔪) hx
  have hyn : y ∈ 𝔫 := (Ideal.mul_le_left : 𝔫 * 𝔫.comap s ≤ 𝔫) hy
  have hyn'' : y ∈ 𝔫.comap s := (Ideal.mul_le_right : 𝔫 * 𝔫.comap s ≤ 𝔫.comap s) hy
  have hyn' : s y ∈ 𝔫 := Ideal.mem_comap.1 hyn''
  have hzm : x * s x ∈ 𝔪 := Ideal.mul_mem_right _ _ hxm
  have hfz : s (x * s x) = x * s x := by rw [map_mul, hss, mul_comm]
  have h1z : 1 - x * s x ∈ 𝔫 := by
    have hx' : x = 1 - y := by rw [← hxy]; ring
    have e : 1 - x * s x = y + s y - y * s y := by rw [hx', map_sub, map_one]; ring
    rw [e]
    exact Ideal.sub_mem _ (Ideal.add_mem _ hyn hyn') (Ideal.mul_mem_right _ _ hyn)
  rcases hloc _ hfz with hu | hu
  · exact h𝔪.ne_top (Ideal.eq_top_of_isUnit_mem _ hzm hu)
  · exact h𝔫.ne_top (Ideal.eq_top_of_isUnit_mem _ h1z hu)

theorem isUnit_tmul (v : HeightOneSpectrum (𝓞 F)) (u : (v.adicCompletionIntegers F)ˣ) :
    IsUnit (⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :
      intLoc F E v) := by
  refine ⟨⟨_, ⟨((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) ⊗ₜ[F] (1 : E),
    tmul_one_mem v _ (u⁻¹ : (v.adicCompletionIntegers F)ˣ).1.2⟩, Subtype.ext ?_, Subtype.ext ?_⟩, rfl⟩
  · show ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) * (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) :
      v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.mul_inv]; rfl
  · show (((u⁻¹ : (v.adicCompletionIntegers F)ˣ) : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) *
      ((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E) = 1
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, ← Subring.coe_mul, Units.inv_mul]; rfl

theorem fixed_local (σ : E →ₐ[F] E) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range) (v : HeightOneSpectrum (𝓞 F))
    (z : intLoc F E v) (hz : sigI σ v z = z) : IsUnit z ∨ IsUnit (1 - z) := by
  obtain ⟨a, ha⟩ := fixed_eq_tmul σ hfix v (z : Fv F v ⊗[F] E) (by rw [← sigI_coe]; exact congrArg Subtype.val hz)
  have haO : a ∈ v.adicCompletionIntegers F := mem_of_tmul_mem v a (ha ▸ z.2)
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨a, haO⟩ : v.adicCompletionIntegers F) with hu | hu
  · left
    obtain ⟨u, hu⟩ := hu
    have e : z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ :=
      Subtype.ext (by rw [ha, hu])
    rw [e]; exact isUnit_tmul v u
  · right
    obtain ⟨u, hu⟩ := hu
    have e : 1 - z = ⟨((u : v.adicCompletionIntegers F) : Fv F v) ⊗ₜ[F] (1 : E), tmul_one_mem v _ (u : v.adicCompletionIntegers F).2⟩ := by
      apply Subtype.ext
      rw [hu]
      show (1 : Fv F v ⊗[F] E) - (z : Fv F v ⊗[F] E) = (1 - a) ⊗ₜ[F] (1 : E)
      rw [ha, TensorProduct.sub_tmul, Algebra.TensorProduct.one_def]
    rw [e]; exact isUnit_tmul v u

theorem orbit (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (hfix : ∀ x, σ x = x ↔ x ∈ (algebraMap F E).range)
    (v : HeightOneSpectrum (𝓞 F)) :
    ∃ 𝔪 : Ideal (intLoc F E v), 𝔪.IsMaximal ∧ ∀ 𝔫 : Ideal (intLoc F E v), 𝔫.IsMaximal → 𝔫 = 𝔪 ∨ 𝔫 = 𝔪.comap (sigI σ v) := by
  have := nontrivial_intLoc (E := E) v
  obtain ⟨𝔪, h𝔪⟩ := Ideal.exists_maximal (intLoc F E v)
  exact ⟨𝔪, h𝔪, fun 𝔫 h𝔫 => orbit_abs (sigI σ v) (sigI_sigI σ hσ v) (fixed_local σ hfix v) 𝔪 𝔫 h𝔪 h𝔫⟩

end PositivityTheory.Rg.Sw.Glob.GenFinLocAH
