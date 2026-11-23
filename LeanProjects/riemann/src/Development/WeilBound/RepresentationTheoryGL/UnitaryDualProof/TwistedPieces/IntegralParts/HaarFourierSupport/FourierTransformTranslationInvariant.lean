import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.HaarFourierSupport.PartialFourierFirstCoordinates

noncomputable section

set_option linter.unusedSectionVars false

open Matrix MeasureTheory GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil ValuativeRel

namespace PositivityTheory.RgUd.TP.Nil.Four

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

def Tm (m : ℕ) (t : kˣ) : GL (Fin m) k := Units.map (Matrix.scalar (Fin m) : k →+* Matrix (Fin m) (Fin m) k) t

theorem Tm_mulVec {m : ℕ} (t : kˣ) (u : Fin m → k) : (Tm m t).val *ᵥ u = (t : k) • u := by
  funext i
  simp [Tm, Matrix.scalar_apply, mulVec_diagonal]

theorem Tm_det {m : ℕ} (t : kˣ) : Matrix.GeneralLinearGroup.det (Tm m t) = t ^ m := by
  ext
  simp [Tm, Matrix.scalar_apply, Matrix.GeneralLinearGroup.val_det_apply, det_diagonal]

variable {τ : Matrix (Fin n) (Fin n) k →ₗ[k] k} {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}
  [MeasurableSpace k] [BorelSpace k] (ψ : AddChar k Circle) (ν : Measure k) [ν.IsAddHaarMeasure]
  (h : Hyp τ Z)

include h

def phi0 (f : Sp k n → ℂ) : Sp k n → ℂ :=
  fun p => GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q)) (Hb h p)

theorem characteristic_function_integral_apply (f : Sp k n → ℂ) (p : Sp k n) :
    phi0 ψ ν h f p = ∫ u, f (p.1 - Pr τ Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D τ Z p.1) : ℂ) ∂(Measure.pi fun _ => ν) := by
  simp only [phi0, GlobalTheory.SplitDict.pf, real_test_function_apply]
  rfl

theorem fourier_transform_on_base (f : Sp k n → ℂ) {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (v : Fin n → k) :
    phi0 ψ ν h f (x, v) = ∫ u, f (E Z u, v) * (ψ (u ⬝ᵥ D τ Z x) : ℂ) ∂(Measure.pi fun _ => ν) := by
  rw [characteristic_function_integral_apply]
  simp only [Pr_of_mem h hx, sub_self, zero_add]

theorem test_vector_mem_schwartz_bruhat {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) :
    phi0 ψ ν h f ∈ supportedIn (Set.univ : Set (Sp k n)) := by
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).1 hf.1
  have h2 := GlobalTheory.SplitDict.pf_mem_SB (Measure.pi fun _ : Fin (dd Z) => ν) hc h1
  exact ⟨(GlobalTheory.SplitDict.bijOn_comp (Hb h)).1 h2, Set.subset_univ _⟩

theorem integrable_slice (hψ : Continuous ψ) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (Set.univ : Set (Sp k n)))
    (p : Sp k n) :
    Integrable (fun u => f (p.1 - Pr τ Z p.1 + E Z u, p.2) * (ψ (u ⬝ᵥ D τ Z p.1) : ℂ)) (Measure.pi fun _ => ν) := by
  obtain ⟨⟨hl, hcs⟩, -⟩ := hf
  have hf' : f ∈ SB (Sp k n) := ⟨hl, hcs⟩
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).mapsTo hf'
  have h2 : (fun u : Fin (dd Z) → k => f (p.1 - Pr τ Z p.1 + E Z u, p.2)) ∈ SB (Fin (dd Z) → k) := by
    have := GlobalTheory.SplitDict.slice_mem_SB h1 (Hb h p).1
    convert this using 1
    funext u
    simp only [real_test_function_apply]
    rfl
  obtain ⟨hl2, hcs2⟩ := h2
  have hc2 : Continuous fun u : Fin (dd Z) → k => (ψ (u ⬝ᵥ D τ Z p.1) : ℂ) :=
    continuous_subtype_val.comp (hψ.comp (continuous_id.dotProduct continuous_const))
  exact (hl2.continuous.mul hc2).integrable_of_hasCompactSupport hcs2.mul_right

def phiS (hψ : Continuous ψ) : (supportedIn (Set.univ : Set (Sp k n))) →ₗ[ℂ] (Sp k n → ℂ) where
  toFun f := phi0 ψ ν h f.1
  map_add' f g := by
    funext p
    simp only [Submodule.coe_add, Pi.add_apply, characteristic_function_integral_apply, add_mul]
    exact integral_add (integrable_slice ψ ν h hψ f.2 p) (integrable_slice ψ ν h hψ g.2 p)
  map_smul' c f := by
    funext p
    simp only [Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, characteristic_function_integral_apply, mul_assoc, RingHom.id_apply]
    exact integral_const_mul _ _

theorem fourier_transform_support (f : Sp k n → ℂ) (hf0 : ∀ q ∈ Bz Z ×ˢ (Set.univ : Set (Fin n → k)), f q = 0) {p : Sp k n}
    (hp : p ∈ Bz Z ×ˢ (Set.univ : Set (Fin n → k))) : phi0 ψ ν h f p = 0 := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp.1
  rw [fourier_transform_on_base ψ ν h f hx]
  have h0 : ∀ u, f (E Z u, v) = 0 := fun u => hf0 _ ⟨E_mem Z u, Set.mem_univ _⟩
  simp [h0]

theorem fourier_transform_equivariant {g : GL (Fin n) k} (hg : g ∈ Gz Z) (f : Sp k n → ℂ) {p : Sp k n} (hp : p.1 ∈ Bz Z) :
    phi0 ψ ν h (fun q => f (act g q)) p = phi0 ψ ν h f (act g p) := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp
  obtain ⟨u0, rfl⟩ := exists_E Z hx
  have hy : (g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) ∈ Bz Z := by
    rw [← E_adL hg]
    exact E_mem Z _
  change _ = phi0 ψ ν h f ((g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k),
    (g : Matrix (Fin n) (Fin n) k) *ᵥ v)
  rw [fourier_transform_on_base ψ ν h _ (E_mem Z u0), fourier_transform_on_base ψ ν h f hy]
  have key := GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν (adU h hg)
    (fun u => f (E Z u, (g : Matrix (Fin n) (Fin n) k) *ᵥ v) *
      (ψ (u ⬝ᵥ D τ Z ((g : Matrix (Fin n) (Fin n) k) * E Z u0 * ((g⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k))) : ℂ))
  have hn : nabs k (Matrix.GeneralLinearGroup.det (adU h hg)) = 1 := by
    simp [nabs, distribHaarChar_adU h hg]
  rw [hn, inv_one, one_smul] at key
  rw [← key]
  congr 1
  funext u
  have hv : ((adU h hg : GL (Fin (dd Z)) k) : Matrix (Fin (dd Z)) (Fin (dd Z)) k) *ᵥ u = adL hg u := adM_mulVec hg u
  simp only [hv, E_adL hg, dot_conj h hg u (E_mem Z u0)]
  rfl

theorem fourier_transform_preserves_compact {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ} (hf : f ∈ supportedIn (UU : Set (Sp k n))) :
    phi0 ψ ν h f ∈ supportedIn (UU : Set (Sp k n)) := by
  refine ⟨(test_vector_mem_schwartz_bruhat ψ ν h hc ⟨hf.1, Set.subset_univ _⟩).1, fun p hp => ?_⟩
  by_contra h0
  have h0' : p.2 = 0 := by simpa [UU] using h0
  apply hp
  rw [characteristic_function_integral_apply]
  have : ∀ u, f (p.1 - Pr τ Z p.1 + E Z u, p.2) = 0 := fun u => by
    by_contra hne
    exact (hf.2 hne) h0'
  simp [this]

omit h [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in

def Refl (τ : Matrix (Fin n) (Fin n) k →ₗ[k] k) (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (p : Sp k n) : Sp k n :=
  (p.1 - (2 : k) • Pr τ Z p.1, p.2)

omit [MeasurableSpace k] [BorelSpace k] [ν.IsAddHaarMeasure] in
theorem Refl_Refl (p : Sp k n) : Refl τ Z (Refl τ Z p) = p := by
  obtain ⟨x, v⟩ := p
  have hP : Pr τ Z (Pr τ Z x) = Pr τ Z x := Pr_E h _
  have hs : Pr τ Z (x - (2 : k) • Pr τ Z x) = Pr τ Z x - (2 : k) • Pr τ Z (Pr τ Z x) := by
    rw [sub_eq_add_neg, Pr_add, ← neg_smul, Pr_smul, neg_smul, ← sub_eq_add_neg]
  simp only [Refl, Prod.mk.injEq, and_true]
  rw [hs, hP]
  module

theorem fourier_transform_involution {c : kˣ} (hc : HasConductor ψ c) {f : Sp k n → ℂ}
    (hf : f ∈ supportedIn (Set.univ : Set (Sp k n))) (p : Sp k n) :
    phi0 ψ ν h (phi0 ψ ν h f) p =
      ((distribHaarChar k (Matrix.GeneralLinearGroup.det (Gu h)) : ℝ) : ℂ)⁻¹ *
        ((((ν.real (𝒪[k] : Set k) ^ 2 * nabs k c) ^ (dd Z) : ℝ)) : ℂ) * f (Refl τ Z p) := by
  obtain ⟨⟨hl, hcs⟩, -⟩ := hf
  have hf' : f ∈ SB (Sp k n) := ⟨hl, hcs⟩
  have h1 : (fun q => f (F1 h q)) ∈ SB (TT τ Z × (Fin (dd Z) → k)) :=
    (GlobalTheory.SplitDict.bijOn_comp (F1 h)).mapsTo hf'
  have e1 : ∀ q, phi0 ψ ν h f (F1 h q) =
      GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q)) (q.1, G τ Z *ᵥ q.2) := by
    intro q
    simp only [phi0, partial_fourier_first_coordinates]
  have e2 := pf_G h ψ ν (GlobalTheory.SplitDict.pf ψ (Measure.pi fun _ : Fin (dd Z) => ν) (fun q => f (F1 h q))) (Hb h p)
  have e3 := GlobalTheory.SplitDict.pf_pf (ψ := ψ) ν hc h1 ((Hb h p).1, (G τ Z)⁻¹ *ᵥ (Hb h p).2)
  have e4 : F1 h ((Hb h p).1, -((G τ Z)⁻¹ *ᵥ (Hb h p).2)) = Refl τ Z p := by
    rw [real_test_function_apply]
    show (p.1 - Pr τ Z p.1 + E Z (-((G τ Z)⁻¹ *ᵥ D τ Z p.1)), p.2) = (p.1 - (2 : k) • Pr τ Z p.1, p.2)
    rw [E_neg]
    show (p.1 - Pr τ Z p.1 + -Pr τ Z p.1, p.2) = _
    congr 1
    module
  show GlobalTheory.SplitDict.pf ψ _ (fun q => phi0 ψ ν h f (F1 h q)) (Hb h p) = _
  simp only [e1]
  calc _ = _ := e2
    _ = _ := by
      rw [e3]
      simp only [e4, Fintype.card_fin]
      ring

theorem fourier_transform_homothety (t : kˣ) (f : Sp k n → ℂ) {p : Sp k n} (hp : p.1 ∈ Bz Z) :
    phi0 ψ ν h f (PositivityTheory.RgUd.TP.Nil.hom t p) =
      ((((nabs k t)⁻¹ ^ dd Z : ℝ)) : ℂ) * phi0 ψ ν h (fun q => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ q)) p := by
  obtain ⟨x, v⟩ := p
  have hx : x ∈ Bz Z := hp
  have htx : (t : k) • x ∈ Bz Z := by
    intro a ha
    rw [mul_smul_comm, smul_mul_assoc, hx a ha]
  change phi0 ψ ν h f ((t : k) • x, v) = _
  rw [fourier_transform_on_base ψ ν h f htx, fourier_transform_on_base ψ ν h _ hx]
  have key := GlobalTheory.SplitWeil.integral_comp_mulVec_eq_smul ν (Tm (dd Z) t)
    (fun u => f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ (E Z u, v)) * (ψ (u ⬝ᵥ D τ Z x) : ℂ))
  rw [Tm_det] at key
  simp only [Tm_mulVec] at key
  have hn : nabs k (t ^ dd Z) = nabs k t ^ dd Z := by
    simp [nabs, map_pow]
  have hl : ∀ u : Fin (dd Z) → k, f (PositivityTheory.RgUd.TP.Nil.hom t⁻¹ (E Z ((t : k) • u), v)) * (ψ (((t : k) • u) ⬝ᵥ D τ Z x) : ℂ) =
      f (E Z u, v) * (ψ (u ⬝ᵥ D τ Z ((t : k) • x)) : ℂ) := by
    intro u
    simp only [PositivityTheory.RgUd.TP.Nil.hom, E_smul, smul_smul, Units.inv_mul, one_smul, D_smul, smul_dotProduct,
      dotProduct_smul]
  simp only [hl] at key
  rw [key, hn, Complex.real_smul, inv_pow]

theorem fourier_transform_translation_invariant (hZ : CR Z) (f : Sp k n → ℂ) {z : Matrix (Fin n) (Fin n) k} (hz : z ∈ Z)
    {x : Matrix (Fin n) (Fin n) k} (hx : x ∈ Bz Z) (hzx : τ (z * x) = 0) (v : Fin n → k) :
    phi0 ψ ν h (fun q => f (q.1 + z, q.2)) (x, v) = phi0 ψ ν h f (x, v) := by
  have hzB : z ∈ Bz Z := fun a ha => hZ.1 a ha z hz
  obtain ⟨uz, rfl⟩ := exists_E Z hzB
  rw [fourier_transform_on_base ψ ν h _ hx, fourier_transform_on_base ψ ν h f hx]
  have h0 : uz ⬝ᵥ D τ Z x = 0 := by
    rw [dot_D]
    exact hzx
  have key := MeasureTheory.integral_add_right_eq_self (μ := Measure.pi fun _ : Fin (dd Z) => ν)
    (fun w => f (E Z w, v) * (ψ ((w - uz) ⬝ᵥ D τ Z x) : ℂ)) uz
  simp only [add_sub_cancel_right, sub_dotProduct, h0, sub_zero, E_add] at key
  exact key

end PositivityTheory.RgUd.TP.Nil.Four
