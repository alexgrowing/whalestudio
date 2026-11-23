import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Flat

namespace PositivityTheory.Xgn.LineLatticeVectorBundle

theorem alt_det {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v : Fin p → E) (c : Matrix (Fin p) (Fin p) Ω) :
    f (fun i => ∑ j, c i j • v j) = c.det • f v := by
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff Ω]
  intro φ
  have h := AlternatingMap.eq_smul_basis_det (Pi.basisFun Ω (Fin p))
    (φ.compAlternatingMap (f.compLinearMap (Fintype.linearCombination Ω v)))
  have h2 := congrArg (fun g => g (fun i => c i)) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.compLinearMap_apply,
    AlternatingMap.smul_apply, Pi.basisFun_det_apply, Pi.basisFun_apply,
    Fintype.linearCombination_apply_single, one_smul, smul_eq_mul] at h2
  simp only [Fintype.linearCombination_apply] at h2
  rw [map_sub, map_smul, h2, smul_eq_mul, mul_comm, sub_eq_zero]
  rfl

theorem line_of_span {Ω E N : Type} [Field Ω] [AddCommGroup E] [Module Ω E] [AddCommGroup N] [Module Ω N] {p : ℕ}
    (f : E [⋀^Fin p]→ₗ[Ω] N) (v v' : Fin p → E)
    (h : Submodule.span Ω (Set.range v') = Submodule.span Ω (Set.range v)) : ∃ c : Ω, f v' = c • f v := by
  have : ∀ i, ∃ c : Fin p → Ω, ∑ j, c j • v j = v' i := fun i =>
    (Submodule.mem_span_range_iff_exists_fun Ω).1 (h ▸ Submodule.subset_span ⟨i, rfl⟩)
  choose c hc using this
  refine ⟨(Matrix.of c).det, ?_⟩
  rw [← alt_det]
  congr 1
  funext i
  exact (hc i).symm

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E]
  {ξ : Spec (CommRingCat.of Ω) ⟶ X}

theorem wedge_frame {A : Lat ξ E} {p : ℕ} {v : Fin p → E} {x : Cpt ξ} (h : A.IsFrameAt v x) :
    A.wedge p x = Submodule.span (regAt ξ x) {exteriorPower.ιMulti Ω p v} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro w ⟨b, hb, rfl⟩
    have : ∀ i, ∃ c : Fin p → regAt ξ x, ∑ j, c j • v j = b i := fun i =>
      (Submodule.mem_span_range_iff_exists_fun _).1 (h.2 ▸ hb i)
    choose c hc using this
    refine Submodule.mem_span_singleton.2 ⟨(Matrix.of c).det, ?_⟩
    have e := alt_det (exteriorPower.ιMulti Ω p) v ((regAt ξ x).subtype.mapMatrix (Matrix.of c))
    rw [← RingHom.map_det] at e
    refine e.symm.trans ?_
    congr 1
    funext i
    exact hc i
  · refine Submodule.span_mono ?_
    rintro w rfl
    exact ⟨v, fun i => h.2 ▸ Submodule.subset_span ⟨i, rfl⟩, rfl⟩

theorem span_unit {x : Cpt ξ} {u : Ω} (hu : unitAt ξ x u) (e : E) :
    Submodule.span (regAt ξ x) {u • e} = Submodule.span (regAt ξ x) {e} := by
  refine le_antisymm ?_ ?_ <;> rw [Submodule.span_singleton_le_iff_mem, Submodule.mem_span_singleton]
  · exact ⟨⟨u, hu.2.1⟩, rfl⟩
  · exact ⟨⟨u⁻¹, hu.2.2⟩, by
      change u⁻¹ • u • e = e
      rw [inv_smul_smul₀ hu.1]⟩

theorem coeff_unit {x : Cpt ξ} {a : E} (ha : a ≠ 0) {α α' : Ω} (h0 : α ≠ 0)
    (h : Submodule.span (regAt ξ x) {α • a} = Submodule.span (regAt ξ x) {α' • a}) :
    ∃ u, unitAt ξ x u ∧ α = u * α' := by
  obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) h
  exact ⟨u, hu, smul_left_injective Ω ha (by simpa [mul_smul] using e)⟩

theorem on_line {A : Lat ξ E} {T : Set (Cpt ξ)} {p : ℕ} {V : Submodule Ω E} (hA : A.IsVBOn T p V)
    {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} (hx : x ∈ T) {α : Ω} (h0 : α ≠ 0)
    (h : A.wedge p x = Submodule.span (regAt ξ x) {α • a}) (v : Fin p → E)
    (hv : Submodule.span Ω (Set.range v) = V) : ∃ γ : Ω, γ ≠ 0 ∧ exteriorPower.ιMulti Ω p v = γ • a := by
  obtain ⟨U, hU, b, hb, hf⟩ := hA x hx
  have h1 := wedge_frame (hf x hx hU)
  obtain ⟨u, -, e⟩ := ZUnit.exists_of_span_eq (smul_ne_zero h0 ha) (h.symm.trans h1)
  obtain ⟨c, hc⟩ := line_of_span (exteriorPower.ιMulti Ω p) v b (hb.trans hv.symm)
  rw [hc, smul_smul] at e
  have huc : u * c ≠ 0 := by
    intro h'
    rw [h', zero_smul] at e
    exact smul_ne_zero h0 ha e
  refine ⟨(u * c)⁻¹ * α, mul_ne_zero (inv_ne_zero huc) h0, ?_⟩
  rw [mul_smul, e, inv_smul_smul₀ huc]

section
variable {A B : Lat ξ E} {p q : ℕ} {a : ⋀[Ω]^p E} {b : ⋀[Ω]^q E} {x : Cpt ξ}

theorem gen_of_coeff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) :
    (lineLat A B p q a b).IsGenAt x f⁻¹ := by
  have h' := h
  obtain ⟨α, β, hα, hβ, hA, hB, e⟩ := h
  have hf : f ≠ 0 := by
    rintro rfl
    exact hβ (by rw [← e, zero_mul])
  refine ⟨inv_ne_zero hf, le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)⟩
  · rintro t ⟨g, ⟨α', β', hα', hβ', hA', hB', e'⟩, rfl⟩
    obtain ⟨u, hu, eu⟩ := coeff_unit ha hα' (hA'.symm.trans hA)
    obtain ⟨w, hw, ew⟩ := coeff_unit hb hβ (hB.symm.trans hB')
    refine Submodule.mem_span_singleton.2 ⟨⟨u * w, mul_mem hu.2.1 hw.2.1⟩, ?_⟩
    change u * w * f⁻¹ = g⁻¹
    have hg : g ≠ 0 := by
      rintro rfl
      exact hβ' (by rw [← e', zero_mul])
    have key : f * α = (w * g * u) * α := by rw [e, ew, ← e', eu]; ring
    have key2 : f = w * g * u := mul_right_cancel₀ hα key
    have := hu.1
    have := hw.1
    rw [key2]
    field_simp
  · rintro t rfl
    exact ⟨f, h', rfl⟩

theorem gen_iff (ha : a ≠ 0) (hb : b ≠ 0) {f : Ω} (h : IsCoeffAt A B p q a b x f) (t : Ω) :
    (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹ := by
  constructor
  · rintro ⟨ht, hL⟩
    refine ⟨ht, ?_⟩
    obtain ⟨u, hu, e⟩ := ZUnit.exists_of_span_eq ht (hL.symm.trans (gen_of_coeff ha hb h).2)
    obtain ⟨α, β, hα, hβ, hA, hB, e'⟩ := h
    refine ⟨u * α, β, mul_ne_zero hu.1 hα, hβ, ?_, hB, ?_⟩
    · rw [mul_smul, span_unit hu, hA]
    · have := hu.1
      rw [e, ← e', smul_eq_mul, mul_inv, inv_inv]
      field_simp
  · rintro ⟨-, h⟩
    simpa using gen_of_coeff ha hb h

theorem coeff_of_frames {v : Fin p → E} {w : Fin q → E} {α β : Ω} (hv : A.IsFrameAt v x) (hw : B.IsFrameAt w x)
    (hα : α ≠ 0) (hβ : β ≠ 0) (ev : exteriorPower.ιMulti Ω p v = α • a)
    (ew : exteriorPower.ιMulti Ω q w = β • b) : IsCoeffAt A B p q a b x (α / β)⁻¹ :=
  ⟨α, β, hα, hβ, ev ▸ wedge_frame hv, ew ▸ wedge_frame hw, by field_simp⟩

end

theorem ne_zero_of_frames {A : Lat ξ E} {p : ℕ} {a : ⋀[Ω]^p E} (ha : a ≠ 0) {x : Cpt ξ} {v v' : Fin p → E}
    {α α' : Ω} (hv : A.IsFrameAt v x) (hv' : A.IsFrameAt v' x) (e : exteriorPower.ιMulti Ω p v = α • a)
    (e' : exteriorPower.ιMulti Ω p v' = α' • a) (h : α' ≠ 0) : α ≠ 0 := by
  rintro rfl
  have h1 := (wedge_frame hv').symm.trans (wedge_frame hv)
  rw [e, e', zero_smul, Submodule.span_zero_singleton, Submodule.span_singleton_eq_bot] at h1
  exact smul_ne_zero h ha h1

end PositivityTheory.Xgn.LineLatticeVectorBundle

theorem PositivityTheory.Xgn.line_lattice_vector_bundle : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (A B : Lat ξ E) (p q : ℕ) (V V' : Submodule Ω E) (T : Set (Cpt ξ)) (a : ⋀[Ω]^p E) (b : ⋀[Ω]^q E), A.IsVBOn T p V → B.IsVBOn T q V' → a ≠ 0 → b ≠ 0 → (∃ x ∈ T, ∃ f, IsCoeffAt A B p q a b x f) → (lineLat A B p q a b).IsVBOn T 1 ⊤ ∧ (∀ x ∈ T, ∀ t : Ω, (lineLat A B p q a b).IsGenAt x t ↔ t ≠ 0 ∧ IsCoeffAt A B p q a b x t⁻¹) ∧ ∀ x ∈ T, ∀ (v : Fin p → E) (w : Fin q → E) (α β : Ω), A.IsFrameAt v x → B.IsFrameAt w x → exteriorPower.ιMulti Ω p v = α • a → exteriorPower.ιMulti Ω q w = β • b → (lineLat A B p q a b).IsGenAt x (α / β) := by
  intro X Ω _ ξ E _ _ A B p q V V' T a b hA hB ha hb hex
  obtain ⟨x₀, hx₀, f₀, α₀, β₀, hα₀, hβ₀, hA₀, hB₀, -⟩ := hex
  have loc : ∀ x ∈ T, ∃ U : X.Opens, x.1 ∈ U ∧ ∃ (v : Fin p → E) (w : Fin q → E) (α β : Ω), α ≠ 0 ∧ β ≠ 0 ∧
      exteriorPower.ιMulti Ω p v = α • a ∧ exteriorPower.ιMulti Ω q w = β • b ∧
      ∀ y ∈ T, y.1 ∈ U → A.IsFrameAt v y ∧ B.IsFrameAt w y := by
    intro x hx
    obtain ⟨U, hU, v, hv, hfv⟩ := hA x hx
    obtain ⟨U', hU', w, hw, hfw⟩ := hB x hx
    obtain ⟨α, hα, ev⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hA ha hx₀ hα₀ hA₀ v hv
    obtain ⟨β, hβ, ew⟩ := PositivityTheory.Xgn.LineLatticeVectorBundle.on_line hB hb hx₀ hβ₀ hB₀ w hw
    exact ⟨U ⊓ U', ⟨hU, hU'⟩, v, w, α, β, hα, hβ, ev, ew, fun y hy hyU => ⟨hfv y hy hyU.1, hfw y hy hyU.2⟩⟩
  refine ⟨fun x hx => ?_, fun x hx t => ?_, fun x hx v w α β hv hw ev ew => ?_⟩
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    have h0 : α / β ≠ 0 := div_ne_zero hα hβ
    have hr : Set.range (fun _ : Fin 1 => α / β) = {α / β} := Set.range_const
    refine ⟨U, hU, fun _ => α / β, ?_, fun y hy hyU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro s _
      exact Submodule.mem_span_singleton.2 ⟨s / (α / β), div_mul_cancel₀ s h0⟩
    · exact linearIndependent_unique_iff.2 h0
    · have := (PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
        (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h y hy hyU).1 (h y hy hyU).2 hα hβ ev ew)).2
      rw [inv_inv] at this
      rw [hr, this]
  · obtain ⟨U, hU, v, w, α, β, hα, hβ, ev, ew, h⟩ := loc x hx
    exact PositivityTheory.Xgn.LineLatticeVectorBundle.gen_iff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames (h x hx hU).1 (h x hx hU).2 hα hβ ev ew) t
  · obtain ⟨U, hU, v', w', α', β', hα, hβ, ev', ew', h⟩ := loc x hx
    have := PositivityTheory.Xgn.LineLatticeVectorBundle.gen_of_coeff ha hb
      (PositivityTheory.Xgn.LineLatticeVectorBundle.coeff_of_frames hv hw
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames ha hv (h x hx hU).1 ev ev' hα)
        (PositivityTheory.Xgn.LineLatticeVectorBundle.ne_zero_of_frames hb hw (h x hx hU).2 ew ew' hβ) ev ew)
    rwa [inv_inv] at this
