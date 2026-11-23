import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFrameOfHasSignature
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianSpacesSameSignatureIsometricStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsFiniteAdelicPointLatticeEqSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GaugeVolumeEqOfSemilinearIsometryGenusStatement

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas

noncomputable section

namespace GlobalTheory.VolInvariant

theorem hform_eq {E : Type} [Field E] [StarRing E] {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (y x : Fin n → E) :
    Formalism.UG.hform (starRingEnd E) J y x = star y ⬝ᵥ (J *ᵥ x) := by
  simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply]

theorem eq_or_conj {E : Type} [Field E] [CharZero E] [StarRing E] (φ ψ : E →+* ℂ)
    (hψ : ∀ a, ψ (star a) = starRingEnd ℂ (ψ a)) (h : ∀ a, star a = a → φ a = ψ a) :
    φ = ψ ∨ φ = (starRingEnd ℂ).comp ψ := by
  by_cases hall : ∀ a : E, star a = a
  · left; ext a; exact h a (hall a)
  push Not at hall
  obtain ⟨b, hb⟩ := hall
  set θ := b - star b with hθ
  have hθ0 : θ ≠ 0 := sub_ne_zero.2 hb.symm
  have hs : star θ = -θ := by simp [hθ]
  have hsq : φ θ ^ 2 = ψ θ ^ 2 := by
    rw [← map_pow, ← map_pow]; apply h; rw [star_pow, hs]; ring
  have h2 : star (2 : E) = 2 := star_ofNat 2
  have dec : ∀ a : E, ∃ u w : E, star u = u ∧ star w = w ∧ a = u + θ * w := by
    intro a
    refine ⟨(a + star a) / 2, (a - star a) / (2 * θ), ?_, ?_, ?_⟩
    · rw [star_div₀, star_add, star_star, h2, add_comm]
    · rw [star_div₀, star_sub, star_star, star_mul', h2, hs]; field_simp; ring
    · field_simp; ring
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h1 | h1
  · left; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    simp only [map_add, map_mul, h u hu, h w hw, h1]
  · right; ext a
    obtain ⟨u, w, hu, hw, rfl⟩ := dec a
    rw [RingHom.comp_apply, ← hψ, star_add, star_mul', hu, hw, hs]
    simp only [map_add, map_mul, map_neg, h u hu, h w hw, h1]

theorem hasSignature_all (I : AutInst) {p q : ℕ} (h : HasSig I p q) (φ : I.E →+* ℂ) :
    Formalism.UG.HasSignature (I.J.map φ) p q := by
  set v : InfinitePlace I.F := InfinitePlace.mk (φ.comp (algebraMap I.F I.E)) with hv
  have hc := I.cm.cmUnram.2.1
  have hag : ∀ a, star a = a → φ a = I.φ v a := by
    intro a ha
    obtain ⟨c, rfl⟩ := (I.cm.fixed a).1 ha
    rw [I.φ_over]
    rcases InfinitePlace.embedding_mk_eq (φ.comp (algebraMap I.F I.E)) with h1 | h1
    · rw [hv, h1]; rfl
    · rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, RingHom.comp_apply, ← hc, ha]
  rw [← (h v).1, ← (h v).2]
  rcases eq_or_conj φ (I.φ v) (hc _) hag with h1 | h1
  · have e0 : I.J.map φ = I.J.map (I.φ v) := congrArg (fun ψ : I.E →+* ℂ => I.J.map ψ) h1
    rw [e0]
    exact GlobalTheory.AutInhab.hasSignature_inst I v
  · refine GlobalTheory.AutInhab.hasSignature_of_frame (P := (I.P v).map (starRingEnd ℂ)) ?_ ?_
    · exact (I.P_unit v).map (starRingEnd ℂ).mapMatrix
    · have := congrArg (fun M => Matrix.map M (starRingEnd ℂ)) (I.P_spec v)
      simp only [Matrix.map_mul] at this
      have e1 : I.J.map φ = (I.J.map (I.φ v)).map (starRingEnd ℂ) := by
        ext i j; conv_lhs => rw [h1]
        rfl
      have e2 : ((I.P v).map (starRingEnd ℂ))ᴴ = ((I.P v)ᴴ).map (starRingEnd ℂ) := by
        ext i j; rfl
      rw [e1, e2, this]
      ext i j
      simp only [Formalism.REAL.Jm, Matrix.map_apply, Matrix.diagonal_apply]
      split_ifs <;> simp

section Transport

variable {E E' : Type} [Field E] [NumberField E] [StarRing E] [Field E'] [NumberField E'] [StarRing E'] {n : ℕ}

theorem exists_image (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) (J : Matrix (Fin n) (Fin n) E)
    (J' : Matrix (Fin n) (Fin n) E') (A : GL (Fin n) E)
    (hA : (A : Matrix (Fin n) (Fin n) E)ᴴ * J * (A : Matrix (Fin n) (Fin n) E) = J'.map e)
    (L : Submodule (𝓞 E') (Fin n → E')) (hL : Submodule.IsLattice E' L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range) :
    ∃ Λ : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n → E', y ∈ L ↔ (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) ∈ Λ := by
  let σ : 𝓞 E' →+* 𝓞 E := (RingOfIntegers.mapRingEquiv e : 𝓞 E' ≃+* 𝓞 E)
  haveI : RingHomSurjective σ := ⟨(RingOfIntegers.mapRingEquiv e).surjective⟩
  haveI : RingHomSurjective (e : E' →+* E) := ⟨e.surjective⟩
  let g : (Fin n → E') →ₛₗ[(e : E' →+* E)] (Fin n → E) :=
    { toFun := fun y => (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i))
      map_add' := fun x y => by
        rw [← Matrix.mulVec_add]; congr 1; ext i; simp
      map_smul' := fun c x => by
        rw [← Matrix.mulVec_smul]; congr 1; ext i; simp }
  let f : (Fin n → E') →ₛₗ[σ] (Fin n → E) :=
    { toFun := g
      map_add' := g.map_add
      map_smul' := fun c x => g.map_smulₛₗ (c : E') x }
  have hf : ∀ y, f y = (A : Matrix (Fin n) (Fin n) E) *ᵥ (fun i => e (y i)) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro x y hxy
    have := congrArg (fun z => ((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ z) hxy
    simp only [hf, Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] at this
    ext i; exact e.injective (congrFun this i)
  have hsurj : Function.Surjective f := by
    intro x
    refine ⟨fun i => e.symm ((((A⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) *ᵥ x) i), ?_⟩
    simp only [hf, RingEquiv.apply_symm_apply]
    rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hform : ∀ x y, star (f y) ⬝ᵥ (J *ᵥ f x) = e (star y ⬝ᵥ (J' *ᵥ x)) := by
    intro x y
    rw [hf, hf, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hA]
    simp [dotProduct, Matrix.mulVec, he]
  have hint : ∀ a : E', e a ∈ (algebraMap (𝓞 E) E).range ↔ a ∈ (algebraMap (𝓞 E') E').range := by
    intro a
    constructor
    · rintro ⟨c, hc⟩
      refine ⟨(RingOfIntegers.mapRingEquiv e).symm c, e.injective ?_⟩
      rw [← hc]
      exact e.apply_symm_apply _
    · rintro ⟨c, rfl⟩
      exact ⟨σ c, rfl⟩
  have hmem : ∀ y, y ∈ L ↔ f y ∈ L.map f := fun y =>
    ⟨fun h => ⟨y, h, rfl⟩, fun ⟨z, hz, h⟩ => hinj h ▸ hz⟩
  refine ⟨L.map f, ⟨hL.fg.map f, ?_⟩, ?_, hmem⟩
  · have : ((L.map f : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) = g '' (L : Set (Fin n → E')) := rfl
    rw [this, ← Submodule.map_span, hL.span_eq_top, Submodule.map_top, LinearMap.range_eq_top]
    exact hsurj
  · intro x
    obtain ⟨x, rfl⟩ := hsurj x
    rw [← hmem, hd]
    constructor
    · rintro h _ ⟨y, hy, rfl⟩
      rw [hform, hint]; exact h y hy
    · intro h y hy
      rw [← hint, ← hform]; exact h _ ⟨y, hy, rfl⟩

theorem exists_isometry (hE : Formalism.HermitianLatticesTheory.IsCMUnram E) (e : E' ≃+* E) (he : ∀ y, e (star y) = star (e y)) {n' : ℕ}
    (hn : n' = n) (J : Matrix (Fin n) (Fin n) E) (J' : Matrix (Fin n') (Fin n') E')
    (hJ : Jᴴ = J) (hJ' : J'ᴴ = J') (hdet : J.det ≠ 0) (hdet' : J'.det ≠ 0)
    (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L)
    (hd : ∀ x, x ∈ L ↔ ∀ y ∈ L, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range)
    (L' : Submodule (𝓞 E') (Fin n' → E')) (hL' : Submodule.IsLattice E' L')
    (hd' : ∀ x, x ∈ L' ↔ ∀ y ∈ L', star y ⬝ᵥ (J' *ᵥ x) ∈ (algebraMap (𝓞 E') E').range)
    {p q : ℕ} (hs : ∀ φ : E →+* ℂ, Formalism.UG.HasSignature (J.map φ) p q)
    (hs' : ∀ φ : E' →+* ℂ, Formalism.UG.HasSignature (J'.map φ) p q) :
    ∃ (A : Matrix (Fin n) (Fin n') E) (Λ : Submodule (𝓞 E) (Fin n → E)), Aᴴ * J * A = J'.map e ∧
      Submodule.IsLattice E Λ ∧
      (∀ x, x ∈ Λ ↔ ∀ y ∈ Λ, star y ⬝ᵥ (J *ᵥ x) ∈ (algebraMap (𝓞 E) E).range) ∧
      ∀ y : Fin n' → E', y ∈ L' ↔ A *ᵥ (fun i => e (y i)) ∈ Λ := by
  subst hn
  obtain ⟨Λ₁, h1, h2, -⟩ := exists_image e he (J'.map e) J' 1 (by simp) L' hL' hd'
  have hh : (J'.map e)ᴴ = J'.map e := by
    ext i j
    rw [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.map_apply, ← he, ← Matrix.conjTranspose_apply, hJ']
  have hde : (J'.map e).det ≠ 0 := by
    have := RingHom.map_det (e : E' →+* E) J'
    rw [RingHom.mapMatrix_apply] at this
    have h3 : (J'.map e).det = e J'.det := this.symm
    rw [h3]
    exact (map_ne_zero e).2 hdet'
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.hermitian_spaces_same_signature_isometric E hE _ J (J'.map e) hJ hh hdet hde ⟨L, hL, hd⟩ ⟨Λ₁, h1, h2⟩
    fun φ => ⟨p, q, hs φ, hs' (φ.comp (e : E' →+* E))⟩
  obtain ⟨Λ, h3, h4, h5⟩ := exists_image e he J J' γ hγ L' hL' hd'
  exact ⟨γ, Λ, hγ, h3, h4, h5⟩

end Transport

theorem rank_eq (I : AutInst) {p q : ℕ} (h : HasSig I p q) : I.n = p + q := by
  obtain ⟨φ⟩ : Nonempty (I.E →+* ℂ) := inferInstance
  simpa using (Formalism.UG.P.sig_data _ p q (hasSignature_all I h φ)).1

theorem volumeInvariant : VolumeInvariant := by
  rintro I I' p q ⟨e, he⟩ h h' c μf _ _ c' μf' _ _ hc hc'
  have hn : I'.n = I.n := (rank_eq I' h').trans (rank_eq I h).symm
  obtain ⟨A, Λ, hA, hΛ, hd, hmem⟩ := exists_isometry I.cm.cmUnram e he hn I.J I'.J I.J_herm I'.J_herm
    I.J_det I'.J_det I.L ⟨I.L_fg, I.L_span⟩ (by simpa only [hform_eq] using I.L_dual)
    I'.L ⟨I'.L_fg, I'.L_span⟩ (by simpa only [hform_eq] using I'.L_dual)
    (hasSignature_all I h) (hasSignature_all I' h')
  obtain ⟨xf, hx⟩ := GlobalTheory.T.exists_finiteAdelicPoint_lattice_eq_selfDual I Λ hΛ (by simpa only [hform_eq] using hd)
  exact GlobalTheory.T.gaugeVolume_eq_of_semilinear_isometry_genus I I' e A xf he hn hA (hx ▸ hmem) c μf c' μf' hc hc'

end GlobalTheory.VolInvariant
