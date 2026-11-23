import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.FourierTransforms.CompP

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.T.Nil.Four.Alg

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Four

variable {k : Type} [Field k] {n : ℕ}

theorem exists_reg {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] [IsSemisimpleModule R M]
    (f : M →ₗ[R] M) : ∃ g : M →ₗ[R] M, f ∘ₗ g ∘ₗ f = f := by
  obtain ⟨C, hC⟩ := exists_isCompl (LinearMap.ker f)
  obtain ⟨D, hD⟩ := exists_isCompl (LinearMap.range f)
  let e : C ≃ₗ[R] LinearMap.range f :=
    (Submodule.quotientEquivOfIsCompl _ C hC).symm.trans f.quotKerEquivRange
  refine ⟨C.subtype ∘ₗ e.symm.toLinearMap ∘ₗ Submodule.projectionOnto _ D hD, ?_⟩
  ext x
  simp only [LinearMap.comp_apply]
  rw [Submodule.projectionOnto_apply_of_mem_left hD (LinearMap.mem_range_self f x)]
  have h2 := e.apply_symm_apply ⟨f x, LinearMap.mem_range_self f x⟩
  have h3 : ∀ c : C, (e c : M) = f c := by
    intro c
    simp [e]
  have h4 := congrArg Subtype.val h2
  rw [h3] at h4
  simpa using h4

abbrev ZV (_Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Type := Fin n → k

instance (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) : Module Z (ZV Z) where
  smul z v := (z : Matrix (Fin n) (Fin n) k) *ᵥ (v : Fin n → k)
  one_smul v := Matrix.one_mulVec (v : Fin n → k)
  mul_smul a b v := (Matrix.mulVec_mulVec (v : Fin n → k) _ _).symm
  smul_zero a := Matrix.mulVec_zero _
  smul_add a u v := Matrix.mulVec_add _ (u : Fin n → k) v
  add_smul a b v := Matrix.add_mulVec _ _ (v : Fin n → k)
  zero_smul v := Matrix.zero_mulVec (v : Fin n → k)

abbrev zComm (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : CommRing Z :=
  { (inferInstance : Ring Z) with mul_comm := fun a b => Subtype.ext (hZ.1 _ a.2 _ b.2) }

theorem isSemisimpleRing (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) : IsSemisimpleRing Z := by
  letI := zComm Z hZ
  haveI : IsReduced Z := hZ.2
  haveI : IsArtinianRing Z := IsArtinianRing.of_finite k Z
  exact IsArtinianRing.isSemisimpleRing_of_isReduced Z

theorem idem_trace [CharZero k] {e : Matrix (Fin n) (Fin n) k} (he : e * e = e) (ht : trace e = 0) : e = 0 := by
  have hi : IsIdempotentElem (Matrix.toLin' e) := by
    unfold IsIdempotentElem
    rw [Module.End.mul_eq_comp, ← Matrix.toLin'_mul, he]
  have htr : LinearMap.trace k (Fin n → k) (Matrix.toLin' e) = 0 := by
    rw [LinearMap.trace_eq_matrix_trace k (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
      LinearMap.toMatrix'_toLin']
    exact ht
  have h0 : Matrix.toLin' e = 0 := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hi).mp htr
  have := congrArg LinearMap.toMatrix' h0
  simpa using this

theorem trB_nondeg [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {w : Matrix (Fin n) (Fin n) k} (hw : w ∈ Bz Z) (h : ∀ b ∈ Bz Z, trace (b * w) = 0) : w = 0 := by
  haveI : IsSemisimpleRing Z := isSemisimpleRing Z hZ
  have hw' : ∀ a ∈ Z, a * w = w * a := hw
  have mext : ∀ A B : Matrix (Fin n) (Fin n) k, (∀ v, A *ᵥ v = B *ᵥ v) → A = B := fun A B h =>
    Matrix.toLin'.injective (LinearMap.ext fun v => by simpa [Matrix.toLin'_apply] using h v)
  let f : ZV Z →ₗ[Z] ZV Z :=
    { toFun := fun v => w *ᵥ (v : Fin n → k)
      map_add' := fun u v => Matrix.mulVec_add _ _ _
      map_smul' := fun z v => by
        show w *ᵥ ((z : Matrix (Fin n) (Fin n) k) *ᵥ (v : Fin n → k)) =
          (z : Matrix (Fin n) (Fin n) k) *ᵥ (w *ᵥ (v : Fin n → k))
        rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hw' _ z.2] }
  obtain ⟨g, hg⟩ := exists_reg f
  have sm_eq : ∀ (z : Z) (u : ZV Z), z • u = (z : Matrix (Fin n) (Fin n) k) *ᵥ (u : Fin n → k) :=
    fun z u => rfl
  have gsmul : ∀ (c : k) (v : Fin n → k), g (c • v) = c • g v := by
    intro c v
    have e1 : ∀ u : ZV Z, (algebraMap k Z c) • u = c • (u : Fin n → k) := by
      intro u
      rw [sm_eq]
      simp [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec]
    have h := g.map_smul (algebraMap k Z c) v
    rw [e1, e1] at h
    exact h
  let gl : (Fin n → k) →ₗ[k] (Fin n → k) :=
    { toFun := fun v => g v, map_add' := fun u v => g.map_add u v, map_smul' := gsmul }
  set G := LinearMap.toMatrix' gl with hGdef
  have hG : ∀ v, G *ᵥ v = g v := fun v => LinearMap.toMatrix'_mulVec gl v
  have hGB : G ∈ Bz Z := by
    intro a ha
    apply mext
    intro v
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG, hG]
    have h := g.map_smul (⟨a, ha⟩ : Z) v
    rw [sm_eq, sm_eq] at h
    exact h.symm
  have hwgw : w * G * w = w := by
    apply mext
    intro v
    have h := LinearMap.congr_fun hg v
    simp only [LinearMap.comp_apply] at h
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hG]
    exact h
  have hidem : G * w * (G * w) = G * w := by
    calc G * w * (G * w) = G * (w * G * w) := by simp only [Matrix.mul_assoc]
      _ = G * w := by rw [hwgw]
  have h0 : G * w = 0 := idem_trace hidem (h G hGB)
  calc w = w * G * w := hwgw.symm
    _ = w * (G * w) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h0, Matrix.mul_zero]

theorem trZ_nondeg [CharZero k] {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)} (hZ : CR Z)
    {c : Matrix (Fin n) (Fin n) k} (hc : c ∈ Z) (h : ∀ b ∈ Z, trace (b * c) = 0) : c = 0 := by
  haveI : IsSemisimpleRing Z := isSemisimpleRing Z hZ
  set c' : Z := ⟨c, hc⟩ with hc'
  obtain ⟨g, hg⟩ := exists_reg (R := Z) (M := Z) (LinearMap.mulRight Z c')
  have h1 := LinearMap.congr_fun hg 1
  simp only [LinearMap.comp_apply, LinearMap.mulRight_apply, one_mul] at h1
  have h2 : g c' = c' * g 1 := by
    calc g c' = g (c' • (1 : Z)) := by rw [smul_eq_mul, mul_one]
      _ = c' • g 1 := g.map_smul _ _
      _ = c' * g 1 := smul_eq_mul _ _
  rw [h2] at h1
  have h3 : c * (g 1 : Matrix (Fin n) (Fin n) k) * c = c := congrArg Subtype.val h1
  set d : Matrix (Fin n) (Fin n) k := (g 1 : Matrix (Fin n) (Fin n) k) with hd
  have hidem : d * c * (d * c) = d * c := by
    calc d * c * (d * c) = d * (c * d * c) := by simp only [Matrix.mul_assoc]
      _ = d * c := by rw [h3]
  have h0 : d * c = 0 := idem_trace hidem (h d (g 1).2)
  calc c = c * d * c := h3.symm
    _ = c * (d * c) := by rw [Matrix.mul_assoc]
    _ = 0 := by rw [h0, Matrix.mul_zero]

end PositivityTheory.RgUd.T.Nil.Four.Alg
