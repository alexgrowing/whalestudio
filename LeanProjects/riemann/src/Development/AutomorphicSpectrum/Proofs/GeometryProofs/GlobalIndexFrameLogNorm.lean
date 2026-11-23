import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PlaceEqOneOfNotMem
import ReciprocityTheory.SemistableReduction.SemiDegBB
open NumberField Matrix IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame

namespace GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet

section Index

variable {W : Type} [AddCommGroup W]

theorem relIndex_pair (Λ : AddSubgroup W) (M a : W →+ W) (hM : Function.Injective M)
    (hc : ∀ x, a (M x) = M (a x)) (h2 : Λ.map a ≤ Λ) (i2 : (Λ.map a).relIndex Λ ≠ 0)
    (h3 : Λ.map (a.comp M) ≤ Λ) (i3 : (Λ.map (a.comp M)).relIndex Λ ≠ 0) :
    Λ.relIndex (Λ.map M) ≠ 0 ∧ (Λ.map M).relIndex Λ ≠ 0 := by
  have e3 : Λ.map (a.comp M) = (Λ.map a).map M := by
    rw [AddSubgroup.map_map]
    congr 1
    ext x
    exact hc x
  have l1 : Λ.map (a.comp M) ≤ Λ.map M := by rw [e3]; exact AddSubgroup.map_mono h2
  have n1 : (Λ.map (a.comp M)).relIndex (Λ.map M) ≠ 0 := by
    rw [e3, AddSubgroup.relIndex_map_map_of_injective _ _ hM]; exact i2
  have o1 : (Λ.map M).relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 l1]; exact one_ne_zero
  have o3 : Λ.relIndex (Λ.map (a.comp M)) ≠ 0 := by
    rw [AddSubgroup.relIndex_eq_one.2 h3]; exact one_ne_zero
  exact ⟨AddSubgroup.relIndex_ne_zero_trans o3 n1, AddSubgroup.relIndex_ne_zero_trans o1 i3⟩

end Index

variable {L : Type} [Field L] [NumberField L] {n : ℕ}

noncomputable def mulVecHom (T : Matrix (Fin n) (Fin n) L) : (Fin n → L) →+ (Fin n → L) :=
  AddMonoidHom.mk' (fun x => T *ᵥ x) (Matrix.mulVec_add T)

theorem mulVecHom_apply (T : Matrix (Fin n) (Fin n) L) (x : Fin n → L) : mulVecHom T x = T *ᵥ x := rfl

theorem frame_eq_map (T : Matrix (Fin n) (Fin n) L) :
    (frame T).toAddSubgroup = (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.map (mulVecHom T) := by
  ext x
  rw [Submodule.mem_toAddSubgroup, AddSubgroup.mem_map, mem_frame]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨_, (Submodule.mem_toAddSubgroup _).2 (mem_frame.2 ⟨z, by simp⟩), rfl⟩
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨z, rfl⟩ := mem_frame.1 ((Submodule.mem_toAddSubgroup _).1 hy)
    exact ⟨z, by simp [mulVecHom_apply]⟩

theorem frame_map_le (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    frame (D.map (algebraMap (𝓞 L) L)) ≤ frame (1 : Matrix (Fin n) (Fin n) L) := by
  rw [frame, Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact mem_frame_one.2 fun i => ⟨D i k, rfl⟩

theorem log_abs_norm (x : 𝓞 L) (hx : x ≠ 0) :
    Real.log ((|Algebra.norm ℤ x| : ℤ) : ℝ) = ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L x)‖ := by
  have hx' : algebraMap (𝓞 L) L x ≠ 0 := by simpa using hx
  rw [← Real.log_prod (fun σ _ => norm_ne_zero_iff.2 ((map_ne_zero σ).2 hx'))]
  congr 1
  have h1 : ∏ σ : L →+* ℂ, σ (algebraMap (𝓞 L) L x) =
      algebraMap ℚ ℂ (Algebra.norm ℚ (algebraMap (𝓞 L) L x)) := by
    rw [Algebra.norm_eq_prod_embeddings ℚ ℂ (algebraMap (𝓞 L) L x)]
    exact Fintype.prod_equiv (RingHom.equivRatAlgHom L ℂ) _ _
      (fun σ => by simp [RingHom.equivRatAlgHom_apply])
  rw [← norm_prod, h1, ← Algebra.coe_norm_int x]
  simp

theorem relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℤ) = |Algebra.norm ℤ D.det| := by
  have hb : LinearIndependent L (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) := by
    have e : (fun k j => (1 : Matrix (Fin n) (Fin n) L) j k) = ⇑(Pi.basisFun L (Fin n)) := by
      funext k j
      simp [Matrix.one_apply, Pi.single_apply]
    rw [e]
    exact (Pi.basisFun L (Fin n)).linearIndependent
  have h := ReciprocityTheory.MultiplicativeHeights.relIndex_span_comb _ hb D hD
  have e : frame (D.map (algebraMap (𝓞 L) L)) = Submodule.span (𝓞 L)
      (Set.range fun j => ∑ i, D i j • fun l => (1 : Matrix (Fin n) (Fin n) L) l i) := by
    rw [frame]
    congr 2
    funext k j
    simp [Finset.sum_apply, Matrix.one_apply, Algebra.smul_def]
  rw [e]
  exact h

theorem relIndex_frame_ne (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 := by
  intro h
  have h1 := relIndex_frame D hD
  rw [h, Nat.cast_zero, eq_comm, abs_eq_zero, Algebra.norm_eq_zero_iff] at h1
  exact hD h1

theorem log_relIndex_frame (D : Matrix (Fin n) (Fin n) (𝓞 L)) (hD : D.det ≠ 0) :
    Real.log (((frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup.relIndex
      (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup : ℕ) : ℝ) =
      ∑ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ := by
  rw [← log_abs_norm _ hD, ← relIndex_frame D hD]
  simp

theorem exists_int_matrix (C : Matrix (Fin n) (Fin n) L) :
    ∃ (d : 𝓞 L) (D : Matrix (Fin n) (Fin n) (𝓞 L)), d ≠ 0 ∧
      D.map (algebraMap (𝓞 L) L) = algebraMap (𝓞 L) L d • C := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 L))
    (fun p : Fin n × Fin n => C p.1 p.2)
  choose D hD using hb
  refine ⟨b, Matrix.of fun i j => D (i, j), nonZeroDivisors.ne_zero b.2, ?_⟩
  ext i j
  simpa [Algebra.smul_def] using hD (i, j)

theorem coe_det (D : Matrix (Fin n) (Fin n) (𝓞 L)) :
    algebraMap (𝓞 L) L D.det = (D.map (algebraMap (𝓞 L) L)).det := by
  rw [RingHom.map_det]
  rfl

theorem gIdx_frame : ∀ (L : Type) [Field L] [NumberField L] (n : ℕ) (C : Matrix (Fin n) (Fin n) L),
    C.det ≠ 0 →
    (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup.relIndex (frame C).toAddSubgroup ≠ 0 ∧
    (frame C).toAddSubgroup.relIndex (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup ≠ 0 ∧
    gIdx (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup (frame C).toAddSubgroup =
      ∑ σ : L →+* ℂ, Real.log ‖σ C.det‖ := by
  intro L _ _ n C hC
  obtain ⟨d, D, hd, hDC⟩ := exists_int_matrix C
  have hδ : algebraMap (𝓞 L) L d ≠ 0 := by simpa using hd
  obtain ⟨δ, hδe⟩ : ∃ δ, δ = algebraMap (𝓞 L) L d := ⟨_, rfl⟩
  rw [← hδe] at hDC hδ
  obtain ⟨S, hSe⟩ : ∃ S : Matrix (Fin n) (Fin n) (𝓞 L), S = d • 1 := ⟨_, rfl⟩
  have hS : S.map (algebraMap (𝓞 L) L) = δ • 1 := by
    ext i j
    by_cases h : i = j <;> simp [hSe, hδe, Matrix.smul_apply, Matrix.one_apply, h]
  have hSdet : S.det = d ^ n := by simp [hSe, Matrix.det_smul]
  have hDdet : algebraMap (𝓞 L) L D.det = δ ^ n * C.det := by
    rw [coe_det, hDC, Matrix.det_smul, Fintype.card_fin]
  have hS0 : S.det ≠ 0 := by rw [hSdet]; exact pow_ne_zero _ hd
  have hD0 : D.det ≠ 0 := by
    intro h
    rw [h, map_zero] at hDdet
    exact mul_ne_zero (pow_ne_zero _ hδ) hC hDdet.symm
  set Λ := (frame (1 : Matrix (Fin n) (Fin n) L)).toAddSubgroup with hΛ
  have ea : Λ.map (mulVecHom (δ • 1)) = (frame (S.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [hS, frame_eq_map]
  have eM : (mulVecHom (δ • 1)).comp (mulVecHom C) = mulVecHom (D.map (algebraMap (𝓞 L) L)) := by
    refine AddMonoidHom.ext fun x => ?_
    simp [mulVecHom_apply, hDC, Matrix.smul_mulVec]
  have eaM : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) =
      (frame (D.map (algebraMap (𝓞 L) L))).toAddSubgroup := by
    rw [eM, frame_eq_map]
  have hc : ∀ x, mulVecHom (δ • 1) (mulVecHom C x) = mulVecHom C (mulVecHom (δ • 1) x) := by
    intro x
    simp [mulVecHom_apply, Matrix.smul_mulVec, Matrix.mulVec_smul]
  have hinj : Function.Injective (mulVecHom C) :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det C).2 (IsUnit.mk0 _ hC))
  have h2 : Λ.map (mulVecHom (δ • 1)) ≤ Λ := by
    rw [ea]; exact fun x hx => frame_map_le S hx
  have i2 : (Λ.map (mulVecHom (δ • 1))).relIndex Λ ≠ 0 := by
    rw [ea]; exact relIndex_frame_ne S hS0
  have h3 : Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C)) ≤ Λ := by
    rw [eaM]; exact fun x hx => frame_map_le D hx
  have i3 : (Λ.map ((mulVecHom (δ • 1)).comp (mulVecHom C))).relIndex Λ ≠ 0 := by
    rw [eaM]; exact relIndex_frame_ne D hD0
  obtain ⟨p1, p2⟩ := relIndex_pair Λ _ _ hinj hc h2 i2 h3 i3
  have hf := GlobalTheory.CompanionTheory.Ar.Cusp.LocFrame.gIdx_frac Λ _ _ hinj hc h2 i2 h3 i3
  rw [ea, eaM, log_relIndex_frame S hS0, log_relIndex_frame D hD0] at hf
  have eC : (frame C).toAddSubgroup = Λ.map (mulVecHom C) := frame_eq_map C
  refine ⟨by rw [eC]; exact p1, by rw [eC]; exact p2, ?_⟩
  rw [eC, gIdx_swap, hf]
  have hsum : ∀ σ : L →+* ℂ, Real.log ‖σ (algebraMap (𝓞 L) L D.det)‖ =
      Real.log ‖σ (algebraMap (𝓞 L) L S.det)‖ + Real.log ‖σ C.det‖ := by
    intro σ
    have a1 : ‖σ (algebraMap (𝓞 L) L S.det)‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero, hSdet, map_pow, ← hδe]
      exact pow_ne_zero _ hδ
    have a2 : ‖σ C.det‖ ≠ 0 := by
      rw [norm_ne_zero_iff, map_ne_zero]; exact hC
    rw [← Real.log_mul a1 a2, ← norm_mul, ← map_mul, hDdet, hSdet, map_pow, ← hδe]
  simp_rw [hsum]
  rw [Finset.sum_add_distrib]
  ring

end GlobalTheory.CompanionTheory.Ar.Cusp.GlobDet
