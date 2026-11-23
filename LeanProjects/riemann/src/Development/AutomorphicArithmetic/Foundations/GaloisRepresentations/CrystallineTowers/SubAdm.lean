import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTower
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.AdmCrys
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsModelOfMem

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

namespace UpperTheory.Gal.Seam

variable {l : ℕ} [Fact l.Prime]

private theorem isAdmP_block (P : LocPrime l) (G : Subgroup (PadicAlgCl l ≃ₐ[ℚ_[l]] PadicAlgCl l)) {N D : ℕ} {a : Fin N → ℕ}
    (e : (Σ n, Fin (a n)) ≃ Fin D) (R : ∀ n, G → Matrix (Fin (a n)) (Fin (a n)) ℚ_[l])
    (h : ∀ n, IsAdmP P G (R n)) :
    IsAdmP P G (fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm) := by
  choose A B hm hAB hσ using h
  have hz : (0 : P.R.BdR) ∈ Set.range P.ιB := ⟨0, map_zero _⟩
  have hmem : ∀ (C : ∀ n, Matrix (Fin (a n)) (Fin (a n)) P.R.BdR), (∀ n i j, C n i j ∈ Set.range P.ιB) →
      ∀ s t, Matrix.blockDiagonal' C s t ∈ Set.range P.ιB := by
    intro C hC s t
    rw [Matrix.blockDiagonal'_apply]
    split_ifs with hst
    · exact hC _ _ _
    · exact hz
  refine ⟨(Matrix.blockDiagonal' A).submatrix e.symm e.symm, (Matrix.blockDiagonal' B).submatrix e.symm e.symm,
    fun i j => ⟨hmem A (fun n i j => (hm n i j).1) _ _, hmem B (fun n i j => (hm n i j).2) _ _⟩, ?_, fun σ => ?_⟩
  · rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
    simp only [hAB]
    exact (congrArg (fun X => Matrix.submatrix X e.symm e.symm) (Matrix.blockDiagonal'_one (m' := fun n => Fin (a n)))).trans
      (Matrix.submatrix_one_equiv _)
  · rw [← Matrix.submatrix_map, ← Matrix.submatrix_map, Matrix.submatrix_mul_equiv,
      Matrix.blockDiagonal'_map _ _ (map_zero _), Matrix.blockDiagonal'_map _ _ (map_zero _),
      ← Matrix.blockDiagonal'_mul]
    simp only [hσ]

end UpperTheory.Gal.Seam

open UpperTheory.Gal.Seam in

theorem UpperTheory.Gal.Seam.subAdm : UpperTheory.Gal.Seam.SubAdm := by
  intro l _ P AI hT E Ω _ _ _ Gw O _ _ _ Bw N d a R r hR M hM hint
  let D := Fintype.card (Σ n, Fin (a n))
  let e : (Σ n, Fin (a n)) ≃ Fin D := Fintype.equivFin _
  let f : ↥(GK Bw.Kw) →* Matrix (Fin D) (Fin D) ℚ_[l] :=
    { toFun := fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm
      map_one' := by
        simp only [fun n => (hR n).1]
        exact (congrArg (fun X => Matrix.submatrix X e.symm e.symm) (Matrix.blockDiagonal'_one (m' := fun n => Fin (a n)))).trans
          (Matrix.submatrix_one_equiv _)
      map_mul' := fun σ τ => by
        rw [Matrix.submatrix_mul_equiv, ← Matrix.blockDiagonal'_mul]
        simp only [fun n => (hR n).2.1 σ τ] }
  let ρ : ↥(GK Bw.Kw) →* GL (Fin D) ℚ_[l] := f.toHomUnits
  have hρf : ∀ σ, (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l]) = f σ := fun σ => MonoidHom.coe_toHomUnits f σ
  have hadm : IsAdmP P (GK Bw.Kw) (fun σ => (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l])) := by
    have h0 : (fun σ => (ρ σ : Matrix (Fin D) (Fin D) ℚ_[l])) =
        fun σ => (Matrix.blockDiagonal' fun n => R n σ).submatrix e.symm e.symm := funext hρf
    rw [h0]
    exact isAdmP_block P (GK Bw.Kw) e R (fun n => (hR n).2.2)
  let L : FinExt l := Bw.LL
  haveI := L.2
  let r' : ↥(GK Bw.Kw) →* GL (Fin D) ↥L.1 :=
    (Units.map (RingHom.mapMatrix (algebraMap ℚ_[l] ↥L.1)).toMonoidHom).comp ρ
  have hr' : ∀ σ i j, (r' σ).val i j = algebraMap ℚ_[l] ↥L.1 ((ρ σ).val i j) := fun σ i j => rfl
  obtain ⟨T⟩ := hT
  have hc := isCrys_of_isAdmP l P AI T Bw.Kw L D ρ r' hr' hadm
  have hcρ : WeaklyAdmissibleFiltrations.IsCrys (P.PD Bw.Kw) (((Matrix.toLinAlgEquiv' : Matrix (Fin D) (Fin D) ℚ_[l] ≃ₐ[ℚ_[l]] _) : _ →* _).comp
      ((Units.coeHom _).comp ρ) : Representation ℚ_[l] ↥(GK Bw.Kw) (Fin D → ℚ_[l])) :=
    (GlobalTheory.Pst.isCrys_ext_iff (P.PD Bw.Kw) (fun g => ⟨(ρ g : Matrix (Fin D) (Fin D) ℚ_[l]), fun x => rfl, fun x => rfl⟩)).1 hc
  refine GlobalTheory.CrysSubRep.isCrysAt_of_sub l P AI ⟨T⟩ E Ω Gw O Bw D d ρ r hcρ (M.submatrix e.symm id) ?_ ?_
  · intro x y hxy
    refine hM (funext fun s => ?_)
    have := congrFun hxy (e s)
    simpa [Matrix.mulVec, dotProduct] using this
  · intro g
    have h1 := hint g
    have h3 : (ρ (Bw.e g) : Matrix (Fin D) (Fin D) ℚ_[l]) =
        (Matrix.blockDiagonal' fun n => R n (Bw.e g)).submatrix e.symm e.symm := hρf _
    rw [h3]
    have h2 : (M.submatrix e.symm id) * (r g : Matrix (Fin d) (Fin d) (Om l)) =
        (M * (r g : Matrix (Fin d) (Fin d) (Om l))).submatrix e.symm id := Matrix.ext fun _ _ => rfl
    rw [h2, ← h1]
    rw [← Matrix.submatrix_map, Matrix.submatrix_mul_equiv]
