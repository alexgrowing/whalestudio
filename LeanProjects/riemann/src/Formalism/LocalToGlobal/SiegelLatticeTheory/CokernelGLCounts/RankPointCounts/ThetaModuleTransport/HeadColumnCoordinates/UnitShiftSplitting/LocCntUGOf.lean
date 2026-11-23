import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.DetRel
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.CornerDeterminantCounts.CornerU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V]

theorem dl_full (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) :
    H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl]
  rfl

theorem locCntUG_of (h1 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ∀ r n, ThetaMbeG M r n)) : Formalism.L2.SG.LocalCountModules.LocCntUG.LocCntUG := by
  intro F _ _ _ E _ _ _ _ M hOK r n hmode V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD Y₁ Y₂ be₁ be₂ al₁ al₂ eY eb
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hmode
  have hg := hyp.1
  have hT := (hg.1.2.2.2.2.2 g hs).2.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hg.1.2.1.2.1, hg.1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hg.1.2.2.1.2.1, hg.1.2.2.1.2.2.1⟩
  have hMM₁ : MMInt H t₁ := by
    have hle : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
    intro m hm m' hm'
    exact (hg.1.1.2.2 m).1 (hle hm) m' (hle hm')
  let t₂ : Term V M r := ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩
  let ZZ₁ := H.ZZplus t₁
  let ZZ₂ := HermSp.ZZplusOf M (H.Zhat f₂ f₂') t₁.T t₁.T'
  have mem₁ : ∀ a b, ZZ₁ a b ∈ M.R := zz_mem_R hs H t₁ hF₁ hF₁' hT hMM₁
  let Z₁ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun a b => ⟨ZZ₁ a b, mem₁ a b⟩
  have e₁ : Z₁.map M.R.subtype = ZZ₁ := by ext a b; rfl
  have hY₁ : ZZ₁.submatrix Fin.castSucc Fin.castSucc = Y₁.Z.map M.R.subtype := by
    ext a b; exact (eY a b).1.symm
  have hY₂ : ZZ₂.submatrix Fin.castSucc Fin.castSucc = Y₂.Z.map M.R.subtype := by
    ext a b; exact (eY a b).2.symm
  have hu₁ : IsUnit (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det := by rw [hY₁]; exact Y₁.unit
  have hu₂ : IsUnit (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det := by rw [hY₂]; exact Y₂.unit
  have hrelZh : ((H.Zhat t₁.f t₁.f').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat f₂ f₂').det =
      ((H.Zhat f₂ f₂').submatrix Fin.castSucc Fin.castSucc).det * (H.Zhat t₁.f t₁.f').det := by
    rw [← dl_eq_det, ← dl_eq_det, ← dl_full, ← dl_full]
    exact hyp.2.2.2.1.2.2.2.2.2
  have hrel : (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * ZZ₂.det =
      (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det * ZZ₁.det :=
    det_rel_split hs _ _ _ _ hrelZh

  let u : E := ZZ₁.det * ↑(hu₁.unit⁻¹)
  obtain ⟨a₀, ha₀⟩ := exists_unit_shift g u
  let x : M.R := ⟨algebraMap F E a₀, alg_mem_R hs a₀⟩
  have hmapZ : ∀ Z : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R,
      (Z + cornerM r x).map M.R.subtype = Z.map M.R.subtype + cornerM r (algebraMap F E a₀) := by
    intro Z; ext i j
    simp only [Matrix.map_apply, Matrix.add_apply, cornerM, Matrix.of_apply]
    split_ifs <;> simp [x]
  have hd₁ : ZZ₁.det = (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * u := by
    simp only [u]
    rw [mul_comm, mul_assoc, IsUnit.val_inv_mul, mul_one]
  have hd₂ : ZZ₂.det = (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det * u := by
    have hh : (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * ↑(hu₁.unit⁻¹) = 1 := IsUnit.mul_val_inv hu₁
    simp only [u]
    calc ZZ₂.det = ZZ₂.det * ((ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * ↑(hu₁.unit⁻¹)) := by rw [hh, mul_one]
      _ = ((ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * ZZ₂.det) * ↑(hu₁.unit⁻¹) := by ring
      _ = _ := by rw [hrel]; ring
  have unit₁ : IsUnit ((Z₁ + cornerM r x).map M.R.subtype).det := by
    rw [hmapZ, e₁, det_add_cornerM, hd₁]
    have : (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * u +
        algebraMap F E a₀ * (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det =
        (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det * (u + algebraMap F E a₀) := by ring
    rw [this]; exact hu₁.mul ha₀
  let W₁ : M.Mat (r + 1) := ⟨Z₁ + cornerM r x, unit₁⟩
  have eY₁ : ∀ a b : Fin r, Y₁.Z a b = W₁.Z a.castSucc b.castSucc := fun a b => by
    have : W₁.Z a.castSucc b.castSucc = Z₁ a.castSucc b.castSucc := by
      simp [W₁, cornerM_castSucc_left]
    rw [this]; exact Subtype.ext (eY a b).1
  have ebe₁ : ∀ a : Fin r, be₁ a = W₁.Z a.castSucc (Fin.last r) := fun a => by
    have : W₁.Z a.castSucc (Fin.last r) = Z₁ a.castSucc (Fin.last r) := by
      simp [W₁, cornerM_castSucc_left]
    rw [this]; exact Subtype.ext (eb a).1
  have eal₁ : ∀ a : Fin r, al₁ a = W₁.Z (Fin.last r) a.castSucc := fun a => by
    have : W₁.Z (Fin.last r) a.castSucc = Z₁ (Fin.last r) a.castSucc := by
      simp [W₁, cornerM_castSucc_right]
    rw [this]; exact Subtype.ext (eb a).2.2.1
  have hhdW₁ : headDet M W₁.Z = (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det := by
    show (((Z₁ + cornerM r x).map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det = _
    rw [hmapZ, e₁, head_add_cornerM]
  have hdetW₁ : (W₁.Z.map M.R.subtype).det =
      ZZ₁.det + algebraMap F E a₀ * (ZZ₁.submatrix Fin.castSucc Fin.castSucc).det := by
    show ((Z₁ + cornerM r x).map M.R.subtype).det = _
    rw [hmapZ, e₁, det_add_cornerM]
  by_cases hint : ∀ a b, ZZ₂ a b ∈ M.R
  · let Z₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) M.R := Matrix.of fun a b => ⟨ZZ₂ a b, hint a b⟩
    have e₂ : Z₂.map M.R.subtype = ZZ₂ := by ext a b; rfl
    have unit₂ : IsUnit ((Z₂ + cornerM r x).map M.R.subtype).det := by
      rw [hmapZ, e₂, det_add_cornerM, hd₂]
      have : (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det * u +
          algebraMap F E a₀ * (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det =
          (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det * (u + algebraMap F E a₀) := by ring
      rw [this]; exact hu₂.mul ha₀
    let W₂ : M.Mat (r + 1) := ⟨Z₂ + cornerM r x, unit₂⟩
    have hu₂' : IsUnit (headDet M Z₂) := by
      show IsUnit ((Z₂.map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det
      rw [e₂]; exact hu₂
    rw [h1 F E M hOK r n hmode V H hn t₁ f₂ f₂' φ φ' hyp hD Z₁ Z₂ e₁ e₂ hu₂', ← card_isoMbe_shift Z₁ Z₂ x]
    refine Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.mbeU_holds M r W₁ W₂ Y₁ Y₂ be₁ be₂ al₁ al₂ ?_ ?_ ?_
    · intro a b
      refine ⟨eY₁ a b, ?_⟩
      have : W₂.Z a.castSucc b.castSucc = Z₂ a.castSucc b.castSucc := by
        simp [W₂, cornerM_castSucc_left]
      rw [this]; exact Subtype.ext (eY a b).2
    · intro a
      refine ⟨ebe₁ a, ?_, eal₁ a, ?_⟩
      · have : W₂.Z a.castSucc (Fin.last r) = Z₂ a.castSucc (Fin.last r) := by
          simp [W₂, cornerM_castSucc_left]
        rw [this]; exact Subtype.ext (eb a).2.1
      · have : W₂.Z (Fin.last r) a.castSucc = Z₂ (Fin.last r) a.castSucc := by
          simp [W₂, cornerM_castSucc_right]
        rw [this]; exact Subtype.ext (eb a).2.2.2
    · have hhdW₂ : headDet M W₂.Z = (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det := by
        show (((Z₂ + cornerM r x).map M.R.subtype).submatrix Fin.castSucc Fin.castSucc).det = _
        rw [hmapZ, e₂, head_add_cornerM]
      have hdetW₂ : (W₂.Z.map M.R.subtype).det =
          ZZ₂.det + algebraMap F E a₀ * (ZZ₂.submatrix Fin.castSucc Fin.castSucc).det := by
        show ((Z₂ + cornerM r x).map M.R.subtype).det = _
        rw [hmapZ, e₂, det_add_cornerM]
      rw [hhdW₁, hhdW₂, hdetW₁, hdetW₂]
      linear_combination hrel
  · have hTh : Theta H t₁ t₂ φ φ' = ∅ := by
      ext θ
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hθ
      exact hint (zz_mem_R hs H t₂ hyp.2.1 hyp.2.2.1 hT hθ.2.1)
    haveI hne : IsEmpty {ψ : M.Cok Y₁ ≃ₗ[M.R] M.Cok Y₂ //
        ψ (Submodule.Quotient.mk be₁) = Submodule.Quotient.mk be₂ ∧
          ∀ v, M.linQ Y₂ al₂ (ψ v) = M.linQ Y₁ al₁ v} := by
      refine ⟨fun ψ => hint ?_⟩
      have hc := Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUL.cornerU_holds M r W₁ (ZZ₂ + cornerM r (algebraMap F E a₀)) Y₁ Y₂
        be₁ be₂ al₁ al₂
        (fun a b => ⟨eY₁ a b, by
          show (Y₂.Z a b : E) = ZZ₂ a.castSucc b.castSucc + cornerM r (algebraMap F E a₀) a.castSucc b.castSucc
          rw [cornerM_castSucc_left, (eY a b).2, add_zero]⟩)
        (fun a => ⟨ebe₁ a, by
            show (be₂ a : E) = ZZ₂ a.castSucc (Fin.last r) + cornerM r (algebraMap F E a₀) a.castSucc (Fin.last r)
            rw [cornerM_castSucc_left, (eb a).2.1, add_zero], eal₁ a, by
            show (al₂ a : E) = ZZ₂ (Fin.last r) a.castSucc + cornerM r (algebraMap F E a₀) (Fin.last r) a.castSucc
            rw [cornerM_castSucc_right, (eb a).2.2.2, add_zero]⟩)
        (by
          rw [hhdW₁, hdetW₁, head_add_cornerM, det_add_cornerM]
          linear_combination hrel) ⟨ψ⟩
      have hcorner : ZZ₂ (Fin.last r) (Fin.last r) ∈ M.R := by
        have h' : ZZ₂ (Fin.last r) (Fin.last r) + algebraMap F E a₀ ∈ M.R := by
          have := hc
          simp only [Matrix.add_apply, cornerM_last] at this
          exact this
        have := M.R.sub_mem h' (alg_mem_R hs a₀)
        simpa using this
      intro a b
      rcases Fin.eq_castSucc_or_eq_last a with ⟨a', rfl⟩ | rfl <;>
        rcases Fin.eq_castSucc_or_eq_last b with ⟨b', rfl⟩ | rfl
      · have := (Y₂.Z a' b').2; rwa [(eY a' b').2] at this
      · have := (be₂ a').2; rwa [(eb a').2.1] at this
      · have := (al₂ b').2; rwa [(eb b').2.2.2] at this
      · exact hcorner
    show Nat.card (Theta H t₁ t₂ φ φ') = _
    rw [hTh, Nat.card_of_isEmpty, Model.nIsoBA, Nat.card_of_isEmpty]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
