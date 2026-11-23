import Mathlib
import GroundTheory.GlobalFields.LocalFieldAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBThetaDescentIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCastRfl
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB

noncomputable section

namespace GlobalTheory.SplitLiftCoord

open Matrix

section Algebra

variable {K : Type} [CommRing K] {M : Type} [Fintype M] [DecidableEq M]

def gramE (J₁ : Matrix M M K) (η : K) : Matrix (Fin 1 ⊕ M ⊕ Fin 1) (Fin 1 ⊕ M ⊕ Fin 1) K :=
  fromBlocks 0 (fromCols 0 1) (fromRows 0 (of fun _ _ => η)) (fromBlocks J₁ 0 0 0)

theorem gramE_inv {J₁ J₁' : Matrix M M K} (h : J₁' * J₁ = 1) {η η' : K} (hη : η' * η = 1) :
    fromBlocks 0 (fromCols 0 (of fun _ _ => η')) (fromRows 0 1) (fromBlocks J₁' 0 0 0) * gramE J₁ η = 1 := by
  have e : ∀ i j, ∑ l, J₁' i l * J₁ l j = (1 : Matrix M M K) i j := fun i j => by
    rw [← h]; rfl
  ext (i | i | i) (j | j | j) <;> simp [gramE, Matrix.mul_apply, Fintype.sum_sum_type, e, Matrix.one_apply,
    Fin.fin_one_eq_zero, hη]

omit [DecidableEq M] in
theorem gramE_levi {J₁ g g' : Matrix M M K} (h : gᵀ * J₁ * g' = J₁) (η : K) (x y : Kˣ) :
    (fromBlocks (of fun _ _ => (x : K)) 0 0 (fromBlocks g 0 0 (of fun _ _ => (y : K))))ᵀ * gramE J₁ η *
      fromBlocks (of fun _ _ => ((y⁻¹ : Kˣ) : K)) 0 0 (fromBlocks g' 0 0 (of fun _ _ => ((x⁻¹ : Kˣ) : K))) = gramE J₁ η := by
  have e : ∀ i j, ∑ k, (∑ l, g l i * J₁ l k) * g' k j = J₁ i j := fun i j => by
    simpa [Matrix.mul_apply] using congrFun (congrFun h i) j
  ext (i | i | i) (j | j | j) <;> simp [gramE, Matrix.mul_apply, Fintype.sum_sum_type, e, Matrix.one_apply,
    Fin.fin_one_eq_zero, mul_comm (y : K), mul_assoc]

theorem gramE_unip {J₁ J₁' : Matrix M M K} (h : J₁ * J₁' = 1) {η η' : K} (hη : η' * η = 1)
    (X : Matrix (Fin 1) (M ⊕ Fin 1) K) (Y : Matrix M (Fin 1) K) :
    ∃ (X' : Matrix (Fin 1) (M ⊕ Fin 1) K) (Y' : Matrix M (Fin 1) K),
      (fromBlocks 1 X 0 (fromBlocks 1 Y 0 1))ᵀ * gramE J₁ η * fromBlocks 1 X' 0 (fromBlocks 1 Y' 0 1) = gramE J₁ η := by
  obtain ⟨X₁, X₂, rfl⟩ : ∃ X₁ X₂, X = fromCols X₁ X₂ := ⟨_, _, (fromCols_toCols X).symm⟩
  refine ⟨fromCols (-(η' • (Yᵀ * J₁))) (-(η' • (X₂ᵀ - Yᵀ * X₁ᵀ))), -(J₁' * X₁ᵀ), ?_⟩
  have hη' : ∀ a : K, η * (η' * a) = a := fun a => by rw [← mul_assoc, mul_comm η, hη, one_mul]
  have k0 : J₁ * (J₁' * X₁ᵀ) = X₁ᵀ := by rw [← Matrix.mul_assoc, h, Matrix.one_mul]
  have k1 : ∀ i, ∑ x, ∑ i1, J₁ i x * (J₁' x i1 * X₁ 0 i1) = X₁ 0 i := fun i => by
    simpa [Matrix.mul_apply, Finset.mul_sum] using congrFun (congrFun k0 i) 0
  have k2 : ∑ x, ∑ x1, ∑ i, Y i 0 * J₁ i x * (J₁' x x1 * X₁ 0 x1) = ∑ i, Y i 0 * X₁ 0 i := by
    have e : ∀ i, Y i 0 * X₁ 0 i = ∑ x, ∑ x1, Y i 0 * J₁ i x * (J₁' x x1 * X₁ 0 x1) := fun i => by
      rw [← k1 i, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun x1 _ => by ring
    rw [Finset.sum_congr rfl fun i _ => e i]
    symm
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_comm
  ext (i | i | i) (j | j | j) <;> simp [gramE, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Fin.fin_one_eq_zero, fromCols, fromBlocks, Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_mul, hη', k1, k2]
  all_goals done

end Algebra

section Frame

open GlobalTheory.JacGeom

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem form_swap (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {ε : F}
    (hJ : ∀ i j, σ (J j i) = algebraMap F E ε * J i j) (x y : Fin n → E) :
    σ (form σ J x y) = algebraMap F E ε * form σ J y x := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_frameE (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁} {ε : F}
    (hJ : ∀ i j, σ (W.J j i) = algebraMap F E ε * W.J i j) (hxx : form σ W.J H.x H.x = 0)
    (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * W.J * H.ι.map σ = W₁.J) :
    (frame H.x H.ι H.y)ᵀ * W.J * (frame H.x H.ι H.y).map σ = gramE W₁.J (form σ W.J H.y H.x) ∧
      algebraMap F E ε * form σ W.J H.y H.x = 1 := by
  have hη : algebraMap F E ε * form σ W.J H.y H.x = 1 := by
    rw [← form_swap hσ hJ, hxy, map_one]
  have hε : algebraMap F E ε ≠ 0 := left_ne_zero_of_mul_eq_one hη
  have o : ∀ j, form σ W.J (fun r => H.ι r j) H.x = 0 ∧ form σ W.J (fun r => H.ι r j) H.y = 0 := fun j => by
    have := horth (Pi.single j 1)
    rwa [Matrix.mulVec_single_one] at this
  have o' : ∀ j, form σ W.J H.x (fun r => H.ι r j) = 0 ∧ form σ W.J H.y (fun r => H.ι r j) = 0 := fun j => by
    refine ⟨?_, ?_⟩
    · have := form_swap hσ hJ (fun r => H.ι r j) H.x
      rw [(o j).1, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hε
    · have := form_swap hσ hJ (fun r => H.ι r j) H.y
      rw [(o j).2, map_zero] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hε
  refine ⟨?_, hη⟩
  have g := hgram
  rw [Matrix.mul_assoc] at g ⊢
  ext (i | i | i) (j | j | j)
  · exact hxx
  · exact (o' j).1.trans (by simp [gramE])
  · exact hxy.trans (by simp [gramE, Subsingleton.elim i j])
  · exact (o i).1.trans (by simp [gramE])
  · exact (congrFun (congrFun g i) j).trans (by simp [gramE])
  · exact (o i).2.trans (by simp [gramE])
  · first
      | (simp [gramE]; done)
      | (simp [gramE]; rfl)
      | rfl
  · exact (o' j).2.trans (by simp [gramE])
  · exact hyy.trans (by simp [gramE])

end Frame

section Shapes

open GlobalTheory.SmGL GlobalTheory.IndLineGL

variable {k : Type} [Field k]

def threeBlockSumEquiv (m : ℕ) : Fin 1 ⊕ Fin m ⊕ Fin 1 ≃ (Σ i : Fin 3, Fin (blk3 m i)) :=
  Equiv.ofBijective (Sum.elim (fun i => ⟨0, i⟩) (Sum.elim (fun i => ⟨1, i⟩) (fun i => ⟨2, i⟩)))
    ((Fintype.bijective_iff_surjective_and_card _).2 ⟨by
      rintro ⟨i, j⟩
      fin_cases i
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr (Sum.inl j), rfl⟩
      · exact ⟨Sum.inr (Sum.inr j), rfl⟩, by simp [Fin.sum_univ_three, add_assoc]⟩)

theorem unip_blocks {n m : ℕ} {e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n} {u : GL (Fin n) k}
    (hu : u ∈ unipRad k e) :
    u.val.submatrix ((threeBlockSumEquiv m).trans e) ((threeBlockSumEquiv m).trans e) =
      fromBlocks 1 (of fun i j => u.val ((threeBlockSumEquiv m).trans e (Sum.inl i)) ((threeBlockSumEquiv m).trans e (Sum.inr j))) 0
        (fromBlocks 1 (of fun i j => u.val ((threeBlockSumEquiv m).trans e (Sum.inr (Sum.inl i)))
          ((threeBlockSumEquiv m).trans e (Sum.inr (Sum.inr j)))) 0 1) := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hu
  have h3 := mem_parab_iff.1 h1
  ext (i | i | i) (j | j | j) <;> rw [submatrix_apply]
  · exact h2 0 i j
  · rfl
  · rfl
  · exact h3 1 0 i j (by decide)
  · exact h2 1 i j
  · rfl
  · exact h3 2 0 i j (by decide)
  · exact h3 2 1 i j (by decide)
  · exact h2 2 i j

theorem levi_blocks {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n)
    (l : Levi k (fun i : Fin 3 => Fin (blk3 m i))) (x y : kˣ) (g : GL (Fin m) k)
    (h0 : ∀ i j, (l 0).val i j = x) (h1 : ∀ i j, (l 1).val i j = g.val i j) (h2 : ∀ i j, (l 2).val i j = y) :
    (leviEmb k e l).val.submatrix ((threeBlockSumEquiv m).trans e) ((threeBlockSumEquiv m).trans e) =
      fromBlocks (of fun _ _ => (x : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => (y : k))) := by
  ext (i | i | i) (j | j | j) <;> rw [submatrix_apply]
  · exact (leviEmb_apply_same k e l 0 i j).trans (h0 i j)
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact (leviEmb_apply_same k e l 1 i j).trans (h1 i j)
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact leviEmb_apply_ne k e l (by decide) _ _
  · exact (leviEmb_apply_same k e l 2 i j).trans (h2 i j)

theorem midIncl_blocks {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (g : GL (Fin m) k) :
    (leviEmb k e (midIncl k m g)).val.submatrix ((threeBlockSumEquiv m).trans e) ((threeBlockSumEquiv m).trans e) =
      fromBlocks (of fun _ _ => ((1 : kˣ) : k)) 0 0 (fromBlocks g.val 0 0 (of fun _ _ => ((1 : kˣ) : k))) := by
  refine levi_blocks e _ 1 1 g (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
  · obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
    show ((Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) (1 : Fin 3) (show GL (Fin (blk3 m 1)) k from g)) 0).val i i = _
    rw [Pi.mulSingle_eq_of_ne (by decide : (0 : Fin 3) ≠ 1)]
    simp
  · show ((Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) (1 : Fin 3) (show GL (Fin (blk3 m 1)) k from g)) 1).val i j = _
    rw [Pi.mulSingle_eq_same]
  · obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
    show ((Pi.mulSingle (M := fun i : Fin 3 => GL (Fin (blk3 m i)) k) (1 : Fin 3) (show GL (Fin (blk3 m 1)) k from g)) 2).val i i = _
    rw [Pi.mulSingle_eq_of_ne (by decide : (2 : Fin 3) ≠ 1)]
    simp

end Shapes

section TorusShape

theorem scalar_fin_one_apply {k : Type} [Field k] (t : kˣ) (i : Fin 1) :
    (Matrix.GeneralLinearGroup.scalar (Fin 1) t).val i i = t := by
  first
    | (simp [Matrix.GeneralLinearGroup.scalar]; done)
    | (simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map, MonoidHom.coe_coe]; simp; done)
    | (rw [Matrix.GeneralLinearGroup.scalar, Units.coe_map]; simp; done)
    | (simp [Matrix.GeneralLinearGroup.scalar, Units.coe_map, Matrix.scalar_apply]; done)
    | rfl

open GlobalTheory.SmGL GlobalTheory.IndLineGL

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem torus_blocks {n m : ℕ} (e : (Σ i : Fin 3, Fin (blk3 m i)) ≃ Fin n) (t₁ t₂ : kˣ) :
    (leviEmb k e (torusPt k m t₁ t₂)).val.submatrix ((threeBlockSumEquiv m).trans e) ((threeBlockSumEquiv m).trans e) =
      fromBlocks (of fun _ _ => (t₁ : k)) 0 0 (fromBlocks (1 : GL (Fin m) k).val 0 0 (of fun _ _ => (t₂ : k))) := by
  refine levi_blocks e _ t₁ t₂ 1 (fun i j => ?_) (fun i j => ?_) (fun i j => ?_)
  · obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
    rw [torusPt_zero]
    exact scalar_fin_one_apply t₁ i
  · rw [torusPt_one]
    rfl
  · obtain rfl : i = j := Subsingleton.elim (α := Fin 1) i j
    rw [torusPt_two]
    exact scalar_fin_one_apply t₂ i

end TorusShape

section Adelic

open GlobalTheory.SplitGLLift GlobalTheory.KSplit GlobalTheory.JacGeom GlobalTheory.SplitUnitLift
open GlobalTheory.Div.CoordOpp (unit_map)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}

theorem exists_lift_frame (hcm : IsCMExt F E σ) (τ : E →ₐ[F] Fv F v) {n n₁ : ℕ} {W : Spc F E n} {W₁ : Spc F E n₁}
    {H : Plane E n n₁} {εW : F} (hermW : ∀ i j, σ (W.J j i) = algebraMap F E εW * W.J i j)
    (hJW : IsUnit (W.J.map τ).det) (hJ₁ : IsUnit (W₁.J.map τ).det) {η : E} (hη : algebraMap F E εW * η = 1)
    (hG : (frame H.x H.ι H.y)ᵀ * W.J * (frame H.x H.ι H.y).map σ = gramE W₁.J η)
    (e : Fin 1 ⊕ Fin n₁ ⊕ Fin 1 ≃ Fin n) :
    ∃ c : GL (Fin n) (Fv F v), ∀ (g : GL (Fin n) (Fv F v))
      (N : Matrix (Fin 1 ⊕ Fin n₁ ⊕ Fin 1) (Fin 1 ⊕ Fin n₁ ⊕ Fin 1) (AE F E)),
      At (evFin F v) (N - 1) → N.map (piW τ) = g.val.submatrix e e →
        (g.val.submatrix e e)ᵀ * gramE (W₁.J.map τ) (τ η) * N.map (piW (τ.comp σ)) = gramE (W₁.J.map τ) (τ η) →
        mat (liftU hcm τ W.J εW hermW hJW (c * g * c⁻¹)) * frame (incV F H.x) (incM F H.ι) (incV F H.y) =
          frame (incV F H.x) (incM F H.ι) (incV F H.y) * N := by
  set P := frame H.x H.ι H.y with hP
  have hGτ : (P.map τ)ᵀ * W.J.map τ * P.map (τ.comp σ) = gramE (W₁.J.map τ) (τ η) := by
    have := congrArg (fun Z => Z.map (τ : E →+* Fv F v)) hG
    simp only [Matrix.map_mul, Matrix.transpose_map] at this
    refine this.trans ?_
    ext (i | i | i) (j | j | j) <;> simp [gramE, Matrix.one_apply, Fin.fin_one_eq_zero]
  have hη' : algebraMap F (Fv F v) εW * τ η = 1 := by
    have := congrArg τ hη
    rwa [map_mul, AlgHom.commutes, map_one] at this
  have hΓ := gramE_inv (Matrix.nonsing_inv_mul _ hJ₁) hη'
  generalize fromBlocks _ _ _ _ = Γ' at hΓ
  have hc : IsUnit ((P.map τ).submatrix id e.symm) := by
    rw [← Matrix.isUnit_transpose]
    refine IsUnit.of_mul_eq_one ((W.J.map τ * P.map (τ.comp σ) * Γ').submatrix id e.symm) ?_
    rw [Matrix.transpose_submatrix, ← Matrix.submatrix_mul _ _ _ id _ Function.bijective_id, ← Matrix.mul_assoc,
      ← Matrix.mul_assoc, hGτ, mul_eq_one_comm.1 hΓ, Matrix.submatrix_one_equiv]
  obtain ⟨c, hcv⟩ : ∃ c : GL (Fin n) (Fv F v), c.val = (P.map τ).submatrix id e.symm := ⟨hc.unit, rfl⟩
  refine ⟨c, fun g N hN h1 h2 => ?_⟩
  have a1 : (mat (liftU hcm τ W.J εW hermW hJW (c * g * c⁻¹))).map (piW τ) * P.map τ =
      P.map τ * g.val.submatrix e e := by
    have b1 : (mat (liftU hcm τ W.J εW hermW hJW (c * g * c⁻¹))).map (piW τ) * c.val =
        c.val * g.val := by
      rw [liftU_piW, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul]
    have b2 : P.map τ = c.val.submatrix id e := by rw [hcv]; simp
    rw [b2, Matrix.submatrix_mul_equiv, ← b1]
    rfl
  have a2 := adj_intertwine e hGτ hΓ (N₀ := (g⁻¹).val.submatrix e e)
    (by rw [Matrix.submatrix_mul_equiv, Units.mul_inv, Matrix.submatrix_one_equiv])
    (unit_map σ (liftU hcm τ W.J εW hermW hJW (c * g * c⁻¹)) τ) a1 h2
  have a3 : frame (incV F H.x) (incM F H.ι) (incV F H.y) = incM F P := by
    ext r (j | j | j) <;> rfl
  rw [a3]
  exact adelic_intertwine hcm τ (liftU_mem_UAt hcm τ W εW hermW hJW _) hN (by rw [h1]; exact a1) a2

end Adelic

end GlobalTheory.SplitLiftCoord

open GlobalTheory.SplitLiftCoord GlobalTheory.SplitGLLift GlobalTheory.KSplit GlobalTheory.JacGeom GlobalTheory.SplitUnitLift in
open GlobalTheory.Div.CoordOpp (unit_map) in

theorem GlobalTheory.SplitLiftCoord.exists_lift_coords : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (hcm : IsCMExt F E σ) (v : Pl F) (τ : E →ₐ[F] Fv F v)
    (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), n = n₁ + 2 → form σ W.J H.x H.x = 0 →
    form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
    (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
    ∀ (εW : F) (hermW : ∀ i j, σ (W.J j i) = algebraMap F E εW * W.J i j) (hJW : IsUnit (W.J.map τ).det)
      (ε₁ : F) (herm₁ : ∀ i j, σ (W₁.J j i) = algebraMap F E ε₁ * W₁.J i j) (hJ₁ : IsUnit (W₁.J.map τ).det)
      (e : (Σ i : Fin 3, Fin (GlobalTheory.IndLineGL.blk3 n₁ i)) ≃ Fin n),
      ∃ c : GL (Fin n) (Fv F v),
        (∀ u ∈ GlobalTheory.SmGL.unipRad (Fv F v) e,
          GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW (c * u * c⁻¹) ∈ unip σ W H) ∧
        (∀ h : GL (Fin n₁) (Fv F v), IsLevi (W₁ := W₁) H 1 (GlobalTheory.SplitUnitLift.liftU hcm τ W₁.J ε₁ herm₁ hJ₁ h)
          (GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW
            (c * GlobalTheory.SmGL.leviEmb (Fv F v) e (GlobalTheory.IndLineGL.midIncl (Fv F v) n₁ h) * c⁻¹))) ∧
        ∀ t₁ t₂ : (Fv F v)ˣ, IsLevi (W₁ := W₁) H (GlobalTheory.JacGeom.idl hcm τ (t₁, t₂⁻¹)) 1
          (GlobalTheory.SplitUnitLift.liftU hcm τ W.J εW hermW hJW
            (c * GlobalTheory.SmGL.leviEmb (Fv F v) e (GlobalTheory.IndLineGL.torusPt (Fv F v) n₁ t₁ t₂) * c⁻¹)) := by
  intro F E _ _ _ _ _ σ hcm v τ n n₁ W W₁ H _ hxx hyy hxy horth hgram εW hermW hJW ε₁ herm₁ hJ₁ e
  have hσ : ∀ x, σ (σ x) = x := GlobalTheory.OppLagr.conj_conj hcm
  obtain ⟨hG, hη⟩ := gram_frameE hσ hermW hxx hyy hxy horth hgram
  have hη' : algebraMap F (Fv F v) εW * τ (form σ W.J H.y H.x) = 1 := by
    have := congrArg τ hη
    rwa [map_mul, AlgHom.commutes, map_one] at this
  obtain ⟨c, hc⟩ := exists_lift_frame hcm τ hermW hJW hJ₁ hη hG ((threeBlockSumEquiv n₁).trans e)
  have lev : ∀ (l : GlobalTheory.SmGL.Levi (Fv F v) fun i : Fin 3 => Fin (GlobalTheory.IndLineGL.blk3 n₁ i)) (x y : (Fv F v)ˣ)
      (g : GL (Fin n₁) (Fv F v)),
      (GlobalTheory.SmGL.leviEmb (Fv F v) e l).val.submatrix ((threeBlockSumEquiv n₁).trans e) ((threeBlockSumEquiv n₁).trans e) =
        Matrix.fromBlocks (Matrix.of fun _ _ => (x : Fv F v)) 0 0
          (Matrix.fromBlocks g.val 0 0 (Matrix.of fun _ _ => (y : Fv F v))) →
      IsLevi (W₁ := W₁) H (idl hcm τ (x, y⁻¹)) (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ g)
        (liftU hcm τ W.J εW hermW hJW (c * GlobalTheory.SmGL.leviEmb (Fv F v) e l * c⁻¹)) := by
    intro l x y g hu
    have hh₁ := liftU_mem_UAt hcm τ W₁ ε₁ herm₁ hJ₁ g
    have g2 : (mat (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ g)).map (piW τ) = g.val := liftU_piW hcm τ W₁.J ε₁ herm₁ hJ₁ g
    have si : cA σ ((idl hcm τ (x, y⁻¹))⁻¹ : (AE F E)ˣ).val = idl hcm τ (y, x⁻¹) := by
      rw [← map_inv, Prod.inv_mk, inv_inv, cA_idl]
    rw [IsLevi, si]
    refine cols_levi (hc _ _ (fun a ha => ?_) ?_ ?_)
    · have b1 := at_idl hcm τ x y⁻¹ a ha
      have b2 := at_idl hcm τ y x⁻¹ a ha
      have b3 := fun i j => congrFun (congrFun (hh₁ a ha) i) j
      ext (i | i | i) (j | j | j)
      all_goals first
        | (simp [Matrix.one_apply, Fin.fin_one_eq_zero, b1, b2]; done)
        | simpa [Matrix.one_apply] using b3 i j
    · rw [hu, ← g2]
      ext (i | i | i) (j | j | j) <;> simp [piW_idl]
    · rw [hu]
      refine Eq.trans ?_ (gramE_levi (g' := (mat (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ g)).map (piW (τ.comp σ)))
        (g2 ▸ unit_map σ (liftU hcm τ W₁.J ε₁ herm₁ hJ₁ g) τ) (τ (form σ W.J H.y H.x)) x y)
      congr 1
      ext (i | i | i) (j | j | j) <;> simp [piW_comp_idl]
  refine ⟨c, fun u hu => ?_, fun g => ?_, fun t₁ t₂ => ?_⟩
  · obtain ⟨X, Y, hs⟩ : ∃ X Y, u.val.submatrix ((threeBlockSumEquiv n₁).trans e) ((threeBlockSumEquiv n₁).trans e) =
        Matrix.fromBlocks 1 X 0 (Matrix.fromBlocks 1 Y 0 1) := ⟨_, _, unip_blocks hu⟩
    obtain ⟨X', Y', hX⟩ := gramE_unip (Matrix.mul_nonsing_inv _ hJ₁) hη' X Y
    refine Subgroup.subset_closure (cols_unip (X := Matrix.of fun i j => liftPair hcm τ (X i j, X' i j))
      (Y := Matrix.of fun i j => liftPair hcm τ (Y i j, Y' i j)) (hc u _ (fun a ha => ?_) ?_ ?_))
    · ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, at_liftPair hcm τ _ a ha]
    · rw [hs]
      ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_liftPair, apply_ite (piW τ)]
    · rw [hs]
      refine Eq.trans ?_ hX
      congr 1
      ext (i | i | i) (j | j | j) <;> simp [Matrix.one_apply, piW_comp_liftPair, apply_ite (piW (τ.comp σ))]
  · have := lev _ 1 1 g (midIncl_blocks e g)
    have h1 : idl hcm τ (1, 1⁻¹) = 1 := by rw [inv_one]; exact map_one (idl hcm τ)
    rwa [h1] at this
  · have := lev _ t₁ t₂ 1 (torus_blocks e t₁ t₂)
    rwa [map_one] at this
