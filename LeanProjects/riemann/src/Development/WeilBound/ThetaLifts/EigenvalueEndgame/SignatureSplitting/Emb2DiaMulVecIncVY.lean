import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.ClosedEmb
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.StabClosed
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.EmbMMul

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix MatrixGroups Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d d₁ d₂ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {W₂ : Spc F E d₂} {H : Plane E d d₁} {H₁ : Plane E d₁ d₂}

def cols {R : Type} (x y : Fin d → R) : Matrix (Fin d) (Fin 2) R := Matrix.of fun i j => ![x i, y i] j

theorem cols_vec {R : Type} [CommRing R] (x y : Fin d → R) (c : Fin 2 → R) : cols x y *ᵥ c = c 0 • x + c 1 • y := by
  ext i; simp [cols, Matrix.mulVec, dotProduct, mul_comm]

theorem cols_map (x y : Fin d → E) : (cols x y).map (inclR (F := F) (AF F)) = cols (incV F x) (incV F y) := by
  ext i j; fin_cases j <;> rfl

theorem cols_tr (J : Matrix (Fin d) (Fin d) E) (x y z : Fin d → AE F E) :
    (incM F J * (cols x y).map (cA σ))ᵀ *ᵥ z = ![fa σ J z x, fa σ J z y] := by
  ext j
  fin_cases j <;> exact dotProduct_comm _ _

theorem form_iota (hH : IsPlane σ H W W₁) (u v : Fin d₁ → E) : form σ W.J (H.ι *ᵥ u) (H.ι *ᵥ v) = form σ W₁.J u v := by
  have e : (fun i => σ ((H.ι *ᵥ v) i)) = H.ι.map σ *ᵥ fun i => σ (v i) := funext fun i => RingHom.map_mulVec σ.toRingHom H.ι v i
  rw [form, form, e, ← hH.gram, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]

theorem fa_iota2 (hH : IsPlane σ H W W₁) (u v : Fin d₁ → AE F E) : fa σ W.J (incM F H.ι *ᵥ u) (incM F H.ι *ᵥ v) = fa σ W₁.J u v := by
  have e : (fun i => cA σ ((incM F H.ι *ᵥ v) i)) = incM F (H.ι.map σ) *ᵥ fun i => cA σ (v i) :=
    incM_conj (F := F) (σ := σ) H.ι ▸ funext fun i => RingHom.map_mulVec (cA σ).toRingHom (incM F H.ι) v i
  rw [fa, fa, e, ← hH.gram, incM_mul, incM_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u]
  exact congrArg (· ⬝ᵥ _) (Matrix.vecMul_transpose _ _).symm

theorem fa_iota_y (hH : IsPlane σ H W W₁) (z : Fin d₁ → AE F E) : fa σ W.J (incM F H.ι *ᵥ z) (incV F H.y) = 0 :=
  by
    have e : H.ιᵀ *ᵥ (W.J *ᵥ fun i => σ (H.y i)) = 0 := funext fun j => by
      have := (hH.orth (Pi.single j 1)).2
      rwa [form, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec, single_one_dotProduct] at this
    rw [fa, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
      show (fun i => cA σ (incV F H.y i)) = incV F fun i => σ (H.y i) from rfl, incM_mulVec,
      show (incM F H.ι)ᵀ = incM F H.ιᵀ from rfl, incM_mulVec, e]
    simp [incV, dotProduct]

variable (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁) (hH₁ : IsPlane σ H₁ W₁ W₂)

include h hJ hH hH₁

theorem dual2 : Dual σ W.J (cols H.x (H.ι *ᵥ H₁.x)) (cols H.y (H.ι *ᵥ H₁.y)) := by
  have sk := form_skew (sig_sig h) hJ
  have ent : ∀ (x x' y y' : Fin d → E), (cols x x')ᵀ * W.J * (cols y y').map σ =
      !![form σ W.J x y, form σ W.J x y'; form σ W.J x' y, form σ W.J x' y'] := fun x x' y y' => by
    rw [Matrix.mul_assoc]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  have o1 : ∀ u, form σ W.J H.x (H.ι *ᵥ u) = 0 := fun u => by rw [sk, (hH.orth u).1, map_zero, neg_zero]
  have o2 : ∀ u, form σ W.J H.y (H.ι *ᵥ u) = 0 := fun u => by rw [sk, (hH.orth u).2, map_zero, neg_zero]
  refine ⟨sig_sig h, Matrix.ext hJ, ?_, ?_, ?_⟩
  · rw [ent, hH.xx, o1, (hH.orth _).1, form_iota hH, hH₁.xx]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  · rw [ent, hH.yy, o2, (hH.orth _).2, form_iota hH, hH₁.yy]
    ext a b
    fin_cases a <;> fin_cases b <;> rfl
  · rw [ent, hH.xy, o1, (hH.orth _).2, form_iota hH, hH₁.xy, Matrix.one_fin_two]

def emb2 : SL(2, AE F E) →* UA σ W.J :=
  ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).emb.comp Matrix.SpecialLinearGroup.toGL

theorem mat_emb2_eq_embM (g : SL(2, AE F E)) : mat (emb2 h hJ hH hH₁ g) = embM (cA σ) (incM F W.J) (cols (incV F H.x) (incM F H.ι *ᵥ incV F H₁.x))
    (cols (incV F H.y) (incM F H.ι *ᵥ incV F H₁.y)) g.1 ((g⁻¹).1.map (cA σ))ᵀ := by
  rw [incM_mulVec, incM_mulVec, ← cols_map, ← cols_map]; rfl

theorem continuous_SL2_embedding : Continuous (emb2 h hJ hH hH₁) :=
  (Dual.emb_cont ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)) (IsModuleTopology.continuous_of_linearMap (cA σ).toLinearMap)).comp Matrix.SpecialLinearGroup.continuous_toGL

theorem emb2_map_inclR (g : SL(2, E)) : emb2 h hJ hH hH₁ (Matrix.SpecialLinearGroup.map (inclR (F := F) (AF F)) g) ∈ ratU σ W.J :=
  (rat_iff _).2 ⟨embM σ W.J (cols H.x (H.ι *ᵥ H₁.x)) (cols H.y (H.ι *ᵥ H₁.y)) g.1 ((g⁻¹).1.map σ)ᵀ, by
    refine Eq.trans ?_ (embM_map (c' := cA σ) (X := cols H.x (H.ι *ᵥ H₁.x)) (Y := cols H.y (H.ι *ᵥ H₁.y)) (inclR (F := F) (AF F))
      (fun _ => rfl) _ _).symm
    rw [mat_emb2_eq_embM, ← map_inv, incM_mulVec, incM_mulVec, ← cols_map, ← cols_map]
    rfl⟩

theorem emb2_mulVec_incV_x_and_complement_x (g : SL(2, AE F E)) :
    mat (emb2 h hJ hH hH₁ g) *ᵥ incV F H.x = g.1 0 0 • incV F H.x + g.1 1 0 • incV F (H.ι *ᵥ H₁.x) ∧
    mat (emb2 h hJ hH hH₁ g) *ᵥ incV F (H.ι *ᵥ H₁.x) = g.1 0 1 • incV F H.x + g.1 1 1 • incV F (H.ι *ᵥ H₁.x) := by
  have e := ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).embX g.1 ((g⁻¹).1.map (cA σ))ᵀ
  rw [cols_map] at e
  rw [← cols_vec _ _ fun i => g.1 i 0, ← cols_vec _ _ fun i => g.1 i 1, mat_emb2_eq_embM, incM_mulVec, incM_mulVec, ← cols_map H.y]
  exact ⟨funext fun i => congrFun (congrFun e i) 0, funext fun i => congrFun (congrFun e i) 1⟩

theorem emb2_dia_mulVec_incV_y (u : (AE F E)ˣ) : mat (emb2 h hJ hH hH₁ (dia u)) *ᵥ incV F H.y = cA σ (u⁻¹).1 • incV F H.y := by
  have e := ((dual2 h hJ hH hH₁).map (c' := cA σ) (inclR (F := F) (AF F)) (fun _ => rfl) (cA_cA h)).embY (dia u).1
    (((dia u)⁻¹).1.map (cA σ))ᵀ
  rw [cols_map H.y] at e
  rw [mat_emb2_eq_embM, incM_mulVec, incM_mulVec, ← cols_map H.x]
  refine funext fun i => (congrFun (congrFun e i) 0).trans ?_
  rw [← map_inv, dia_val]
  simp [cols, Matrix.mul_apply, mul_comm]

theorem emb2_mulVec_complement_eq (g : SL(2, AE F E)) (z : Fin d₁ → AE F E) : mat (emb2 h hJ hH hH₁ g) *ᵥ (incM F H.ι *ᵥ z) =
    incM F H.ι *ᵥ (z + ((g.1 1 1 - 1) * fa σ W₁.J z (incV F H₁.y)) • incV F H₁.x -
      ((cA σ ((g⁻¹).1 1 1) - 1) * fa σ W₁.J z (incV F H₁.x)) • incV F H₁.y) + (g.1 0 1 * fa σ W₁.J z (incV F H₁.y)) • incV F H.x -
      (cA σ ((g⁻¹).1 1 0) * fa σ W₁.J z (incV F H₁.x)) • incV F H.y := by
  rw [mat_emb2_eq_embM, embM, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.one_mulVec, ← Matrix.mulVec_mulVec _ (_ * _),
    ← Matrix.mulVec_mulVec _ (_ * _), cols_tr, cols_tr, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, cols_vec, cols_vec,
    fa_iota hH, fa_iota_y hH, fa_iota2 hH, fa_iota2 hH, Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, mul_zero, zero_add,
    Matrix.sub_apply, Matrix.one_apply_eq, Matrix.one_apply_ne (zero_ne_one (α := Fin 2)), sub_zero, Matrix.transpose_apply,
    Matrix.map_apply]
  abel

theorem emb2_dia_isLevi (hJ₁ : ∀ i j, σ (W₁.J j i) = -W₁.J i j) (u : (AE F E)ˣ) {m : UA σ W₁.J} (hm : IsLevi (W₁ := W₂) H₁ u⁻¹ 1 m) :
    IsLevi H u m (emb2 h hJ hH hH₁ (dia u)) := by
  have e : ∀ z, mat (emb2 h hJ hH hH₁ (dia u)) *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (z + (((u⁻¹).1 - 1) *
      fa σ W₁.J z (incV F H₁.y)) • incV F H₁.x - ((cA σ u.1 - 1) * fa σ W₁.J z (incV F H₁.x)) • incV F H₁.y) := fun z => by
    rw [emb2_mulVec_complement_eq, ← map_inv, dia_val, dia_val]; simp
  have yx : form σ W₁.J H₁.y H₁.x = -1 := by rw [form_skew (sig_sig h) hJ₁, hH₁.xy, map_one]
  refine ⟨by simpa [dia_val] using (emb2_mulVec_incV_x_and_complement_x h hJ hH hH₁ (dia u)).1, emb2_dia_mulVec_incV_y h hJ hH hH₁ u, fr_ext h hJ₁ hH₁ ?_ ?_ ?_⟩
  · refine Matrix.ext_iff_mulVec.2 fun z => ?_
    rw [Matrix.mul_assoc _ (mat m), hm.2.2, mat_one, Matrix.mul_one, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e,
      fa_iota hH₁, fa_iota_y hH₁]
    simp
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, hm.1, fa_inc, fa_inc, hH₁.xy, hH₁.xx]
    simp [sub_smul]
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, e, hm.2.1, fa_inc, fa_inc, hH₁.yy, yx]
    simp [sub_smul]

end PositivityTheory.ThKEnd.Two

end
