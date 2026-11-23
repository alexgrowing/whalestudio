import Development.WeilBound.ThetaLifts.EigenvalueEndgame.UnipotentGroups.IsFrPlane
import Development.WeilBound.ThetaLifts.EigenvalueEndgame.SignatureSplitting.StageSub

noncomputable section

set_option linter.unusedSectionVars false

namespace PositivityTheory.ThKEnd.Two

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK PositivityTheory.ThKEnd.Grp PositivityTheory.ThKG.Tow.Levi

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H : Plane E d d₁}

theorem inc_inj : Function.Injective (inclR (F := F) (E := E) (AF F)) := by
  have : Nontrivial (AF F) := inferInstanceAs (Nontrivial (InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F))
  have : Nontrivial (AE F E) := Algebra.TensorProduct.nontrivial_of_algebraMap_injective_of_flat_left F _ _ (algebraMap F E).injective
  exact RingHom.injective _

theorem rat_iff {J : Matrix (Fin d) (Fin d) E} (g : UA σ J) : g ∈ ratU σ J ↔ ∃ A, mat g = incM F A := by
  refine ⟨fun ⟨A, h⟩ => ⟨A.1, (congrArg Units.val h).symm⟩, fun ⟨A, h⟩ => ?_⟩
  have h1 : A.det ≠ 0 := fun h0 => by
    have := congrArg Matrix.det (mat_mul_inv g)
    rw [Matrix.det_mul, h, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det, h0, map_zero, zero_mul, Matrix.det_one] at this
    exact zero_ne_one (inc_inj (F := F) (E := E) (by rw [map_zero, map_one, this]))
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero A h1, Units.ext h.symm⟩

theorem cont_hom {B : Type} [Group B] [TopologicalSpace B] [IsTopologicalGroup B] {J : Matrix (Fin d) (Fin d) E} (φ : B →* UA σ J)
    (h : Continuous fun b => mat (φ b)) : Continuous φ :=
  (Units.continuous_iff.2 ⟨h, (h.comp continuous_inv).congr fun b => by simp only [Function.comp, map_inv]; rfl⟩ :
    Continuous fun b => (φ b).1).subtype_mk _

theorem lat_of_good {J : Matrix (Fin d) (Fin d) E} [DiscreteTopology (ratU σ J)] {N : Subgroup (UA σ J)} (h : UnipGood N) :
    Lat ((ratU σ J).subgroupOf N) :=
  haveI := PositivityTheory.ThKF.countable_ratU σ J
  ⟨h.cnt, DiscreteTopology.of_continuous_injective (f := fun γ => (⟨γ.1.1, γ.2⟩ : ratU σ J))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun a b h => Subtype.ext (Subtype.ext (congrArg Subtype.val h :)), h.cov⟩

theorem conj_unipU {U : Submodule E (Fin d → E)} {γ m : UA σ W.J} (hγ : γ ∈ ratU σ W.J)
    (h1 : ∀ u ∈ U, ∃ u' ∈ U, mat γ *ᵥ incV F u = incV F u') (h2 : ∀ u ∈ U, ∃ u' ∈ U, mat γ⁻¹ *ᵥ incV F u = incV F u')
    (hm : m ∈ unipU σ W U) : γ⁻¹ * m * γ ∈ unipU σ W U := by
  rw [(unipU_eq U).choose_spec.choose_spec.2] at hm ⊢
  obtain ⟨A, hA⟩ := (rat_iff γ).1 hγ
  simp only [mat_mul, ← Matrix.mulVec_mulVec]
  refine ⟨fun u hu => ?_, fun z hz => ?_⟩
  · obtain ⟨u', a, b⟩ := h1 u hu
    rw [b, hm.1 u' a, inv_vec b]
  · have e : mat γ *ᵥ incV F z = incV F (A *ᵥ z) := by rw [hA, incM_mulVec]
    have := hm.2 (A *ᵥ z) fun u hu => by
      obtain ⟨u', a, b⟩ := h2 u hu
      have b' := inv_vec b
      rw [inv_inv] at b'
      refine inc_inj (F := F) ?_
      rw [← fa_inc, ← e, ← b', fa_mat, fa_inc, hz u' a]
    rw [e]
    conv => enter [2, 2]; rw [← inv_vec e]
    rw [← Matrix.mulVec_sub]
    refine Submodule.mem_comap.1 ((Submodule.span_le (p := Submodule.comap (mat γ⁻¹).mulVecLin
      (Submodule.span (AE F E) (incV F '' (U : Set (Fin d → E)))))).2 ?_ this)
    rintro _ ⟨u, hu, rfl⟩
    obtain ⟨u', a, b⟩ := h2 u hu
    exact Submodule.subset_span ⟨u', a, b.symm⟩

variable (σ W) in

def stab (x : Fin d → E) : Subgroup (UA σ W.J) where
  carrier := {u | mat u *ᵥ incV F x = incV F x}
  one_mem' := Matrix.one_mulVec _
  mul_mem' := fun {a b} ha hb => by
    change (mat a * mat b) *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, hb, ha]
  inv_mem' := fun ha => inv_vec ha

theorem stab_closed (x : Fin d → E) : IsClosed (stab σ W x : Set (UA σ W.J)) :=
  isClosed_eq (continuous_mat.matrix_mulVec continuous_const) continuous_const

variable (h : IsCMExt F E σ) (hJ : ∀ i j, σ (W.J j i) = -W.J i j) (hH : IsPlane σ H W W₁)

include h hJ hH

theorem exists_Q : ∃ Q : Matrix (Fin d₁) (Fin d) E, incM F Q * incM F H.ι = 1 ∧ incM F Q *ᵥ incV F H.x = 0 ∧ incM F Q *ᵥ incV F H.y = 0 := by
  obtain ⟨A, -, h2⟩ := fr_inv (form_yx h (Or.inr hJ) hH) hH
  refine ⟨A.submatrix Sum.inl id, ?_, ?_, ?_⟩
  · rw [← incM_mul, ← incM_one]
    congr 1
    ext i j
    exact (congrFun (congrFun h2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  · rw [incM_mulVec]
    exact funext fun i => (congrArg _ (congrFun (congrFun h2 (Sum.inl i)) (Sum.inr 0))).trans (map_zero _)
  · rw [incM_mulVec]
    exact funext fun i => (congrArg _ (congrFun (congrFun h2 (Sum.inl i)) (Sum.inr 1))).trans (map_zero _)

theorem fr_ext {n : Type} {M N : Matrix n (Fin d) (AE F E)} (h1 : M * incM F H.ι = N * incM F H.ι)
    (h2 : M *ᵥ incV F H.x = N *ᵥ incV F H.x) (h3 : M *ᵥ incV F H.y = N *ᵥ incV F H.y) : M = N := by
  obtain ⟨A, h4, -⟩ := fr_inv (form_yx h (Or.inr hJ) hH) hH
  have e : M * incM F (fr H.ι H.x H.y) = N * incM F (fr H.ι H.x H.y) := by
    ext i (j | j)
    · exact congrFun (congrFun h1 i) j
    · fin_cases j
      exacts [congrFun h2 i, congrFun h3 i]
  rw [← Matrix.mul_one M, ← Matrix.mul_one N, ← incM_one, ← h4, incM_mul, ← Matrix.mul_assoc, e, Matrix.mul_assoc]

theorem levi_uniq {t : (AE F E)ˣ} {y : UA σ W₁.J} {m m' : UA σ W.J} (a : IsLevi H t y m) (b : IsLevi H t y m') : m = m' :=
  mat_inj (fr_ext h hJ hH (a.2.2.trans b.2.2.symm) (a.1.trans b.1.symm) (a.2.1.trans b.2.1.symm))

omit h hJ hH in
theorem levi_mul {t t' : (AE F E)ˣ} {y y' : UA σ W₁.J} {m m' : UA σ W.J} (a : IsLevi H t y m) (b : IsLevi H t' y' m') :
    IsLevi H (t * t') (y * y') (m * m') := by
  refine ⟨?_, ?_, ?_⟩
  · rw [mat_mul, ← Matrix.mulVec_mulVec, b.1, Matrix.mulVec_smul, a.1, smul_smul, mul_comm, Units.val_mul]
  · rw [mat_mul, ← Matrix.mulVec_mulVec, b.2.1, Matrix.mulVec_smul, a.2.1, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · rw [mat_mul, Matrix.mul_assoc, b.2.2, ← Matrix.mul_assoc, a.2.2, mat_mul, Matrix.mul_assoc]

theorem iota_inj {z z' : Fin d₁ → AE F E} {a a' : AE F E}
    (e : incM F H.ι *ᵥ z + a • incV F H.x = incM F H.ι *ᵥ z' + a' • incV F H.x) : z = z' := by
  obtain ⟨Q, q1, q2, -⟩ := exists_Q h hJ hH
  simpa [Matrix.mulVec_add, Matrix.mulVec_smul, q1, q2] using congrArg (incM F Q *ᵥ ·) e

theorem levi_data : ∃ (lev : UA σ W₁.J →* UA σ W.J) (ρ : stab σ W H.x →* UA σ W₁.J), Continuous lev ∧ Continuous ρ ∧
    (∀ y, IsLevi H 1 y (lev y)) ∧ (∀ y ∈ ratU σ W₁.J, lev y ∈ ratU σ W.J) ∧ (∀ u, u.1 ∈ ratU σ W.J → ρ u ∈ ratU σ W₁.J) ∧
    ∀ u z, ∃ a : AE F E, mat u.1 *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (mat (ρ u) *ᵥ z) + a • incV F H.x := by
  obtain ⟨Q, q1, q2, q3⟩ := exists_Q h hJ hH
  choose l hl using (leviPlane F E σ h d d₁ W W₁ H hJ hH).1 1
  have e : ∀ y, mat (l y) = incM F H.ι * mat y * incM F Q + incM F (1 - H.ι * Q) := fun y => by
    rw [incM_sub, incM_one, incM_mul]
    refine fr_ext h hJ hH ?_ ?_ ?_
    · simp [(hl y).2.2, Matrix.add_mul, Matrix.sub_mul, Matrix.mul_assoc, q1]
    · simp [(hl y).1, Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, q2]
    · simp [(hl y).2.1, Matrix.add_mulVec, Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, q3]
  have fr := (isFr_plane h hJ hH).map (inclR (F := F) (AF F)) (c' := (cA σ : AE F E →+* AE F E)) fun _ => rfl
  have st : ∀ u : stab σ W H.x, (incM F Q * mat u.1 * incM F H.ι)ᵀ * incM F W₁.J * (incM F Q * mat u.1 * incM F H.ι).map (cA σ) =
      incM F W₁.J ∧ ∀ z, ∃ a : AE F E, mat u.1 *ᵥ (incM F H.ι *ᵥ z) =
        incM F H.ι *ᵥ ((incM F Q * mat u.1 * incM F H.ι) *ᵥ z) + a • incV F H.x := fun u => by
    obtain ⟨g, α, g1, g2⟩ := fr.stab (mul_one 1) (mat_unit u.1) (u.2.trans (one_smul _ _).symm)
    change ∀ z, mat u.1 *ᵥ (incM F H.ι *ᵥ z) = incM F H.ι *ᵥ (g *ᵥ z) + (α ⬝ᵥ z) • incV F H.x at g2
    have : incM F Q * mat u.1 * incM F H.ι = g := Matrix.ext_iff_mulVec.2 fun z => by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, g2, Matrix.mulVec_add, Matrix.mulVec_smul, q2, smul_zero, add_zero,
        Matrix.mulVec_mulVec _ (incM F Q), q1, Matrix.one_mulVec]
    exact this ▸ ⟨g1, fun z => ⟨_, g2 z⟩⟩
  have mu : ∀ u v : stab σ W H.x, incM F Q * mat (u * v).1 * incM F H.ι =
      incM F Q * mat u.1 * incM F H.ι * (incM F Q * mat v.1 * incM F H.ι) := fun u v => Matrix.ext_iff_mulVec.2 fun z => by
    obtain ⟨a, ha⟩ := (st v).2 z
    rw [← Matrix.mulVec_mulVec z (_ * _ * _), Subgroup.coe_mul, mat_mul, ← Matrix.mulVec_mulVec z, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_add, Matrix.mulVec_smul, u.2, Matrix.mulVec_add, Matrix.mulVec_smul, q2, smul_zero,
      add_zero]
    simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
  have on : incM F Q * mat (1 : stab σ W H.x).1 * incM F H.ι = 1 := by rw [OneMemClass.coe_one, mat_one, Matrix.mul_one, q1]
  let ρ : stab σ W H.x →* UA σ W₁.J := MonoidHom.mk' (fun u => ⟨⟨incM F Q * mat u.1 * incM F H.ι, incM F Q * mat (u⁻¹).1 * incM F H.ι,
    by rw [← mu, mul_inv_cancel, on], by rw [← mu, inv_mul_cancel, on]⟩, (st u).1⟩) fun u v => mat_inj (mu u v)
  let lev : UA σ W₁.J →* UA σ W.J := MonoidHom.mk' l fun y y' =>
    levi_uniq h hJ hH (hl _) (by simpa using levi_mul (hl y) (hl y'))
  refine ⟨lev, ρ, cont_hom lev ?_, cont_hom ρ ?_, hl, fun y hy => ?_, fun u hu => ?_, fun u => (st u).2⟩
  · exact (((continuous_const.matrix_mul continuous_mat).matrix_mul continuous_const).add continuous_const).congr fun y => (e y).symm
  · exact (continuous_const.matrix_mul (continuous_mat.comp continuous_subtype_val)).matrix_mul continuous_const
  · obtain ⟨A, hA⟩ := (rat_iff y).1 hy
    refine (rat_iff _).2 ⟨H.ι * A * Q + (1 - H.ι * Q), (e y).trans ?_⟩
    rw [hA, ← incM_mul, ← incM_mul]
    exact Matrix.ext fun _ _ => (map_add (inclR (F := F) (E := E) (AF F)) _ _).symm
  · obtain ⟨A, hA⟩ := (rat_iff u.1).1 hu
    exact (rat_iff _).2 ⟨Q * A * H.ι, by rw [incM_mul, incM_mul, ← hA]; rfl⟩

end PositivityTheory.ThKEnd.Two

end
