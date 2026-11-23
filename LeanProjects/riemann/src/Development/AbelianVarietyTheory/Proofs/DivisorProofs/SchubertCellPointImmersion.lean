import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open GlobalTheory.ProjSpace

namespace GlobalTheory.FlagZ

theorem isImmersion_of_X_mem_range {σ : Type} {Y : Scheme.{0}} (f : Sp (MvPolynomial σ ℤ) ⟶ Y) (U : Y.Opens)
    (h : ⊤ ≤ f ⁻¹ᵁ U) (hX : ∀ s, fnOn ⊤ (MvPolynomial.X s) ∈ (f.appLE U ⊤ h).hom.range) : IsImmersion f := by
  choose t ht using hX
  let ψ : CommRingCat.of (MvPolynomial σ ℤ) ⟶ Γ(Y, U) :=
    CommRingCat.ofHom (MvPolynomial.eval₂Hom (Int.castRingHom _) t)
  have e : ψ ≫ f.appLE U ⊤ h = CommRingCat.ofHom (fnOn ⊤) := by
    ext1
    refine MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) fun s => ?_
    rw [CommRingCat.hom_ofHom, ← ht s]
    simp [ψ]
  have i₁ : IsIso (CommRingCat.ofHom (fnOn (A := MvPolynomial σ ℤ) ⊤)) :=
    (ConcreteCategory.isIso_iff_bijective _).2 fnOn_top_bijective
  have i₂ : IsIso (⊤ : (Sp (MvPolynomial σ ℤ)).Opens).toSpecΓ :=
    (isAffineOpen_top _).isoSpec.isIso_hom
  have i₃ : IsImmersion (f.resLE U ⊤ h ≫ U.toSpecΓ ≫ Spec.map ψ) := by
    rw [← Scheme.Opens.toSpecΓ_SpecMap_appLE_assoc, ← Spec.map_comp, e]
    infer_instance
  have i₄ : IsImmersion (f.resLE U ⊤ h) := IsImmersion.of_comp _ (U.toSpecΓ ≫ Spec.map ψ)
  have e₂ : f = (Sp (MvPolynomial σ ℤ)).topIso.inv ≫ f.resLE U ⊤ h ≫ U.ι := by
    rw [Scheme.Hom.resLE_comp_ι, ← Scheme.topIso_hom, Iso.inv_hom_id_assoc]
  rw [e₂]
  infer_instance

variable {N : ℕ} {A : Type} [CommRing A]

theorem exists_det_eq_sign_mul_minor (g : Matrix (Fin N) (Fin N) A) (l : Fin (N + 1)) (e : Fin l → Fin N)
    (he : Function.Injective e) :
    ∃ (I : Rows N l) (ε : ℤˣ), (g.submatrix e (Fin.castLE l.is_le)).det = ((ε : ℤ) : A) * minor g l I := by
  let I : Rows N l := ⟨Finset.univ.map ⟨e, he⟩, by simp [Set.powersetCard.mem_iff]⟩
  have hr : Set.range e = Set.range (subsetEnum I) := by
    rw [range_subsetEnum]
    simp [I]
  let p : Equiv.Perm (Fin l) := (Equiv.ofInjective e he).trans
    ((Equiv.setCongr hr).trans (Equiv.ofInjective _ (subsetEnum_injective I)).symm)
  have hp : subsetEnum I ∘ p = e := funext fun x => Equiv.apply_ofInjective_symm (subsetEnum_injective I) _
  refine ⟨I, Equiv.Perm.sign p, ?_⟩
  rw [minor, ← det_permute, submatrix_submatrix, hp]
  rfl

theorem det_updateRow_of_col_eq {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n A) (hM : M.det = 1) (j : n)
    (hj : ∀ c, M c j = (1 : Matrix n n A) c j) (r : n → A) : (M.updateRow j r).det = r j := by
  have h := congrFun (mulVec_cramer Mᵀ r) j
  rw [det_transpose, hM, one_smul] at h
  rw [← h, ← cramer_transpose_apply]
  simp [mulVec, dotProduct, hj, one_apply]

variable {ι κ : Type} (a : κ → ι) (l : κ → Fin (N + 1))

theorem det_lowMat_lead (τ : ι) (m : Fin (N + 1)) :
    ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).det = 1 := by
  have h {i j : Fin N} (hij : i ≤ j) : lowMat a l τ i j = (1 : Matrix _ _ _) i j :=
    dif_neg fun ⟨_, _, h₁, h₂⟩ => (h₁.trans_le h₂).not_ge hij
  have ht : ((lowMat a l τ).submatrix (Fin.castLE m.is_le) (Fin.castLE m.is_le)).BlockTriangular
      OrderDual.toDual := fun i j hij =>
    (h (le_of_lt (show i < j from hij))).trans
      (one_apply_ne ((Fin.castLE_injective _).ne (ne_of_lt (show i < j from hij))))
  rw [det_of_isLowerTriangular _ ht]
  simp [h le_rfl]

theorem exists_det_lowMat_eq (w : ι → Equiv.Perm (Fin N)) (τ : ι) (m : Fin (N + 1)) (e : Fin m → Fin N)
    (he : Function.Injective e) : ∃ (c : Fin (plDim N m + 1)) (ε : ℤˣ),
      ((lowMat a l τ).submatrix e (Fin.castLE m.is_le)).det =
        ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w τ).1 m c := by
  obtain ⟨I, ε, h⟩ := exists_det_eq_sign_mul_minor (cellGL a l w τ).1 m ((w τ).symm ∘ e)
    ((w τ).symm.injective.comp he)
  refine ⟨rowsEquiv N m I, ε, ?_⟩
  rw [plVec_rowsEquiv, ← h]
  congr 1
  refine Matrix.ext fun i j => ?_
  change _ = lowMat a l τ (w τ ((w τ).symm (e i))) _
  rw [Equiv.apply_symm_apply]
  rfl

theorem exists_X_eq_plVec [Finite κ] (w : ι → Equiv.Perm (Fin N)) (x : CellVar a l) :
    ∃ (k : κ) (c : Fin (plDim N (l k) + 1)) (ε : ℤˣ),
      MvPolynomial.X x = ((ε : ℤ) : CellRing a l) * plVec (cellGL a l w (a k)).1 (l k) c := by
  obtain ⟨⟨τ, i, j⟩, k₀, hk₀, h₁, h₂⟩ := x
  obtain ⟨k, ⟨rfl, hj⟩, hmin⟩ := Set.exists_min_image {k | a k = τ ∧ (j : ℕ) < l k} (fun k => (l k : ℕ))
    (Set.toFinite _) ⟨k₀, hk₀, h₁⟩
  have hi : (l k : ℕ) ≤ i := (hmin k₀ ⟨hk₀, h₁⟩).trans h₂
  have hinj : Function.Injective (Function.update (Fin.castLE (l k).is_le) ⟨j, hj⟩ i) := by
    intro s t hst
    by_cases hs : s = ⟨j, hj⟩ <;> by_cases ht : t = ⟨j, hj⟩
    · rw [hs, ht]
    · rw [hs, Function.update_self, Function.update_of_ne ht] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst)) t.2.not_ge
    · rw [ht, Function.update_self, Function.update_of_ne hs] at hst
      exact absurd (hi.trans_eq (congrArg Fin.val hst.symm)) s.2.not_ge
    · rw [Function.update_of_ne hs, Function.update_of_ne ht] at hst
      exact Fin.castLE_injective _ hst
  obtain ⟨c, ε, h⟩ := exists_det_lowMat_eq a l w (a k) (l k) _ hinj
  refine ⟨k, c, ε, Eq.trans ?_ h⟩
  have hd := det_updateRow_of_col_eq _ (det_lowMat_lead a l (a k) (l k)) ⟨j, hj⟩ (fun c => by
    refine (dif_neg fun ⟨k', hk', h₃, h₄⟩ => ((hmin k' ⟨hk', h₃⟩).trans h₄).not_gt c.2).trans ?_
    simp only [one_apply, (Fin.castLE_injective _).eq_iff]) fun c => lowMat a l (a k) i (Fin.castLE (l k).is_le c)
  refine Eq.trans (Eq.trans ?_ hd.symm) ?_
  · change _ = lowMat a l (a k) i j
    rw [lowMat, of_apply, dif_pos ⟨k₀, hk₀, h₁, h₂⟩]
  · congr 1
    refine Matrix.ext fun s t => ?_
    by_cases hs : s = ⟨j, hj⟩
    · simp [hs]
    · simp [updateRow_ne hs, Function.update_of_ne hs]

theorem isImmersion_plPt_cellGL : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1))
    (w : ι → Equiv.Perm (Fin N)), IsImmersion (plPt a l (cellGL a l w)) := by
  intro ι κ _ _ N a l w
  choose b η hb using fun k => exists_det_lowMat_eq a l w (a k) (l k) _ (Fin.castLE_injective (l k).is_le)
  simp only [det_lowMat_lead] at hb
  let U : (Amb l).Opens := ⟨⋂ k, (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).1,
    isOpen_iInter_of_finite fun k => (Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k)).2⟩
  have hU (k) : U ≤ Pi.π (fun k => PSpace ℤ (plDim N (l k))) k ⁻¹ᵁ chart ℤ _ (b k) :=
    fun y hy => Set.mem_iInter.1 hy k
  have hu (k) : IsUnit (plVec (cellGL a l w (a k)).1 (l k) (b k)) := IsUnit.of_mul_eq_one_right _ (hb k).symm
  have h₀ (k) : ⊤ ≤ (plPt a l (cellGL a l w) ≫ Pi.π _ k) ⁻¹ᵁ chart ℤ _ (b k) := by
    rw [plPt_π, pt_preimage_chart]
    exact fun y _ => mem_spOpen.2 fun hy => y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hy (hu k))
  have h : ⊤ ≤ plPt a l (cellGL a l w) ⁻¹ᵁ U := fun y hy => Set.mem_iInter.2 fun k => h₀ k hy
  refine isImmersion_of_X_mem_range _ U h fun x => ?_
  obtain ⟨k, c, ε, hx⟩ := exists_X_eq_plVec a l w x
  have e₁ := pullRatio_pt_top_mul (Int.castRingHom _) _ (span_plVec (cellGL a l w (a k)) (l k)) (b k) c (hu k)
    (plPt_π a l (cellGL a l w) k ▸ h₀ k)
  rw [← pullRatio_of_eq (plPt_π a l (cellGL a l w) k) (h₀ k), ← appLE_pullRatio (hi := hU k) _ h] at e₁
  have e₂ : plVec (cellGL a l w (a k)).1 (l k) (b k) = ((η k : ℤ) : CellRing a l) := by
    have := congrArg (((η k : ℤ) : CellRing a l) * ·) (hb k)
    simp only [mul_one, ← mul_assoc, ← Int.cast_mul, Int.units_coe_mul_self, Int.cast_one, one_mul] at this
    exact this.symm
  rw [hx, map_mul, ← e₁, e₂, map_intCast, map_intCast]
  exact mul_mem (intCast_mem _ _) (mul_mem ⟨_, rfl⟩ (intCast_mem _ _))

end GlobalTheory.FlagZ
