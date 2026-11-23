import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameIn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsLowInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagToroidalEigenFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagBundlePointFramesTriangularComponent
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsAffineEigenframeFlag
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCellOfLeadingMinorsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagComponentEigenframeOnAffineOpenStatement

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ShFam
open scoped CategoryTheory.MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Cell

section MatCarry

variable {m : ℕ}

theorem inCell_of_mul_left {K : Type} [Field K] {T M : Matrix (Fin m) (Fin m) K} {w : Equiv.Perm (Fin m)}
    {a : Above m → K} (hT : ∀ i j, i < j → T i j = 0) (hTd : ∀ i, T i i ≠ 0) (h : InCell (T * M) w a) :
    InCell M w a := by
  obtain ⟨L, hL, e⟩ := h
  have hb : T.BlockTriangular OrderDual.toDual := fun i j hij => hT i j (OrderDual.toDual_lt_toDual.1 hij)
  have hd : T.det ≠ 0 := by
    rw [Matrix.det_of_lowerTriangular T hb]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hTd i
  letI := Matrix.invertibleOfIsUnitDet T (isUnit_iff_ne_zero.2 hd)
  have hbN : (T⁻¹ * L).BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular hb).mul hL.blockTriangular
  refine ⟨T⁻¹ * L, ⟨fun i j hij => hbN (OrderDual.toDual_lt_toDual.2 hij), fun i => ?_⟩, ?_⟩
  · have hdN : (T⁻¹ * L).det ≠ 0 := by
      rw [Matrix.det_mul, Matrix.det_nonsing_inv, Ring.inverse_eq_inv']
      exact mul_ne_zero (inv_ne_zero hd) (isUnit_det_of_isLowInv hL).ne_zero
    rw [Matrix.det_of_lowerTriangular _ hbN] at hdN
    exact isUnit_iff_ne_zero.2 (Finset.prod_ne_zero_iff.1 hdN i (Finset.mem_univ i))
  · have e1 : (T * M).submatrix id w = T * M.submatrix id w := rfl
    rw [Matrix.mul_assoc, ← e, e1, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hd),
      Matrix.one_mul]

theorem InCell.isUnit_minor {R : Type} [CommRing R] {M : Matrix (Fin m) (Fin m) R} {w : Equiv.Perm (Fin m)}
    {a : Above m → R} (h : InCell M w a) (k : ℕ) (hk : k ≤ m) :
    IsUnit ((M.submatrix id w).submatrix (Fin.castLE hk) (Fin.castLE hk)).det := by
  obtain ⟨L, hL, e⟩ := h
  rw [e]
  have hlt : ∀ i j : Fin k, i < j → Fin.castLE hk i < Fin.castLE hk j := fun i j hij => by
    rw [Fin.lt_def] at hij ⊢
    simpa using hij
  have hsub : (L * upMat a).submatrix (Fin.castLE hk) (Fin.castLE hk) =
      L.submatrix (Fin.castLE hk) (Fin.castLE hk) * (upMat a).submatrix (Fin.castLE hk) (Fin.castLE hk) := by
    ext i j
    simp only [Matrix.submatrix_apply, Matrix.mul_apply]
    symm
    refine ((Finset.sum_map Finset.univ (Fin.castLEEmb hk)
      (fun l => L (Fin.castLE hk i) l * upMat a l (Fin.castLE hk j))).symm).trans ?_
    refine Finset.sum_subset (Finset.subset_univ _) fun l _ hl => ?_
    have hkl : k ≤ (l : ℕ) := by
      by_contra hlk
      exact hl (Finset.mem_map.2 ⟨⟨l, by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
    have hil : Fin.castLE hk i < l := by
      rw [Fin.lt_def]
      simp only [Fin.val_castLE]
      omega
    rw [hL.1 _ _ hil, zero_mul]
  rw [hsub, Matrix.det_mul]
  refine IsUnit.mul (isUnit_det_of_isLowInv ⟨fun i j hij => hL.1 _ _ (hlt i j hij), fun i => hL.2 _⟩) ?_
  have hb : ((upMat a).submatrix (Fin.castLE hk) (Fin.castLE hk)).BlockTriangular id :=
    fun i j hij => upMat_blockTriangular a (show Fin.castLE hk j < Fin.castLE hk i from hlt j i hij)
  rw [Matrix.det_of_isUpperTriangular hb]
  simp

end MatCarry

section Carry

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {e : F ≃+* c.F}

theorem eq_mul_of_carries (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)}
    (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)) {Ω : Type} [Field Ω] (ψ : Γ(gen Z, V) →+* Ω) {x : Sp Ω ⟶ gen Z}
    (hx : spMap ψ ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z) (p : Sp Ω ⟶ C.Y.X)
    (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) {φ' : c.F →+* Ω} (h : EigFrame Z φ' (x ≫ genι Z))
    (hg : C.Carries p g) (hh : C.Carries p h) (A M : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω)
    (hA : ∀ τ i, g.vec τ i = ∑ k, A τ i k • res ψ hx (f₀.vec τ k))
    (hM : ∀ τ i, h.vec τ i = ∑ k, M τ i k • res ψ hx (f₀.vec τ k)) :
    ∃ T : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) Ω,
      (∀ τ i j, i < j → T τ i j = 0) ∧ (∀ τ i, T τ i i ≠ 0) ∧ ∀ τ, A τ = T τ * M τ := by
  obtain ⟨t, htri⟩ := GlobalTheory.VarFlag.tri_of_carries C hh hg
  obtain ⟨T, ⟨-, -, hT⟩, hTd, hTl⟩ := (h.tri_iff (RingHom.id Ω) g t).1 htri
  obtain ⟨f₁, hf₁⟩ := Spread.exists_bc f₀ ψ rfl hx
  have hid : spMap (dualMap (RingHom.id Ω)) = 𝟙 _ := by
    rw [← Spec.map_id]
    congr 1
    ext r <;> simp [dualMap]
  refine ⟨T, hTl, fun τ i => by rw [hTd]; exact Units.ne_zero _, fun τ => ?_⟩
  ext i k
  have e1 : g.vec τ i = ∑ j, T τ i j • h.vec τ j := by
    have := hT τ i
    simp only [hid, Category.id_comp] at this
    exact (GlobalTheory.LieMet.isComb_iff (h.vec τ) (T τ i) (g.vec τ i)).1 this
  have e2 : g.vec τ i = ∑ k, (T τ * M τ) i k • f₁.vec τ k := by
    rw [e1]
    simp only [hM, hf₁, Finset.smul_sum, smul_smul, Matrix.mul_apply, Finset.sum_smul]
    exact Finset.sum_comm
  have e3 : g.vec τ i = ∑ k, A τ i k • f₁.vec τ k := by
    rw [hA]
    simp only [hf₁]
  exact congrFun ((f₁.existsUnique_sum τ (g.vec τ i) (g.act_vec τ i)).unique e3 e2) k

end Carry

section Main

open GlobalTheory.LieLocFrame (res res_sum res_res)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (spMap_comp_spMap)

theorem mem_cellOpen_of_carries : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β} {F : Type} [Field F] {e : F ≃+* c.F}, ∀ (C : FlagCpt Z e) {V : (gen Z).Opens} (hV : IsAffineOpen V) {φV : c.F →+* Γ(gen Z, V)} (f₀ : EigFrame Z φV (hV.fromSpec ≫ genι Z)), hV.fromSpec ≫ genStr Z = spMap φV → ∀ (w : ∀ τ : E →+* ℂ, Equiv.Perm (Fin (Dw.mult τ))) (u : Cell.Coord Dw → Γ(C.Y.X, Cell.cellOpen C hV f₀ w)), Cell.IsCoord C hV f₀ w u → ∀ (Ω : Type) [Field Ω] (ψ : Γ(gen Z, V) →+* Ω) (x : Sp Ω ⟶ gen Z) (hx : spMap ψ ≫ hV.fromSpec = x) (g : EigFrame Z (ψ.comp φV) (x ≫ genι Z)) (a : Cell.Coord Dw → Ω), Cell.FrameIn hV f₀ w ψ hx g a → ∀ p : Sp Ω ⟶ C.Y.X, p ≫ C.π = x → C.Carries p g → ∃ q : Sp Ω ⟶ (Cell.cellOpen C hV f₀ w).toScheme, q ≫ (Cell.cellOpen C hV f₀ w).ι = p ∧ ∀ i, (Scheme.ΓSpecIso (.of Ω)).hom (q.appTop (Cell.coordTop C hV f₀ w u i)) = a i := by
  intro E _ _ _ H Dw l Xo c O _ β Z F _ e C V hV φV f₀ hs₀ w u hu Ω _ ψ x hx g a hFI p hpx hcar
  obtain ⟨Ag, hAg, hAgc⟩ := hFI
  have hxg : spMap ψ ≫ hV.fromSpec ≫ genι Z = x ≫ genι Z := by rw [← Category.assoc, hx]
  set z := p (IsLocalRing.closedPoint Ω) with hz_def
  have hzV : C.π z ∈ V := by
    have h1 : (p ≫ C.π) (IsLocalRing.closedPoint Ω) ∈ (V : Set (gen Z)) := by
      rw [hpx, ← hx, ← hV.range_fromSpec]
      exact ⟨spMap ψ (IsLocalRing.closedPoint Ω), rfl⟩
    exact h1

  obtain ⟨U, hU, hzU, φ, fr, t, hUV, hs, htri, -⟩ :=
    Spread.exists_frame_nhds E H Dw l Xo c O β Z F e C z (C.π ⁻¹ᵁ V) hzV
  have hsp : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec = hU.fromSpec ≫ C.π :=
    IsAffineOpen.SpecMap_appLE_fromSpec C.π hV hU hUV
  have hxU : spMap (C.π.appLE V U hUV).hom ≫ hV.fromSpec ≫ genι Z = (hU.fromSpec ≫ C.π) ≫ genι Z := by
    rw [← Category.assoc, hsp]
  have hφ : (C.π.appLE V U hUV).hom.comp φV = φ := by
    have h1 : spMap ((C.π.appLE V U hUV).hom.comp φV) = spMap φ := by
      rw [← spMap_comp_spMap, ← hs₀, ← hs, ← Category.assoc, hsp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  obtain ⟨g₀, hg₀⟩ := Spread.exists_bc f₀ (C.π.appLE V U hUV).hom hφ hxU
  choose A B hBA hA using Spread.exists_coord g₀ fr

  let ψz : C.Y.X.presheaf.stalk z →+* Ω := (Scheme.stalkClosedPointTo (R := .of Ω) p).hom
  let gm : Γ(C.Y.X, U) →+* C.Y.X.presheaf.stalk z := (C.Y.X.presheaf.germ U z hzU).hom
  let θ : Γ(C.Y.X, U) →+* Ω := ψz.comp gm
  let ρ : Γ(gen Z, V) →+* Γ(C.Y.X, U) := (C.π.appLE V U hUV).hom
  have hP' : spMap ψz ≫ C.Y.X.fromSpecStalk z = p := GlobalTheory.FlagBundle.spMap_stalkClosedPointTo p
  have hθ : spMap θ ≫ (show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) = p := by
    rw [← spMap_comp_spMap, Category.assoc, GlobalTheory.ShFam.Spread.spMap_germ hU hzU]
    exact hP'
  have hθρ : θ.comp ρ = ψ := by
    have h1 : spMap (θ.comp ρ) ≫ hV.fromSpec = spMap ψ ≫ hV.fromSpec := by
      rw [← spMap_comp_spMap, Category.assoc, hsp, ← Category.assoc, hθ, hpx, hx]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono hV.fromSpec).1 h1))
  have hxθ : spMap θ ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z = x ≫ genι Z := by
    rw [← hpx, ← hθ]
    simp only [Category.assoc]
  obtain ⟨frΩ, hfrΩ⟩ := Spread.exists_bc fr θ rfl hxθ
  have hfrv : ∀ τ i, frΩ.vec τ i = ∑ k, (A τ).map θ i k • res ψ hxg (f₀.vec τ k) := by
    intro τ i
    rw [hfrΩ, hA τ i, res_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hg₀, res_res ρ hxU θ hxθ hθρ hxg]
    rfl

  have hxS : spMap gm ≫ ((show Sp Γ(C.Y.X, U) ⟶ C.Y.X from hU.fromSpec) ≫ C.π) ≫ genι Z =
      stalkPt C.Y z ≫ C.π ≫ genι Z := by
    rw [Category.assoc, ← Category.assoc, GlobalTheory.ShFam.Spread.spMap_germ hU hzU]
    rfl
  have hxψ : spMap ψz ≫ stalkPt C.Y z ≫ C.π ≫ genι Z = x ≫ genι Z := by
    show spMap ψz ≫ C.Y.X.fromSpecStalk z ≫ C.π ≫ genι Z = _
    rw [← hpx, ← hP']
    simp only [Category.assoc]
  obtain ⟨fS, hfS⟩ := GlobalTheory.ShFam.Spread.exists_bc fr gm rfl hxS
  have hcarΩ : C.Carries p frΩ := by
    refine ⟨z, ψz, gm.comp φ, fS, t, 1, hP'.symm, ?_, ?_⟩
    · exact tri_bc fr gm rfl hxS fS hfS _ (RingHom.ext fun s => GlobalTheory.Cartier.algebraMap_germ hzU s) htri
    · refine tri_of_comb fS ψz rfl hxψ frΩ (fun _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne) 1
        (fun τ i => by simp) fun τ i => ?_
      simp only [Matrix.one_apply, ite_smul, one_smul, zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [hfrΩ, hfS, res_res gm hxS ψz hxψ rfl hxθ]

  obtain ⟨T, hT0, hTd, hTM⟩ := eq_mul_of_carries C hV f₀ ψ hxg p g frΩ hcar hcarΩ Ag (fun τ => (A τ).map θ) hAg hfrv
  have hcellθ : ∀ τ, InCell ((A τ).map θ) (w τ) (fun q => a ⟨τ, q⟩) := fun τ =>
    inCell_of_mul_left (hT0 τ) (hTd τ) (by rw [← hTM τ]; exact hAgc τ)

  let mn : (Σ τ : E →+* ℂ, Fin (Dw.mult τ + 1)) → Γ(C.Y.X, U) := fun q =>
    (((A q.1).submatrix id (w q.1)).submatrix (Fin.castLE (Nat.lt_succ_iff.mp q.2.is_lt))
      (Fin.castLE (Nat.lt_succ_iff.mp q.2.is_lt))).det
  have hmn : ∀ q, IsUnit (gm (mn q)) := fun q => by
    have h1 := (hcellθ q.1).isUnit_minor q.2 (Nat.lt_succ_iff.mp q.2.is_lt)
    have h2 : IsUnit (ψz (gm (mn q))) := by
      simpa [mn, θ, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using h1
    exact isUnit_of_map_unit ψz _ h2
  let f := ∏ q, mn q
  have hzf : z ∈ C.Y.X.basicOpen f := by
    rw [Scheme.mem_basicOpen _ _ _ hzU]
    show IsUnit (gm f)
    rw [map_prod]
    exact IsUnit.prod_univ_iff.mpr hmn
  have hle : C.Y.X.basicOpen f ≤ U := Scheme.basicOpen_le _ f
  let r := (C.Y.X.presheaf.map (homOfLE hle).op).hom
  have hfu : IsUnit (r f) := RingedSpace.isUnit_res_basicOpen C.Y.X.toRingedSpace f
  have hmu : ∀ q, IsUnit (r (mn q)) := fun q =>
    isUnit_of_dvd_unit (map_dvd r (Finset.dvd_prod_of_mem mn (Finset.mem_univ q))) hfu
  have hc : ∀ τ, ∃ a', InCell ((A τ).map r) (w τ) a' := fun τ => by
    refine GlobalTheory.T.exists_cell_of_leading_minors _ _ fun k hk => ?_
    have := hmu ⟨τ, ⟨k, Nat.lt_succ_of_le hk⟩⟩
    simpa [mn, RingHom.map_det, RingHom.mapMatrix_apply, Matrix.submatrix_map] using this
  choose a' ha' using hc
  have hcell := GlobalTheory.T.flag_component_eigenframe_on_affine_open C hV f₀ hU hUV (gen_mem hzU) fr t hxU A hs htri
    (fun τ i => by rw [hA τ i]; simp only [hg₀]) (hU.basicOpen f) hle (gen_mem hzf) w a' ha'
  have hzc : z ∈ cellOpen C hV f₀ w :=
    le_sSup (show C.Y.X.basicOpen f ∈ {U | ∃ a, CellAt C hV f₀ w U a} from ⟨a', hcell⟩) hzf

  have hrange : Set.range p ⊆ Set.range (cellOpen C hV f₀ w).ι := by
    rintro _ ⟨s, rfl⟩
    rw [Scheme.Opens.range_ι]
    have hs' : s = IsLocalRing.closedPoint Ω := Subsingleton.elim _ _
    rw [hs']
    exact hzc
  let q := IsOpenImmersion.lift (cellOpen C hV f₀ w).ι p hrange
  have hq : q ≫ (cellOpen C hV f₀ w).ι = p := IsOpenImmersion.lift_fac _ _ _
  refine ⟨q, hq, ?_⟩

  obtain ⟨ω, hω, φΩ, M, hωx, hφx, hM, ⟨g', hg'⟩, hcar'⟩ := point_data C hV f₀ w u hu Ω q x (by rw [hq, hpx])
  have hωψ : ω = ψ :=
    congrArg CommRingCat.Hom.hom (Spec.map_injective ((cancel_mono hV.fromSpec).1 (hωx.trans hx.symm)))
  have hφΩ : φΩ = ψ.comp φV := by
    have h1 : spMap φΩ = spMap (ψ.comp φV) := by
      rw [← hφx, ← hx, Category.assoc, hs₀, spMap_comp_spMap]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  subst hφΩ
  subst hωψ
  have hcarg' : C.Carries p g' := by
    have h1 := hcar' g' (fun τ => 1) (fun _ _ => 1) (fun τ i j hij => Matrix.one_apply_ne hij.ne)
      (fun τ i => by simp) fun τ i => by
        rw [hg']
        simp [Matrix.one_apply]
    rwa [hq] at h1
  obtain ⟨T', hT0', hTd', hTM'⟩ := eq_mul_of_carries C hV f₀ _ hxg p g g' hcar hcarg' Ag M hAg hg'
  intro i
  have hMa : InCell (M i.1) (w i.1) (fun q => a ⟨i.1, q⟩) :=
    inCell_of_mul_left (hT0' i.1) (hTd' i.1) (by rw [← hTM' i.1]; exact hAgc i.1)
  exact congrFun (InCell.unique (hM i.1) hMa) i.2

end Main

end GlobalTheory.ShFam.Cell
