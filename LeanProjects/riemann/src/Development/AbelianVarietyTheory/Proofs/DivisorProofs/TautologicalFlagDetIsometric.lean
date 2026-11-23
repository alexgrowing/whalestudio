import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetMetricShortExactIsometric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenImmersionCellFlAlt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMinorCellMatRowsW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClsDivPullEqVPull
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace GlobalTheory.FlagZ.StepDet

open GlobalTheory.FlagZ.TautCell
open GlobalTheory.QCoh (pullbackSections res_pullbackSections pullbackSections_res pullback_map_app_pullbackSections
  pullbackSections_smul)
open GlobalTheory.Twist (resM resM_resM app_resM resM_self resM_smul)

theorem pullbackSections_image_top {X Y : Scheme.{0}} (j : Y ⟶ X) [IsOpenImmersion j] (G : X.Modules)
    (h : ⊤ ≤ j ⁻¹ᵁ j ''ᵁ ⊤) (t : Γ(G, j ''ᵁ ⊤)) :
    pullbackSections j G h t = ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app G).app ⊤ t := by
  have e := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction j)
    (Scheme.Modules.pullbackPushforwardAdjunction j) G
  have H := congr(($e).app (j ''ᵁ ⊤) t)
  rw [QCoh.pullbackSections_apply]
  refine (congrArg _ H.symm).trans ?_
  refine (app_resM ((Scheme.Modules.restrictFunctorIsoPullback j).hom.app G) h _).symm.trans (congrArg _ ?_)
  exact (resM_resM (F := G) _ _ t).trans (resM_self _ _)

variable {ι : Type} [Fintype ι] {N : ℕ}

theorem exists_frame_step
    (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N) (hfl : Taut.IsTaut ι N fl)
    (a : ι) (l : Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) :
    ∃ e : Fin l → Γ((fl a).F l, cellU w), VB.IsFrame e ∧
      ∀ j, ((fl a).ι l).app (cellU w) (e j) = colP w a (Fin.castLE l.is_le j) := by
  obtain ⟨s, hs, h⟩ := hfl (R ι N) (cellGL Prod.fst Prod.snd w) a l
  let c : Sp (R ι N) ⟶ Fl ι N := cell Prod.fst Prod.snd w
  have hc : ⊤ ≤ c ⁻¹ᵁ c ''ᵁ ⊤ := (c.preimage_image_eq ⊤).ge
  let ρ := Scheme.Modules.restrictFunctorIsoPullback c
  refine ⟨fun k => (ρ.inv.app ((fl a).F l)).app ⊤ (s k),
    (VB.isFrame_restrict_iff c _).1 (hs.map_iso (ρ.inv.app ((fl a).F l))), fun k => ?_⟩
  have inj : Function.Injective (pullbackSections c ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) hc) := by
    rw [funext (pullbackSections_image_top c _ hc)]
    exact (ConcreteCategory.bijective_of_isIso ((ρ.hom.app _).app ⊤)).1
  refine inj ((ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.pullbackComp c (flStr ι N)).hom.app (Taut.stdE N)).app ⊤)).1 ?_)
  have e₁ : pullbackSections c _ hc ((ρ.inv.app ((fl a).F l)).app ⊤ (s k)) = s k :=
    (pullbackSections_image_top c _ hc _).trans congr(($(ρ.inv_hom_id_app ((fl a).F l))).app ⊤ (s k))
  refine ((congrArg _ ((pullback_map_app_pullbackSections c ((fl a).ι l) hc _).symm.trans (congrArg _ e₁))).trans
    (h k)).trans ?_
  rw [Taut.colSec, colP, map_sum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  erw [pullbackSections_smul]
  rw [Scheme.Modules.Hom.app_smul]
  refine congrArg₂ (· • ·) ?_ ?_
  · have e₂ := congr($(c.appIso_inv_appLE hc) ((Scheme.ΓSpecIso (CommRingCat.of (R ι N))).inv
      ((cellGL (Prod.fst : ι × Fin (N + 1) → ι) Prod.snd w a).1 i (Fin.castLE l.is_le k))))
    exact (e₂.trans (GlobalTheory.Cartier.resG_self (X := Sp (R ι N)) le_top _)).symm
  · refine Eq.trans ?_ (congrArg _ (Vert.DivPull.pullbackComp_inv_app c (flStr ι N) (Taut.stdE N) (U := ⊤) _ hc le_top _))
    exact congr(($((Scheme.Modules.pullbackComp c (flStr ι N)).inv_hom_id_app (Taut.stdE N))).app ⊤ _).symm

open scoped ComplexOrder in

theorem form_colP (a : ι) (w : ι → Equiv.Perm (Fin N)) (σ : ℤ →+* ℂ) (y : CxPts (flStr ι N) σ)
    (hy : y ∈ CxPts.ptsIn (flStr ι N) σ (cellU w)) (j k : Fin N) :
    (((HermVB.std (𝟙 (Sp ℤ)) N).h.pull (flStr ι N) (Category.comp_id _)).met σ).form (colP w a j) (colP w a k) y =
      ∑ i, matAt w a y i j * star (matAt w a y i k) := by
  set h := (((HermVB.std (𝟙 (Sp ℤ)) N).h.pull (flStr ι N) (Category.comp_id _)).met σ)
  let b : Fin N → Γ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N), cellU w) := fun i =>
    pullbackSections (flStr ι N) (Taut.stdE N) (by simp) (VB.freeFrame (Sp ℤ) (Fin N) i)
  have hb (i i' : Fin N) : h.form (b i) (b i') y = (1 : Matrix (Fin N) (Fin N) ℂ) i i' := by
    refine (Met.form_pull _ (flStr ι N) (Category.comp_id _) _ _ _ hy).trans ?_
    refine (Met.form_frame _ ⟨⊤, _, VB.isFrame_freeFrame (Sp ℤ) (Fin N)⟩ CxPts.mem_ptsIn_top i i').trans ?_
    exact congrFun₂ (Met.ofFrame_G (VB.isFrame_freeFrame (Sp ℤ) (Fin N)) (fun _ => 1)
      (fun _ => Matrix.PosDef.one) _) i i'
  have hsum (t : Γ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N), cellU w)) (j : Fin N) :
      h.form (colP w a j) t y = ∑ i, matAt w a y i j * h.form (b i) t y := by
    have h0 : h.form 0 t y = 0 := by simpa using h.form_add_left 0 0 t y
    let φ : Γ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N), cellU w) →+ ℂ :=
      ⟨⟨fun s => h.form s t y, h0⟩, fun s s' => h.form_add_left s s' t y⟩
    refine (map_sum φ _ _).trans (Finset.sum_congr rfl fun i _ => h.form_smul_left _ _ _ _)
  rw [hsum]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  rw [← h.conj_form, hsum]
  simp [hb, Matrix.one_apply]

theorem det_step_φ (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N)
    (a : ι) (l : Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) (e : Fin l → Γ((fl a).F l, cellU w)) (he : VB.IsFrame e)
    (hP : ∀ j, ((fl a).ι l).app (cellU w) (e j) = colP w a (Fin.castLE l.is_le j))
    (σ : ℤ →+* ℂ) (y : CxPts (flStr ι N) σ) (hy : y ∈ CxPts.ptsIn (flStr ι N) σ (cellU w)) :
    ((VMetric.det (((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (flStr ι N) (Category.comp_id _)).restrict
      ((fl a).isSubbundle l) ((fl a).isVB l))).φ σ).φ ⟨_, e, he⟩ y = -Real.log (volSq (matAt w a y) l) := by
  have hG : (((HermVB.std (𝟙 (Sp ℤ)) N).h.pull (flStr ι N) (Category.comp_id _)).met σ).gram
      (fun j => ((fl a).ι l).app (cellU w) (e j)) y =
      ((cols (matAt w a y) l).conjTranspose * cols (matAt w a y) l).transpose := by
    ext j k
    simp only [hP]
    refine (form_colP a w σ y hy _ _).trans ?_
    simp [Matrix.mul_apply, cols, mul_comm]
  refine (congrArg (fun M : Matrix (Fin l) (Fin l) ℂ => -Real.log M.det.re) hG).trans ?_
  simp only [Matrix.det_transpose, ← volSq_eq_det, Complex.ofReal_re]

theorem minor_eq_mul_detUnit (fl : ∀ _ : ι, Vert.Flag ((Scheme.Modules.pullback (flStr ι N)).obj (Taut.stdE N)) N)
    (a : ι) (l : Fin (N + 1)) (w w' : ι → Equiv.Perm (Fin N))
    (e : Fin l → Γ((fl a).F l, cellU w)) (e' : Fin l → Γ((fl a).F l, cellU w')) (he : VB.IsFrame e) (he' : VB.IsFrame e')
    (hP : ∀ j, ((fl a).ι l).app (cellU w) (e j) = colP w a (Fin.castLE l.is_le j))
    (hP' : ∀ j, ((fl a).ι l).app (cellU w') (e' j) = colP w' a (Fin.castLE l.is_le j)) (I : Rows N l) :
    resG (Fl ι N) (inf_le_right : cellU w ⊓ cellU w' ≤ _) (minor (cellMat w' a).1 l I) =
      resG (Fl ι N) (inf_le_left : cellU w ⊓ cellU w' ≤ _) (minor (cellMat w a).1 l I) *
      (he.detUnit he' (inf_le_left : cellU w ⊓ cellU w' ≤ _) inf_le_right).val := by
  have hE : (Taut.stdE N).IsQuasicoherent := (HermVB.std (𝟙 (Sp ℤ)) N).h.isVB.isQuasicoherent
  have hb := (VB.isFrame_freeFrame (Sp ℤ) (Fin N)).pullback (F := Taut.stdE N) (flStr ι N)
  let B := hb.basis (V := cellU w ⊓ cellU w') le_top
  have hcol (v : ι → Equiv.Perm (Fin N)) (hv : cellU w ⊓ cellU w' ≤ cellU v) (i j : Fin N) :
      B.repr (resM _ hv (colP v a j)) i = resG (Fl ι N) hv ((cellMat v a).1 i j) := by
    have : resM _ hv (colP v a j) = ∑ i, resG (Fl ι N) hv ((cellMat v a).1 i j) • B i := by
      rw [colP, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [resM_smul, VB.IsFrame.basis_apply]
      exact congrArg _ ((res_pullbackSections _ _ _ _ _).trans (res_pullbackSections _ _ _ _ _).symm)
    rw [this, Module.Basis.repr_sum_self]
  rw [VB.IsFrame.val_detUnit, Module.Basis.det_apply, minor, minor, RingHom.map_det, RingHom.map_det, ← Matrix.det_mul]
  congr 1
  ext i j
  have h₁ := congrArg (((fl a).ι l).app _)
    ((he.basis (inf_le_left : cellU w ⊓ cellU w' ≤ _)).sum_repr (resM _ inf_le_right (e' j)))
  simp only [map_sum, Scheme.Modules.Hom.app_smul, VB.IsFrame.basis_apply, app_resM, hP, hP'] at h₁
  have h₂ := congrArg (fun s => B.repr s (subsetEnum I i)) h₁
  simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, hcol, smul_eq_mul] at h₂
  refine h₂.symm.trans ?_
  rw [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun k _ => mul_comm _ _

theorem dual_flDet_φ (a : ι) (l : Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) (σ : ℤ →+* ℂ) (y : CxPts (flStr ι N) σ)
    (hy : y ∈ CxPts.ptsIn (flStr ι N) σ (cellU w)) :
    ((flDet a l).dual.φ σ).φ (frameIdx Prod.fst Prod.snd (a, l) (rowsW w a l)) y =
      -Real.log (volSq (matAt w a y) l) := by
  let g : ι → GL (Fin N) ℂ := fun τ =>
    Matrix.GeneralLinearGroup.map (Points.valMap y.1 (cellU w) hy).hom (cellMat w τ)
  have e : y = cxPt Prod.fst Prod.snd σ g := Subtype.ext (eq_flagPt_of_le w y.1 hy)
  have hm : matAt w a y = (g a).1 := by
    ext i j
    exact Points.valR_eq _ _ hy _
  obtain ⟨ε, hε⟩ := exists_minor_cellMat_rowsW w a l
  have h1 : ‖minor (g a).1 l (rowsW w a l)‖ = 1 := by
    rw [show minor (g a).1 l (rowsW w a l) = _ from minor_map (Points.valMap y.1 (cellU w) hy).hom _ l _, hε,
      map_intCast]
    rcases Int.units_eq_one_or ε with h | h <;> simp [h]
  have h2 := detDual_φ Prod.fst Prod.snd σ g (a, l) (rowsW w a l) (by
    intro h
    rw [show minor (g a).1 l (rowsW w a l) = 0 from h] at h1
    simp at h1)
  rw [← e] at h2
  refine (congrArg (- ·) h2).trans ?_
  rw [hm, show ‖minor (g a).1 l (rowsW w a l)‖ = 1 from h1, one_pow, div_one]

theorem top_le_fromSpecStalk {X : Scheme.{0}} (x : X) {U : X.Opens} (hx : x ∈ U) : ⊤ ≤ X.fromSpecStalk x ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem _ (by simpa using hx)).ge

theorem valR_fromSpecStalk {X : Scheme.{0}} (x : X) {U : X.Opens} (hx : x ∈ U) (f : Γ(X, U)) :
    valR (A := X.presheaf.stalk x) (X.fromSpecStalk x) U f = (X.presheaf.germ U x hx).hom f := by
  rw [Points.valR_eq _ _ (top_le_fromSpecStalk x hx)]
  have : Points.valMap (C := X.presheaf.stalk x) (X.fromSpecStalk x) U (top_le_fromSpecStalk x hx) =
      X.presheaf.germ U x hx := by
    rw [Points.valMap, Scheme.Hom.appLE, Scheme.fromSpecStalk_app hx]
    simp only [Category.assoc]
    erw [← (Spec (X.presheaf.stalk x)).presheaf.map_comp_assoc]
    rw [← op_comp, Subsingleton.elim (_ ≫ _ : (⊤ : (Spec (X.presheaf.stalk x)).Opens) ⟶ ⊤) (𝟙 _), op_id,
      CategoryTheory.Functor.map_id, Category.id_comp]
    exact (congrArg _ (Iso.inv_hom_id _)).trans (Category.comp_id _)
  exact congr($(this).hom f)

theorem gm_dual_flDet_g (a : ι) (l : Fin (N + 1)) (w : ι → Equiv.Perm (Fin N)) (I J : Rows N l) (x : Fl ι N)
    (hx : x ∈ cellU w) (hI : x ∈ (flDet a l).dual.B.U (frameIdx Prod.fst Prod.snd (a, l) I))
    (hJ : x ∈ (flDet a l).dual.B.U (frameIdx Prod.fst Prod.snd (a, l) J)) :
    ((Fl ι N).presheaf.germ _ x hx).hom (minor (cellMat w a).1 l I) =
      (gm (𝟙 _) x _ ((flDet a l).dual.B.g (frameIdx Prod.fst Prod.snd (a, l) I)
        (frameIdx Prod.fst Prod.snd (a, l) J))).val * ((Fl ι N).presheaf.germ _ x hx).hom (minor (cellMat w a).1 l J) := by
  let π : Fl ι N ⟶ PSpace ℤ (plDim N l) := plEmb Prod.fst Prod.snd ≫ Limits.Pi.π _ (a, l)
  let p : Sp ((Fl ι N).presheaf.stalk x) ⟶ Fl ι N := (Fl ι N).fromSpecStalk x
  have hp : ⊤ ≤ p ⁻¹ᵁ cellU w := top_le_fromSpecStalk x hx
  let g : ι → GL (Fin N) ((Fl ι N).presheaf.stalk x) := fun τ =>
    Matrix.GeneralLinearGroup.map (Points.valMap p (cellU w) hp).hom (cellMat w τ)
  have e₀ : p ≫ π = ProjSpace.pt (Int.castRingHom _) (plVec (g a).1 l) (span_plVec _ _) :=
    (congrArg (· ≫ π) (eq_flagPt_of_le w p hp)).trans
      ((flagPt_plEmb_assoc _ _ g _).trans (plPt_π Prod.fst Prod.snd g (a, l)))
  have hm (K : Rows N l) : plVec (g a).1 l (rowsEquiv N l K) =
      ((Fl ι N).presheaf.germ _ x hx).hom (minor (cellMat w a).1 l K) := by
    rw [plVec_rowsEquiv, ← valR_fromSpecStalk, Points.valR_eq _ _ hp]
    exact minor_map _ _ l K
  have hI' : π x ∈ ProjSpace.chart ℤ _ (rowsEquiv N l I) := mem_pull.1 hI
  have hJ' : π x ∈ ProjSpace.chart ℤ _ (rowsEquiv N l J) := mem_pull.1 hJ
  have hIJ : x ∈ π ⁻¹ᵁ (ProjSpace.chart ℤ _ (rowsEquiv N l I) ⊓ ProjSpace.chart ℤ _ (rowsEquiv N l J)) := ⟨hI', hJ'⟩
  have hu : IsUnit (plVec (g a).1 l (rowsEquiv N l I)) :=
    (Points.le_pt_preimage_chart_iff (Int.castRingHom _) _ (span_plVec _ _) _).1
      (by rw [← e₀]; exact top_le_fromSpecStalk (U := π ⁻¹ᵁ ProjSpace.chart ℤ _ (rowsEquiv N l I)) x hI')
  have e₁ : (gm (𝟙 _ ≫ π) x _ ((ProjSpace.O1 ℤ _).g (rowsEquiv N l I) (rowsEquiv N l J))).val =
      plVec (g a).1 l (rowsEquiv N l J) * Ring.inverse (plVec (g a).1 l (rowsEquiv N l I)) := by
    rw [← Points.valR_pt_ratio (Int.castRingHom _) _ (span_plVec _ _) hu, ← e₀]
    refine (gm_val _ x _ hIJ _).trans ((valR_fromSpecStalk x hIJ _).symm.trans ?_)
    refine Eq.trans ?_ ((Points.valR_appLE p π le_rfl (top_le_fromSpecStalk x hIJ) _).trans
      (Points.valR_res (p ≫ π) inf_le_left (top_le_fromSpecStalk x hIJ) _))
    rw [← Scheme.Hom.app_eq_appLE]
    rfl
  have e₂ : gm (𝟙 _) x _ ((flDet a l).dual.B.g (frameIdx Prod.fst Prod.snd (a, l) I)
      (frameIdx Prod.fst Prod.snd (a, l) J)) =
      (gm (𝟙 _ ≫ π) x _ ((ProjSpace.O1 ℤ _).g (rowsEquiv N l I) (rowsEquiv N l J)))⁻¹ :=
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_pull_g (ProjSpace.O1 ℤ _) π (𝟙 _) x _ _ hI hJ))
  rw [e₂, Units.eq_inv_mul_iff_mul_eq, e₁, ← hm, ← hm, mul_assoc, Ring.inverse_mul_cancel _ hu, mul_one]

theorem isometric_det_step : ∀ (ι : Type) [Fintype ι] (N : ℕ)
    (fl : ∀ _ : ι, GlobalTheory.Vert.Flag ((Scheme.Modules.pullback (GlobalTheory.FlagZ.flStr ι N)).obj (GlobalTheory.FlagZ.Taut.stdE N)) N),
    GlobalTheory.FlagZ.Taut.IsTaut ι N fl → ∀ (a : ι) (l : Fin (N + 1)),
    (VMetric.det (((HermVB.std (𝟙 (Sp ℤ)) N).cInf.pull (GlobalTheory.FlagZ.flStr ι N) (Category.comp_id _)).restrict
      ((fl a).isSubbundle l) ((fl a).isVB l))).Isometric (GlobalTheory.FlagZ.flDet a l).dual := by
  intro ι _ N fl hfl a l
  choose e he hP using fun w => exists_frame_step fl hfl a l w
  choose ε hε using fun w : ι → Equiv.Perm (Fin N) => exists_minor_cellMat_rowsW w a l
  let u (w : ι → Equiv.Perm (Fin N)) : Γ(Fl ι N, cellU w)ˣ := Units.map (Int.castRingHom _).toMonoidHom (ε w)
  have hu (w : ι → Equiv.Perm (Fin N)) : (u w).val = minor (cellMat w a).1 l (rowsW w a l) := (hε w).symm
  refine HermLB.isometric_of_local (J := ι → Equiv.Perm (Fin N)) cellU ?_
    (fun w => frameIdx Prod.fst Prod.snd (a, l) (rowsW w a l))
    (fun w => (⟨_, e w, he w⟩ : GlobalTheory.VB.Chart ((fl a).F l) l))
    (fun w => cellU_le_chart a l w) (fun w => le_rfl) u (fun x w w' hw hw' => ?_) ?_
  · intro x
    obtain ⟨w, hw⟩ := exists_mem_range_cell ι (ι × Fin (N + 1)) N Prod.fst Prod.snd x
    exact ⟨w, by simpa [cellU] using hw⟩
  · have hx : x ∈ cellU w ⊓ cellU w' := ⟨hw, hw'⟩
    have e₁ := gm_dual_flDet_g a l w _ _ x hw (cellU_le_chart a l w hw) (cellU_le_chart a l w' hw')
    have e₂ := congrArg ((Fl ι N).presheaf.germ _ x hx).hom
      (minor_eq_mul_detUnit fl a l w w' (e w) (e w') (he w) (he w') (hP w) (hP w') (rowsW w' a l))
    rw [map_mul] at e₂
    erw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at e₂
    have e₃ : (gm (𝟙 _) x _ ((he w).detUnit (he w') (inf_le_left : cellU w ⊓ cellU w' ≤ _) inf_le_right)).val =
      ((Fl ι N).presheaf.germ _ x hx).hom ((he w).detUnit (he w') inf_le_left inf_le_right).val := gm_val _ _ _ hx _
    have e₄ (v : ι → Equiv.Perm (Fin N)) (hv : x ∈ cellU v) : (gm (𝟙 _) x _ (u v)).val =
      ((Fl ι N).presheaf.germ _ x hv).hom (minor (cellMat v a).1 l (rowsW v a l)) :=
      (gm_val _ _ _ hv _).trans (by rw [hu]; rfl)
    rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
    refine Units.ext ?_
    rw [Units.val_mul, Units.val_mul, e₄ w hw, e₄ w' hw', e₁, mul_assoc]
    exact congrArg (_ * ·) ((congrArg (_ * ·) e₃).trans e₂.symm)
  · intro σ w y hy
    have h0 : CxPts.logSq y (cellU w) (u w) = 0 := by
      rw [CxPts.logSq, hu, hε, CxPts.ev_eq hy, map_intCast]
      rcases Int.units_eq_one_or (ε w) with h | h <;> simp [h]
    rw [dual_flDet_φ a l w _ y hy, h0, add_zero]
    exact (det_step_φ fl a l w (e w) (he w) (hP w) _ y hy).symm

end GlobalTheory.FlagZ.StepDet
