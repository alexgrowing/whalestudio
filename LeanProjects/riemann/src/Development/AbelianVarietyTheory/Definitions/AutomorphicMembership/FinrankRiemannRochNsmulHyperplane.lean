import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemRiemannRochSpaceIffRegularAtEverywhere
import Development.AbelianVarietyTheory.Definitions.Divisors.NotHasNonzeroSecOfIsEmpty

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory.CechPic GlobalTheory.Adelic GlobalTheory.Cartier GlobalTheory.Cartier.CartierDiv GlobalTheory.QCoh

namespace GlobalTheory.ProjVar

namespace Var

variable {F : Type} [Field F] (Y : Var F)

instance isNoetherian_X : AlgebraicGeometry.IsNoetherian Y.X :=
  isNoetherian_of_isProjOver Y.isProjOver

def sheaf (Δ : Y.Dv) : Y.X.Modules := twist (structureModule Y.X) (Y.lb Δ)

instance isFiniteQC_sheaf (Δ : Y.Dv) : IsFiniteQC (Y.sheaf Δ) :=
  Twist.isFiniteQC_twist (isLB_toLB Δ)

abbrev H (i : ℕ) (Δ : Y.Dv) : Type := coh (Y.sheaf Δ) i

def hdim (i : ℕ) (Δ : Y.Dv) : ℕ := GlobalTheory.hdim F (Y.sheaf Δ) i

def chi (Δ : Y.Dv) : ℤ := GlobalTheory.chi F (Y.sheaf Δ)

instance finite_H (i : ℕ) (Δ : Y.Dv) : FiniteDimensional F (Y.H i Δ) :=
  finite_coh_of_isProjOver Y.algebraMap_Γ _ Y.isProjOver i

theorem hdim_def (i : ℕ) (Δ : Y.Dv) : Y.hdim i Δ = Module.finrank F (Y.H i Δ) := rfl

theorem hdim_eq_zero_iff (i : ℕ) (Δ : Y.Dv) : Y.hdim i Δ = 0 ↔ Subsingleton (Y.H i Δ) :=
  Module.finrank_zero_iff

def hZeroEquiv (Δ : Y.Dv) : Y.H 0 Δ ≃ₗ[F] Y.H0 Δ := cohEquiv (presents_toLB Δ)

theorem hdim_zero (Δ : Y.Dv) : Y.hdim 0 Δ = Module.finrank F (Y.H0 Δ) :=
  (Y.hZeroEquiv Δ).finrank_eq

theorem subsingleton_H {i : ℕ} (hi : Y.dim < i) (Δ : Y.Dv) : Subsingleton (Y.H i Δ) :=
  Y.isAmple_projective_O_one.subsingleton_coh_of_dim_lt _
    (by rw [Y.topologicalKrullDim_eq]; exact_mod_cast hi)

theorem hdim_eq_zero_of_lt {i : ℕ} (hi : Y.dim < i) (Δ : Y.Dv) : Y.hdim i Δ = 0 :=
  (Y.hdim_eq_zero_iff i Δ).2 (Y.subsingleton_H hi Δ)

theorem chi_eq_sum (Δ : Y.Dv) :
    Y.chi Δ = ∑ i ∈ Finset.range (Y.dim + 1), (-1 : ℤ) ^ i * Y.hdim i Δ :=
  chi_eq_sum_range F _ fun _ hi => Y.subsingleton_H hi Δ

theorem eulerChar_eq_finrank_riemannRoch {Δ : Y.Dv} (h : ∀ i, 0 < i → Y.hdim i Δ = 0) :
    Y.chi Δ = Module.finrank F (Y.H0 Δ) :=
  (chi_eq_hdim_zero F fun i hi => (Y.hdim_eq_zero_iff i Δ).1 (h i hi)).trans
    (congrArg _ (Y.hdim_zero Δ))

variable {Y} in

theorem hdim_eq_of_toPic_eq {Δ : Y.Dv} {L : LB Y.X} (hL : L.IsLB) (e : toPic Δ = cls L hL) (i : ℕ) :
    Y.hdim i Δ = GlobalTheory.hdim F (twist (structureModule Y.X) L) i :=
  (nonempty_twist_iso_of_cls_eq _ (isLB_toLB Δ) hL e).elim (hdim_congr F i)

variable {Y} in

theorem hdim_congr {Δ Δ' : Y.Dv} (e : toPic Δ = toPic Δ') (i : ℕ) : Y.hdim i Δ = Y.hdim i Δ' :=
  hdim_eq_of_toPic_eq (isLB_toLB Δ') e i

theorem hdim_add_principal (i : ℕ) (Δ : Y.Dv) (g : Y.Fnˣ) :
    Y.hdim i (Δ + principal g) = Y.hdim i Δ :=
  hdim_congr (by rw [map_add, toPic_principal, add_zero]) i

theorem chi_eq_chiPic (Δ : Y.Dv) : Y.chi Δ = chiPic F (structureModule Y.X) (toPic Δ) := rfl

theorem chi_zero : Y.chi 0 = GlobalTheory.chi F (structureModule Y.X) := by
  rw [chi_eq_chiPic, map_zero, chiPic_zero]

def stdOpen (j : Fin (Y.N + 1)) : Y.X.Opens := Y.ι ⁻¹ᵁ ProjSpace.chart F Y.N j

theorem isAffineOpen_stdOpen (j : Fin (Y.N + 1)) : IsAffineOpen (Y.stdOpen j) :=
  (ProjSpace.isAffineOpen_chart F Y.N j).preimage _

theorem iSup_stdOpen : ⨆ j, Y.stdOpen j = ⊤ := eq_top_iff.2 fun y _ =>
  have ⟨j, hj⟩ := ProjSpace.exists_mem_chart F Y.N (Y.ι y)
  Opens.mem_iSup.2 ⟨j, hj⟩

theorem isAffineOpen_biInf_stdOpen (s : Finset (Fin (Y.N + 1))) (hs : s.Nonempty) :
    IsAffineOpen (⨅ j ∈ s, Y.stdOpen j) :=
  have := isAffineHom_diagonal_of_isSeparated Y.str
  isAffineOpen_finset_biInf Y.isAffineOpen_stdOpen s hs

def cechCx (Δ : Y.Dv) : CochainComplex (ModuleCat.{0} F) ℕ := cech F (Y.sheaf Δ) ⊤ Y.stdOpen

def cechEquiv (i : ℕ) (Δ : Y.Dv) : (Y.cechCx Δ).homology i ≃ₗ[F] Y.H i Δ :=
  cechHEquivCoh F Y.iSup_stdOpen Y.isAffineOpen_biInf_stdOpen (Y.sheaf Δ) i

theorem hdim_eq_cech (i : ℕ) (Δ : Y.Dv) :
    Y.hdim i Δ = Module.finrank F ((Y.cechCx Δ).homology i) := (Y.cechEquiv i Δ).finrank_eq.symm

def inter (Δ : Fin Y.dim → Y.Dv) : ℤ := interNum F (structureModule Y.X) fun i => Y.lb (Δ i)

theorem inter_eq_multiDiff (Δ : Fin Y.dim → Y.Dv) : Y.inter Δ = multiDiff Δ Y.chi 0 := by
  have e := congrFun (multiDiff_comap toPic Δ (chiPic F (structureModule Y.X))) 0
  rw [Function.comp_apply, map_zero] at e
  exact (interNum_eq_multiDiff F _ fun i => isLB_toLB (Δ i)).trans e.symm

theorem inter_eq_sum (Δ : Fin Y.dim → Y.Dv) :
    Y.inter Δ = ∑ S : Finset (Fin Y.dim), (-1 : ℤ) ^ S.card * Y.chi (-∑ i ∈ S, Δ i) := by
  simp only [inter_eq_multiDiff, multiDiff_apply, zero_sub, smul_eq_mul]

variable {Y} in

theorem inter_eq_of_toPic_eq {Δ : Fin Y.dim → Y.Dv} {L : Fin Y.dim → LB Y.X}
    (hL : ∀ i, (L i).IsLB) (e : ∀ i, toPic (Δ i) = cls (L i) (hL i)) :
    Y.inter Δ = interNum F (structureModule Y.X) L :=
  interNum_congr_cls F _ (fun i => isLB_toLB (Δ i)) hL e

variable {Y} in

theorem inter_congr {Δ Δ' : Fin Y.dim → Y.Dv} (e : ∀ i, toPic (Δ i) = toPic (Δ' i)) :
    Y.inter Δ = Y.inter Δ' := inter_eq_of_toPic_eq (fun i => isLB_toLB (Δ' i)) e

theorem inter_eq_zero_of_principal (Δ : Fin Y.dim → Y.Dv) (i : Fin Y.dim) (g : Y.Fnˣ)
    (h : Δ i = principal g) : Y.inter Δ = 0 :=
  interNum_eq_zero_of_cls_eq_zero F _ (fun i => isLB_toLB (Δ i)) i
    ((toPic_apply _).symm.trans (h ▸ toPic_principal g))

theorem inter_comp_perm (Δ : Fin Y.dim → Y.Dv) (σ : Equiv.Perm (Fin Y.dim)) :
    Y.inter (Δ ∘ σ) = Y.inter Δ :=
  interNum_comp_perm F _ (L := fun i => Y.lb (Δ i)) (fun i => isLB_toLB (Δ i)) σ

theorem inter_const (Δ : Y.Dv) : Y.inter (fun _ => Δ) = topSelfIntersection F (Y.lb Δ) Y.dim := rfl

theorem del_linSys {Δ : Y.Dv} {n : ℕ} (b : Fin n → Y.H0 Δ) :
    (Y.linSys b).del = Y.inter fun _ => Δ := rfl

theorem diffVanish_chi : DiffVanish (Y.dim + 1) Y.chi :=
  (diffVanish_chiPic_of_isProjOver Y.algebraMap_Γ (structureModule Y.X) Y.isProjOver
    (by rw [suppDim_structureModule, Y.topologicalKrullDim_eq])).comap toPic

def interForm : MultilinearMap ℤ (fun _ : Fin Y.dim => Y.Dv) ℤ := Y.diffVanish_chi.form

@[simp] theorem interForm_apply (Δ : Fin Y.dim → Y.Dv) : Y.interForm Δ = Y.inter Δ :=
  (Y.diffVanish_chi.form_apply Δ 0).trans (Y.inter_eq_multiDiff Δ).symm

theorem inter_update_add (Δ : Fin Y.dim → Y.Dv) (i : Fin Y.dim) (A B : Y.Dv) :
    Y.inter (Function.update Δ i (A + B)) =
      Y.inter (Function.update Δ i A) + Y.inter (Function.update Δ i B) := by
  simp only [← interForm_apply, MultilinearMap.map_update_add]

theorem inter_update_zsmul (Δ : Fin Y.dim → Y.Dv) (i : Fin Y.dim) (n : ℤ) (A : Y.Dv) :
    Y.inter (Function.update Δ i (n • A)) = n * Y.inter (Function.update Δ i A) := by
  simp only [← interForm_apply, MultilinearMap.map_update_smul, smul_eq_mul]

theorem inter_zsmul (n : Fin Y.dim → ℤ) (Δ : Fin Y.dim → Y.Dv) :
    Y.inter (fun i => n i • Δ i) = (∏ i, n i) * Y.inter Δ := by
  simp only [← interForm_apply, MultilinearMap.map_smul_univ, smul_eq_mul]

theorem inter_const_nsmul (n : ℕ) (Δ : Y.Dv) :
    Y.inter (fun _ => n • Δ) = (n : ℤ) ^ Y.dim * Y.inter fun _ => Δ := by
  simpa using Y.inter_zsmul (fun _ => n) fun _ => Δ

theorem exists_polynomial_chi (A Δ : Y.Dv) : ∃ p : Polynomial ℚ, p.natDegree ≤ Y.dim ∧
    (∀ n : ℤ, p.eval (n : ℚ) = Y.chi (A + n • Δ)) ∧
      p.coeff Y.dim = (Y.dim.factorial : ℚ)⁻¹ * Y.inter fun _ => Δ := by
  obtain ⟨p, h₁, h₂, h₃⟩ := Y.diffVanish_chi.exists_polynomial_int ℚ Δ A
  exact ⟨p, h₁, h₂, by rw [h₃, inter_eq_multiDiff, Y.diffVanish_chi.multiDiff_eq _ A 0]⟩

def sheafOn (Z : Y.Cl) (Δ : Y.Dv) : Y.X.Modules :=
  twist ((Scheme.Modules.pushforward (redι Z)).obj (structureModule _)) (Y.lb Δ)

def chiOn (Z : Y.Cl) (Δ : Y.Dv) : ℤ := GlobalTheory.chi F (Y.sheafOn Z Δ)

def interOn (Z : Y.Cl) {d : ℕ} (Δ : Fin d → Y.Dv) : ℤ := interNumRed F Z fun i => Y.lb (Δ i)

def IsCurve (Z : Y.Cl) : Prop :=
  IsIrreducible (Z : Set Y.X) ∧ topologicalKrullDim (Z : Set Y.X) = 1

def deg (C : Y.Cl) (Δ : Y.Dv) : ℤ := interNumRed F C ![Y.lb Δ]

theorem finiteCoh_sheafOn (Z : Y.Cl) (Δ : Y.Dv) : FiniteCoh F (Y.sheafOn Z Δ) := by
  letI := algebraΓAlong F (redι Z)
  have hf := algebraMap_eq_strHom F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  have : IsProper (strHom F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along F (redι Z)), strHom_eq Y.algebraMap_Γ]
    infer_instance
  exact ((Y.isAmple_projective_O_one.pull_of_isClosedImmersion (redι Z)).finiteCohTwists hf
    (structureModule _)).pushforward_of_isClosedImmersion (appTop_algebraMap_along F (redι Z)) _
      (isLB_toLB Δ)

theorem chiOn_eq_chi_pull (Z : Y.Cl) (Δ : Y.Dv) :
    letI := algebraΓAlong F (redι Z)
    Y.chiOn Z Δ = GlobalTheory.chi F (twist (structureModule _) ((Y.lb Δ).pull (redι Z))) :=
  letI := algebraΓAlong F (redι Z)
  chi_twist_pushforward_of_isClosedImmersion (appTop_algebraMap_along F (redι Z)) _ _

theorem interOn_eq_multiDiff (Z : Y.Cl) {d : ℕ} (Δ : Fin d → Y.Dv) :
    Y.interOn Z Δ = multiDiff Δ (Y.chiOn Z) 0 := by
  have e := congrFun (multiDiff_comap toPic Δ
    (chiPic F ((Scheme.Modules.pushforward (redι Z)).obj (structureModule _)))) 0
  rw [Function.comp_apply, map_zero] at e
  exact (interNum_eq_multiDiff F _ fun i => isLB_toLB (Δ i)).trans e.symm

theorem interOn_eq_sum (Z : Y.Cl) {d : ℕ} (Δ : Fin d → Y.Dv) :
    Y.interOn Z Δ = ∑ S : Finset (Fin d), (-1 : ℤ) ^ S.card * Y.chiOn Z (-∑ i ∈ S, Δ i) := by
  simp only [interOn_eq_multiDiff, multiDiff_apply, zero_sub, smul_eq_mul]

variable {Y} in

theorem interOn_congr (Z : Y.Cl) {d : ℕ} {Δ Δ' : Fin d → Y.Dv}
    (e : ∀ i, toPic (Δ i) = toPic (Δ' i)) : Y.interOn Z Δ = Y.interOn Z Δ' :=
  interNum_congr_cls F _ (fun i => isLB_toLB (Δ i)) (fun i => isLB_toLB (Δ' i)) e

theorem interOn_comp_perm (Z : Y.Cl) {d : ℕ} (Δ : Fin d → Y.Dv) (σ : Equiv.Perm (Fin d)) :
    Y.interOn Z (Δ ∘ σ) = Y.interOn Z Δ :=
  interNum_comp_perm F _ (L := fun i => Y.lb (Δ i)) (fun i => isLB_toLB (Δ i)) σ

theorem chiOn_top (Δ : Y.Dv) : Y.chiOn ⊤ Δ = Y.chi Δ := by
  have h := InterModel.interNumRed_eq_interNumOn F (𝟙 Y.X) ⊤ (by simp) ![Y.lb (-Δ)]
  have h₀ := InterModel.interNumRed_eq_interNumOn F (𝟙 Y.X) ⊤ (by simp) (![] : Fin 0 → LB Y.X)
  rw [interNumOn_id] at h h₀
  have hL := isLB_toLB (-Δ)
  have e : cls _ (isLB_toLB Δ) = -cls _ hL := by rw [← toPic_apply, ← toPic_apply, map_neg, neg_neg]
  have h₁ := (interNum_cons_of_cls_eq_neg F _ (P := ![]) hL isEmptyElim _ e).symm.trans
    (h.trans (interNum_cons_of_cls_eq_neg F _ (P := ![]) hL isEmptyElim _ e))
  rw [← h₀, interNum_of_isEmpty F (twist _ _), interNum_of_isEmpty F (twist _ _)] at h₁
  exact sub_right_injective h₁

theorem interOn_top_eq_interNum {d : ℕ} (Δ : Fin d → Y.Dv) :
    Y.interOn ⊤ Δ = interNum F (structureModule Y.X) fun i => Y.lb (Δ i) := by
  rw [interOn, InterModel.interNumRed_eq_interNumOn F (𝟙 _) ⊤ (by simp), interNumOn_id]

theorem interOn_top (Δ : Fin Y.dim → Y.Dv) : Y.interOn ⊤ Δ = Y.inter Δ :=
  Y.interOn_top_eq_interNum Δ

variable {Y} in

theorem interOn_top_cons {A : Y.Dv} (f : Y.H0 A) (hf : (f : Y.Fn) ≠ 0) {d : ℕ} (Δ : Fin d → Y.Dv) :
    Y.interOn ⊤ (Fin.cons A Δ : Fin (d + 1) → Y.Dv) =
      interNumSub F (ThickeningDetermines.secIdeal (isLB_toLB A) (sec f)) fun i => Y.lb (Δ i) := by
  have := (mono_cutHom_structureModule_iff (isLB_toLB A) (sec f)).2
    (((presents_toLB A).generatesAt_rat_iff _).1 ((rat_sec f).symm ▸ generatesAt_genericPoint A hf))
  rw [interOn_top_eq_interNum, ← interNum_cons_eq_interNumSub (isLB_toLB A) (sec f)
    (fun i => isLB_toLB (Δ i)) (Y.isAmple_projective_O_one.finiteCohTwists Y.algebraMap_Γ _)]
  exact congrArg _ (funext (Fin.cases rfl fun _ => rfl))

variable {Y} in

theorem diffVanish_chiOn {Z : Y.Cl} {d : ℕ} (hd : topologicalKrullDim (Z : Set Y.X) ≤ d) :
    DiffVanish (d + 1) (Y.chiOn Z) := by
  letI := algebraΓAlong F (redι Z)
  have hf := algebraMap_eq_strHom F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme
  have : IsProper (strHom F (Scheme.IdealSheafData.vanishingIdeal Z).subscheme) := by
    rw [← comp_strHom (appTop_algebraMap_along F (redι Z)), strHom_eq Y.algebraMap_Γ]
    infer_instance
  exact (((Y.isAmple_projective_O_one.pull_of_isClosedImmersion (redι Z)).diffVanish_chiPic_of_isProper hf
    (structureModule _) (by rwa [suppDim_structureModule, topologicalKrullDim_red])
      ).chiPic_pushforward_of_isAffineHom (appTop_algebraMap_along F (redι Z))).comap toPic

variable {Y} in

theorem interOn_update_add {Z : Y.Cl} {d : ℕ} (hd : topologicalKrullDim (Z : Set Y.X) ≤ d)
    (Δ : Fin d → Y.Dv) (i : Fin d) (A B : Y.Dv) :
    Y.interOn Z (Function.update Δ i (A + B)) =
      Y.interOn Z (Function.update Δ i A) + Y.interOn Z (Function.update Δ i B) := by
  simp only [interOn_eq_multiDiff, (diffVanish_chiOn hd).multiDiff_update_add, Pi.add_apply]

variable {Y} in

theorem interOn_eq_zero {Z : Y.Cl} {d : ℕ} (hd : topologicalKrullDim (Z : Set Y.X) ≤ d)
    (Δ : Fin (d + 1) → Y.Dv) : Y.interOn Z Δ = 0 := by
  rw [interOn_eq_multiDiff, diffVanish_chiOn hd Δ, Pi.zero_apply]

theorem isCurve_iff (Z : Y.Cl) : Y.IsCurve Z ↔ IsCompleteCurve F Z := (Y.isCompleteCurve_iff Z).symm

theorem isCurve_top (h : Y.dim = 1) : Y.IsCurve ⊤ :=
  ⟨IrreducibleSpace.isIrreducible_univ _,
    (topologicalKrullDim_eq_of_isEmbedding Topology.IsEmbedding.id Set.range_id).trans
      (Y.topologicalKrullDim_eq.trans (by rw [h]; rfl))⟩

variable {Y} in

theorem IsCurve.eq_top (h : Y.dim = 1) {C : Y.Cl} (hC : Y.IsCurve C) : C = ⊤ :=
  not_not.1 fun hn => (Y.properCl_iff C).1 hn (PositivityModel.genericPoint_mem
    (Y.topologicalKrullDim_eq.trans (by rw [h]; rfl)) ((Y.isCurve_iff C).1 hC))

theorem deg_eq_interOn (C : Y.Cl) (Δ : Y.Dv) : Y.deg C Δ = Y.interOn C ![Δ] :=
  congrArg (interNumRed F C) (funext fun i => by fin_cases i; rfl)

theorem deg_eq (C : Y.Cl) (Δ : Y.Dv) : Y.deg C Δ = Y.chiOn C 0 - Y.chiOn C (-Δ) := by
  rw [deg_eq_interOn, interOn_eq_multiDiff]
  refine (congrFun (multiDiff_cons Δ ![] (Y.chiOn C)) 0).trans ?_
  rw [multiDiff_of_isEmpty, bwdDiff_apply, zero_sub]

theorem deg_top (h : Y.dim = 1) (Δ : Y.Dv) : Y.deg ⊤ Δ = Y.inter fun _ => Δ := by
  rw [deg_eq_interOn, interOn_top_eq_interNum, inter_const, h]
  exact congrArg _ (funext fun i => by fin_cases i; rfl)

variable {Y}

theorem deg_eq_of_toPic_eq (C : Y.Cl) {Δ : Y.Dv} {L : LB Y.X} (hL : L.IsLB)
    (e : toPic Δ = cls L hL) : Y.deg C Δ = interNumRed F C ![L] :=
  interNumRed_one_congr (isLB_toLB Δ) hL e C

theorem deg_congr (C : Y.Cl) {Δ Δ' : Y.Dv} (e : toPic Δ = toPic Δ') : Y.deg C Δ = Y.deg C Δ' :=
  deg_eq_of_toPic_eq C (isLB_toLB Δ') e

theorem deg_principal (C : Y.Cl) (g : Y.Fnˣ) : Y.deg C (principal g) = 0 :=
  interNumRed_one_eq_zero (isLB_toLB _) (toPic_principal g) C

@[simp] theorem deg_zero (C : Y.Cl) : Y.deg C 0 = 0 := deg_principal C 1

namespace IsCurve

variable {C : Y.Cl} (hC : Y.IsCurve C)

include hC

theorem deg_add (A B : Y.Dv) : Y.deg C (A + B) = Y.deg C A + Y.deg C B :=
  ((Y.isCurve_iff C).1 hC).interNumRed_of_cls_eq_add Y.isAmple_projective_O_one (isLB_toLB _) (isLB_toLB A)
    (isLB_toLB B) (map_add toPic A B)

def degHom : Y.Dv →+ ℤ := AddMonoidHom.mk' (Y.deg C) hC.deg_add

theorem deg_neg (Δ : Y.Dv) : Y.deg C (-Δ) = -Y.deg C Δ := map_neg hC.degHom Δ

theorem deg_sub (A B : Y.Dv) : Y.deg C (A - B) = Y.deg C A - Y.deg C B := map_sub hC.degHom A B

theorem deg_zsmul (n : ℤ) (Δ : Y.Dv) : Y.deg C (n • Δ) = n * Y.deg C Δ := map_zsmul hC.degHom n Δ

theorem deg_nsmul (n : ℕ) (Δ : Y.Dv) : Y.deg C (n • Δ) = n * Y.deg C Δ := by
  rw [← natCast_zsmul, hC.deg_zsmul]

theorem deg_eq (Δ : Y.Dv) : Y.deg C Δ = Y.chiOn C Δ - Y.chiOn C 0 := by
  have := Y.deg_eq C (-Δ)
  rw [hC.deg_neg, neg_neg] at this
  omega

theorem deg_nonneg_of_generatesAt {Δ : Y.Dv} {f : Y.Fn} (hf : f ∈ Y.H0 Δ) {x : Y.X} (hx : x ∈ C)
    (h : Δ.GeneratesAt x f) :
    0 ≤ Y.deg C Δ ∧ ((∃ y ∈ C, Δ.VanishesAt y f) → 0 < Y.deg C Δ) := by
  have e := rat_sec (⟨f, hf⟩ : Y.H0 Δ)
  have H := ((Y.isCurve_iff C).1 hC).interNumRed_nonneg_of_sec Y.isAmple_projective_O_one (isLB_toLB Δ)
    (sec ⟨f, hf⟩) hx (((presents_toLB Δ).generatesAt_rat_iff _).1 (e.symm ▸ h))
  exact ⟨H.1, fun ⟨y, hy, hy'⟩ =>
    H.2 ⟨y, hy, ((presents_toLB Δ).vanishesAt_rat_iff _).1 (e.symm ▸ hy')⟩⟩

theorem deg_nonneg_of_eff {Δ : Y.Dv} (h : Y.Eff Δ) (hs : ¬ Y.subCl C (Y.supp Δ)) :
    0 ≤ Y.deg C Δ ∧ ((∃ y ∈ C, y ∈ Y.supp Δ) → 0 < Y.deg C Δ) := by
  obtain ⟨x, hx, hx'⟩ := SetLike.not_le_iff_exists.1 hs
  have H := hC.deg_nonneg_of_generatesAt (eff_iff_one_mem.1 h) hx (notMem_supp_iff.1 hx')
  exact ⟨H.1, fun ⟨y, hy, hy'⟩ => H.2 ⟨y, hy, (CartierDiv.Eff.mem_supp_iff h).1 hy'⟩⟩

end IsCurve

variable (Y) in

def nef (Δ : Y.Dv) : Prop := IsNef F (Y.lb Δ)

variable (Y) in

def big (Δ : Y.Dv) : Prop := IsBig F (Y.lb Δ)

variable (Y) in

def ample (Δ : Y.Dv) : Prop := IsAmpleLB (Y.lb Δ)

variable {Δ A B : Y.Dv} {L : LB Y.X}

theorem nef_iff : Y.nef Δ ↔ ∀ C, Y.IsCurve C → 0 ≤ Y.deg C Δ :=
  ⟨fun h C hC => h.2 C ((Y.isCurve_iff C).1 hC),
    fun h => ⟨isLB_toLB Δ, fun C hC => h C ((Y.isCurve_iff C).2 hC)⟩⟩

theorem finrank_riemannRoch_nsmul (Δ : Y.Dv) (n : ℕ) :
    Module.finrank F (Y.H0 (n • Δ)) = lbH0 F (lbPow (Y.lb Δ) n) :=
  (Y.hdim_zero _).symm.trans (hdim_eq_of_toPic_eq (isLB_lbPow (isLB_toLB Δ) n)
    (by rw [cls_lbPow (isLB_toLB Δ), map_nsmul, toPic_apply]) 0)

theorem big_iff : Y.big Δ ↔ ∃ c : ℝ, 0 < c ∧
    ∃ᶠ n : ℕ in atTop, c * (n : ℝ) ^ Y.dim ≤ Module.finrank F (Y.H0 (n • Δ)) := by
  simp only [finrank_riemannRoch_nsmul]
  exact (isBig_iff Y.algebraMap_Γ Y.isProjOver Y.topologicalKrullDim_eq).trans
    (and_iff_right (isLB_toLB Δ))

theorem nef_iff_of_toPic_eq (hL : L.IsLB) (e : toPic Δ = cls L hL) : Y.nef Δ ↔ IsNef F L :=
  ⟨fun h => h.of_cls_eq hL e.symm, fun h => h.of_cls_eq (isLB_toLB Δ) e⟩

theorem big_iff_of_toPic_eq (hL : L.IsLB) (e : toPic Δ = cls L hL) : Y.big Δ ↔ IsBig F L :=
  ⟨fun h => h.of_cls_eq hL e.symm, fun h => h.of_cls_eq (isLB_toLB Δ) e⟩

theorem ample_iff_of_toPic_eq (hL : L.IsLB) (e : toPic Δ = cls L hL) : Y.ample Δ ↔ IsAmpleLB L :=
  ⟨fun h => h.of_lbIso hL ((cls_eq_iff _ _).1 e.symm),
    fun h => h.of_lbIso (isLB_toLB Δ) ((cls_eq_iff _ _).1 e)⟩

theorem nef_congr (e : toPic A = toPic B) : Y.nef A ↔ Y.nef B :=
  nef_iff_of_toPic_eq (isLB_toLB B) e

theorem big_congr (e : toPic A = toPic B) : Y.big A ↔ Y.big B :=
  big_iff_of_toPic_eq (isLB_toLB B) e

theorem ample_congr (e : toPic A = toPic B) : Y.ample A ↔ Y.ample B :=
  ample_iff_of_toPic_eq (isLB_toLB B) e

variable (Y) in

theorem nef_zero : Y.nef 0 := nef_iff.2 fun C _ => (deg_zero C).ge

theorem nef.add (hA : Y.nef A) (hB : Y.nef B) : Y.nef (A + B) := nef_iff.2 fun C hC =>
  (add_nonneg (nef_iff.1 hA C hC) (nef_iff.1 hB C hC)).trans_eq (hC.deg_add A B).symm

theorem nef.nsmul (h : Y.nef Δ) (n : ℕ) : Y.nef (n • Δ) := nef_iff.2 fun C hC =>
  (mul_nonneg (Nat.cast_nonneg n) (nef_iff.1 h C hC)).trans_eq (hC.deg_nsmul n Δ).symm

theorem nef_nsmul_iff {n : ℕ} (hn : 1 ≤ n) : Y.nef (n • Δ) ↔ Y.nef Δ :=
  ⟨fun h => nef_iff.2 fun C hC => nonneg_of_mul_nonneg_right
      ((nef_iff.1 h C hC).trans_eq (hC.deg_nsmul n Δ)) (Nat.cast_pos.2 hn), fun h => h.nsmul n⟩

theorem bpf.nef {V : Set Y.Fn} (h : Y.bpf Δ V) : Y.nef Δ := nef_iff.2 fun _ hC => by
  obtain ⟨x, hx⟩ := hC.1.nonempty
  obtain ⟨f, hf, hfx⟩ := h.2 x
  exact (hC.deg_nonneg_of_generatesAt (h.mem f hf) hx hfx).1

theorem nef_iff_of_dim_eq_one (h : Y.dim = 1) : Y.nef Δ ↔ 0 ≤ Y.inter fun _ => Δ := by
  rw [nef_iff, ← Y.deg_top h]
  exact ⟨fun H => H _ (Y.isCurve_top h), fun H C hC => hC.eq_top h ▸ H⟩

theorem ample.deg_pos (h : Y.ample A) {C : Y.Cl} (hC : Y.IsCurve C) : 0 < Y.deg C A :=
  IsAmpleLB.interNumRed_pos h ((Y.isCurve_iff C).1 hC)

theorem ample.nef (h : Y.ample A) : Y.nef A := IsAmpleLB.isNef h

theorem ample.eventually_hdim_eq_zero (h : Y.ample A) (Δ : Y.Dv) :
    ∀ᶠ n : ℕ in atTop, ∀ i, 0 < i → Y.hdim i (Δ + n • A) = 0 :=
  (IsAmpleLB.eventually_subsingleton_coh_twist Y.algebraMap_Γ (Y.sheaf Δ) h).mono fun n hn i hi => by
    obtain ⟨e⟩ := nonempty_twist_twist_iso_of_cls_eq (structureModule Y.X) (isLB_toLB Δ)
      (isLB_lbPow (isLB_toLB A) n) (isLB_toLB (Δ + n • A))
      (by rw [cls_lbPow (isLB_toLB A), ← toPic_apply, ← toPic_apply, ← toPic_apply, map_add,
        map_nsmul])
    exact (Y.hdim_eq_zero_iff i _).2 ((cohOn.mapIso F ⊤ i e).toEquiv.subsingleton_congr.1 (hn i hi))

variable (Y) in

theorem ample_hyp {i : Fin (Y.N + 1)} (hi : Y.ι (genericPoint Y.X) ∈ ProjSpace.chart F Y.N i) :
    Y.ample (Y.hyp hi) :=
  (ample_iff_of_toPic_eq Y.isLineBundle_twistingSheafOne (Y.presents_hyp hi).toPic_eq).2 Y.isAmple_projective_O_one

theorem hasNonzeroSec_iff : HasNonzeroSec (Y.lb Δ) ↔ Y.H0 Δ ≠ ⊥ :=
  hasNonzeroSec_iff_nontrivial.trans
    ((Y.hZeroEquiv Δ).toEquiv.nontrivial_congr.trans Submodule.nontrivial_iff_ne_bot)

theorem big.isBig_add_of_riemannRoch_ne_bot (hA : Y.big A) (hB : Y.H0 B ≠ ⊥) : Y.big (A + B) :=
  IsBig.of_cls_eq_add Y.algebraMap_Γ Y.isProjOver hA (isLB_toLB B) (hasNonzeroSec_iff.2 hB)
    (isLB_toLB _) (map_add toPic A B)

theorem big.add_eff (hA : Y.big A) (hB : Y.Eff B) : Y.big (A + B) :=
  hA.isBig_add_of_riemannRoch_ne_bot ((Submodule.ne_bot_iff _).2 ⟨1, eff_iff_one_mem.1 hB, one_ne_zero⟩)

theorem big_nsmul_iff {n : ℕ} (hn : 1 ≤ n) : Y.big (n • Δ) ↔ Y.big Δ :=
  (big_iff_of_toPic_eq (isLB_lbPow (isLB_toLB Δ) n)
    (by rw [cls_lbPow (isLB_toLB Δ), map_nsmul, toPic_apply])).trans
      (isBig_pow_iff Y.algebraMap_Γ Y.isProjOver (isLB_toLB Δ) hn)

theorem big.isBig_frequently_riemannRoch_ne_bot (h : Y.big Δ) : ∃ᶠ n : ℕ in atTop, Y.H0 (n • Δ) ≠ ⊥ :=
  (IsBig.frequently_hasNonzeroSec h).mono fun n hn => hasNonzeroSec_iff.1
    (hn.of_cls_eq (isLB_toLB _) (isLB_lbPow (isLB_toLB Δ) n)
      (by rw [cls_lbPow (isLB_toLB Δ), ← toPic_apply, ← toPic_apply, map_nsmul]))

theorem not_big_zero (h : 1 ≤ Y.dim) : ¬ Y.big 0 := fun hb => by
  obtain ⟨c, hc, hn⟩ := big_iff.1 hb
  have ht : Tendsto (fun n : ℕ => c * (n : ℝ) ^ Y.dim) atTop atTop :=
    ((tendsto_pow_atTop (by omega)).comp tendsto_natCast_atTop_atTop).const_mul_atTop hc
  obtain ⟨n, h₁, h₂⟩ :=
    (hn.and_eventually (ht.eventually_gt_atTop (Module.finrank F (Y.H0 0)))).exists
  rw [nsmul_zero] at h₁
  exact h₂.not_ge h₁

end Var

section Proj

open ProjSpace

variable (F : Type) [Field F] (n : ℕ)

theorem hdim_zsmul_projHyp (i : ℕ) (m : ℤ) :
    (proj F n).hdim i (m • projHyp F n) = GlobalTheory.hdim F (ProjCoh.sheafO F n m) i := by
  have := Geo.Tor.isProper_str F n
  have H : IsPullback (proj F n).ι (proj F n).str (PSpace.str F n)
      (Spec.map (CommRingCat.ofHom (algebraMap F F))) := by
    rw [show Spec.map (CommRingCat.ofHom (algebraMap F F)) = 𝟙 _ from Spec.map_id _]
    exact IsPullback.of_horiz_isIso ⟨(Category.comp_id _).symm⟩
  have hm := Twist.isLB_lbZPow (O1_isLB F n) m
  have h := FieldChangeInter.hdim_pull (f := PSpace.str F n) H hm i
  refine (Var.hdim_eq_of_toPic_eq (LB.isLB_pull hm _) ?_ i).trans (h.trans ?_)
  · refine Eq.trans ?_ (cls_pull hm _ _).symm
    rw [map_zsmul, cls_lbZPow (O1_isLB F n), map_zsmul]
    exact congrArg _ (((proj F n).presents_hyp _).toPic_eq.trans (cls_pull (O1_isLB F n) _ _))
  · rw [← projSys.algebraΓ_eq]

theorem chi_zsmul_projHyp (m : ℤ) : (proj F n).chi (m • projHyp F n) = Ring.choose (m + n) n :=
  (finsum_congr fun i => congrArg (fun a : ℕ => (-1 : ℤ) ^ i * a)
    (hdim_zsmul_projHyp F n i m)).trans (ProjCoh.chi_sheafO F n m)

theorem finrank_riemannRoch_nsmul_hyperplane (m : ℕ) :
    Module.finrank F ((proj F n).H0 (m • projHyp F n)) = (m + n).choose n := by
  rw [← Var.hdim_zero, ← natCast_zsmul, hdim_zsmul_projHyp]
  exact sectionDim_twistingSheaf_pow F n m

theorem hdim_top_zsmul_projHyp (hn : 1 ≤ n) (m : ℤ) :
    (proj F n).hdim n (m • projHyp F n) = (-m - 1).toNat.choose n :=
  (hdim_zsmul_projHyp F n n m).trans (ProjCoh.finrank_coh_top F hn m)

theorem inter_projHyp : (proj F n).inter (fun _ => projHyp F n) = 1 := by
  obtain ⟨p, -, h₂, h₃⟩ := (proj F n).exists_polynomial_chi 0 (projHyp F n)
  have e : p = Polynomial.preHilbertPoly ℚ n 0 :=
    Polynomial.eq_of_infinite_eval_eq _ _ (Set.infinite_of_injective_forall_mem
      (f := fun m : ℤ => (m : ℚ)) Int.cast_injective fun m => by
        rw [Set.mem_setOf_eq, h₂, zero_add, chi_zsmul_projHyp, ← ProjCoh.chi_sheafO F,
          ProjCoh.chi_sheafO_eq_eval])
  replace h₃ : p.coeff n = (n.factorial : ℚ)⁻¹ * (proj F n).inter fun _ => projHyp F n := h₃
  rw [e, Polynomial.coeff_preHilbertPoly_self, eq_comm,
    mul_eq_left₀ (inv_ne_zero (Nat.cast_ne_zero.2 n.factorial_ne_zero))] at h₃
  exact_mod_cast h₃

theorem inter_zsmul_projHyp (d : Fin n → ℤ) :
    (proj F n).inter (fun i => d i • projHyp F n) = ∏ i, d i :=
  ((proj F n).inter_zsmul d fun _ => projHyp F n).trans (by rw [inter_projHyp]; exact mul_one _)

theorem exists_inter_eq_one :
    ∃ (Y : Var F) (Δ : Y.Dv), Y.dim = n ∧ Y.inter (fun _ => Δ) = 1 :=
  ⟨proj F n, projHyp F n, rfl, inter_projHyp F n⟩

theorem ample_projHyp : (proj F n).ample (projHyp F n) := (proj F n).ample_hyp _

theorem nef_projHyp : (proj F n).nef (projHyp F n) := (ample_projHyp F n).nef

theorem big_projHyp : (proj F n).big (projHyp F n) := by
  refine Var.big_iff.2 ⟨(n.factorial : ℝ)⁻¹, by positivity, Frequently.of_forall fun m => ?_⟩
  rw [finrank_riemannRoch_nsmul_hyperplane, ← div_eq_inv_mul, proj_dim]
  refine le_trans ?_ (Nat.pow_le_choose n (m + n))
  gcongr
  omega

theorem deg_projHyp_line : (proj F 1).deg ⊤ (projHyp F 1) = 1 :=
  ((proj F 1).deg_top rfl _).trans (inter_projHyp F 1)

theorem deg_zsmul_projHyp_line (m : ℤ) : (proj F 1).deg ⊤ (m • projHyp F 1) = m := by
  rw [((proj F 1).isCurve_top rfl).deg_zsmul, deg_projHyp_line, mul_one]

theorem nef_zsmul_projHyp_line (m : ℤ) : (proj F 1).nef (m • projHyp F 1) ↔ 0 ≤ m := by
  rw [Var.nef_iff_of_dim_eq_one rfl, ← (proj F 1).deg_top rfl, deg_zsmul_projHyp_line]

theorem big_zsmul_projHyp (hn : 1 ≤ n) (m : ℤ) : (proj F n).big (m • projHyp F n) ↔ 0 < m := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra! hm
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, m = -k := ⟨m.natAbs, by omega⟩
    have he : (proj F n).Eff (k • projHyp F n) := by
      clear h hm
      induction k with
      | zero => rw [zero_nsmul]; exact Var.eff_zero _
      | succ k ih => rw [succ_nsmul]; exact Var.eff_add _ _ _ ih (Var.eff_hyp _ _)
    have := h.add_eff he
    rw [neg_zsmul, natCast_zsmul, neg_add_cancel] at this
    exact Var.not_big_zero hn this
  · lift m to ℕ using h.le
    rw [natCast_zsmul]
    exact (Var.big_nsmul_iff (by omega)).2 (big_projHyp F n)

example : (proj F 1).hdim 1 ((-2 : ℤ) • projHyp F 1) = 1 ∧
    (proj F 1).hdim 1 ((-1 : ℤ) • projHyp F 1) = 0 ∧
    (proj F 1).chi ((-2 : ℤ) • projHyp F 1) = -1 :=
  ⟨hdim_top_zsmul_projHyp F 1 le_rfl _, hdim_top_zsmul_projHyp F 1 le_rfl _,
    (chi_zsmul_projHyp F 1 _).trans (by simp)⟩

example : (proj F 2).inter (fun i => (![2, 3] : Fin 2 → ℤ) i • projHyp F 2) = 6 :=
  (inter_zsmul_projHyp F 2 _).trans (by simp [Fin.prod_univ_two])

example : ¬ (proj F 1).nef ((-1 : ℤ) • projHyp F 1) ∧ ¬ (proj F 1).big ((-1 : ℤ) • projHyp F 1) ∧
    (proj F 1).nef 0 ∧ ¬ (proj F 1).big 0 :=
  ⟨by rw [nef_zsmul_projHyp_line]; omega, by rw [big_zsmul_projHyp F 1 le_rfl]; omega,
    Var.nef_zero _, Var.not_big_zero le_rfl⟩

end Proj

end GlobalTheory.ProjVar
