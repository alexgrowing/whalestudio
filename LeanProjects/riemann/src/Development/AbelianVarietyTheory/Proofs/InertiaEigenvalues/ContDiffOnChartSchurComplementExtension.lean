import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemIdemSf

open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.SchurExt
open scoped ContDiff Topology

noncomputable section

namespace GlobalTheory.SchurExt.SmoothPart

section Calc

variable {K : Type} [NormedCommRing K] [NormedAlgebra ℝ K] [CompleteSpace K]
variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {s : Set X}

theorem ent_mul {p k q : ℕ} {f : X → Matrix (Fin p) (Fin k) K} {g : X → Matrix (Fin k) (Fin q) K}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x * g x) i j) s := by
  intro i j
  simp only [Matrix.mul_apply]
  exact ContDiffOn.sum fun l _ => (hf i l).mul (hg l j)

theorem ent_sub {p q : ℕ} {f g : X → Matrix (Fin p) (Fin q) K}
    (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) (hg : ∀ i j, ContDiffOn ℝ ∞ (fun x => g x i j) s) :
    ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x - g x) i j) s := fun i j => (hf i j).sub (hg i j)

theorem det_sm {p : ℕ} {f : X → Matrix (Fin p) (Fin p) K} (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s) :
    ContDiffOn ℝ ∞ (fun x => (f x).det) s := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => hf _ _)

theorem ent_inv {p : ℕ} {f : X → Matrix (Fin p) (Fin p) K} (hf : ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s)
    (hu : ∀ x ∈ s, IsUnit (f x).det) : ∀ i j, ContDiffOn ℝ ∞ (fun x => (f x)⁻¹ i j) s := by
  intro i j
  have hd := det_sm hf
  have hi : ContDiffOn ℝ ∞ (fun x => Ring.inverse (f x).det) s := fun x hx => by
    obtain ⟨u, hu'⟩ := hu x hx
    have h1 : ContDiffAt ℝ ∞ Ring.inverse (u : K) := contDiffAt_ringInverse ℝ u
    rw [hu'] at h1
    exact h1.comp_contDiffWithinAt x (hd x hx)
  have ha : ContDiffOn ℝ ∞ (fun x => (f x).adjugate i j) s := by
    simp only [Matrix.adjugate_apply]
    refine det_sm fun k l => ?_
    by_cases hk : k = j
    · subst hk; simp only [Matrix.updateRow_self]; exact contDiffOn_const
    · simp only [Matrix.updateRow_ne hk]; exact hf k l
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul]
  exact hi.mul ha

end Calc

section Maps

variable {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) {m r : ℕ}

theorem map_inv_of {k : ℕ} (N : Matrix (Fin k) (Fin k) R) (h : IsUnit N.det) : N⁻¹.map p = (N.map p)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ h, Matrix.map_one _ (map_zero p) (map_one p)]

theorem map_Xof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Xof M).map p = Xof (M.map p) := by
  rw [Xof, Xof, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Yof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Yof M).map p = Yof (M.map p) := by
  rw [Yof, Yof, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (h : IsUnit (Dof M).det) :
    (Scof M).map p = Scof (M.map p) := by
  rw [Scof, Scof, Matrix.map_sub _ (map_sub p), Matrix.map_mul, Matrix.map_mul, map_inv_of p _ h]; rfl

theorem map_Dof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) :
    (Dof M).map p = Dof (M.map p) := rfl

theorem det_Scof (M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) R) (hM : IsUnit M.det)
    (hD : IsUnit (Dof M).det) : IsUnit (Scof M).det := by
  letI := (blk M).toBlocks₂₂.invertibleOfIsUnitDet hD
  have h1 : M.det = (Dof M).det * (Scof M).det := by
    rw [← Matrix.det_submatrix_equiv_self (eqv m r).symm M]
    have := Matrix.det_fromBlocks₂₂ (blk M).toBlocks₁₁ (blk M).toBlocks₁₂ (blk M).toBlocks₂₁ (blk M).toBlocks₂₂
    rw [Matrix.fromBlocks_toBlocks] at this
    rw [show M.submatrix (eqv m r).symm (eqv m r).symm = blk M from rfl, this, Matrix.invOf_eq_nonsing_inv]
    rfl
  rw [h1] at hM
  exact isUnit_of_mul_isUnit_right hM

end Maps

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

theorem isUnit_ad_iff (a : Ad E) : IsUnit a ↔ IsUnit (pInf E a) ∧ IsUnit (pFin E a) := by
  change IsUnit a ↔ IsUnit ((infEq E).symm a.1) ∧ IsUnit a.2
  rw [isUnit_map_iff]
  exact Prod.isUnit_iff (x := (a : InfiniteAdeleRing E × Af E))

theorem mkGL_split {k : ℕ} (N : Matrix (Fin k) (Fin k) (Ad E)) (h : IsUnit N.det) :
    mkGL N = infGL E k (mkGL (N.map (pInf E))) * finGL E k (mkGL (N.map (pFin E))) := by
  have hi : IsUnit (N.map (pInf E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  have hf : IsUnit (N.map (pFin E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  refine ga_ext ?_ ?_
  · rw [map_mul, pInf_infGL, pInf_finGL, mul_one]
    apply Units.ext
    change (mkGL N : Matrix (Fin k) (Fin k) (Ad E)).map (pInf E) = _
    rw [coe_mkGL h, coe_mkGL hi]
  · rw [map_mul, pFin_infGL, pFin_finGL, one_mul]
    apply Units.ext
    change (mkGL N : Matrix (Fin k) (Fin k) (Ad E)).map (pFin E) = _
    rw [coe_mkGL h, coe_mkGL hf]

theorem apply_mkGL {k : ℕ} (φ : GA E k → ℂ) (N : Matrix (Fin k) (Fin k) (Ad E)) (h : IsUnit N.det) :
    φ (mkGL N) = chart φ (finGL E k (mkGL (N.map (pFin E)))) (toL (N.map (pInf E))) := by
  have hi : IsUnit (N.map (pInf E)).det := by rw [show (N.map _).det = _ from (RingHom.map_det _ N).symm]; exact h.map _
  rw [mkGL_split N h, infGL_comm, ← chart_val φ (finGL E k _) (mkGL (N.map (pInf E))), coe_mkGL hi]

theorem psi_split (a : Ad E) :
    psi a = GlobalTheory.WhitBump.psiInf (pInf E a) * GlobalTheory.WhitBump.psiFin (pFin E a) := by
  have e : a = sInf E (pInf E a) + sFin E (pFin E a) := by
    refine ad_ext ?_ ?_
    · rw [map_add]
      change pInf E a = (infEq E).symm (infEq E (pInf E a)) + (infEq E).symm 0
      simp
    · rw [map_add]
      change pFin E a = 0 + pFin E a
      simp
  rw [psi]
  conv_lhs => rw [e]
  rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  rfl

theorem contDiff_psiInf : ContDiff ℝ ∞ (GlobalTheory.WhitBump.psiInf (E := E)) := by
  let T : Cinf E →+ ℝ := (GroundTheory.Global.infiniteTrace E).comp (infEq E).toAddMonoidHom
  have hT : Continuous T := (GroundTheory.Global.continuous_infiniteTrace E).comp (continuous_infEq E)
  let L := AddMonoidHom.toRealLinearMap T hT
  have e : ∀ z, GlobalTheory.WhitBump.psiInf z = Complex.exp (((2 * Real.pi * (-(L z)) : ℝ) : ℂ) * Complex.I) := fun z => by
    change ((GroundTheory.Global.adelicChar E ((infEq E z, 0) : InfiniteAdeleRing E × Af E)) : ℂ) = _
    rw [GroundTheory.Global.adelicChar_infinite, Real.fourierChar_apply]
    rfl
  rw [show GlobalTheory.WhitBump.psiInf (E := E) = fun z => Complex.exp (((2 * Real.pi * (-(L z)) : ℝ) : ℂ) * Complex.I) from funext e]
  exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul L.contDiff.neg)).mul contDiff_const)

theorem continuous_pInf_sm : Continuous (pInf E) :=
  continuous_pi fun w =>
    ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)).comp continuous_fst

variable {m r : ℕ}

theorem chart_schurF_eq (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ)
    (g : GA E (m + r + 1 + 1)) (x : Lie E (m + r + 1 + 1)) (hx : IsUnit (Matrix.of x))
    (hD : IsUnit (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x)).det)
    (hDf : IsUnit (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E))).det) :
    chart (schurF β b₁ χ) g x =
      GlobalTheory.WhitBump.psiInf (Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) (Fin.last m) 0) *
      GlobalTheory.WhitBump.psiFin (Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) (Fin.last m) 0) *
      chart β (finGL E _ (mkGL (Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)))))
        (toL (Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x))) *
      chart b₁ (finGL E _ (mkGL (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)))))
        (toL (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x))) *
      ((χ (fun i j => Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) i j) : ℂ) *
        (open Classical in if ∀ i j, Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j ∈
          GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then 1 else 0)) := by
  set M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E) :=
    ((g * infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  have hMi : M.map (pInf E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) = Matrix.of x :=
      (congrArg Units.val (pInf_infGL hx.unit)).trans hx.unit_spec
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1]
  have hMf : M.map (pFin E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) = 1 :=
      congrArg Units.val (pFin_infGL hx.unit)
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1, Matrix.mul_one]
  have hDM : IsUnit (Dof M).det := by
    rw [isUnit_ad_iff, RingHom.map_det, RingHom.map_det]
    exact ⟨by rw [RingHom.mapMatrix_apply, map_Dof, hMi]; exact hD,
      by rw [RingHom.mapMatrix_apply, map_Dof, hMf]; exact hDf⟩
  have hSM : IsUnit (Scof M).det :=
    det_Scof M ((Matrix.isUnit_iff_isUnit_det _).1 (Units.isUnit _)) hDM
  rw [chart, dif_pos hx]
  change schurF β b₁ χ (g * infGL E _ hx.unit) = _
  rw [schurF]
  rw [if_pos hDM, psi_split, apply_mkGL β _ hSM, apply_mkGL b₁ _ hDM, chiF]
  have e1 : pInf E (Xof M (Fin.last m) 0) = Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) (Fin.last m) 0 := by
    rw [← hMi, ← map_Xof _ M hDM, Matrix.map_apply]
  have e2 : pFin E (Xof M (Fin.last m) 0) = Xof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) (Fin.last m) 0 := by
    rw [← hMf, ← map_Xof _ M hDM, Matrix.map_apply]
  have e3 : (Scof M).map (pFin E) = Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) := by
    rw [map_Scof _ M hDM, hMf]
  have e4 : (Scof M).map (pInf E) = Scof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) := by
    rw [map_Scof _ M hDM, hMi]
  have e5 : (Dof M).map (pFin E) = Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) := by
    rw [map_Dof, hMf]
  have e6 : (Dof M).map (pInf E) = Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) := by
    rw [map_Dof, hMi]
  have e7 : (fun i j => pInf E (Yof M i j)) = fun i j => Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x) i j := by
    funext i j; rw [← hMi, ← map_Yof _ M hDM, Matrix.map_apply]
  have e8 : ∀ i j, pFin E (Yof M i j) = Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j := by
    intro i j; rw [← hMf, ← map_Yof _ M hDM, Matrix.map_apply]
  have e9 : (∀ i j, pFin E (Yof M i j) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) =
      (∀ i j, Yof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E)) i j ∈
        GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) :=
    propext (forall_congr' fun i => forall_congr' fun j => by rw [e8])
  rw [e1, e2, e3, e4, e5, e6, e7]
  split_ifs with h1 h2 h2
  · ring
  · exact absurd (e9 ▸ h1) h2
  · exact absurd (e9 ▸ h2) h1
  · ring

theorem chart_schurF_zero (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ)
    (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ) (C : Set (GA E (r + 1)))
    (hC : ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C)
    (g : GA E (m + r + 1 + 1)) (x : Lie E (m + r + 1 + 1)) (hx : IsUnit (Matrix.of x))
    (hK : (Dof ((g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x)).det ∉
      (fun c : GA E (r + 1) => pInf E (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det) '' C) :
    chart (schurF β b₁ χ) g x = 0 := by
  set M : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E) :=
    ((g * infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)) with hMdef
  have hMi : M.map (pInf E) = (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) * Matrix.of x := by
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) = Matrix.of x :=
      (congrArg Units.val (pInf_infGL hx.unit)).trans hx.unit_spec
    rw [hMdef, Units.val_mul, Matrix.map_mul, h1]
  rw [chart, dif_pos hx]
  change schurF β b₁ χ (g * infGL E _ hx.unit) = 0
  rw [schurF]
  split_ifs with hDM
  · have hb : b₁ (mkGL (Dof M)) = 0 := by
      by_contra hne
      obtain ⟨u, hu, hc⟩ := hC _ hne
      apply hK
      refine ⟨_, hc, ?_⟩
      have hu1 : (u : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = 1 := by
        rw [Matrix.det_of_upperTriangular (fun i j h => hu.1 i j h)]
        exact Finset.prod_eq_one fun i _ => hu.2 i
      have hu2 : ((u⁻¹ : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = 1 := by
        have := congrArg Matrix.det (congrArg Units.val (inv_mul_cancel u))
        rw [Units.val_mul, Matrix.det_mul, hu1, mul_one, Units.val_one, Matrix.det_one] at this
        exact this
      change pInf E ((u⁻¹ * mkGL (Dof M) : GA E (r + 1)) : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det = _
      rw [Units.val_mul, Matrix.det_mul, hu2, one_mul, coe_mkGL hDM, RingHom.map_det, RingHom.mapMatrix_apply,
        map_Dof, hMi]
    rw [hb]; ring
  · rfl

end GlobalTheory.SchurExt.SmoothPart

namespace GlobalTheory.SchurExt

open GlobalTheory.SchurExt.SmoothPart in

theorem contDiffOn_chart_schurF : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m r : ℕ)
    (β : GA E (m + 1) → ℂ) (b₁ : GA E (r + 1) → ℂ) (χ : (Fin (r + 1) → Fin (m + 1) → Cinf E) → ℝ),
    (∀ g, ContDiffOn ℝ ∞ (chart β g) (invSet E (m + 1))) → (∀ g, ContDiffOn ℝ ∞ (chart b₁ g) (invSet E (r + 1))) →
    (∃ C : Set (GA E (r + 1)), IsCompact C ∧ ∀ p, b₁ p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA E (r + 1), u⁻¹ * p ∈ C) →
    ContDiff ℝ ∞ χ → ∀ g, ContDiffOn ℝ ∞ (chart (schurF β b₁ χ) g) (invSet E (m + r + 1 + 1)) := by
  intro E _ _ _ m r β b₁ χ hβ hb hC hχ g
  set Gi := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pInf E) with hGi
  set Gf := (g : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) with hGf
  by_cases hDf : IsUnit (Dof Gf).det
  swap
  · refine (contDiffOn_const (c := (0 : ℂ))).congr fun x hx0 => ?_
    have hx : IsUnit (Matrix.of x) := hx0
    rw [chart, dif_pos hx]
    change schurF β b₁ χ (g * infGL E _ hx.unit) = 0
    rw [schurF, if_neg]
    intro hDM
    apply hDf
    have h1 : ((infGL E _ hx.unit : GA E _) : Matrix (Fin (m + r + 1 + 1)) (Fin (m + r + 1 + 1)) (Ad E)).map (pFin E) = 1 :=
      congrArg Units.val (pFin_infGL hx.unit)
    have := ((isUnit_ad_iff _).1 hDM).2
    rwa [RingHom.map_det, RingHom.mapMatrix_apply, map_Dof, Units.val_mul, Matrix.map_mul, h1, Matrix.mul_one] at this
  obtain ⟨C, hCc, hCp⟩ := hC
  set K := (fun c : GA E (r + 1) => pInf E (c : Matrix (Fin (r + 1)) (Fin (r + 1)) (Ad E)).det) '' C with hK
  have hKc : IsCompact K := hCc.image (continuous_pInf_sm.comp (Continuous.matrix_det Units.continuous_val))
  have hKu : ∀ z ∈ K, IsUnit z := by
    rintro _ ⟨c, -, rfl⟩
    exact ((Matrix.isUnit_iff_isUnit_det _).1 c.isUnit).map _
  have hf0 : ∀ i j, ContDiffOn ℝ ∞ (fun x : Lie E (m + r + 1 + 1) => (Gi * Matrix.of x) i j) Set.univ :=
    ent_mul (fun _ _ => contDiffOn_const) (fun i j => ((contDiff_apply ℝ _ j).comp (contDiff_apply ℝ _ i)).contDiffOn)
  set φ := fun x : Lie E (m + r + 1 + 1) => (Dof (Gi * Matrix.of x)).det with hφ
  have hφc : Continuous φ := (contDiffOn_univ.1 (det_sm fun i j => hf0 _ _)).continuous
  have hGu : IsUnit Gi.det := by
    rw [hGi, show (Gi).det = _ from (RingHom.map_det _ _).symm]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 g.isUnit).map _
  refine contDiffOn_of_locally_contDiffOn fun x hx => ?_
  by_cases hu : IsUnit (φ x)
  · refine ⟨{x | IsUnit (φ x)}, Units.isOpen.preimage hφc, hu, ?_⟩
    set s := invSet E (m + r + 1 + 1) ∩ {x | IsUnit (φ x)} with hs
    have hf : ∀ i j, ContDiffOn ℝ ∞ (fun x : Lie E (m + r + 1 + 1) => (Gi * Matrix.of x) i j) s :=
      fun i j => (hf0 i j).mono (Set.subset_univ _)
    have hA : ∀ i j, ContDiffOn ℝ ∞ (fun x => Aof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hB : ∀ i j, ContDiffOn ℝ ∞ (fun x => Bof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hCm : ∀ i j, ContDiffOn ℝ ∞ (fun x => Cof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hD : ∀ i j, ContDiffOn ℝ ∞ (fun x => Dof (Gi * Matrix.of x) i j) s := fun i j => hf _ _
    have hDi := ent_inv hD fun x hx => hx.2
    have hX := ent_mul hB hDi
    have hS := ent_sub hA (ent_mul (ent_mul hB hDi) hCm)
    have hY := ent_mul hDi hCm
    have t1 : ContDiffOn ℝ ∞ (fun x => GlobalTheory.WhitBump.psiInf (Xof (Gi * Matrix.of x) (Fin.last m) 0)) s :=
      contDiff_psiInf.comp_contDiffOn (hX _ _)
    have t2 : ContDiffOn ℝ ∞ (fun x => chart β (finGL E _ (mkGL (Scof Gf))) (toL (Scof (Gi * Matrix.of x)))) s :=
      (hβ _).comp (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hS i j) fun x hx' => by
        show IsUnit (Scof (Gi * Matrix.of x))
        rw [Matrix.isUnit_iff_isUnit_det]
        refine det_Scof _ ?_ hx'.2
        rw [Matrix.det_mul]
        exact hGu.mul ((Matrix.isUnit_iff_isUnit_det _).1 hx'.1)
    have t3 : ContDiffOn ℝ ∞ (fun x => chart b₁ (finGL E _ (mkGL (Dof Gf))) (toL (Dof (Gi * Matrix.of x)))) s :=
      (hb _).comp (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hD i j) fun x hx' =>
        (Matrix.isUnit_iff_isUnit_det _).2 hx'.2
    have t4 : ContDiffOn ℝ ∞ (fun x => (χ (fun i j => Yof (Gi * Matrix.of x) i j) : ℂ)) s :=
      Complex.ofRealCLM.contDiff.comp_contDiffOn
        (hχ.comp_contDiffOn (contDiffOn_pi.2 fun i => contDiffOn_pi.2 fun j => hY i j))
    refine ((((t1.mul (contDiffOn_const (c := GlobalTheory.WhitBump.psiFin (Xof Gf (Fin.last m) 0)))).mul t2).mul t3).mul
      (t4.mul (contDiffOn_const (c := (open Classical in
        if ∀ i j, Yof Gf i j ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E then (1 : ℂ) else 0))))).congr fun x hx' => ?_
    exact chart_schurF_eq β b₁ χ g x hx'.1 hx'.2 hDf
  · refine ⟨φ ⁻¹' Kᶜ, hKc.isClosed.isOpen_compl.preimage hφc, fun hk => hu (hKu _ hk), ?_⟩
    exact (contDiffOn_const (c := (0 : ℂ))).congr fun x hx' => chart_schurF_zero β b₁ χ C hCp g x hx'.1 hx'.2

end GlobalTheory.SchurExt
