import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Development.AbelianVarietyTheory.Definitions.Foundations.SmoothPartStable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwConj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfValuedEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsOpenKerFinIdele

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped ContDiff

namespace GlobalTheory.CuspRep

section Corner

variable {R S T : Type}

def corner [Ring R] [Ring S] (s : R →ₙ+* S) : R →* S where
  toFun x := 1 - s 1 + s x
  map_one' := by simp
  map_mul' x y := by
    have h1 : s 1 * s y = s y := by rw [← map_mul, one_mul]
    have h2 : s x * s 1 = s x := by rw [← map_mul, mul_one]
    have h3 : s 1 * s 1 = s 1 := by rw [← map_mul, mul_one]
    rw [map_mul]
    simp only [mul_add, add_mul, sub_mul, mul_sub, one_mul, mul_one, h1, h2, h3]
    abel

variable [CommRing R] [CommRing S] [CommRing T] {a : ℕ}

def matN (a : ℕ) (s : R →ₙ+* S) : Matrix (Fin a) (Fin a) R →ₙ+* Matrix (Fin a) (Fin a) S where
  toFun x := x.map s
  map_mul' x y := by ext i j; simp [Matrix.mul_apply, map_sum]
  map_zero' := by ext i j; simp
  map_add' x y := by ext i j; simp

def cornerGL (a : ℕ) (s : R →ₙ+* S) : GL (Fin a) R →* GL (Fin a) S := Units.map (corner (matN a s))

theorem map_cornerGL_of_zero (s : R →ₙ+* S) (p : S →+* T) (h : ∀ x, p (s x) = 0) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = 1 := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = _
  simp [h, Matrix.one_apply, apply_ite p]

theorem map_cornerGL_of_hom (s : R →ₙ+* S) (p : S →+* T) (q : R →+* T) (h : ∀ x, p (s x) = q x) (g : GL (Fin a) R) :
    GeneralLinearGroup.map p (cornerGL a s g) = GeneralLinearGroup.map q g := by
  ext i j
  change p ((1 : Matrix (Fin a) (Fin a) S) i j - s ((1 : Matrix (Fin a) (Fin a) R) i j) + s (g i j)) = q (g i j)
  simp [h, Matrix.one_apply, apply_ite p, apply_ite q]

theorem det_map (p : S →+* T) (g : GL (Fin a) S) :
    ((GeneralLinearGroup.det (GeneralLinearGroup.map p g) : Tˣ) : T) = p (GeneralLinearGroup.det g : Sˣ) :=
  (RingHom.map_det p (g : Matrix (Fin a) (Fin a) S)).symm

end Corner

variable (E : Type) [Field E] [NumberField E]

abbrev Ad : Type := AdeleRing (𝓞 E) E

abbrev Af : Type := FiniteAdeleRing (𝓞 E) E

abbrev Cinf : Type := InfinitePlace E → ℂ

abbrev GA (a : ℕ) : Type := GL (Fin a) (Ad E)

abbrev Lie (a : ℕ) : Type := Fin a → Fin a → Cinf E

def pFin : Ad E →+* Af E := RingHom.snd (InfiniteAdeleRing E) (Af E)

def sFin : Af E →ₙ+* Ad E where
  toFun x := ((0, x) : InfiniteAdeleRing E × Af E)
  map_mul' _ _ := Prod.ext (mul_zero _).symm rfl
  map_zero' := rfl
  map_add' _ _ := Prod.ext (add_zero _).symm rfl

def pLoc (w : HeightOneSpectrum (𝓞 E)) : Af E →+* w.adicCompletion E :=
  RestrictedProduct.evalRingHom (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w

open Classical in

def sLoc (w : HeightOneSpectrum (𝓞 E)) : w.adicCompletion E →ₙ+* Af E where
  toFun x := ⟨Pi.single w x, by
    filter_upwards [(Set.finite_singleton w).compl_mem_cofinite] with v hv
    rw [Pi.single_eq_of_ne hv]
    exact zero_mem _⟩
  map_mul' x y := Subtype.ext (Pi.single_mul (α := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)
  map_zero' := Subtype.ext (Pi.single_zero (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  map_add' x y := Subtype.ext (Pi.single_add (f := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x y)

def ratGL (a : ℕ) : GL (Fin a) E →* GA E a := GeneralLinearGroup.map (algebraMap E (Ad E))

def finGL (a : ℕ) : GL (Fin a) (Af E) →* GA E a := cornerGL a (sFin E)

def locGL (a : ℕ) (w : HeightOneSpectrum (𝓞 E)) : GL (Fin a) (w.adicCompletion E) →* GL (Fin a) (Af E) :=
  cornerGL a (sLoc E w)

def finId : (Af E)ˣ →* Ideles E := Units.map (corner (sFin E))

variable {E} in

theorem pLoc_locGL {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E w) (locGL E a w g) = g := by
  classical
  rw [locGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x =>
    Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w x]
  rfl

variable {E} in

theorem pLoc_locGL_of_ne {a : ℕ} {w v : HeightOneSpectrum (𝓞 E)} (h : v ≠ w) (g : GL (Fin a) (w.adicCompletion E)) :
    GeneralLinearGroup.map (pLoc E v) (locGL E a w g) = 1 := by
  classical
  exact map_cornerGL_of_zero _ _ (fun x =>
    Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) h x) g

variable {E} in

theorem finId_det_locGL {a : ℕ} (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    finId E (GeneralLinearGroup.det (locGL E a w g)) = localIdele E w (GeneralLinearGroup.det g) := by
  classical
  refine Units.ext (Prod.ext ?_ (FiniteAdeleRing.ext _ fun v => ?_))
  · change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp
  · change pLoc E v (1 - 1 + (GeneralLinearGroup.det (locGL E a w g) : (Af E)ˣ)) = Function.update (fun v : HeightOneSpectrum (𝓞 E) => (1 : v.adicCompletion E)) w _ v
    rw [sub_self, zero_add, ← det_map]
    by_cases h : v = w
    · subst h; rw [pLoc_locGL, Function.update_self]
    · rw [pLoc_locGL_of_ne h, Function.update_of_ne h]; simp

theorem continuous_finId : Continuous (finId E) :=
  Continuous.units_map _ (continuous_const.add (continuous_const.prodMk continuous_id :
    Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E)))

variable [IsTotallyComplex E]

def infEq : Cinf E ≃+* InfiniteAdeleRing E :=
  RingEquiv.piCongrRight fun w => (InfinitePlace.Completion.ringEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm

theorem continuous_infEq : Continuous (infEq E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).symm.continuous.comp
      (continuous_apply w)

def pInf : Ad E →+* Cinf E := (infEq E).symm.toRingHom.comp (RingHom.fst (InfiniteAdeleRing E) (Af E))

def sInf : Cinf E →ₙ+* Ad E where
  toFun x := ((infEq E x, 0) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext (map_mul (infEq E) x y) (mul_zero _).symm
  map_zero' := Prod.ext (map_zero (infEq E)) rfl
  map_add' x y := Prod.ext (map_add (infEq E) x y) (add_zero _).symm

def infGL (a : ℕ) : GL (Fin a) (Cinf E) →* GA E a := cornerGL a (sInf E)

def infId : (Cinf E)ˣ →* Ideles E := Units.map (corner (sInf E))

theorem continuous_infId : Continuous (infId E) :=
  Continuous.units_map _ (continuous_const.add ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E)))

variable {E} {a : ℕ}

theorem pInf_algebraMap (x : E) (w : InfinitePlace E) : pInf E (algebraMap E (Ad E) x) w = w.embedding x :=
  InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)

theorem ad_ext {x y : Ad E} (h1 : pInf E x = pInf E y) (h2 : pFin E x = pFin E y) : x = y :=
  Prod.ext ((infEq E).symm.injective h1) h2

theorem ga_ext {g h : GA E a} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : GeneralLinearGroup.map (pFin E) g = GeneralLinearGroup.map (pFin E) h) : g = h := by
  ext i j
  exact ad_ext (congrArg (fun x : GL (Fin a) (Cinf E) => x i j) h1) (congrArg (fun x : GL (Fin a) (Af E) => x i j) h2)

@[simp] theorem pInf_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pInf E) (infGL E a y) = y := by
  rw [infGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => (infEq E).symm_apply_apply x]; rfl

@[simp] theorem pFin_infGL (y : GL (Fin a) (Cinf E)) : GeneralLinearGroup.map (pFin E) (infGL E a y) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) y

@[simp] theorem pInf_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pInf E) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => map_zero (infEq E).symm) k

omit [IsTotallyComplex E] in
@[simp] theorem pFin_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pFin E) (finGL E a k) = k := by
  rw [finGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => rfl]; rfl

theorem infGL_mul_finGL (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g :=
  ga_ext (by simp) (by simp)

theorem infGL_comm (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) :
    infGL E a y * finGL E a k = finGL E a k * infGL E a y :=
  ga_ext (by simp) (by simp)

theorem det_infGL (y : GL (Fin a) (Cinf E)) :
    GeneralLinearGroup.det (infGL E a y) = infId E (GeneralLinearGroup.det y) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← det_map, pInf_infGL]
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  · rw [← det_map, pFin_infGL]
    change _ = (1 : Af E) - 0 + 0
    simp

theorem det_finGL (k : GL (Fin a) (Af E)) :
    GeneralLinearGroup.det (finGL E a k) = finId E (GeneralLinearGroup.det k) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← det_map, pInf_finGL]
    change _ = pInf E (1 - sFin E 1 + sFin E _)
    have h : ∀ x, pInf E (sFin E x) = 0 := fun x => map_zero (infEq E).symm
    simp [h]
  · rw [← det_map, pFin_finGL]
    change _ = (1 : Af E) - 1 + (GeneralLinearGroup.det k : (Af E)ˣ)
    simp

omit [NumberField E] [IsTotallyComplex E] in

abbrev toL (x : Matrix (Fin a) (Fin a) (Cinf E)) : Lie E a := Matrix.of.symm x

omit [NumberField E] [IsTotallyComplex E] in

def invSet (E : Type) [Field E] (a : ℕ) : Set (Lie E a) := {x | IsUnit (Matrix.of x)}

omit [IsTotallyComplex E] in

theorem contDiff_det : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

omit [IsTotallyComplex E] in

theorem isOpen_invSet : IsOpen (invSet E a) := by
  have : invSet E a = (fun x : Lie E a => (Matrix.of x).det) ⁻¹' {u | IsUnit u} := by
    ext x; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  exact Units.isOpen.preimage contDiff_det.continuous

omit [NumberField E] [IsTotallyComplex E] in

theorem val_mem_invSet (y : GL (Fin a) (Cinf E)) : (toL y.val) ∈ invSet E a := y.isUnit

open Classical in

def chart (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then φ (g * infGL E a h.unit) else 0

theorem chart_val (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ g (toL y.val) = φ (g * infGL E a y) := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [chart, dif_pos h, e]

omit [IsTotallyComplex E] in

def lmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] _)

omit [IsTotallyComplex E] in

def rmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] _)

theorem chart_mul (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ (g * infGL E a y) = chart φ g ∘ lmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = (toL u.val) := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]
    rfl
  · have h' : ¬ IsUnit (Matrix.of (lmul (toL y.val) x)) := fun h' => h ((Units.isUnit_units_mul y _).1 h')
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem chart_rt_inf (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart (fun x => φ (x * infGL E a y)) g = chart φ g ∘ rmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = (toL u.val) := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]
    rfl
  · have h' : ¬ IsUnit (Matrix.of (rmul (toL y.val) x)) := fun h' => h ((Units.isUnit_mul_units _ y).1 h')
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem chart_rt_fin (φ : GA E a → ℂ) (g : GA E a) (k : GL (Fin a) (Af E)) :
    chart (fun x => φ (x * finGL E a k)) g = chart φ (g * finGL E a k) := by
  funext x
  simp only [chart, mul_assoc, infGL_comm]

variable (E a) in

def Sm : Submodule ℂ (GA E a → ℂ) where
  carrier := {φ | ∀ g, ContDiffOn ℝ ∞ (chart φ g) (invSet E a)}
  add_mem' := fun {φ ψ} h h' g => ((h g).add (h' g)).congr fun x hx => by
    have hx' : IsUnit (Matrix.of x) := hx
    simp [chart, hx']
  zero_mem' g := contDiffOn_const.congr (f := fun _ => 0) fun x _ => by simp [chart]
  smul_mem' c φ h g := ((h g).const_smul c).congr fun x _ => by simp [chart]

theorem rt_mem_Sm (h : GA E a) (φ : GA E a → ℂ) (hφ : φ ∈ Sm E a) : GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ h φ ∈ Sm E a := by
  intro g
  rw [← infGL_mul_finGL h]
  set y := GeneralLinearGroup.map (pInf E) h
  set k := GeneralLinearGroup.map (pFin E) h
  have e : GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ (infGL E a y * finGL E a k) φ =
      fun x => (fun x => φ (x * finGL E a k)) (x * infGL E a y) := by
    funext x
    exact congrArg φ (mul_assoc _ _ _).symm
  rw [e, chart_rt_inf (fun x => φ (x * finGL E a k)), chart_rt_fin]
  exact (hφ _).comp (rmul (toL y.val)).contDiff.contDiffOn fun x hx => IsUnit.mul hx y.isUnit

variable (E a) in

def rt : Representation ℂ (GA E a) (Sm E a) := GlobalTheory.PRep.sub (GlobalTheory.PRep.rightReg ℂ (GA E a) ℂ) (Sm E a) rt_mem_Sm

@[simp] theorem rt_apply (h g : GA E a) (φ : Sm E a) : (rt E a h φ).1 g = φ.1 (g * h) := rfl

omit [NumberField E] [IsTotallyComplex E] in

abbrev oneL (E : Type) [Field E] (a : ℕ) : Lie E a := toL 1

def lieD (X : Lie E a) (φ : GA E a → ℂ) (g : GA E a) : ℂ := fderiv ℝ (chart φ g) (oneL E a) X

theorem contDiffAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    ContDiffAt ℝ ∞ (chart φ g) x := (hφ g).contDiffAt (isOpen_invSet.mem_nhds hx)

theorem differentiableAt_chart {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (g : GA E a) :
    DifferentiableAt ℝ (chart φ g) (oneL E a) := (contDiffAt_chart hφ g isUnit_one).differentiableAt (by simp)

theorem chart_lieD {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) (X : Lie E a) (g : GA E a) {x : Lie E a} (hx : x ∈ invSet E a) :
    chart (lieD X φ) g x = fderiv ℝ (chart φ g) x (rmul X x) := by
  obtain ⟨u, hu⟩ := id hx
  have e : x = (toL u.val) := hu.symm
  subst e
  rw [chart_val, lieD, chart_mul]
  have e1 : lmul (toL u.val) (oneL E a) = toL u.val := mul_one u.val
  rw [fderiv_comp _ (by rw [e1]; exact (contDiffAt_chart hφ g hx).differentiableAt (by simp)) (lmul (toL u.val)).differentiableAt,
    e1, ContinuousLinearMap.fderiv]
  rfl

theorem lieD_mem_Sm (X : Lie E a) {φ : GA E a → ℂ} (hφ : φ ∈ Sm E a) : lieD X φ ∈ Sm E a := fun g =>
  (((hφ g).fderiv_of_isOpen isOpen_invSet (by simp)).clm_apply (rmul X).contDiff.contDiffOn).congr
    fun _ hx => chart_lieD hφ X g hx

variable (E a) in

def lie : Lie E a →ₗ[ℝ] Module.End ℂ (Sm E a) where
  toFun X :=
    { toFun := fun φ => ⟨lieD X φ.1, lieD_mem_Sm X φ.2⟩
      map_add' := fun φ ψ => Subtype.ext <| funext fun g => by
        have e : chart (φ.1 + ψ.1) g = chart φ.1 g + chart ψ.1 g := by
          funext x; by_cases h : IsUnit (Matrix.of x) <;> simp [chart, h]
        change fderiv ℝ (chart (φ.1 + ψ.1) g) _ X = _
        rw [e, fderiv_add (differentiableAt_chart φ.2 g) (differentiableAt_chart ψ.2 g)]
        rfl
      map_smul' := fun c φ => Subtype.ext <| funext fun g => by
        have e : chart (c • φ.1) g = c • chart φ.1 g := by
          funext x; simp [chart]
        change fderiv ℝ (chart (c • φ.1) g) _ X = _
        rw [e, fderiv_const_smul (differentiableAt_chart φ.2 g)]
        rfl }
  map_add' X Y := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_add (fderiv ℝ (chart φ.1 g) _) X Y
  map_smul' c X := LinearMap.ext fun φ => Subtype.ext <| funext fun g => map_smul (fderiv ℝ (chart φ.1 g) _) c X

@[simp] theorem lie_apply (X : Lie E a) (φ : Sm E a) (g : GA E a) : (lie E a X φ).1 g = lieD X φ.1 g := rfl

theorem hasDerivAt_curve (φ : Sm E a) (g : GA E a) (c : ℝ → GL (Fin a) (Cinf E)) (X : Lie E a) (h0 : c 0 = 1)
    (hc : HasDerivAt (fun t => toL (c t).val) X 0) :
    HasDerivAt (fun t => φ.1 (g * infGL E a (c t))) (lieD X φ.1 g) 0 := by
  have h : HasFDerivAt (chart φ.1 g) (fderiv ℝ (chart φ.1 g) (oneL E a)) (toL (c 0).val) := by
    rw [h0]; exact (differentiableAt_chart φ.2 g).hasFDerivAt
  have h2 := h.comp_hasDerivAt (0 : ℝ) hc
  simp only [Function.comp_def, chart_val] at h2
  exact h2

theorem lie_rt_fin (X : Lie E a) (k : GL (Fin a) (Af E)) :
    lie E a X * rt E a (finGL E a k) = rt E a (finGL E a k) * lie E a X :=
  LinearMap.ext fun φ => Subtype.ext <| funext fun g =>
    congrArg (fun f => fderiv ℝ f (oneL E a) X) (chart_rt_fin φ.1 g k)

theorem lie_comm (X Y : Lie E a) :
    lie E a X * lie E a Y - lie E a Y * lie E a X =
      lie E a (toL (Matrix.of X * Matrix.of Y)) - lie E a (toL (Matrix.of Y * Matrix.of X)) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  have hs : ContDiffAt ℝ ∞ (chart φ.1 g) (oneL E a) := contDiffAt_chart φ.2 g isUnit_one
  have hd : DifferentiableAt ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) :=
    (hs.fderiv_right (m := 1) (by norm_cast)).differentiableAt (by simp)
  have key : ∀ X Y : Lie E a, lieD X (lieD Y φ.1) g =
      fderiv ℝ (fderiv ℝ (chart φ.1 g)) (oneL E a) X Y + lieD (toL (Matrix.of X * Matrix.of Y)) φ.1 g := by
    intro X Y
    have e : chart (lieD Y φ.1) g =ᶠ[𝓝 (oneL E a)] fun x => fderiv ℝ (chart φ.1 g) x (rmul Y x) :=
      Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => chart_lieD φ.2 Y g hx
    rw [lieD, e.fderiv_eq, fderiv_clm_apply hd (rmul Y).differentiableAt, ContinuousLinearMap.fderiv]
    have e1 : rmul Y (oneL E a) = Y := one_mul (Matrix.of Y)
    rw [e1, add_comm]
    rfl
  change lieD X (lieD Y φ.1) g - lieD Y (lieD X φ.1) g = lieD _ φ.1 g - lieD _ φ.1 g
  rw [key, key, (hs.isSymmSndFDerivAt (by simp; norm_cast)).eq X Y]
  ring

end GlobalTheory.CuspRep
