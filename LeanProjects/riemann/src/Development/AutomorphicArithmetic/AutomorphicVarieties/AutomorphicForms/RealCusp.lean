import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.CuspRep Formalism.L2.Host
open scoped ContDiff

namespace UpperTheory.V.TR

variable (E : Type) [Field E] [NumberField E]

abbrev Rinf : Type := InfinitePlace E → ℝ

abbrev Lie (a : ℕ) : Type := Fin a → Fin a → Rinf E

variable [IsTotallyReal E]

def infEq : Rinf E ≃+* InfiniteAdeleRing E :=
  RingEquiv.piCongrRight fun w => (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm

theorem continuous_infEq : Continuous (infEq E) :=
  continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivRealOfIsReal (IsTotallyReal.isReal w)).symm.continuous.comp
      (continuous_apply w)

def pInf : Ad E →+* Rinf E := (infEq E).symm.toRingHom.comp (RingHom.fst (InfiniteAdeleRing E) (Af E))

def sInf : Rinf E →ₙ+* Ad E where
  toFun x := ((infEq E x, 0) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext (map_mul (infEq E) x y) (mul_zero _).symm
  map_zero' := Prod.ext (map_zero (infEq E)) rfl
  map_add' x y := Prod.ext (map_add (infEq E) x y) (add_zero _).symm

def infGL (a : ℕ) : GL (Fin a) (Rinf E) →* GA E a := cornerGL a (sInf E)

def infId : (Rinf E)ˣ →* Ideles E := Units.map (corner (sInf E))

theorem continuous_infId : Continuous (infId E) :=
  Continuous.units_map _ (continuous_const.add ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Rinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E)))

variable {E} {a : ℕ}

theorem ad_ext {x y : Ad E} (h1 : pInf E x = pInf E y) (h2 : pFin E x = pFin E y) : x = y :=
  Prod.ext ((infEq E).symm.injective h1) h2

theorem ga_ext {g h : GA E a} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : GeneralLinearGroup.map (pFin E) g = GeneralLinearGroup.map (pFin E) h) : g = h := by
  ext i j
  exact ad_ext (congrArg (fun x : GL (Fin a) (Rinf E) => x i j) h1) (congrArg (fun x : GL (Fin a) (Af E) => x i j) h2)

@[simp] theorem pInf_infGL (y : GL (Fin a) (Rinf E)) : GeneralLinearGroup.map (pInf E) (infGL E a y) = y := by
  rw [infGL, map_cornerGL_of_hom _ _ (RingHom.id _) fun x => (infEq E).symm_apply_apply x]; rfl

@[simp] theorem pFin_infGL (y : GL (Fin a) (Rinf E)) : GeneralLinearGroup.map (pFin E) (infGL E a y) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => rfl) y

@[simp] theorem pInf_finGL (k : GL (Fin a) (Af E)) : GeneralLinearGroup.map (pInf E) (finGL E a k) = 1 :=
  map_cornerGL_of_zero _ _ (fun _ => map_zero (infEq E).symm) k

theorem infGL_mul_finGL (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g :=
  ga_ext (by simp) (by simp)

theorem infGL_comm (y : GL (Fin a) (Rinf E)) (k : GL (Fin a) (Af E)) :
    infGL E a y * finGL E a k = finGL E a k * infGL E a y :=
  ga_ext (by simp) (by simp)

theorem det_infGL (y : GL (Fin a) (Rinf E)) :
    GeneralLinearGroup.det (infGL E a y) = infId E (GeneralLinearGroup.det y) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← GlobalTheory.CuspRep.det_map, pInf_infGL]
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  · rw [← GlobalTheory.CuspRep.det_map, pFin_infGL]
    change _ = (1 : Af E) - 0 + 0
    simp

omit [NumberField E] [IsTotallyReal E] in

abbrev toL (x : Matrix (Fin a) (Fin a) (Rinf E)) : Lie E a := Matrix.of.symm x

omit [NumberField E] [IsTotallyReal E] in

def invSet (E : Type) [Field E] (a : ℕ) : Set (Lie E a) := {x | IsUnit (Matrix.of x)}

omit [IsTotallyReal E] in

theorem contDiff_det : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

omit [IsTotallyReal E] in

theorem isOpen_invSet : IsOpen (invSet E a) := by
  have : invSet E a = (fun x : Lie E a => (Matrix.of x).det) ⁻¹' {u | IsUnit u} := by
    ext x; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  exact Units.isOpen.preimage contDiff_det.continuous

omit [NumberField E] [IsTotallyReal E] in

theorem val_mem_invSet (y : GL (Fin a) (Rinf E)) : (toL y.val) ∈ invSet E a := y.isUnit

open Classical in

def chart (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then φ (g * infGL E a h.unit) else 0

theorem chart_val (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Rinf E)) :
    chart φ g (toL y.val) = φ (g * infGL E a y) := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [chart, dif_pos h, e]

omit [IsTotallyReal E] in

def lmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Rinf E) →ₗ[ℝ] _)

omit [IsTotallyReal E] in

def rmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Rinf E) →ₗ[ℝ] _)

theorem chart_mul (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Rinf E)) :
    chart φ (g * infGL E a y) = chart φ g ∘ lmul (toL y.val) := by
  funext x
  by_cases h : IsUnit (Matrix.of x)
  · obtain ⟨u, hu⟩ := h
    have hx : x = (toL u.val) := hu.symm
    rw [hx, chart_val, mul_assoc, ← map_mul, ← chart_val φ g]
    rfl
  · have h' : ¬ IsUnit (Matrix.of (lmul (toL y.val) x)) := fun h' => h ((Units.isUnit_units_mul y _).1 h')
    rw [Function.comp_apply, chart, chart, dif_neg h, dif_neg h']

theorem chart_rt_inf (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Rinf E)) :
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

omit [NumberField E] [IsTotallyReal E] in

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

theorem hasDerivAt_curve (φ : Sm E a) (g : GA E a) (c : ℝ → GL (Fin a) (Rinf E)) (X : Lie E a) (h0 : c 0 = 1)
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

open Classical in

def Eop (v : InfinitePlace E) (i j : Fin a) : Module.End ℂ (Sm E a) :=
  lie E a (toL (Matrix.single i j (Pi.single v 1)))

def cap (v : InfinitePlace E) (u : ℂ) : Module.End ℂ (Sm E a) := Formalism.REAL.qdet (Eop v) (u + ((a : ℂ) - 1) / 2)

variable (E a) in

def Zalg : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Algebra.adjoin ℂ {z | ∃ v u, z = cap v u}

abbrev Kinf (E : Type) [Field E] (a : ℕ) : Type := Matrix.unitaryGroup (Fin a) (Rinf E)

inductive Op (E : Type) [Field E] [NumberField E] (a : ℕ) : Type
  | fin (k : GL (Fin a) (Af E))
  | cpt (k : Kinf E a)
  | lie (X : Lie E a)

variable (E a) in

def finRep : Representation ℂ (GL (Fin a) (Af E)) (Sm E a) := (rt E a).comp (finGL E a)

variable (E a) in

def cptRep : Representation ℂ (Kinf E a) (Sm E a) := (rt E a).comp ((infGL E a).comp Unitary.toUnits)

def act : Op E a → Module.End ℂ (Sm E a)
  | .fin k => finRep E a k
  | .cpt k => cptRep E a k
  | .lie X => lie E a X

def IsStable (V : Submodule ℂ (Sm E a)) : Prop := ∀ o, ∀ φ ∈ V, act o φ ∈ V

def height (y : GL (Fin a) (Rinf E)) : ℝ := 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖

structure IsAutForm (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  level : IsOpen {k | finRep E a k φ = φ}
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
  growth : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N

def IsCuspForm (φ : Sm E a) : Prop := IsAutForm φ ∧ GlobalTheory.CuspRep.IsCuspidal φ.1

variable (E a) in

@[ext] structure CuspSub where

  V : Submodule ℂ (Sm E a)
  cusp : ∀ φ ∈ V, IsCuspForm φ
  stable : IsStable V
  ne_bot : V ≠ ⊥
  irred : ∀ W ≤ V, IsStable W → W = ⊥ ∨ W = V

namespace CuspSub

variable (π π' : CuspSub E a)

def op (o : Op E a) : Module.End ℂ π.V := (act o).restrict (π.stable o)

@[simp] theorem op_val (o : Op E a) (φ : π.V) : (π.op o φ).1 = act o φ.1 := rfl

def Iso : Prop := ∃ T : π.V ≃ₗ[ℂ] π'.V, ∀ o φ, T (π.op o φ) = π'.op o (T φ)

def HasInfChar (v : InfinitePlace E) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u, ∀ φ ∈ π.V, cap v u φ = (m.map (u + ·)).prod • φ

def IsRegAlg : Prop :=
  ∀ v, ∃ m, π.HasInfChar v m ∧ m.Nodup ∧ ∀ z ∈ m, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

def finPart : Representation ℂ (GL (Fin a) (Af E)) π.V :=
  GlobalTheory.PRep.sub (finRep E a) π.V fun k => π.stable (.fin k)

def locRep (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) π.V :=
  π.finPart.comp (locGL E a w)

def IsLocComp (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)

def IsFinComp (σ : SmIrr (GL (Fin a) (Af E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.finPart g (f v)

def HasSat (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop := GlobalTheory.LFun.HasSatGL w (π.locRep w) B

def IsSelfDualBy (χ : HChar E) : Prop :=
  ∃ (B : π.V →ₗ[ℂ] π.V →ₗ[ℂ] ℂ) (d : Rinf E →ₗ[ℝ] ℂ),
    (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ (z : Rinf E) (u : (Rinf E)ˣ), (∀ v, u.val v = Real.exp (z v)) →
      ((χ.1 (infId E u) : ℂˣ) : ℂ) = Complex.exp (d z)) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π.op (.fin k) ψ) = ((chiDet a χ (finGL E a k) : ℂˣ) : ℂ) * B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π.op (.cpt k) ψ) =
      ((chiDet a χ (infGL E a (Unitary.toUnits k)) : ℂˣ) : ℂ) * B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π.op (.lie X) ψ) = d (Matrix.of X).trace * B φ ψ

structure Polarized (χ : HChar E) : Prop where
  sign : ∀ v v' : InfinitePlace E, χ.locInf v (-1) = χ.locInf v' (-1)
  dual : π.IsSelfDualBy χ

end CuspSub

variable (E a) in

def oneFn : Sm E a :=
  ⟨fun _ => 1, fun _ => contDiffOn_const.congr (f := fun _ => 1) fun x hx => dif_pos (show IsUnit (Matrix.of x) from hx)⟩

theorem oneFn_ne_zero : oneFn E a ≠ 0 := fun h => one_ne_zero (congrFun (congrArg Subtype.val h) 1)

theorem lie_oneFn (X : Lie E a) : lie E a X (oneFn E a) = 0 := by
  refine Subtype.ext <| funext fun g => ?_
  have e : chart (oneFn E a).1 g =ᶠ[𝓝 (oneL E a)] fun _ => 1 :=
    Filter.eventually_of_mem (isOpen_invSet.mem_nhds isUnit_one) fun x hx => dif_pos (show IsUnit (Matrix.of x) from hx)
  change fderiv ℝ _ _ X = 0
  rw [e.fderiv_eq]
  simp

theorem Zalg_stable {V : Submodule ℂ (Sm E a)} (hV : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : ∀ φ ∈ V, z φ ∈ V := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ ∈ V, z φ ∈ V}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => V.add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => V.smul_mem c h }
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j => hV _
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

theorem isStable_const : IsStable (Submodule.span ℂ {oneFn E a}) := fun o φ hφ => by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  rw [map_smul]
  refine Submodule.smul_mem _ _ ?_
  cases o with
  | fin k => exact Submodule.mem_span_singleton_self _
  | cpt k => exact Submodule.mem_span_singleton_self _
  | lie X => exact (lie_oneFn X).symm ▸ Submodule.zero_mem _

theorem isAutForm_const {φ : Sm E a} (hφ : φ ∈ Submodule.span ℂ {oneFn E a}) : IsAutForm φ := by
  obtain ⟨c, e⟩ := Submodule.mem_span_singleton.1 hφ
  refine ⟨fun _ _ => e ▸ rfl, ?_, ?_, ?_, fun g => ⟨‖c‖, 0, fun y => ?_⟩⟩
  · have : {k | finRep E a k φ = φ} = Set.univ := Set.eq_univ_of_forall fun k => e ▸ rfl
    rw [this]; exact isOpen_univ
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {oneFn E a}) (Submodule.span_le.2 ?_)
    rintro _ ⟨k, rfl⟩
    exact isStable_const (.cpt k) φ hφ
  · refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {oneFn E a}) (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    exact Zalg_stable (fun X => isStable_const (.lie X)) hz φ hφ
  · rw [← e]
    change ‖c * 1‖ ≤ _
    simp

variable (E) in

def CuspSub.triv (ha : a ≤ 1) : CuspSub E a where
  V := Submodule.span ℂ {oneFn E a}
  cusp φ hφ := ⟨isAutForm_const hφ, fun r h0 h1 => by omega⟩
  stable := isStable_const
  ne_bot h := oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 h)
  irred W hW _ := ((nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW)

end UpperTheory.V.TR
