import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.LFun GlobalTheory.CuspRep
open scoped ContDiff Classical

namespace GlobalTheory.CuspNF

variable (E : Type) [Field E] [NumberField E]

abbrev Cinf : Type := mixedEmbedding.mixedSpace E

abbrev Lie (a : ℕ) : Type := Fin a → Fin a → Cinf E

def infEq : Cinf E ≃+* InfiniteAdeleRing E := (InfiniteAdeleRing.ringEquiv_mixedSpace E).symm

def pInf : Ad E →+* Cinf E := (infEq E).symm.toRingHom.comp (RingHom.fst (InfiniteAdeleRing E) (Af E))

def sInf : Cinf E →ₙ+* Ad E where
  toFun x := ((infEq E x, 0) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext (map_mul (infEq E) x y) (mul_zero _).symm
  map_zero' := Prod.ext (map_zero (infEq E)) rfl
  map_add' x y := Prod.ext (map_add (infEq E) x y) (add_zero _).symm

def infGL (a : ℕ) : GL (Fin a) (Cinf E) →* GA E a := cornerGL a (sInf E)

def infId : (Cinf E)ˣ →* Ideles E := Units.map (corner (sInf E))

variable {E} {a : ℕ}

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

theorem infGL_mul_finGL (g : GA E a) :
    infGL E a (GeneralLinearGroup.map (pInf E) g) * finGL E a (GeneralLinearGroup.map (pFin E) g) = g :=
  ga_ext (by simp) (by simp)

theorem infGL_comm (y : GL (Fin a) (Cinf E)) (k : GL (Fin a) (Af E)) :
    infGL E a y * finGL E a k = finGL E a k * infGL E a y :=
  ga_ext (by simp) (by simp)

theorem det_infGL (y : GL (Fin a) (Cinf E)) :
    GeneralLinearGroup.det (infGL E a y) = infId E (GeneralLinearGroup.det y) := by
  refine Units.ext (ad_ext ?_ ?_)
  · rw [← CuspRep.det_map, pInf_infGL]
    change _ = pInf E (1 - sInf E 1 + sInf E _)
    have h : ∀ x, pInf E (sInf E x) = x := fun x => (infEq E).symm_apply_apply x
    simp [h]
  · rw [← CuspRep.det_map, pFin_infGL]
    change _ = (1 : Af E) - 0 + 0
    simp

abbrev toL (x : Matrix (Fin a) (Fin a) (Cinf E)) : Lie E a := Matrix.of.symm x

def invSet (E : Type) [Field E] (a : ℕ) : Set (Lie E a) := {x | IsUnit (Matrix.of x)}

theorem contDiff_det : ContDiff ℝ ∞ fun x : Lie E a => (Matrix.of x).det := by
  simp only [Matrix.det_apply', Matrix.of_apply]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => ?_)
  exact (contDiff_apply ℝ _ i).comp (contDiff_apply ℝ _ (σ i))

theorem isOpen_invSet : IsOpen (invSet E a) := by
  have : invSet E a = (fun x : Lie E a => (Matrix.of x).det) ⁻¹' {u | IsUnit u} := by
    ext x; exact Matrix.isUnit_iff_isUnit_det _
  rw [this]
  exact Units.isOpen.preimage contDiff_det.continuous

theorem val_mem_invSet (y : GL (Fin a) (Cinf E)) : (toL y.val) ∈ invSet E a := y.isUnit

open Classical in

def chart (φ : GA E a → ℂ) (g : GA E a) (x : Lie E a) : ℂ :=
  if h : IsUnit (Matrix.of x) then φ (g * infGL E a h.unit) else 0

theorem chart_val (φ : GA E a → ℂ) (g : GA E a) (y : GL (Fin a) (Cinf E)) :
    chart φ g (toL y.val) = φ (g * infGL E a y) := by
  have h : IsUnit (Matrix.of (toL y.val)) := y.isUnit
  have e : h.unit = y := Units.ext h.unit_spec
  rw [chart, dif_pos h, e]

def lmul (y : Lie E a) : Lie E a →L[ℝ] Lie E a :=
  LinearMap.toContinuousLinearMap (LinearMap.mulLeft ℝ (Matrix.of y) : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] _)

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

open Classical in

def atEmb (τ : E →+* ℂ) (z : ℂ) : Cinf E :=
  (fun w => if w.1 = InfinitePlace.mk τ then z.re else 0,
   fun w => if w.1 = InfinitePlace.mk τ then (if w.1.embedding = τ then z else starRingEnd ℂ z) else 0)

open Classical in

def idRe (τ : E →+* ℂ) : Cinf E := if ComplexEmbedding.IsReal τ then atEmb τ 1 else (1 / 2 : ℝ) • atEmb τ 1

open Classical in

def idIm (τ : E →+* ℂ) : Cinf E := if ComplexEmbedding.IsReal τ then 0 else (-1 / 2 : ℝ) • atEmb τ Complex.I

theorem id_idem (τ : E →+* ℂ) : idRe τ * idRe τ - idIm τ * idIm τ = idRe τ ∧ idRe τ * idIm τ + idIm τ * idRe τ = idIm τ := by
  classical
  unfold idRe idIm
  by_cases h : ComplexEmbedding.IsReal τ
  · have hr : (InfinitePlace.mk τ).IsReal := InfinitePlace.isReal_mk_iff.2 h
    simp only [if_pos h, mul_zero, zero_mul, sub_zero, add_zero, and_true]
    refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp only [atEmb, Prod.fst_mul, Pi.mul_apply]; split_ifs <;> simp
    · simp only [atEmb, Prod.snd_mul, Pi.mul_apply]; split_ifs <;> simp
  · have hw : ∀ w : {w : InfinitePlace E // w.IsReal}, w.1 ≠ InfinitePlace.mk τ := fun w e =>
      h (InfinitePlace.isReal_mk_iff.1 (e ▸ w.2))
    simp only [if_neg h]
    constructor <;> refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
    · simp [atEmb, hw w]
    · simp only [atEmb, Prod.snd_mul, Prod.snd_sub, Prod.smul_snd, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply]
      split_ifs <;> apply Complex.ext <;> simp <;> norm_num
    · simp [atEmb, hw w]
    · simp only [atEmb, Prod.snd_mul, Prod.snd_add, Prod.smul_snd, Pi.mul_apply, Pi.add_apply, Pi.smul_apply]
      split_ifs <;> apply Complex.ext <;> simp <;> norm_num

variable (E a) in

def lieS (i j : Fin a) : Cinf E →ₗ[ℝ] Module.End ℂ (Sm E a) :=
  (lie E a).comp (Matrix.singleLinearMap ℝ i j : Cinf E →ₗ[ℝ] Matrix (Fin a) (Fin a) (Cinf E))

theorem lieS_apply (i j : Fin a) (x : Cinf E) : lieS E a i j x = lie E a (toL (Matrix.single i j x)) := rfl

theorem lieS_comm (i j k l : Fin a) (x y : Cinf E) :
    lieS E a i j x * lieS E a k l y - lieS E a k l y * lieS E a i j x =
      (if j = k then lieS E a i l (x * y) else 0) - (if l = i then lieS E a k j (x * y) else 0) := by
  simp only [lieS_apply]
  rw [lie_comm]
  congr 1
  · split_ifs with h
    · subst h; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)
  · split_ifs with h
    · subst h; rw [mul_comm x]; exact congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_same _ _ _ _ _)
    · exact (congrArg (fun X => lie E a (toL X)) (Matrix.single_mul_single_of_ne _ _ _ _ h _)).trans (map_zero _)

def Eop (τ : E →+* ℂ) (i j : Fin a) : Module.End ℂ (Sm E a) :=
  lieS E a i j (idRe τ) + Complex.I • lieS E a i j (idIm τ)

theorem glRel_Eop (τ : E →+* ℂ) : Formalism.REAL.GlRel (Eop (a := a) τ) := by
  intro i j k l
  have h1 := lieS_comm i j k l (idRe τ) (idRe τ)
  have h2 := lieS_comm i j k l (idRe τ) (idIm τ)
  have h3 := lieS_comm i j k l (idIm τ) (idRe τ)
  have h4 := lieS_comm i j k l (idIm τ) (idIm τ)
  have e : ∀ p q : Fin a, Eop τ p q = lieS E a p q (idRe τ * idRe τ) - lieS E a p q (idIm τ * idIm τ) +
      Complex.I • (lieS E a p q (idRe τ * idIm τ) + lieS E a p q (idIm τ * idRe τ)) := fun p q => by
    rw [← map_sub, ← map_add, (id_idem τ).1, (id_idem τ).2, Eop]
  rw [e i l, e k j]
  simp only [Eop, smul_mul_assoc, mul_smul_comm, add_mul, mul_add, smul_add, smul_smul]
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  split_ifs at h1 h2 h3 h4 ⊢ <;>
    linear_combination (norm := skip) (exp := 1) h1 + (Complex.I : ℂ) • h2 + (Complex.I : ℂ) • h3 - h4 <;>
    match_scalars <;> ring_nf <;> simp

def cap (τ : E →+* ℂ) (u : ℂ) : Module.End ℂ (Sm E a) := Formalism.REAL.qdet (Eop τ) (u + ((a : ℂ) - 1) / 2)

theorem cap_comm (τ : E →+* ℂ) (u : ℂ) (i j : Fin a) : cap τ u * Eop τ i j = Eop τ i j * cap τ u :=
  Formalism.REAL.qDetCentral _ a _ (glRel_Eop τ) _ i j

theorem cap_highest (τ : E →+* ℂ) (ν : Fin a → ℂ) (φ : Sm E a) (h : Formalism.REAL.IsHW (Eop τ) ν φ) (u : ℂ) :
    cap τ u φ = (∏ k : Fin a, (u + (ν k + (((a : ℂ) - 1) / 2 - (k : ℕ))))) • φ := by
  rw [cap, Formalism.REAL.qDetHW _ a _ ν φ (glRel_Eop τ) h]
  congr 1
  exact Finset.prod_congr rfl fun k _ => by ring

variable (E a) in

def Zalg : Subalgebra ℂ (Module.End ℂ (Sm E a)) := Algebra.adjoin ℂ {z | ∃ τ u, z = cap τ u}

theorem Zalg_stable {V : Submodule ℂ (Sm E a)} (hV : ∀ X, ∀ φ ∈ V, lie E a X φ ∈ V) {z : Module.End ℂ (Sm E a)}
    (hz : z ∈ Zalg E a) : ∀ φ ∈ V, z φ ∈ V := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ ∈ V, z φ ∈ V}
      mul_mem' := fun hx hy φ h => hx _ (hy φ h)
      add_mem' := fun hx hy φ h => V.add_mem (hx φ h) (hy φ h)
      algebraMap_mem' := fun c φ h => V.smul_mem c h }
  have hE : ∀ τ i j, Eop τ i j ∈ S := fun τ i j =>
    S.add_mem (hV _) (S.smul_mem (hV _) _)
  refine (Algebra.adjoin_le (S := S) ?_) hz
  rintro _ ⟨τ, u, rfl⟩
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
  obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
  refine S.add_mem ?_ (hE _ _ _)
  split_ifs
  · exact S.algebraMap_mem _
  · exact S.zero_mem

abbrev Kinf (E : Type) [Field E] (a : ℕ) : Type := Matrix.unitaryGroup (Fin a) (Cinf E)

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

def height (y : GL (Fin a) (Cinf E)) : ℝ := 1 + ‖toL y.val‖ + ‖toL (y⁻¹).val‖

structure IsAutForm (φ : Sm E a) : Prop where
  left : ∀ γ g, φ.1 (ratGL E a γ * g) = φ.1 g
  level : IsOpen {k | finRep E a k φ = φ}
  kfin : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => cptRep E a k φ))
  zfin : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))
  growth : ∀ g, ∃ (C : ℝ) (N : ℕ), ∀ y, ‖φ.1 (g * infGL E a y)‖ ≤ C * height y ^ N

def IsCuspForm (φ : Sm E a) : Prop := IsAutForm φ ∧ IsCuspidal φ.1

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

variable (E a) in

instance setoid : Setoid (CuspSub E a) where
  r := Iso
  iseqv := ⟨fun π => ⟨.refl _ _, fun _ _ => rfl⟩,
    fun ⟨T, h⟩ => ⟨T.symm, fun o φ => T.injective (by rw [h]; simp)⟩,
    fun ⟨T, h⟩ ⟨T', h'⟩ => ⟨T.trans T', fun o φ => by simp [h, h']⟩⟩

def HasInfChar (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Multiset.card m = a ∧ ∀ u, ∀ φ ∈ π.V, cap τ u φ = (m.map (u + ·)).prod • φ

variable {π π'}

theorem HasInfChar.unique {τ : E →+* ℂ} {m m' : Multiset ℂ} (h : π.HasInfChar τ m) (h' : π.HasInfChar τ m') :
    m = m' := by
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  have e : (( m.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod =
      ((m'.map Neg.neg).map fun z => Polynomial.X - Polynomial.C z).prod := by
    refine Polynomial.funext fun u => ?_
    have := smul_left_injective ℂ h0 ((h.2 u φ hφ).symm.trans (h'.2 u φ hφ))
    simpa [Polynomial.eval_multiset_prod, Multiset.map_map] using this
  have e2 := congrArg Polynomial.roots e
  rw [Polynomial.roots_multiset_prod_X_sub_C, Polynomial.roots_multiset_prod_X_sub_C] at e2
  exact Multiset.map_injective neg_injective e2

theorem iso_cap (T : π.V ≃ₗ[ℂ] π'.V) (hT : ∀ o φ, T (π.op o φ) = π'.op o (T φ)) (τ : E →+* ℂ) (u : ℂ) (φ : π.V) :
    ∃ h : cap τ u φ.1 ∈ π.V, (T ⟨_, h⟩).1 = cap τ u (T φ).1 := by
  let S : Subalgebra ℂ (Module.End ℂ (Sm E a)) :=
    { carrier := {z | ∀ φ : π.V, ∃ h : z φ.1 ∈ π.V, (T ⟨_, h⟩).1 = z (T φ).1}
      mul_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hy φ
        obtain ⟨h2, e2⟩ := hx ⟨_, h1⟩
        exact ⟨h2, e2.trans (congrArg x e1)⟩
      add_mem' := fun {x y} hx hy φ => by
        obtain ⟨h1, e1⟩ := hx φ
        obtain ⟨h2, e2⟩ := hy φ
        exact ⟨add_mem h1 h2, (congrArg Subtype.val (map_add T ⟨_, h1⟩ ⟨_, h2⟩)).trans (congrArg₂ (· + ·) e1 e2)⟩
      algebraMap_mem' := fun c φ => ⟨π.V.smul_mem c φ.2, congrArg Subtype.val (map_smul T c φ)⟩ }
  have hL : ∀ X, lie E a X ∈ S := fun X φ => ⟨π.stable (.lie X) _ φ.2, congrArg Subtype.val (hT (.lie X) φ)⟩
  have hE : ∀ i j, Eop τ i j ∈ S := fun i j => S.add_mem (hL _) (S.smul_mem (hL _) _)
  have : cap τ u ∈ S := by
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨k, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact this φ

theorem Iso.hasInfChar (h : Iso π π') {τ : E →+* ℂ} {m : Multiset ℂ} (hm : π.HasInfChar τ m) : π'.HasInfChar τ m := by
  obtain ⟨T, hT⟩ := h
  refine ⟨hm.1, fun u φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := T.surjective ⟨φ, hφ⟩
  obtain ⟨h1, e⟩ := iso_cap T hT τ u ψ
  have e2 : (⟨_, h1⟩ : π.V) = (m.map (u + ·)).prod • ψ := Subtype.ext (hm.2 u _ ψ.2)
  rw [e2, map_smul, hψ] at e
  exact e.symm

variable (π) in

def finPart : Representation ℂ (GL (Fin a) (Af E)) π.V :=
  GlobalTheory.PRep.sub (finRep E a) π.V fun k => π.stable (.fin k)

variable (π) in

def locRep (w : HeightOneSpectrum (𝓞 E)) : Representation ℂ (GL (Fin a) (w.adicCompletion E)) π.V :=
  π.finPart.comp (locGL E a w)

theorem locRep_eq (w : HeightOneSpectrum (𝓞 E)) (g : GL (Fin a) (w.adicCompletion E)) :
    π.locRep w g = π.op (.fin (locGL E a w g)) := rfl

variable (π) in

theorem isSmooth_finPart : GlobalTheory.PRep.IsSmooth π.finPart := fun φ => by
  convert (π.cusp _ φ.2).1.level using 1
  ext k
  exact Subtype.ext_iff

variable (π) in

theorem isSmooth_locRep (w : HeightOneSpectrum (𝓞 E)) : GlobalTheory.PRep.IsSmooth (π.locRep w) := fun φ =>
  (π.isSmooth_finPart φ).preimage (GlobalTheory.CuspRep.CuspSub.continuous_locGL w)

variable (π) in

def IsLocComp (w : HeightOneSpectrum (𝓞 E)) (σ : SmIrr (GL (Fin a) (w.adicCompletion E))) : Prop :=
  ∃ f : σ.V →ₗ[ℂ] π.V, f ≠ 0 ∧ ∀ g v, f (σ.ρ g v) = π.locRep w g (f v)

theorem IsLocComp.congr {w : HeightOneSpectrum (𝓞 E)} {σ σ' : SmIrr (GL (Fin a) (w.adicCompletion E))}
    (h : π.IsLocComp w σ) (hπ : Iso π π') (hσ : Nonempty (σ.ρ.Equiv σ'.ρ)) : π'.IsLocComp w σ' := by
  obtain ⟨f, h0, hf⟩ := h
  obtain ⟨T, hT⟩ := hπ
  obtain ⟨e⟩ := hσ
  refine ⟨T.toLinearMap ∘ₗ f ∘ₗ e.symm.toLinearEquiv.toLinearMap, fun h => h0 (LinearMap.ext fun v => T.injective ?_),
    fun g v => ?_⟩
  · have := LinearMap.congr_fun h (e.toLinearEquiv v)
    rw [LinearMap.zero_apply, map_zero]
    exact (congrArg (fun x => T (f x)) (e.toLinearEquiv.symm_apply_apply v)).symm.trans this
  · have h1 : e.symm.toLinearEquiv (σ'.ρ g v) = σ.ρ g (e.symm.toLinearEquiv v) :=
      LinearMap.congr_fun (e.symm.isIntertwining' g) v
    change T (f (e.symm.toLinearEquiv (σ'.ρ g v))) = π'.locRep w g (T (f (e.symm.toLinearEquiv v)))
    rw [h1, hf, locRep_eq, hT, locRep_eq]

theorem Iso.hasSatGL (h : Iso π π') {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ}
    (hB : HasSatGL w (π.locRep w) B) : HasSatGL w (π'.locRep w) B := by
  obtain ⟨T, hT⟩ := h
  have hf : ∀ g y, T.toLinearMap (π.locRep w g y) = π'.locRep w g (T.toLinearMap y) := fun g y => hT (.fin _) y
  constructor
  · obtain ⟨x, hx⟩ := hB.exists_vec
    have h1 := hx.map T.toLinearMap hf ((map_ne_zero_iff T T.injective).2 hx.1)
    exact (Submodule.ne_bot_iff _).2 ⟨_, h1.2.1, h1.1⟩
  · intro y hy h0
    obtain ⟨x, rfl⟩ := T.surjective y
    refine (hB.2 x (GlobalTheory.LGrp.mem_fixed.2 fun k hk => T.injective ?_) fun e => h0 (by rw [e, map_zero])).map
      T.toLinearMap hf h0
    exact (hf k x).trans (GlobalTheory.LGrp.mem_fixed.1 hy k hk)

variable (π) in

def HasCentChar (η : HChar E) : Prop := GlobalTheory.SmGL.HasCentralChar π.finPart (η.1.comp (finId E))

theorem Iso.hasCentChar (h : Iso π π') {η : HChar E} (hη : π.HasCentChar η) : π'.HasCentChar η := by
  obtain ⟨T, hT⟩ := h
  intro z y
  obtain ⟨x, rfl⟩ := T.surjective y
  exact ((hT (.fin _) x).symm.trans (congrArg T (hη z x))).trans (map_smul T _ x)

variable (π) in

def fn : Submodule ℂ (GA E a → ℂ) := π.V.map (Sm E a).subtype

variable (π π') in

def IsTwist (χ : HChar E) : Prop :=
  ∀ ψ : GA E a → ℂ, ψ ∈ π'.fn ↔ ∃ φ ∈ π.fn, ψ = fun g => φ g * ((chiDet a χ g : ℂˣ) : ℂ)

variable (π) in

def HasFixed (U : Subgroup (GL (Fin a) (Af E))) : Prop := ∃ φ ∈ π.V, φ ≠ 0 ∧ ∀ k ∈ U, finRep E a k φ = φ

theorem Iso.hasFixed (h : Iso π π') {U : Subgroup (GL (Fin a) (Af E))} (hU : π.HasFixed U) : π'.HasFixed U := by
  obtain ⟨T, hT⟩ := h
  obtain ⟨φ, hφ, h0, hk⟩ := hU
  refine ⟨(T ⟨φ, hφ⟩).1, (T ⟨φ, hφ⟩).2, fun e => h0 ?_, fun k hk' => ?_⟩
  · exact congrArg Subtype.val ((map_eq_zero_iff T T.injective).1 (Subtype.ext e))
  · have h1 := congrArg Subtype.val (hT (.fin k) ⟨φ, hφ⟩)
    have h2 : π.op (.fin k) ⟨φ, hφ⟩ = ⟨φ, hφ⟩ := Subtype.ext (hk k hk')
    rw [h2] at h1
    exact h1.symm

end CuspSub

def barK (k : Kinf E a) : Kinf E a :=
  ⟨(star k.1)ᵀ, Matrix.mem_unitaryGroup_iff.2 (by
    have e : star ((star k.1)ᵀ) = k.1ᵀ := by
      ext i j : 1
      simp [Matrix.star_apply]
    have h' : k.1 * star k.1 = 1 := Matrix.mem_unitaryGroup_iff.1 k.2
    rw [e, ← Matrix.transpose_mul, h', Matrix.transpose_one])⟩

def Paired (π π' : CuspSub E a) (s : Op E a → Op E a) : Prop :=
  ∃ B : π.V →ₗ[ℂ] π'.V →ₗ[ℂ] ℂ, (∀ φ, (∀ ψ, B φ ψ = 0) → φ = 0) ∧ (∀ ψ, (∀ φ, B φ ψ = 0) → ψ = 0) ∧
    (∀ k φ ψ, B (π.op (.fin k) φ) (π'.op (s (.fin k)) ψ) = B φ ψ) ∧
    (∀ k φ ψ, B (π.op (.cpt k) φ) (π'.op (s (.cpt k)) ψ) = B φ ψ) ∧
    ∀ X φ ψ, B (π.op (.lie X) φ) ψ + B φ (π'.op (s (.lie X)) ψ) = 0

def IsConjAut (c : E ≃+* E) : Prop := ∀ (τ : E →+* ℂ) (x : E), τ (c x) = starRingEnd ℂ (τ x)

def conjOp (c : E ≃+* E) : Op E a → Op E a
  | .fin k => .fin (GeneralLinearGroup.map (conjFin c) k)
  | .cpt k => .cpt (barK k)
  | .lie X => .lie fun i j => star (X i j)

def DualIsConjBy (π : CuspSub E a) (c : E ≃+* E) (ψ : HChar E) : Prop :=
  ∃ π' : CuspSub E a, π.IsTwist π' ψ⁻¹ ∧ Paired π' π (conjOp c)

def chiInf (χ : HChar E) (x : Cinf E) : ℂ := if h : IsUnit x then ((χ.1 (infId E h.unit) : ℂˣ) : ℂ) else 0

def dchi (χ : HChar E) : Cinf E →L[ℝ] ℂ := fderiv ℝ (chiInf χ) 1

def expo (χ : HChar E) (τ : E →+* ℂ) : ℂ := dchi χ (idRe τ) + Complex.I * dchi χ (idIm τ)

variable (E) in

def Ohat : Subring (Af E) := ⨅ v : HeightOneSpectrum (𝓞 E), (v.adicCompletionIntegers E).toSubring.comap (pLoc E v)

variable (E a) in

def Kpr (M : ℕ) : Subgroup (GL (Fin a) (Af E)) :=
  (GeneralLinearGroup.map (n := Fin a) (Ideal.Quotient.mk (Ideal.span {(M : Ohat E)}))).ker.map
    (GeneralLinearGroup.map (Ohat E).subtype)

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

def opTriv : Op E a → ℂ
  | .fin _ => 1
  | .cpt _ => 1
  | .lie _ => 0

theorem act_oneFn (o : Op E a) : act o (oneFn E a) = opTriv o • oneFn E a := by
  cases o with
  | fin k => exact (one_smul _ _).symm
  | cpt k => exact (one_smul _ _).symm
  | lie X => exact (lie_oneFn X).trans (zero_smul _ _).symm

theorem isStable_const : IsStable (Submodule.span ℂ {oneFn E a}) := fun o φ hφ => by
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
  rw [map_smul, act_oneFn]
  exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))

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

theorem cap_oneFn (τ : E →+* ℂ) (u : ℂ) :
    cap τ u (oneFn E a) = (∏ k : Fin a, (u + (((a : ℂ) - 1) / 2 - (k : ℕ)))) • oneFn E a := by
  have h : ∀ i j, Eop τ i j (oneFn E a) = 0 := fun i j => by simp [Eop, lieS_apply, lie_oneFn]
  simpa using cap_highest τ 0 (oneFn E a) ⟨fun i => by simp [h], fun i j _ => h i j⟩ u

variable (E) in

def CuspSub.triv (ha : a ≤ 1) : CuspSub E a where
  V := Submodule.span ℂ {oneFn E a}
  cusp φ hφ := ⟨isAutForm_const hφ, fun r h0 h1 => by omega⟩
  stable := isStable_const
  ne_bot h := oneFn_ne_zero (Submodule.span_singleton_eq_bot.1 h)
  irred W hW _ := ((nonzero_span_atom _ oneFn_ne_zero).le_iff.1 hW)

variable (E a) in

def CG : Type := Quotient (CuspSub.setoid E a)

namespace CG

def mk (π : CuspSub E a) : CG E a := Quotient.mk _ π

def HasInfChar (π : CG E a) (τ : E →+* ℂ) (m : Multiset ℂ) : Prop :=
  Quotient.liftOn π (·.HasInfChar τ m) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasInfChar h, CuspSub.Iso.hasInfChar (Setoid.symm h)⟩

open Classical in

def infChar (π : CG E a) (τ : E →+* ℂ) : Multiset ℂ :=
  if h : ∃ m, π.HasInfChar τ m then h.choose else Multiset.replicate a 0

theorem HasInfChar.infChar_eq {π : CG E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) :
    π.infChar τ = m := by
  have h' : ∃ m, π.HasInfChar τ m := ⟨m, h⟩
  rw [infChar, dif_pos h']
  have h2 := h'.choose_spec
  generalize h'.choose = m' at h2
  induction π using Quotient.inductionOn
  exact CuspSub.HasInfChar.unique h2 h

theorem card_infChar (π : CG E a) (τ : E →+* ℂ) : Multiset.card (π.infChar τ) = a := by
  unfold infChar
  split_ifs with h
  · have h2 := h.choose_spec
    generalize h.choose = m' at h2
    induction π using Quotient.inductionOn
    exact h2.1
  · simp

def IsRegAlg (π : CG E a) : Prop :=
  ∀ τ, (π.infChar τ).Nodup ∧ ∀ z ∈ π.infChar τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2

def IsLoc (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (σ : Irr (GL (Fin a) (w.adicCompletion E))) : Prop :=
  Quotient.liftOn₂ π σ (fun π σ => π.IsLocComp w σ) fun _ _ _ _ h h' =>
    propext ⟨fun x => x.congr h h', fun x => x.congr (Setoid.symm h) (Setoid.symm h')⟩

def HasSat (π : CG E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) : Prop :=
  Quotient.liftOn π (fun π => HasSatGL w (π.locRep w) B) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasSatGL h, CuspSub.Iso.hasSatGL (Setoid.symm h)⟩

@[simp] theorem hasSat_mk (π : CuspSub E a) (w : HeightOneSpectrum (𝓞 E)) (B : Multiset ℂˣ) :
    (mk π).HasSat w B ↔ HasSatGL w (π.locRep w) B := Iff.rfl

theorem HasSat.unique {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B B' : Multiset ℂˣ} (h : π.HasSat w B)
    (h' : π.HasSat w B') : B = B' := by
  induction π using Quotient.inductionOn
  exact HasSatGL.unique h h'

theorem HasSat.card {π : CG E a} {w : HeightOneSpectrum (𝓞 E)} {B : Multiset ℂˣ} (h : π.HasSat w B) :
    B.card = a := by
  induction π using Quotient.inductionOn
  exact HasSatGL.card h

def HasCentChar (π : CG E a) (η : HChar E) : Prop :=
  Quotient.liftOn π (·.HasCentChar η) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasCentChar h, CuspSub.Iso.hasCentChar (Setoid.symm h)⟩

@[simp] theorem hasCentChar_mk (π : CuspSub E a) (η : HChar E) : (mk π).HasCentChar η ↔ π.HasCentChar η := Iff.rfl

def HasFixed (π : CG E a) (U : Subgroup (GL (Fin a) (Af E))) : Prop :=
  Quotient.liftOn π (·.HasFixed U) fun _ _ h =>
    propext ⟨CuspSub.Iso.hasFixed h, CuspSub.Iso.hasFixed (Setoid.symm h)⟩

@[simp] theorem hasFixed_mk (π : CuspSub E a) (U : Subgroup (GL (Fin a) (Af E))) :
    (mk π).HasFixed U ↔ π.HasFixed U := Iff.rfl

instance : Inhabited (CG E 1) := ⟨mk (CuspSub.triv E le_rfl)⟩

instance : Inhabited (CG E 0) := ⟨mk (CuspSub.triv E zero_le_one)⟩

theorem isRegAlg_triv : (mk (CuspSub.triv E (le_refl 1))).IsRegAlg := fun τ => by
  have h : (mk (CuspSub.triv E (le_refl 1))).HasInfChar τ {0} := ⟨rfl, fun u φ hφ => by
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hφ
    rw [map_smul, cap_oneFn, smul_comm]
    simp⟩
  rw [h.infChar_eq]
  exact ⟨by simp, fun z hz => ⟨0, by simpa using hz⟩⟩

end CG

end GlobalTheory.CuspNF
