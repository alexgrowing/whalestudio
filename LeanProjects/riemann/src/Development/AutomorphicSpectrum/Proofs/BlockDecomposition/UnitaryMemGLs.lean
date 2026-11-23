import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ConjSingleApply

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate

namespace GlobalTheory.CompanionTheory.RCalc

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

section Gen

variable {E F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_comp_clm {h : E → F} (A : E →L[ℝ] E) {g : E} (hd : DifferentiableAt ℝ h (A g)) (v : E) :
    fderiv ℝ (fun y => h (A y)) g v = fderiv ℝ h (A g) (A v) := by
  have := (hd.hasFDerivAt.comp g A.hasFDerivAt).fderiv
  have e : (fun y => h (A y)) = h ∘ A := rfl
  rw [e, this]; rfl

end Gen

theorem fderiv_post {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {h : E → F} (L : F →L[ℂ] F) {g : E} (hd : DifferentiableAt ℝ h g) (v : E) :
    fderiv ℝ (fun y => L (h y)) g v = L (fderiv ℝ h g v) := by
  have := ((L.restrictScalars ℝ).hasFDerivAt.comp g hd.hasFDerivAt).fderiv
  have e : (fun y => L (h y)) = (L.restrictScalars ℝ) ∘ h := rfl
  rw [e, this]; rfl

variable (n V) in

def Sm : Submodule ℂ (Mat n → V) where
  carrier := {f | ContDiffOn ℝ ∞ f (GLs n) ∧ ∀ g, g ∉ GLs n → f g = 0}
  add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun g hg => by simp [ha.2 g hg, hb.2 g hg]⟩
  zero_mem' := ⟨contDiffOn_const, fun _ _ => rfl⟩
  smul_mem' := fun c f hf => ⟨hf.1.const_smul c, fun g hg => by simp [hf.2 g hg]⟩

def res {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : Sm n V :=
  ⟨(GLs n).indicator f, hf.congr fun _ hg => Set.indicator_of_mem hg f, fun _ hg => Set.indicator_of_notMem hg f⟩

theorem res_apply {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    (res hf).1 g = f g := Set.indicator_of_mem hg f

theorem Sm_ext {h h' : Sm n V} (e : Set.EqOn h.1 h'.1 (GLs n)) : h = h' := by
  apply Subtype.ext
  funext g
  by_cases hg : g ∈ GLs n
  · exact e hg
  · rw [h.2.2 g hg, h'.2.2 g hg]

def Dmf (X : Mat n) (h : Sm n V) : Sm n V := res (Rd_contDiffOn X h.2.1)

theorem Dmf_apply (X : Mat n) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (Dmf X h).1 g = Rd X h.1 g :=
  res_apply (Rd_contDiffOn X h.2.1) hg

def Dm (X : Mat n) : Module.End ℂ (Sm n V) where
  toFun h := Dmf X h
  map_add' a b := Sm_ext fun g hg => by
    show (Dmf X (a + b)).1 g = (Dmf X a).1 g + (Dmf X b).1 g
    rw [Dmf_apply _ _ hg, Dmf_apply _ _ hg, Dmf_apply _ _ hg]
    exact Rd_add X a.2.1 b.2.1 hg
  map_smul' c a := Sm_ext fun g hg => by
    show (Dmf X (c • a)).1 g = c • (Dmf X a).1 g
    rw [Dmf_apply _ _ hg, Dmf_apply _ _ hg]
    exact Rd_smul c X a.2.1 hg

theorem Dm_apply (X : Mat n) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (Dm X h).1 g = Rd X h.1 g :=
  Dmf_apply X h hg

variable (n V) in

def DA : Mat n →+ Module.End ℂ (Sm n V) where
  toFun := Dm
  map_zero' := by
    ext h : 1
    refine Sm_ext fun g hg => ?_
    rw [Dm_apply _ _ hg]
    simp [Rd]
  map_add' X Y := by
    ext h : 1
    refine Sm_ext fun g hg => ?_
    show (Dm (X + Y) h).1 g = (Dm X h).1 g + (Dm Y h).1 g
    rw [Dm_apply _ _ hg, Dm_apply _ _ hg, Dm_apply _ _ hg, Rd_add_left]
    rfl

theorem DA_apply (X : Mat n) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (DA n V X h).1 g = Rd X h.1 g :=
  Dmf_apply X h hg

theorem DA_bracket (X Y : Mat n) : DA n V X * DA n V Y - DA n V Y * DA n V X = DA n V (X * Y - Y * X) := by
  ext h : 1
  refine Sm_ext fun g hg => ?_
  show (DA n V X (DA n V Y h)).1 g - (DA n V Y (DA n V X h)).1 g = (DA n V (X * Y - Y * X) h).1 g
  rw [DA_apply _ _ hg, DA_apply _ _ hg, DA_apply _ _ hg, Rd_congr X (fun _ hy => DA_apply Y h hy) hg,
    Rd_congr Y (fun _ hy => DA_apply X h hy) hg]
  exact Rd_bracket X Y h.2.1 hg

theorem DA_smul (r : ℝ) (X : Mat n) : DA n V ((r : ℂ) • X) = (r : ℂ) • DA n V X := by
  ext h : 1
  refine Sm_ext fun g hg => ?_
  show (DA n V ((r : ℂ) • X) h).1 g = (r : ℂ) • (DA n V X h).1 g
  rw [DA_apply _ _ hg, DA_apply _ _ hg]
  have e : (r : ℂ) • X = r • X := by ext; simp
  rw [e, Rd_smul_left]
  simp

theorem Eu_congr (s : Bool) (a b : Fin n) {f h : Mat n → V} (e : Set.EqOn f h (GLs n)) :
    Set.EqOn (Eu s a b f) (Eu s a b h) (GLs n) := by
  intro g hg
  simp only [Eu, Pi.smul_apply, Pi.add_apply]
  rw [Rd_congr _ e hg, Rd_congr _ e hg]

theorem Tc_apply (s : Bool) (a b : Fin n) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (Tc (DA n V) s a b h).1 g = Eu s a b h.1 g := by
  have e : (Complex.I • Matrix.single a b (1 : ℂ) : Mat n) = Matrix.single a b Complex.I := by
    simp [Matrix.smul_single]
  show ((1 / 2 : ℂ) • (DA n V (Matrix.single a b 1) h + eps s • DA n V (Complex.I • Matrix.single a b 1) h)).1 g = _
  rw [e]
  show (1 / 2 : ℂ) • ((DA n V (Matrix.single a b 1) h).1 g + eps s • (DA n V (Matrix.single a b Complex.I) h).1 g) = _
  rw [DA_apply _ _ hg, DA_apply _ _ hg]
  rfl

def Gl (n : ℕ) (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (s : Bool) (m : ℕ) : Module.End ℂ (Sm n V) :=
  ∑ c, Pw (Tc (DA n V) s) m c c

theorem Epow_eq (s : Bool) (m : ℕ) (a b : Fin n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (Epow s m a b f) (Pw (Tc (DA n V) s) m a b (res hf)).1 (GLs n) := by
  induction m generalizing a b with
  | zero =>
    intro g hg
    by_cases h : a = b
    · simp [Epow, Pw, h, res_apply hf hg]
    · simp [Epow, Pw, h]
  | succ m ih =>
    intro g hg
    have e : (Pw (Tc (DA n V) s) (m + 1) a b (res hf)).1 g =
        ∑ c, (Tc (DA n V) s a c (Pw (Tc (DA n V) s) m c b (res hf))).1 g := by
      simp [Pw, LinearMap.sum_apply, Finset.sum_apply]
    rw [e]
    simp only [Epow, Finset.sum_apply]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [Tc_apply _ _ _ _ hg]
    exact Eu_congr s a c (ih c b) hg

theorem gel_eq (s : Bool) (m : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    Set.EqOn (gel s m f) (Gl n V s m (res hf)).1 (GLs n) := by
  intro g hg
  have e : (Gl n V s m (res hf)).1 g = ∑ c, (Pw (Tc (DA n V) s) m c c (res hf)).1 g := by
    simp [Gl, LinearMap.sum_apply, Finset.sum_apply]
  rw [e]
  simp only [gel, Finset.sum_apply]
  exact Finset.sum_congr rfl fun c _ => Epow_eq s m c c hf hg

theorem mul_mem_GLs {x g : Mat n} (hx : x ∈ GLs n) (hg : g ∈ GLs n) : x * g ∈ GLs n := by
  simp only [GLs, Set.mem_setOf_eq, Matrix.det_mul] at *
  exact mul_ne_zero hx hg

def preF (φ : Mat n →L[ℝ] Mat n) (hφ : Set.MapsTo φ (GLs n) (GLs n)) (h : Sm n V) : Sm n V :=
  res (h.2.1.comp φ.contDiff.contDiffOn hφ)

theorem preF_apply (φ : Mat n →L[ℝ] Mat n) (hφ : Set.MapsTo φ (GLs n) (GLs n)) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (preF φ hφ h).1 g = h.1 (φ g) :=
  res_apply (h.2.1.comp φ.contDiff.contDiffOn hφ) hg

def preE (φ : Mat n →L[ℝ] Mat n) (hφ : Set.MapsTo φ (GLs n) (GLs n)) : Module.End ℂ (Sm n V) where
  toFun h := preF φ hφ h
  map_add' a b := Sm_ext fun g hg => by
    show (preF φ hφ (a + b)).1 g = (preF φ hφ a).1 g + (preF φ hφ b).1 g
    rw [preF_apply _ _ _ hg, preF_apply _ _ _ hg, preF_apply _ _ _ hg]
    rfl
  map_smul' c a := Sm_ext fun g hg => by
    show (preF φ hφ (c • a)).1 g = c • (preF φ hφ a).1 g
    rw [preF_apply _ _ _ hg, preF_apply _ _ _ hg]
    rfl

theorem preE_apply (φ : Mat n →L[ℝ] Mat n) (hφ : Set.MapsTo φ (GLs n) (GLs n)) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) :
    (preE φ hφ h).1 g = h.1 (φ g) :=
  preF_apply φ hφ h hg

def postF (L : V →L[ℂ] V) (h : Sm n V) : Sm n V :=
  res ((L.restrictScalars ℝ).contDiff.comp_contDiffOn h.2.1)

theorem postF_apply (L : V →L[ℂ] V) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (postF L h).1 g = L (h.1 g) :=
  res_apply ((L.restrictScalars ℝ).contDiff.comp_contDiffOn h.2.1) hg

def postE (L : V →L[ℂ] V) : Module.End ℂ (Sm n V) where
  toFun h := postF L h
  map_add' a b := Sm_ext fun g hg => by
    show (postF L (a + b)).1 g = (postF L a).1 g + (postF L b).1 g
    rw [postF_apply _ _ hg, postF_apply _ _ hg, postF_apply _ _ hg]
    exact map_add L _ _
  map_smul' c a := Sm_ext fun g hg => by
    show (postF L (c • a)).1 g = c • (postF L a).1 g
    rw [postF_apply _ _ hg, postF_apply _ _ hg]
    exact map_smul L c _

theorem postE_apply (L : V →L[ℂ] V) (h : Sm n V) {g : Mat n} (hg : g ∈ GLs n) : (postE L h).1 g = L (h.1 g) :=
  postF_apply L h hg

theorem Gl_commute {u : Module.End ℂ (Sm n V)} (h : ∀ X, Commute u (DA n V X)) (s : Bool) (m : ℕ) :
    Commute u (Gl n V s m) := by
  refine Commute.sum_right _ _ _ fun c _ => Pw_commute (fun a b => ?_) m c c
  simp only [Tc, TX]
  exact ((h _).add_right ((h _).smul_right _)).smul_right _

theorem DA_Gl_commute (X : Mat n) (s : Bool) (m : ℕ) : Commute (DA n V X) (Gl n V s m) :=
  D_commute_trPw DA_bracket (fun r X => DA_smul r X) s m X

theorem gel_contDiffOn (s : Bool) (m : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (gel s m f) (GLs n) :=
  (Gl n V s m (res hf)).2.1.congr (gel_eq s m hf)

theorem Rd_gel (X : Mat n) (s : Bool) (m : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    Rd X (gel s m f) g = gel s m (Rd X f) g := by
  have e : res (Rd_contDiffOn X hf) = DA n V X (res hf) := Sm_ext fun y hy => by
    rw [res_apply _ hy, DA_apply _ _ hy]
    exact (Rd_congr X (fun _ h => res_apply hf h) hy).symm
  rw [Rd_congr X (gel_eq s m hf) hg, gel_eq s m (Rd_contDiffOn X hf) hg, e, ← DA_apply _ _ hg]
  have := LinearMap.congr_fun (DA_Gl_commute (V := V) X s m).eq (res hf)
  exact congrArg (fun h : Sm n V => h.1 g) this

theorem gel_pre (φ : Mat n →L[ℝ] Mat n) (hφ : Set.MapsTo φ (GLs n) (GLs n)) (s : Bool) (m : ℕ)
    (hc : Commute (preE (V := V) φ hφ) (Gl n V s m)) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : gel s m (fun y => f (φ y)) g = gel s m f (φ g) := by
  have hf' : ContDiffOn ℝ ∞ (fun y => f (φ y)) (GLs n) := hf.comp φ.contDiff.contDiffOn hφ
  have e : res hf' = preE φ hφ (res hf) := Sm_ext fun y hy => by
    rw [res_apply _ hy, preE_apply _ _ _ hy, res_apply hf (hφ hy)]
  rw [gel_eq s m hf' hg, gel_eq s m hf (hφ hg), e, ← preE_apply φ hφ _ hg]
  have := LinearMap.congr_fun hc.eq (res hf)
  exact (congrArg (fun h : Sm n V => h.1 g) this).symm

theorem gel_post (L : V →L[ℂ] V) (s : Bool) (m : ℕ) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) {g : Mat n}
    (hg : g ∈ GLs n) : gel s m (fun y => L (f y)) g = L (gel s m f g) := by
  have hf' : ContDiffOn ℝ ∞ (fun y => L (f y)) (GLs n) := (L.restrictScalars ℝ).contDiff.comp_contDiffOn hf
  have e : res hf' = postE L (res hf) := Sm_ext fun y hy => by
    rw [res_apply _ hy, postE_apply _ _ hy, res_apply hf hy]
  have hc : Commute (postE (n := n) L) (Gl n V s m) := Gl_commute (fun X => by
    ext h : 1
    refine Sm_ext fun y hy => ?_
    show (postE L (DA n V X h)).1 y = (DA n V X (postE L h)).1 y
    rw [postE_apply _ _ hy, DA_apply _ _ hy, DA_apply _ _ hy, Rd_congr X (fun _ h' => postE_apply L h h') hy]
    exact (fderiv_post L (differentiableAt_of_smooth h.2.1 hy) _).symm) s m
  rw [gel_eq s m hf' hg, gel_eq s m hf hg, e, ← postE_apply L _ hg]
  have := LinearMap.congr_fun hc.eq (res hf)
  exact (congrArg (fun h : Sm n V => h.1 g) this).symm

theorem mapsTo_mulL {x : Mat n} (hx : x ∈ GLs n) : Set.MapsTo (mulL x) (GLs n) (GLs n) := fun _ hg => mul_mem_GLs hx hg

theorem mapsTo_mulR {x : Mat n} (hx : x ∈ GLs n) : Set.MapsTo (mulR x) (GLs n) (GLs n) := fun _ hg => mul_mem_GLs hg hx

theorem gel_left (s : Bool) (m : ℕ) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : gel s m (fun y => f (x * y)) g = gel s m f (x * g) := by
  refine gel_pre (mulL x) (mapsTo_mulL hx) s m (Gl_commute (fun X => ?_) s m) hf hg
  ext h : 1
  refine Sm_ext fun y hy => ?_
  show (preE (mulL x) (mapsTo_mulL hx) (DA n V X h)).1 y = (DA n V X (preE (mulL x) (mapsTo_mulL hx) h)).1 y
  rw [preE_apply _ _ _ hy, DA_apply _ _ (mapsTo_mulL hx hy), DA_apply _ _ hy,
    Rd_congr X (fun _ h' => preE_apply (mulL x) (mapsTo_mulL hx) h h') hy]
  have := fderiv_comp_clm (mulL x) (differentiableAt_of_smooth h.2.1 (mapsTo_mulL hx hy)) (y * X)
  refine Eq.trans ?_ this.symm
  simp only [Rd, mulL_apply, mul_assoc]
  rfl

theorem gel_right (s : Bool) (m : ℕ) {x : Mat n} (hx : x ∈ GLs n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n))
    {g : Mat n} (hg : g ∈ GLs n) : gel s m (fun y => f (y * x)) g = gel s m f (g * x) := by
  have hu : IsUnit x.det := isUnit_iff_ne_zero.mpr hx
  have hyx : x⁻¹ * x = 1 := Matrix.nonsing_inv_mul x hu
  have hxy : x * x⁻¹ = 1 := Matrix.mul_nonsing_inv x hu
  refine gel_pre (mulR x) (mapsTo_mulR hx) s m ?_ hf hg
  refine Commute.symm (trPw_conj (fun r X => DA_smul r X) s m hyx fun X => ?_)
  ext h : 1
  refine Sm_ext fun y hy => ?_
  show (DA n V X (preE (mulR x) (mapsTo_mulR hx) h)).1 y = (preE (mulR x) (mapsTo_mulR hx) (DA n V (x⁻¹ * X * x) h)).1 y
  rw [preE_apply _ _ _ hy, DA_apply _ _ (mapsTo_mulR hx hy), DA_apply _ _ hy,
    Rd_congr X (fun _ h' => preE_apply (mulR x) (mapsTo_mulR hx) h h') hy]
  have := fderiv_comp_clm (mulR x) (differentiableAt_of_smooth h.2.1 (mapsTo_mulR hx hy)) (y * X)
  refine this.trans ?_
  have e : y * x * (x⁻¹ * X * x) = y * X * x := by
    calc y * x * (x⁻¹ * X * x) = y * (x * x⁻¹) * X * x := by simp only [mul_assoc]
      _ = y * X * x := by rw [hxy, mul_one]
  simp only [Rd, mulR_apply, e]
  rfl

theorem unitary_mem_GLs (k : Matrix.unitaryGroup (Fin n) ℂ) : k.1 ∈ GLs n := by
  have h : k.1 * star k.1 = 1 := (Matrix.mem_unitaryGroup_iff).mp k.2
  have := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_one] at this
  exact left_ne_zero_of_mul_eq_one this

theorem gel_mem_CE (E : KMod n) {f : Mat n → E.V} (hf : f ∈ CE E) (s : Bool) (m : ℕ) : gel s m f ∈ CE E := by
  refine ⟨gel_contDiffOn s m hf.1, fun g hg k => ?_⟩
  have hk := unitary_mem_GLs k
  rw [← gel_right s m hk hf.1 hg, ← gel_post (E.ρ k⁻¹) s m hf.1 hg]
  have h1 : ContDiffOn ℝ ∞ (fun y => f (y * k.1)) (GLs n) := hf.1.comp (mulR k.1).contDiff.contDiffOn (mapsTo_mulR hk)
  have h2 : ContDiffOn ℝ ∞ (fun y => E.ρ k⁻¹ (f y)) (GLs n) := ((E.ρ k⁻¹).restrictScalars ℝ).contDiff.comp_contDiffOn hf.1
  have e : res h1 = res h2 := Sm_ext fun y hy => by
    rw [res_apply _ hy, res_apply _ hy]
    exact hf.2 y hy k
  rw [gel_eq s m h1 hg, gel_eq s m h2 hg, e]

end GlobalTheory.CompanionTheory.RCalc
