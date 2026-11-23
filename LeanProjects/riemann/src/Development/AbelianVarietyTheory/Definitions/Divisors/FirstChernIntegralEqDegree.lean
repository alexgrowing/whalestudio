import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsTorsionFreeOfForallExists
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtFormAdjEqNegSecondForm

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open GlobalTheory.LB (resG_resG resG_self toMod)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (pullbackSections)
open scoped ContDiff ComplexOrder

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {σ σ' : k →+* ℂ}

namespace CxPts

variable {F G : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
  [NormedSpace ℝ G] {y : CxPts p σ} {f f' : CxPts p σ → F}

def VInfAt (f : CxPts p σ → F) (y : CxPts p σ) : Prop :=
  ∃ (W : X.Opens) (ι : Type) (_ : Fintype ι) (g : ι → Γ(X, W)) (Φ : (ι → ℂ) → F) (O : Set (ι → ℂ)),
    y ∈ ptsIn p σ W ∧ IsOpen O ∧ (fun a => ev p σ W (g a) y) ∈ O ∧ ContDiffOn ℝ ∞ Φ O ∧
      f =ᶠ[𝓝 y] fun z => Φ fun a => ev p σ W (g a) z

theorem vInfAt_iff_cInfAt {u : CxPts p σ → ℝ} : VInfAt u y ↔ CInfAt u y := Iff.rfl

theorem VInfAt.congr (h : VInfAt f y) (e : f' =ᶠ[𝓝 y] f) : VInfAt f' y :=
  have ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  ⟨W, ι, i, g, F, O, h₁, h₂, h₃, h₄, e.trans h₅⟩

theorem vInfAt_const (c : F) (y : CxPts p σ) : VInfAt (fun _ => c) y :=
  ⟨⊤, Empty, inferInstance, Empty.elim, fun _ => c, univ, mem_ptsIn_top, isOpen_univ, trivial,
    contDiffOn_const, EventuallyEq.rfl⟩

theorem vInfAt_ev {W : X.Opens} (g : Γ(X, W)) (hy : y ∈ ptsIn p σ W) : VInfAt (ev p σ W g) y :=
  ⟨W, Unit, inferInstance, fun _ => g, fun v => v (), univ, hy, isOpen_univ, trivial,
    (contDiff_apply _ _ _).contDiffOn, EventuallyEq.rfl⟩

theorem VInfAt.comp (h : VInfAt f y) {Ψ : F → G} {T : Set F} (hT : IsOpen T) (hy : f y ∈ T)
    (hΨ : ContDiffOn ℝ ∞ Ψ T) : VInfAt (fun z => Ψ (f z)) y := by
  obtain ⟨W, ι, _, g, Φ, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨W, ι, inferInstance, g, Ψ ∘ Φ, O ∩ Φ ⁻¹' T, h₁,
    h₄.continuousOn.isOpen_inter_preimage h₂ hT, ⟨h₃, ?_⟩,
    hΨ.comp (h₄.mono inter_subset_left) fun _ hv => hv.2, h₅.fun_comp Ψ⟩
  rw [mem_preimage, ← h₅.eq_of_nhds]
  exact hy

theorem VInfAt.comp_contDiff (h : VInfAt f y) {Ψ : F → G} (hΨ : ContDiff ℝ ∞ Ψ) :
    VInfAt (fun z => Ψ (f z)) y := h.comp isOpen_univ trivial hΨ.contDiffOn

theorem VInfAt.prodMk {f' : CxPts p σ → G} (h : VInfAt f y) (h' : VInfAt f' y) :
    VInfAt (fun z => (f z, f' z)) y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  obtain ⟨W', ι', _, g', F', O', h₁', h₂', h₃', h₄', h₅'⟩ := h'
  have hW := mem_ptsIn_inf.2 ⟨h₁, h₁'⟩
  have cl : ContDiff ℝ ∞ fun (v : ι ⊕ ι' → ℂ) a => v (.inl a) :=
    contDiff_pi.2 fun a => contDiff_apply _ _ _
  have cr : ContDiff ℝ ∞ fun (v : ι ⊕ ι' → ℂ) a => v (.inr a) :=
    contDiff_pi.2 fun a => contDiff_apply _ _ _
  refine ⟨W ⊓ W', ι ⊕ ι', inferInstance,
    Sum.elim (fun a => resG X inf_le_left (g a)) fun a => resG X inf_le_right (g' a),
    fun v => (F fun a => v (.inl a), F' fun a => v (.inr a)),
    (fun v a => v (.inl a)) ⁻¹' O ∩ (fun v a => v (.inr a)) ⁻¹' O', hW,
    (h₂.preimage cl.continuous).inter (h₂'.preimage cr.continuous), ⟨?_, ?_⟩,
    (h₄.comp cl.contDiffOn fun _ hv => hv.1).prodMk
      (h₄'.comp cr.contDiffOn fun _ hv => hv.2), ?_⟩
  · simpa only [mem_preimage, Sum.elim_inl, ev_res _ hW] using h₃
  · simpa only [mem_preimage, Sum.elim_inr, ev_res _ hW] using h₃'
  · filter_upwards [h₅, h₅', (isOpen_ptsIn _).mem_nhds hW] with z e e' hz
    simp only [Sum.elim_inl, Sum.elim_inr, ev_res _ hz, e, e']

theorem vInfAt_pi {ι : Type} [Fintype ι] {f : CxPts p σ → ι → F}
    (h : ∀ i, VInfAt (fun z => f z i) y) : VInfAt f y := by
  classical
  have H (s : Finset ι) : VInfAt (fun z => ∑ i ∈ s, (Pi.single i (f z i) : ι → F)) y := by
    induction s using Finset.induction_on with
    | empty => simpa using vInfAt_const (0 : ι → F) y
    | insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact ((h a).prodMk ih).comp_contDiff (Ψ := fun x => Pi.single a x.1 + x.2)
        (((ContinuousLinearMap.single ℝ (fun _ : ι => F) a).contDiff.comp contDiff_fst).add
          contDiff_snd)
  simpa only [Finset.univ_sum_single] using H Finset.univ

theorem VInfAt.continuousAt (h : VInfAt f y) : ContinuousAt f y := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ContinuousAt.congr ?_ h₅.symm
  exact ContinuousAt.comp (f := fun z a => ev p σ W (g a) z)
    (h₄.continuousOn.continuousAt (h₂.mem_nhds h₃)) (continuousAt_pi.2 fun a =>
      (continuousOn_ev (g a)).continuousAt ((isOpen_ptsIn W).mem_nhds h₁))

theorem VInfAt.pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) {z : CxPts q σ}
    (h : VInfAt f (PtsOver.map π hπ _ z)) : VInfAt (fun w => f (PtsOver.map π hπ _ w)) z := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  refine ⟨π ⁻¹ᵁ W, ι, inferInstance, fun a => π.app W (g a), F, O, h₁, h₂, ?_, h₄, ?_⟩
  · simpa only [ev_app π hπ] using h₃
  · simp only [ev_app π hπ]
    exact (PtsOver.continuous_map π hπ _).continuousAt.eventually h₅

theorem VInfAt.contDiffAt_chart (h : VInfAt f y) {D : ℕ} (c : AlgChart p σ D)
    (hy : y ∈ c.e.source) : ContDiffAt ℝ ∞ (fun v => f (c.e.symm v)) (c.e y) := by
  obtain ⟨W, ι, _, g, F, O, h₁, h₂, h₃, h₄, h₅⟩ := h
  have ho := ChartGlue.isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) W)
  have e := c.e.left_inv hy
  have hg : ContDiffAt ℝ ∞ (fun w a => ev p σ W (g a) (c.e.symm w)) (c.e y) :=
    contDiffAt_pi.2 fun a => (ChartGlue.contDiffOn_real ho (c.holo W (g a))).contDiffAt
      (ho.mem_nhds (ChartGlue.mem_over c.e hy h₁))
  have h₆ : ContDiffAt ℝ ∞ F (fun a => ev p σ W (g a) (c.e.symm (c.e y))) := by
    rw [e]; exact h₄.contDiffAt (h₂.mem_nhds h₃)
  refine (h₆.comp (c.e y) hg).congr_of_eventuallyEq ?_
  have := c.e.continuousAt_symm (c.e.map_source hy)
  rw [ContinuousAt, e] at this
  exact this.eventually h₅

theorem mem_ptsIn_iff_of_conj {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    {W : X.Opens} : y' ∈ ptsIn p σ' W ↔ y ∈ ptsIn p σ W := by
  have e : y'.1 (IsLocalRing.closedPoint ℂ) = y.1 (IsLocalRing.closedPoint ℂ) := by
    rw [h]
    exact congrArg y.1 (Subsingleton.elim (α := PrimeSpectrum ℂ) _ _)
  rw [mem_ptsIn, mem_ptsIn, e]

theorem ev_conj' {y : CxPts p σ} {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1)
    (W : X.Opens) (g : Γ(X, W)) : ev p σ' W g y' = star (ev p σ W g y) := by
  by_cases hy : y ∈ ptsIn p σ W
  · exact ev_conj h hy g
  · rw [ev_of_notMem hy, ev_of_notMem (mt (mem_ptsIn_iff_of_conj h).1 hy), star_zero]

end CxPts

namespace VB.Chart

variable {E : X.Modules} {r : ℕ} (c c' c'' : Chart E r) {V W : X.Opens} {y : CxPts p σ}

variable (p σ) in

def crd (s : Γ(E, V)) (y : CxPts p σ) : Fin r → ℂ := fun a =>
  ev p σ (V ⊓ c.U) ((c.isFrame.basis inf_le_right).repr (resM E inf_le_left s) a) y

variable (p σ) in

def tr (y : CxPts p σ) : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => c.crd p σ (c'.e b) y a

theorem crd_eq (s : Γ(E, V)) (h : W ≤ V) (h' : W ≤ c.U) (hy : y ∈ ptsIn p σ W) (a : Fin r) :
    c.crd p σ s y a = ev p σ W ((c.isFrame.basis h').repr (resM E h s) a) y := by
  rw [crd, ← ev_res (le_inf h h') hy, ← c.isFrame.repr_resM, resM_resM]

theorem crd_resM (s : Γ(E, V)) (h : W ≤ V) (hy : y ∈ ptsIn p σ W) :
    c.crd p σ (resM E h s) y = c.crd p σ s y := by
  funext a
  by_cases hc : y ∈ ptsIn p σ c.U
  · rw [c.crd_eq s (inf_le_left.trans h) inf_le_right (mem_ptsIn_inf.2 ⟨hy, hc⟩), crd, resM_resM]
  · rw [crd, crd, ev_of_notMem (fun h => hc (mem_ptsIn_inf.1 h).2),
      ev_of_notMem fun h => hc (mem_ptsIn_inf.1 h).2]

theorem crd_add (s t : Γ(E, V)) (y : CxPts p σ) :
    c.crd p σ (s + t) y = c.crd p σ s y + c.crd p σ t y := funext fun a => by
  simp only [crd, map_add, Finsupp.add_apply, ev_add, Pi.add_apply]

theorem crd_smul (g : Γ(X, V)) (s : Γ(E, V)) (y : CxPts p σ) :
    c.crd p σ (g • s) y = ev p σ V g y • c.crd p σ s y := funext fun a => by
  by_cases hy : y ∈ ptsIn p σ (V ⊓ c.U)
  · simp only [crd, resM_smul, map_smul, Finsupp.smul_apply, smul_eq_mul, ev_mul, Pi.smul_apply,
      ev_res _ hy]
  · simp only [crd, ev_of_notMem hy, Pi.smul_apply, smul_zero]

theorem crd_zero (y : CxPts p σ) : c.crd p σ (0 : Γ(E, V)) y = 0 := by
  have := c.crd_add (p := p) (σ := σ) (0 : Γ(E, V)) 0 y
  rw [add_zero] at this
  exact left_eq_add.1 this

theorem crd_sum {ι : Type*} (T : Finset ι) (s : ι → Γ(E, V)) (y : CxPts p σ) :
    c.crd p σ (∑ i ∈ T, s i) y = ∑ i ∈ T, c.crd p σ (s i) y :=
  map_sum (AddMonoidHom.mk' (fun s : Γ(E, V) => c.crd p σ s y) fun s t => c.crd_add s t y) s T

theorem crd_frame (hy : y ∈ ptsIn p σ c.U) (b : Fin r) : c.crd p σ (c.e b) y = Pi.single b 1 := by
  funext a
  rw [c.crd_eq _ le_rfl le_rfl hy, ← c.isFrame.basis_apply, Module.Basis.repr_self, ev_eq hy,
    Finsupp.single_apply, Pi.single_apply]
  simp only [eq_comm (a := a)]
  split_ifs <;> simp

theorem tr_mulVec (s : Γ(E, V)) (hy : y ∈ ptsIn p σ V) (h' : y ∈ ptsIn p σ c'.U) :
    c.tr p σ c' y *ᵥ c'.crd p σ s y = c.crd p σ s y := by
  have hW := mem_ptsIn_inf.2 ⟨hy, h'⟩
  rw [← c.crd_resM s inf_le_left hW, ← (c'.isFrame.basis inf_le_right).sum_repr (resM E _ s), crd_sum]
  funext a
  simp only [crd_smul, IsFrame.basis_apply, c.crd_resM _ _ hW, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, mulVec, dotProduct, tr, of_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem tr_mul (h' : y ∈ ptsIn p σ c'.U) (h'' : y ∈ ptsIn p σ c''.U) :
    c.tr p σ c' y * c'.tr p σ c'' y = c.tr p σ c'' y := by
  ext a b
  exact congrFun (c.tr_mulVec c' (c''.e b) h'' h') a

theorem tr_self (h : y ∈ ptsIn p σ c.U) : c.tr p σ c y = 1 := by
  ext a b
  rw [tr, of_apply, c.crd_frame h, Pi.single_apply, one_apply]

theorem isUnit_tr (h : y ∈ ptsIn p σ c.U) (h' : y ∈ ptsIn p σ c'.U) : IsUnit (c.tr p σ c' y) :=
  IsUnit.of_mul_eq_one _ ((c.tr_mul c' c h' h).trans (c.tr_self h))

theorem det_tr (h : y ∈ ptsIn p σ c.U) (h' : y ∈ ptsIn p σ c'.U) :
    (c.tr p σ c' y).det = gv p σ (det E r) c c' y := by
  have hW := mem_ptsIn_inf.2 ⟨h, h'⟩
  change _ = ev p σ (c.U ⊓ c'.U) (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val y
  rw [IsFrame.val_detUnit, Module.Basis.det_apply, ev_eq hW, RingHom.map_det]
  congr 1
  ext a b
  rw [tr, of_apply, c.crd_eq _ inf_le_right inf_le_left hW, ev_eq hW]
  rfl

theorem crd_conj {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (s : Γ(E, V)) :
    c.crd p σ' s y' = star (c.crd p σ s y) := funext fun _ => ev_conj' h _ _

theorem tr_conj {y' : CxPts p σ'} (h : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) :
    c.tr p σ' c' y' = (c.tr p σ c' y).map star := by
  ext a b
  exact congrFun (c.crd_conj h _) a

theorem vInfAt_crd (s : Γ(E, V)) (hy : y ∈ ptsIn p σ V) (h : y ∈ ptsIn p σ c.U) (a : Fin r) :
    VInfAt (fun z => c.crd p σ s z a) y := vInfAt_ev _ (mem_ptsIn_inf.2 ⟨hy, h⟩)

def pull (hE : IsVB E r) (π : Y ⟶ X) : Chart ((Scheme.Modules.pullback π).obj E) r :=
  have := hE.isQuasicoherent
  ⟨π ⁻¹ᵁ c.U, _, c.isFrame.pullback π⟩

theorem crd_pull (hE : IsVB E r) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (s : Γ(E, V))
    {T : Y.Opens} (hT : T ≤ π ⁻¹ᵁ V) {z : CxPts q σ} (hz : z ∈ ptsIn q σ T)
    (hc : z ∈ ptsIn q σ (π ⁻¹ᵁ c.U)) :
    (c.pull hE π).crd q σ (pullbackSections π E hT s) z = c.crd p σ s (PtsOver.map π hπ _ z) := by
  have := hE.isQuasicoherent
  funext a
  have hW := mem_ptsIn_inf.2 ⟨hz, hc⟩
  have hle : T ⊓ π ⁻¹ᵁ c.U ≤ π ⁻¹ᵁ (V ⊓ c.U) := inf_le_inf_right _ hT
  have e := c.isFrame.pullback_basis_repr π inf_le_right hle (resM E inf_le_left s) a
  rw [crd, crd, ← ev_app π hπ, ← ev_res hle hW]
  refine congrArg (ev q σ _ · z) (Eq.trans ?_ e)
  exact congrArg (fun t => ((c.isFrame.pullback π).basis inf_le_right).repr t a)
    ((QCoh.res_pullbackSections π E hT inf_le_left s).trans
      (QCoh.pullbackSections_res π E hle inf_le_left s).symm)

def dual : Chart (VB.dual E) r := ⟨c.U, _, c.isFrame.dual⟩

theorem tr_dual (h : y ∈ ptsIn p σ c.U) (h' : y ∈ ptsIn p σ c'.U) :
    c.dual.tr p σ c'.dual y = (c'.tr p σ c y)ᵀ := by
  have hW := mem_ptsIn_inf.2 ⟨h, h'⟩
  ext a b
  rw [tr, tr, transpose_apply, of_apply, of_apply, c'.crd_eq _ inf_le_left inf_le_right hW]
  exact (c.dual.crd_eq (c'.dual.e b) inf_le_right inf_le_left hW a).trans
    (congrArg (ev p σ _ · y) (c.isFrame.dual_basis_repr _ _ a))

def map {E' : X.Modules} (φ : E ≅ E') : Chart E' r := ⟨c.U, _, c.isFrame.map_iso φ.hom⟩

theorem crd_map {E' : X.Modules} (φ : E ≅ E') (s : Γ(E, V)) (y : CxPts p σ) :
    (c.map φ).crd p σ (φ.hom.app V s) y = c.crd p σ s y := by
  by_cases hy : y ∈ ptsIn p σ (V ⊓ c.U)
  · have h₁ := (mem_ptsIn_inf.1 hy).2
    rw [← c.crd_resM s inf_le_left hy, ← (c.map φ).crd_resM _ inf_le_left hy, ← app_resM,
      ← (c.isFrame.basis inf_le_right).sum_repr (resM E _ s)]
    simp only [map_sum, Scheme.Modules.Hom.app_smul, crd_sum, crd_smul, IsFrame.basis_apply,
      app_resM, crd_resM _ _ _ hy, c.crd_frame h₁]
    exact Finset.sum_congr rfl fun b _ => congrArg _ ((c.map φ).crd_frame h₁ b)
  · funext a
    exact (ev_of_notMem hy _).trans (ev_of_notMem hy _).symm

theorem tr_of_notMem (h' : y ∉ ptsIn p σ c'.U) : c.tr p σ c' y = 0 := by
  ext a b
  exact ev_of_notMem (fun h => h' (mem_ptsIn_inf.1 h).1) _

theorem tr_mul' (h' : y ∈ ptsIn p σ c'.U) : c.tr p σ c' y * c'.tr p σ c'' y = c.tr p σ c'' y := by
  by_cases h : y ∈ ptsIn p σ c''.U
  · exact c.tr_mul c' c'' h' h
  · rw [tr_of_notMem _ _ h, tr_of_notMem _ _ h, Matrix.mul_zero]

theorem tr_pull (hE : IsVB E r) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) {z : CxPts q σ}
    (h : PtsOver.map π hπ _ z ∈ ptsIn p σ c.U) (h' : PtsOver.map π hπ _ z ∈ ptsIn p σ c'.U) :
    (c.pull hE π).tr q σ (c'.pull hE π) z = c.tr p σ c' (PtsOver.map π hπ _ z) := by
  ext a b
  exact congrFun (c.crd_pull hE π hπ (c'.e b) le_rfl h' h) a

theorem tr_map {E' : X.Modules} (φ : E ≅ E') (y : CxPts p σ) :
    (c.map φ).tr p σ (c'.map φ) y = c.tr p σ c' y := by
  ext a b
  exact congrFun (c.crd_map φ (c'.e b) y) a

def ofLB {L : LB X} (hL : L.IsLB) (i : L.ι) : Chart (toMod L) 1 :=
  ⟨L.U i, _, isFrame_chartSec hL i⟩

theorem tr_ofLB {L : LB X} (hL : L.IsLB) {i j : L.ι} (hi : y ∈ ptsIn p σ (L.U i))
    (hj : y ∈ ptsIn p σ (L.U j)) (a b : Fin 1) :
    (ofLB hL i).tr p σ (ofLB hL j) y a b = gv p σ L i j y := by
  have hW := mem_ptsIn_inf.2 ⟨hi, hj⟩
  have e := (ofLB hL i).crd_resM (LB.chartSec hL j) inf_le_right hW
  have e' := (ofLB hL i).crd_resM (LB.chartSec hL i) inf_le_left hW
  rw [show resM (toMod L) inf_le_right (LB.chartSec hL j) = _ from
    LB.map_chartSec_change hL i j inf_le_left inf_le_right, crd_smul, e', resG_self] at e
  refine (congrFun e a).symm.trans ?_
  have := congrFun ((ofLB hL i).crd_frame hi a) a
  rw [Pi.single_eq_same] at this
  exact (congrArg (_ * ·) this).trans (mul_one _)

end VB.Chart

namespace HermFrame

variable {m n l : Type} [Fintype m] [Fintype n] [Fintype l]

def chg (A : Matrix n m ℂ) (H : Matrix n n ℂ) : Matrix m m ℂ := Aᵀ * H * Aᴴᵀ

theorem form_chg (A : Matrix n m ℂ) (H : Matrix n n ℂ) (u w : m → ℂ) :
    form (chg A H) u w = form H (A *ᵥ u) (A *ᵥ w) := (form_mulVec H A A u w).symm

theorem chg_apply (A : Matrix n m ℂ) (H : Matrix n n ℂ) (a b : m) :
    chg A H a b = form H (fun i => A i a) fun i => A i b := by
  classical
  rw [← form_single (chg A H), form_chg, mulVec_single_one, mulVec_single_one]
  rfl

theorem chg_chg (A : Matrix n m ℂ) (B : Matrix m l ℂ) (H : Matrix n n ℂ) :
    chg B (chg A H) = chg (A * B) H := by
  simp only [chg, transpose_mul, conjTranspose_mul, Matrix.mul_assoc]

@[simp] theorem chg_one [DecidableEq n] (H : Matrix n n ℂ) : chg 1 H = H := by simp [chg]

@[simp] theorem chg_zero (H : Matrix n n ℂ) : chg (0 : Matrix n m ℂ) H = 0 := by simp [chg]

theorem chg_smul (A : Matrix n m ℂ) (t : ℂ) (H : Matrix n n ℂ) : chg A (t • H) = t • chg A H := by
  simp [chg]

theorem chg_map_star (A : Matrix n m ℂ) (H : Matrix n n ℂ) :
    chg (A.map star) (H.map star) = (chg A H).map star := by
  ext a b
  simp [chg_apply, form_eq_sum]

theorem posDef_chg [DecidableEq n] {A H : Matrix n n ℂ} (hA : IsUnit A) (h : H.PosDef) :
    (chg A H).PosDef := by
  refine posDef_iff.2 ⟨?_, fun v hv => ?_⟩
  · have := isHermitian_mul_mul_conjTranspose Aᵀ h.isHermitian
    rwa [show Aᵀᴴ = Aᴴᵀ from rfl] at this
  · rw [form_chg]
    exact (posDef_iff.1 h).2 _ fun e => hv (mulVec_injective_iff_isUnit.2 hA (e.trans (mulVec_zero A).symm))

theorem det_chg [DecidableEq n] (A H : Matrix n n ℂ) :
    (chg A H).det = (‖A.det‖ ^ 2 : ℝ) * H.det := by
  rw [chg, det_mul, det_mul, det_transpose, det_transpose, det_conjTranspose, mul_right_comm,
    Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem dualGram_chg [DecidableEq n] {A B : Matrix n n ℂ} (h : A * B = 1) (H : Matrix n n ℂ) :
    dualGram (chg A H) = chg Bᵀ (dualGram H) := by
  have e₁ : Aᵀ⁻¹ = Bᵀ := inv_eq_left_inv (by rw [← transpose_mul, h, transpose_one])
  have e₂ : Aᴴᵀ⁻¹ = Bᴴᵀ := inv_eq_right_inv (by
    rw [← transpose_mul, ← conjTranspose_mul, h, conjTranspose_one, transpose_one])
  simp only [dualGram, chg, Matrix.mul_inv_rev, e₁, e₂, transpose_mul, transpose_transpose,
    Matrix.mul_assoc]
  rfl

theorem posDef_dualGram [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) : (dualGram H).PosDef :=
  h.inv.transpose

theorem dualGram_map_star [DecidableEq n] (H : Matrix n n ℂ) :
    dualGram (H.map star) = (dualGram H).map star :=
  congrArg transpose (show Hᵀᴴ⁻¹ = H⁻¹ᵀᴴ by rw [← conjTranspose_nonsing_inv, transpose_nonsing_inv])

theorem det_re_pos [DecidableEq n] {H : Matrix n n ℂ} (h : H.PosDef) : 0 < H.det.re :=
  (Complex.pos_iff.1 h.det_pos).1

end HermFrame

namespace CxPts

variable {m n l : Type} {y : CxPts p σ}

def MInfAt (A : CxPts p σ → Matrix m n ℂ) (y : CxPts p σ) : Prop :=
  ∀ a b, VInfAt (fun z => A z a b) y

variable {A A' : CxPts p σ → Matrix m n ℂ}

theorem MInfAt.congr (h : MInfAt A y) (e : A' =ᶠ[𝓝 y] A) : MInfAt A' y := fun a b =>
  (h a b).congr (e.fun_comp fun M => M a b)

theorem MInfAt.mContDiffAt (h : MInfAt A y) {D : ℕ} (c : AlgChart p σ D) (hy : y ∈ c.e.source) :
    MContDiffAt ∞ (fun v => A (c.e.symm v)) (c.e y) := fun a b => (h a b).contDiffAt_chart c hy

variable [Fintype m] [Fintype n]

theorem MInfAt.comp (h : MInfAt A y) {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {Ψ : (m → n → ℂ) → F} {T : Set (m → n → ℂ)} (hT : IsOpen T) (hy : A y ∈ T)
    (hΨ : ∀ M ∈ T, ContDiffAt ℝ ∞ Ψ M) : VInfAt (fun z => Ψ (A z)) y :=
  VInfAt.comp (F := m → n → ℂ) (vInfAt_pi fun a => vInfAt_pi fun b => h a b) hT hy
    fun M hM => (hΨ M hM).contDiffWithinAt

theorem mContDiffAt_id (M : m → n → ℂ) : MContDiffAt ∞ (fun N : m → n → ℂ => Matrix.of N) M :=
  fun a b => (contDiffAt_apply _ _ b _).comp M (contDiffAt_apply _ _ a _)

theorem MInfAt.chg {H : CxPts p σ → Matrix m m ℂ} (h : MInfAt A y) (hH : MInfAt H y) :
    MInfAt (fun z => chg (A z) (H z)) y := fun a b => by
  have h₁ : VInfAt (F := m → n → ℂ) A y := vInfAt_pi fun a => vInfAt_pi fun b => h a b
  have h₂ : VInfAt (F := m → m → ℂ) H y := vInfAt_pi fun a => vInfAt_pi fun b => hH a b
  refine (h₁.prodMk h₂).comp_contDiff (Ψ := fun x => HermFrame.chg (of x.1) (of x.2) a b)
    (contDiff_iff_contDiffAt.2 fun x => ?_)
  have e₁ : MContDiffAt ∞ (fun x : (m → n → ℂ) × (m → m → ℂ) => of x.1) x := fun a b =>
    (mContDiffAt_id x.1 a b).comp x contDiffAt_fst
  have e₂ : MContDiffAt ∞ (fun x : (m → n → ℂ) × (m → m → ℂ) => of x.2) x := fun a b =>
    (mContDiffAt_id x.2 a b).comp x contDiffAt_snd
  exact (e₁.transpose.mul e₂).mul e₁.conjTranspose.transpose a b

theorem isOpen_isUnit_det [DecidableEq m] : IsOpen {M : m → m → ℂ | IsUnit (of M).det} :=
  isOpen_iff_mem_nhds.2 fun M hM => (mContDiffAt_id M).eventually_isUnit hM

theorem MInfAt.dualGram [DecidableEq m] {H : CxPts p σ → Matrix m m ℂ} (h : MInfAt H y)
    (hu : IsUnit (H y).det) : MInfAt (fun z => dualGram (H z)) y := fun a b =>
  h.comp (Ψ := fun M => HermFrame.dualGram (of M) a b) isOpen_isUnit_det hu
    fun M hM => ((mContDiffAt_id M).inv hM).transpose a b

theorem MInfAt.log_det [DecidableEq m] {H : CxPts p σ → Matrix m m ℂ} (h : MInfAt H y)
    (hu : (H y).det.re ≠ 0) : CInfAt (fun z => Real.log (H z).det.re) y := by
  have hd (M : m → m → ℂ) : ContDiffAt ℝ ∞ (fun N : m → m → ℂ => (of N).det.re) M :=
    Complex.reCLM.contDiff.contDiffAt.comp M (mContDiffAt_id M).det
  exact h.comp (Ψ := fun M => Real.log (of M).det.re) (T := {M | (of M).det.re ≠ 0})
    (isOpen_ne_fun (contDiff_iff_contDiffAt.2 hd).continuous continuous_const) hu
    fun M hM => (hd M).log hM

end CxPts

@[ext] structure Met (p : X ⟶ Sp k) (σ : k →+* ℂ) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  G : Chart E r → CxPts p σ → Matrix (Fin r) (Fin r) ℂ

  posDef : ∀ c y, y ∈ ptsIn p σ c.U → (G c y).PosDef

  trans : ∀ c c' y, y ∈ ptsIn p σ c.U → G c' y = chg (c.tr p σ c' y) (G c y)

def VB.IsVB.pick {E : X.Modules} {r : ℕ} (h : IsVB E r) (y : CxPts p σ) : Chart E r :=
  CxPts.pick h.isLB_det y

theorem VB.IsVB.mem_pick {E : X.Modules} {r : ℕ} (h : IsVB E r) (y : CxPts p σ) :
    y ∈ ptsIn p σ (h.pick y).U := CxPts.mem_pick h.isLB_det y

namespace Met

variable {E E' : X.Modules} {r : ℕ} (h : Met p σ E r) {V W : X.Opens} {y : CxPts p σ}

def form (s t : Γ(E, V)) (y : CxPts p σ) : ℂ :=
  HermFrame.form (h.G (h.isVB.pick y) y) ((h.isVB.pick y).crd p σ s y) ((h.isVB.pick y).crd p σ t y)

theorem form_eq (c : Chart E r) (hc : y ∈ ptsIn p σ c.U) (s t : Γ(E, V)) (hy : y ∈ ptsIn p σ V) :
    h.form s t y = HermFrame.form (h.G c y) (c.crd p σ s y) (c.crd p σ t y) := by
  have := h.isVB.mem_pick y
  rw [form, h.trans c _ y hc, form_chg, c.tr_mulVec _ s hy this, c.tr_mulVec _ t hy this]

theorem form_frame (c : Chart E r) (hc : y ∈ ptsIn p σ c.U) (a b : Fin r) :
    h.form (c.e a) (c.e b) y = h.G c y a b := by
  rw [h.form_eq c hc _ _ hc, c.crd_frame hc, c.crd_frame hc, form_single]

theorem form_resM (s t : Γ(E, V)) (hW : W ≤ V) (hy : y ∈ ptsIn p σ W) :
    h.form (resM E hW s) (resM E hW t) y = h.form s t y := by
  rw [form, form, Chart.crd_resM _ _ _ hy, Chart.crd_resM _ _ _ hy]

theorem form_add_left (s s' t : Γ(E, V)) (y : CxPts p σ) :
    h.form (s + s') t y = h.form s t y + h.form s' t y := by
  rw [form, Chart.crd_add, HermFrame.form_add_left]; rfl

theorem form_smul_left (g : Γ(X, V)) (s t : Γ(E, V)) (y : CxPts p σ) :
    h.form (g • s) t y = ev p σ V g y * h.form s t y := by
  rw [form, Chart.crd_smul, HermFrame.form_smul_left]; rfl

theorem conj_form (s t : Γ(E, V)) (y : CxPts p σ) :
    starRingEnd ℂ (h.form s t y) = h.form t s y :=
  HermFrame.conj_form (h.posDef _ y (h.isVB.mem_pick y)).isHermitian _ _

theorem G_of_notMem (c : Chart E r) (hc : y ∉ ptsIn p σ c.U) : h.G c y = 0 := by
  rw [h.trans _ c y (h.isVB.mem_pick y), Chart.tr_of_notMem _ _ hc, chg_zero]

theorem ext_of_exists {h h' : Met p σ E r}
    (H : ∀ y, ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧ h.G c y = h'.G c y) : h = h' :=
  Met.ext (funext₂ fun c y => by
    obtain ⟨c₀, hy, e⟩ := H y
    rw [h.trans c₀ c y hy, h'.trans c₀ c y hy, e])

theorem ext_form {h h' : Met p σ E r}
    (H : ∀ (V : X.Opens) (s t : Γ(E, V)) y, y ∈ ptsIn p σ V → h.form s t y = h'.form s t y) :
    h = h' := ext_of_exists fun y => ⟨_, h.isVB.mem_pick y, Matrix.ext fun a b => by
      rw [← h.form_frame _ (h.isVB.mem_pick y), ← h'.form_frame _ (h.isVB.mem_pick y),
        H _ _ _ _ (h.isVB.mem_pick y)]⟩

def ofPt (hE : IsVB E r) (c : CxPts p σ → Chart E r) (hc : ∀ y, y ∈ ptsIn p σ (c y).U)
    (H : CxPts p σ → Matrix (Fin r) (Fin r) ℂ) (hH : ∀ y, (H y).PosDef) : Met p σ E r where
  isVB := hE
  G c' y := chg ((c y).tr p σ c' y) (H y)
  posDef c' y hy := posDef_chg ((c y).isUnit_tr c' (hc y) hy) (hH y)
  trans c' c'' y hy := by rw [chg_chg, (c y).tr_mul' c' c'' hy]

def ofCover (hE : IsVB E r) {ι : Sort*} (c : ι → Chart E r)
    (hc : ∀ y : CxPts p σ, ∃ i, y ∈ ptsIn p σ (c i).U)
    (H : ι → CxPts p σ → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ i y, y ∈ ptsIn p σ (c i).U → (H i y).PosDef) : Met p σ E r :=
  ofPt hE (fun y => c (hc y).choose) (fun y => (hc y).choose_spec) (fun y => H (hc y).choose y)
    fun y => hH _ y (hc y).choose_spec

theorem ofCover_G {hE : IsVB E r} {ι : Sort*} {c : ι → Chart E r} {hc}
    {H : ι → CxPts p σ → Matrix (Fin r) (Fin r) ℂ} {hH}
    (ht : ∀ i j y, y ∈ ptsIn p σ (c i).U → y ∈ ptsIn p σ (c j).U →
      H j y = chg ((c i).tr p σ (c j) y) (H i y)) {i : ι} (hy : y ∈ ptsIn p σ (c i).U) :
    (ofCover hE c hc H hH).G (c i) y = H i y := (ht _ i y (hc y).choose_spec hy).symm

def IsCInf : Prop := ∀ (c : Chart E r), ∀ y ∈ ptsIn p σ c.U, MInfAt (h.G c) y

variable {h} in

theorem isCInf_of_exists (H : ∀ y, ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧ MInfAt (h.G c) y) :
    h.IsCInf := fun c y hy => by
  obtain ⟨c₀, h₀, e⟩ := H y
  refine (MInfAt.chg (A := c₀.tr p σ c) (fun a b => c₀.vInfAt_crd _ hy h₀ a) e).congr ?_
  filter_upwards [(isOpen_ptsIn _).mem_nhds h₀] with z hz using h.trans c₀ c z hz

def IsConj (h' : Met p σ' E r) : Prop :=
  ∀ (c : Chart E r) (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
    h'.G c y' = (h.G c y).map star

variable {h} in

theorem isConj_of_exists {h' : Met p σ' E r}
    (H : ∀ (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 →
      ∃ c : Chart E r, y ∈ ptsIn p σ c.U ∧ h'.G c y' = (h.G c y).map star) : h.IsConj h' :=
  fun c y y' e => by
    obtain ⟨c₀, h₀, e₀⟩ := H y y' e
    rw [h.trans c₀ c y h₀, h'.trans c₀ c y' ((mem_ptsIn_iff_of_conj e).2 h₀), e₀, c₀.tr_conj c e,
      chg_map_star]

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    Met q σ ((Scheme.Modules.pullback π).obj E) r :=
  ofCover (h.isVB.pullback π) (fun c : Chart E r => c.pull h.isVB π)
    (fun z => ⟨_, h.isVB.mem_pick (PtsOver.map π hπ _ z)⟩)
    (fun c z => h.G c (PtsOver.map π hπ _ z)) fun c _ hz => h.posDef c _ hz

theorem pull_G {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (c : Chart E r) {z : CxPts q σ}
    (hz : PtsOver.map π hπ _ z ∈ ptsIn p σ c.U) :
    (h.pull π hπ).G (c.pull h.isVB π) z = h.G c (PtsOver.map π hπ _ z) :=
  ofCover_G (c := fun c : Chart E r => c.pull h.isVB π) (fun c c' z hz hz' => by
    rw [c.tr_pull c' _ π hπ hz hz', ← h.trans c c' _ hz]) hz

theorem form_pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) (s t : Γ(E, V)) {T : Y.Opens}
    (hT : T ≤ π ⁻¹ᵁ V) {z : CxPts q σ} (hz : z ∈ ptsIn q σ T) :
    (h.pull π hπ).form (pullbackSections π E hT s) (pullbackSections π E hT t) z =
      h.form s t (PtsOver.map π hπ _ z) := by
  have hc := h.isVB.mem_pick (PtsOver.map π hπ _ z)
  rw [(h.pull π hπ).form_eq (Chart.pull _ h.isVB π) hc _ _ hz, h.pull_G π hπ _ hc,
    Chart.crd_pull _ _ π hπ _ _ hz hc, Chart.crd_pull _ _ π hπ _ _ hz hc, form]

def dual : Met p σ (VB.dual E) r :=
  ofCover h.isVB.dual Chart.dual (fun y => ⟨_, h.isVB.mem_pick y⟩)
    (fun c y => dualGram (h.G c y)) fun c y hy => posDef_dualGram (h.posDef c y hy)

theorem dual_G (c : Chart E r) (hy : y ∈ ptsIn p σ c.U) :
    h.dual.G c.dual y = dualGram (h.G c y) :=
  ofCover_G (fun c c' y hy hy' => by
    rw [c.tr_dual c' hy hy', h.trans c c' y hy,
      dualGram_chg ((c.tr_mul c' c hy' hy).trans (c.tr_self hy))]) hy

def map (φ : E ≅ E') : Met p σ E' r :=
  ofCover (h.isVB.of_iso φ) (·.map φ) (fun y => ⟨_, h.isVB.mem_pick y⟩) h.G h.posDef

theorem map_G (φ : E ≅ E') (c : Chart E r) (hy : y ∈ ptsIn p σ c.U) :
    (h.map φ).G (c.map φ) y = h.G c y :=
  ofCover_G (fun c c' y hy _ => by rw [c.tr_map c' φ, ← h.trans c c' y hy]) hy

theorem form_map (φ : E ≅ E') (s t : Γ(E, V)) (hy : y ∈ ptsIn p σ V) :
    (h.map φ).form (φ.hom.app V s) (φ.hom.app V t) y = h.form s t y := by
  have hc := h.isVB.mem_pick y
  rw [(h.map φ).form_eq (Chart.map _ φ) hc _ _ hy, h.map_G φ _ hc, Chart.crd_map, Chart.crd_map, form]

def expMul (u : CxPts p σ → ℝ) : Met p σ E r where
  isVB := h.isVB
  G c y := (Real.exp (u y) : ℂ) • h.G c y
  posDef c y hy := (h.posDef c y hy).smul (by exact_mod_cast Real.exp_pos _)
  trans c c' y hy := by rw [chg_smul, ← h.trans c c' y hy]

theorem form_expMul (u : CxPts p σ → ℝ) (s t : Γ(E, V)) (y : CxPts p σ) :
    (h.expMul u).form s t y = Real.exp (u y) * h.form s t y := form_smul _ _ _ _

def detWeight : Weight p σ (det E r) where
  isLB := h.isVB.isLB_det
  φ c y := -Real.log (h.G c y).det.re
  trans c c' y hy hy' := by
    have := gv_ne_zero (B := det E r) hy hy'
    rw [h.trans c c' y hy, det_chg, c.det_tr c' hy hy', Complex.re_ofReal_mul,
      Real.log_mul (by positivity) (det_re_pos (h.posDef c y hy)).ne']
    ring

def ofWeight {L : LB X} (φ : Weight p σ L) : Met p σ (toMod L) 1 :=
  ofCover (isVB_toMod φ.isLB) (Chart.ofLB φ.isLB) (fun y => ⟨_, mem_pick φ.isLB y⟩)
    (fun i y => (Real.exp (-φ.φ i y) : ℂ) • 1)
    fun _ _ _ => PosDef.one.smul (by exact_mod_cast Real.exp_pos _)

theorem ofWeight_G {L : LB X} (φ : Weight p σ L) {i : L.ι} (hy : y ∈ ptsIn p σ (L.U i)) :
    (ofWeight φ).G (Chart.ofLB φ.isLB i) y = (Real.exp (-φ.φ i y) : ℂ) • 1 :=
  ofCover_G (fun i j y hi hj => by
    have := gv_ne_zero (B := L) hi hj
    have e := det_chg ((Chart.ofLB φ.isLB i).tr p σ (Chart.ofLB φ.isLB j) y)
      ((Real.exp (-φ.φ i y) : ℂ) • 1)
    simp only [det_unique, Chart.tr_ofLB φ.isLB hi hj, Matrix.smul_apply, one_apply_eq,
      smul_eq_mul, mul_one] at e
    ext a b
    rw [Subsingleton.elim a default, Subsingleton.elim b default, e, φ.trans i j y hi hj, neg_sub,
      sub_eq_add_neg, Real.exp_add, Real.exp_log (by positivity)]
    simp) hy

def ofFrame {e : Fin r → Γ(E, ⊤)} (he : IsFrame e) (H : CxPts p σ → Matrix (Fin r) (Fin r) ℂ)
    (hH : ∀ y, (H y).PosDef) : Met p σ E r :=
  ofPt (fun _ => ⟨⊤, e, trivial, he⟩) (fun _ => ⟨⊤, e, he⟩) (fun _ => mem_ptsIn_top) H hH

theorem ofFrame_G {e : Fin r → Γ(E, ⊤)} (he : IsFrame e)
    (H : CxPts p σ → Matrix (Fin r) (Fin r) ℂ) (hH : ∀ y, (H y).PosDef) (y : CxPts p σ) :
    (ofFrame he H hH).G ⟨⊤, e, he⟩ y = H y :=
  (congrArg (chg · (H y)) (Chart.tr_self ⟨⊤, e, he⟩ mem_ptsIn_top)).trans (chg_one _)

variable {h}

theorem IsCInf.pull (H : h.IsCInf) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (h.pull π hπ).IsCInf := isCInf_of_exists fun z => by
  have hc := h.isVB.mem_pick (PtsOver.map π hπ _ z)
  refine ⟨Chart.pull _ h.isVB π, hc, MInfAt.congr (fun a b => (H _ _ hc a b).pull π hπ) ?_⟩
  filter_upwards [(isOpen_ptsIn (π ⁻¹ᵁ _)).mem_nhds hc] with w hw using h.pull_G π hπ _ hw

theorem IsCInf.dual (H : h.IsCInf) : h.dual.IsCInf := isCInf_of_exists fun y => by
  have hc := h.isVB.mem_pick y
  refine ⟨Chart.dual _, hc, ((H _ _ hc).dualGram (h.posDef _ _ hc).det_pos.ne'.isUnit).congr ?_⟩
  filter_upwards [(isOpen_ptsIn _).mem_nhds hc] with w hw using h.dual_G _ hw

theorem IsCInf.map (H : h.IsCInf) (φ : E ≅ E') : (h.map φ).IsCInf := isCInf_of_exists fun y => by
  have hc := h.isVB.mem_pick y
  refine ⟨Chart.map _ φ, hc, (H _ _ hc).congr ?_⟩
  filter_upwards [(isOpen_ptsIn _).mem_nhds hc] with w hw using h.map_G φ _ hw

theorem IsCInf.expMul (H : h.IsCInf) {u : CxPts p σ → ℝ} (hu : ∀ y, CInfAt u y) :
    (h.expMul u).IsCInf := fun c y hy a b =>
  ((vInfAt_iff_cInfAt.2 (hu y)).prodMk (H c y hy a b)).comp_contDiff
    (Ψ := fun x => (Real.exp x.1 : ℂ) * x.2)
    ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_fst)).mul contDiff_snd)

theorem IsCInf.detWeight (H : h.IsCInf) : h.detWeight.IsCInf := fun c y hy =>
  ((H c y hy).log_det (det_re_pos (h.posDef c y hy)).ne').neg

theorem isCInf_ofWeight {L : LB X} {φ : Weight p σ L} (H : φ.IsCInf) : (ofWeight φ).IsCInf :=
  isCInf_of_exists fun y => by
    have hc := mem_pick φ.isLB y
    refine ⟨Chart.ofLB φ.isLB _, hc, MInfAt.congr (A := fun w =>
      (Real.exp (-φ.φ (pick φ.isLB y) w) : ℂ) • 1) (fun a b => ?_) ?_⟩
    · exact (vInfAt_iff_cInfAt.2 (H _ y hc)).comp_contDiff
        (Ψ := fun x => (Real.exp (-x) : ℂ) * (1 : Matrix (Fin 1) (Fin 1) ℂ) a b)
        ((Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp contDiff_neg)).mul contDiff_const)
    · filter_upwards [(isOpen_ptsIn _).mem_nhds hc] with w hw using ofWeight_G φ hw

theorem isCInf_ofFrame {e : Fin r → Γ(E, ⊤)} (he : IsFrame e)
    {H : CxPts p σ → Matrix (Fin r) (Fin r) ℂ} (hH : ∀ y, (H y).PosDef) (hs : ∀ y, MInfAt H y) :
    (ofFrame he H hH).IsCInf := isCInf_of_exists fun y =>
  ⟨⟨⊤, e, he⟩, mem_ptsIn_top, (hs y).congr (.of_forall (ofFrame_G he H hH))⟩

end Met

namespace Met

variable {E E' : X.Modules} {r : ℕ} {h : Met p σ E r} {h' : Met p σ' E r}

theorem IsConj.form_eq (H : h.IsConj h') {V : X.Opens} (s t : Γ(E, V)) {y : CxPts p σ}
    {y' : CxPts p σ'} (e : y'.1 = spMap (starRingEnd ℂ) ≫ y.1) (hy : y ∈ ptsIn p σ V) :
    h'.form s t y' = starRingEnd ℂ (h.form s t y) := by
  have hc := h.isVB.mem_pick y
  rw [h'.form_eq _ ((mem_ptsIn_iff_of_conj e).2 hc) _ _ ((mem_ptsIn_iff_of_conj e).2 hy), H _ y y' e,
    Chart.crd_conj _ e, Chart.crd_conj _ e, form]
  simp [form_eq_sum]

theorem IsConj.pull (H : h.IsConj h') {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (h.pull π hπ).IsConj (h'.pull π hπ) := isConj_of_exists fun z z' e => by
  have hc := h.isVB.mem_pick (PtsOver.map π hπ _ z)
  have e' : (PtsOver.map π hπ _ z').1 = spMap (starRingEnd ℂ) ≫ (PtsOver.map π hπ _ z).1 :=
    (congrArg (· ≫ π) e).trans (Category.assoc _ _ _)
  exact ⟨Chart.pull _ h.isVB π, hc, by
    rw [h.pull_G π hπ _ hc, h'.pull_G π hπ _ ((mem_ptsIn_iff_of_conj e').2 hc), H _ _ _ e']⟩

theorem IsConj.dual (H : h.IsConj h') : h.dual.IsConj h'.dual := isConj_of_exists fun y y' e => by
  have hc := h.isVB.mem_pick y
  exact ⟨Chart.dual _, hc, by
    rw [h.dual_G _ hc, h'.dual_G _ ((mem_ptsIn_iff_of_conj e).2 hc), H _ _ _ e, dualGram_map_star]⟩

theorem IsConj.map (H : h.IsConj h') (φ : E ≅ E') : (h.map φ).IsConj (h'.map φ) :=
  isConj_of_exists fun y y' e => by
    have hc := h.isVB.mem_pick y
    exact ⟨Chart.map _ φ, hc, by
      rw [h.map_G _ _ hc, h'.map_G _ _ ((mem_ptsIn_iff_of_conj e).2 hc), H _ _ _ e]⟩

theorem IsConj.expMul (H : h.IsConj h') {u : CxPts p σ → ℝ} {u' : CxPts p σ' → ℝ}
    (hu : ∀ (y : CxPts p σ) (y' : CxPts p σ'), y'.1 = spMap (starRingEnd ℂ) ≫ y.1 → u' y' = u y) :
    (h.expMul u).IsConj (h'.expMul u') := fun c y y' e => by
  ext a b
  simp only [Met.expMul, H c y y' e, hu y y' e, Matrix.smul_apply, map_apply, smul_eq_mul,
    Complex.star_def, map_mul, Complex.conj_ofReal]

theorem det_map_star_re {n : Type} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) :
    (M.map star).det.re = M.det.re := by
  rw [show M.map star = Mᵀᴴ from rfl, det_conjTranspose, det_transpose, Complex.star_def,
    Complex.conj_re]

theorem IsConj.detWeight (H : h.IsConj h') : h.detWeight.IsConj h'.detWeight :=
  fun c y y' e _ => congrArg (fun x => -Real.log x) ((congrArg (·.det.re) (H c y y' e)).trans
    (det_map_star_re _))

theorem isConj_ofWeight {L : LB X} {φ : Weight p σ L} {φ' : Weight p σ' L} (H : φ.IsConj φ') :
    (ofWeight φ).IsConj (ofWeight φ') := isConj_of_exists fun y y' e => by
  have hc := mem_pick φ.isLB y
  refine ⟨Chart.ofLB φ.isLB _, hc, ?_⟩
  rw [ofWeight_G φ hc, ofWeight_G φ' ((mem_ptsIn_iff_of_conj e).2 hc), H _ y y' e hc]
  ext a b
  simp only [Matrix.smul_apply, map_apply, smul_eq_mul, Complex.star_def, map_mul,
    Complex.conj_ofReal, Subsingleton.elim a b, one_apply_eq, map_one]

theorem detWeight_ofWeight {L : LB X} (φ : Weight p σ L) {i : L.ι} {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ (L.U i)) : (ofWeight φ).detWeight.φ (Chart.ofLB φ.isLB i) y = φ.φ i y := by
  change -Real.log _ = _
  rw [ofWeight_G φ hy]
  simp only [det_unique, Matrix.smul_apply, one_apply_eq, smul_eq_mul, mul_one, Complex.ofReal_re,
    Real.log_exp, neg_neg]

end Met

@[ext] structure VMetric (p : X ⟶ Sp k) (E : X.Modules) (r : ℕ) where

  isVB : IsVB E r

  met : ∀ σ : k →+* ℂ, Met p σ E r

  conj : ∀ σ σ', (met σ).IsConj (met σ')

namespace VMetric

variable {E E' E₁ E₂ : X.Modules} {r r₁ r₂ : ℕ} (h : VMetric p E r)

def IsCInf : Prop := ∀ σ, (h.met σ).IsCInf

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    VMetric q ((Scheme.Modules.pullback π).obj E) r :=
  ⟨h.isVB.pullback π, fun σ => (h.met σ).pull π hπ, fun σ σ' => (h.conj σ σ').pull π hπ⟩

def dual : VMetric p (VB.dual E) r :=
  ⟨h.isVB.dual, fun σ => (h.met σ).dual, fun σ σ' => (h.conj σ σ').dual⟩

def map (φ : E ≅ E') : VMetric p E' r :=
  ⟨h.isVB.of_iso φ, fun σ => (h.met σ).map φ, fun σ σ' => (h.conj σ σ').map φ⟩

def scale (t : ℝ) : VMetric p E r :=
  ⟨h.isVB, fun σ => (h.met σ).expMul fun _ => t, fun σ σ' => (h.conj σ σ').expMul fun _ _ _ => rfl⟩

def ofLB (L : HermLB p) : VMetric p (toMod L.B) 1 :=
  ⟨isVB_toMod L.isLB, fun σ => .ofWeight (L.φ σ), fun σ σ' => Met.isConj_ofWeight (L.conj σ σ')⟩

variable (p) in

def orthonormal {e : Fin r → Γ(E, ⊤)} (he : IsFrame e) : VMetric p E r :=
  ⟨fun _ => ⟨⊤, e, trivial, he⟩, fun _ => .ofFrame he (fun _ => 1) fun _ => PosDef.one,
    fun _ _ => Met.isConj_of_exists fun _ _ _ => ⟨⟨⊤, e, he⟩, mem_ptsIn_top, by
      rw [Met.ofFrame_G, Met.ofFrame_G, Matrix.map_one _ (star_zero _) (star_one _)]⟩⟩

def IsCInfNorm : Prop :=
  ∀ (Y : Scheme.{0}) (π : Y ⟶ X), SmoothOfRelativeDimension 1 (π ≫ p) → (h.pull π rfl).IsCInf

def IsIsometry (h' : VMetric p E' r) (φ : E ≅ E') : Prop :=
  ∀ σ (V : X.Opens) (s t : Γ(E, V)), ∀ y ∈ ptsIn p σ V,
    (h'.met σ).form (φ.hom.app V s) (φ.hom.app V t) y = (h.met σ).form s t y

def IsOrthSum (h : VMetric p (E₁ ⊞ E₂) r) (h₁ : VMetric p E₁ r₁) (h₂ : VMetric p E₂ r₂) : Prop :=
  ∀ σ (V : X.Opens) (s t : Γ(E₁ ⊞ E₂, V)), ∀ y ∈ ptsIn p σ V, (h.met σ).form s t y =
    (h₁.met σ).form ((Limits.biprod.fst : E₁ ⊞ E₂ ⟶ E₁).app V s)
        ((Limits.biprod.fst : E₁ ⊞ E₂ ⟶ E₁).app V t) y +
      (h₂.met σ).form ((Limits.biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app V s)
        ((Limits.biprod.snd : E₁ ⊞ E₂ ⟶ E₂).app V t) y

theorem isIsometry_iff {h' : VMetric p E' r} {φ : E ≅ E'} : h.IsIsometry h' φ ↔ h' = h.map φ := by
  refine ⟨fun H => VMetric.ext (funext fun σ => Met.ext_form fun V s t y hy => ?_), ?_⟩
  · obtain ⟨s, rfl⟩ : ∃ s', φ.hom.app V s' = s := ⟨φ.inv.app V s, congr(($(φ.inv_hom_id)).app V s)⟩
    obtain ⟨t, rfl⟩ : ∃ t', φ.hom.app V t' = t := ⟨φ.inv.app V t, congr(($(φ.inv_hom_id)).app V t)⟩
    exact (H σ V s t y hy).trans ((h.met σ).form_map φ s t hy).symm
  · rintro rfl σ V s t y hy
    exact (h.met σ).form_map φ s t hy

variable {h}

theorem IsCInf.pull (H : h.IsCInf) {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (h.pull π hπ).IsCInf := fun σ => (H σ).pull π hπ

theorem IsCInf.isCInfNorm (H : h.IsCInf) : h.IsCInfNorm := fun _ π _ => H.pull π rfl

theorem IsCInf.dual (H : h.IsCInf) : h.dual.IsCInf := fun σ => (H σ).dual

theorem IsCInf.map (H : h.IsCInf) (φ : E ≅ E') : (h.map φ).IsCInf := fun σ => (H σ).map φ

theorem IsCInf.scale (H : h.IsCInf) (t : ℝ) : (h.scale t).IsCInf := fun σ =>
  (H σ).expMul (cInfAt_const t)

theorem isCInf_ofLB (L : HermLB p) : (ofLB L).IsCInf := fun σ => Met.isCInf_ofWeight (L.cInf σ)

theorem isCInf_orthonormal {e : Fin r → Γ(E, ⊤)} (he : IsFrame e) : (orthonormal p he).IsCInf :=
  fun _ => Met.isCInf_ofFrame he (fun _ => PosDef.one) fun y _ _ => vInfAt_const _ y

def det (H : h.IsCInf) : HermLB p where
  B := VB.det E r
  isLB := h.isVB.isLB_det
  φ σ := (h.met σ).detWeight
  cInf σ := (H σ).detWeight
  conj σ σ' := (h.conj σ σ').detWeight

variable (h) in

def FirstChernIntegrable : Prop :=
  ∀ σ, (h.met σ).detWeight.ChernIntegrableOn 1 univ fun _ => 1

variable (h) in

def first_chern_integral : ℝ := ∑ᶠ σ, (h.met σ).detWeight.chernInt 1 univ fun _ => 1

theorem firstChernIntegral_eq_degree (H : h.IsCInf) : h.first_chern_integral = ArInt.gdeg (det H) 1 := rfl

end VMetric

structure HermVB (p : X ⟶ Sp k) (r : ℕ) where

  E : X.Modules

  h : VMetric p E r

  cInf : h.IsCInf

namespace HermVB

variable {r : ℕ} (E : HermVB p r)

def pull {q : Y ⟶ Sp k} (π : Y ⟶ X) (hπ : π ≫ p = q) : HermVB q r :=
  ⟨_, E.h.pull π hπ, E.cInf.pull π hπ⟩

def dual : HermVB p r := ⟨_, E.h.dual, E.cInf.dual⟩

def scale (t : ℝ) : HermVB p r := ⟨_, E.h.scale t, E.cInf.scale t⟩

def det : HermLB p := VMetric.det E.cInf

def ofLB (L : HermLB p) : HermVB p 1 := ⟨_, .ofLB L, VMetric.isCInf_ofLB L⟩

variable (p r) in

def std : HermVB p r :=
  ⟨_, .orthonormal p (isFrame_freeFrame X (Fin r)), VMetric.isCInf_orthonormal _⟩

end HermVB

example {E : X.Modules} {r : ℕ} (h : VMetric p E r) (t : ℝ) (c : Chart E r) {y : CxPts p σ}
    (hy : y ∈ ptsIn p σ c.U) :
    ((h.scale t).met σ).detWeight.φ c y = (h.met σ).detWeight.φ c y - r * t := by
  change -Real.log ((Real.exp t : ℂ) • (h.met σ).G c y).det.re = -Real.log _ - _
  rw [det_smul, Fintype.card_fin, ← Complex.ofReal_pow, Complex.re_ofReal_mul,
    Real.log_mul (by positivity) (det_re_pos ((h.met σ).posDef c y hy)).ne', Real.log_pow,
    Real.log_exp]
  ring

example {E : X.Modules} (h : Met p σ E 1) (c : Chart E 1) {y : CxPts p σ} (hy : y ∈ ptsIn p σ c.U)
    (e : h.G c y = (Real.pi : ℂ) • 1) : h.dual.G c.dual y 0 0 = 1 / Real.pi := by
  rw [h.dual_G c hy, e]
  simp [dualGram, Matrix.inv_def, Ring.inverse_eq_inv]

end GlobalTheory
