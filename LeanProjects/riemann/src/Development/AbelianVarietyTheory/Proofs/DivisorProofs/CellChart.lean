import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TotalEqCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjacentPullPull
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniREqUni
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtalePolynomialSubstitutionStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Points GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame GlobalTheory.ArInt GlobalTheory.MixDens GlobalTheory.CovTest
open GlobalTheory.FlagFibre (Low uni dens)
open ReciprocityTheory.L2DbarEstimates (V cHess)
open scoped ContDiff ComplexOrder Classical

open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open Set

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CellChart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ}

include w in

theorem algX_eq {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) :
    (π.appLE U W hW).hom.comp (algX q U) = algX p W := by
  subst w
  have e := Scheme.Hom.appLE_comp_appLE π q ⊤ U W le_top hW
  exact congrArg (fun f ↦ (CommRingCat.Hom.hom f).comp (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom) e

theorem map_mem {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    PtsOver.map π w (spMap σ) y ∈ ptsIn q σ U :=
  le_preimage_comp y.1 π hW hy

theorem ev_appLE {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) {y : CxPts p σ} (hy : y ∈ ptsIn p σ W)
    (g : Γ(B, U)) : ev p σ W ((π.appLE U W hW).hom g) y = ev q σ U g (PtsOver.map π w (spMap σ) y) :=
  valR_appLE y.1 π hW hy g

variable {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) {N : Type} (n : N → Γ(Y, W))
  (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))

def cellHom {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) : Γ(Y, W) →+* ℂ :=
  (MvPolynomial.eval₂Hom (evHom hb) z).comp (RingEquiv.ofBijective _ hΦ).symm.toRingHom

theorem cellHom_eq {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (φ : Γ(Y, W) →+* ℂ)
    (h₁ : ∀ g, φ ((π.appLE U W hW).hom g) = evHom hb g) (h₂ : ∀ s, φ (n s) = z s) :
    cellHom π hW n hΦ hb z = φ := by
  have H : φ.comp (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n) = MvPolynomial.eval₂Hom (evHom hb) z :=
    MvPolynomial.ringHom_ext (fun g => by simp [h₁]) fun s => by simp [h₂]
  ext g
  obtain ⟨P, rfl⟩ := hΦ.2 g
  have e : (RingEquiv.ofBijective _ hΦ).symm (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n P) = P :=
    (RingEquiv.ofBijective _ hΦ).symm_apply_apply P
  simp only [cellHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e]
  rw [← H, RingHom.comp_apply]

theorem cellHom_appLE {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (g : Γ(B, U)) :
    cellHom π hW n hΦ hb z ((π.appLE U W hW).hom g) = evHom hb g := by
  have e : (RingEquiv.ofBijective _ hΦ).symm ((π.appLE U W hW).hom g) = MvPolynomial.C g := by
    rw [RingEquiv.symm_apply_eq]; simp
  simp only [cellHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
    MvPolynomial.eval₂Hom_C]

theorem cellHom_n {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (s : N) :
    cellHom π hW n hΦ hb z (n s) = z s := by
  have e : (RingEquiv.ofBijective _ hΦ).symm (n s) = MvPolynomial.X s := by
    rw [RingEquiv.symm_apply_eq]; simp
  simp only [cellHom, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom, e,
    MvPolynomial.eval₂Hom_X']

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {U : B.Opens} {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ U) (hWa : IsAffineOpen W) {N : Type}
  (n : N → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE U W hW).hom n))

def cellPt {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) : CxPts p σ :=
  ofHom hWa (cellHom π hW n hΦ hb z) fun a => by
    rw [← algX_eq π w hW, RingHom.comp_apply, cellHom_appLE, ← ev_eq hb, ev_algX hb]

theorem cellPt_mem {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) :
    cellPt π w hW hWa n hΦ hb z ∈ ptsIn p σ W := ofHom_mem _ _ _

theorem ev_cellPt {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (g : Γ(Y, W)) :
    ev p σ W g (cellPt π w hW hWa n hΦ hb z) = cellHom π hW n hΦ hb z g := ev_ofHom _ _ _ g

theorem ev_n_cellPt {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) (s : N) :
    ev p σ W (n s) (cellPt π w hW hWa n hΦ hb z) = z s := by
  rw [ev_cellPt, cellHom_n]

theorem map_cellPt (hU : IsAffineOpen U) {b : CxPts q σ} (hb : b ∈ ptsIn q σ U) (z : N → ℂ) :
    PtsOver.map π w (spMap σ) (cellPt π w hW hWa n hΦ hb z) = b := by
  have hm := map_mem π w hW (cellPt_mem π w hW hWa n hΦ hb z)
  refine Subtype.ext (ext_of_valR hU hm hb fun g => ?_)
  have h₁ := ev_appLE π w hW (cellPt_mem π w hW hWa n hΦ hb z) g
  rw [ev_cellPt, cellHom_appLE, ← ev_eq hb] at h₁
  exact h₁.symm

theorem cellPt_self {y : CxPts p σ} (hy : y ∈ ptsIn p σ W) :
    cellPt π w hW hWa n hΦ (map_mem π w hW hy) (fun s => ev p σ W (n s) y) = y := by
  refine Subtype.ext (ext_of_valR hWa (cellPt_mem π w hW hWa n hΦ _ _) hy fun g => ?_)
  change ev p σ W g _ = ev p σ W g y
  rw [ev_cellPt, cellHom_eq π hW n hΦ _ _ (evHom hy) (fun g => ?_) (fun s => ?_), ← ev_eq hy]
  · rw [← ev_eq hy, ← ev_eq (map_mem π w hW hy), ev_appLE π w hW hy]
  · rw [← ev_eq hy]

theorem cellPt_congr {b b' : CxPts q σ} (hb : b ∈ ptsIn q σ U) (hb' : b' ∈ ptsIn q σ U) (e : b = b')
    {z z' : N → ℂ} (ez : z = z') : cellPt π w hW hWa n hΦ hb z = cellPt π w hW hWa n hΦ hb' z' := by
  subst e ez; rfl

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))

omit [CommRing k] in

theorem differentiable_base : Differentiable ℂ (base e) := by
  refine differentiable_euclidean.2 fun i => ?_
  obtain rfl : i = 0 := Subsingleton.elim _ _
  simp only [base, EuclideanSpace.single_apply, if_true]
  fun_prop

variable (c : AlgChart q σ 1) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (n : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n))
  (y₀ : CxPts p σ)

def inv (v : V (d + 1)) : CxPts p σ :=
  if h : base e v ∈ c.e.target then
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun s => v (e.symm (some s)))
  else y₀

variable {e c hW hWa n hΦ}

theorem inv_eq {v : V (d + 1)} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v =
    cellPt π w hW hWa n hΦ (c.source_subset (c.e.map_target h)) (fun s => v (e.symm (some s))) := dif_pos h

theorem inv_mem {v : V (d + 1)} (h : base e v ∈ c.e.target) : inv π w e c hW hWa n hΦ y₀ v ∈ ptsIn p σ W := by
  rw [inv_eq _ _ _ h]; exact cellPt_mem ..

theorem map_inv {v : V (d + 1)} (h : base e v ∈ c.e.target) :
    PtsOver.map π w (spMap σ) (inv π w e c hW hWa n hΦ y₀ v) = c.e.symm (base e v) := by
  rw [inv_eq _ _ _ h]; exact map_cellPt _ _ _ _ _ _ c.affine _ _

theorem ev_n_inv {v : V (d + 1)} (h : base e v ∈ c.e.target) (s : Σ a, Low (r a)) :
    ev p σ W (n s) (inv π w e c hW hWa n hΦ y₀ v) = v (e.symm (some s)) := by
  rw [inv_eq _ _ _ h]; exact ev_n_cellPt ..

theorem ev_appLE_inv {v : V (d + 1)} (h : base e v ∈ c.e.target) (g : Γ(B, c.U)) :
    ev p σ W ((π.appLE c.U W hW).hom g) (inv π w e c hW hWa n hΦ y₀ v) = ev q σ c.U g (c.e.symm (base e v)) := by
  rw [ev_appLE π w hW (inv_mem π w y₀ h), map_inv π w y₀ h]

theorem holo_inv (g : Γ(Y, W)) :
    DifferentiableOn ℂ (fun v => ev p σ W g (inv π w e c hW hWa n hΦ y₀ v)) {v | base e v ∈ c.e.target} := by
  obtain ⟨P, rfl⟩ := hΦ.2 g
  induction P using MvPolynomial.induction_on with
  | C a =>
    have hd : DifferentiableOn ℂ (fun v => ev q σ c.U a (c.e.symm (base e v))) {v | base e v ∈ c.e.target} :=
      (c.holo c.U a).comp (differentiable_base e).differentiableOn fun v hv =>
        ⟨hv, c.source_subset (c.e.map_target hv)⟩
    refine hd.congr fun v hv => ?_
    simp only [MvPolynomial.eval₂Hom_C]
    exact ev_appLE_inv π w y₀ hv a
  | add P Q hP hQ =>
    simp only [map_add, ev_add]
    exact hP.add hQ
  | mul_X P s hP =>
    have hd : DifferentiableOn ℂ (fun v : V (d + 1) => v (e.symm (some s))) {v | base e v ∈ c.e.target} := by
      fun_prop
    simp only [map_mul, ev_mul, MvPolynomial.eval₂Hom_X']
    exact hP.mul (hd.congr fun v hv => ev_n_inv π w y₀ hv s)

end Chart

end GlobalTheory.CellChart

namespace GlobalTheory.CellChart

section Chart

variable {k : Type} [CommRing k] {B Y : Scheme.{0}} {q : B ⟶ Sp k} {p : Y ⟶ Sp k} (π : Y ⟶ B) (w : π ≫ q = p)
  {σ : k →+* ℂ} {ι : Type} {r : ι → ℕ} {d : ℕ} (e : Fin (d + 1) ≃ Option (Σ a, Low (r a)))
  (c : AlgChart q σ 1) {W : Y.Opens} (hW : W ≤ π ⁻¹ᵁ c.U) (hWa : IsAffineOpen W)
  (n : (Σ a, Low (r a)) → Γ(Y, W)) (hΦ : Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n))
  (y₀ : CxPts p σ)

def toF (y : CxPts p σ) : V (d + 1) :=
  pt e (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (n ⟨a, s⟩) y

def chart : OpenPartialHomeomorph (CxPts p σ) (V (d + 1)) where
  toFun := toF π w e c n
  invFun := inv π w e c hW hWa n hΦ y₀
  source := PtsOver.map π w (spMap σ) ⁻¹' c.e.source ∩ ptsIn p σ W
  target := {v | base e v ∈ c.e.target}
  map_source' y hy := by
    show base e (toF π w e c n y) ∈ c.e.target
    rw [toF, base_pt]
    exact c.e.map_source hy.1
  map_target' v hv :=
    ⟨by rw [mem_preimage, map_inv π w y₀ hv]; exact c.e.map_target hv, inv_mem π w y₀ hv⟩
  left_inv' y hy := by
    have hb : base e (toF π w e c n y) ∈ c.e.target := by
      rw [toF, base_pt]; exact c.e.map_source hy.1
    rw [inv_eq π w y₀ hb]
    refine (cellPt_congr π w hW hWa n hΦ _ (map_mem π w hW hy.2) ?_ ?_).trans (cellPt_self π w hW hWa n hΦ hy.2)
    · rw [toF, base_pt, c.e.left_inv hy.1]
    · funext s
      simp [toF, pt]
  right_inv' v hv := by
    ext j
    simp only [toF, pt, PiLp.toLp_apply]
    rcases h : e j with _ | s
    · have hj : e.symm none = j := by rw [← h, Equiv.symm_apply_apply]
      simp only [Option.elim]
      rw [map_inv π w y₀ hv, c.e.right_inv hv]
      simp [base, hj]
    · simp only [Option.elim]
      rw [ev_n_inv π w y₀ hv, ← h, Equiv.symm_apply_apply]
  open_source := ((PtsOver.continuous_map π w _).isOpen_preimage _ c.e.open_source).inter (isOpen_ptsIn W)
  open_target := c.e.open_target.preimage (differentiable_base e).continuous
  continuousOn_toFun := by
    refine (PiLp.continuous_toLp 2 _).comp_continuousOn (continuousOn_pi.2 fun j => ?_)
    rcases h : e j with _ | s
    · simp only [h, Option.elim]
      exact (PiLp.continuous_apply 2 _ 0).comp_continuousOn
        (c.e.continuousOn.comp (PtsOver.continuous_map π w _).continuousOn fun y hy => hy.1)
    · simp only [h, Option.elim]
      exact (continuousOn_ev (n s)).mono inter_subset_right
  continuousOn_invFun := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base e).continuous)
    (fun v hv => inv_mem π w y₀ hv) fun g => holo_inv π w y₀ g).1

def cellChart : AlgChart p σ (d + 1) where
  e := chart π w e c hW hWa n hΦ y₀
  U := W
  affine := hWa
  x j := (e j).elim ((π.appLE c.U W hW).hom (c.x 0)) n
  etale := by
    have hx : c.x = fun _ => c.x 0 := funext fun i => by rw [Subsingleton.elim i 0]
    have h := GlobalTheory.T.etale_polynomial_substitution (algX q c.U) (c.x 0) (π.appLE c.U W hW).hom n e (hx ▸ c.etale) hΦ
    rwa [algX_eq π w hW] at h
  source_subset := inter_subset_right
  apply_eq y hy j := by
    show toF π w e c n y j = _
    simp only [toF, pt, PiLp.toLp_apply]
    rcases h : e j with _ | s
    · simp only [Option.elim]
      rw [c.apply_eq _ hy.1 0, ev_appLE π w hW hy.2]
    · rfl
  holo W' f := (holo_of_affine hWa (c.e.open_target.preimage (differentiable_base e).continuous)
    (fun v hv => inv_mem π w y₀ hv) fun g => holo_inv π w y₀ g).2 W' f

end Chart

end GlobalTheory.CellChart

open GlobalTheory.CellChart in

theorem GlobalTheory.cell_chart : ∀ (k : Type) [CommRing k] (B Y : Scheme.{0}) (q : B ⟶ Sp k) (p : Y ⟶ Sp k) (π : Y ⟶ B) (w : π ≫ q = p) (ι : Type) [Fintype ι] (r : ι → ℕ) (d : ℕ) (e : Fin (d + 1) ≃ Option (Σ a, Low (r a))) (σ : k →+* ℂ) (c : AlgChart q σ 1) (W : Y.Opens) (hW : W ≤ π ⁻¹ᵁ c.U), IsAffineOpen W → ∀ n : (Σ a, Low (r a)) → Γ(Y, W), Function.Bijective (MvPolynomial.eval₂Hom (π.appLE c.U W hW).hom n) → c.e.source.Nonempty → ∃ c' : AlgChart p σ (d + 1), IsCell e π w c c' ∧ c'.e.source ⊆ ptsIn p σ W ∧ ∀ y ∈ c'.e.source, ∀ a s, fib e (c'.e y) a s = ev p σ W (n ⟨a, s⟩) y := by
  intro k _ B Y q p π w ι _ r d e σ c W hW hWa n hΦ hne
  obtain ⟨b₀, hb₀⟩ := hne
  refine ⟨cellChart π w e c hW hWa n hΦ (cellPt π w hW hWa n hΦ (c.source_subset hb₀) 0),
    ⟨rfl, rfl, fun y _ => ?_⟩, inter_subset_right, fun y _ a s => ?_⟩
  · exact base_pt e (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (n ⟨a, s⟩) y
  · exact congrFun (congrFun (fib_pt e (c.e (PtsOver.map π w (spMap σ) y)) fun a s => ev p σ W (n ⟨a, s⟩) y) a) s
