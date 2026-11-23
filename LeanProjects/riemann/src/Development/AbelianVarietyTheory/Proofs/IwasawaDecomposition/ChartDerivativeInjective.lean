import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ToroidalCompactificationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvaluationHolomorphicOnFramesStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatrixFamilyCriticalRowsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodTransformationUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisDeterminantUnitStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FrameMoebiusRowRelationStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformizedFamilyChartIndexStatement

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.ShFam
open Formalism.DegreeFormula Formalism.MJ GlobalTheory.HodgeDomain GlobalTheory.TrueCx
open scoped ComplexOrder ContDiff

namespace GlobalTheory.ShFam.Imm

open ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up

section Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r) (ψ : X.Ψ)

def wv (v : Fin r → E) : Fin j ⊕ Fin (r - j) → ℂ :=
  fun m => ((mat (x0F X) ψ)⁻¹.mulVec (Data.emb ψ.1 v)) ((idx hj).symm m)

def wm (c : Fin r → Fin r → E) : Matrix (Fin j ⊕ Fin (r - j)) (Fin r) ℂ :=
  Matrix.of fun m l => wv X hj ψ (c l) m

theorem wm_eq (c : Fin r → Fin r → E) : wm X hj ψ c =
    ((mat (x0F X) ψ)⁻¹ * Matrix.of fun m l => ψ.1 (c l m)).submatrix (idx hj).symm id := rfl

end Frames

section Periods

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r)
  (hp : X.p0 = r - j) (ψ : X.Ψ) (Dd : Datum H) (φ : Dd.La ≃ₗ[𝓞 E] X.Λ) {g : ℕ} (ty : Fin g → (E →+* ℂ))
  (ρ : Fin j → Fin g)

include hp in

theorem period_rel (hρ : Function.Injective ρ) (hty : ∀ i, ty i = ψ.1 ↔ i ∈ Set.range ρ) {x : Frame X.Ψ r}
    (hx : x ∈ X.dom) (hi : ∀ a : Fin j, X.p0 + (a : ℕ) < r) (Pm Q : Dd.La →+ (Fin g → ℂ)) (hPm : IsPeriod Dd ty Pm)
    (hQ : IsPeriod Dd ty Q)
    (hval : ∀ b (a : Fin j), Pm b (ρ a) = ((mat x ψ)⁻¹.mulVec (Data.emb ψ.1 (φ b : Fin r → E))) ⟨X.p0 + a, hi a⟩)
    (gam : Dd.La ≃ₗ[𝓞 E] Dd.La) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)) (e : ∀ a, Q (gam a) = h (Pm a)) :
    ∃ (Hm : Matrix (Fin j) (Fin j) ℂ) (R : Matrix (Fin j) (Fin j ⊕ Fin (r - j)) ℂ), IsUnit Hm ∧
      R * Matrix.fromRows (moeb (frameCo X hj x ψ) 0) (1 : Matrix (Fin (r - j)) (Fin (r - j)) ℂ) = 0 ∧
      (∃ Rr : Matrix (Fin j ⊕ Fin (r - j)) (Fin j) ℂ, R * Rr = 1) ∧
      ∀ c : Fin r → Dd.La, (Matrix.of fun a l => Q (c l) (ρ a)) =
        (Hm * R) * wm X hj ψ fun l => (φ (gam.symm (c l)) : Fin r → E) := by
  obtain ⟨Hm, hHm, hb⟩ := GlobalTheory.T.period_transformation_unitary E H Dd g j ty ψ.1 ρ hρ hty Pm Q hPm hQ gam h e
  obtain ⟨R, h1, h2, h3⟩ := GlobalTheory.T.frame_moebius_row_relation E r X j hj hp x hx ψ
  refine ⟨Hm, R, hHm, h1, h2, fun c => ?_⟩
  ext a l
  have e1 : Q (c l) = h (Pm (gam.symm (c l))) := by rw [← e, LinearEquiv.apply_symm_apply]
  have e2 : ∀ b', Pm (gam.symm (c l)) (ρ b') = (R.mulVec (wv X hj ψ (φ (gam.symm (c l)) : Fin r → E))) b' := fun b' => by
    rw [hval, h3 _ _ (hi b')]
    rfl
  rw [Matrix.of_apply, e1, hb]
  simp only [e2]
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b' _ => ?_
  rfl

end Periods

section Inverse

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r) {j : ℕ} (hj : j ≤ r) (ψ : X.Ψ)

def wi (c : Fin r → Fin r → E) : Matrix (Fin r) (Fin j ⊕ Fin (r - j)) ℂ :=
  (((mat (x0F X) ψ)⁻¹ * Matrix.of fun m l => ψ.1 (c l m))⁻¹).submatrix id (idx hj).symm

theorem wm_mul_wi {c₀ c : Fin r → Fin r → E} (h₀ : IsUnit (Matrix.of fun m l => ψ.1 (c₀ l m) : Matrix (Fin r) (Fin r) ℂ).det)
    (h : IsUnit (Matrix.of fun m l => ψ.1 (c l m) : Matrix (Fin r) (Fin r) ℂ).det) :
    IsUnit (wm X hj ψ c * wi X hj ψ c₀) ∧ (c = c₀ → wm X hj ψ c * wi X hj ψ c₀ = 1) := by
  have hx : IsUnit (mat (x0F X) ψ)⁻¹.det := isUnit_nonsing_inv_det _ (det_x0F X ψ).isUnit
  set U₀ := (mat (x0F X) ψ)⁻¹ * (Matrix.of fun m l => ψ.1 (c₀ l m) : Matrix (Fin r) (Fin r) ℂ) with hU₀
  set U := (mat (x0F X) ψ)⁻¹ * (Matrix.of fun m l => ψ.1 (c l m) : Matrix (Fin r) (Fin r) ℂ) with hU
  have d₀ : IsUnit U₀.det := by rw [hU₀, det_mul]; exact hx.mul h₀
  have d : IsUnit U.det := by rw [hU, det_mul]; exact hx.mul h
  have e : wm X hj ψ c * wi X hj ψ c₀ = (U * U₀⁻¹).submatrix (idx hj).symm (idx hj).symm := by
    rw [wm_eq, wi, ← hU, ← hU₀]
    exact (submatrix_mul _ _ _ id _ Function.bijective_id).symm
  rw [e]
  refine ⟨?_, fun hc => ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, det_submatrix_equiv_self, det_mul]
    exact d.mul (isUnit_nonsing_inv_det _ d₀)
  · have : U = U₀ := by rw [hU, hU₀, hc]
    rw [this, mul_nonsing_inv _ d₀, submatrix_one_equiv]

end Inverse

section Main

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)

theorem chart_reg (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim) :
    ∃ T : Set (D.what₂.Tau × Fin j × Fin (N - j) → ℂ), IsOpen T ∧
      (∀ v ∈ T, unflat v ∈ DomI D.what₂.Tau j (N - j) ∧ s.toCpt L k (unflat v) ∈ c.e.source) ∧
      DifferentiableOn ℂ (fun v => c.e (s.toCpt L k (unflat v))) T ∧
      ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ c.e.source → flat z ∈ T := by
  let sp : (D.what₂.Tau × Fin j × Fin (N - j) → ℂ) → CxPts (genStr s.T.Z) κ.σ₀ := fun v => s.toCpt L k (unflat v)
  have hI := fun f => GlobalTheory.T.evaluation_holomorphic_on_frames D A N j S κ s L k c.U f
  have hT := (hI 0).1
  obtain ⟨hc, -⟩ := holo_of_affine c.affine hT (s := sp) (fun v hv => hv.2) (fun a => (hI a).2)
  refine ⟨_ ∩ sp ⁻¹' c.e.source, hc.isOpen_inter_preimage hT c.e.open_source, fun v hv => ⟨hv.1.1, hv.2⟩, ?_, ?_⟩
  · exact differentiableOn_euclidean.2 fun a => ((hI (c.x a)).2.mono Set.inter_subset_left).congr
      fun v hv => c.apply_eq _ hv.2 a
  · intro z hz hs
    have e : unflat (flat z) = z := rfl
    exact ⟨⟨by simpa [DomFlat, e] using hz, by simpa [sp, e] using c.source_subset hs⟩, by simpa [sp, e] using hs⟩

theorem immersion : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (k : s.Comp)
    (c : AlgChart (genStr s.T.Z) κ.σ₀ S.Dw.dim), ∀ z ∈ DomI D.what₂.Tau j (N - j), s.toCpt L k z ∈ c.e.source →
    Function.Injective (fderiv ℂ (fun v => c.e (s.toCpt L k (unflat v))) (flat z)) := by
  intro D A N j S κ s L k c z hz hsrc
  classical
  obtain ⟨-, hΨ, -, -, -, g, e, Fu, ik, φ, -, hPm⟩ := s.isUnf
  obtain ⟨T, hT, hTm, hTd, hT0⟩ := chart_reg s L k c
  have hv₀ := hT0 z hz hsrc
  obtain ⟨i, B, P, hB, hb₀, hBt, hBP, hBd, hBu⟩ := GlobalTheory.T.uniformized_family_chart_index _ _ _ _ _ _ _ _ s.T.Z κ.σ₀ S.Dw.dim g _ Fu c
    ((s.U κ.σ₀).un k (s.frameOver L k z)) hsrc
  let Fn : (D.what₂.Tau × Fin j × Fin (N - j) → ℂ) → ReciprocityTheory.L2DbarEstimates.V S.Dw.dim := fun v => c.e (s.toCpt L k (unflat v))
  have hT₂ : IsOpen (T ∩ Fn ⁻¹' B) := hTd.continuousOn.isOpen_inter_preimage hT hB
  have hv₂ : flat z ∈ T ∩ Fn ⁻¹' B := ⟨hv₀, hb₀⟩
  have key : ∀ v ∈ T ∩ Fn ⁻¹' B, Fu.u i (P (Fn v)) = ((s.U κ.σ₀).un k (s.frameOver L k (unflat v))).x := fun v hv =>
    hBu _ hv.2 _ (c.e.left_inv (hTm v hv.1).2)
  obtain ⟨Pm₀, -, hper₀, hx₀, -⟩ := hPm k (s.frameOver L k z)
  obtain rfl : i = ik k := Fu.disj i (ik k) (P (Fn (flat z))) Pm₀ (hBP _ hb₀) hper₀ ((key _ hv₂).trans hx₀)
  rw [show (fun v => c.e (s.toCpt L k (unflat v))) = Fn from rfl]
  refine (injective_iff_map_eq_zero _).2 fun w' hw' => ?_
  have hj := s.j_le
  have hp := s.p0_eq k
  have hFd : HasFDerivAt Fn (fderiv ℂ Fn (flat z)) (flat z) :=
    ((hTd.differentiableAt (hT.mem_nhds hv₀))).hasFDerivAt
  suffices hmain : ∀ t0 : D.what₂.Tau, unflat w' t0 = 0 by
    funext ⟨t0, a, b⟩
    exact congrFun (congrFun (hmain t0) a) b
  intro t0
  let X := s.fd k
  let ψ : X.Ψ := s.lab L k t0
  have hψ : ψ.1 ((A.H.rt : D.host.E)) = A.H.rt0 := (((hΨ k).2 ψ.1).1 ψ.2)
  have hmult : S.Dw.mult ψ.1 = j := by rw [Datum.mult, if_pos hψ]; exact S.p_eq
  let ρ : Fin j → Fin g := fun a => e.symm ⟨ψ.1, Fin.cast hmult.symm a⟩
  have hρ : Function.Injective ρ := fun a b h => by
    have := e.symm.injective h
    simpa [Fin.ext_iff] using this
  let ty : Fin g → (D.host.E →+* ℂ) := fun j' => Formalism.L2.PjFree.relab κ.c κ.σ₀ (e j').1
  have he : ∀ a, e (ρ a) = ⟨ψ.1, Fin.cast hmult.symm a⟩ := fun a => e.apply_symm_apply _
  have he1 : ∀ a, (e (ρ a)).1 = ψ.1 := fun a => congrArg Sigma.fst (he a)
  have he2 : ∀ a, ((e (ρ a)).2 : ℕ) = a := fun a => by
    have := congrArg (fun x : (τ : D.host.E →+* ℂ) × Fin (S.Dw.mult τ) => (x.2 : ℕ)) (he a)
    simpa using this
  have hty : ∀ i', ty i' = ψ.1 ↔ i' ∈ Set.range ρ := fun i' => by
    constructor
    · intro h
      have h' : (e i').1 = ψ.1 := h
      rcases he' : e i' with ⟨τ', b⟩
      rw [he'] at h'
      dsimp only at h'
      subst h'
      refine ⟨Fin.cast hmult b, ?_⟩
      show e.symm _ = i'
      rw [Equiv.symm_apply_eq, he']
      simp
    · rintro ⟨a, rfl⟩
      exact he1 a
  have hi : ∀ a : Fin j, X.p0 + (a : ℕ) < N := fun a => by
    have := a.2
    have : X.p0 = N - j := hp
    omega
  have hval : ∀ (f : X.dom) (Pm : (Fu.Di (ik k)).La →+ (Fin g → ℂ)),
      (∀ a j', Pm a j' = perFr X f.1 (φ k a : Fin N → D.host.E) (Formalism.L2.PjFree.relab κ.c κ.σ₀ (e j').1) (e j').2) →
      ∀ b (a : Fin j), Pm b (ρ a) =
        ((mat f.1 ψ)⁻¹.mulVec (Data.emb ψ.1 (φ k b : Fin N → D.host.E))) ⟨X.p0 + a, hi a⟩ := fun f Pm h b a => by
    rw [h, Lv.relab_σ₀, he2, he1, perFr, dif_pos ψ.2, dif_pos (hi a)]
  let Fl : ℂ → (D.what₂.Tau × Fin j × Fin (N - j) → ℂ) := fun t => flat z + t • w'
  have hFl : Continuous Fl := by fun_prop
  have hFl0 : Fl 0 = flat z := by simp [Fl]
  obtain ⟨r, hr, hball⟩ : ∃ r > 0, Metric.ball (0 : ℂ) r ⊆ Fl ⁻¹' (T ∩ Fn ⁻¹' B) :=
    Metric.isOpen_iff.1 (hT₂.preimage hFl) 0 (by rw [Set.mem_preimage, hFl0]; exact hv₂)
  have hFlD : Differentiable ℂ Fl := by fun_prop

  have hfr : ∀ t ∈ Metric.ball (0 : ℂ) r, ∃ (gam : (Fu.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (Fu.Di (ik k)).La)
      (Hm : Matrix (Fin j) (Fin j) ℂ) (R : Matrix (Fin j) (Fin j ⊕ Fin (N - j)) ℂ), IsUnit Hm ∧
      R * Matrix.fromRows (z t0 + t • unflat w' t0) (1 : Matrix (Fin (N - j)) (Fin (N - j)) ℂ) = 0 ∧
      (∃ Rr : Matrix (Fin j ⊕ Fin (N - j)) (Fin j) ℂ, R * Rr = 1) ∧
      ∀ c : Fin N → (Fu.Di (ik k)).La, (Matrix.of fun a l => P (Fn (Fl t)) (c l) (ρ a)) =
        (Hm * R) * wm X hj ψ fun l => (φ k (gam.symm (c l)) : Fin N → D.host.E) := fun t ht => by
    have hv := hball ht
    obtain ⟨Pm, hv1, hper, hx, -⟩ := hPm k (s.frameOver L k (unflat (Fl t)))
    obtain ⟨gam, h, -, -, -, hg⟩ := (Fu.fibre (ik k) Pm (P (Fn (Fl t))) hper (hBP _ hv.2)).1 (hx.symm.trans (key _ hv).symm)
    obtain ⟨Hm, R, h1, h2, h3, h4⟩ := period_rel X hj hp ψ (Fu.Di (ik k)) (φ k) ty ρ hρ hty
      (s.frameOver L k (unflat (Fl t))).2 hi Pm (P (Fn (Fl t))) hper (hBP _ hv.2) (hval _ _ hv1) gam h hg
    refine ⟨gam, Hm, R, h1, ?_, h3, h4⟩
    have e1 : moeb (frameCo X hj (s.frameOver L k (unflat (Fl t))).1 ψ) 0 = z t0 + t • unflat w' t0 :=
      congrFun (s.zOf_frameOver L k (hTm _ hv.1).1) t0
    rwa [e1] at h2
  obtain ⟨a, ha⟩ := GlobalTheory.T.lattice_basis_determinant_unit D.host.E N (Fu.Di (ik k)).La X.Λ X.Λ_span (φ k)
  have : Countable D.host.E := (Module.finBasis ℚ D.host.E).equivFun.injective.countable
  have : Countable (Fu.Di (ik k)).La := (φ k).injective.countable
  let c₀ : Fin N → Fin N → D.host.E := fun l => (φ k (a l) : Fin N → D.host.E)
  let Wi := wi X hj ψ c₀
  have hunit : ∀ δ : (Fu.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (Fu.Di (ik k)).La,
      IsUnit (wm X hj ψ (fun l => (φ k (δ (a l)) : Fin N → D.host.E)) * Wi) := fun δ =>
    (wm_mul_wi X hj ψ (ha (LinearEquiv.refl _ _) ψ.1) (ha δ ψ.1)).1
  have hone : wm X hj ψ c₀ * Wi = 1 := (wm_mul_wi X hj ψ (ha (LinearEquiv.refl _ _) ψ.1) (ha (LinearEquiv.refl _ _) ψ.1)).2 rfl
  let ι := {bv : Fin N → (Fu.Di (ik k)).La // ∃ gam : (Fu.Di (ik k)).La ≃ₗ[𝓞 D.host.E] (Fu.Di (ik k)).La,
    bv = fun l => gam (a l)}
  let M : ι → ℂ → Matrix (Fin j) (Fin j ⊕ Fin (N - j)) ℂ := fun bv t =>
    (Matrix.of fun a' l => P (Fn (Fl t)) (bv.1 l) (ρ a')) * Wi
  have hdl : ∀ x, DifferentiableOn ℂ (fun t => P (Fn (Fl t)) x) (Metric.ball 0 r) := fun x =>
    (hBd x).comp (hTd.comp hFlD.differentiableOn fun t ht => (hball ht).1) fun t ht => (hball ht).2
  have hdz : ∀ x, HasDerivAt (fun t => P (Fn (Fl t)) x) 0 0 := fun x => by
    have h1 : HasDerivAt Fl w' 0 := by
      simpa [Fl] using ((hasDerivAt_id (0 : ℂ)).smul_const w').const_add (flat z)
    have h2 : HasDerivAt (fun t => Fn (Fl t)) 0 0 := by
      have := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) hFd h1 hFl0.symm
      rwa [hw'] at this
    have h3 := ((hBd x).differentiableAt (hB.mem_nhds hb₀)).hasFDerivAt
    have h4 := HasFDerivAt.comp_hasDerivAt_of_eq (0 : ℂ) h3 h2 (by simp only [hFl0]; rfl)
    rw [map_zero] at h4
    exact h4
  refine GlobalTheory.T.matrix_family_critical_rows j (N - j) ι r hr (z t0) (unflat w' t0) M ?_ ?_ ?_ ?_
  · intro bv a' b
    simp only [M, Matrix.mul_apply, Matrix.of_apply]
    exact DifferentiableOn.fun_sum fun l _ => ((differentiableOn_pi.1 (hdl _)) (ρ a')).mul_const _
  · intro bv a' b
    have h := HasDerivAt.fun_sum (u := Finset.univ) fun l _ =>
      ((hasDerivAt_pi.1 (hdz (bv.1 l))) (ρ a')).mul_const (Wi l b)
    simpa [M, Matrix.mul_apply] using h.deriv
  · intro t ht
    obtain ⟨gam, Hm, R, -, h2, -, h4⟩ := hfr t ht
    refine ⟨⟨fun l => gam (a l), gam, rfl⟩, ?_⟩
    show (Matrix.of fun a' l => P (Fn (Fl t)) (gam (a l)) (ρ a')) * Wi * _ = 0
    rw [h4]
    simp only [LinearEquiv.symm_apply_apply]
    rw [Matrix.mul_assoc (Hm * R), hone, Matrix.mul_one, Matrix.mul_assoc, h2, Matrix.mul_zero]
  · rintro ⟨_, γ, rfl⟩
    obtain ⟨gam, Hm, R, h1, -, ⟨Rr, hRr⟩, h4⟩ := hfr 0 (Metric.mem_ball_self hr)
    have hG := hunit (γ.trans gam.symm)
    obtain ⟨G, hGd⟩ : ∃ G, G = wm X hj ψ (fun l => (φ k ((γ.trans gam.symm) (a l)) : Fin N → D.host.E)) * Wi := ⟨_, rfl⟩
    rw [← hGd] at hG
    have hGi : G * G⁻¹ = 1 := mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hG)
    have hHi : Hm * Hm⁻¹ = 1 := mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 h1)
    refine ⟨G⁻¹ * Rr * Hm⁻¹, ?_⟩
    show (Matrix.of fun a' l => P (Fn (Fl 0)) (γ (a l)) (ρ a')) * Wi * _ = 1
    rw [h4, Matrix.mul_assoc (Hm * R)]
    have e2 : wm X hj ψ (fun l => (φ k (gam.symm (γ (a l))) : Fin N → D.host.E)) * Wi = G := hGd.symm
    rw [e2]
    calc Hm * R * G * (G⁻¹ * Rr * Hm⁻¹) = Hm * (R * ((G * G⁻¹) * Rr)) * Hm⁻¹ := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hGi, Matrix.one_mul, hRr, Matrix.mul_one, hHi]

end Main

end GlobalTheory.ShFam.Imm
