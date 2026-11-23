import Development.WeilBound.ThetaLifts.FrameEstimates.TowerRallisLemma
import Development.WeilBound.ThetaLifts.FrameEstimates.LatMeas
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsSmoothModerateOfIsAutFunSm
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen

noncomputable section

namespace PositivityTheory.ThKEst

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.SiegelSet GlobalTheory.Orb Matrix
open Formalism.UG (cT)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n r : ℕ} {J : Matrix (Fin n) (Fin n) E}

namespace CuspR

open LatticeQuotientMeasure

def rat (H : Subgroup (GL (Fin n) (AE F E))) : Subgroup H :=
  (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F))).range.subgroupOf H

theorem ratPts_eq : ratPts σ J = rat (HR (AF F) σ J) := by
  have : Nontrivial (AE F E) := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    obtain ⟨τ⟩ : Nonempty (EmbOver E w) := inferInstance
    exact ((infEmb τ).comp (compInf F E w)).domain_nontrivial
  ext g
  refine ⟨fun ⟨δ, _, hδ⟩ => ⟨δ, hδ⟩, fun ⟨δ, hδ⟩ => ⟨δ, ?_, hδ⟩⟩
  show cT (σ : E →+* E) δ.1 * J * δ.1 = J
  apply Matrix.map_injective (inclR (F := F) (E := E) (AF F)).injective
  have hg : cT (sigR (AF F) σ) (matHom _ σ J g).1 * JR (AF F) J * (matHom _ σ J g).1 = JR (AF F) J := g.2
  have e : δ.1.map (inclR (F := F) (AF F)) = (matHom _ σ J g).1 := congrArg Units.val hδ
  rw [← e] at hg
  simp only [Matrix.map_mul]
  exact hg

theorem exists_herm (h : IsCMExt F E σ) (hJ : EpsHerm σ J) : ∃ c : E, c ≠ 0 ∧ IsHermND σ (c • J.map σ) := by
  have hσ := sigma_sigma h
  have hd : ∀ c : E, c ≠ 0 → (c • J.map σ).det ≠ 0 := fun c hc => by
    have e : (J.map σ).det = σ J.det := ((σ : E →+* E).map_det _).symm
    rw [det_smul, e]
    exact mul_ne_zero (pow_ne_zero _ hc) ((map_ne_zero σ).2 hJ.2)
  rcases hJ.1 with h1 | h1
  · exact ⟨1, one_ne_zero, fun i j => by simp [h1], hd 1 one_ne_zero⟩
  · obtain ⟨x, hx⟩ : ∃ x, σ x ≠ x := by
      by_contra! hx
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      have := h.2.1
      refine IsTotallyComplex.complexEmbedding_not_isReal τ ?_
      rw [ComplexEmbedding.isReal_iff]
      ext z
      have := h.2.2.2 τ z
      rw [hx] at this
      exact this.symm
    refine ⟨σ x - x, sub_ne_zero.2 hx, fun i j => ?_, hd _ (sub_ne_zero.2 hx)⟩
    simp only [Matrix.smul_apply, map_apply, smul_eq_mul, map_mul, map_sub, hσ, h1 j i]
    ring

omit [NumberField F] [NumberField E] in
theorem gram (hσ : ∀ x, σ (σ x) = x) (c : E) (Z : Matrix (Fin n) (Fin r) E) (u : Fin n → E) (i : Fin r) :
    ((cT (σ : E →+* E) Z * (c • J.map σ)) *ᵥ u) i = c * σ (form σ J (fun k => Z k i) u) := by
  simp only [form, mulVec, dotProduct, Matrix.mul_apply, cT, transpose_apply, map_apply, Matrix.smul_apply, smul_eq_mul,
    map_sum, map_mul, hσ, RingHom.coe_coe, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] [NumberField E] in
theorem swap (hσ : ∀ x, σ (σ x) = x) (hJ : EpsHerm σ J) {x y : Fin n → E} (e : form σ J x y = 0) :
    form σ J y x = 0 := by
  have e2 := congrArg σ e
  simp only [form, mulVec, dotProduct, map_sum, map_mul, hσ, map_zero, Finset.mul_sum] at e2 ⊢
  rw [Finset.sum_comm]
  rcases hJ.1 with h1 | h1
  · rw [← e2]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by rw [h1]; ring
  · rw [← neg_zero, ← e2, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by rw [h1]; ring

omit [NumberField F] [NumberField E] in
theorem perp_span {S : Set (Fin n → E)} {z : Fin n → E} (h : ∀ u ∈ S, form σ J u z = 0) :
    ∀ u ∈ Submodule.span E S, form σ J u z = 0 := by
  intro u hu
  induction hu using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => exact zero_dotProduct _
  | add x y _ _ hx hy => rw [form, add_dotProduct]; exact (congrArg₂ (· + ·) hx hy).trans (add_zero 0)
  | smul a x _ hx => rw [form, smul_dotProduct]; exact (congrArg (a • ·) hx).trans (smul_zero a)

omit [NumberField F] [NumberField E] in
theorem perp_iff (hσ : ∀ x, σ (σ x) = x) (hJ : EpsHerm σ J) {c : E} (hc : c ≠ 0) (C : Matrix (Fin n) (Fin r) E)
    (z : Fin n → E) : (∀ u ∈ Submodule.span E (Set.range Cᵀ), form σ J z u = 0) ↔
      (cT (σ : E →+* E) C * (c • J.map σ)) *ᵥ z = 0 := by
  constructor
  · intro h
    funext i
    have e : form σ J (fun k => C k i) z = 0 := swap hσ hJ (h (Cᵀ i) (Submodule.subset_span ⟨i, rfl⟩))
    rw [gram hσ, e, map_zero, mul_zero]; rfl
  · intro h u hu
    refine swap hσ hJ (perp_span ?_ u hu)
    rintro _ ⟨i, rfl⟩
    have := (gram (J := J) hσ c C z i).symm.trans (congrFun h i)
    have e : form σ J (fun k => C k i) z = 0 := by simpa [hc] using this
    exact e

def unip (H : Subgroup (GL (Fin n) (AE F E))) (U : Submodule E (Fin n → E)) (P : (Fin n → E) → Prop) : Subgroup H :=
  Subgroup.closure {m | (∀ u ∈ U, m.1.1 *ᵥ incV F u = incV F u) ∧ ∀ z : Fin n → E, P z →
    m.1.1 *ᵥ incV F z - incV F z ∈ Submodule.span (AE F E) (incV F '' (U : Set (Fin n → E)))}

def Van {H : Subgroup (GL (Fin n) (AE F E))} (Γ N : Subgroup H) (f : H → ℂ) : Prop :=
  letI : MeasurableSpace H := borel H
  ∀ (μ : Measure N) (𝓕 : Set N), μ.IsHaarMeasure → IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ →
    ∀ h, ∫ u in 𝓕, f (u.1 * h) ∂μ = 0

def lines (H : Subgroup (GL (Fin n) (AE F E))) : Set (Multiplicative ℝ →* H) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) ((γ t).1.1 - 1)}

omit [NumberField E] in
theorem incV_mulVec (C : Matrix (Fin n) (Fin r) E) (a : Fin r → E) :
    incV F (C *ᵥ a) = adMat F C *ᵥ incV F a := funext fun i =>
  RingHom.map_mulVec (inclR (F := F) (AF F)) C a i

omit [NumberField E] in
theorem mem_cols {C : Matrix (Fin n) (Fin r) E} {u : Fin n → E} (hu : u ∈ Submodule.span E (Set.range Cᵀ)) :
    ∃ a, C *ᵥ a = u := by
  have e : LinearMap.range C.mulVecLin = Submodule.span E (Set.range Cᵀ) := Matrix.range_mulVecLin C
  rw [← e] at hu
  exact hu

omit [NumberField E] in
theorem span_eq (C : Matrix (Fin n) (Fin r) E) (x : Fin n → AE F E) :
    x ∈ Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E))) ↔
      ∃ a, x = adMat F C *ᵥ a := by
  have e : Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E))) =
      LinearMap.range (adMat F C).mulVecLin := by
    refine le_antisymm (Submodule.span_le.2 ?_) ?_
    · rintro _ ⟨u, hu, rfl⟩
      obtain ⟨a, rfl⟩ := mem_cols hu
      exact ⟨incV F a, (incV_mulVec C a).symm⟩
    · rw [Matrix.range_mulVecLin]
      refine Submodule.span_mono ?_
      rintro _ ⟨i, rfl⟩
      exact ⟨Cᵀ i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
  rw [e]
  exact ⟨fun ⟨a, ha⟩ => ⟨a, ha.symm⟩, fun ⟨a, ha⟩ => ⟨a, ha.symm⟩⟩

omit [NumberField E] in
theorem unipRad_eq (C : Matrix (Fin n) (Fin r) E) : unipRad σ J C =
    unip (HR (AF F) σ J) (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0 := by
  refine congrArg Subgroup.closure (Set.ext fun g => ?_)
  obtain ⟨m, hm⟩ : ∃ m : Matrix (Fin n) (Fin n) (AE F E), m = (matHom _ σ J g).1 := ⟨_, rfl⟩
  have hg : cT (sigR (AF F) σ) m * JR (AF F) J * m = JR (AF F) J := hm ▸ g.2
  have key : ((m - 1) * adMat F C = 0 ∧ adMat F (cT (σ : E →+* E) C * J) * (m - 1) = 0 ∧
      ∀ x : Fin n → E, (cT (σ : E →+* E) C * J) *ᵥ x = 0 → ∃ a : Fin r → AE F E, (m - 1) *ᵥ incV F x = adMat F C *ᵥ a) ↔
      ((∀ u ∈ Submodule.span E (Set.range Cᵀ), m *ᵥ incV F u = incV F u) ∧ ∀ z : Fin n → E,
        (cT (σ : E →+* E) C * J) *ᵥ z = 0 → m *ᵥ incV F z - incV F z ∈
          Submodule.span (AE F E) (incV F '' (Submodule.span E (Set.range Cᵀ) : Set (Fin n → E)))) := by
    simp only [span_eq, sub_mulVec, one_mulVec, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      sub_eq_zero]
    refine ⟨fun ⟨h1, _, h3⟩ => ⟨fun u hu => ?_, h3⟩, fun ⟨h1, h3⟩ => ?_⟩
    · obtain ⟨a, rfl⟩ := mem_cols hu
      rw [incV_mulVec, mulVec_mulVec, h1]
    · have h2 : m * adMat F C = adMat F C := Matrix.ext fun i j =>
        congrFun (h1 (Cᵀ j) (Submodule.subset_span ⟨j, rfl⟩)) i
      refine ⟨h2, ?_, h3⟩
      have e : adMat F (cT (σ : E →+* E) C * J) =
          (cT (sigR (AF F) σ) (adMat F C) * JR (F := F) (AF F) J : Matrix (Fin r) (Fin n) (AF F ⊗[F] E)) := by
        rw [adMat, Matrix.map_mul]; rfl
      rw [e]
      conv_lhs => rw [← h2, Formalism.UG.cT_mul, Matrix.mul_assoc, Matrix.mul_assoc, ← Matrix.mul_assoc (cT _ m), hg]
  subst hm
  exact key

omit [NumberField E] in
theorem idempotent_smul_eq_zero_of_map (x : AE F E) (h : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = 0) : e0 F • x = 0 := by
  have : ∀ x : AE F E, e0 F • x = LinearMap.rTensor E (show Af F →ₗ[F] AF F from LinearMap.inr F (Ainf F) (Af F))
      (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x) := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
    | tmul a y =>
      rw [TensorProduct.smul_tmul', Algebra.TensorProduct.map_tmul, LinearMap.rTensor_tmul]
      exact congrArg (· ⊗ₜ[F] y) (Prod.ext (zero_mul _) (one_mul _))
  rw [this, h, map_zero]

omit [NumberField E] in
theorem at_of_projFin {g : GAd σ J} (h : GlobalTheory.AdelicU.projFin σ J g = 1) : At (evI F) ((matHom _ σ J g).1 - 1) := by
  refine (at_iff _).2 (Matrix.ext fun i j => idempotent_smul_eq_zero_of_map _ ?_)
  have e : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) ((matHom _ σ J g).1 i j) =
      (1 : Matrix (Fin n) (Fin n) (Af F ⊗[F] E)) i j :=
    congrArg (fun y : GFin σ J => (matHom _ σ J y).1 i j) h
  rw [Matrix.sub_apply, map_sub, e, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem line_of (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    ∃ δ ∈ lines (HR (AF F) σ J), ∀ t, δ (Multiplicative.ofAdd t) = γ t := by
  obtain ⟨w, τ, Z, -, hZ⟩ := hγ
  choose y e1 e2 using hZ
  have hE := isEmbedding_archMat J h τ
  have hi : ∀ a b, archMat σ J τ a = archMat σ J τ b → a = b := fun a b e => hE.injective e
  have h0 : y 0 = 1 := hi _ _ (by rw [e2, zero_smul, NormedSpace.exp_zero, map_one])
  have h1 : ∀ s t, y (s + t) = y s * y t := fun s t => hi _ _ (by
    rw [map_mul, e2, e2, e2, add_smul]
    exact Matrix.exp_add_of_commute _ _ (((Commute.refl Z).smul_left s).smul_right t))
  have hc : Continuous y := hE.continuous_iff.2 (by
    have : (matCoord (archMat σ J τ) ∘ y) = fun t : ℝ => NormedSpace.exp (t • Z) := funext e2
    rw [this]
    haveI : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) := FiniteDimensional.complete ℝ _
    have hz : Continuous fun t : ℝ => t • Z := continuous_id.smul continuous_const
    exact (NormedSpace.exp_continuous (𝔸 := Matrix (Fin n) (Fin n) ℂ)).comp hz)
  let δ : Multiplicative ℝ →* GAd σ J :=
    { toFun := fun t => embArch σ J w (y t.toAdd)
      map_one' := by rw [toAdd_one, h0, map_one]
      map_mul' := fun s t => by rw [toAdd_mul, h1, map_mul] }
  exact ⟨δ, ⟨(continuous_embArch σ J w).comp (hc.comp continuous_toAdd),
    fun t => at_of_projFin (projFin_embArch σ J w _)⟩, fun t => (e1 t).symm⟩

theorem level (τ : ∀ w : InfinitePlace F, EmbOver E w) {f : GAd σ J → ℂ} {U : Set (GAd σ J)} (hU : U ∈ 𝓝 1)
    (hf : ∀ u ∈ U, (∀ w, (matHom _ σ J u).1.map (piInf (τ w)) = 1) → ∀ h, f (h * u) = f h) :
    ∃ U : Subgroup (GAd σ J), IsOpen (U : Set (GAd σ J)) ∧ ∀ k ∈ U, k ∈ finPts σ J → ∀ g, f (g * k) = f g := by
  haveI := GlobalTheory.Doubling.nonarchimedeanGroup_GFin σ J
  obtain ⟨V, hV⟩ := NonarchimedeanGroup.is_nonarchimedean (ofFin σ J ⁻¹' U)
    ((continuous_ofFin σ J).continuousAt.preimage_mem_nhds (by rwa [map_one]))
  refine ⟨V.1.comap (GlobalTheory.AdelicU.projFin σ J), V.isOpen.preimage (continuous_projFin σ J), fun k hk hk' => hf k ?_ fun w => ?_⟩
  · have := ofInf_projInf_mul_ofFin_projFin σ J k
    rw [mem_finPts.1 hk', map_one, one_mul] at this
    rw [← this]
    exact hV hk
  · change archMat σ J (τ w) (projArch σ J w k) = 1
    rw [← projInfArch_projInf, mem_finPts.1 hk', map_one, map_one]

def linesG (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E) : Set (Multiplicative ℝ →* GAd σ J) := lines (HR (AF F) σ J)

theorem line_ofG (h : IsCMExt F E σ) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    ∃ δ ∈ linesG σ J, γ = fun t => δ (Multiplicative.ofAdd t) :=
  let ⟨δ, a, b⟩ := line_of h hγ
  ⟨δ, a, funext fun t => (b t).symm⟩

theorem moderate (h : IsCMExt F E σ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (f : GAd σ J → ℂ)
    (h1 : ∀ γ ∈ ratPts σ J, ∀ g, f (γ * g) = f g)
    (h2 : ∃ (k : ℕ) (S : Set (GAd σ J → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧
      (∃ C : ℝ, ∀ g, ‖f₁ g‖ ≤ C * (height σ J g : ℝ) ^ k) ∧
      ∀ γ ∈ linesG σ J, ∃ f₂ ∈ S, ∀ g, HasDerivAt (fun t : ℝ => f₁ (g * γ (Multiplicative.ofAdd t))) (f₂ g) 0)
    (h3 : ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* GAd σ J)), (∀ i, γ i ∈ linesG σ J) → ∀ g,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod))
    (h4 : ∃ U ∈ 𝓝 (1 : GAd σ J), ∀ u ∈ U, (∀ w, (matHom _ σ J u).1.map (piInf (τ w)) = 1) → ∀ g, f (g * u) = f g) :
    IsSmoothModerate σ J f := by
  obtain ⟨k, S, hf, hSS⟩ := h2
  obtain ⟨U, hU, hU'⟩ := h4
  refine ⟨h1, level τ hU hU', (hSS f hf).1, fun k γ hγ g => ?_, k, fun l hl => ?_⟩
  · choose δ hδ e using fun i => line_ofG h (hγ i)
    obtain rfl : γ = fun i t => δ i (Multiplicative.ofAdd t) := funext e
    exact h3 k δ hδ g
  · have : l.foldr lineDer f ∈ S := by
      induction l with
      | nil => exact hf
      | cons γ l ih =>
        obtain ⟨δ, hδ, e⟩ := line_ofG h (hl γ List.mem_cons_self)
        obtain ⟨f₂, a1, a2⟩ := (hSS _ (ih fun β hβ => hl β (List.mem_cons_of_mem _ hβ))).2.2 δ hδ
        have e2 : lineDer γ (l.foldr lineDer f) = f₂ := funext fun g => by
          rw [e]
          exact (a2 g).deriv
        rw [List.foldr_cons, e2]
        exact a1
    exact (hSS _ this).2.1

theorem cuspidal (f : GAd σ J → ℂ)
    (h5 : ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E Cᵀ → cT (σ : E →+* E) C * J * C = 0 →
      Van (rat (HR (AF F) σ J))
        (unip (HR (AF F) σ J) (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0) f) :
    IsCuspidal σ J f := fun r C hC => by
  have := h5 r C hC.1 hC.2.1 hC.2.2
  rw [← unipRad_eq, ← ratPts_eq] at this
  exact this

theorem rapidG (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J) (f : GAd σ J → ℂ)
    (hm : IsSmoothModerate σ J f) (hc : IsCuspidal σ J f) (N : ℕ) :
    ∃ C : ℝ, ∀ g, ∃ γ ∈ ratPts σ J, ‖f g‖ * (height σ J (γ * g) : ℝ) ^ N ≤ C := by
  obtain ⟨S₀, -, hcov, -, -, hφ⟩ := exists_cover hS h hJ
  obtain ⟨C, hC⟩ := (hφ f hm hc N).1
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, s, hs, rfl⟩ := hcov g
  refine ⟨γ⁻¹, inv_mem hγ, ?_⟩
  rw [inv_mul_cancel_left, hm.left γ hγ]
  exact hC s hs

theorem core (hS : GlobalTheory.Published.SiegelSetUnitary) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (H : Subgroup (GL (Fin n) (AE F E))) (hH : H = HR (AF F) σ J) (f : H → ℂ)
    (h1 : ∀ γ ∈ rat H, ∀ g, f (γ * g) = f g)
    (h2 : ∃ (k : ℕ) (S : Set (H → ℂ)), f ∈ S ∧ ∀ f₁ ∈ S, Continuous f₁ ∧ (∃ C : ℝ, ∀ g, ‖f₁ g‖ ≤ C * (heightGL F g.1 : ℝ) ^ k) ∧
      ∀ γ ∈ lines H, ∃ f₂ ∈ S, ∀ g, HasDerivAt (fun t : ℝ => f₁ (g * γ (Multiplicative.ofAdd t))) (f₂ g) 0)
    (h3 : ∀ (k : ℕ) (γ : Fin k → (Multiplicative ℝ →* H)), (∀ i, γ i ∈ lines H) → ∀ g, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (Multiplicative.ofAdd (t i))).prod))
    (h4 : ∃ U ∈ 𝓝 (1 : H), ∀ u ∈ U, (∀ w, u.1.1.map (piInf (τ w)) = 1) → ∀ g, f (g * u) = f g)
    (h5 : ∀ (r : ℕ) (C : Matrix (Fin n) (Fin r) E), 0 < r → LinearIndependent E Cᵀ → cT (σ : E →+* E) C * J * C = 0 →
      Van (rat H) (unip H (Submodule.span E (Set.range Cᵀ)) fun z => (cT (σ : E →+* E) C * J) *ᵥ z = 0) f)
    (N : ℕ) : ∃ C : ℝ, ∀ g, ∃ γ ∈ rat H, ‖f g‖ * (heightGL F (γ * g).1 : ℝ) ^ N ≤ C := by
  subst hH
  have h6 := cuspidal f h5
  rw [← ratPts_eq] at h1 ⊢
  exact rapidG hS h hJ f (moderate h τ f h1 h2 h3 h4) h6 N

end CuspR

open CuspR in
theorem cuspRapid_of (hS : GlobalTheory.Published.SiegelSetUnitary) (hU : UMGSmooth) : CuspRapid := by
  intro F E _ _ _ _ _ σ h τ d W hJ f h1 h2 h4 h5 N
  have hσ := sigma_sigma h
  obtain ⟨c, hc, hJ'⟩ := exists_herm h hJ
  obtain ⟨C, hC⟩ := core hS h hJ' τ (UG (cA σ) (incM F W.J)) (ug_eq_hr hσ hc) f h1 h2 (hU F E σ h τ d W hJ f h2) h4
    (fun r C hr hl hi => by
      have e : (fun z => (cT (σ : E →+* E) C * (c • W.J.map σ)) *ᵥ z = 0) =
          fun z => ∀ u ∈ Submodule.span E (Set.range Cᵀ), form σ W.J z u = 0 :=
        funext fun z => propext (perp_iff hσ hJ hc C z).symm
      rw [e]
      refine h5 _ (fun h0 => ?_) fun u hu => (perp_iff hσ hJ hc C u).2 ?_
      · exact hl.ne_zero ⟨0, hr⟩ ((Submodule.eq_bot_iff _).1 h0 _ (Submodule.subset_span ⟨_, rfl⟩))
      · obtain ⟨a, rfl⟩ := mem_cols hu
        rw [mulVec_mulVec, hi, zero_mulVec]) N
  refine ⟨C, fun g => ?_⟩
  obtain ⟨γ, hγ, e⟩ := hC g
  refine le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ N) (norm_nonneg _)) e
  exact NNReal.coe_le_coe.2 (ciInf_le' (fun γ : ratU σ W.J => ht (γ.1 * g)) ⟨γ, hγ⟩)

end PositivityTheory.ThKEst

end
