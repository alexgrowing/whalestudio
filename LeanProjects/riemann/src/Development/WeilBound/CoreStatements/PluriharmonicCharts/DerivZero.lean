import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.OmHeightslockG
import Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsPeriodOfFrames
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HolDifferentiableAt

open AlgebraicGeometry CategoryTheory NumberField Matrix ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Top GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.BMx ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped ComplexOrder

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory.PeriodChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {g : ℕ}

theorem mat_uniq {a b : Matrix (Fin g) (Fin g) ℂ} (h : ∀ z : Fin g → ℂ, a *ᵥ z + b *ᵥ star z = 0) : a = 0 ∧ b = 0 := by
  have key : ∀ i k, a i k = 0 ∧ b i k = 0 := fun i k => by
    have h1 := congrFun (h (Pi.single k 1)) i
    have h2 := congrFun (h (Complex.I • Pi.single k 1)) i
    simp only [star_smul, star_single, Matrix.mulVec_smul] at h1 h2
    simp at h1 h2
    constructor
    · linear_combination (1 / 2 : ℂ) * h1 - (Complex.I / 2) * h2 + (a i k - b i k) / 2 * Complex.I_mul_I
    · linear_combination (1 / 2 : ℂ) * h1 + (Complex.I / 2) * h2 - (a i k - b i k) / 2 * Complex.I_mul_I
  exact ⟨Matrix.ext fun i k => (key i k).1, Matrix.ext fun i k => (key i k).2⟩

theorem mat_ext {Λ : Type} {P : Λ → Fin g → ℂ} (hs : Submodule.span ℝ (Set.range P) = ⊤)
    {a b a' b' : Matrix (Fin g) (Fin g) ℂ} (h : ∀ x, a *ᵥ P x + b *ᵥ star (P x) = a' *ᵥ P x + b' *ᵥ star (P x)) :
    a = a' ∧ b = b' := by
  rw [← sub_eq_zero, ← sub_eq_zero (a := b)]
  refine mat_uniq fun z => ?_
  have hz : z ∈ Submodule.span ℝ (Set.range P) := hs ▸ Submodule.mem_top
  induction hz using Submodule.span_induction with
  | mem x hx => obtain ⟨x, rfl⟩ := hx; simp only [Matrix.sub_mulVec]; linear_combination h x
  | zero => simp
  | add x y _ _ hx hy => simp only [star_add, Matrix.mulVec_add]; linear_combination hx + hy
  | smul r x _ hx => rw [star_smul, star_trivial, Matrix.mulVec_smul, Matrix.mulVec_smul, ← smul_add, hx, smul_zero]

theorem dM_congr {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X] {I J : Type} {A B : X → Matrix I J ℂ} {u : X}
    (h : ∀ᶠ x in nhds u, A x = B x) (v : X) : dM A u v = dM B u v := by
  ext a b
  have : (fun x => A x a b) =ᶠ[nhds u] fun x => B x a b := h.mono fun x hx => by simp only [hx]
  simp only [dM, Matrix.of_apply, this.fderiv_eq]

theorem deriv_zero {D : Datum H} {l : Level H} {Xo : Moduli D l} {σ : KA l →+* ℂ} {ty : Fin g → (E →+* ℂ)}
    (FU : FamilyUnif Xo σ ty) (i : Fin FU.n) {n : ℕ} {B : Set (Fin n → ℂ)} (hB : IsOpen B) (h0 : 0 ∈ B)
    {P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ))} (hP : IsHolPeriods (FU.Di i) ty B P) (v : Fin n → ℂ) :
    ∃ α β : Matrix (Fin g) (Fin g) ℂ,
      (∀ x, fderiv ℂ (fun u => P u x) 0 v = α *ᵥ P 0 x + β *ᵥ star (P 0 x)) ∧
      (∀ i k, ty i ≠ ty k → α i k = 0) ∧ (∀ i k, ty i ≠ ComplexEmbedding.conjugate (ty k) → β i k = 0) ∧
      ((∀ i k, ty i (H.rt : E) = H.rt0 → β i k = 0) → ∀ (U : Xo.X.Opens) (f : Γ(Xo.X, U)),
        ⊤ ≤ FU.u i (P 0) ⁻¹ᵁ U → fderiv ℂ (fun u => valAt' (FU.u i (P u)) U f) 0 v = 0) := by
  classical
  have hn : B ∈ nhds (0 : Fin n → ℂ) := hB.mem_nhds h0
  obtain ⟨hl, hi, hd, hs, G, hG, hp, hE⟩ := hP.1 0 h0
  have hblock := herm_block (hP.1 0 h0) hE
  rw [lin_iff] at hl
  simp only [← sesq_apply] at hp hE
  have hex : ∀ u, ∃ (Z : Matrix (Fin g) (Fin g) ℂ) (h : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ)), u ∈ B →
      (∀ a z, anti Z (dg ty a *ᵥ z) = dg ty a *ᵥ anti Z z) ∧ (∀ z w, sesq G (anti Z z) w = sesq G (anti Z w) z) ∧
      (∀ z, z ≠ 0 → (sesq G (anti Z z) (anti Z z)).re < (sesq G z z).re) ∧
      ∀ x, P u x = h (P 0 x + anti Z (P 0 x)) := fun u => by
    by_cases hu : u ∈ B
    · obtain ⟨Z, h, hh⟩ := exists_contraction (P 0) hl hi hd hs G hp hE (P u) (hP.1 u hu)
      exact ⟨Z, h, fun _ => hh⟩
    · exact ⟨0, LinearEquiv.refl _ _, fun h => absurd h hu⟩
  choose Z h hZ using hex
  let a : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun u => LinearMap.toMatrix' (h u).toLinearMap
  have ha : ∀ u z, a u *ᵥ z = h u z := fun u z => LinearMap.toMatrix'_mulVec _ _
  have had : ∀ u, (a u).det ≠ 0 := fun u e => by
    obtain ⟨y, hy0, hy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 e
    exact hy0 ((h u).injective (by rw [← ha, hy, map_zero]))
  let b : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun u => a u * Z u
  have hab : ∀ u ∈ B, ∀ x, P u x = a u *ᵥ P 0 x + b u *ᵥ star (P 0 x) := fun u hu x => by
    rw [(hZ u hu).2.2.2, ← ha, Matrix.mulVec_add, anti_apply, Matrix.mulVec_mulVec]
  have hT : ∀ z, DifferentiableOn ℂ (fun u => a u *ᵥ z + b u *ᵥ star z) B := fun z => by
    have hz : z ∈ Submodule.span ℝ (Set.range (P 0)) := hs ▸ Submodule.mem_top
    induction hz using Submodule.span_induction with
    | mem x hx => obtain ⟨x, rfl⟩ := hx; exact (hP.2 x).congr fun u hu => (hab u hu x).symm
    | zero => simpa using differentiableOn_const _
    | add x y _ _ hx hy =>
      exact (hx.add hy).congr fun u _ => by simp only [star_add, Matrix.mulVec_add, Pi.add_apply]; abel
    | smul r x _ hx =>
      exact (hx.const_smul (r : ℂ)).congr fun u _ => by
        simp only [star_smul, star_trivial, Matrix.mulVec_smul, Pi.smul_apply, smul_add, Complex.coe_smul]
  have hab' : ∀ j k, DifferentiableOn ℂ (fun u => a u j k) B ∧ DifferentiableOn ℂ (fun u => b u j k) B := by
    intro j k
    have h1 := differentiableOn_pi.1 (hT (Pi.single k 1)) j
    have h2 := differentiableOn_pi.1 (hT (Complex.I • Pi.single k 1)) j
    simp only [star_smul, star_single, Matrix.mulVec_smul] at h1 h2
    constructor
    · refine ((h1.const_mul (1 / 2)).sub (h2.const_mul (Complex.I / 2))).congr fun u _ => ?_
      simp
      linear_combination (a u j k - b u j k) / 2 * Complex.I_mul_I
    · refine ((h1.const_mul (1 / 2)).add (h2.const_mul (Complex.I / 2))).congr fun u _ => ?_
      simp
      linear_combination -(a u j k - b u j k) / 2 * Complex.I_mul_I
  have hA : HolM B a := fun j k => (hab' j k).1
  have hb : HolM B b := fun j k => (hab' j k).2
  obtain ⟨a0, b0⟩ : a 0 = 1 ∧ b 0 = 0 := mat_ext hs fun x => by rw [← hab 0 h0]; simp
  have hty : ∀ u ∈ B, (∀ j k, ¬ ty j = ty k → a u j k = 0) ∧
      ∀ j k, ¬ ty j = ComplexEmbedding.conjugate (ty k) → b u j k = 0 := fun u hu => by
    have := fun t => mat_ext hs (a := dg ty t * a u) (b := dg ty t * b u) (a' := a u * dg ty t)
      (b' := b u * dg (fun i => ComplexEmbedding.conjugate (ty i)) t) fun x => by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_add, ← hab u hu,
          ← (lin_iff _).1 (hP.1 u hu).1, hab u hu, hl, star_mulVec', dg_map, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec]
    exact ⟨(comm_iff ty ty _).1 fun t => (this t).1, (comm_iff ty _ _).1 fun t => (this t).2⟩
  have dz : ∀ {c : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ} {j k}, (∀ u ∈ B, c u j k = 0) → dM c 0 v j k = 0 := by
    intro c j k hc
    have : (fun u => c u j k) =ᶠ[nhds 0] fun _ => 0 := Filter.eventually_of_mem hn hc
    simp [dM, this.fderiv_eq]
  refine ⟨dM a 0 v, dM b 0 v, fun x => ?_, fun j k h => dz fun u hu => (hty u hu).1 j k h,
    fun j k h => dz fun u hu => (hty u hu).2 j k h, fun hβ U f hU => ?_⟩
  · funext j
    have h1 : (fun u => P u x j) =ᶠ[nhds 0] fun u => (a u * replicateCol Unit (P 0 x)) j () +
        (b u * replicateCol Unit (star (P 0 x))) j () :=
      Filter.eventually_of_mem hn fun u hu => congrFun (hab u hu x) j
    have h2 := congrFun (congrFun (dM_mul hA (HolM.const B (replicateCol Unit (P 0 x))) hn v) j) ()
    have h3 := congrFun (congrFun (dM_mul hb (HolM.const B (replicateCol Unit (star (P 0 x)))) hn v) j) ()
    rw [dM_const (A := fun _ => replicateCol Unit _) (.of_forall fun _ => rfl), Matrix.mul_zero, add_zero] at h2 h3
    have h4 := fderiv_pi (𝕜 := ℂ) (φ := fun j u => P u x j) (x := 0)
      (fun j => (differentiableOn_pi.1 (hP.2 x) j).differentiableAt hn)
    have h5 : fderiv ℂ (fun u => P u x) 0 v j = fderiv ℂ (fun u => P u x j) 0 v := by
      rw [show (fun u => P u x) = fun u j => P u x j from rfl, h4]; rfl
    rw [h5, h1.fderiv_eq, fderiv_fun_add (((hA.mul (HolM.const B _)) j ()).differentiableAt hn)
      (((hb.mul (HolM.const B _)) j ()).differentiableAt hn)]
    exact congrArg₂ (· + ·) h2 h3
  have hZe : ∀ u, Z u = (a u)⁻¹ * b u := fun u =>
    (Matrix.nonsing_inv_mul_cancel_left _ _ (IsUnit.mk0 _ (had u))).symm
  have hZh : HolM B Z := by
    have := (hA.inv fun u _ => had u).mul hb
    simpa only [← hZe] using this
  have Z0 : Z 0 = 0 := by rw [hZe, b0, Matrix.mul_zero]
  have dZ : dM Z 0 v = dM b 0 v := by
    have := dM_mul hA hZh hn v
    rw [Z0, a0, Matrix.mul_zero, zero_add, Matrix.one_mul] at this
    exact this.symm
  have hu : IsUnit Gᵀ.det := by
    rw [det_transpose]
    refine isUnit_det_of_ker G fun z hz h => ?_
    have := hp (star z) (by simpa using hz)
    simp [sesq_apply, hermForm, h] at this
  have dS : dM (fun u => Gᵀ * Z u) 0 v = Gᵀ * dM b 0 v := by
    rw [dM_mul (HolM.const B Gᵀ) hZh hn, dM_const (A := fun _ => Gᵀ) (.of_forall fun _ => rfl), dZ]
    simp
  have hsym : (Gᵀ * dM b 0 v)ᵀ = Gᵀ * dM b 0 v := by
    rw [← dS]
    exact dM_congr (A := fun u => (Gᵀ * Z u)ᵀ)
      (Filter.eventually_of_mem hn fun u hu => (anti_symm_iff _ _).1 (hZ u hu).2.1) v
  have hS1 : ∀ j k, ty j (H.rt : E) = H.rt0 ∨ ¬ ty k (H.rt : E) = H.rt0 → (Gᵀ * dM b 0 v) j k = 0 := by
    intro j k hjk
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun m _ => ?_
    by_cases hm : ty m (H.rt : E) = H.rt0
    · rw [hβ m k hm, mul_zero]
    rcases hjk with hj | hk
    · rw [Matrix.transpose_apply, hblock m j (fun e => hm (e ▸ hj)), zero_mul]
    · rw [dz fun u hu => (hty u hu).2 m k fun e => hm ?_, mul_zero]
      rw [e]
      by_contra hc
      exact hk ((conj_rt H (ty k)).2 hc)
  have dZ0 : dM Z 0 v = 0 := by
    have : Gᵀ * dM b 0 v = 0 := by
      ext j k
      by_cases hk : ty k (H.rt : E) = H.rt0
      · rw [← hsym, Matrix.transpose_apply]; exact hS1 k j (.inl hk)
      · exact hS1 j k (.inr hk)
    rw [dZ, ← Matrix.nonsing_inv_mul_cancel_left _ (dM b 0 v) hu, this, Matrix.mul_zero]
  let 𝒵 : Submodule ℂ (Matrix (Fin g) (Fin g) ℂ) :=
    { carrier := {X | (∀ a, dg ty a * X = X * dg (fun i => ComplexEmbedding.conjugate (ty i)) a) ∧
        (Gᵀ * X)ᵀ = Gᵀ * X}
      add_mem' := fun {X Y} hX hY => ⟨fun a => by rw [Matrix.mul_add, Matrix.add_mul, hX.1, hY.1],
        by rw [Matrix.mul_add, Matrix.transpose_add, hX.2, hY.2]⟩
      zero_mem' := ⟨fun a => by simp, by simp⟩
      smul_mem' := fun c X hX => ⟨fun a => by rw [Matrix.mul_smul, Matrix.smul_mul, hX.1],
        by rw [Matrix.mul_smul, Matrix.transpose_smul, hX.2]⟩ }
  let e := (Module.finBasis ℂ 𝒵).equivFun
  obtain ⟨π, hπ⟩ := 𝒵.subtype.exists_leftInverse_of_injective (Submodule.ker_subtype _)
  let L : (Fin (Module.finrank ℂ 𝒵) → ℂ) →ₗ[ℂ] Matrix (Fin g) (Fin g) ℂ := 𝒵.subtype ∘ₗ e.symm.toLinearMap
  let R : (Fin g → Fin g → ℂ) →L[ℂ] (Fin (Module.finrank ℂ 𝒵) → ℂ) :=
    LinearMap.toContinuousLinearMap (e.toLinearMap ∘ₗ π ∘ₗ (Matrix.ofLinearEquiv ℂ).toLinearMap)
  have hLR : ∀ u ∈ B, L (R fun j k => Z u j k) = Z u := fun u hu => by
    have hm : Z u ∈ 𝒵 := ⟨fun a => (anti_comm_iff ty a _).1 ((hZ u hu).1 a), (anti_symm_iff _ _).1 (hZ u hu).2.1⟩
    have h1 : π (Z u) = ⟨Z u, hm⟩ := DFunLike.congr_fun hπ ⟨Z u, hm⟩
    show ((e.symm (e (π (Z u))) : 𝒵) : Matrix (Fin g) (Fin g) ℂ) = Z u
    rw [e.symm_apply_apply, h1]
  obtain ⟨ho, -⟩ := isOpen_convex G hp L
  let Q : (Fin (Module.finrank ℂ 𝒵) → ℂ) → ((FU.Di i).La →+ (Fin g → ℂ)) := fun b =>
    P 0 + (anti (L b)).toAddMonoidHom.comp (P 0)
  have hQ : IsHolPeriods (FU.Di i) ty _ Q := ⟨fun b hb => isPeriod_add (P 0) hl hi hd hs G hG hE _
    (fun a => (anti_comm_iff ty a _).2 ((e.symm b).2.1 a)) ((anti_symm_iff _ _).2 (e.symm b).2.2) hb, fun x => by
      let f : (Fin (Module.finrank ℂ 𝒵) → ℂ) →ₗ[ℂ] (Fin g → ℂ) :=
        { toFun := fun b => L b *ᵥ star (P 0 x)
          map_add' := fun b c => by rw [map_add, add_mulVec]
          map_smul' := fun c b => by rw [map_smul, smul_mulVec]; rfl }
      exact ((differentiable_const (P 0 x)).add f.toContinuousLinearMap.differentiable).differentiableOn⟩
  let w : (Fin n → ℂ) → Fin (Module.finrank ℂ 𝒵) → ℂ := fun u => R fun j k => Z u j k
  have hwm : ∀ u ∈ B, w u ∈ {b | ∀ z, z ≠ 0 → (sesq G (anti (L b) z) (anti (L b) z)).re < (sesq G z z).re} :=
    fun u hu => by
      show ∀ z, z ≠ 0 → (sesq G (anti (L (w u)) z) (anti (L (w u)) z)).re < _
      rw [hLR u hu]; exact (hZ u hu).2.2.1
  have hQP : ∀ u ∈ B, FU.u i (Q (w u)) = FU.u i (P u) := fun u hu =>
    (FU.fibre i _ _ (hQ.1 _ (hwm u hu)) (hP.1 u hu)).2 ⟨LinearEquiv.refl _ _, h u, fun _ _ => rfl,
      fun a _ => ⟨0, by simp⟩, fun a => ⟨0, by simp⟩, fun x => by
        rw [LinearEquiv.refl_apply, (hZ u hu).2.2.2, ← hLR u hu]; rfl⟩
  have hF := GlobalTheory.LocalLift.hol_differentiableAt (FU.hol i _ _ Q ho hQ).1 (hwm 0 h0) (U := U)
    (by rw [hQP 0 h0]; exact hU) f
  have hZd : HasFDerivAt (fun u j k => Z u j k)
      (ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun k => fderiv ℂ (fun u => Z u j k) 0) 0 :=
    hasFDerivAt_pi.2 fun j => hasFDerivAt_pi.2 fun k => ((hZh j k).differentiableAt hn).hasFDerivAt
  have hc := hF.hasFDerivAt.comp (0 : Fin n → ℂ) (R.hasFDerivAt.comp (0 : Fin n → ℂ) hZd)
  have he : (fun u => valAt' (FU.u i (P u)) U f) =ᶠ[nhds 0]
      (fun z => valAt' (FU.u i (Q z)) U f) ∘ w :=
    Filter.eventually_of_mem hn fun u hu => by simp only [Function.comp_apply, hQP u hu]
  rw [he.fderiv_eq, hc.fderiv]
  have : (ContinuousLinearMap.pi fun j => ContinuousLinearMap.pi fun k => fderiv ℂ (fun u => Z u j k) 0) v = 0 := dZ0
  simp only [ContinuousLinearMap.comp_apply, this, map_zero]

end PositivityTheory.Xgp.c_bm_exists_period
