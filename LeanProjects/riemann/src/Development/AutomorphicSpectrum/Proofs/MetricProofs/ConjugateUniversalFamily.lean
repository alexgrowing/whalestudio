import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam

open scoped ComplexOrder

def conjEnd (g : ℕ) : Module.End ℂ (Fin g → ℂ) →+* Module.End ℂ (Fin g → ℂ) where
  toFun f :=
    { toFun := fun x => star (f (star x))
      map_add' := fun x y => by simp only [star_add, map_add]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply] }
  map_one' := by ext x; simp
  map_mul' f f' := by ext x; simp
  map_zero' := by ext x; simp
  map_add' f f' := by ext x; simp

theorem conjEnd_apply {g : ℕ} (f : Module.End ℂ (Fin g → ℂ)) (x : Fin g → ℂ) :
    conjEnd g f x = star (f (star x)) := rfl

theorem mem_eigSp_iff {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ)
    (x : Fin g → ℂ) : x ∈ eigSp ρ σ ↔ ∀ a, ρ a x = σ a • x := by
  simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem star_mem_of_conj {g : ℕ} {O : Type} [CommRing O] {ρ : O →+* Module.End ℂ (Fin g → ℂ)} {σ : O →+* ℂ}
    {x : Fin g → ℂ} (hx : x ∈ eigSp ((conjEnd g).comp ρ) σ) : star x ∈ eigSp ρ ((starRingEnd ℂ).comp σ) := by
  rw [mem_eigSp_iff] at hx ⊢
  intro a
  have := congrArg star (hx a)
  simpa [conjEnd_apply, star_smul] using this

theorem star_mem_conj {g : ℕ} {O : Type} [CommRing O] {ρ : O →+* Module.End ℂ (Fin g → ℂ)} {σ : O →+* ℂ}
    {y : Fin g → ℂ} (hy : y ∈ eigSp ρ ((starRingEnd ℂ).comp σ)) : star y ∈ eigSp ((conjEnd g).comp ρ) σ := by
  rw [mem_eigSp_iff] at hy ⊢
  intro a
  simp [conjEnd_apply, hy a, star_smul]

theorem finrank_eigSp_conj {g : ℕ} {O : Type} [CommRing O] (ρ : O →+* Module.End ℂ (Fin g → ℂ)) (σ : O →+* ℂ) :
    Module.finrank ℂ (eigSp ((conjEnd g).comp ρ) σ) = Module.finrank ℂ (eigSp ρ ((starRingEnd ℂ).comp σ)) := by
  let j : eigSp ((conjEnd g).comp ρ) σ ≃+ eigSp ρ ((starRingEnd ℂ).comp σ) :=
    { toFun := fun x => ⟨star x.1, star_mem_of_conj x.2⟩
      invFun := fun y => ⟨star y.1, star_mem_conj y.2⟩
      left_inv := fun x => Subtype.ext (star_star _)
      right_inv := fun y => Subtype.ext (star_star _)
      map_add' := fun x y => Subtype.ext (star_add _ _) }
  have hr := rank_eq_of_equiv_equiv (R := ℂ) (R' := ℂ) (starRingEnd ℂ) j
    (Function.Involutive.bijective (f := starRingEnd ℂ) (fun z => by simp)) (fun r m => Subtype.ext (by simp [j, star_smul]))
  exact congrArg Cardinal.toNat hr

theorem star_herm {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (z w : Fin g → ℂ) :
    star z ⬝ᵥ Hm.map (starRingEnd ℂ) *ᵥ star (star w) = star (z ⬝ᵥ Hm *ᵥ star w) := by
  simp [dotProduct, mulVec, star_sum]

theorem conj_conj_comp {O : Type} [Semiring O] (s : O →+* ℂ) :
    (starRingEnd ℂ).comp ((starRingEnd ℂ).comp s) = s := by
  ext a; simp

theorem differentiableOn_conj {n g : ℕ} {U U' : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → Fin g → ℂ}
    (hf : DifferentiableOn ℂ f U) (hU : ∀ t ∈ U', star t ∈ U) :
    DifferentiableOn ℂ (fun t => star (f (star t))) U' := by
  intro t ht
  obtain ⟨L, hL⟩ := hf (star t) (hU t ht)
  let L' : (Fin n → ℂ) →L[ℂ] (Fin g → ℂ) :=
    { toFun := fun v => star (L (star v))
      map_add' := fun x y => by simp only [star_add, map_add]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply]
      cont := continuous_star.comp (L.continuous.comp continuous_star) }
  refine ⟨L', ?_⟩
  rw [hasFDerivWithinAt_iff_tendsto] at hL ⊢
  have hs : Tendsto (star : (Fin n → ℂ) → (Fin n → ℂ)) (𝓝[U'] t) (𝓝[U] (star t)) :=
    tendsto_nhdsWithin_iff.2 ⟨(continuous_star.tendsto t).mono_left nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin.mono hU⟩
  refine (hL.comp hs).congr (fun x => ?_)
  have h1 : star (f (star x)) - star (f (star t)) - L' (x - t) =
      star (f (star x) - f (star t) - L (star x - star t)) := by
    show _ - _ - star (L (star (x - t))) = _
    simp only [star_sub]
  have h2 : ‖star x - star t‖ = ‖x - t‖ := by rw [← star_sub, norm_star]
  simp only [Function.comp]
  rw [h1, norm_star, h2]

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

def conjLat {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] (R : RiemLat E g Λ) : RiemLat E g Λ where
  free := R.free
  fin := R.fin
  rank := R.rank
  form := -R.form
  alt x := by simp [R.alt x]
  unimod := by
    constructor
    · intro x y h
      exact R.unimod.1 (neg_injective (by simpa using h))
    · intro f
      obtain ⟨x, hx⟩ := R.unimod.2 (-f)
      exact ⟨x, by simp [hx]⟩
  adj a a' h x y := by simp [R.adj a a' h x y]
  P :=
    { toFun := fun x => star (R.P x)
      map_zero' := by simp
      map_add' := fun x y => by simp }
  Hm := R.Hm.map (starRingEnd ℂ)
  herm := by
    ext i j
    have := R.herm.apply i j
    simp [Matrix.conjTranspose_apply, ← this]
  pos z hz := by
    have h := R.pos (star z) (by simpa using hz)
    have h' := star_herm R.Hm (star z) (star z)
    simp only [star_star] at h'
    rw [h']
    simpa using h
  im x y := by
    have h := R.im x y
    have h' := star_herm R.Hm (R.P x) (R.P y)
    simp only [AddMonoidHom.coe_mk, ZeroHom.coe_mk]
    rw [h']
    simp [h]
  B := (conjEnd g).comp R.B
  act a x := by simp [conjEnd_apply, R.act]

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ] {Ψ : Type} [Fintype Ψ] {j j' n : ℕ}

theorem hasSig_conjLat {R : RiemLat E g Λ} {σ : Ψ → (𝓞 E →+* ℂ)} (h : R.HasSig σ j j') :
    (conjLat R).HasSig (fun τ => (starRingEnd ℂ).comp (σ τ)) j j' := by
  intro τ
  constructor
  · show Module.finrank ℂ (eigSp ((conjEnd g).comp R.B) _) = j'
    rw [finrank_eigSp_conj, conj_conj_comp]
    exact (h τ).1
  · show Module.finrank ℂ (eigSp ((conjEnd g).comp R.B) _) = j
    rw [finrank_eigSp_conj, conj_conj_comp]
    exact (h τ).2

theorem isCMFam_conj {σ : Ψ → (𝓞 E →+* ℂ)} (h : IsCMFam σ) :
    IsCMFam (fun τ => (starRingEnd ℂ).comp (σ τ)) := by
  have e : ∀ a b : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp a = b ↔ a = (starRingEnd ℂ).comp b := fun a b =>
    ⟨fun hab => by rw [← hab, conj_conj_comp], fun hab => by rw [hab, conj_conj_comp]⟩
  refine ⟨fun a b hab => h.1 ?_, fun s => ?_⟩
  · have := congrArg (fun c : 𝓞 E →+* ℂ => (starRingEnd ℂ).comp c) hab
    simpa only [conj_conj_comp] using this
  · have key := h.2 ((starRingEnd ℂ).comp s)
    rw [conj_conj_comp] at key
    simp only [e, conj_conj_comp]
    exact key

theorem eqvBy_conj {R₁ R₂ R₁' R₂' : RiemLat E g Λ} {γ : Λ ≃ₗ[𝓞 E] Λ} (h₁ : ∀ x, R₁'.P x = star (R₁.P x))
    (h₂ : ∀ x, R₂'.P x = star (R₂.P x)) (h : R₁.EqvBy R₂ γ) : R₁'.EqvBy R₂' γ := by
  obtain ⟨e, he⟩ := h
  let e' : (Fin g → ℂ) ≃ₗ[ℂ] (Fin g → ℂ) :=
    { toFun := fun x => star (e (star x))
      invFun := fun x => star (e.symm (star x))
      map_add' := fun x y => by simp only [star_add, map_add]
      map_smul' := fun c x => by simp only [star_smul, map_smul, star_star, RingHom.id_apply]
      left_inv := fun x => by simp
      right_inv := fun x => by simp }
  refine ⟨e', fun x => ?_⟩
  show R₂'.P (γ x) = star (e (star (R₁'.P x)))
  rw [h₂, he, h₁, star_star]

theorem ip_conj (R : RiemLat E g Λ) (x y : Fin g → ℂ) :
    (conjLat R).ip (star x) (star y) = star (R.ip x y) :=
  star_herm R.Hm y x

theorem gram_conj (R : RiemLat E g Λ) {m : ℕ} (u : Fin m → Fin g → ℂ) :
    (conjLat R).gram (fun a => star (u a)) = (R.gram u).map (starRingEnd ℂ) := by
  ext a b
  simp only [RiemLat.gram, Matrix.of_apply, Matrix.map_apply, ip_conj]
  rfl

theorem det_conj_re {m : Type} [Fintype m] [DecidableEq m] (M : Matrix m m ℂ) :
    (M.map (starRingEnd ℂ)).det.re = M.det.re := by
  have := RingHom.map_det (starRingEnd ℂ) M
  rw [RingHom.mapMatrix_apply] at this
  rw [← this, Complex.conj_re]

theorem logDet_conj (R : RiemLat E g Λ) {m : ℕ} (b : Ψ → Fin m → Fin g → ℂ) :
    (conjLat R).logDet (fun τ i => star (b τ i)) = R.logDet b := by
  simp only [RiemLat.logDet]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [gram_conj, det_conj_re]

theorem ballMat_star (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) :
    ballMat q (star t) τ = (ballMat q t τ).map (starRingEnd ℂ) := by
  ext a b
  simp [ballMat]

theorem one_sub_star (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) (τ : Ψ) :
    1 - (ballMat q (star t) τ)ᴴ * ballMat q (star t) τ =
      (1 - (ballMat q t τ)ᴴ * ballMat q t τ).map (starRingEnd ℂ) := by
  rw [ballMat_star]
  ext a b
  simp [Matrix.mul_apply, Matrix.one_apply, Matrix.sub_apply, Matrix.conjTranspose_apply, map_sum, apply_ite]

theorem star_mem_ballDom {q : Ψ × Fin j × Fin j' ≃ Fin n} {t : Fin n → ℂ} (ht : t ∈ ballDom q) :
    star t ∈ ballDom q := by
  intro τ
  have h := ht τ
  rw [one_sub_star]
  have he : (1 - (ballMat q t τ)ᴴ * ballMat q t τ).map (starRingEnd ℂ) =
      (1 - (ballMat q t τ)ᴴ * ballMat q t τ)ᵀ := by
    ext a b
    exact h.1.apply b a
  rw [he]
  exact h.transpose

theorem ballPot_star (q : Ψ × Fin j × Fin j' ≃ Fin n) (t : Fin n → ℂ) : ballPot q (star t) = ballPot q t := by
  simp only [ballPot, one_sub_star, det_conj_re]

theorem linearIndependent_star {m : ℕ} {v : Fin m → Fin g → ℂ} (h : LinearIndependent ℂ v) :
    LinearIndependent ℂ (fun i => star (v i)) := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro c hc i
  have h0 : ∑ k, star (c k) • v k = 0 := by
    have := congrArg star hc
    simpa [star_sum, star_smul] using this
  simpa using h (fun k => star (c k)) h0 i

theorem star_mem_span {m : ℕ} {v : Fin m → Fin g → ℂ} {y : Fin g → ℂ}
    (hy : y ∈ Submodule.span ℂ (Set.range v)) :
    star y ∈ Submodule.span ℂ (Set.range fun i => star (v i)) := by
  induction hy using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact Submodule.subset_span ⟨i, rfl⟩
  | zero => simp
  | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx

theorem span_star {m : ℕ} {O : Type} [CommRing O] {ρ : O →+* Module.End ℂ (Fin g → ℂ)} {s : O →+* ℂ}
    {v : Fin m → Fin g → ℂ} (h : Submodule.span ℂ (Set.range v) = eigSp ρ s) :
    Submodule.span ℂ (Set.range fun i => star (v i)) = eigSp ((conjEnd g).comp ρ) ((starRingEnd ℂ).comp s) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have hv : v i ∈ eigSp ρ s := h ▸ Submodule.subset_span ⟨i, rfl⟩
    refine star_mem_conj ?_
    rwa [conj_conj_comp]
  · intro x hx
    have h1 := star_mem_of_conj hx
    rw [conj_conj_comp, ← h] at h1
    simpa using star_mem_span h1

def conjFam (F : UnivFam E Ψ j j' n g Λ) : UnivFam E Ψ j j' n g Λ where
  q := F.q
  σ τ := (starRingEnd ℂ).comp (F.σ τ)
  cm := isCMFam_conj F.cm
  form := -F.form
  R t := conjLat (F.R (star t))
  form_eq t := by
    show -(F.R (star t)).form = _
    rw [F.form_eq]
  hol := by
    refine ⟨fun t _ t' _ => ?_, fun x => ?_⟩
    · show -(F.R (star t)).form = -(F.R (star t')).form
      rw [F.form_eq, F.form_eq]
    · exact differentiableOn_conj (F.hol.2 x) (fun t ht => star_mem_ballDom ht)
  sig t ht := hasSig_conjLat (F.sig _ (star_mem_ballDom ht))
  b τ i t := star (F.b τ i (star t))
  frames := by
    refine ⟨fun τ i => differentiableOn_conj (F.frames.1 τ i) (fun t ht => star_mem_ballDom ht), fun t ht τ => ?_⟩
    obtain ⟨h1, h2⟩ := F.frames.2 (star t) (star_mem_ballDom ht) τ
    exact ⟨linearIndependent_star h1, span_star h2⟩
  logDet_eq t ht := by
    rw [logDet_conj (F.R (star t)) (fun τ i => F.b τ i (star t)), F.logDet_eq _ (star_mem_ballDom ht), ballPot_star]
  univ R' hf hs := by
    have hf0 : (conjLat R').form = F.form := by
      show -R'.form = _
      rw [hf, neg_neg]
    have hs0 : (conjLat R').HasSig F.σ j j' := by
      have := hasSig_conjLat hs
      simpa only [conj_conj_comp] using this
    obtain ⟨t₀, ⟨ht₀, hE⟩, hu⟩ := F.univ (conjLat R') hf0 hs0
    refine ⟨star t₀, ⟨star_mem_ballDom ht₀, ?_⟩, ?_⟩
    · refine eqvBy_conj (fun x => ?_) (fun x => ?_) hE
      · show star ((F.R (star (star t₀))).P x) = _
        rw [star_star]
      · show _ = star (star (R'.P x))
        rw [star_star]
    · rintro t ⟨ht, hE'⟩
      have : star t = t₀ := hu (star t) ⟨star_mem_ballDom ht, eqvBy_conj (fun x => ?_) (fun x => rfl) hE'⟩
      · rw [← this, star_star]
      · show _ = star (star ((F.R (star t)).P x))
        rw [star_star]

end GlobalTheory.CompanionTheory.Ar.Cusp.ConjFam

namespace GlobalTheory.CompanionTheory.Ar.Cusp

theorem exists_conj_univFam : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Type) [Fintype Ψ] (j j' n g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ] (F : UnivFam E Ψ j j' n g Λ), ∃ F' : UnivFam E Ψ j j' n g Λ, F'.q = F.q ∧ (∀ τ, F'.σ τ = (starRingEnd ℂ).comp (F.σ τ)) ∧ F'.form = -F.form ∧ ∀ t, (∀ x, (F'.R t).P x = star ((F.R (star t)).P x)) ∧ (F'.R t).Hm = (F.R (star t)).Hm.map (starRingEnd ℂ) ∧ ∀ a x, (F'.R t).B a x = star ((F.R (star t)).B a (star x)) := by
  intro E _ _ _ Ψ _ j j' n g Λ _ _ F
  exact ⟨ConjFam.conjFam F, rfl, fun _ => rfl, rfl, fun t => ⟨fun _ => rfl, rfl, fun _ _ => rfl⟩⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
