import Mathlib
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.CartanInvolutionConjTransposeMul

open Matrix Filter Topology Set
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.Upq.Sm

section SmOn

variable {E E' V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
  [NormedSpace ℝ E'] [NormedAddCommGroup V] [NormedSpace ℝ V]

def SmOn (A : Set E) (f : E → V) : Prop :=
  ∀ a ∈ A, ∃ (U : Set E) (F : E → V), IsOpen U ∧ a ∈ U ∧ ContDiffOn ℝ ∞ F U ∧
    ∀ g ∈ U, g ∈ A → f g = F g

theorem SmOn.congr {A : Set E} {f f' : E → V} (hf : SmOn A f) (h : ∀ a ∈ A, f' a = f a) :
    SmOn A f' := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  exact ⟨U, F, hU, haU, hF, fun g hg hgA => (h g hgA).trans (hfF g hg hgA)⟩

theorem SmOn.comp {A : Set E} {B : Set E'} {f : E → V} (hf : SmOn A f) {φ : E' → E}
    (hφ : ContDiff ℝ ∞ φ) (hm : MapsTo φ B A) : SmOn B (fun b => f (φ b)) := fun b hb => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf (φ b) (hm hb)
  exact ⟨φ ⁻¹' U, fun x => F (φ x), hU.preimage hφ.continuous, haU,
    hF.comp hφ.contDiffOn (fun x hx => hx), fun g hg hgB => hfF _ hg (hm hgB)⟩

theorem SmOn.of_contDiff {A : Set E} {f : E → V} (hf : ContDiff ℝ ∞ f) : SmOn A f :=
  fun _ _ => ⟨univ, f, isOpen_univ, mem_univ _, hf.contDiffOn, fun _ _ _ => rfl⟩

theorem SmOn.add {A : Set E} {f f' : E → V} (hf : SmOn A f) (hf' : SmOn A f') :
    SmOn A (fun a => f a + f' a) := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  obtain ⟨U', F', hU', haU', hF', hfF'⟩ := hf' a ha
  exact ⟨U ∩ U', fun x => F x + F' x, hU.inter hU', ⟨haU, haU'⟩,
    (hF.mono inter_subset_left).add (hF'.mono inter_subset_right),
    fun g hg hgA => by simp only [hfF g hg.1 hgA, hfF' g hg.2 hgA]⟩

theorem SmOn.clm {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {A : Set E} {f : E → V}
    (hf : SmOn A f) (L : V →L[ℝ] W) : SmOn A (fun a => L (f a)) := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  exact ⟨U, fun x => L (F x), hU, haU, L.contDiff.comp_contDiffOn hF,
    fun g hg hgA => by simp only [hfF g hg hgA]⟩

theorem SmOn.continuousOn {A : Set E} {f : E → V} (hf : SmOn A f) : ContinuousOn f A := by
  intro a ha
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
  have h1 : ContinuousWithinAt F A a :=
    (hF.continuousOn.continuousAt (hU.mem_nhds haU)).continuousWithinAt
  refine h1.congr_of_eventuallyEq ?_ (hfF a haU ha)
  filter_upwards [mem_nhdsWithin_of_mem_nhds (hU.mem_nhds haU), self_mem_nhdsWithin] with g h1 h2
  exact hfF g h1 h2

theorem hasDerivAt_local {A U : Set E} {f F : E → V} {a v : E} {γ : ℝ → E} (hγ : ∀ t, γ t ∈ A)
    (h0 : γ 0 = a) (hd : HasDerivAt γ v 0) (hU : IsOpen U) (haU : a ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) (hfF : ∀ g ∈ U, g ∈ A → f g = F g) :
    HasDerivAt (fun t => f (γ t)) (fderiv ℝ F a v) 0 := by
  have hFd : DifferentiableAt ℝ F a :=
    (hF.differentiableOn (by simp)).differentiableAt (hU.mem_nhds haU)
  have hcomp : HasDerivAt (fun t : ℝ => F (γ t)) (fderiv ℝ F a v) 0 :=
    hFd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hd h0.symm
  have hmem : ∀ᶠ t : ℝ in 𝓝 0, γ t ∈ U :=
    hd.continuousAt.preimage_mem_nhds (by rw [h0]; exact hU.mem_nhds haU)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards [hmem] with t ht
  exact hfF _ ht (hγ t)

theorem SmOn.flow {A : Set E} {f : E → V} (hf : SmOn A f) {γ : E → ℝ → E} {v : E → E}
    (hγ : ∀ a ∈ A, ∀ t, γ a t ∈ A) (h0 : ∀ a, γ a 0 = a) (hd : ∀ a, HasDerivAt (γ a) (v a) 0)
    (hv : ContDiff ℝ ∞ v) :
    (∀ a ∈ A, DifferentiableAt ℝ (fun t => f (γ a t)) 0) ∧
      SmOn A (fun a => deriv (fun t => f (γ a t)) 0) := by
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
    exact (hasDerivAt_local (hγ a ha) (h0 a) (hd a) hU haU hF hfF).differentiableAt
  · obtain ⟨U, F, hU, haU, hF, hfF⟩ := hf a ha
    refine ⟨U, fun x => fderiv ℝ F x (v x), hU, haU, ?_, fun g hg hgA => ?_⟩
    · exact (hF.fderiv_of_isOpen hU (by simp)).clm_apply hv.contDiffOn
    · exact (hasDerivAt_local (hγ g hgA) (h0 g) (hd g) hU hg hF hfF).deriv

end SmOn

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

abbrev Mat (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

theorem contDiff_mul : ContDiff ℝ ∞ (fun p : Mat n × Mat n => p.1 * p.2) := by
  let B : Mat n →L[ℝ] Mat n →L[ℝ] Mat n :=
    LinearMap.toContinuousLinearMap
      ((LinearMap.toContinuousLinearMap : (Mat n →ₗ[ℝ] Mat n) ≃ₗ[ℝ] _).toLinearMap ∘ₗ
        LinearMap.mul ℝ (Mat n))
  exact B.isBoundedBilinearMap.contDiff

theorem contDiff_mul' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : E → Mat n}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) : ContDiff ℝ ∞ (fun x => f x * g x) :=
  contDiff_mul.comp (hf.prodMk hg)

def ex (X : Mat n) (t : ℝ) : Mat n := NormedSpace.exp ((t : ℂ) • X)

theorem ex_zero (X : Mat n) : ex X 0 = 1 := by simp [ex, NormedSpace.exp_zero]

theorem hasDerivAt_mul_ex (g X : Mat n) : HasDerivAt (fun t => g * ex X t) (g * X) 0 :=
  Formalism.REAL.hasDerivAt_mul_exp_smul_zero g X

def ds (σ : Mat n → (H →L[ℂ] H)) (X : Mat n) (v : H) : H := deriv (fun t : ℝ => σ (ex X t) v) 0

def dsW (σ : Mat n → (H →L[ℂ] H)) (W : List (Mat n)) (v : H) : H := W.foldr (ds σ) v

theorem dsW_cons (σ : Mat n → (H →L[ℂ] H)) (X : Mat n) (W : List (Mat n)) (v : H) :
    dsW σ (X :: W) v = ds σ X (dsW σ W v) := rfl

structure RepOn (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) : Prop where
  one_mem : 1 ∈ G
  mul_mem : ∀ a ∈ G, ∀ b ∈ G, a * b ∈ G
  map_one : σ 1 = 1
  map_mul : ∀ a ∈ G, ∀ b ∈ G, σ (a * b) = (σ a).comp (σ b)

def LieW (G : Set (Mat n)) (W : List (Mat n)) : Prop := ∀ X ∈ W, ∀ t, ex X t ∈ G

def IsSm (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (v : H) : Prop := SmOn G (fun g => σ g v)

variable {G : Set (Mat n)} {σ : Mat n → (H →L[ℂ] H)}

theorem RepOn.apply_mul (h : RepOn G σ) {a b : Mat n} (ha : a ∈ G) (hb : b ∈ G) (v : H) :
    σ (a * b) v = σ a (σ b v) := by rw [h.map_mul a ha b hb]; rfl

theorem apply_ds (h : RepOn G σ) {X g : Mat n} (hX : ∀ t, ex X t ∈ G) (hg : g ∈ G) {u : H}
    (hu : DifferentiableAt ℝ (fun t => σ (ex X t) u) 0) :
    σ g (ds σ X u) = deriv (fun t => σ (g * ex X t) u) 0 := by
  have h1 := ((σ g).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hu.hasDerivAt
  have h2 : (fun t => σ (g * ex X t) u) = ((σ g).restrictScalars ℝ) ∘ fun t => σ (ex X t) u := by
    ext t; exact h.apply_mul hg (hX t) u
  rw [h2, h1.deriv]; rfl

theorem smOn_ds {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : RepOn G σ) {A : Set E}
    {u : E → H} (hu : SmOn (G ×ˢ A) (fun q : Mat n × E => σ q.1 (u q.2))) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) :
    (∀ p ∈ A, DifferentiableAt ℝ (fun t => σ (ex X t) (u p)) 0) ∧
      SmOn (G ×ˢ A) (fun q : Mat n × E => σ q.1 (ds σ X (u q.2))) := by
  obtain ⟨h1, h2⟩ := hu.flow (γ := fun q t => (q.1 * ex X t, q.2)) (v := fun q => (q.1 * X, 0))
    (fun q hq t => ⟨h.mul_mem _ hq.1 _ (hX t), hq.2⟩) (fun q => by simp [ex_zero])
    (fun q => (hasDerivAt_mul_ex q.1 X).prodMk (hasDerivAt_const _ _))
    ((contDiff_mul' contDiff_fst contDiff_const).prodMk contDiff_const)
  have h3 : ∀ p ∈ A, DifferentiableAt ℝ (fun t => σ (ex X t) (u p)) 0 := fun p hp => by
    simpa using h1 (1, p) ⟨h.one_mem, hp⟩
  exact ⟨h3, h2.congr fun q hq => apply_ds h hX hq.1 (h3 _ hq.2)⟩

theorem smOn_dsW {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (h : RepOn G σ) {A : Set E}
    {u : E → H} (hu : SmOn (G ×ˢ A) (fun q : Mat n × E => σ q.1 (u q.2))) :
    ∀ {W : List (Mat n)}, LieW G W →
      SmOn (G ×ˢ A) (fun q : Mat n × E => σ q.1 (dsW σ W (u q.2)))
  | [], _ => hu
  | X :: W, hW =>
    (smOn_ds h (u := fun p => dsW σ W (u p))
      (smOn_dsW h hu fun Y hY => hW Y (List.mem_cons_of_mem _ hY)) (hW X List.mem_cons_self)).2

theorem IsSm.prod {v : H} (hv : IsSm G σ v) :
    SmOn (G ×ˢ (univ : Set ℝ)) (fun q : Mat n × ℝ => σ q.1 v) :=
  SmOn.comp hv contDiff_fst fun _ hq => hq.1

theorem IsSm.differentiableAt (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n}
    (hX : ∀ t, ex X t ∈ G) : DifferentiableAt ℝ (fun t => σ (ex X t) v) 0 :=
  (smOn_ds h (u := fun _ : ℝ => v) hv.prod hX).1 0 (mem_univ _)

theorem IsSm.dsW (h : RepOn G σ) {v : H} (hv : IsSm G σ v) {W : List (Mat n)} (hW : LieW G W) :
    IsSm G σ (dsW σ W v) :=
  SmOn.comp (smOn_dsW h (u := fun _ : ℝ => v) hv.prod hW) (φ := fun g : Mat n => (g, (0 : ℝ)))
    (contDiff_id.prodMk contDiff_const) fun _ hg => ⟨hg, mem_univ _⟩

theorem IsSm.add {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v') : IsSm G σ (v + v') :=
  (SmOn.add hv hv').congr fun _ _ => map_add _ _ _

theorem IsSm.smul {v : H} (hv : IsSm G σ v) (c : ℂ) : IsSm G σ (c • v) :=
  (SmOn.clm hv ((c • ContinuousLinearMap.id ℂ H).restrictScalars ℝ)).congr fun _ _ => by simp

theorem IsSm.zero : IsSm G σ 0 :=
  (SmOn.of_contDiff (contDiff_const (c := (0 : H)))).congr fun _ _ => map_zero _

theorem IsSm.sub {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v') : IsSm G σ (v - v') := by
  have := hv.add (hv'.smul (-1))
  rwa [neg_one_smul, ← sub_eq_add_neg] at this

theorem IsSm.smOn_mul (h : RepOn G σ) {w : H} (hw : IsSm G σ w) :
    SmOn (G ×ˢ G) (fun q : Mat n × Mat n => σ q.1 (σ q.2 w)) :=
  (SmOn.comp hw contDiff_mul fun _ hq => h.mul_mem _ hq.1 _ hq.2).congr
    fun _ hq => (h.apply_mul hq.1 hq.2 w).symm

theorem IsSm.apply (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {x : Mat n} (hx : x ∈ G) :
    IsSm G σ (σ x w) :=
  SmOn.comp (hw.smOn_mul h) (φ := fun g : Mat n => (g, x)) (contDiff_id.prodMk contDiff_const)
    fun _ hg => ⟨hg, hx⟩

theorem ds_add (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {v v' : H} (hv : IsSm G σ v)
    (hv' : IsSm G σ v') : ds σ X (v + v') = ds σ X v + ds σ X v' := by
  unfold ds
  simp only [map_add]
  exact deriv_fun_add (hv.differentiableAt h hX) (hv'.differentiableAt h hX)

theorem ds_smul (h : RepOn G σ) {X : Mat n} (hX : ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v)
    (c : ℂ) : ds σ X (c • v) = c • ds σ X v := by
  unfold ds
  simp only [map_smul]
  exact deriv_fun_const_smul c (hv.differentiableAt h hX)

theorem dsW_add (h : RepOn G σ) {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v') :
    ∀ {W : List (Mat n)}, LieW G W → dsW σ W (v + v') = dsW σ W v + dsW σ W v'
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    simp only [dsW_cons]
    rw [dsW_add h hv hv' hW', ds_add h (hW X List.mem_cons_self) (hv.dsW h hW') (hv'.dsW h hW')]

theorem dsW_smul (h : RepOn G σ) {v : H} (hv : IsSm G σ v) (c : ℂ) :
    ∀ {W : List (Mat n)}, LieW G W → dsW σ W (c • v) = c • dsW σ W v
  | [], _ => rfl
  | X :: W, hW => by
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    simp only [dsW_cons]
    rw [dsW_smul h hv c hW', ds_smul h (hW X List.mem_cons_self) (hv.dsW h hW')]

theorem dsW_sub (h : RepOn G σ) {v v' : H} (hv : IsSm G σ v) (hv' : IsSm G σ v')
    {W : List (Mat n)} (hW : LieW G W) : dsW σ W (v - v') = dsW σ W v - dsW σ W v' := by
  rw [sub_eq_add_neg, ← neg_one_smul ℂ v', dsW_add h hv (hv'.smul _) hW, dsW_smul h hv' _ hW,
    neg_one_smul, ← sub_eq_add_neg]

theorem continuousOn_dsW_orbit (h : RepOn G σ) {w : H} (hw : IsSm G σ w) {W : List (Mat n)}
    (hW : LieW G W) : ContinuousOn (fun x => dsW σ W (σ x w)) G := by
  have h1 := SmOn.comp (smOn_dsW h (u := fun x => σ x w) (hw.smOn_mul h) hW)
    (φ := fun x : Mat n => ((1 : Mat n), x)) (B := G) (contDiff_const.prodMk contDiff_id)
    fun _ hg => ⟨h.one_mem, hg⟩
  refine h1.continuousOn.congr fun x _ => ?_
  simp [h.map_one]

end CompanionTheory.D.Upq.Sm

end
