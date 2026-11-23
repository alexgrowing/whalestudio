import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.HaarBumpFunctions.ExistsIsBump
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SmoothOnAdditive

open Matrix Filter Topology Set
open scoped ContDiff InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.FinalFormK

open PI CompanionTheory.D.Upq.ModEx CompanionTheory.D.Upq.Sm CompanionTheory.D.gk.Poul

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {G : Set (Mat n)} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] {σ : Mat n → (H →L[ℂ] H)} {τ : Mat n → (H' →L[ℂ] H')}

def nu (σ : Mat n → (H →L[ℂ] H)) (Ws : List (List (Mat n))) (v : H) : ℝ := (Ws.map fun W => ‖dsW σ W v‖).sum

theorem nu_nonneg (Ws : List (List (Mat n))) (v : H) : 0 ≤ nu σ Ws v :=
  List.sum_nonneg fun _ h => by obtain ⟨W, -, rfl⟩ := List.mem_map.1 h; exact norm_nonneg _

theorem nu_append (Ws Ws' : List (List (Mat n))) (v : H) : nu σ (Ws ++ Ws') v = nu σ Ws v + nu σ Ws' v := by
  simp [nu]

theorem nu_eq_sum (Ws : List (List (Mat n))) (v : H) : nu σ Ws v = ∑ i : Fin Ws.length, ‖dsW σ (Ws.get i) v‖ := by
  rw [nu, ← List.sum_ofFn]
  conv_lhs => rw [← List.ofFn_get Ws, List.map_ofFn]
  rfl

def Bdd (G : Set (Mat n)) (L : Mat n → Prop) (σ : Mat n → (H →L[ℂ] H)) {E : Type} [NormedAddCommGroup E]
    (T : H → E) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mat n))), (∀ W ∈ Ws, ∀ X ∈ W, L X) ∧ ∀ v, IsSm G σ v → ‖T v‖ ≤ C * nu σ Ws v

def Lin (G : Set (Mat n)) (σ : Mat n → (H →L[ℂ] H)) (T : H → H') : Prop :=
  (∀ v w, IsSm G σ v → IsSm G σ w → T (v + w) = T v + T w) ∧ ∀ (a : ℂ) v, IsSm G σ v → T (a • v) = a • T v

variable {L : Mat n → Prop}

theorem Bdd.congr {E : Type} [NormedAddCommGroup E] {T T' : H → E} (h : Bdd G L σ T)
    (e : ∀ v, IsSm G σ v → T' v = T v) : Bdd G L σ T' := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  exact ⟨C, Ws, hW, fun v hv => by rw [e v hv]; exact hb v hv⟩

theorem Bdd.add {E : Type} [NormedAddCommGroup E] {T T' : H → E} (h : Bdd G L σ T) (h' : Bdd G L σ T') :
    Bdd G L σ fun v => T v + T' v := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  obtain ⟨C', Ws', hW', hb'⟩ := h'
  refine ⟨|C| + |C'|, Ws ++ Ws', fun W hW0 => (List.mem_append.1 hW0).elim (hW W) (hW' W), fun v hv => ?_⟩
  rw [nu_append]
  have h1 := (hb v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C) (nu_nonneg Ws v))
  have h2 := (hb' v hv).trans (mul_le_mul_of_nonneg_right (le_abs_self C') (nu_nonneg Ws' v))
  nlinarith [norm_add_le (T v) (T' v), mul_nonneg (abs_nonneg C) (nu_nonneg (σ := σ) Ws' v),
    mul_nonneg (abs_nonneg C') (nu_nonneg (σ := σ) Ws v)]

theorem Bdd.zero {E : Type} [NormedAddCommGroup E] : Bdd G L σ fun _ => (0 : E) :=
  ⟨0, [], by simp, fun _ _ => by simp⟩

theorem Bdd.smul {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {T : H → E} (h : Bdd G L σ T) (a : ℂ) :
    Bdd G L σ fun v => a • T v := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨‖a‖ * C, Ws, hW, fun v hv => ?_⟩
  rw [norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hb v hv) (norm_nonneg _)

theorem Bdd.sum {E ι : Type} [NormedAddCommGroup E] {T : ι → H → E} (s : Finset ι) (h : ∀ i ∈ s, Bdd G L σ (T i)) :
    Bdd G L σ fun v => ∑ i ∈ s, T i v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Bdd.zero
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact (h i (Finset.mem_insert_self _ _)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem dsW_append (W W' : List (Mat n)) (v : H) : dsW σ (W ++ W') v = dsW σ W (dsW σ W' v) := List.foldr_append

theorem Bdd.comp_dsW {E : Type} [NormedAddCommGroup E] {T : H → E} (h : Bdd G L σ T) (hσ : RepOn G σ)
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {W' : List (Mat n)} (hW' : ∀ X ∈ W', L X) :
    Bdd G L σ fun v => T (dsW σ W' v) := by
  obtain ⟨C, Ws, hW, hb⟩ := h
  refine ⟨C, Ws.map (· ++ W'), fun W hW0 X hX => ?_, fun v hv => ?_⟩
  · obtain ⟨W₀, hW₀, rfl⟩ := List.mem_map.1 hW0
    exact (List.mem_append.1 hX).elim (hW W₀ hW₀ X) (hW' X)
  · refine (hb _ (hv.dsW hσ fun X hX => hL X (hW' X hX))).trans (le_of_eq ?_)
    simp only [nu, List.map_map, Function.comp_def, dsW_append]

theorem exists_factor [CompleteSpace H] [CompleteSpace H'] {T : H → H'} (hl : Lin G σ T) (hσ : RepOn G σ) {C : ℝ}
    {ι : Type} [Fintype ι] {W : ι → List (Mat n)} (hW : ∀ i, LieW G (W i))
    (hb : ∀ v, IsSm G σ v → ‖T v‖ ≤ C * ∑ i, ‖dsW σ (W i) v‖) :
    ∃ Λ : ι → (H →L[ℂ] H'), ∀ v, IsSm G σ v → T v = ∑ i, Λ i (dsW σ (W i) v) := by
  classical
  let S : Submodule ℂ H :=
    { carrier := {x | IsSm G σ x}
      add_mem' := fun ha hb => ha.add hb
      zero_mem' := IsSm.zero
      smul_mem' := fun c _ hx => hx.smul c }
  let J : S →ₗ[ℂ] PiLp 2 fun _ : ι => H :=
    { toFun := fun x => WithLp.toLp 2 fun i => dsW σ (W i) x
      map_add' := fun x y => PiLp.ext fun i => dsW_add hσ x.2 y.2 (hW i)
      map_smul' := fun c x => PiLp.ext fun i => dsW_smul hσ x.2 c (hW i) }
  let Tl : S →ₗ[ℂ] H' :=
    { toFun := fun x => T x
      map_add' := fun x y => hl.1 _ _ x.2 y.2
      map_smul' := fun c x => hl.2 c _ x.2 }
  let K := (LinearMap.range J).topologicalClosure
  have : CompleteSpace K := (LinearMap.range J).isClosed_topologicalClosure.completeSpace_coe
  let e : S →ₗ[ℂ] K := J.codRestrict K fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩
  have hd : DenseRange e := by
    refine Subtype.dense_iff.2 fun y hy => closure_mono ?_ hy
    rintro _ ⟨x, rfl⟩
    exact ⟨e x, ⟨x, rfl⟩, rfl⟩
  have hn : ∃ D, ∀ x, ‖Tl x‖ ≤ D * ‖e x‖ := by
    refine ⟨|C| * Fintype.card ι, fun x => (hb _ x.2).trans ?_⟩
    rw [mul_assoc]
    refine mul_le_mul (le_abs_self C) ?_ (Finset.sum_nonneg fun _ _ => norm_nonneg _) (abs_nonneg _)
    refine (Finset.sum_le_sum fun i _ => PiLp.norm_apply_le (J x) i).trans (le_of_eq ?_)
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rfl
  let Λ : PiLp 2 (fun _ : ι => H) →L[ℂ] H' := Tl.extendOfNorm e ∘L K.orthogonalProjectionOnto
  let s : ι → (H →L[ℂ] PiLp 2 fun _ : ι => H) := fun i =>
    (PiLp.continuousLinearEquiv 2 ℂ fun _ : ι => H).symm.toContinuousLinearMap ∘L
      ContinuousLinearMap.single ℂ (fun _ : ι => H) i
  refine ⟨fun i => Λ ∘L s i, fun v hv => ?_⟩
  have h1 : Λ (J ⟨v, hv⟩) = T v := by
    show Tl.extendOfNorm e (K.orthogonalProjectionOnto (e ⟨v, hv⟩ : PiLp 2 fun _ : ι => H)) = Tl ⟨v, hv⟩
    rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self, LinearMap.extendOfNorm_eq hd hn]
  rw [← h1]
  simp only [ContinuousLinearMap.comp_apply, ← map_sum]
  congr 1
  refine PiLp.ext fun j => ?_
  show dsW σ (W j) v = (∑ i, s i (dsW σ (W i) v)).ofLp j
  rw [WithLp.ofLp_sum, Finset.sum_apply, Finset.sum_eq_single j (fun i _ hij => Pi.single_eq_of_ne' hij _) (by simp)]
  exact (Pi.single_eq_same (M := fun _ : ι => H) j _).symm

theorem hasDerivAt_matrix_exp_zero (X : Mat n) : HasDerivAt (ex X) X 0 := by
  have := hasDerivAt_ex X 0
  rwa [ex_zero, Matrix.one_mul] at this

theorem smOn_orbit (hσ : RepOn G σ) {w : H} (hw : IsSm G σ w) {W : List (Mat n)} (hW : LieW G W) :
    SmOn G fun x => dsW σ W (σ x w) := by
  have h1 := SmOn.comp (smOn_dsW hσ (u := fun x => σ x w) (hw.smOn_mul hσ) hW)
    (φ := fun x : Mat n => ((1 : Mat n), x)) (B := G) (contDiff_const.prodMk contDiff_id)
    fun _ hg => ⟨hσ.one_mem, hg⟩
  exact h1.congr fun x _ => by simp [hσ.map_one]

theorem hasDerivAt_ds (hσ : RepOn G σ) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => σ (ex X t) v) (ds σ X v) 0 := (hv.differentiableAt hσ hX).hasDerivAt

theorem inner_ds (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {u v : H} (hu : IsSm G σ u)
    (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) : ⟪u, ds σ X v⟫_ℂ = ⟪-ds σ X u, v⟫_ℂ := by
  have h1 := (hasDerivAt_ds hσ hu hX).inner ℂ (hasDerivAt_ds hσ hv hX)
  have e : (fun t => ⟪σ (ex X t) u, σ (ex X t) v⟫_ℂ) = fun _ => ⟪u, v⟫_ℂ := funext fun t =>
    (⟨(σ (ex X t) : H →ₗ[ℂ] H), hiso _ (hX t)⟩ : H →ₗᵢ[ℂ] H).inner_map_map u v
  rw [e] at h1
  have h2 := h1.unique (hasDerivAt_const _ _)
  simp only [ex_zero, hσ.map_one, ContinuousLinearMap.one_apply] at h2
  rw [inner_neg_left]
  linear_combination h2

theorem exists_adj (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) {W : List (Mat n)} (hW : LieW G W)
    {u : H} (hu : IsSm G σ u) : ∃ u', ∀ v, IsSm G σ v → ⟪u, dsW σ W v⟫_ℂ = ⟪u', v⟫_ℂ := by
  induction W generalizing u with
  | nil => exact ⟨u, fun _ _ => rfl⟩
  | cons X W ih =>
    have hW' : LieW G W := fun Y hY => hW Y (List.mem_cons_of_mem _ hY)
    have hX := hW X List.mem_cons_self
    have h1 : IsSm G σ (ds σ X u) := hu.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    obtain ⟨u', hu'⟩ := ih hW' (u := -ds σ X u) (by simpa using h1.smul (-1))
    exact ⟨u', fun v hv => by rw [dsW_cons, inner_ds hσ hiso hu (hv.dsW hσ hW') hX, hu' v hv]⟩

theorem hasDerivAt_dsW_orbit (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v})
    {v : H} (hv : IsSm G σ v) {W : List (Mat n)} (hW : LieW G W) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => dsW σ W (σ (ex X t) v)) (dsW σ W (ds σ X v)) 0 := by
  obtain ⟨U, F, hU, h1U, hF, hfF⟩ := smOn_orbit hσ hv hW 1 hσ.one_mem
  have h0 := hasDerivAt_local (f := fun x => dsW σ W (σ x v)) hX (ex_zero X)
    (hasDerivAt_matrix_exp_zero X) hU h1U hF hfF
  have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  convert h0 using 1
  refine hd.eq_of_inner_right (𝕜 := ℂ) fun u hu => ?_
  obtain ⟨u', hu'⟩ := exists_adj hσ hiso hW hu
  have a1 := (hasDerivAt_const (0 : ℝ) u).inner ℂ h0
  have a2 := (hasDerivAt_const (0 : ℝ) u').inner ℂ (hasDerivAt_ds hσ hv hX)
  have e : (fun t => ⟪u, dsW σ W (σ (ex X t) v)⟫_ℂ) = fun t => ⟪u', σ (ex X t) v⟫_ℂ :=
    funext fun t => hu' _ (hv.apply hσ (hX t))
  rw [e] at a1
  have := a1.unique a2
  simp only [inner_zero_left, add_zero] at this
  rw [hu' _ hs, this]

theorem SmOn.smul' {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    {A : Set E} {c : E → ℂ} {f : E → V} (hc : SmOn A c) (hf : SmOn A f) : SmOn A fun a => c a • f a := fun a ha => by
  obtain ⟨U, F, hU, haU, hF, hfF⟩ := hc a ha
  obtain ⟨U', F', hU', haU', hF', hfF'⟩ := hf a ha
  exact ⟨U ∩ U', fun x => F x • F' x, hU.inter hU', ⟨haU, haU'⟩,
    (hF.mono inter_subset_left).smul (hF'.mono inter_subset_right),
    fun g hg hgA => by simp only [hfF g hg.1 hgA, hfF' g hg.2 hgA]⟩

theorem SmOn.sum' {E V ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
    {A : Set E} {f : ι → E → V} (s : Finset ι) (hf : ∀ i ∈ s, SmOn A (f i)) : SmOn A fun a => ∑ i ∈ s, f i a :=
  _root_.UpperTheory.Reformulated.B.SmoothOnAdditive.main s hf

section Lift

variable [CompleteSpace H] [CompleteSpace H']

theorem Bdd.smOn_orbit {T : H → H'} (hb : Bdd G L σ T) (hl : Lin G σ T) (hσ : RepOn G σ)
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) : SmOn G fun g => T (σ g v) := by
  obtain ⟨C, Ws, hW, hb⟩ := hb
  have hW' : ∀ i, LieW G (Ws.get i) := fun i X hX => hL X (hW _ (List.get_mem _ _) X hX)
  obtain ⟨Λ, hΛ⟩ := exists_factor hl hσ hW' (C := C) fun v hv => by rw [← nu_eq_sum]; exact hb v hv
  exact (SmOn.sum' Finset.univ fun i _ =>
    (FinalFormK.smOn_orbit hσ hv (hW' i)).clm ((Λ i).restrictScalars ℝ)).congr fun g hg => hΛ _ (hv.apply hσ hg)

theorem Bdd.hasDerivAt {T : H → H'} (hb : Bdd G L σ T) (hl : Lin G σ T) (hσ : RepOn G σ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v})
    (hL : ∀ X, L X → ∀ t, ex X t ∈ G) {v : H} (hv : IsSm G σ v) {X : Mat n} (hX : ∀ t, ex X t ∈ G) :
    HasDerivAt (fun t => T (σ (ex X t) v)) (T (ds σ X v)) 0 := by
  obtain ⟨C, Ws, hW, hb⟩ := hb
  have hW' : ∀ i, LieW G (Ws.get i) := fun i X hX => hL X (hW _ (List.get_mem _ _) X hX)
  obtain ⟨Λ, hΛ⟩ := exists_factor hl hσ hW' (C := C) fun v hv => by rw [← nu_eq_sum]; exact hb v hv
  have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
  have e : (fun t => T (σ (ex X t) v)) = fun t => ∑ i, Λ i (dsW σ (Ws.get i) (σ (ex X t) v)) :=
    funext fun t => hΛ _ (hv.apply hσ (hX t))
  rw [e, hΛ _ hs]
  exact HasDerivAt.fun_sum fun i _ => ((Λ i).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ)
    (hasDerivAt_dsW_orbit hσ hiso hd hv (hW' i) hX)

structure TwInt (G : Set (Mat n)) (L : Mat n → Prop) (σ : Mat n → (H →L[ℂ] H)) (τ : Mat n → (H' →L[ℂ] H'))
    {ι : Type} [Fintype ι] (M : Mat n → ι → ι → ℂ) (T : ι → H → H') : Prop where
  lin : ∀ c, Lin G σ (T c)
  bdd : ∀ c, Bdd G L σ (T c)
  eqv : ∀ g ∈ G, ∀ c v, IsSm G σ v → τ g (T c v) = ∑ d, M g c d • T d (σ g v)

variable {ι : Type} [Fintype ι] [DecidableEq ι] {M : Mat n → ι → ι → ℂ} {T : ι → H → H'}

omit [DecidableEq ι] in
theorem TwInt.isSm (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (c : ι) {v : H} (hv : IsSm G σ v) : IsSm G τ (T c v) :=
  (SmOn.sum' Finset.univ fun d _ => SmOn.smul' (hM c d) ((h.bdd d).smOn_orbit (h.lin d) hσ hL hv)).congr
    fun g hg => h.eqv g hg c v hv

theorem TwInt.ds_eq (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖)
    (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {X : Mat n} (hX : ∀ t, ex X t ∈ G) {M' : ι → ι → ℂ}
    (hM' : ∀ c d, HasDerivAt (fun t => M (ex X t) c d) (M' c d) 0) (c : ι) {v : H} (hv : IsSm G σ v) :
    ds τ X (T c v) = T c (ds σ X v) + ∑ d, M' c d • T d v := by
  have h1 : HasDerivAt (fun t => ∑ d, M (ex X t) c d • T d (σ (ex X t) v))
      (∑ d, (M (ex X 0) c d • T d (ds σ X v) + M' c d • T d (σ (ex X 0) v))) 0 :=
    HasDerivAt.fun_sum fun d _ => (hM' c d).smul ((h.bdd d).hasDerivAt (h.lin d) hσ hiso hd hL hv hX)
  have e : (fun t => τ (ex X t) (T c v)) = fun t => ∑ d, M (ex X t) c d • T d (σ (ex X t) v) :=
    funext fun t => h.eqv _ (hX t) c v hv
  unfold ds
  rw [e, h1.deriv]
  simp [ex_zero, hM1, hσ.map_one, Finset.sum_add_distrib, ite_smul, ds]

theorem TwInt.bdd_dsW (h : TwInt G L σ τ M T) (hσ : RepOn G σ) (hτ : RepOn G τ)
    (hiso : ∀ g ∈ G, ∀ v, ‖σ g v‖ = ‖v‖) (hd : Dense {v | IsSm G σ v}) (hL : ∀ X, L X → ∀ t, ex X t ∈ G)
    (hM : ∀ c d, SmOn G fun g => M g c d) (hM1 : ∀ c d, M 1 c d = if c = d then 1 else 0)
    {W : List (Mat n)} (hW : ∀ X ∈ W, L X) (c : ι) : Bdd G L σ fun v => dsW τ W (T c v) := by
  induction W using List.reverseRecOn generalizing c with
  | nil => exact h.bdd c
  | append_singleton W X ih =>
    have hW' : ∀ Y ∈ W, L Y := fun Y hY => hW Y (List.mem_append_left _ hY)
    have hLX : L X := hW X (by simp)
    have hX := hL X hLX
    have hWG : LieW G W := fun Y hY => hL Y (hW' Y hY)
    have hM' : ∀ c d, ∃ m, HasDerivAt (fun t => M (ex X t) c d) m 0 := fun c d => by
      obtain ⟨U, F, hU, h1U, hF, hfF⟩ := hM c d 1 hσ.one_mem
      exact ⟨_, hasDerivAt_local (f := fun g => M g c d) hX (ex_zero X) (hasDerivAt_matrix_exp_zero X)
        hU h1U hF hfF⟩
    choose M' hM' using hM'
    have h1 := (ih hW' c).comp_dsW hσ hL (W' := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hLX
    refine (h1.add (Bdd.sum Finset.univ fun d _ => (ih hW' d).smul (M' c d))).congr fun v hv => ?_
    have hs : IsSm G σ (ds σ X v) := hv.dsW hσ (W := [X]) fun Y hY => by rw [List.mem_singleton.1 hY]; exact hX
    have hsum : ∀ s : Finset ι, IsSm G τ (∑ d ∈ s, M' c d • T d v) ∧
        dsW τ W (∑ d ∈ s, M' c d • T d v) = ∑ d ∈ s, M' c d • dsW τ W (T d v) := by
      intro s
      induction s using Finset.induction_on with
      | empty => exact ⟨by simpa using IsSm.zero, by simpa using dsW_smul hτ (IsSm.zero (G := G) (σ := τ)) 0 hWG⟩
      | insert i s hi ih' =>
        have hi' := h.isSm hσ hL hM i hv
        rw [Finset.sum_insert hi, Finset.sum_insert hi, dsW_add hτ (hi'.smul _) ih'.1 hWG, ih'.2,
          dsW_smul hτ hi' _ hWG]
        exact ⟨(hi'.smul _).add ih'.1, rfl⟩
    rw [dsW_append]
    show dsW τ W (ds τ X (T c v)) = dsW τ W (T c (ds σ X v)) + _
    rw [h.ds_eq hσ hiso hd hL hM1 hX hM' c hv, dsW_add hτ (h.isSm hσ hL hM c hs) (hsum _).1 hWG, (hsum _).2]

end Lift

end CompanionTheory.D.gk.FinalFormK
