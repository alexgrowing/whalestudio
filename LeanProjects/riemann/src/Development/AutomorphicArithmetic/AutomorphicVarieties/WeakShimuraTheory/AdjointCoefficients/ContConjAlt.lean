import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GspLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem isLocallyConstant_finset_sum {S Y ι : Type} [TopologicalSpace S] [AddCommMonoid Y] (t : Finset ι)
    (f : ι → S → Y) (h : ∀ i ∈ t, IsLocallyConstant (f i)) : IsLocallyConstant fun x => ∑ i ∈ t, f i x := by
  classical
  induction t using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : Y)
  | insert a t ha ih =>
    simp only [Finset.sum_insert ha]
    exact IsLocallyConstant.comp₂ (h a (Finset.mem_insert_self a t))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi)) (· + ·)

private theorem cont_conj {S R : Type} [TopologicalSpace S] [CommRing R] (I : Ideal R) (x : S → M4 R) (a b : M4 R)
    (h : ∀ i j, AdicCont I fun s => x s i j) (i j : Fin 4) : AdicCont I fun s => (a * x s * b) i j := by
  intro N
  have e : (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j)) = fun s =>
      ∑ l, (∑ k, Ideal.Quotient.mk (I ^ N) (a i k) * Ideal.Quotient.mk (I ^ N) (x s k l)) *
        Ideal.Quotient.mk (I ^ N) (b l j) := by
    funext s
    simp [Matrix.mul_apply, map_sum, map_mul]
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (I ^ N) ((a * x s * b) i j))
  rw [e]
  refine isLocallyConstant_finset_sum _ _ fun l _ => ?_
  refine IsLocallyConstant.comp₂ ?_ (IsLocallyConstant.const _) (· * ·)
  refine isLocallyConstant_finset_sum _ _ fun k _ => ?_
  exact IsLocallyConstant.comp₂ (IsLocallyConstant.const _) (h k l N) (· * ·)

private theorem cont_push {Λ S A A' : Type} [CommRing Λ] [IsLocalRing Λ] [TopologicalSpace S] [CommRing A] [Algebra Λ A]
    [IsCO Λ A] [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p : A →ₐ[Λ] A') (x : S → A)
    (h : AdicCont (maximalIdeal A) x) : AdicCont (maximalIdeal A') fun s => p (x s) := by
  intro N
  have hm : Ideal.map p (maximalIdeal A) ≤ maximalIdeal A' := by
    rw [Ideal.map_le_iff_le_comap]
    intro y hy
    rw [Ideal.mem_comap, ← res_eq_zero_iff Λ A', res_map, res_eq_zero_iff]
    exact hy
  have hle : maximalIdeal A ^ N ≤ Ideal.comap p (maximalIdeal A' ^ N) := by
    rw [← Ideal.map_le_iff_le_comap, Ideal.map_pow]
    exact pow_le_pow_left' hm N
  have e : (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s))) =
      fun s => Ideal.quotientMap (maximalIdeal A' ^ N) (p : A →+* A') hle (Ideal.Quotient.mk (maximalIdeal A ^ N) (x s)) := by
    funext s
    rfl
  show IsLocallyConstant (fun s => Ideal.Quotient.mk (maximalIdeal A' ^ N) (p (x s)))
  rw [e]
  exact (h N).comp _

private theorem gsp_conj {R : Type} [CommRing R] {c : R} {x n : M4 R} (hx : IsGSp c x) (hn : IsGSp 1 n) :
    IsGSp c (adj n * x * n) := by
  obtain ⟨hmul, hadj, -⟩ := grp R
  have hn1 : adj n * n = 1 := by
    have := hn
    unfold IsGSp at this
    rw [this, one_smul]
  have hn2 : n * adj n = 1 := mul_eq_one_comm.mp hn1
  have hx' : adj x * x = c • 1 := hx
  show adj (adj n * x * n) * (adj n * x * n) = c • 1
  rw [hmul, hmul, hadj]
  calc adj n * (adj x * n) * (adj n * x * n) = adj n * (adj x * (n * adj n) * x) * n := by
        simp only [Matrix.mul_assoc]
    _ = c • 1 := by
        rw [hn2, Matrix.mul_one, hx', Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, hn1]

private theorem gsp_push {Λ A A' : Type} [CommRing Λ] [CommRing A] [Algebra Λ A] [CommRing A'] [Algebra Λ A']
    (p : A →ₐ[Λ] A') {c : Λ} {x : M4 A} (hx : IsGSp (algebraMap Λ A c) x) : IsGSp (algebraMap Λ A' c) (x.map p) := by
  have := isGSp_map (p : A →+* A') hx
  rwa [AlgHom.coe_toRingHom, AlgHom.commutes] at this

theorem UpperTheory.V.Ws.X1.slEx :
    ∀ {Λ : Type} [CommRing Λ] [IsLocalRing Λ] [IsNoetherianRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ], IsUnit (2 : Λ) → ∀ {Γ V : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] {Gv : V → Type} [∀ v, Group (Gv v)] [∀ v, TopologicalSpace (Gv v)] [∀ v, IsTopologicalGroup (Gv v)] (loc : ∀ v, Gv v →* Γ), (∀ v, Continuous (loc v)) → ∀ {A R : Type} [CommRing A] [Algebra Λ A] [IsCO Λ A] [CommRing R] [Algebra Λ R] [IsCO Λ R] (p : A →ₐ[Λ] R), Function.Surjective p → maximalIdeal A * RingHom.ker p = ⊥ → ∀ (ν : Γ →* Λˣ) (r : Γ →* M4 R) (n : V → M4 R), AdicCont (maximalIdeal Λ) (fun g => (ν g : Λ)) → WP loc (fun g => algebraMap Λ R (ν g)) r n → (∀ i j, AdicCont (maximalIdeal R) fun g => r g i j) → ∃ D : SL loc ν r n p, ∀ (A' : Type) [CommRing A'] [Algebra Λ A'] [IsCO Λ A'] (p' : A →ₐ[Λ] A') (p'' : A' →ₐ[Λ] R), p''.comp p' = p → ∃ D' : SL loc ν r n p'', (∀ s t, D'.om s t = (D.om s t).map p') ∧ ∀ v s, D'.de v s = (D.de v s).map p' := by
  intro Λ _ _ _ _ h2 Γ V _ _ _ Gv _ _ _ loc hloc A R _ _ _ _ _ _ p hp hker ν r n hν hW hr
  obtain ⟨yr, hyc, hym, hyp, -⟩ := X1.gspLift h2 p hp hker Γ (fun g => ν g) (fun g => r g) hν hr hW.mult
  letI : TopologicalSpace V := ⊥
  haveI : DiscreteTopology V := ⟨rfl⟩
  obtain ⟨yn, -, hnm, hnp, -⟩ := X1.gspLift h2 p hp hker V (fun _ => 1) n
    (by intro N; exact IsLocallyConstant.of_discrete _)
    (by intro i j N; exact IsLocallyConstant.of_discrete _)
    (fun v => by simpa using hW.sp v)
  have hnm' : ∀ v, IsGSp 1 (yn v) := fun v => by simpa using hnm v
  have ht : ∀ v, ∃ y : Gv v → M4 A, (∀ i j, AdicCont (maximalIdeal A) fun s => y s i j) ∧
      (∀ s, IsGSp (algebraMap Λ A (ν (loc v s))) (y s)) ∧
      (∀ s, (y s).map p = adj (n v) * r (loc v s) * n v) ∧ ∀ s, IsUp (y s) := by
    intro v
    obtain ⟨y, h1, h2', h3, h4⟩ := X1.gspLift h2 p hp hker (Gv v) (fun s => ν (loc v s))
      (fun s => adj (n v) * r (loc v s) * n v)
      (by intro N; exact (hν N).comp_continuous (hloc v))
      (by
        intro i j
        exact cont_conj _ _ _ _ (fun i j N => (hr i j N).comp_continuous (hloc v)) i j)
      (fun s => gsp_conj (hW.mult _) (hW.sp v))
    exact ⟨y, h1, h2', h3, h4 (hW.flag v)⟩
  choose yt hyt using ht
  let D : SL loc ν r n p := ⟨yr, hyc, hym, hyp, yn, hnm', hnp, yt, fun v => (hyt v).1, fun v => (hyt v).2.1,
    fun v => (hyt v).2.2.2, fun v => (hyt v).2.2.1⟩
  refine ⟨D, ?_⟩
  intro A' _ _ _ p' p'' hpp
  have hc : ∀ a, p'' (p' a) = p a := fun a => by rw [← hpp]; rfl
  have hmap : ∀ X : M4 A, (X.map p').map p'' = X.map p := fun X => by
    ext i j
    simp [hc]
  have hm1 : ∀ X Y : M4 A, (X * Y).map p' = X.map p' * Y.map p' := fun X Y => by
    ext i j
    simp [Matrix.mul_apply, map_sum]
  have hm2 : ∀ X Y : M4 A, (X - Y).map p' = X.map p' - Y.map p' := fun X Y => by
    ext i j
    simp
  have hadj : ∀ X : M4 A, adj (X.map p') = (adj X).map p' := fun X => adj_map (p' : A →+* A') X
  refine ⟨⟨fun g => (yr g).map p', ?_, ?_, ?_, fun v => (yn v).map p', ?_, ?_, fun v s => (yt v s).map p',
    ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro i j
    exact cont_push p' _ (hyc i j)
  · intro g
    exact gsp_push p' (hym g)
  · intro g
    rw [hmap, hyp]
  · intro v
    have := isGSp_map (p' : A →+* A') (hnm' v)
    simpa using this
  · intro v
    rw [hmap, hnp]
  · intro v i j
    exact cont_push p' _ ((hyt v).1 i j)
  · intro v s
    exact gsp_push p' ((hyt v).2.1 s)
  · intro v s i j hij
    simp [(hyt v).2.2.2 s i j hij]
  · intro v s
    rw [hmap]
    exact (hyt v).2.2.1 s
  · intro s t
    show (yr s).map p' * (yr t).map p' - (yr (s * t)).map p' = (yr s * yr t - yr (s * t)).map p'
    rw [hm2, hm1]
  · intro v s
    show (yr (loc v s)).map p' - (yn v).map p' * (yt v s).map p' * adj ((yn v).map p') =
      (yr (loc v s) - yn v * yt v s * adj (yn v)).map p'
    rw [hm2, hm1, hm1, hadj]
