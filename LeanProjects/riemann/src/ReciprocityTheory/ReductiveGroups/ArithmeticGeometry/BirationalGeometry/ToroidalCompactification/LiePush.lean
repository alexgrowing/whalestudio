import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

variable {S : Type} [CommRing S] {X : Scheme.{0}} {x : Sp S ⟶ X} {G : Over X} {G' : Over (Sp S)} [GrpObj G] [GrpObj G']
  {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G x φ)
include h

theorem inj_over {T : Over (Sp S)} {u v : T ⟶ G'} (e : u.left ≫ φ = v.left ≫ φ) : u = v := Over.OverMorphism.ext (h.1.hom_ext e (by simp))

theorem tan_push (w : epsR S ⟶ G') : IsTangent w ↔
    Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = (1 : Over.mk x ⟶ G).left := by
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have hmul : ∀ {T : Over (Sp S)} (a b : T ⟶ G'), pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b :=
    fun {T} a b => Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : ∀ T : Over (Sp S), pushPt h.1.w (1 : T ⟶ G') = 1 := by
    intro T
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have hη : η[G'].left ≫ φ = x ≫ η[G].left := by
    have e := congrArg (fun g => g.left) (hone (Over.mk (𝟙 (Sp S))))
    simp only [pushPt, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e
  have hfa : Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (epsR S).hom = 𝟙 _ := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    rw [← Spec.map_id]
    congr 1
    all_goals
      ext r
      first
        | (simp [TrivSqZeroExt.algebraMap_eq_inl]; done)
        | (simp; done)
  let t : Over.mk (𝟙 (Sp S)) ⟶ epsR S :=
    Over.homMk (Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom) hfa
  rw [oneL]
  simp only [Over.mk_hom]
  constructor
  · intro hw
    unfold IsTangent at hw
    rw [← Category.assoc, hw, hη]
  · intro hw
    unfold IsTangent
    have key : t ≫ w = 1 := by
      apply inj_over h
      show Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ w.left ≫ φ = _
      rw [hw, oneL, Category.assoc, hη]
      simp
    have e := congrArg (fun g => g.left) key
    simp only [Over.comp_left, t, Over.homMk_left, oneL, Over.mk_hom] at e
    simpa using e

theorem prod_push {n : ℕ} {T : Over (Sp S)} (u : Fin n → (T ⟶ G')) :
    (List.ofFn u).prod.left ≫ φ = (List.ofFn fun i => pushPt h.1.w (u i)).prod.left := by
  have hmul : ∀ a b : T ⟶ G', pushPt h.1.w (a * b) = pushPt h.1.w a * pushPt h.1.w b := fun a b =>
    Over.OverMorphism.ext (h.2 T a b (pushPt h.1.w a) (pushPt h.1.w b) rfl rfl).symm
  have hone : pushPt h.1.w (1 : T ⟶ G') = 1 := by
    have e1 : pushPt h.1.w (1 : T ⟶ G') * pushPt h.1.w 1 = pushPt h.1.w 1 := by
      rw [← hmul, _root_.one_mul]
    exact mul_right_cancel (e1.trans (_root_.one_mul _).symm)
  have key : ∀ {m : ℕ} (v : Fin m → (T ⟶ G')),
      pushPt h.1.w (List.ofFn v).prod = (List.ofFn fun i => pushPt h.1.w (v i)).prod := by
    intro m
    induction m with
    | zero => intro v; simp only [List.ofFn_zero, List.prod_nil]; exact hone
    | succ m ih => intro v; simp only [List.ofFn_succ, List.prod_cons]; rw [hmul, ih]
  exact congrArg (fun f => f.left) (key u)

theorem comb_push {n : ℕ} (c : Fin n → S) (v : Fin n → (epsR S ⟶ G')) (w : epsR S ⟶ G') : IsLieComb c v w ↔
    ∃ u : Fin n → (Over.mk (Geo.Tor.spMap (algebraMap S (DualNumber S)) ≫ x) ⟶ G),
      (∀ i, (u i).left = Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left ≫ φ) ∧ (List.ofFn u).prod.left = w.left ≫ φ := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine ⟨fun i => pushPt h.1.w (u i), fun i => ?_, (prod_push h u).symm⟩
    simp [pushPt, hu i]
  · rintro ⟨u, hu, hw⟩
    have hs : ∀ i, Geo.Tor.spMap (epsScaleR (c i)) ≫ (epsR S).hom = (epsR S).hom := by
      intro i
      simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
      congr 1
      ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    let u' : Fin n → (epsR S ⟶ G') := fun i =>
      Over.homMk (Geo.Tor.spMap (epsScaleR (c i)) ≫ (v i).left) (by rw [Category.assoc, Over.w (v i)]; exact hs i)
    refine ⟨u', fun i => rfl, ?_⟩
    apply inj_over h
    have e : (fun i => pushPt h.1.w (u' i)) = u :=
      funext fun i => Over.OverMorphism.ext (by simp [pushPt, u', hu i])
    rw [prod_push h u', ← hw, e]

omit h in
theorem comb_baseChange {R : Type} [CommRing R] {G₀ : Over (Sp R)} [GrpObj G₀] (f : R →+* S) {ψ : G'.left ⟶ G₀.left}
    (h : IsGrpPullback G' G₀ (Geo.Tor.spMap f) ψ) {n : ℕ} {c : Fin n → R} {v : Fin n → (epsR R ⟶ G₀)} {w : epsR R ⟶ G₀}
    (hc : IsLieComb c v w) {v' : Fin n → (epsR S ⟶ G')} {w' : epsR S ⟶ G'}
    (hv : ∀ i, (v' i).left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ (v i).left)
    (hw : w'.left ≫ ψ = Geo.Tor.spMap (dualMapR f) ≫ w.left) : IsLieComb (fun i => f (c i)) v' w' := by
  obtain ⟨u, hu, rfl⟩ := hc
  have hs : ∀ s : S, Geo.Tor.spMap (epsScaleR s) ≫ (epsR S).hom = (epsR S).hom := by
    intro s
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first | simp [epsScaleR] | simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hd : Geo.Tor.spMap (dualMapR f) ≫ (epsR R).hom = (epsR S).hom ≫ Geo.Tor.spMap f := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext r <;> first
      | (simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR]; done)
      | simp [dualMapR, TrivSqZeroExt.algebraMap_eq_inl, TrivSqZeroExt.fst_inl, TrivSqZeroExt.snd_inl]
  have hcomm : ∀ i, Geo.Tor.spMap (dualMapR f) ≫ Geo.Tor.spMap (epsScaleR (c i)) =
      Geo.Tor.spMap (epsScaleR (f (c i))) ≫ Geo.Tor.spMap (dualMapR f) := by
    intro i
    simp only [Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    ext a <;> first
      | (simp [dualMapR, epsScaleR]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, mul_comm]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, map_mul, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [dualMapR, epsScaleR, smul_eq_mul, TrivSqZeroExt.algebraMap_eq_inl]; clear * -; done)
  let d : Over.mk ((epsR S).hom ≫ Geo.Tor.spMap f) ⟶ epsR R := Over.homMk (Geo.Tor.spMap (dualMapR f)) hd
  have cm : ∀ a b : epsR R ⟶ G₀, d ≫ (a * b) = (d ≫ a) * (d ≫ b) := fun a b => by
    show d ≫ (lift a b ≫ μ) = lift (d ≫ a) (d ≫ b) ≫ μ
    rw [comp_lift_assoc]
  have c1 : d ≫ (1 : epsR R ⟶ G₀) = 1 := by
    show d ≫ (toUnit _ ≫ η) = toUnit _ ≫ η
    rw [comp_toUnit_assoc]
  have key : ∀ {m : ℕ} (a : Fin m → (epsR R ⟶ G₀)),
      d ≫ (List.ofFn a).prod = (List.ofFn fun i => d ≫ a i).prod := by
    intro m
    induction m with
    | zero => intro a; simp only [List.ofFn_zero, List.prod_nil]; exact c1
    | succ m ih => intro a; simp only [List.ofFn_succ, List.prod_cons]; rw [cm, ih]
  let u' : Fin n → (epsR S ⟶ G') := fun i =>
    Over.homMk (Geo.Tor.spMap (epsScaleR (f (c i))) ≫ (v' i).left)
      (by rw [Category.assoc, Over.w (v' i)]; exact hs _)
  have e2 : (fun i => d ≫ u i) = fun i => pushPt h.1.w (u' i) := by
    funext i
    apply Over.OverMorphism.ext
    simp only [Over.comp_left, d, Over.homMk_left, pushPt, u', hu i, Category.assoc, hv i]
    rw [← Category.assoc, hcomm i, Category.assoc]
  refine ⟨u', fun i => rfl, ?_⟩
  apply inj_over h
  rw [hw, prod_push h u']
  show (d ≫ (List.ofFn u).prod).left = _
  rw [key, e2]

omit h in
theorem comb_iff_coord {n d : ℕ} {y : ∀ m : ℕ, sp (R₀ := S) (JetR S (Fin n) m) ⟶ G'} (hy : IsUnivChart G' n y) (c : Fin d → S)
    {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTan (v i)) {w : epsR S ⟶ G'} (hw : IsTan w) :
    IsLieComb c v w ↔ tcoord hy w hw = ∑ i, c i • tcoord hy (v i) (hv i) := by
  obtain ⟨k, e⟩ := prodPts_tan hy c v hv
  rw [isLieComb_iff]
  exact ⟨fun q => (tcoord_congr hy q hw k).trans e, fun q => tan_ext hy hw k (q.trans e.symm)⟩

omit h in
theorem eq_of_comb_single [IsLocalRing S] [Smooth G'.hom] {d : ℕ} {v : Fin d → (epsR S ⟶ G')} (hv : ∀ i, IsTangent (v i))
    {w : epsR S ⟶ G'} (hw : IsTangent w) (j : Fin d) (hc : IsLieComb (Pi.single j 1) v w) : w = v j := by
  obtain ⟨u, hu, rfl⟩ := hc
  have oneL : ∀ {Y : Scheme.{0}} (T H : Over Y) [GrpObj H], (1 : T ⟶ H).left = T.hom ≫ η[H].left := by
    intro Y T H _
    show (toUnit T ≫ η[H]).left = _
    rw [Over.comp_left]
    congr 1
    all_goals first
      | simpa using Over.w (toUnit T)
      | (have e := Over.w (toUnit T)
         rwa [show (𝟙_ (Over Y)).hom = 𝟙 Y from rfl, Category.comp_id] at e)
  have single : ∀ {m : ℕ} (a : Fin m → (epsR S ⟶ G')) (k : Fin m), (∀ i, i ≠ k → a i = 1) →
      (List.ofFn a).prod = a k := by
    intro m
    induction m with
    | zero => intro a k; exact k.elim0
    | succ m ih =>
      intro a k ha
      rw [List.ofFn_succ, List.prod_cons]
      rcases Fin.eq_zero_or_eq_succ k with rfl | ⟨k', rfl⟩
      · have ht : (fun i : Fin m => a i.succ) = fun _ => 1 := funext fun i => ha _ (Fin.succ_ne_zero i)
        rw [ht]
        simp
      · rw [ha 0 (Fin.succ_ne_zero k').symm, _root_.one_mul]
        exact ih (fun i => a i.succ) k' (fun i hi => ha _ (fun e => hi (Fin.succ_injective _ e)))
  have hv' : ∀ i, Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom ≫ (v i).left = η[G'].left := hv
  have h0 : Geo.Tor.spMap (epsScaleR (0 : S)) =
      (epsR S).hom ≫ Geo.Tor.spMap (TrivSqZeroExt.fstHom S S S).toRingHom := by
    simp only [epsR, Over.mk_hom, Geo.Tor.spMap, ← Spec.map_comp]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done)
      | (simp [epsScaleR]; done))
  have h1 : Geo.Tor.spMap (epsScaleR (1 : S)) = 𝟙 _ := by
    simp only [Geo.Tor.spMap]
    rw [← Spec.map_id]
    congr 1
    all_goals (ext r <;> first
      | (simp [epsScaleR]; done)
      | (simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]; done))
  have hu1 : ∀ i, i ≠ j → u i = 1 := by
    intro i hi
    apply Over.OverMorphism.ext
    rw [hu i, Pi.single_eq_of_ne hi, h0, oneL, Category.assoc, hv' i]
  have huj : u j = v j := by
    apply Over.OverMorphism.ext
    rw [hu j, Pi.single_eq_same, h1, Category.id_comp]
  rw [single u j hu1, huj]

omit h in
theorem coords_basis [IsLocalRing S] [Smooth G'.hom] {d n : ℕ} {v : Fin d → (epsR S ⟶ G')} {u : Fin n → (epsR S ⟶ G')}
    (hv : IsLieBasis v) (hu : IsLieBasis u) (U : Fin n → Fin d → S) (hU : ∀ i, IsLieComb (U i) v (u i)) (z : Fin d → S) :
    ∃! a : Fin n → S, ∀ j, ∑ i, a i * U i j = z j := by
  obtain ⟨m, y, hy⟩ := univChartLoc G'
  have tv := fun i => (isTan_iff _).2 (hv.1 i)
  have tu := fun i => (isTan_iff _).2 (hu.1 i)
  obtain ⟨tw, -⟩ := prodPts_tan hy z v tv
  have hz : IsLieComb z v (prodPts z v) := (isLieComb_iff _ _ _).2 rfl
  have key : ∀ a : Fin n → S, IsLieComb a u (prodPts z v) ↔ ∀ j, ∑ i, a i * U i j = z j := fun a => by
    have e : ∑ i, a i • tcoord hy (u i) (tu i) = ∑ j, (∑ i, a i * U i j) • tcoord hy (v j) (tv j) := by
      simp only [(comb_iff_coord hy _ tv (tu _)).1 (hU _), Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    rw [comb_iff_coord hy a tu tw, e, ← comb_iff_coord hy _ tv tw, ← funext_iff]
    exact ⟨fun q => (hv.2 _ ((isTan_iff _).1 tw)).unique q hz, fun q => q ▸ hz⟩
  simpa only [key] using hu.2 _ ((isTan_iff _).1 tw)

end ReciprocityTheory.ChartRestriction.G.Chart
