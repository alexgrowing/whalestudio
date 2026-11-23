import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedTanDefs

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws

theorem rank_le_of_lowest : ∀ {k V : Type} [Field k] [AddCommGroup V] [Module k V] (π : ℤ → V →ₗ[k] V) (T U : Submodule k V),
      (∀ p q x, π p (π q x) = if p = q then π q x else 0) → (∃ lo : ℤ, ∀ q < lo, π q = 0) →
      (∃ hi : ℤ, ∀ x, (∀ q < hi, π q x = 0) → x = 0) →
      (∀ p, ∀ x ∈ T, (∀ q < p, π q x = 0) → π p x ∈ U) → Module.rank k T ≤ Module.rank k U := by
  intro k V _ _ _ π T U h ⟨lo, hlo⟩ ⟨hi, hhi⟩ H
  let K : ℤ → Submodule k V := fun p => ⨅ q < p, LinearMap.ker (π q)
  have hK : ∀ p x, x ∈ K p ↔ ∀ q < p, π q x = 0 := fun p x => by simp [K, Submodule.mem_iInf]
  have step : ∀ (W : Submodule k V) p, Module.rank k ↥(W ⊓ K p) =
      Module.rank k ↥((W ⊓ K p).map (π p)) + Module.rank k ↥(W ⊓ K (p + 1)) := by
    intro W p
    rw [← LinearMap.rank_range_add_rank_ker ((π p).domRestrict (W ⊓ K p)), LinearMap.range_domRestrict]
    congr 1
    rw [LinearMap.ker_domRestrict]
    have e : W ⊓ K (p + 1) = (W ⊓ K p) ⊓ LinearMap.ker (π p) := by
      ext x
      simp only [Submodule.mem_inf, hK, LinearMap.mem_ker]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, fun q hq => h2 q (by omega)⟩, h2 p (by omega)⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩
        refine ⟨h1, fun q hq => ?_⟩
        rcases lt_or_eq_of_le (show q ≤ p by omega) with h4 | rfl
        exacts [h2 q h4, h3]
    rw [e, ← Submodule.map_comap_subtype (W ⊓ K p) (LinearMap.ker (π p))]
    exact (Submodule.equivMapOfInjective _ (W ⊓ K p).subtype_injective _).rank_eq
  have main : ∀ p ≤ max hi lo, Module.rank k ↥(T ⊓ K p) ≤ Module.rank k ↥(U ⊓ K p) := by
    intro p hp
    induction p, hp using Int.le_induction_down with
    | base =>
      have : T ⊓ K (max hi lo) = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        exact hhi x fun q hq => (hK _ _).1 hx.2 q (lt_max_of_lt_left hq)
      rw [this]; simp
    | pred n hn ih =>
      rw [step T, step U, sub_add_cancel]
      refine add_le_add (Submodule.rank_mono ?_) ih
      rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
      refine ⟨π (n - 1) x, ⟨H _ x h1 ((hK _ _).1 h2), (hK _ _).2 fun q hq => ?_⟩, ?_⟩
      · rw [h, if_neg hq.ne]
      · rw [h, if_pos rfl]
  have top : K lo = ⊤ := by
    rw [eq_top_iff]
    intro x _
    exact (hK _ _).2 fun q hq => by simp [hlo q hq]
  have := main lo (le_max_right _ _)
  rwa [top, inf_top_eq, inf_top_eq] at this

theorem tan_lowest : ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k] (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ), Symp m →
      (∀ g, Lim m (c.r g) (c₀.r g)) → (∀ v, Lim m (c.n v) (c₀.n v)) → ∀ p : ℤ, ∀ x ∈ Φ.Tan S c,
      (∀ g, FGe m p (x.1 g)) → (∀ v, FGe m p (x.2 v)) → Φ.cmpT m p x ∈ Φ.Tan S c₀ := by
  intro O Γ _ _ _ Φ k _ S c c₀ m hm hr hn p x ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ hX hY
  have c3 : ∀ {A B Z : M4 k}, FGe m 0 A → FGe m 0 B → FGe m p Z →
      FGe m p (A * Z * B) ∧ cmp m p (A * Z * B) = cmp m 0 A * cmp m p Z * cmp m 0 B := by
    intro A B Z hA hB hZ
    have h1 := (hA.mul hZ).mul hB
    have h2 := cmp_mul (hA.mul hZ) hB
    rw [cmp_mul hA hZ] at h2
    simp only [zero_add, add_zero] at h1 h2
    exact ⟨h1, h2⟩
  have csp : ∀ {Z : M4 k}, Z ∈ sp4 k → cmp m p Z ∈ sp4 k := by
    intro Z hZ
    show adj _ = -_
    rw [← cmp_adj hm, show adj Z = -Z from hZ, map_neg]
  have cz : ∀ {Z : M4 k} {i j}, Z i j = 0 → cmp m p Z i j = 0 := by
    intro Z i j h
    simp [cmp_apply, h]
  have cn : ∀ v {Z : M4 k}, FGe m p Z → adj (c₀.n v) * cmp m p Z * c₀.n v = cmp m p (adj (c.n v) * Z * c.n v) := by
    intro v Z hZ
    rw [(c3 ((hn v).1.adj hm) (hn v).1 hZ).2, cmp_adj hm, ← (hn v).2]
  refine ⟨a1.comp (cmp m p), fun g => csp (a2 g), fun g h => ?_, fun g h => ?_, fun i j h => cz (a5 h),
    fun g i j h1 h2 => ?_, fun v => ⟨csp (a7 v).1, fun i j h => ?_⟩, fun v s hs i j h => ?_⟩
  · simp only [Fr.cmpT_fst]
    rw [a3, map_add, (c3 (hr g).1 (hr g⁻¹).1 (hX h)).2, ← (hr g).2, ← (hr g⁻¹).2]
  · rw [Fr.cmpT_fst, a4 g h, map_zero]
  · have := cmp_mul (hX g) (hr g).1
    rw [add_zero, ← (hr g).2] at this
    rw [Fr.cmpT_fst, ← this]
    exact cz (a6 g i j h1 h2)
  · rw [Fr.cmpT_snd, cn v (hY v)]
    exact cz ((a7 v).2 i j h)
  · have h3 := c3 (hr s).1 (hr s⁻¹).1 (hY v)
    rw [← (hr s).2, ← (hr s⁻¹).2] at h3
    rw [Fr.cmpT_snd, Fr.cmpT_fst, ← h3.2, ← map_add, ← map_sub, cn v (((hX s).add h3.1).sub (hY v))]
    exact cz (a8 v s hs i j h)

theorem tan_flow {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] (Φ : Fr O Γ) {k : Type} [Field k]
    (S : Finset (ℤ × ℤ)) (c c₀ : PD Φ.ι Γ k) (m : Fin 4 → ℤ) (hm : Symp m)
    (hr : ∀ g, Lim m (c.r g) (c₀.r g)) (hn : ∀ v, Lim m (c.n v) (c₀.n v)) :
    Module.rank k (Φ.TanS S c) ≤ Module.rank k (Φ.TanS S c₀) := by
  obtain ⟨N, hN⟩ : ∃ N : ℤ, ∀ i j, |m i - m j| < N :=
    ⟨∑ z : Fin 4 × Fin 4, |m z.1 - m z.2| + 1, fun i j => Int.lt_add_one_of_le
      (Finset.single_le_sum (f := fun z : Fin 4 × Fin 4 => |m z.1 - m z.2|) (fun _ _ => abs_nonneg _) (Finset.mem_univ (i, j)))⟩
  have ge : ∀ {p : ℤ} {Z : M4 k}, (∀ q < p, cmp m q Z = 0) → FGe m p Z := by
    intro p Z h i j hij
    have := congrFun (congrFun (h _ hij) i) j
    simpa [cmp_apply] using this
  have cc : ∀ (p q : ℤ) (Z : M4 k), cmp m p (cmp m q Z) = if p = q then cmp m q Z else 0 := by
    intro p q Z
    ext i j
    by_cases h : p = q
    · subst h; simp only [cmp_apply, if_true]; split_ifs <;> rfl
    · simp only [cmp_apply, if_neg h, Matrix.zero_apply]
      split_ifs with h1 h2
      · omega
      all_goals rfl
  refine rank_le_of_lowest (Φ.cmpT m) _ _ (fun p q x => ?_) ⟨-N, fun q hq => ?_⟩ ⟨N, fun x hx => ?_⟩ fun p x hx h => ?_
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · rw [Fr.cmpT_fst, Fr.cmpT_fst, cc]; split_ifs <;> rfl
    · rw [Fr.cmpT_snd, Fr.cmpT_snd, cc]; split_ifs <;> rfl
  · have : ∀ Z : M4 k, cmp m q Z = 0 := fun Z => by
      ext i j
      have := abs_lt.1 (hN i j)
      rw [cmp_apply, if_neg (by omega)]; rfl
    exact LinearMap.ext fun x => Prod.ext (funext fun g => this _) (funext fun v => this _)
  · refine Prod.ext (funext fun g => ?_) (funext fun v => ?_) <;> ext i j
    · exact ge (fun q hq => congrArg (·.1 g) (hx q hq)) i j (abs_lt.1 (hN i j)).2
    · exact ge (fun q hq => congrArg (·.2 v) (hx q hq)) i j (abs_lt.1 (hN i j)).2
  · exact tan_lowest Φ S c c₀ m hm hr hn p x hx (fun g => ge fun q hq => congrArg (·.1 g) (h q hq))
      fun v => ge fun q hq => congrArg (·.2 v) (h q hq)

end UpperTheory.V.Ws
