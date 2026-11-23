import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeDeformations.IsHostFrame
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised

open Matrix IsLocalRing ReciprocityTheory.Gal UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Alg UpperTheory.V.UnitaryThreeInertia Module

private theorem mid {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [Module.Finite k B] (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : Function.Exact f g) :
    finrank k B = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by
  have := LinearMap.finrank_range_add_finrank_ker g
  rw [LinearMap.exact_iff.1 h] at this
  omega

private theorem six {k A B C D E F : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B] [Module k B]
    [AddCommGroup C] [Module k C] [AddCommGroup D] [Module k D] [AddCommGroup E] [Module k E]
    [AddCommGroup F] [Module k F] [Module.Finite k B] [Module.Finite k C] [Module.Finite k E]
    (f : A →ₗ[k] B) (g : B →ₗ[k] C) (h : C →ₗ[k] D) (p : D →ₗ[k] E) (q : E →ₗ[k] F)
    (hf : Function.Injective f) (h1 : Function.Exact f g) (h2 : Function.Exact g h) (h3 : Function.Exact h p)
    (h4 : Function.Exact p q) (hq : Function.Surjective q) :
    Module.Finite k D ∧ finrank k A + finrank k C + finrank k E = finrank k B + finrank k D + finrank k F := by
  have hD : Module.Finite k D := by
    have e : Function.Exact h p.rangeRestrict := by
      intro y
      rw [← h3 y, Subtype.ext_iff]
      rfl
    exact Module.Finite.of_exact e p.surjective_rangeRestrict
  refine ⟨hD, ?_⟩
  have a1 := mid f g h1
  have a2 := mid g h h2
  have a3 := mid h p h3
  have a4 := mid p q h4
  have a5 := LinearMap.finrank_range_of_inj hf
  have a6 : finrank k (LinearMap.range q) = finrank k F := by
    rw [LinearMap.range_eq_top.2 hq, finrank_top]
  omega

private theorem cone {k ι A1 A2 : Type} [Field k] [Fintype ι] {L1 L2 : ι → Type} [AddCommGroup A1] [Module k A1]
    [AddCommGroup A2] [Module k A2] [∀ v, AddCommGroup (L1 v)] [∀ v, Module k (L1 v)]
    [∀ v, AddCommGroup (L2 v)] [∀ v, Module k (L2 v)]
    (C Z1 : Submodule k A1) (Z2 : Submodule k A2) (d : A1 →ₗ[k] A2)
    (Cv Z1v ZL : ∀ v, Submodule k (L1 v)) (Z2v : ∀ v, Submodule k (L2 v)) (dv : ∀ v, L1 v →ₗ[k] L2 v)
    (r1 : ∀ v, A1 →ₗ[k] L1 v) (r2 : ∀ v, A2 →ₗ[k] L2 v)
    (hZ : ∀ x, x ∈ Z1 ↔ x ∈ C ∧ d x = 0) (hZv : ∀ v x, x ∈ Z1v v ↔ x ∈ Cv v ∧ dv v x = 0)
    (hC : ∀ v, ∀ x ∈ C, r1 v x ∈ Cv v) (hd : ∀ v x, r2 v (d x) = dv v (r1 v x))
    (hZ2 : ∀ v, ∀ x ∈ Z2, r2 v x ∈ Z2v v) (hL : ∀ v, ZL v ≤ Z1v v)
    (selmerCocycles : Submodule k A1) (hZ1L : ∀ x, x ∈ selmerCocycles ↔ x ∈ Z1 ∧ ∀ v, r1 v x ∈ ZL v)
    (framedTwoCocycles framedTwoCoboundaries : Submodule k (A2 × ∀ v, L1 v))
    (hZ2c : ∀ x, x ∈ framedTwoCocycles ↔ x.1 ∈ Z2 ∧ ∀ v, x.2 v ∈ Cv v ∧ dv v (x.2 v) = r2 v x.1)
    (hB2c : ∀ x, x ∈ framedTwoCoboundaries ↔ ∃ h ∈ C, d h = x.1 ∧ ∀ v, x.2 v - r1 v h ∈ ZL v)
    [Module.Finite k Z1] [∀ v, Module.Finite k (Z1v v)]
    [Module.Finite k (Z2 ⧸ (C.map d).comap Z2.subtype)]
    [∀ v, Module.Finite k (Z2v v ⧸ ((Cv v).map (dv v)).comap (Z2v v).subtype)]
    (hs : ∀ κ : ∀ v, Z2v v, ∃ z : Z2, ∀ v, r2 v z.1 - (κ v).1 ∈ (Cv v).map (dv v)) :
    Module.Finite k (framedTwoCocycles ⧸ framedTwoCoboundaries.comap framedTwoCocycles.subtype) ∧
      finrank k selmerCocycles + ∑ v, finrank k (Z1v v) + finrank k (Z2 ⧸ (C.map d).comap Z2.subtype) =
        finrank k Z1 + ∑ v, finrank k (ZL v) + finrank k (framedTwoCocycles ⧸ framedTwoCoboundaries.comap framedTwoCocycles.subtype) +
          ∑ v, finrank k (Z2v v ⧸ ((Cv v).map (dv v)).comap (Z2v v).subtype) := by
  have hr : ∀ v, ∀ x ∈ Z1, r1 v x ∈ Z1v v := fun v x hx =>
    (hZv v _).2 ⟨hC v x ((hZ x).1 hx).1, by rw [← hd, ((hZ x).1 hx).2, map_zero]⟩
  haveI : ∀ v, Module.Finite k (ZL v) := fun v =>
    Module.Finite.of_injective _ (Submodule.inclusion_injective (hL v))
  let f : selmerCocycles →ₗ[k] Z1 × ∀ v, ZL v :=
    { toFun := fun x => (⟨x.1, ((hZ1L _).1 x.2).1⟩, fun v => ⟨-r1 v x.1, neg_mem (((hZ1L _).1 x.2).2 v)⟩)
      map_add' := fun x y => by ext <;> simp [add_comm]
      map_smul' := fun a x => by ext <;> simp }
  let g : (Z1 × ∀ v, ZL v) →ₗ[k] ∀ v, Z1v v :=
    { toFun := fun x v => ⟨r1 v x.1.1 + (x.2 v).1, add_mem (hr v _ x.1.2) (hL v (x.2 v).2)⟩
      map_add' := fun x y => by ext; simp; abel
      map_smul' := fun a x => by ext; simp }
  let h0 : (∀ v, Z1v v) →ₗ[k] framedTwoCocycles :=
    { toFun := fun y => ⟨(0, fun v => (y v).1), (hZ2c _).2 ⟨zero_mem _, fun v =>
        ⟨((hZv v _).1 (y v).2).1, by simpa using ((hZv v _).1 (y v).2).2⟩⟩⟩
      map_add' := fun x y => by ext <;> simp
      map_smul' := fun a x => by ext <;> simp }
  let p0 : framedTwoCocycles →ₗ[k] Z2 :=
    { toFun := fun y => ⟨y.1.1, ((hZ2c _).1 y.2).1⟩
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  let p : (framedTwoCocycles ⧸ framedTwoCoboundaries.comap framedTwoCocycles.subtype) →ₗ[k] (Z2 ⧸ (C.map d).comap Z2.subtype) :=
    Submodule.mapQ _ _ p0 fun x hx => by
      obtain ⟨h, h1, h2, -⟩ := (hB2c _).1 hx
      exact ⟨h, h1, h2⟩
  let q0 : ∀ v, Z2 →ₗ[k] Z2v v := fun v => (r2 v).restrict (hZ2 v)
  let q : (Z2 ⧸ (C.map d).comap Z2.subtype) →ₗ[k]
      ∀ v, (Z2v v ⧸ ((Cv v).map (dv v)).comap (Z2v v).subtype) :=
    LinearMap.pi fun v => Submodule.mapQ _ _ (q0 v) fun x hx => by
      obtain ⟨h, h1, h2⟩ := hx
      exact ⟨r1 v h, hC v h h1, by rw [← hd, h2]; rfl⟩
  have key := six f g ((Submodule.mkQ _) ∘ₗ h0) p q ?_ ?_ ?_ ?_ ?_ ?_
  · rw [Module.finrank_prod, Module.finrank_pi_fintype, Module.finrank_pi_fintype,
      Module.finrank_pi_fintype] at key
    exact key
  · intro x y hxy
    exact Subtype.ext (congrArg (fun t => t.1.1) hxy)
  · intro x
    constructor
    · intro hx
      have e : ∀ v, r1 v x.1.1 = -(x.2 v).1 := fun v =>
        eq_neg_of_add_eq_zero_left (congrArg Subtype.val (congrFun hx v))
      refine ⟨⟨x.1.1, (hZ1L _).2 ⟨x.1.2, fun v => e v ▸ neg_mem (x.2 v).2⟩⟩, ?_⟩
      refine Prod.ext rfl (funext fun v => Subtype.ext ?_)
      show -r1 v x.1.1 = _
      rw [e, neg_neg]
    · rintro ⟨y, rfl⟩
      funext v
      exact Subtype.ext (add_neg_cancel _)
  · intro y
    rw [LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, hB2c]
    constructor
    · rintro ⟨h, h1, h2, h3⟩
      refine ⟨(⟨h, (hZ h).2 ⟨h1, h2⟩⟩, fun v => ⟨_, h3 v⟩), funext fun v => Subtype.ext ?_⟩
      exact add_sub_cancel _ _
    · rintro ⟨x, rfl⟩
      refine ⟨x.1.1, ((hZ _).1 x.1.2).1, ((hZ _).1 x.1.2).2, fun v => ?_⟩
      show r1 v x.1.1 + (x.2 v).1 - r1 v x.1.1 ∈ _
      rw [add_sub_cancel_left]
      exact (x.2 v).2
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      obtain ⟨h, h1, h2⟩ := (Submodule.Quotient.mk_eq_zero _).1 hy
      have h2' : d h = y.1.1 := h2
      have hy2 := ((hZ2c _).1 y.2).2
      refine ⟨fun v => ⟨y.1.2 v - r1 v h, (hZv v _).2 ⟨sub_mem (hy2 v).1 (hC v h h1), ?_⟩⟩, ?_⟩
      · rw [map_sub, (hy2 v).2, ← hd, h2', sub_self]
      · refine (Submodule.Quotient.eq _).2 ((hB2c _).2 ⟨-h, neg_mem h1, ?_, fun v => ?_⟩)
        · show d (-h) = 0 - y.1.1
          rw [map_neg, h2', zero_sub]
        · show y.1.2 v - r1 v h - y.1.2 v - r1 v (-h) ∈ _
          rw [map_neg, show y.1.2 v - r1 v h - y.1.2 v - -r1 v h = 0 by abel]
          exact zero_mem _
    · rintro ⟨x, hx⟩
      rw [← hx]
      exact (Submodule.Quotient.mk_eq_zero _).2 (zero_mem (C.map d))
  · intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      have e : ∀ v, ∃ c ∈ Cv v, dv v c = r2 v y.1 := fun v =>
        (Submodule.Quotient.mk_eq_zero _).1 (congrFun hy v)
      choose c hc1 hc2 using e
      exact ⟨Submodule.Quotient.mk ⟨(y.1, c), (hZ2c _).2 ⟨y.2, fun v => ⟨hc1 v, hc2 v⟩⟩⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      funext v
      have hx2 := ((hZ2c _).1 x.2).2 v
      exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x.1.2 v, hx2.1, hx2.2⟩
  · intro y
    choose κ hκ using fun v => Submodule.Quotient.mk_surjective _ (y v)
    obtain ⟨z, hz⟩ := hs κ
    refine ⟨Submodule.Quotient.mk z, funext fun v => ?_⟩
    rw [← hκ]
    exact (Submodule.Quotient.eq _).2 (hz v)

private theorem mem_cocycles_iff {R G M : Type} [CommRing R] [Group G] [TopologicalSpace G] [AddCommGroup M] [Module R M]
    [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul R M] (rho : Representation R G M)
    (x : G → M) : x ∈ Z1 rho ↔ x ∈ contMaps R M G ∧ d1 rho x = 0 := by
  refine and_congr Iff.rfl ⟨fun h => funext fun p => ?_, fun h g g' => ?_⟩
  · obtain ⟨g, g'⟩ := p
    rw [d1_apply, h, Pi.zero_apply]; abel
  · have e := congrFun h (g, g')
    rw [d1_apply, Pi.zero_apply] at e
    rw [← sub_eq_zero, ← neg_eq_zero, ← e]; abel

private theorem quot {k A : Type} [Field k] [AddCommGroup A] [Module k A] (B Z : Submodule k A) (h : B ≤ Z)
    [Module.Finite k B] [Module.Finite k (Z ⧸ B.comap Z.subtype)] :
    Module.Finite k Z ∧ finrank k (Z ⧸ B.comap Z.subtype) + finrank k B = finrank k Z := by
  have e := Submodule.comapSubtypeEquivOfLe h
  haveI : Module.Finite k (B.comap Z.subtype) := Module.Finite.equiv e.symm
  haveI : Module.Finite k Z := Module.Finite.of_submodule_quotient (B.comap Z.subtype)
  exact ⟨this, by rw [← e.finrank_eq]; exact Submodule.finrank_quotient_add_finrank _⟩

theorem UpperTheory.selmerComplex_finite_and_euler_characteristic :
    ∀ {O : Type} [CommRing O] [IsLocalRing O] {G Γ ι : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Fintype ι] (F : Frame O G Γ ι) (j : ℤ),
        Continuous F.π → ContAction (F.gbar j) → Module.Finite (ResidueField O) (Gb (ResidueField O) j) →
        (∀ v, B1 (F.gloc j v) ≤ F.ZL j v) →
        Module.Finite (ResidueField O) (H1 (F.gbar j)) → Module.Finite (ResidueField O) (H2 (F.gbar j)) →
        (∀ v, Module.Finite (ResidueField O) (H1 (F.gloc j v))) → (∀ v, Module.Finite (ResidueField O) (H2 (F.gloc j v))) →
        (∀ κ : ∀ v, Z2 (F.gloc j v), ∃ z : Z2 (F.gbar j), ∀ v, F.res2 j v z.1 - (κ v).1 ∈ B2 (F.gloc j v)) →
        Module.Finite (ResidueField O) (F.selmerCohomologyQuotient j) ∧ Module.Finite (ResidueField O) (F.Ob j) ∧
          (finrank (ResidueField O) (F.selmerCohomologyQuotient j) : ℤ) - finrank (ResidueField O) (F.Ob j) =
            (finrank (ResidueField O) (H1 (F.gbar j)) : ℤ) - finrank (ResidueField O) (H2 (F.gbar j)) +
              ∑ v, ((finrank (ResidueField O) (H2 (F.gloc j v)) : ℤ) - finrank (ResidueField O) (Z1 (F.gloc j v)) + finrank (ResidueField O) (F.ZL j v)) := by
  intro O _ _ G Γ ι _ _ _ _ _ _ _ F j hπ hact hfin hB h1 h2 h1v h2v hs
  have hloc : ∀ v, Continuous (F.loc v) := fun v => hπ.comp continuous_subtype_val
  have hL : ∀ v, F.ZL j v ≤ Z1 (F.gloc j v) := fun v y hy => hy.1
  haveI : Module.Finite (ResidueField O) (B1 (F.gbar j)) := Module.Finite.range _
  haveI : ∀ v, Module.Finite (ResidueField O) (B1 (F.gloc j v)) := fun v => Module.Finite.range _
  obtain ⟨fZ, eZ⟩ := quot (B1 (F.gbar j)) (Z1 (F.gbar j)) (coboundaries_le_cocycles _ hact)
  haveI : ∀ v, Module.Finite (ResidueField O) (Z1 (F.gloc j v)) := fun v =>
    (quot (B1 (F.gloc j v)) (Z1 (F.gloc j v)) ((hB v).trans (hL v))).1
  have hZ1L : ∀ x, x ∈ F.selmerCocycles j ↔ x ∈ Z1 (F.gbar j) ∧ ∀ v, F.res1 j v x ∈ F.ZL j v := fun x => by
    simp [Frame.selmerCocycles, Submodule.mem_iInf]
  have hBL : B1 (F.gbar j) ≤ F.selmerCocycles j := fun x hx => (hZ1L x).2 ⟨coboundaries_le_cocycles _ hact hx, fun v => hB v (by
    obtain ⟨m, rfl⟩ := hx
    exact ⟨m, rfl⟩)⟩
  haveI : Module.Finite (ResidueField O) (F.selmerCocycles j) :=
    Module.Finite.of_injective _ (Submodule.inclusion_injective (fun x hx => ((hZ1L x).1 hx).1 : F.selmerCocycles j ≤ Z1 (F.gbar j)))
  have fL : Module.Finite (ResidueField O) (F.selmerCohomologyQuotient j) := inferInstance
  obtain ⟨-, eL⟩ := quot (B1 (F.gbar j)) (F.selmerCocycles j) hBL
  haveI := h2
  haveI := h2v
  have key := @cone (ResidueField O) ι _ _ _ _ _ _ _ _ _ _ _ _ _ _ (contMaps _ _ Γ) (Z1 (F.gbar j)) (Z2 (F.gbar j)) (d1 (F.gbar j))
    (fun v => contMaps _ _ (F.D v)) (fun v => Z1 (F.gloc j v)) (F.ZL j) (fun v => Z2 (F.gloc j v))
    (fun v => d1 (F.gloc j v)) (F.res1 j) (F.res2 j) (mem_cocycles_iff _) (fun v => mem_cocycles_iff _)
    (fun v x hx => Continuous.comp hx (hloc v))
    (fun v x => by
      funext p
      obtain ⟨a, b⟩ := p
      simp [Frame.res1, Frame.res2, LinearMap.funLeft_apply])
    (fun v x hx => (restrictCocycles2 (F.gbar j) (F.loc v) (hloc v) ⟨x, hx⟩).2) hL (F.selmerCocycles j) hZ1L (F.framedTwoCocycles j) (F.framedTwoCoboundaries j)
    (fun x => by simp [Frame.framedTwoCocycles, Submodule.mem_iInf])
    (fun x => by
      rw [Frame.framedTwoCoboundaries, Submodule.mem_sup]
      constructor
      · rintro ⟨_, ⟨h, hh, rfl⟩, _, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨h, hh, by simp, fun v => ?_⟩
        simpa using hz v trivial
      · rintro ⟨h, hh, e, hz⟩
        refine ⟨_, ⟨h, hh, rfl⟩, _, ⟨fun v => x.2 v - F.res1 j v h, fun v _ => hz v, rfl⟩, ?_⟩
        ext <;> simp [e])
    _ _ h2 h2v hs
  refine ⟨fL, key.1, ?_⟩
  have k2 : finrank (ResidueField O) (F.selmerCocycles j) + ∑ v, finrank (ResidueField O) (Z1 (F.gloc j v)) +
        finrank (ResidueField O) (H2 (F.gbar j)) =
      finrank (ResidueField O) (Z1 (F.gbar j)) + ∑ v, finrank (ResidueField O) (F.ZL j v) +
        finrank (ResidueField O) (F.Ob j) + ∑ v, finrank (ResidueField O) (H2 (F.gloc j v)) := key.2
  have eZ' : finrank (ResidueField O) (H1 (F.gbar j)) + finrank (ResidueField O) (B1 (F.gbar j)) =
      finrank (ResidueField O) (Z1 (F.gbar j)) := eZ
  have eL' : finrank (ResidueField O) (F.selmerCohomologyQuotient j) + finrank (ResidueField O) (B1 (F.gbar j)) =
      finrank (ResidueField O) (F.selmerCocycles j) := eL
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Nat.cast_sum, ← Nat.cast_sum, ← Nat.cast_sum]
  clear key eZ eL
  omega
