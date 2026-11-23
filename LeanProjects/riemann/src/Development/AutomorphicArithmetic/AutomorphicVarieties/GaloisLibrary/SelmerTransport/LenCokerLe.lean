import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.RestrictionMemInvariantH1

open ReciprocityTheory.Gal UpperTheory.V.Base

private theorem len_ker_eq_coker {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (f : A →ₗ[R] A) (hfin : Module.length R A ≠ ⊤) :
    Module.length R (A ⧸ LinearMap.range f) = Module.length R (LinearMap.ker f) := by
  have h1 := Module.length_eq_add_of_exact (LinearMap.range f).subtype (LinearMap.range f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  have h2 := Module.length_eq_add_of_exact (LinearMap.ker f).subtype (LinearMap.ker f).mkQ
    (Submodule.subtype_injective _) (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ _)
  rw [(f.quotKerEquivRange).length_eq] at h2
  have h3 : Module.length R (LinearMap.range f) ≠ ⊤ := by
    intro h
    rw [h, top_add] at h1
    exact hfin h1
  rw [h1, add_comm] at h2
  exact (WithTop.add_right_inj h3).1 h2

private theorem len_sup_ne_top {R A : Type} [CommRing R] [AddCommGroup A] [Module R A]
    (S T : Submodule R A) (hS : Module.length R S ≠ ⊤) (hT : Module.length R T ≠ ⊤) :
    Module.length R (S ⊔ T : Submodule R A) ≠ ⊤ := by
  have h := Module.length_le_of_surjective (S.subtype.coprod T.subtype).rangeRestrict
    (LinearMap.surjective_rangeRestrict _)
  rw [LinearMap.range_coprod, Submodule.range_subtype, Submodule.range_subtype,
    Module.length_prod] at h
  exact ne_top_of_le_ne_top (WithTop.add_ne_top.2 ⟨hS, hT⟩) h

private theorem len_map_le {R N : Type} [CommRing R] [AddCommGroup N] [Module R N] (a : R)
    (F : Submodule R N) (hF : Module.length R F ≠ ⊤) :
    Module.length R (F.map (LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))).mkQ) ≤
      Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  let g : F →ₗ[R] F.map P.mkQ := P.mkQ.submoduleMap F
  have hg : Function.Surjective g := LinearMap.submoduleMap_surjective _ _
  have hle : LinearMap.range (a • (LinearMap.id : F →ₗ[R] F)) ≤ LinearMap.ker g := by
    rintro _ ⟨x, rfl⟩
    refine Subtype.ext ?_
    show P.mkQ (a • (x : N)) = 0
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hg' : Function.Surjective (Submodule.liftQ _ g hle) := by
    intro y
    obtain ⟨x, rfl⟩ := hg y
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  refine (Module.length_le_of_surjective _ hg').trans ?_
  rw [len_ker_eq_coker _ hF]
  refine Module.length_le_of_injective
    (F.subtype.restrict (p := LinearMap.ker (a • (LinearMap.id : F →ₗ[R] F)))
      (q := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) ?_) ?_
  · intro x hx
    exact congrArg Subtype.val hx
  · intro x y h
    have h' := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')

theorem UpperTheory.V.Base.lenCokerLe :
    ∀ (R N : Type) [CommRing R] [AddCommGroup N] [Module R N], (∀ m : N, Module.length R (Submodule.span R {m}) ≠ ⊤) → ∀ a : R,
      Module.length R (N ⧸ LinearMap.range (a • (LinearMap.id : N →ₗ[R] N))) ≤ Module.length R (LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N))) := by
  intro R N _ _ _ hN a
  by_contra hlt
  rw [not_le] at hlt
  set P := LinearMap.range (a • (LinearMap.id : N →ₗ[R] N)) with hP
  set K := LinearMap.ker (a • (LinearMap.id : N →ₗ[R] N)) with hK
  have key : ∀ k : ℕ, ∃ F : Submodule R N, Module.length R F ≠ ⊤ ∧
      (k : ℕ∞) ≤ Module.length R (F.map P.mkQ) := by
    intro k
    induction k with
    | zero => exact ⟨⊥, by simp, by simp⟩
    | succ k ih =>
      obtain ⟨F, hF, hk⟩ := ih
      have h1 : Module.length R (F.map P.mkQ) ≤ Module.length R K := len_map_le a F hF
      have h2 : F.map P.mkQ ≠ ⊤ := by
        intro h
        rw [h, Module.length_top] at h1
        exact absurd hlt (not_lt.2 h1)
      obtain ⟨y, hy⟩ : ∃ y, y ∉ F.map P.mkQ := by
        by_contra hh
        exact h2 (eq_top_iff.2 fun y _ => by_contra fun h => hh ⟨y, h⟩)
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective P y
      refine ⟨F ⊔ Submodule.span R {x}, len_sup_ne_top _ _ hF (hN x), ?_⟩
      have h3 : F.map P.mkQ < (F ⊔ Submodule.span R {x}).map P.mkQ := by
        refine lt_of_le_of_ne (Submodule.map_mono le_sup_left) fun h => hy ?_
        rw [h]
        exact Submodule.mem_map_of_mem (Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
      have h4 : Order.height (F.map P.mkQ) < ⊤ := by
        rw [← Module.length_submodule]
        exact lt_of_le_of_lt h1 (lt_of_lt_of_le hlt le_top)
      have h5 := Order.height_strictMono h3 h4
      rw [← Module.length_submodule, ← Module.length_submodule] at h5
      rw [Nat.cast_succ]
      exact Order.add_one_le_of_lt (lt_of_le_of_lt hk h5)
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.1 (lt_of_lt_of_le hlt le_top).ne
  obtain ⟨F, hF, hk⟩ := key (n + 1)
  have h := hk.trans (len_map_le a F hF)
  rw [← hK, ← hn] at h
  exact absurd (Nat.cast_le.1 h) (by omega)
