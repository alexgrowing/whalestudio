import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4

open IsLocalRing UpperTheory.V UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

namespace UpperTheory.V.Ws.X1

variable {k : Type} [Field k]

private theorem ent (X : sp4 k) (i j : Fin 4) : (sgn i * sgn j) • X.1 j.rev i.rev = -X.1 i j := by
  have h : adj X.1 = -X.1 := X.2
  have h' := congrFun (congrFun h i) j
  rwa [adj_apply, Matrix.neg_apply] at h'

private theorem conj_mem (n : M4 k) (X : sp4 k) : adj n * X.1 * n ∈ sp4 k := by
  show adj (adj n * X.1 * n) = -(adj n * X.1 * n)
  rw [(grp k).1, (grp k).1, (grp k).2.1, show adj X.1 = -X.1 from X.2]
  noncomm_ring

private noncomputable def cj (n : M4 k) : sp4 k →ₗ[k] sp4 k where
  toFun X := ⟨adj n * X.1 * n, conj_mem n X⟩
  map_add' X Y := Subtype.ext (by simp [mul_add, add_mul])
  map_smul' c X := Subtype.ext (by simp)

private noncomputable def cjE (n : M4 k) (hn : IsGSp 1 n) : sp4 k ≃ₗ[k] sp4 k :=
  LinearEquiv.ofLinear (cj n) (cj (adj n))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      show adj n * (adj (adj n) * X.1 * adj n) * n = X.1
      rw [(grp k).2.1, mul_assoc n, ← mul_assoc (adj n), h, one_mul, mul_assoc, h, mul_one]))
    (LinearMap.ext fun X => Subtype.ext (by
      have h : adj n * n = 1 := by simpa [IsGSp] using hn
      have h' : n * adj n = 1 := mul_eq_one_comm.mp h
      show adj (adj n) * (adj n * X.1 * n) * adj n = X.1
      rw [(grp k).2.1, mul_assoc (adj n), ← mul_assoc n, h', one_mul, mul_assoc, h', mul_one]))

private theorem cj_one (X : M4 k) : adj 1 * X * 1 = X := by
  rw [(grp k).2.2.2.2.1, one_mul, mul_one]

private theorem mem_borel_identity_iff_upper (X : sp4 k) : X ∈ bor (1 : M4 k) ↔ IsUp X.1 := by
  show IsUp (adj 1 * X.1 * 1) ↔ _
  rw [cj_one]

private theorem mem_nilradical_identity_iff (X : sp4 k) : X ∈ nil (1 : M4 k) ↔ ∀ i j, i ≤ j → X.1 i j = 0 := by
  show (∀ i j, i ≤ j → (adj 1 * X.1 * 1 : M4 k) i j = 0) ↔ _
  rw [cj_one]

private theorem bor_eq (n : M4 k) (hn : IsGSp 1 n) : bor n = (bor 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_borel_identity_iff_upper]
  rfl

private theorem nil_eq (n : M4 k) (hn : IsGSp 1 n) : nil n = (nil 1).comap (cjE n hn : sp4 k →ₗ[k] sp4 k) := by
  ext X
  rw [Submodule.mem_comap, mem_nilradical_identity_iff]
  rfl

private theorem compl1 : IsCompl (bor (1 : M4 k)) (nil 1) := by
  constructor
  · rw [Submodule.disjoint_def]
    intro X h1 h2
    rw [mem_borel_identity_iff_upper] at h1
    rw [mem_nilradical_identity_iff] at h2
    apply Subtype.ext
    ext i j
    rcases lt_or_ge j i with h | h
    · exact h1 i j h
    · exact h2 i j h
  · rw [codisjoint_iff, eq_top_iff]
    intro X _
    let L : M4 k := Matrix.of fun i j => if j < i then X.1 i j else 0
    have hL : L ∈ sp4 k := by
      show adj L = -L
      ext i j
      rw [adj_apply, Matrix.neg_apply]
      simp only [L, Matrix.of_apply, Fin.rev_lt_rev]
      split_ifs with h
      · exact ent X i j
      · simp
    have hU : X.1 - L ∈ sp4 k := Submodule.sub_mem _ X.2 hL
    rw [Submodule.mem_sup]
    refine ⟨⟨X.1 - L, hU⟩, ?_, ⟨L, hL⟩, ?_, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      simp [L, h]
    · rw [mem_nilradical_identity_iff]
      intro i j h
      simp [L, not_lt.mpr h]
    · apply Subtype.ext
      simp

private theorem up_mem (a b c d e f : k) : (!![a, c, d, e; 0, b, f, d; 0, 0, -b, -c; 0, 0, 0, -a] : M4 k) ∈ sp4 k := by
  show adj _ = -_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev]

private theorem up_zero (X : sp4 k) (hu : IsUp X.1) (h0 : X.1 0 0 = 0) (h1 : X.1 1 1 = 0) (h2 : X.1 0 1 = 0)
    (h3 : X.1 0 2 = 0) (h4 : X.1 0 3 = 0) (h5 : X.1 1 2 = 0) : X = 0 := by
  apply Subtype.ext
  ext i j
  have e := ent X i j
  fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1, h2, h3, h4, h5] at e ⊢ <;>
    first
    | exact hu _ _ (by decide)
    | exact e
    | exact neg_eq_zero.mp e.symm
    | skip

private theorem bor1 : Module.finrank k (bor (1 : M4 k)) = 6 := by
  let f : bor (1 : M4 k) →ₗ[k] (Fin 6 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1, X.1.1 0 1, X.1.1 0 2, X.1.1 0 3, X.1.1 1 2]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have hc : ∀ t, f X t = 0 := fun t => congrFun hX t
    exact Subtype.ext (up_zero X.1 ((mem_borel_identity_iff_upper X.1).mp X.2) (hc 0) (hc 1) (hc 2) (hc 3) (hc 4) (hc 5))
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, v 2, v 3, v 4; 0, v 1, v 5, v 3; 0, 0, -v 1, -v 2; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · rw [mem_borel_identity_iff_upper]
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

private theorem tor2 : Module.finrank k (tor k) = 2 := by
  let f : tor k →ₗ[k] (Fin 2 → k) :=
    { toFun := fun X => ![X.1.1 0 0, X.1.1 1 1]
      map_add' := fun X Y => by
        ext t
        fin_cases t <;> rfl
      map_smul' := fun c X => by
        ext t
        fin_cases t <;> rfl }
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro X hX
    have h0 : X.1.1 0 0 = 0 := congrFun hX 0
    have h1 : X.1.1 1 1 = 0 := congrFun hX 1
    have hd : Matrix.IsDiag X.1.1 := X.2
    apply Subtype.ext
    apply Subtype.ext
    ext i j
    have e := ent X.1 i j
    fin_cases i <;> fin_cases j <;> simp [sgn, Fin.rev, h0, h1] at e ⊢ <;>
      first
      | exact hd (by decide)
      | exact e
      | exact neg_eq_zero.mp e.symm
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨⟨⟨!![v 0, 0, 0, 0; 0, v 1, 0, 0; 0, 0, -v 1, -0; 0, 0, 0, -v 0],
      up_mem _ _ _ _ _ _⟩, ?_⟩, ?_⟩
    · show Matrix.IsDiag _
      intro i j h
      fin_cases i <;> fin_cases j <;> simp_all
    · ext t
      fin_cases t <;> rfl
  rw [LinearEquiv.finrank_eq (LinearEquiv.ofBijective f ⟨hinj, hsurj⟩), Module.finrank_fin_fun]

end UpperTheory.V.Ws.X1

theorem UpperTheory.V.Ws.X1.spDims :
    ∀ (k : Type) [Field k], (2 : k) ≠ 0 → Module.finrank k (tor k) = 2 ∧ ∀ n : M4 k, IsGSp 1 n → Module.finrank k (bor n) = 6 ∧ IsCompl (bor n) (nil n) := by
  intro k _ _
  refine ⟨X1.tor2, fun n hn => ⟨?_, ?_⟩⟩
  · have hm : (bor (1 : M4 k)).map ((X1.cjE n hn).symm : sp4 k →ₗ[k] sp4 k)
        = (bor 1).comap (X1.cjE n hn : sp4 k →ₗ[k] sp4 k) :=
      Submodule.map_equiv_eq_comap_symm _ _
    rw [X1.bor_eq n hn, ← hm, LinearEquiv.finrank_map_eq, X1.bor1]
  · rw [X1.bor_eq n hn, X1.nil_eq n hn]
    exact (Submodule.orderIsoMapComap (X1.cjE n hn)).symm.isCompl X1.compl1
