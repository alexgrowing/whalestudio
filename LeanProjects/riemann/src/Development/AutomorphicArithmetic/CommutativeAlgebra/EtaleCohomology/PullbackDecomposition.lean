import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CrystallineComparison

set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory CrystallineSemistableComparison

namespace UpperTheory.Ru.crystallineComparison

variable {l : ℕ} [Fact l.Prime]

private theorem isDec_surj {A : Test l} {S : Fam A} (h : IsDec S) (i : S.ι) :
    Function.Surjective (PAlg.Hom.f (S.f i).hom) := by
  classical
  intro b
  obtain ⟨a, ha⟩ := h.2 (Pi.single i b)
  exact ⟨a, by simpa using congrFun ha i⟩

private theorem exists_idem {A : Test l} {S : Fam A} (h : IsDec S) :
    ∃ e : S.ι → A.obj.A, CompleteOrthogonalIdempotents e ∧
      (∀ i, PAlg.Hom.f (S.f i).hom (e i) = 1) ∧
      ∀ i a, PAlg.Hom.f (S.f i).hom a = 0 → a * e i = 0 := by
  classical
  choose e he using fun i => h.2 (Pi.single i (1 : (S.B i).obj.A))
  have hv : ∀ i j, PAlg.Hom.f (S.f j).hom (e i) = (Pi.single i 1 : ∀ k, (S.B k).obj.A) j :=
    fun i j => congrFun (he i) j
  have ext' : ∀ x y : A.obj.A, (∀ j, PAlg.Hom.f (S.f j).hom x = PAlg.Hom.f (S.f j).hom y) → x = y :=
    fun x y hxy => h.1 (funext hxy)
  have hsame : ∀ i, PAlg.Hom.f (S.f i).hom (e i) = 1 := fun i => by rw [hv, Pi.single_eq_same]
  have hne : ∀ i j, j ≠ i → PAlg.Hom.f (S.f j).hom (e i) = 0 := fun i j hji => by
    rw [hv, Pi.single_eq_of_ne hji]
  refine ⟨e, ⟨⟨?_, ?_⟩, ?_⟩, hsame, ?_⟩
  · intro i
    refine ext' _ _ fun j => ?_
    rw [map_mul]
    by_cases hji : j = i
    · subst hji; rw [hsame, one_mul]
    · rw [hne i j hji, zero_mul]
  · intro i i' hii
    refine ext' _ _ fun j => ?_
    rw [map_mul, map_zero]
    by_cases hji : j = i
    · subst hji; rw [hne i' j hii, mul_zero]
    · rw [hne i j hji, zero_mul]
  · refine ext' _ _ fun j => ?_
    rw [map_sum, map_one, Finset.sum_eq_single j, hsame]
    · intro i _ hij
      exact hne i j hij.symm
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  · intro i a ha
    refine ext' _ _ fun j => ?_
    rw [map_mul, map_zero]
    by_cases hji : j = i
    · subst hji; rw [ha, zero_mul]
    · rw [hne i j hji, mul_zero]

private theorem pullback_decomposition {A A' : Test l} (φ : A ⟶ A') (S : Fam A) (h : IsDec S) :
    ∃ (B' : S.ι → Test l) (f' : ∀ i, A' ⟶ B' i) (ψ : ∀ i, S.B i ⟶ B' i),
      IsDec (⟨S.ι, B', f'⟩ : Fam A') ∧ ∀ i, S.f i ≫ ψ i = φ ≫ f' i := by
  obtain ⟨e, he, h1, h0⟩ := exists_idem h
  obtain ⟨B', f', hd, hf⟩ := decEx l A' S.ι (fun i => PAlg.Hom.f φ.hom (e i))
    (he.map (PAlg.Hom.f φ.hom))
  have key : ∀ i, RingHom.ker (PAlg.Hom.f (S.f i).hom) ≤
      RingHom.ker ((PAlg.Hom.f (f' i).hom).comp (PAlg.Hom.f φ.hom)) := by
    intro i a ha
    have ha0 : a * e i = 0 := h0 i a ha
    have h2 : PAlg.Hom.f (f' i).hom (PAlg.Hom.f φ.hom a) * 1 = 0 := by
      have h3 := hf i
      rw [← h3, ← map_mul, ← map_mul, ha0, map_zero, map_zero]
    simpa [RingHom.mem_ker] using h2
  let g : ∀ i, (S.B i).obj.A →+* (B' i).obj.A := fun i =>
    (PAlg.Hom.f (S.f i).hom).liftOfRightInverse (Function.surjInv (isDec_surj h i))
      (Function.rightInverse_surjInv _) ⟨_, key i⟩
  have hg : ∀ i a, g i (PAlg.Hom.f (S.f i).hom a) = PAlg.Hom.f (f' i).hom (PAlg.Hom.f φ.hom a) :=
    fun i a => RingHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hcomm : ∀ i, (g i).comp (S.B i).obj.s = (B' i).obj.s := by
    intro i
    refine RingHom.ext fun x => ?_
    have c1 : PAlg.Hom.f (S.f i).hom (A.obj.s x) = (S.B i).obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm (S.f i).hom) x
    have c2 : PAlg.Hom.f φ.hom (A.obj.s x) = A'.obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm φ.hom) x
    have c3 : PAlg.Hom.f (f' i).hom (A'.obj.s x) = (B' i).obj.s x :=
      RingHom.congr_fun (PAlg.Hom.comm (f' i).hom) x
    rw [RingHom.comp_apply, ← c1, hg, c2, c3]
  refine ⟨B', f', fun i => ObjectProperty.homMk (⟨g i, hcomm i⟩ : PAlg.Hom _ _), hd, fun i => ?_⟩
  apply ObjectProperty.hom_ext
  apply PAlg.Hom.ext
  exact RingHom.ext fun a => hg i a

theorem partsEx :
    UpperTheory.Ru.crystallineComparison.PartsEx := by
  intro l _
  refine ⟨{ Cov := fun S => IsDec S, triv := ?_, pull := ?_, trans := ?_, epi := ?_, disj := ?_ },
    fun _ _ => Iff.rfl⟩
  · intro A
    constructor
    · intro a b hab
      exact congrFun hab ()
    · intro b
      exact ⟨b (), funext fun _ => rfl⟩
  · intro A A' φ S h
    exact pullback_decomposition φ S h
  · intro A S T hS hT
    constructor
    · intro a b hab
      refine hS.1 (funext fun i => (hT i).1 (funext fun j => ?_))
      exact congrFun hab ⟨i, j⟩
    · intro c
      choose b hb using fun i => (hT i).2 (fun j => c ⟨i, j⟩)
      obtain ⟨a, ha⟩ := hS.2 b
      refine ⟨a, funext fun x => ?_⟩
      obtain ⟨i, j⟩ := x
      have h1 : PAlg.Hom.f (S.f i).hom a = b i := congrFun ha i
      have h2 := congrFun (hb i) j
      simp only at h2
      rw [← h1] at h2
      exact h2
  · intro A S h i
    refine ⟨fun {X} u v huv => ?_⟩
    apply ObjectProperty.hom_ext
    apply PAlg.Hom.ext
    refine RingHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := isDec_surj h i b
    have := congrArg (fun w => PAlg.Hom.f w.hom a) huv
    exact this
  · intro A S h i j hij X u v huv
    classical
    obtain ⟨a, ha⟩ := h.2 (Pi.single i 1)
    have hi : PAlg.Hom.f (S.f i).hom a = 1 := by
      have := congrFun ha i
      simpa using this
    have hj : PAlg.Hom.f (S.f j).hom a = 0 := by
      have := congrFun ha j
      simpa [Pi.single_eq_of_ne hij.symm] using this
    have h10 : (1 : X.obj.A) = 0 := by
      have h3 : PAlg.Hom.f u.hom (PAlg.Hom.f (S.f i).hom a) = PAlg.Hom.f v.hom (PAlg.Hom.f (S.f j).hom a) :=
        congrArg (fun w => PAlg.Hom.f w.hom a) huv
      rw [hi, hj, map_one, map_zero] at h3
      exact h3
    have hs : Subsingleton X.obj.A := subsingleton_of_zero_eq_one h10.symm
    constructor
    · intro a b _
      exact Subsingleton.elim a b
    · intro b
      exact ⟨0, funext fun e => e.elim⟩

end UpperTheory.Ru.crystallineComparison
