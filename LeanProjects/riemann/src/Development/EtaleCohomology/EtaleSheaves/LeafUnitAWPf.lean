import Development.EtaleCohomology.EtaleSheaves.LeafRingUnitPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafUnitAWPf
open LateralTheory.E.CupProductRingLaws LateralTheory.E.LeafRingUnitPf

theorem sec_sub {R : Type} [CommRing R] (F : Shv R) (s : ℤ) (hs : s < 0) (U : Scheme.{0}) :
    Subsingleton (Sec ((res R F).X s) U) := by
  have hz : IsZero ((res R F).X s) := by
    unfold res
    exact CochainComplex.isZero_of_isStrictlyGE _ 0 _ (by omega)
  have h2 : IsZero (((res R F).X s).obj.obj (op U)) :=
    Functor.map_isZero ((sheafToPresheaf _ _) ⋙ (evaluation _ _).obj (op U)) hz
  exact ModuleCat.isZero_iff_subsingleton.mp h2

theorem sub_zero_self {E : Spc} {N : ℕ} {U : Scheme.{0}} (x : Sx E N U) (h : 0 + N ≤ N) : x.sub 0 N h = x := by
  have : SimplexCategory.subinterval (n := N) 0 N h = 𝟙 _ := by
    ext i : 3
    simp [SimplexCategory.subinterval]
  simp [Sx.sub, this]

theorem main_gen (q : ℕ) [NeZero q] (E : Spc) (i j : ℤ) (hij : i = j)
    (μ : Pair (res _ (tw q 0)) (res _ (tw q i)) (res _ (tw q j)))
    (hU : ∀ (U : Scheme.{0}) (t w : ℤ) (h : 0 + t = w) (a : Sec ((res _ (tw q 0)).X 0) U) (b : Sec ((res _ (tw q i)).X t) U),
      Loc U (fun V g => ∃ ζ : Prim q Γ(V, ⊤), Sec.res g a = resGen 0 ζ) → HEq (μ.mul U 0 t w h a b) b)
    (α : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q 0)) 0) (hα : OneLoc α)
    (n k : ℤ) (hnk : n = k) (β : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q i)) n) :
    ∃ γ : Cocycle ((chains (ZMod q)).obj E) (res _ (tw q j)) k, μ.IsAW (show 0 + n = k by omega) α.1 β.1 γ.1 ∧
      CohomologyClass.mk γ = Ht.cast hnk hij (CohomologyClass.mk β : Ht q E n i) := by
  subst hij hnk
  refine ⟨β, ?_, rfl⟩
  intro N w h U x
  have hmz : ∀ (s t w : ℤ) (h : s + t = w) (a : Sec ((res _ (tw q 0)).X s) U) (b : Sec ((res _ (tw q i)).X t) U),
      s < 0 → μ.mul U s t w h a b = 0 := by
    intro s t w h a b hs
    have := sec_sub (tw q 0) s hs U
    rw [Subsingleton.elim a 0]
    simp
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero, add_zero]
  · subst h
    show _ = (n * ((0 : ℕ) : ℤ)).negOnePow • μ.mul U (-((0 : ℕ) : ℤ) + 0) (-((N - 0 : ℕ) : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 _ rfl U (x.sub 0 0 (by omega))) (ev β.1 (N - 0) _ rfl U (x.sub 0 (N - 0) (by omega)))
    have h1 : (n * ((0 : ℕ) : ℤ)).negOnePow = 1 := by simp
    rw [h1, one_smul]
    show _ = μ.mul U 0 (-(N : ℤ) + n) (-(N : ℤ) + n) (by omega)
      (ev α.1 0 0 (by simp) U (x.sub 0 0 (by omega))) (ev β.1 N _ rfl U (x.sub 0 N (by omega)))
    rw [sub_zero_self]
    exact (eq_of_heq (hU U _ _ (by omega) _ (ev β.1 N _ rfl U x) (hα U (x.sub 0 0 (by omega))))).symm
  · intro p _
    rw [hmz, smul_zero]
    simp
    omega

theorem LeafUnitAW_of : LeafUnitAW := by
  intro q _ E i μ hU α hα n β
  exact main_gen q E i (0 + i) (by ring) μ hU α hα n (0 + n) (by ring) β

end LateralTheory.E.LeafUnitAWPf
