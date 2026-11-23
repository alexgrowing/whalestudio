import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdicLattices.CompanionTheory
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Ws.Lat

namespace UpperTheory.V.Ws.Lat

section
variable {R K : Type} [CommRing R] [CommRing K] {f : R →+* K} {t : Kˣ × Kˣ}

private theorem wt_self (i : Fin 4) : wt i i = 0 := by revert i; decide

private theorem tc_entry {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) (i j : Fin 4) :
    f (X' i j) = (wv t (wt i j) : K) * f (X i j) := congrFun (congrFun h i) j

private theorem tc_diag (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) (i : Fin 4) :
    X' i i = X i i := by
  apply hf
  rw [tc_entry h, wt_self]
  simp [wv]

private theorem tc_zero (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {i j : Fin 4}
    (h0 : X i j = 0) : X' i j = 0 := by
  apply hf
  rw [tc_entry h, h0]
  simp

private theorem tc_mul {X X' Y Y' : M4 R} (h : X'.map f = tconj t (X.map f)) (h' : Y'.map f = tconj t (Y.map f)) :
    (X' * Y').map f = tconj t ((X * Y).map f) := by
  obtain ⟨-, -, -, -, -, -, -, -, hmul, -⟩ := grp K
  rw [Matrix.map_mul, Matrix.map_mul, h, h', hmul]

private theorem tc_adj {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) :
    (adj X').map f = tconj t ((adj X).map f) := by
  obtain ⟨-, -, -, -, -, hmap, -⟩ := grp R
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hadj, -⟩ := grp K
  rw [← hmap, ← hmap, h, hadj]

private theorem tc_scalar (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {c : R}
    (hX : X = c • (1 : M4 R)) : X' = c • (1 : M4 R) := by
  subst hX
  ext i j
  by_cases hij : i = j
  · subst hij
    rw [tc_diag hf h]
  · rw [tc_zero hf h (by simp [Matrix.one_apply_ne hij])]
    simp [Matrix.one_apply_ne hij]

private theorem tc_gsp (hf : Function.Injective f) {X X' : M4 R} (h : X'.map f = tconj t (X.map f)) {c : R}
    (hX : IsGSp c X) : IsGSp c X' := tc_scalar hf (tc_mul (tc_adj h) h) hX

end

end UpperTheory.V.Ws.Lat

theorem UpperTheory.V.Ws.Lat.tcPair :
    ∀ {O Γ R K : Type} [CommRing O] [Group Γ] [CommRing R] [CommRing K] (Φ : Fr O Γ) (a : O →+* R) (f : R →+* K), Function.Injective f →
      ∀ (t : Kˣ × Kˣ) (P P' : PD Φ.ι Γ R), TConj f t P P' → Φ.IsPair a P →
      Φ.IsPair a P' ∧ (∀ g i, P'.r g i i = P.r g i i) ∧ (∀ v i s, P'.ψ v i s = P.ψ v i s) ∧ IsConj4 (mapRep f P.r) (mapRep f P'.r) := by
  intro O Γ R K _ _ _ _ Φ a f hf t P P' hT hP
  obtain ⟨hr, hn⟩ := hT
  have hY : ∀ v s, (adj (P'.n v) * P'.r s * P'.n v).map f
      = tconj t ((adj (P.n v) * P.r s * P.n v).map f) := fun v s =>
    tc_mul (tc_mul (tc_adj (hn v)) (hr s)) (hn v)
  have hpsi : ∀ v i s, P'.ψ v i s = P.ψ v i s := fun v i s => tc_diag hf (hY v s) i
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, fun g i => tc_diag hf (hr g) i, hpsi, ?_⟩
  · intro g
    exact tc_gsp hf (hr g) (hP.mult g)
  · intro g hg
    have := tc_scalar hf (hr g) (c := 1) (by rw [one_smul]; exact hP.kill g hg)
    rwa [one_smul] at this
  · intro i j hij
    exact tc_zero hf (hr Φ.g0) (hP.nrm hij)
  · intro v
    obtain ⟨h1, h2, h3⟩ := hP.low v
    refine ⟨tc_gsp hf (hn v) h1, fun i => ?_, fun i j hij => tc_zero hf (hn v) (h3 i j hij)⟩
    rw [tc_diag hf (hn v), h2]
  · intro v s hs i j hij
    exact tc_zero hf (hY v s) (hP.flag v s hs i j hij)
  · intro v s hs i
    rw [hpsi]
    exact hP.mu v s hs i
  · obtain ⟨u, hu⟩ := (grp K).2.2.2.2.2.2.2.2.2.2.2.2 t
    refine ⟨u, fun g => ?_⟩
    change (P'.r g).map f = _
    rw [hr g, hu]
    rfl
