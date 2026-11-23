import Development.EtaleCohomology.TateTwists.KumAddPf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

abbrev LkumTex : Prop := ∀ (q : ℕ) [NeZero q], IsKum q (kumT q)

abbrev LevMk : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}
  (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U),
  (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) →
  ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

abbrev LevDelta : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m)
  (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}),
  (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧
  ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U),
    ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) +
      m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

lemma units_map_appTop_comp {V U X : Scheme.{0}} (g : V ⟶ U) (x : U ⟶ X) (u : (Γ(X, ⊤))ˣ) :
    Units.map g.appTop.hom.toMonoidHom (Units.map x.appTop.hom.toMonoidHom u) =
      Units.map (g ≫ x).appTop.hom.toMonoidHom u := by
  ext; simp; rfl

lemma isUnit_q_pull {U X : Scheme.{0}} (q : ℕ) (x : U ⟶ X) (hq : IsUnit (q : Γ(X, ⊤))) :
    IsUnit (q : Γ(U, ⊤)) := by
  simpa using hq.map x.appTop.hom

theorem kum_pow_coc_of (hk : LkumTex) (hmk : LevMk) (hd : LevDelta) (he : kum_exists) : kum_pow_coc := by
  intro q _ X u hq
  let I := res _ (tw q 1)
  let a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + 0 = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U :=
    fun p s _ U x => if hs : s = 0 then (by subst hs; exact kumT q U (Units.map (x : U ⟶ X).appTop.hom.toMonoidHom u))
      else 0
  have ha : ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a p s h U x) = a p s h V (x.res g) := by
    intro p s h V U g x
    by_cases hs : s = 0
    · subst hs
      simp only [a, dif_pos]
      rw [(hk q).1 V U g _ (isUnit_q_pull q x hq)]
      exact congrArg (kumT q V) (units_map_appTop_comp g x u)
    · simp only [a, dif_neg hs, map_zero]
  obtain ⟨α, hα⟩ := hmk (ZMod q) a ha
  refine ⟨Cocycle.mk (δ 0 1 α) 2 (by norm_num) (δ_δ 0 1 2 α), ⟨?_, ?_⟩, ?_⟩
  · have key : ∀ (U : Scheme.{0}) (x : Sx (sch.obj X) (0 + 1) U), ev (δ 0 1 α) (0 + 1) 0 (by simp) U x = 0 := by
      intro U x
      rw [(hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).2 0 (-1) 0 (by simp) (by simp) x, hα]
      have z : a (0 + 1) (-1) (by simp) U x = 0 := dif_neg (by norm_num)
      have f0 : x.face 0 = x.face 1 := rfl
      rw [z, Fin.sum_univ_two, f0]
      simp [Sec.map]
    exact fun U x => key U x
  · intro U x v hv
    obtain ⟨γ0, _, hγ0⟩ := he q X (u ^ q) hq
    have e1 := hγ0 U x v hv
    have e2 := hγ0 U x (Units.map x.appTop.hom.toMonoidHom u) (by rw [map_pow])
    have h1 := (hd (ZMod q) (n := 0) (m := 1) (by norm_num) α U).1 x
    refine h1.trans ?_
    erw [hα]
    simp only [a, dif_pos]
    exact e2.symm.trans e1
  · rw [CohomologyClass.mk_eq_zero_iff]
    exact ⟨0, by norm_num, α, rfl⟩

end LateralTheory.EtaleFoundations
