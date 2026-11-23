import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubNatCompSubIncl
open AlgebraicGeometry CategoryTheory Limits Opposite GlobalTheory.QcSub

namespace GlobalTheory.QcSub.Local

theorem adjoin_mem_of_away {R A R' A' : Type} [CommRing R] [CommRing A] [CommRing R'] [CommRing A']
    [Algebra R A] [Algebra R R'] [Algebra R' A'] [Algebra A A'] [Algebra R A']
    [IsScalarTower R A A'] [IsScalarTower R R' A'] (g : R) [IsLocalization.Away g R']
    [IsLocalization.Away (algebraMap R A g) A'] (T : Set A) (b : A)
    (hb : algebraMap A A' b ∈ Algebra.adjoin R' (algebraMap A A' '' T)) :
    ∃ m : ℕ, algebraMap R A g ^ m * b ∈ Algebra.adjoin R T := by
  classical
  have hgen : ∀ k : ℕ, algebraMap R A g ^ k ∈ Algebra.adjoin R T := fun k =>
    pow_mem (Subalgebra.algebraMap_mem _ g) k
  have hgA : algebraMap A A' (algebraMap R A g) = algebraMap R' A' (algebraMap R R' g) := by
    rw [← IsScalarTower.algebraMap_apply R A A', ← IsScalarTower.algebraMap_apply R R' A']
  have key : ∀ x ∈ Algebra.adjoin R' (algebraMap A A' '' T), ∃ m : ℕ, ∃ s ∈ Algebra.adjoin R T,
      algebraMap A A' (algebraMap R A g) ^ m * x = algebraMap A A' s := by
    intro x hx
    induction hx using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨t, ht, rfl⟩ := hx
      exact ⟨0, t, Algebra.subset_adjoin ht, by simp⟩
    | algebraMap r =>
      obtain ⟨⟨a, ⟨_, n, rfl⟩⟩, hr⟩ := IsLocalization.surj (Submonoid.powers g) r
      refine ⟨n, algebraMap R A a, Subalgebra.algebraMap_mem _ a, ?_⟩
      have h2 := congrArg (algebraMap R' A') hr
      simp only [map_mul, map_pow] at h2
      rw [mul_comm, hgA, h2, ← IsScalarTower.algebraMap_apply R R' A',
        ← IsScalarTower.algebraMap_apply R A A']
    | add x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, algebraMap R A g ^ m2 * s1 + algebraMap R A g ^ m1 * s2,
        add_mem (mul_mem (hgen _) hs1) (mul_mem (hgen _) hs2), ?_⟩
      rw [map_add, map_mul, map_mul, map_pow, map_pow, ← e1, ← e2]
      ring
    | mul x y _ _ hx hy =>
      obtain ⟨m1, s1, hs1, e1⟩ := hx
      obtain ⟨m2, s2, hs2, e2⟩ := hy
      refine ⟨m1 + m2, s1 * s2, mul_mem hs1 hs2, ?_⟩
      rw [map_mul, ← e1, ← e2]
      ring
  obtain ⟨m, s, hs, hms⟩ := key _ hb
  rw [← map_pow, ← map_mul] at hms
  obtain ⟨⟨_, k, rfl⟩, hk⟩ :=
    (IsLocalization.eq_iff_exists (Submonoid.powers (algebraMap R A g)) A').mp hms
  refine ⟨k + m, ?_⟩
  have h3 : algebraMap R A g ^ (k + m) * b = algebraMap R A g ^ k * s := by
    rw [pow_add, mul_assoc]
    exact hk
  rw [h3]
  exact mul_mem (hgen k) hs

theorem mem_gen_of_local (X : Scheme.{0}) (F : X.Opensᵒᵖ ⥤ CommRingCat) (α : X.presheaf ⟶ F)
    (hα : ((Scheme.AffineZariskiSite.toOpensFunctor X).op.whiskerLeft α).Coequifibered)
    (V W : X.Opens) (T : Set (F.obj (op V))) (b : F.obj (op W))
    (H : ∀ x ∈ W ⊓ V, ∃ D : X.Opens, IsAffineOpen D ∧ x ∈ D ∧ ∃ (hW : D ≤ W) (hV : D ≤ V),
      (F.map (homOfLE hW).op).hom b ∈ gen F α hV T)
    (W' : X.Opens) (hW' : IsAffineOpen W') (hW : W' ≤ W) (hV : W' ≤ V) :
    (F.map (homOfLE hW).op).hom b ∈ gen F α hV T := by
  classical
  let _ : Algebra Γ(X, W') (F.obj (op W')) := (α.app (op W')).hom.toAlgebra
  have comp : ∀ {U₁ U₂ U₃ : X.Opens} (h₁₂ : U₂ ≤ U₁) (h₂₃ : U₃ ≤ U₂) (y : F.obj (op U₁)),
      (F.map (homOfLE h₂₃).op).hom ((F.map (homOfLE h₁₂).op).hom y) =
        (F.map (homOfLE (h₂₃.trans h₁₂)).op).hom y := by
    intro U₁ U₂ U₃ h₁₂ h₂₃ y
    show (F.map (homOfLE h₁₂).op ≫ F.map (homOfLE h₂₃).op).hom y = _
    rw [← F.map_comp]
    rfl
  let b' := (F.map (homOfLE hW).op).hom b
  let T' : Set (F.obj (op W')) := (F.map (homOfLE hV).op).hom '' T
  let S := Algebra.adjoin Γ(X, W') T'
  let I : Ideal Γ(X, W') :=
    (Subalgebra.toSubmodule S).comap (LinearMap.toSpanSingleton Γ(X, W') (F.obj (op W')) b')
  have hI : ∀ r, r ∈ I ↔ (α.app (op W')).hom r * b' ∈ S := fun r => by
    simp only [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply, Subalgebra.mem_toSubmodule,
      Algebra.smul_def]
    rfl
  have key : ∀ (D : X.Opens) (f : Γ(X, W')) (hfD : X.basicOpen f ≤ D) (hDW : D ≤ W) (hDV : D ≤ V),
      (F.map (homOfLE hDW).op).hom b ∈ gen F α hDV T → f ∈ I.radical := by
    intro D f hfD hDW hDV hbD
    let _ : Algebra Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      (α.app (op (X.basicOpen f))).hom.toAlgebra
    let _ : Algebra (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      (F.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    let _ : Algebra Γ(X, W') (F.obj (op (X.basicOpen f))) :=
      ((F.map (homOfLE (X.basicOpen_le f)).op).hom.comp (α.app (op W')).hom).toAlgebra
    have : IsScalarTower Γ(X, W') (F.obj (op W')) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun _ => rfl)
    have : IsScalarTower Γ(X, W') Γ(X, X.basicOpen f) (F.obj (op (X.basicOpen f))) :=
      IsScalarTower.of_algebraMap_eq (fun x => by
        have h := congrArg (fun φ => φ.hom x) (α.naturality (homOfLE (X.basicOpen_le f)).op)
        exact h.symm)
    have : IsLocalization.Away f Γ(X, X.basicOpen f) := hW'.isLocalization_basicOpen f
    have : IsLocalization.Away (algebraMap Γ(X, W') (F.obj (op W')) f)
        (F.obj (op (X.basicOpen f))) := isLocalizationAway F α hα hW' f
    have hres := res_mem_gen_of_mem F α hDV hfD T hbD
    rw [gen_eq_adjoin] at hres
    have hb'' : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' ∈
        Algebra.adjoin Γ(X, X.basicOpen f)
          (algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T') := by
      have e1 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) b' =
          (F.map (homOfLE hfD).op).hom ((F.map (homOfLE hDW).op).hom b) :=
        (comp hW (X.basicOpen_le f) b).trans (comp hDW hfD b).symm
      have e2 : algebraMap (F.obj (op W')) (F.obj (op (X.basicOpen f))) '' T' =
          (F.map (homOfLE (hfD.trans hDV)).op).hom '' T := by
        simp only [T', Set.image_image]
        exact Set.image_congr (fun y _ => comp hV (X.basicOpen_le f) y)
      rw [e1, e2]
      exact hres
    obtain ⟨m, hm⟩ := adjoin_mem_of_away f T' b' hb''
    exact ⟨m, (hI _).mpr (by rw [map_pow]; exact hm)⟩
  have cover : W' ≤ ⨆ f : (I.radical : Set Γ(X, W')), X.basicOpen f.1 := by
    intro x hx
    rw [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨D, hD, hxD, hDW, hDV, hbD⟩ := H x (by exact ⟨hW hx, hV hx⟩)
    obtain ⟨f, hfD, hxf⟩ := hW'.exists_basicOpen_le (V := D) ⟨x, hxD⟩ hx
    exact ⟨⟨f, key D f hfD hDW hDV hbD⟩, hxf⟩
  have htop : I = ⊤ := by
    rw [← Ideal.radical_eq_top, ← Ideal.span_eq I.radical]
    exact (hW'.self_le_iSup_basicOpen_iff).mp cover
  have h1 : (1 : Γ(X, W')) ∈ I := htop ▸ Submodule.mem_top
  rw [hI, map_one, one_mul] at h1
  rw [gen_eq_adjoin]
  exact h1

end GlobalTheory.QcSub.Local
