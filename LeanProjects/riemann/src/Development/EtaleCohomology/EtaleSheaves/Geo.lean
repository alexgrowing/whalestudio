import Development.EtaleCohomology.EtaleSheaves.PowQEqOne

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.LeafTw0LocGenPfB
open LateralTheory.E.LeafTw0LocGenPfA

theorem geo {q : ℕ} [NeZero q] (V : Scheme.{0}) (ζ ξ : Prim q Γ(V, ⊤)) :
    Loc V fun W h => ∃ a : (ZMod q)ˣ, h.appTop ξ.1 = (h.appTop ζ.1) ^ (a : ZMod q).val := by
  classical
  have key : ∀ x : V, ∃ (Wx : V.Opens) (_ : x ∈ Wx) (a : (ZMod q)ˣ),
      V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op ξ.1 =
        V.presheaf.map (homOfLE le_top : Wx ⟶ ⊤).op (ζ.1 ^ (a : ZMod q).val) := by
    intro x
    have hq : IsUnit ((q : V.presheaf.stalk x)) := by
      simpa using ζ.2.1.map (V.presheaf.germ ⊤ x trivial).hom
    have hr : ∀ z : Γ(V, ⊤), Polynomial.aeval z (Polynomial.cyclotomic q ℤ) = 0 →
        Polynomial.aeval ((V.presheaf.germ ⊤ x trivial).hom z) (Polynomial.cyclotomic q ℤ) = 0 := by
      intro z hz
      have h := Polynomial.aeval_algHom_apply (V.presheaf.germ ⊤ x trivial).hom.toIntAlgHom z (Polynomial.cyclotomic q ℤ)
      rw [hz, map_zero] at h
      exact h
    obtain ⟨a, ha⟩ := local_pow hq (hr _ ζ.2.2) (hr _ ξ.2.2)
    have h2 : (V.presheaf.germ ⊤ x trivial).hom ξ.1 = (V.presheaf.germ ⊤ x trivial).hom (ζ.1 ^ (a : ZMod q).val) := by
      rw [map_pow]; exact ha
    obtain ⟨Wx, hx, i1, i2, he⟩ := TopCat.Presheaf.germ_eq V.presheaf (U := ⊤) (V := ⊤) x trivial trivial _ _ h2
    refine ⟨Wx, hx, a, ?_⟩
    have e1 : i1 = homOfLE le_top := Subsingleton.elim _ _
    have e2 : i2 = homOfLE le_top := Subsingleton.elim _ _
    subst e1 e2
    exact he
  choose Wx hx a ha using key
  have fin : ∀ (x : V) {W : Scheme.{0}} (g' : W ⟶ (Wx x).toScheme),
      (g' ≫ (Wx x).ι).appTop ξ.1 = ((g' ≫ (Wx x).ι).appTop ζ.1) ^ (a x : ZMod q).val := by
    intro x W g'
    have hle : (Wx x).ι ''ᵁ ⊤ ≤ Wx x := by simp
    have hW : ∀ z : Γ(V, ⊤), (Wx x).ι.appTop z =
        V.presheaf.map (homOfLE hle).op (V.presheaf.map (homOfLE le_top : Wx x ⟶ ⊤).op z) := by
      intro z
      rw [Scheme.Opens.ι_appTop, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
    rw [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hW, hW, ha x]
    simp only [map_pow]
    exact map_pow (ConcreteCategory.hom (Scheme.Hom.appTop g')) _ _
  let 𝒰 : V.Cover (Scheme.precoverage @Etale) :=
    Scheme.Cover.mkOfCovers V (fun x => (Wx x).toScheme) (fun x => (Wx x).ι) (fun x => ⟨x, ⟨x, hx x⟩, rfl⟩)
  refine ⟨_, Scheme.Cover.mem_grothendieckTopology 𝒰, fun W h hh => ?_⟩
  obtain ⟨x, g, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hh
  exact ⟨a x, fin x g⟩

end LateralTheory.E.LeafTw0LocGenPfB
