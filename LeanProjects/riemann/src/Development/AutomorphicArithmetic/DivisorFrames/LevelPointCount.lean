import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsAgree
import Development.AutomorphicArithmetic.LocalEmbeddings.ConsMatch
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CardLiesOverEqIndex
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsRingEquivComplexCompEq
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Cartier GlobalTheory.ConsGeo

private theorem card_of_fibres {A S : Type} [Finite S] (f : A → S) (n : ℕ) (hn : 0 < n)
    (h : ∀ s, Nat.card {a // f a = s} = n) : Nat.card A = n * Nat.card S := by
  classical
  have := Fintype.ofFinite S
  have : ∀ s, Finite {a // f a = s} := fun s => Nat.finite_of_card_ne_zero (by rw [h]; exact hn.ne')
  rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f), Nat.card_sigma]
  simp [h, mul_comm]

private theorem card_ext {F K : IntermediateField ℚ ℂ} [FiniteDimensional ℚ K] (θ : F →+* K) :
    Finite {s : K →+* ℂ // s.comp θ = F.val.toRingHom} ∧
      Nat.card {s : K →+* ℂ // s.comp θ = F.val.toRingHom} = embDeg θ := by
  letI := θ.toAlgebra
  haveI : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  haveI : FiniteDimensional F K := Module.Finite.of_restrictScalars_finite ℚ F K
  let e : {s : K →+* ℂ // s.comp θ = F.val.toRingHom} ≃ (K →ₐ[F] ℂ) :=
    { toFun := fun s => { s.1 with commutes' := fun x => RingHom.congr_fun s.2 x }
      invFun := fun s => ⟨s.toRingHom, RingHom.ext fun x => s.commutes x⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  refine ⟨Finite.of_equiv _ e.symm, ?_⟩
  rw [Nat.card_congr e, Nat.card_eq_fintype_card, AlgHom.card]
  rfl

private theorem spm_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  rw [← Spec.map_comp]; rfl

private theorem spm_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) :
    f = g := congrArg CommRingCat.Hom.hom (Spec.map_injective h)

private theorem spm_pre {A B : Type} [CommRing A] [CommRing B] (u : Sp B ⟶ Sp A) :
    spMap (Spec.preimage u).hom = u := Spec.map_preimage u

theorem UpperTheory.level_point_count :
    ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p} {O : Type} [CommRing O] {β : O →+* i₀.c.F} {Z : LocM.Mdl Y i₀} {T : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Model (Xo i₀.l) i₀.c β} (L : Lev Z T), 1 ≤ Dw.p + Dw.q → ∀ y : CxPt (Xo i₀.l) i₀.c, Nat.card {y₂ : Sp ℂ ⟶ (Xo Z.i.l).XF Z.i.c // y₂ ≫ L.r = y.1} = levDeg Z.dvd (Xo i₀.l) i₀.c (Xo Z.i.l) Z.i.c * embDeg (incl Z) := by
  intro E _ _ _ H Dw Xo p W Y i₀ O _ β Z T L hpq y
  haveI := Z.i.c.fin
  obtain ⟨hfin, hcard⟩ := card_ext (incl Z)
  obtain ⟨π, hπ, hpb, hr⟩ := L.fst
  have hs := L.snd
  obtain ⟨π₀, -, -, huniq, -⟩ :=
    (GlobalTheory.LevelCompare.levelMaps_iff hpq).1 (GlobalTheory.moduliScheme_levelMaps_heckePoints.2 E H Dw hpq).1 _ _ Z.dvd
      (Xo i₀.l) (Xo Z.i.l)
  let f : {y₂ : Sp ℂ ⟶ (Xo Z.i.l).XF Z.i.c // y₂ ≫ L.r = y.1} →
      {s : Z.i.c.F →+* ℂ // s.comp (incl Z) = i₀.c.F.val.toRingHom} := fun a =>
    ⟨(Spec.preimage (a.1 ≫ pullback.snd _ _)).hom, spm_inj (by
      rw [← spm_comp, spm_pre, Category.assoc, ← hs, ← Category.assoc, a.2]; exact y.2)⟩
  have hf : ∀ a s, f a = s ↔ a.1 ≫ pullback.snd _ _ = spMap s.1 := fun a s =>
    ⟨fun h => by rw [← h]; exact (spm_pre _).symm,
      fun h => Subtype.ext (spm_inj ((spm_pre _).trans h))⟩
  rw [← hcard]
  refine card_of_fibres f _ (levDeg_pos _ _ _ _ _) fun s => ?_
  haveI : Countable Z.i.c.F := Finsupp.Countable.of_moduleFinite (R := ℚ)
  obtain ⟨γ, hγ⟩ := GlobalTheory.CompRat.exists_ringEquiv_complex_comp_eq _ s.1 Z.i.c.F.val.toRingHom
  have hγ1 : γ.toRingHom.comp s.1 = Z.i.c.F.val.toRingHom := RingHom.ext hγ
  have hγ2 : γ.symm.toRingHom.comp Z.i.c.F.val.toRingHom = s.1 := RingHom.ext fun x => by
    rw [← hγ1]; simp
  have hγ3 : γ.toRingHom.comp i₀.c.F.val.toRingHom = i₀.c.F.val.toRingHom := by
    conv_lhs => rw [← s.2, ← RingHom.comp_assoc, hγ1]
    rfl
  have i1 : spMap γ.toRingHom ≫ spMap γ.symm.toRingHom = 𝟙 _ := by
    rw [spm_comp, ← GlobalTheory.LevelCompare.spMap_id]; congr 1; ext; simp
  have i2 : spMap γ.symm.toRingHom ≫ spMap γ.toRingHom = 𝟙 _ := by
    rw [spm_comp, ← GlobalTheory.LevelCompare.spMap_id]; congr 1; ext; simp
  let y' : CxPt (Xo i₀.l) i₀.c := ⟨spMap γ.toRingHom ≫ y.1, by
    rw [Category.assoc, y.2, spm_comp, hγ3]⟩
  rw [← card_liesOver hpq Z.dvd (Xo Z.i.l) Z.i.c y']
  refine Nat.card_congr
    { toFun := fun a => ⟨⟨spMap γ.toRingHom ≫ a.1.1, by
        rw [Category.assoc, (hf _ _).1 a.2, spm_comp, hγ1]⟩, π, hπ, hpb, by
        change (_ ≫ a.1.1) ≫ _ = (_ ≫ y.1) ≫ _
        rw [← hr, Category.assoc, Category.assoc, ← Category.assoc a.1.1, a.1.2]⟩
      invFun := fun b => ⟨⟨spMap γ.symm.toRingHom ≫ b.1.1, ?_⟩, (hf _ _).2 (by
        change (_ ≫ b.1.1) ≫ _ = _
        rw [Category.assoc, b.1.2, spm_comp, hγ2])⟩
      left_inv := fun a => Subtype.ext (Subtype.ext (by
        change _ ≫ _ ≫ a.1.1 = a.1.1
        rw [← Category.assoc, i2, Category.id_comp]))
      right_inv := fun b => Subtype.ext (Subtype.ext (by
        change _ ≫ _ ≫ b.1.1 = b.1.1
        rw [← Category.assoc, i1, Category.id_comp])) }
  obtain ⟨π', a₁, a₂, a₃⟩ := b.2
  obtain rfl : π' = π := (huniq π' a₁ a₂).trans (huniq π hπ hpb).symm
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, hr, a₃]
    change _ ≫ (_ ≫ y.1) ≫ _ = _
    rw [← Category.assoc, ← Category.assoc, i2, Category.id_comp]
  · rw [Category.assoc, Category.assoc, hs, ← Category.assoc b.1.1, b.1.2, ← Category.assoc, spm_comp, hγ2,
      spm_comp, s.2]
    exact y.2.symm
