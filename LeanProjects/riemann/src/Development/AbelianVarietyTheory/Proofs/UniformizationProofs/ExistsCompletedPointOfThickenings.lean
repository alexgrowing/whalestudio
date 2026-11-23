import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AgreeOfCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsUniqueIsPointOfDualNumber

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompletedPoint

theorem adicLevelMap_surjective {B : Type} [CommRing B] (J : Ideal B) (n : ℕ) :
    Function.Surjective (adicLevelMap J (Nat.succ_le_succ (Nat.zero_le n))) := by
  intro p
  have : Set.range (PrimeSpectrum.comap (Ideal.Quotient.factorPow J (Nat.succ_le_succ (Nat.zero_le n)))) = _ :=
    range_comap_of_surjective _ _ (Ideal.Quotient.factor_surjective _)
  refine this.ge ?_
  refine (PrimeSpectrum.mem_zeroLocus _ _).2 fun a ha => ?_
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective a
  have hb : b ∈ J := by
    have h : Ideal.Quotient.mk (J ^ (0 + 1)) b = 0 := ha
    rwa [Ideal.Quotient.eq_zero_iff_mem, zero_add, pow_one] at h
  refine p.isPrime.mem_of_pow_mem (n + 1) ?_
  rw [← map_pow, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.pow_mem_pow hb _)]
  exact zero_mem _

theorem hom_ext_spec {B : Type} [CommRing B] (J : Ideal B) [IsHausdorff J B] {S : CommRingCat.{0}}
    {g g' : Spec (CommRingCat.of B) ⟶ Spec S}
    (h : ∀ n, adicLevelι J (n + 1) ≫ g = adicLevelι J (n + 1) ≫ g') : g = g' := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  obtain ⟨φ', rfl⟩ := Spec.map_surjective g'
  congr 1
  ext1
  apply DFunLike.coe_injective
  apply IsHausdorff.StrictMono.funext' J (a := fun n => n + 1) (strictMono_id.add_const 1)
  intro n a
  have h1 := h n
  rw [← Spec.map_comp, ← Spec.map_comp] at h1
  exact congr($(Spec.map_injective h1).hom a)

theorem exists_of_isAdicFamily {B : Type} [CommRing B] (J : Ideal B) [IsAdicComplete J B] {X : Scheme.{0}}
    {V : X.Opens} (hV : IsAffineOpen V) {f : ∀ n : ℕ, Spec (CommRingCat.of (B ⧸ J ^ (n + 1))) ⟶ X}
    (hf : IsAdicFamily J f) (h₀ : ∀ p, f 0 p ∈ V) :
    ∃ g : Spec (CommRingCat.of B) ⟶ X, (∀ p, g p ∈ V) ∧ ∀ n, adicLevelι J (n + 1) ≫ g = f n := by
  have hr : ∀ n, Set.range (f n) ⊆ Set.range hV.fromSpec := fun n => by
    rintro _ ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := adicLevelMap_surjective J n p
    rw [hV.range_fromSpec, ← Scheme.Hom.comp_apply, hf.of_le (Nat.zero_le n)]
    exact h₀ q
  have hφ : ∀ n, ∃ φ : Γ(X, V) ⟶ CommRingCat.of (B ⧸ J ^ (n + 1)), Spec.map φ ≫ hV.fromSpec = f n := fun n => by
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (IsOpenImmersion.lift hV.fromSpec (f n) (hr n))
    exact ⟨φ, by rw [hφ, IsOpenImmersion.lift_fac]⟩
  choose φ hφ using hφ
  have ha : StrictMono fun n : ℕ => n + 1 := strictMono_id.add_const 1
  have hc : ∀ {m : ℕ}, (Ideal.Quotient.factorPow J (ha.monotone m.le_succ)).comp
      (φ (m + 1)).hom = (φ m).hom := by
    intro m
    have h1 : adicLevelMap J (Nat.le_succ (m + 1)) ≫ Spec.map (φ (m + 1)) = Spec.map (φ m) := by
      rw [← cancel_mono hV.fromSpec, Category.assoc, hφ, hφ, hf m]
    rw [← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom)
  refine ⟨Spec.map (CommRingCat.ofHom
    (IsAdicComplete.StrictMono.liftRingHom J ha (fun n => (φ n).hom) hc)) ≫ hV.fromSpec, fun p => ?_,
    fun n => ?_⟩
  · exact hV.range_fromSpec.le ⟨_, rfl⟩
  · rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp,
      IsAdicComplete.StrictMono.mk_comp_liftRingHom J ha (fun n => (φ n).hom) hc (n := n)]
    exact hφ n

theorem exists_completion {A : Type} [CommRing A] [IsNoetherianRing A] (J : Ideal A) :
    ∃ (B : Type) (_ : CommRing B) (ψ : A →+* B), IsAdicComplete (J.map ψ) B ∧ ψ.Flat ∧
      ∀ p : PrimeSpectrum A, J ≤ p.asIdeal → p ∈ Set.range (PrimeSpectrum.comap ψ) := by
  refine ⟨AdicCompletion J A, inferInstance, algebraMap _ _, ?_, ?_, fun p hp => ?_⟩
  · rw [IsAdicComplete.map_algebraMap_iff]
    exact AdicCompletion.isAdicComplete J.fg_of_isNoetherianRing
  · exact RingHom.flat_algebraMap_iff.2 inferInstance
  · have h : p ∈ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk (J ^ 1))) := by
      rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective, PrimeSpectrum.mem_zeroLocus,
        Ideal.mk_ker, pow_one]
      exact hp
    obtain ⟨q, rfl⟩ := h
    refine ⟨PrimeSpectrum.comap (AdicCompletion.evalₐ J 1).toRingHom q, ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply]
    congr 2

open GlobalTheory.FormalPoint in

theorem exists_completed_point {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (G G' : Over (Spec (CommRingCat.of R))) [Flat G'.hom] [LocallyOfFiniteType G'.hom]
    (j : ∀ e : ℕ, thickObj R I e G' ⟶ thickObj R I e G)
    (hj : ∀ e, thickMap R I e G' ≫ (j (e + 1)).left = (j e).left ≫ thickMap R I e G)
    (x : (thickObj R I 0 G').left) (W : G.left.Opens) (W' : G'.left.Opens)
    (hW : (fstG I 0 G).left ((j 0).left x) ∈ W) (hW' : (fstG I 0 G').left x ∈ W') :
    ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left)
      (g : Spec (CommRingCat.of B) ⟶ G.left), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧
      Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧
      g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧
      g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ W' ∧ ⊤ ≤ g ⁻¹ᵁ W ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left),
        r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).left ≫ (fstG I e G).left = ρ ≫ g := by
  have tf : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      thickMap R I e H ≫ (fstG I (e + 1) H).left = (fstG I e H).left := fun e H =>
    (pullback.lift_fst _ _ _).trans (Category.comp_id _)
  have fh : ∀ (e : ℕ) (H : Over (Spec (CommRingCat.of R))),
      (fstG I e H).left ≫ H.hom = (thickObj R I e H).hom ≫ thick R I e := fun e H => pullback.condition
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := G.left.isBasis_affineOpens.exists_subset_of_mem_open hW W.isOpen
  have hci : IsClosedImmersion (thick R I 0) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have hci' : IsClosedImmersion (fstG I 0 G').left :=
    inferInstanceAs (IsClosedImmersion (pullback.fst G'.hom (thick R I 0)))
  obtain ⟨O, hO, hO'⟩ := (fstG I 0 G').left.isClosedEmbedding.isInducing.isOpen_iff.1
    (((j 0).left ≫ (fstG I 0 G).left) ⁻¹ᵁ V).isOpen
  have hxO : (fstG I 0 G').left x ∈ O := hO'.ge hxV
  obtain ⟨_, ⟨V', hV', rfl⟩, hxV', hVO⟩ := G'.left.isBasis_affineOpens.exists_subset_of_mem_open
    (show (fstG I 0 G').left x ∈ O ∩ W' from ⟨hxO, hW'⟩) (hO.inter W'.isOpen)
  replace hV' : IsAffineOpen V' := hV'
  have hln : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  have hN : IsNoetherianRing Γ(G'.left, V') := IsLocallyNoetherian.component_noetherian ⟨V', hV'⟩
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (hV'.fromSpec ≫ G'.hom)
  have hφf : φ.hom.Flat := by
    have : Flat (Spec.map φ) := by rw [hφ]; exact Flat.comp _ _
    exact Flat.SpecMap_iff.1 this
  obtain ⟨B, _, ψ, hB, hψ, hs⟩ := exists_completion (I.map φ.hom)
  letI : Algebra R B := (ψ.comp φ.hom).toAlgebra
  have hBc : IsAdicComplete (I.map (algebraMap R B)) B := by
    rw [Ideal.map_map] at hB; exact hB
  let g' : Spec (CommRingCat.of B) ⟶ G'.left := Spec.map (CommRingCat.ofHom ψ) ≫ hV'.fromSpec
  have hg' : g' ≫ G'.hom = spMap (algebraMap R B) := by
    rw [Category.assoc, ← hφ, ← Spec.map_comp]; rfl
  have hg'V : ∀ p, g' p ∈ V' := fun p => hV'.range_fromSpec.le ⟨_, rfl⟩
  let y : Over.mk (spMap (algebraMap R B)) ⟶ G' := Over.homMk g' hg'
  have hy : ∀ e, reduction I y e ≫ (fstG I e G').left = adicLevelι (I.map (algebraMap R B)) (e + 1) ≫ g' :=
    fun e => reduction_fstG I y e
  have hf : IsAdicFamily (I.map (algebraMap R B)) fun e => reduction I y e ≫ (j e).left ≫ (fstG I e G).left := by
    intro e
    have h₁ : adicLevelMap (I.map (algebraMap R B)) (Nat.le_succ (e + 1)) ≫ reduction I y (e + 1) =
        reduction I y e ≫ thickMap R I e G' := by
      rw [← cancel_mono (fstG I (e + 1) G').left, Category.assoc, Category.assoc, hy, tf, hy, adicLevelMap_ι_assoc]
    show _ ≫ _ ≫ _ = _
    rw [reassoc_of% h₁, reassoc_of% (hj e), tf]
  obtain ⟨g, hgV, hg⟩ := exists_of_isAdicFamily _ hV hf fun p => by
    have h₁ : (fstG I 0 G').left (reduction I y 0 p) ∈ O := by
      have : (reduction I y 0 ≫ (fstG I 0 G').left) p ∈ V' := by rw [hy]; exact hg'V _
      exact (hVO this).1
    exact hO'.le h₁
  refine ⟨B, inferInstance, inferInstance, g', g, hBc, RingHom.Flat.comp hφf hψ, ?_, ?_, hg', ?_, fun p _ => (hVO (hg'V p)).2,
    fun p _ => hVW (hgV p), fun e Z ρ r h => ?_⟩
  · have : Flat (Spec.map (CommRingCat.ofHom ψ)) := Flat.SpecMap_iff.2 hψ
    exact Flat.comp _ _
  · obtain ⟨p, hp⟩ := hV'.range_fromSpec.ge hxV'
    obtain ⟨q, hq⟩ := hs p (by
      rw [Ideal.map_le_iff_le_comap]
      have h₁ : Spec.map φ p = thick R I 0 ((thickObj R I 0 G').hom x) := by
        rw [hφ, Scheme.Hom.comp_apply, hp, ← Scheme.Hom.comp_apply, fh]; rfl
      have h₂ : p.asIdeal.comap φ.hom = _ := congrArg PrimeSpectrum.asIdeal h₁
      rw [h₂]
      intro a ha
      show Ideal.Quotient.mk (I ^ (0 + 1)) a ∈ PrimeSpectrum.asIdeal _
      rw [Ideal.Quotient.eq_zero_iff_mem.2 (by rwa [zero_add, pow_one])]
      exact zero_mem _)
    exact ⟨q, (congrArg hV'.fromSpec hq).trans hp⟩
  · refine hom_ext_spec (I.map (algebraMap R B)) fun e => ?_
    rw [reassoc_of% (hg e), fh, ← Category.assoc (j e).left, Over.w, ← Category.assoc, reduction_hom,
      levelMap_thick]
  · have w : ρ ≫ spMap (algebraMap R B) = (r ≫ (thickObj R I e G').hom) ≫ thick R I e := by
      rw [← hg', ← Category.assoc, ← h, Category.assoc, fh, Category.assoc]
    obtain ⟨l, rfl⟩ := exists_factor_level I (algebraMap R B) ρ _ w
    obtain rfl : r = l ≫ reduction I y e := by
      rw [← cancel_mono (fstG I e G').left, Category.assoc, hy]
      exact h.trans (Category.assoc _ _ _)
    rw [Category.assoc, Category.assoc, hg]

end GlobalTheory.CompletedPoint

theorem GlobalTheory.exists_completed_point_of_thickenings : ∀ (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (I : Ideal R), AdmBase R I → I = IsLocalRing.maximalIdeal R → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ (U : Unif I D A G) (U' : Unif I D' A' G') (hD : IsPullDeg (RingHom.id R) D.toPre D'.toPre) (j : ∀ e : ℕ, thickObj R I e G' ≅ thickObj R I e G), (∀ e : ℕ, IsMonHom (j e).hom ∧ thickMap R I e G' ≫ (j (e + 1)).hom.left = (j e).hom.left ≫ thickMap R I e G ∧ (U'.gt e).pG.left ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ (hD.e.hom.left ≫ pullback.fst D.toPre.P.A.hom (specOf (RingHom.id R))) = (j e).hom.left ≫ D.toPre.Oφ (U.gt e).pG (hD.xe x) κ) ∧ PMaps hD.w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (hD.xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (hD.xe x)) (j e).hom.left) → ∀ x : (thickObj R I 0 G').left, ∃ (B : Type) (_ : CommRing B) (_ : Algebra R B) (g' : Spec (CommRingCat.of B) ⟶ G'.left) (g : Spec (CommRingCat.of B) ⟶ G.left) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), IsAdicComplete (I.map (algebraMap R B)) B ∧ Module.Flat R B ∧ Flat g' ∧ (fstG I 0 G').left x ∈ Set.range g' ∧ g' ≫ G'.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ g ≫ G.hom = Spec.map (CommRingCat.ofHom (algebraMap R B)) ∧ ⊤ ≤ g' ⁻¹ᵁ U'.LG.L.U jL' ∧ ⊤ ≤ g ⁻¹ᵁ U.LG.L.U jL ∧ ∀ (e : ℕ) (Z : Scheme.{0}) (ρ : Z ⟶ Spec (CommRingCat.of B)) (r : Z ⟶ (thickObj R I e G').left), r ≫ (fstG I e G').left = ρ ≫ g' → r ≫ (j e).hom.left ≫ (fstG I e G).left = ρ ≫ g := by
  intro R _ _ _ I _ _ D D' A A' G G' _ _ _ _ _ hG' U U' hD j hj x
  have := hG'.smooth
  obtain ⟨jL, h⟩ : ∃ i, (fstG I 0 G).left ((j 0).hom.left x) ∈ U.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U.LG.isLB.cover.ge trivial)
  obtain ⟨jL', h'⟩ : ∃ i, (fstG I 0 G').left x ∈ U'.LG.L.U i :=
    TopologicalSpace.Opens.mem_iSup.1 (U'.LG.isLB.cover.ge trivial)
  obtain ⟨B, _, _, g', g, H⟩ := GlobalTheory.CompletedPoint.exists_completed_point I G G' (fun e => (j e).hom)
    (fun e => (hj e).2.1) x _ _ h h'
  exact ⟨B, _, _, g', g, jL, jL', H⟩
