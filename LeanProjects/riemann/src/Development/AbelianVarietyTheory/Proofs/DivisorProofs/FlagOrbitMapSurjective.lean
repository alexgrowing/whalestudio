import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfValILeOne

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.FlagZ GlobalTheory.FlagPoly Formalism.DegreeFormula
open IsLocalRing

namespace GlobalTheory.FlagZ

variable {ι κ : Type} [Fintype ι] [Finite κ] {N : ℕ} (a : κ → ι) (l : κ → Fin (N + 1))

theorem exists_eq_flagPt_of_valuationRing (V K : Type) [CommRing V] [IsDomain V] [ValuationRing V] [Field K]
    [Algebra V K] [IsFractionRing V K] (s : Sp K ⟶ Sp (GLRing ι N)) (t : Sp V ⟶ Part a l)
    (w : s ≫ orbit a l = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ t) :
    ∃ k : ι → GL (Fin N) V, t = flagPt a l k := by
  obtain ⟨ψ, rfl⟩ := Spec.map_surjective s
  let g : ι → GL (Fin N) K := fun τ => GeneralLinearGroup.map ψ.hom (univGL ι N τ)
  have hg : Spec.map ψ ≫ orbit a l = flagPt a l g := by
    rw [← flagPt_univGL]
    exact spMap_flagPt a l ψ.hom _
  choose k b hb hkb using fun τ => GlobalTheory.ValIwasawa.iwasawa V K N (g τ)
  have e : flagPt a l g = Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ flagPt a l k := by
    have : g = (fun τ => GeneralLinearGroup.map (algebraMap V K) (k τ)) * b := funext hkb
    rw [this, flagPt_mul a l _ b fun c i j h₁ h₂ => hb (a c) (h₁.trans_le h₂)]
    exact (spMap_flagPt a l (algebraMap V K) k).symm
  refine ⟨k, ?_⟩
  have hu := GlobalTheory.ProjSpace.existsUnique_extend_of_isProjOver (V := V) (K := K) (isProjOver_str a l)
    (Int.castRingHom V) (flagPt a l g) (toZ_ext _ _)
  exact hu.unique ⟨toZ_ext _ _, w.symm.trans hg⟩ ⟨toZ_ext _ _, e.symm⟩

theorem mem_range_orbit_of_specializes (x' : Sp (GLRing ι N)) (y : Part a l) (h : orbit a l x' ⤳ y) :
    y ∈ Set.range (orbit a l) := by
  let φ : (Part a l).presheaf.stalk y ⟶ (Sp (GLRing ι N)).residueField x' :=
    (Part a l).presheaf.stalkSpecializes h ≫ (orbit a l).stalkMap x' ≫ (Sp (GLRing ι N)).residue x'
  obtain ⟨A, hA, hA_local⟩ := exists_factor_valuationRing φ.hom
  let χ : (Part a l).presheaf.stalk y ⟶ .of A := CommRingCat.ofHom (φ.hom.codRestrict _ hA)
  have w : (Sp (GLRing ι N)).fromSpecResidueField x' ≫ orbit a l =
      Spec.map (CommRingCat.ofHom (algebraMap A ((Sp (GLRing ι N)).residueField x'))) ≫
        Spec.map χ ≫ (Part a l).fromSpecStalk y := by
    rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk h]
    simp_rw [← Spec.map_comp_assoc]
    rfl
  obtain ⟨k, hk⟩ := exists_eq_flagPt_of_valuationRing a l A ((Sp (GLRing ι N)).residueField x') _ _ w
  refine ⟨spMap (evalGL k) (closedPoint A), ?_⟩
  have h₁ : Spec.map χ (closedPoint A) = closedPoint ((Part a l).presheaf.stalk y) :=
    comap_closedPoint (S := A) (φ.hom.codRestrict A.toSubring hA)
  have h₂ : (Spec.map χ ≫ (Part a l).fromSpecStalk y) (closedPoint A) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg ((Part a l).fromSpecStalk y) h₁).trans (Part a l).fromSpecStalk_closedPoint)
  rw [hk] at h₂
  exact (Scheme.Hom.comp_apply _ _ _).symm.trans h₂

theorem surjective_orbit : ∀ (ι κ : Type) [Fintype ι] [Finite κ] (N : ℕ) (a : κ → ι) (l : κ → Fin (N + 1)),
    Function.Surjective (orbit a l) := by
  intro ι κ _ _ N a l y
  have hd : DenseRange (orbit a l) := (orbit a l).denseRange
  have hη := (genericPoint_spec (Sp (GLRing ι N))).image (orbit a l).continuous
  rw [Set.image_univ, hd.closure_range] at hη
  exact mem_range_orbit_of_specializes a l _ y (hη.specializes (Set.mem_univ y))

end GlobalTheory.FlagZ
