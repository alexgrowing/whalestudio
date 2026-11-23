import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreservesFilteredColimitsModuleCatIffForgetIffElStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsuppMapDomainEqZeroAtFilteredStageStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CyclotomicPrimitiveRootsFilteredColimitStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.TwistFiltered

theorem ring_eq_later {J : Type} [SmallCategory J] [IsFiltered J] {D : J ⥤ CommRingCat.{0}} {c : Cocone D}
    (hc : IsColimit c) {j : J} {x y : D.obj j} (h : c.ι.app j x = c.ι.app j y) :
    ∃ (k : J) (f : j ⟶ k), D.map f x = D.map f y :=
  (Types.FilteredColimit.isColimit_eq_iff' (isColimitOfPreserves (forget CommRingCat.{0}) hc) x y).1 h

def primSys (q : ℕ) {J : Type} [SmallCategory J] (D : J ⥤ CommRingCat.{0}) : J ⥤ Type where
  obj j := Prim q (D.obj j)
  map f := TypeCat.ofHom (Prim.map (q := q) (D.map f).hom)
  map_id j := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]
  map_comp f g := by
    ext ζ
    apply Subtype.ext
    simp [Prim.map]

end GlobalTheory.EtC.TwistFiltered

namespace GlobalTheory.EtC.TwistFiltered

theorem prim_map_comp {q : ℕ} {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    Prim.map (q := q) g ∘ Prim.map f = Prim.map (g.comp f) := by
  funext ζ
  rfl

theorem twF_preservesFilteredColimits : ∀ (q : ℕ) (i : ℤ), PreservesFilteredColimitsOfSize.{0, 0} (twF q i) := by
  intro q i
  rw [(GlobalTheory.T.preservesFilteredColimits_moduleCat_iff_forget_iff_elements (ULift.{1} (ZMod q)) (twF q i)).2]
  intro J _ _ D c hc
  obtain ⟨hon, hinj⟩ := GlobalTheory.T.cyclotomicPrimitiveRoots_filtered_colimit q J D c hc
  have hw : ∀ {j k : J} (f : j ⟶ k) (y : (twF q i).obj (D.obj j)),
      ((twF q i).map (c.ι.app k)).hom (((twF q i).map (D.map f)).hom y) = ((twF q i).map (c.ι.app j)).hom y := by
    intro j k f y
    rw [← ModuleCat.comp_apply, ← Functor.map_comp, c.w]
  have hwP : ∀ {j k : J} (f : j ⟶ k), Prim.map (q := q) (c.ι.app k).hom ∘ Prim.map (D.map f).hom = Prim.map (c.ι.app j).hom := by
    intro j k f
    rw [prim_map_comp, ← CommRingCat.hom_comp, c.w]
  have hwP' : ∀ {j k : J} (f : j ⟶ k) (ζ : Prim q (D.obj j)), Prim.map (q := q) (c.ι.app k).hom (Prim.map (D.map f).hom ζ) = Prim.map (c.ι.app j).hom ζ :=
    fun f ζ => congrFun (hwP f) ζ
  refine ⟨?_, ?_⟩
  · intro x
    induction x using Submodule.Quotient.induction_on with
    | H f =>
    induction f using Finsupp.induction_linear with
    | zero =>
      obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
      exact ⟨j, 0, by rw [map_zero]; rfl⟩
    | add f g hf hg =>
      obtain ⟨j, y, hy⟩ := hf
      obtain ⟨j', y', hy'⟩ := hg
      refine ⟨IsFiltered.max j j', ((twF q i).map (D.map (IsFiltered.leftToMax j j'))).hom y + ((twF q i).map (D.map (IsFiltered.rightToMax j j'))).hom y', ?_⟩
      rw [map_add, hw, hw, hy, hy']
      rfl
    | single ζ a =>
      obtain ⟨j, ξ, hξ⟩ := hon ζ
      refine ⟨j, Submodule.Quotient.mk (Finsupp.single ξ a), ?_⟩
      change Submodule.Quotient.mk (Finsupp.mapDomain _ _) = _
      rw [Finsupp.mapDomain_single, hξ]
  · intro j y hy
    induction y using Submodule.Quotient.induction_on with
    | H x =>
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (c.ι.app j).hom) x) = 0 at hy
    rw [Submodule.Quotient.mk_eq_zero] at hy
    have hlift : ∀ r ∈ twRel q i c.pt, ∃ (k : J) (s : Prim q (D.obj k) →₀ ULift.{1} (ZMod q)),
        s ∈ twRel q i (D.obj k) ∧ Finsupp.mapDomain (Prim.map (c.ι.app k).hom) s = r := by
      intro r hr
      induction hr using Submodule.span_induction with
      | mem r hr =>
        obtain ⟨ζ, ξ, a, hrel, rfl⟩ := hr
        obtain ⟨j1, ζ1, hζ1⟩ := hon ζ
        obtain ⟨j2, ξ1, hξ1⟩ := hon ξ
        obtain ⟨ζm, hζm⟩ : ∃ ζm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ζm = ζ :=
          ⟨_, (hwP' (IsFiltered.leftToMax j1 j2) ζ1).trans hζ1⟩
        obtain ⟨ξm, hξm⟩ : ∃ ξm : Prim q (D.obj (IsFiltered.max j1 j2)), Prim.map (c.ι.app _).hom ξm = ξ :=
          ⟨_, (hwP' (IsFiltered.rightToMax j1 j2) ξ1).trans hξ1⟩
        have heq : c.ι.app (IsFiltered.max j1 j2) ξm.1 = c.ι.app (IsFiltered.max j1 j2) (ζm.1 ^ (a : ZMod q).val) := by
          rw [map_pow]
          have h1 := congrArg Subtype.val hζm
          have h2 := congrArg Subtype.val hξm
          simp only [Prim.map] at h1 h2
          rw [h1, h2, hrel]
        obtain ⟨n, g, hg⟩ := ring_eq_later hc heq
        refine ⟨n, Finsupp.single (Prim.map (D.map g).hom ξm) 1 - Finsupp.single (Prim.map (D.map g).hom ζm) (ULift.up ((a ^ i : (ZMod q)ˣ) : ZMod q)), Submodule.subset_span ⟨_, _, a, ?_, rfl⟩, ?_⟩
        · simp only [Prim.map]
          rw [hg, map_pow]
        · rw [Finsupp.mapDomain_sub, Finsupp.mapDomain_single, Finsupp.mapDomain_single, hwP' g ξm, hwP' g ζm, hζm, hξm]
      | zero =>
        obtain ⟨j⟩ := IsFiltered.nonempty (C := J)
        exact ⟨j, 0, zero_mem _, by simp⟩
      | add r r' _ _ hr hr' =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        obtain ⟨k', s', hs', rfl⟩ := hr'
        refine ⟨IsFiltered.max k k', Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax k k')).hom) s +
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax k k')).hom) s',
          add_mem (twRel_le q i _ hs) (twRel_le q i _ hs'), ?_⟩
        rw [Finsupp.mapDomain_add, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP]
      | smul a r _ hr =>
        obtain ⟨k, s, hs, rfl⟩ := hr
        exact ⟨k, a • s, Submodule.smul_mem _ a hs, by rw [Finsupp.mapDomain_smul]⟩
    obtain ⟨k, s, hs, hsr⟩ := hlift _ hy
    have hz : Finsupp.mapDomain (Prim.map (c.ι.app (IsFiltered.max j k)).hom)
        (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k)).hom) x -
          Finsupp.mapDomain (Prim.map (D.map (IsFiltered.rightToMax j k)).hom) s) = 0 := by
      rw [Finsupp.mapDomain_sub, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, hwP, hwP, hsr, sub_self]
    have key := GlobalTheory.T.finsupp_mapDomain_eq_zero_at_filtered_stage (ULift.{1} (ZMod q)) J (primSys q D) (Prim q c.pt) (fun j => Prim.map (c.ι.app j).hom)
      (fun j k f ζ => hwP' f ζ) hinj (IsFiltered.max j k) _ hz
    obtain ⟨n, h, hn⟩ := key
    refine ⟨n, IsFiltered.leftToMax j k ≫ h, ?_⟩
    change Submodule.Quotient.mk (Finsupp.mapDomain (Prim.map (D.map (IsFiltered.leftToMax j k ≫ h)).hom) x) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    change Finsupp.mapDomain (Prim.map (D.map h).hom) _ = 0 at hn
    rw [Finsupp.mapDomain_sub, sub_eq_zero, ← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp, prim_map_comp, prim_map_comp] at hn
    rw [Functor.map_comp, CommRingCat.hom_comp, hn]
    have := twRel_le q i (D.map (IsFiltered.rightToMax j k ≫ h)).hom hs
    rwa [Functor.map_comp, CommRingCat.hom_comp] at this

end GlobalTheory.EtC.TwistFiltered
