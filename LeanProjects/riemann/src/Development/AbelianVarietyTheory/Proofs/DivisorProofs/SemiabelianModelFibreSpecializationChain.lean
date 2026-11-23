import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsActIffIsDiagEnd
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.ImmersedBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZHAbove
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FibrePreconnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsIsoMorphismRestrictOfIsHomIdStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.SpecChain

theorem eqvGen_specializes {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    [PreconnectedSpace X] (x y : X) : Relation.EqvGen (· ⤳ ·) x y := by
  classical
  let C : Set X := {y | Relation.EqvGen (· ⤳ ·) x y}
  have hsub : ∀ K ∈ irreducibleComponents X, (K ∩ C).Nonempty → K ⊆ C := by
    rintro K hK ⟨w, hwK, hwC⟩ v hv
    have hI : IsIrreducible K := hK.1
    have hcl : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
    have hg := hI.isGenericPoint_genericPoint hcl
    have h1 : hI.genericPoint ⤳ w := hg.specializes hwK
    have h2 : hI.genericPoint ⤳ v := hg.specializes hv
    exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.trans _ _ _ hwC (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ h1)))
      (Relation.EqvGen.rel _ _ h2)
  have hfin := TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (α := X)
  have hC : C = ⋃ K ∈ {K ∈ irreducibleComponents X | (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      exact ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v,
        ⟨v, mem_irreducibleComponent, hv⟩⟩, mem_irreducibleComponent⟩
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩
      exact hsub K hK hne hvK
  have hCc : Cᶜ = ⋃ K ∈ {K ∈ irreducibleComponents X | ¬ (K ∩ C).Nonempty}, K := by
    ext v
    simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop]
    constructor
    · intro hv
      refine ⟨irreducibleComponent v, ⟨irreducibleComponent_mem_irreducibleComponents v, ?_⟩, mem_irreducibleComponent⟩
      intro hne
      exact hv (hsub _ (irreducibleComponent_mem_irreducibleComponents v) hne mem_irreducibleComponent)
    · rintro ⟨K, ⟨hK, hne⟩, hvK⟩ hv
      exact hne ⟨v, hvK, hv⟩
  have hC1 : IsClosed C := by
    rw [hC]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hC2 : IsClosed Cᶜ := by
    rw [hCc]
    exact (hfin.subset (Set.sep_subset _ _)).isClosed_biUnion fun K hK => isClosed_of_mem_irreducibleComponents K hK.1
  have hclo : IsClopen C := ⟨hC1, isClosed_compl_iff.mp hC2⟩
  have hx : x ∈ C := Relation.EqvGen.refl x
  have := hclo.eq_univ ⟨x, hx⟩
  have hy : y ∈ C := this ▸ Set.mem_univ y
  exact hy

theorem quasiSober_of_generalization {X : Type*} [TopologicalSpace X] [QuasiSober X] (S : Set X)
    (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) : QuasiSober S := by
  constructor
  intro T hT hTc
  have hT' : IsIrreducible (((↑) : S → X) '' T) := hT.image _ continuous_subtype_val.continuousOn
  have hξ := hT'.isGenericPoint_genericPoint_closure
  obtain ⟨t, ht⟩ := hT.nonempty
  have hξt : hT'.genericPoint ⤳ (t : X) := hξ.specializes (subset_closure ⟨t, ht, rfl⟩)
  have hξS : hT'.genericPoint ∈ S :=
    hS _ t t.2 hξt (closure_mono (Subtype.coe_image_subset S T) hξ.mem)
  refine ⟨⟨hT'.genericPoint, hξS⟩, ?_⟩
  show closure {(⟨hT'.genericPoint, hξS⟩ : S)} = T
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, Set.image_singleton]
  change ((↑) : S → X) ⁻¹' closure {hT'.genericPoint} = T
  rw [hξ.def, ← Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image, hTc.closure_eq]

theorem eqvGen_of_isPreconnected {X : Type*} [TopologicalSpace X] [TopologicalSpace.NoetherianSpace X] [QuasiSober X]
    (S : Set X) (hc : IsPreconnected S) (hS : ∀ x s, s ∈ S → x ⤳ s → x ∈ closure S → x ∈ S) :
    ∀ a ∈ S, ∀ b ∈ S, Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) a b := by
  intro a ha b hb
  haveI := quasiSober_of_generalization S hS
  haveI : PreconnectedSpace S := Subtype.preconnectedSpace hc
  have h := eqvGen_specializes (⟨a, ha⟩ : S) ⟨b, hb⟩
  have key : ∀ u v : S, Relation.EqvGen (· ⤳ ·) u v →
      Relation.EqvGen (fun u v : X => u ∈ S ∧ v ∈ S ∧ u ⤳ v) u v := by
    intro u v huv
    induction huv with
    | rel p q hpq => exact Relation.EqvGen.rel _ _ ⟨p.2, q.2, hpq.map continuous_subtype_val⟩
    | refl p => exact Relation.EqvGen.refl _
    | symm p q _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans p q r _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  exact key _ _ h

end GlobalTheory.SpecChain

namespace GlobalTheory.SpecChain

theorem fibre_chain : ∀ (g n : ℕ) (F : SFam g n (zetaAway n)) (W : Matrix (Fin 8) (Fin 8) ℤ) (Z : Scheme.{0}) (i : F.X ⟶ Z) (X₁ : Setup F W i) (z₁ : X₁.M.Z) (Y : RatModel X₁.o₁ X₁.Ω₁) (πY : Y.Z ⟶ X₁.M.Z), Cmp.ZHAbove X₁ Y πY → ∀ y y' : Y.Z, πY y = z₁ → πY y' = z₁ → Relation.EqvGen (fun a b : Y.Z => πY a = z₁ ∧ πY b = z₁ ∧ a ⤳ b) y y' := by
  intro g n F W Z i X₁ z₁ Y πY hZH y y' hy hy'
  obtain ⟨U₀, EE, -, -, -, hHom, hProp⟩ := hZH
  obtain ⟨U, hU, hiso⟩ := GlobalTheory.T.exists_nonempty_isIso_morphismRestrict_of_isHom_id X₁.o₁ X₁.Ω₁ Y X₁.M πY hHom
  haveI : IsDedekindDomain X₁.o₁ := X₁.ar.ded
  haveI : IsLocallyNoetherian (Sp X₁.o₁) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of X₁.o₁)))
  haveI := X₁.M.lft
  haveI := Y.lft
  haveI := Y.qc
  haveI : IsLocallyNoetherian X₁.M.Z := LocallyOfFiniteType.isLocallyNoetherian X₁.M.s
  haveI : IsLocallyNoetherian Y.Z := LocallyOfFiniteType.isLocallyNoetherian Y.s
  haveI : CompactSpace Y.Z := by
    constructor
    have := QuasiCompact.isCompact_preimage (f := Y.s) (U := Set.univ) isOpen_univ isCompact_univ
    simpa using this
  haveI : IsNoetherian Y.Z := {}
  haveI : IsProper πY := hProp
  have hN : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X₁.M.Z := (GlobalTheory.isNormalScheme_iff_pred _).1 X₁.normal
  have hc := GlobalTheory.ZariskiConn.fibre_preconnected Y.Z X₁.M.Z πY hN U hU hiso z₁
  have hS : ∀ x s, s ∈ πY.base ⁻¹' {z₁} → x ⤳ s → x ∈ closure (πY.base ⁻¹' {z₁}) → x ∈ πY.base ⁻¹' {z₁} := by
    intro x s hs hxs hx
    have h1 : πY.base x ⤳ z₁ := by
      have := hxs.map πY.base.hom.continuous
      rwa [show πY.base s = z₁ from hs] at this
    have h2 : z₁ ⤳ πY.base x := by
      rw [specializes_iff_mem_closure]
      have hcont := πY.base.hom.continuous
      have : closure (πY.base ⁻¹' {z₁}) ⊆ πY.base ⁻¹' closure {z₁} :=
        closure_minimal (Set.preimage_mono subset_closure) (isClosed_closure.preimage hcont)
      exact this hx
    exact (h1.antisymm h2).eq
  exact eqvGen_of_isPreconnected _ hc hS y hy y' hy'

end GlobalTheory.SpecChain
