import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CoordNoeth

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (U : X.Opens) (h : genPt ξ ∈ U) : Γ(X, U) →+* Ω :=
  (X.presheaf.germ U (genPt ξ) h ≫ Scheme.stalkClosedPointTo ξ).hom

lemma genMap_germ (ξ : Spec (CommRingCat.of Ω) ⟶ X) (q : Cpt ξ) (U : X.Opens) (hq : q.1 ∈ U)
    (h : genPt ξ ∈ U) (s : Γ(X, U)) :
    genMap ξ q (X.presheaf.germ U q.1 hq s) = secVal ξ U h s := by
  have e : X.presheaf.germ U q.1 hq ≫ X.presheaf.stalkSpecializes q.2 = X.presheaf.germ U (genPt ξ) h :=
    TopCat.Presheaf.germ_stalkSpecializes _ _ _
  simp only [genMap, secVal, ← e]
  rfl

lemma secVal_res (ξ : Spec (CommRingCat.of Ω) ⟶ X) {U V : X.Opens} (i : V ⟶ U) (h : genPt ξ ∈ V)
    (s : Γ(X, U)) : secVal ξ V h (X.presheaf.map i.op s) = secVal ξ U (leOfHom i h) s := by
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ_res_apply i (genPt ξ) h s)

lemma secVal_injective {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) : Function.Injective (secVal ξ U h) := by
  intro s t e
  refine TopCat.Presheaf.section_ext X.sheaf U s t fun q hq => ?_
  apply hg.inj ⟨q, hU q hq⟩
  exact (genMap_germ ξ ⟨q, hU q hq⟩ U hq h s).trans (e.trans (genMap_germ ξ ⟨q, hU q hq⟩ U hq h t).symm)

lemma exists_secVal_eq {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (U : X.Opens)
    (h : genPt ξ ∈ U) (hU : ∀ q : X, q ∈ U → genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ q : Cpt ξ, q.1 ∈ U → a ∈ regAt ξ q) : ∃ s, secVal ξ U h s = a := by
  have key : ∀ q : U, ∃ (W : X.Opens) (_ : q.1 ∈ W) (_ : W ⟶ U) (hW : genPt ξ ∈ W) (s : Γ(X, W)),
      secVal ξ W hW s = a := by
    intro q
    obtain ⟨t, ht⟩ := ha ⟨q.1, hU _ q.2⟩ q.2
    obtain ⟨V, hqV, s, rfl⟩ := X.presheaf.germ_exist t
    have hqW : q.1 ∈ V ⊓ U := ⟨hqV, q.2⟩
    have hW : genPt ξ ∈ V ⊓ U := (hU _ q.2).mem_open (V ⊓ U).isOpen hqW
    refine ⟨V ⊓ U, hqW, homOfLE inf_le_right, hW, X.presheaf.map (homOfLE inf_le_left).op s, ?_⟩
    rw [secVal_res, ← genMap_germ ξ ⟨q.1, hU _ q.2⟩ V hqV]
    exact ht
  choose W hq i hW s hs using key
  have comp : TopCat.Presheaf.IsCompatible X.sheaf.1 W s := by
    intro p q
    apply secVal_injective hg (W p ⊓ W q) ⟨hW p, hW q⟩ (fun r hr => hU r (leOfHom (i p) hr.1))
    refine (secVal_res ξ _ _ _).trans (Eq.trans ?_ (secVal_res ξ _ _ _).symm)
    rw [hs, hs]
  obtain ⟨t, ht, -⟩ := X.sheaf.existsUnique_gluing' W U i
    (fun r hr => TopologicalSpace.Opens.mem_iSup.2 ⟨⟨r, hr⟩, hq _⟩) s comp
  refine ⟨t, ?_⟩
  rw [← hs ⟨_, h⟩, ← ht ⟨_, h⟩]
  exact (secVal_res ξ _ _ _).symm

lemma mem_regAt_self {ξ : Spec (CommRingCat.of Ω) ⟶ X} (hg : IsCptGen ξ) (a : Ω) :
    a ∈ regAt ξ ⟨genPt ξ, specializes_rfl⟩ := by
  obtain ⟨t, ht⟩ := hg.bij.2 a
  refine ⟨t, ?_⟩
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl, Category.id_comp]
  exact ht

lemma isNoetherianRing_chart {ξ : Spec (CommRingCat.of Ω) ⟶ X} {o : Type} [CommRing o]
    [IsNoetherianRing o] [Algebra o Ω] {κ : Type} [Finite κ] {x : κ → Ω} (tie : CoordTie o ξ x)
    (c : κ) (hc : x c ≠ 0) (U : X.Opens) (hU : ∀ q : X, q ∈ U ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c ⟨q, h⟩)
    (h : genPt ξ ∈ U) : IsNoetherianRing Γ(X, U) := by
  have hsp : ∀ q : X, q ∈ U → genPt ξ ⤳ q := fun q hq => ((hU q).1 hq).elim fun h _ => h
  have hA : IsNoetherianRing (Algebra.adjoin o (Set.range fun j => x j / x c)) := by
    have : Algebra.FiniteType o (Algebra.adjoin o (Set.range fun j => x j / x c)) :=
      (Subalgebra.fg_iff_finiteType _).1 ⟨(Set.finite_range fun j => x j / x c).toFinset, by simp⟩
    exact Algebra.FiniteType.isNoetherianRing o _
  have mem : ∀ a, a ∈ Algebra.adjoin o (Set.range fun j => x j / x c) ↔ ∃ s, secVal ξ U h s = a := by
    intro a
    rw [tie.ring c hc a]
    constructor
    · intro H
      refine exists_secVal_eq tie.gen U h hsp a fun q hq => ?_
      obtain ⟨_, hc'⟩ := (hU q.1).1 hq
      exact H q hc'
    · rintro ⟨s, rfl⟩ p hp
      have hpU : p.1 ∈ U := (hU p.1).2 ⟨p.2, hp⟩
      exact ⟨_, genMap_germ ξ p U hpU h s⟩
  let g : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) :=
    (secVal ξ U h).codRestrict _ fun s => (mem _).2 ⟨s, rfl⟩
  have hb : Function.Bijective g := by
    constructor
    · intro s t e
      exact secVal_injective tie.gen U h hsp (congrArg Subtype.val e)
    · rintro ⟨a, ha⟩
      obtain ⟨s, rfl⟩ := (mem a).1 ha
      exact ⟨s, rfl⟩
  exact isNoetherianRing_of_ringEquiv _ (RingEquiv.ofBijective g hb).symm

theorem noetherian_of_coordTie (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X)
    (o : Type) [CommRing o] [IsNoetherianRing o] [Algebra o Ω] (κ : Type) [Finite κ] (x : κ → Ω)
    (tie : CoordTie o ξ x) :
    (∀ p : Cpt ξ, IsNoetherianRing (regAt ξ p)) ∧ ((∀ q : X, genPt ξ ⤳ q) → IsNoetherian X ∧ IsIntegral X) := by
  refine ⟨fun p => ?_, fun hall => ?_⟩
  · obtain ⟨c, hcp⟩ := tie.cover p
    obtain ⟨U, hUa, hU⟩ := tie.affine c hcp.1
    have hp : p.1 ∈ U := (hU p.1).2 ⟨p.2, hcp⟩
    have h : genPt ξ ∈ U := p.2.mem_open U.isOpen hp
    haveI := isNoetherianRing_chart tie c hcp.1 U hU h
    letI := X.presheaf.algebra_section_stalk (⟨p.1, hp⟩ : U)
    haveI := hUa.isLocalization_stalk ⟨p.1, hp⟩
    haveI : IsNoetherianRing (X.presheaf.stalk p.1) :=
      IsLocalization.isNoetherianRing (hUa.primeIdealOf ⟨p.1, hp⟩).asIdeal.primeCompl _ ‹_›
    exact isNoetherianRing_of_surjective _ _ (genMap ξ p).rangeRestrict
      (genMap ξ p).rangeRestrict_surjective
  · have ex : ∀ c : {c // x c ≠ 0}, ∃ U : X.affineOpens,
        ∀ q : X, q ∈ (U : X.Opens) ↔ ∃ h : genPt ξ ⤳ q, InChart ξ x c.1 ⟨q, h⟩ := fun c => by
      obtain ⟨U, hUa, hU⟩ := tie.affine c.1 c.2
      exact ⟨⟨U, hUa⟩, hU⟩
    choose S hS using ex
    have hcov : (⨆ c, (S c : X.Opens)) = ⊤ := by
      refine eq_top_iff.2 fun q _ => ?_
      obtain ⟨c, hc⟩ := tie.cover ⟨q, hall q⟩
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨c, hc.1⟩, (hS _ q).2 ⟨hall q, hc⟩⟩
    have hgen : ∀ c, genPt ξ ∈ (S c : X.Opens) := fun c =>
      (hS c _).2 ⟨specializes_rfl, c.2, fun _ => mem_regAt_self tie.gen _⟩
    haveI : IsLocallyNoetherian X := isLocallyNoetherian_of_affine_cover hcov fun c =>
      isNoetherianRing_chart tie c.1 c.2 _ (hS c) (hgen c)
    haveI : CompactSpace X := by
      refine ⟨?_⟩
      have e : (Set.univ : Set X) = ⋃ c, ((S c : X.Opens) : Set X) := by
        have := congrArg (fun V : X.Opens => (V : Set X)) hcov
        simpa using this.symm
      rw [e]
      exact isCompact_iUnion fun c => (S c).2.isCompact
    have hcl : closure {genPt ξ} = (Set.univ : Set X) :=
      Set.eq_univ_of_forall fun q => specializes_iff_mem_closure.1 (hall q)
    have hirr : IsIrreducible (Set.univ : Set X) := hcl ▸ isIrreducible_singleton.closure
    haveI : IrreducibleSpace X := (irreducibleSpace_def X).2 hirr
    haveI : ∀ q : X, _root_.IsReduced (X.presheaf.stalk q) := fun q =>
      isReduced_of_injective (genMap ξ ⟨q, hall q⟩) (tie.gen.inj _)
    haveI : AlgebraicGeometry.IsReduced X := isReduced_of_isReduced_stalk X
    exact ⟨{}, isIntegral_of_irreducibleSpace_of_isReduced X⟩

end GlobalTheory.CompanionTheory.Ar.CoordNoeth

end
