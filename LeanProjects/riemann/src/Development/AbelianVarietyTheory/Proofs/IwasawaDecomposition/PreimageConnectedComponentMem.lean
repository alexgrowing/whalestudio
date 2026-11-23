import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivComp
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStalkFactor
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsSmulOfPreservesFrameOrbits
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfD
import Formalism.LocalToGlobal.ProjectiveLattices.CompSplitPfB

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsDedekindDomain Topology
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

namespace GlobalTheory.ShFam.PtComp

theorem disjoint_of_smooth {K : Type} [Field K] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of K)) (hsm : Smooth f)
    (Z Z' : Set X) (hZ : Z ∈ irreducibleComponents X) (hZ' : Z' ∈ irreducibleComponents X) (hne : Z ≠ Z') :
    Disjoint Z Z' := by
  refine CompSplitPfD.cspD_disj (fun x => ?_) Z Z' hZ hZ' hne
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hV' : IsAffineOpen V := hV
  have h1 := HasRingHomProperty.appLE (P := @Smooth) f hsm
    ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ (fun p _ => by simp)
  let ψ : K →+* Γ(X, V) :=
    (f.appLE ⊤ V (fun p _ => by simp)).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  have hψ : ψ.Smooth := RingHom.Smooth.comp
    (RingHom.Smooth.of_bijective (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.bijective) h1
  let _ : Algebra K Γ(X, V) := ψ.toAlgebra
  have : Algebra.Smooth K Γ(X, V) := hψ
  obtain ⟨r, hr, n, _, _, _⟩ := Algebra.IsSmoothAt.exists_isStandardEtale_mvPolynomial (R := K)
    (p := (hV'.primeIdealOf ⟨x, hxV⟩).asIdeal)
  refine ⟨PrimeSpectrum (Localization.Away r), inferInstance,
    hV'.fromSpec ∘ PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)), ?_, ?_, ?_⟩
  · exact (hV'.fromSpec.isOpenEmbedding).comp (PrimeSpectrum.localization_away_isOpenEmbedding _ r)
  · obtain ⟨z, hz⟩ : hV'.primeIdealOf ⟨x, hxV⟩ ∈
        Set.range (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away r) r]
      exact hr
    refine ⟨z, ?_⟩
    show hV'.fromSpec (PrimeSpectrum.comap (algebraMap Γ(X, V) (Localization.Away r)) z) = x
    rw [hz]
    exact hV'.fromSpec_primeIdealOf ⟨x, hxV⟩
  · intro a b y ha hb hay hby
    have : IsIntegrallyClosed (MvPolynomial (Fin n) K) := UniqueFactorizationMonoid.instIsIntegrallyClosed
    have hmin : ∀ a : PrimeSpectrum (Localization.Away r), (∀ a', a' ⤳ a → a' = a) →
        a.asIdeal ∈ minimalPrimes (Localization.Away r) := by
      intro a ha
      refine ⟨⟨a.isPrime, bot_le⟩, fun J hJ hJa => ?_⟩
      have := ha ⟨J, hJ.1⟩ ((PrimeSpectrum.le_iff_specializes _ _).1 hJa)
      exact (congrArg PrimeSpectrum.asIdeal this).ge
    exact PrimeSpectrum.ext (CompSplitPfC.cspC_minimal_unique (MvPolynomial (Fin n) K) (q := y.asIdeal)
      (hmin a ha) (hmin b hb) ((PrimeSpectrum.le_iff_specializes _ _).2 hay)
      ((PrimeSpectrum.le_iff_specializes _ _).2 hby))

theorem connectedComponent_mem {X : Type} [TopologicalSpace X] (hfin : (irreducibleComponents X).Finite)
    (hd : ∀ Z ∈ irreducibleComponents X, ∀ Z' ∈ irreducibleComponents X, Z ≠ Z' → Disjoint Z Z') (z : X) :
    connectedComponent z ∈ irreducibleComponents X ∧ IsOpen (connectedComponent z) := by
  have hV := irreducibleComponent_mem_irreducibleComponents z
  have hU : irreducibleComponent z = (⋃ W ∈ irreducibleComponents X \ {irreducibleComponent z}, W)ᶜ := by
    ext p
    simp only [Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · intro hp W hW hpW
      exact Set.disjoint_left.1 (hd _ hW.1 _ hV hW.2) hpW hp
    · intro hp
      by_contra hpZ
      exact hp _ ⟨irreducibleComponent_mem_irreducibleComponents p,
        fun h => hpZ ((show irreducibleComponent p = _ from h) ▸ mem_irreducibleComponent)⟩ mem_irreducibleComponent
  have ho : IsOpen (irreducibleComponent z) := by
    rw [hU]
    exact ((hfin.subset Set.diff_subset).isClosed_biUnion fun W hW =>
      isClosed_of_mem_irreducibleComponents _ hW.1).isOpen_compl
  have e : connectedComponent z = irreducibleComponent z :=
    ((IsClopen.connectedComponent_subset ⟨isClosed_irreducibleComponent, ho⟩ mem_irreducibleComponent)).antisymm
      irreducibleComponent_subset_connectedComponent
  rw [e]
  exact ⟨hV, ho⟩

theorem exists_point {K Ω : Type} [Field K] [Field Ω] [IsAlgClosed Ω] {X : Scheme.{0}} (π : X ⟶ Sp K)
    [LocallyOfFiniteType π] (x : Sp Ω ⟶ Sp K) {O : Set X} (hO : IsOpen O) (hne : O.Nonempty) :
    ∃ g : Sp Ω ⟶ X, g ≫ π = x ∧ ∀ a, g a ∈ O := by
  obtain ⟨p, hp⟩ := hne
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := π) (g := x) p (IsLocalRing.closedPoint Ω)
    (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  have := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨c, hcO, hc'⟩ := nonempty_inter_closedPoints (Z := pullback.fst π x ⁻¹' O)
    ⟨z, show pullback.fst π x z ∈ O from hz ▸ hp⟩ (hO.preimage (pullback.fst π x).continuous).isLocallyClosed
  have hc : IsClosed {c} := hc'
  refine ⟨pointOfClosedPoint (pullback.snd π x) c hc ≫ pullback.fst π x, ?_, fun a => ?_⟩
  · rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]
  · show pullback.fst π x (pointOfClosedPoint (pullback.snd π x) c hc a) ∈ O
    rw [pointOfClosedPoint_apply]
    exact hcO

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem preimage_connectedComponent_mem (Z : Model Xo c β) (hsm : Smooth (genStr Z)) (z : gen Z) :
    Z.jQ ⁻¹' connectedComponent z ∈ irreducibleComponents (Xo.XF c) := by
  have := isProper_genStr Z
  have : IsLocallyNoetherian (gen Z) := LocallyOfFiniteType.isLocallyNoetherian (genStr Z)
  have : CompactSpace (gen Z) := QuasiCompact.compactSpace_of_compactSpace (genStr Z)
  have : IsNoetherian (gen Z) := {}
  obtain ⟨h1, h2⟩ := connectedComponent_mem TopologicalSpace.NoetherianSpace.finite_irreducibleComponents
    (fun W hW W' hW' => disjoint_of_smooth (genStr Z) hsm W W' hW hW') z
  have := Z.jQ_open
  exact preimage_mem_irreducibleComponents h1 Z.jQ.isOpenEmbedding
    (Z.jQ_dense.inter_open_nonempty _ h2 ⟨z, mem_connectedComponent⟩)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ)

theorem exists_equiv : ∃ q : s.Comp ≃ Comp (S.Xo κ.l) κ.c, ∀ k z,
    OnComp s k z ↔ (q k).1 = s.T.Z.jQ ⁻¹' connectedComponent z := by
  have hσ : Formalism.L2.PjFree.GoodEmb κ.c κ.σ₀ := rfl
  have hne : ∀ k, ((s.U κ.σ₀).X k).dom.Nonempty := fun k => GlobalTheory.OrbitScalar.exists_mem_dom _
  obtain ⟨q, hq⟩ := GlobalTheory.UnifComp.exists_equiv_comp _ _ _ _ _ _ κ.σ₀ N (s.U κ.σ₀) hσ (s.unf _ hσ).1 hne s.geo
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q, fun k z => ⟨?_, fun h => ?_⟩⟩
  · rintro ⟨x, hx⟩
    by_contra hn
    let pt : Sp (CAt κ.σ₀) := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ)
    exact Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
      ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩ fun e => hn (congrArg Subtype.val e)) (hq k x pt) (hx pt)
  · obtain ⟨x, hx⟩ := hne k
    refine ⟨⟨x, hx⟩, fun pt => ?_⟩
    have := hq k ⟨x, hx⟩ pt
    rw [h] at this
    exact this

theorem existsUnique_onComp (z : gen s.T.Z) : ∃! k, OnComp s k z := by
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  refine ⟨q.symm ⟨_, preimage_connectedComponent_mem s.T.Z hsm z⟩, (hq _ _).2 (by rw [Equiv.apply_symm_apply]),
    fun k hk => ?_⟩
  rw [Equiv.eq_symm_apply]
  exact Subtype.ext ((hq _ _).1 hk)

theorem onComp_compPt (y : Pt s) (pt : Sp Qb) : OnComp s (compPt s y) (y.y pt) := by
  obtain ⟨k, hk, -⟩ := existsUnique_onComp s (y.y pt)
  have : ∃ k, ∀ pt', OnComp s k (y.y pt') :=
    ⟨k, fun pt' => (Subsingleton.elim (α := PrimeSpectrum Qb) pt pt') ▸ hk⟩
  exact Classical.epsilon_spec this pt

theorem compPt_surjective : Function.Surjective (compPt s) := by
  intro k
  obtain ⟨q, hq⟩ := exists_equiv s
  have hsm : Smooth (genStr s.T.Z) := haveI := s.T.smooth; SmoothOfRelativeDimension.smooth S.Dw.dim _
  have := s.T.Z.jQ_open
  have := κ.c.fin
  have : IsAlgClosed Qb := (algebraicClosure.isAlgClosure ℚ ℂ).isAlgClosed
  let φ : κ.c.F →+* Qb := (IsAlgClosed.lift : κ.c.F →ₐ[ℚ] Qb).toRingHom
  have ho : IsOpen (q k).1 := (CompSplitPfB.cspB_isClopen (CompSplitPfD.cspD_comp_disj _ _) (q k)).isOpen
  obtain ⟨g, hg, hgO⟩ := exists_point (genStr s.T.Z) (spMap φ) (s.T.Z.jQ.isOpenEmbedding.isOpenMap _ ho)
    ((q k).2.1.nonempty.image _)
  obtain ⟨f⟩ := GlobalTheory.ShFam.EigLoc.exists_eigFrame _ _ _ _ _ _ _ _ s.T.Z Qb φ g hg
  let y : Pt s := ⟨φ, g, hg, f.v, f.tan, f.eig, f.basis⟩
  let pt : Sp Qb := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum Qb)
  obtain ⟨a, ha, hag⟩ := hgO pt
  refine ⟨y, (existsUnique_onComp s (g pt)).unique (onComp_compPt s y pt) ((hq _ _).2 ?_)⟩
  by_contra hn
  refine Set.disjoint_left.1 (CompSplitPfD.cspD_comp_disj _ _ (q k)
    ⟨_, preimage_connectedComponent_mem s.T.Z hsm (g pt)⟩ fun e => hn (congrArg Subtype.val e)) ha ?_
  show s.T.Z.jQ a ∈ connectedComponent (g pt)
  rw [hag]
  exact mem_connectedComponent

end GlobalTheory.ShFam.PtComp
