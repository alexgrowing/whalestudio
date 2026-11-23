import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsFrameVec
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SpecializesOfUnits
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.DominatesOfCoordsRegular
open NumberField IsDedekindDomain MeasureTheory Filter Topology
open Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Inst Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Rec
open AlgebraicGeometry CategoryTheory
open scoped Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots

theorem chart_point : ∀ (X : AlgebraicGeometry.Scheme.{0}) (Ω : Type) [Field Ω] (ξ : AlgebraicGeometry.Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ (A : Subring Ω) (T : CDVR) (evT : A →+* T.Fr) (c : (k : K) → J k), (∀ k, y ⟨k, c k⟩ ≠ 0) → ∀ (hr : ∀ k i, y ⟨k, i⟩ / y ⟨k, c k⟩ ∈ A), (∀ k i, evT ⟨_, hr k i⟩ ∈ (algebraMap T.V T.Fr).range) → (∀ a : A, ∃ b : A, evT b ≠ 0 ∧ (b : Ω) ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) ∧ (a : Ω) * b ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩)) → ∃ (zV : AlgebraicGeometry.Spec (CommRingCat.of T.V) ⟶ X) (h : genPt ξ ⤳ centre zV), InChart ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) c ⟨centre zV, h⟩ ∧ FinRd.Roots.ReadsPt ξ A T evT zV := by
  intro X Ω _ ξ K _ J _ y hall tie A T evT c hc hr hint hfrac
  classical
  have hx : (∏ k, y ⟨k, c k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨U, hU, hmem⟩ := tie.affine c hx
  have hCeq : Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) =
      Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) :=
    (TiePrimes.adjoin_eq hc).trans (Algebra.adjoin_range_eq_range_aeval ℤ _).symm

  have hgU : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, CoordMap.inChart_genPt tie.gen _ c hx specializes_rfl⟩
  let e : Γ(X, U) →+* Ω := (genMap ξ ⟨genPt ξ, specializes_rfl⟩).comp (X.presheaf.germ U _ hgU).hom
  have he : ∀ {p : X} (hp : p ∈ U) (t : Γ(X, U)), genMap ξ ⟨p, hall p⟩ (X.presheaf.germ U p hp t) = e t := by
    intro p hp t
    show _ = genMap ξ ⟨genPt ξ, specializes_rfl⟩ (X.presheaf.germ U _ hgU t)
    rw [RootHt.ArchC.genMap_germ U (hall p) hp t, RootHt.ArchC.genMap_germ U specializes_rfl hgU t]
  have hC : ∀ t, e t ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩) := fun t => by
    rw [← hCeq]
    exact (tie.ring c hx (e t)).2 fun p hp =>
      ⟨X.presheaf.germ U p.1 ((hmem p.1).2 ⟨p.2, hp⟩) t, he _ t⟩

  let S : Subring Ω := ((algebraMap T.V T.Fr).range.comap evT).map A.subtype
  have hCS : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩), a ∈ S := by
    intro a ha
    induction ha using Algebra.adjoin_induction with
    | mem a ha =>
      obtain ⟨j, rfl⟩ := ha
      exact ⟨⟨_, hr j.1 j.2⟩, hint j.1 j.2, rfl⟩
    | algebraMap n => simpa using intCast_mem S n
    | add _ _ _ _ h1 h2 => exact add_mem h1 h2
    | mul _ _ _ _ h1 h2 => exact mul_mem h1 h2
  have hAm : ∀ t, e t ∈ A := fun t => by
    obtain ⟨b, -, hb⟩ := hCS _ (hC t)
    rw [← hb]
    exact b.2
  let e' : Γ(X, U) →+* A := e.codRestrict A hAm
  let ev : Γ(X, U) →+* T.Fr := evT.comp e'
  have hev : ∀ t, ev t ∈ (algebraMap T.V T.Fr).range := fun t => by
    obtain ⟨b, hb, hb'⟩ := hCS _ (hC t)
    have : b = e' t := Subtype.ext hb'
    show evT (e' t) ∈ _
    rw [← this]
    exact hb

  obtain ⟨g, hg⟩ : ∃ g : Γ(X, U) →+* T.V, (algebraMap T.V T.Fr).comp g = ev := by
    have hι : Function.Injective (algebraMap T.V T.Fr) := IsFractionRing.injective T.V T.Fr
    let eV : T.V ≃+* (algebraMap T.V T.Fr).range :=
      RingEquiv.ofBijective (algebraMap T.V T.Fr).rangeRestrict
        ⟨fun a b h => hι (congrArg Subtype.val h), (algebraMap T.V T.Fr).rangeRestrict_surjective⟩
    refine ⟨eV.symm.toRingHom.comp (ev.codRestrict _ hev), RingHom.ext fun t => ?_⟩
    exact congrArg Subtype.val (eV.apply_symm_apply (ev.codRestrict _ hev t))
  have h0 : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  have hcV : centre (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec : Spec (CommRingCat.of T.V) ⟶ X) ∈ U :=
    h0 (Set.mem_univ (Spec.map (CommRingCat.ofHom g) (IsLocalRing.closedPoint T.V)))
  obtain ⟨hV, hinV⟩ := (hmem _).1 hcV
  refine ⟨_, hV, hinV, ?_⟩

  have hz : gen T (Spec.map (CommRingCat.ofHom g) ≫ hU.fromSpec) =
      Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec := by
    rw [gen, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hg]
  obtain ⟨hcz, hgerm⟩ := RootHt.ArchC.point_of_ringHom hU ev
  obtain ⟨hgz, hchz⟩ := (hmem _).1 hcz
  have hval : ∀ a : A, (a : Ω) ∈ regAt ξ ⟨_, hgz⟩ →
      ValAt ξ (Spec.map (CommRingCat.ofHom ev) ≫ hU.fromSpec) (a : Ω) (evT a) := by
    intro a ha
    refine RootHt.ArchC.val_of_fractions hU hcz hgz ev hgerm ha fun t₁ t₂ h => ?_
    rw [he hcz, he hcz] at h
    have h' : a * e' t₂ = e' t₁ := Subtype.ext h
    have h'' := congrArg evT h'
    rwa [map_mul] at h''
  have hreg : ∀ a ∈ Algebra.adjoin ℤ (Set.range fun j : Σ k, J k => y j / y ⟨j.1, c j.1⟩),
      a ∈ regAt ξ ⟨_, hgz⟩ := fun a ha =>
    (tie.ring c hx a).1 (hCeq ▸ ha) _ hchz
  intro a
  rw [hz]
  refine hval a ?_
  obtain ⟨b, hb0, hbC, habC⟩ := hfrac a
  obtain ⟨h', s, hs1, hs2⟩ := hval b (hreg _ hbC)
  obtain ⟨s₂, hs₂⟩ := hreg _ habC
  have hu : IsUnit s := (Scheme.isLocalHom_stalkClosedPointTo' _).map_nonunit s (by
    rw [hs2]
    exact isUnit_iff_ne_zero.2 hb0)
  obtain ⟨u, rfl⟩ := hu
  have hb1 : (b : Ω) * genMap ξ ⟨_, hgz⟩ (↑u⁻¹ : X.presheaf.stalk _) = 1 := by
    rw [← hs1, ← map_mul, Units.mul_inv, map_one]
  refine ⟨s₂ * ↑u⁻¹, ?_⟩
  rw [map_mul, hs₂, _root_.mul_assoc, hb1, _root_.mul_one]

end GlobalTheory.CompanionTheory.Ar.Rec.FinRd.Roots
