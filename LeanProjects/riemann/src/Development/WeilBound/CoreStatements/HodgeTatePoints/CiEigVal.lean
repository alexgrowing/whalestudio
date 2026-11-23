import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.CurveSemiAbelianConjecture
import Development.AutomorphicSpectrum.Statements.GeometryStatements.SeparableFormGroupElementFixesUniquePositiveLine
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.EigenProjectorsSplitActionStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.LieValAtBase
import Development.WeilBound.CoreStatements.HodgeTatePoints.EigFrob

set_option backward.isDefEq.respectTransparency false

noncomputable section

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Ci

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {V : Type} [AddCommGroup V] [Module Ω V]

theorem span_values [IsCommMonObj G] (hξ : IsCptGen ξ) (hs : Smooth G.hom) (M : LieModel G ξ V) {R : Type}
    [CommRing R] [IsLocalRing R] (z : Spec (CommRingCat.of R) ⟶ X) (h : genPt ξ ⤳ centre z) {ER : Type}
    [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER) :
    Submodule.span R {v | ∃ e, M.ValAt z e (MR.pt v)} = ⊤ := by
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z))
  obtain ⟨j, hj, -, hjb⟩ := exists_base (A := X.presheaf.stalk (centre z)) (Scheme.stalkClosedPointTo z).hom _ z
    (LieTangent.spec_centre z) MA MR
  obtain ⟨i, hi, -, -⟩ := exists_base (genMap ξ ⟨centre z, h⟩) _ ξ
    (LieTangent.spec_genMap ξ ⟨centre z, h⟩) MA M
  obtain ⟨hf, hp⟩ := PositivityTheory.HtPt.Htat.lie_fin X G (X.presheaf.stalk (centre z)) (X.fromSpecStalk (centre z)) EA MA
  have : Module.Free (X.presheaf.stalk (centre z)) EA := Module.free_of_flat_of_isLocalRing
  obtain ⟨bz, hbz⟩ := hjb hs _ (Module.finBasis _ EA)
  refine top_le_iff.1 (bz.span_eq.symm.le.trans (Submodule.span_mono ?_))
  rintro _ ⟨k, rfl⟩
  refine ⟨i (Module.finBasis _ EA k), (M.valAt_iff _ _ _).2 ⟨h, MA.pt _,
    (M.extends_iff _ _ _).2 ⟨MA.tan _, hi _⟩, ?_⟩⟩
  rw [hbz, hj]

theorem lieValAt_end {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {f : G ⟶ G} [IsMonHom f] {A : V →ₗ[Ω] V} (hA : M.IsDiffOf f A) {e : V}
    {w : epsAt z ⟶ G} (h : M.ValAt z e w) : M.ValAt z (A e) (w ≫ f) := by
  rw [LieModel.valAt_iff] at h ⊢
  obtain ⟨hc, v, hv, rfl⟩ := h
  rw [LieModel.extends_iff] at hv
  refine ⟨hc, v ≫ f, (M.extends_iff _ _ _).2 ⟨?_, ?_⟩, Category.assoc _ _ _⟩
  · rw [LieTangent.isTanAt_iff, ← Category.assoc, (LieTangent.isTanAt_iff _).1 hv.1, MonObj.one_comp]
  · rw [hA e, hv.2, Category.assoc]

theorem lieValAt_smul {M : LieModel G ξ V} {R : Type} [CommRing R] [IsLocalRing R]
    {z : Spec (CommRingCat.of R) ⟶ X} {ER : Type} [AddCommGroup ER] [Module R ER] {MR : LieModel G z ER} {e : V}
    {v : ER} (h : M.ValAt z e (MR.pt v)) {a : Ω} {r : R} (ha : ValAt ξ z a r) :
    M.ValAt z (a • e) (MR.pt (r • v)) := by
  obtain ⟨h1, s, rfl, rfl⟩ := ha
  rw [MR.pt_smul]
  exact h.smul h1 s

def emptyCurve (K : Type) [Field K] : ACurve K where
  I := Empty
  v := fun i => i.elim
  w := fun i => i.elim
  fin := fun _ _ => Set.toFinite _
  prod := fun _ _ => finsum_of_isEmpty _

theorem eig_val : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (k K : Type) [Field k] [Field K] [Algebra k K] (z : Spec (CommRingCat.of K) ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (Vz : Type) [AddCommGroup Vz] [Module K Vz] (Mz : LieModel G z Vz) (h₀ : genPt ξ ⤳ centre z) (O S : Type) [CommRing O] [Fintype S] (act : O → (G ⟶ G)) (r : O →+* Module.End Ω V) (rz : O →+* Module.End K Vz) (σ : S → (O →+* Ω)) (χ : S → (O →+* k)), IsCptGen ξ → Smooth G.hom → (∀ a, IsMonHom (act a)) → M.IsActOf act r → Mz.IsActOf act rz → IsSplit χ → (∀ s a, ValAt ξ z (σ s a) (algebraMap k K (χ s a))) → M.lat ⟨centre z, h₀⟩ = ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩ → ∀ s, Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)} = eigSp rz ((algebraMap k K).comp (χ s)) := by
  intro X Ω _ ξ k K _ _ _ z G _ _ V _ _ M Vz _ _ Mz h₀ O S _ _ act r rz σ χ hξ hs hm hr hrz hχ hσ hlat s
  classical
  have : Module.Finite K Vz := (PositivityTheory.HtPt.Htat.lie_fin X G K z Vz Mz).1
  obtain ⟨e, -, -, he3, -, he5⟩ := GlobalTheory.T.eigen_projectors_split_action K (emptyCurve K) Vz (fun i => i.elim) O k S χ hχ (fun i => i.elim) rz
    ⟨fun i => i.elim, Module.finBasis K Vz, Set.toFinite (α := Empty) _⟩ (fun a i => i.elim)
  obtain ⟨m, c, a, hc, hes⟩ := he5 s
  let U : S → Submodule K Vz := fun s =>
    Submodule.span K {v | ∃ e ∈ M.eigLat r (σ s) ⟨centre z, h₀⟩, M.ValAt z e (Mz.pt v)}
  have hU : ∀ t, U t ≤ eig (fun a => rz a) (fun a => algebraMap k K (χ t a)) := by
    intro t
    refine Submodule.span_le.2 ?_
    rintro v ⟨x, hx, hv⟩
    refine mem_eig.2 fun b => Mz.inj ?_
    have := hm b
    have h1 := lieValAt_end (hr b) hv
    have h2 := lieValAt_smul hv (hσ t b)
    have h3 : r b x = σ t b • x := (mem_eig (ρ := fun a => r a) (χ := fun a => σ t a)).1 hx.2 b
    rw [h3] at h1
    exact (hrz b v).trans (h1.unique hξ h2)
  have htop : ⨆ t, U t = ⊤ := by
    refine top_le_iff.1 ((span_values hξ hs M z h₀ Mz).symm.le.trans (Submodule.span_le.2 ?_))
    rintro v ⟨x, hx⟩
    obtain ⟨_, hxl⟩ := (M.exists_valAt_iff z x).1 ⟨_, hx⟩
    have key : ∀ x ∈ ⨆ s, M.eigLat r (σ s) ⟨centre z, h₀⟩, ∃ v ∈ ⨆ t, U t, M.ValAt z x (Mz.pt v) := by
      intro x hx
      induction hx using Submodule.iSup_induction' with
      | mem t x hx =>
        obtain ⟨w, hw⟩ := (M.exists_valAt_iff z x).2 ⟨h₀, hx.1⟩
        obtain ⟨v, rfl⟩ := Mz.onto w hw.isTanAt
        exact ⟨v, Submodule.mem_iSup_of_mem t (Submodule.subset_span ⟨x, hx, hw⟩), hw⟩
      | zero => exact ⟨0, zero_mem _, by rw [Mz.pt_zero]; exact M.valAt_zero h₀⟩
      | add x y _ _ hx hy =>
        obtain ⟨v, hv, hv'⟩ := hx
        obtain ⟨w, hw, hw'⟩ := hy
        exact ⟨v + w, add_mem hv hw, by rw [Mz.add]; exact hv'.add hw'⟩
    obtain ⟨v', hv', hv''⟩ := key x (hlat ▸ hxl)
    rw [Mz.inj (hx.unique hξ hv'')]
    exact hv'
  refine le_antisymm (hU s) fun v hv => ?_
  have key : ∀ v ∈ ⨆ t, U t, e s v ∈ U s := by
    intro v hv
    induction hv using Submodule.iSup_induction' with
    | mem t x hx =>
      have h1 : e s x = algebraMap k K (if t = s then 1 else 0) • x := by
        rw [← hc t, hes, LinearMap.sum_apply, map_sum, Finset.sum_smul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [LinearMap.smul_apply, mem_eig.1 (hU t hx) (a j), map_mul, mul_smul]
      rw [h1]
      split_ifs with h
      · subst h; exact Submodule.smul_mem _ _ hx
      · simp
    | zero => simp
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  have := key v (htop ▸ Submodule.mem_top)
  rwa [he3 s v hv] at this

end PositivityTheory.HtPt.Ci
