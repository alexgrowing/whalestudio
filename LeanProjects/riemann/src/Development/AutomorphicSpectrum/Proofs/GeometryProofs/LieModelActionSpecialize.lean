import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Geometry₂.GagaSections
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ValueSpan

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric

theorem mem_eigSp_iff {R E O : Type} [CommRing R] [AddCommGroup E] [Module R E] [CommRing O]
    {ρ : O →+* Module.End R E} {σ : O →+* R} {v : E} : v ∈ eigSp ρ σ ↔ ∀ a, ρ a v = σ a • v := by
  simp [eigSp, Submodule.mem_iInf, LinearMap.mem_ker, sub_eq_zero]

theorem valAt_act {X : Scheme.{0}} {G : Over X} [GrpObj G] {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {V : Type}
    [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) {F : Type} [Field F] {z : Sp F ⟶ X} {W : Type}
    [AddCommGroup W] [Module F W] (Mz : LieModel G z W) {A : Type} [CommRing A] (act : OAct A G)
    {ρ : A →+* Module.End Ω V} {ρz : A →+* Module.End F W} (hρ : M.IsActOf act.act ρ)
    (hρz : Mz.IsActOf act.act ρz) (a : A) {e : V} {w : W} (h : M.ValAt z e (Mz.pt w)) :
    M.ValAt z (ρ a e) (Mz.pt (ρz a w)) := by
  haveI : IsMonHom (act.act a) := act.hom a
  obtain ⟨h', v, ⟨ht, he⟩, hw⟩ := h
  refine ⟨h', v ≫ act.act a, ⟨?_, ?_⟩, ?_⟩
  · show _ ≫ (v ≫ act.act a).left = (1 : Over.mk _ ⟶ G).left
    have h1 : (1 : Over.mk (X.fromSpecStalk (centre z)) ⟶ G) ≫ act.act a = 1 := MonObj.one_comp _
    exact (Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ (act.act a).left) ht).trans (congrArg CommaMorphism.left h1))
  · rw [hρ a e, Over.comp_left, he]
    exact Category.assoc _ _ _
  · rw [hρz a w, Over.comp_left, hw]
    exact Category.assoc _ _ _

theorem value_span : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (F : Type) [Field F] (z : Sp F ⟶ X) (h : genPt ξ ⤳ centre z) (W : Type) [AddCommGroup W] [Module F W] (Mz : LieModel G z W) (A : Type) [CommRing A] (act : OAct A G) (ρ : A →+* Module.End Ω V) (ρz : A →+* Module.End F W) (K : Type) [Field K] (inc : K →+* Ω) (βF : K →+* F) (σ : A →+* K) (n : ℕ) (e : Fin n → A) (cf : Fin n → K) (r : ℕ) (b : Fin r → V), IsCptGen ξ → Smooth G.hom → M.IsActOf act.act ρ → Mz.IsActOf act.act ρz → (∀ k : K, ValAt ξ z (inc k) (βF k)) → ∑ k, cf k * σ (e k) = 1 → (∀ (a : A) (w : V), ρ a (∑ k, inc (cf k) • ρ (e k) w) = inc (σ a) • ∑ k, inc (cf k) • ρ (e k) w) → (M.eigLat ρ (inc.comp σ)).IsFrameAt b ⟨centre z, h⟩ → ∃ u : Fin r → W, (∀ i, M.ValAt z (b i) (Mz.pt (u i))) ∧ Submodule.span F (Set.range u) = eigSp ρz (βF.comp σ) := by
  intro X G _ _ Ω _ ξ V _ _ M F _ z h W _ _ Mz A _ act ρ ρz K _ inc βF σ n e cf r b hgen hsm hρ hρz hinc hsum hπ hb
  obtain ⟨ev, hval, hsmul, hspan⟩ := GlobalTheory.T.lie_lattice_eval_at_local_ring X G Ω ξ V M F z h W Mz hgen hsm
  have hreg : ∀ k : K, inc k ∈ regAt ξ ⟨centre z, h⟩ := by
    intro k
    obtain ⟨_, s, hs, _⟩ := hinc k
    exact ⟨s, hs⟩
  have hvalr : ∀ c : regAt ξ ⟨centre z, h⟩, ∃ t : F, ValAt ξ z (c : Ω) t := by
    rintro ⟨_, s, rfl⟩
    exact ⟨_, h, s, rfl, rfl⟩
  have hself : ∀ l : M.lat ⟨centre z, h⟩, M.ValAt z l (Mz.pt (ev l)) :=
    fun l => (hval _ _).2 ⟨l.2, rfl⟩
  have hact : ∀ (a : A) (l : M.lat ⟨centre z, h⟩), ∃ he : ρ a l ∈ M.lat ⟨centre z, h⟩,
      ev ⟨ρ a l, he⟩ = ρz a (ev l) :=
    fun a l => (hval _ _).1 (valAt_act M Mz act hρ hρz a (hself l))
  have hbm : ∀ i, b i ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := fun i => by
    rw [hb.2]
    exact Submodule.subset_span ⟨i, rfl⟩
  have hbl : ∀ i, b i ∈ M.lat ⟨centre z, h⟩ := fun i => (hbm i).1
  have hbe : ∀ i, b i ∈ eigSp ρ (inc.comp σ) := fun i => (hbm i).2
  refine ⟨fun i => ev ⟨b i, hbl i⟩, fun i => hself ⟨b i, hbl i⟩, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine mem_eigSp_iff.2 fun a => ?_
    obtain ⟨he, h2⟩ := hact a ⟨b i, hbl i⟩
    have h3 : ρ a (b i) = inc (σ a) • b i := mem_eigSp_iff.1 (hbe i) a
    have h4 : (⟨ρ a (b i), he⟩ : M.lat ⟨centre z, h⟩) =
        (⟨inc (σ a), hreg _⟩ : regAt ξ ⟨centre z, h⟩) • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := Subtype.ext h3
    have h5 : ρz a (ev ⟨b i, hbl i⟩) = βF (σ a) • ev ⟨b i, hbl i⟩ := by
      rw [← h2]
      refine (congrArg ev h4).trans ?_
      exact hsmul _ _ _ (hinc _)
    exact h5
  · intro w hw
    have hw' := mem_eigSp_iff.1 hw
    let πW : W →ₗ[F] W := ∑ k, βF (cf k) • ρz (e k)
    have hπw : πW w = w := by
      have h1 : ∀ k, βF (cf k) • ρz (e k) w = βF (cf k * σ (e k)) • w := fun k => by
        rw [hw' (e k), map_mul, mul_smul]
        rfl
      simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply]
      rw [Finset.sum_congr rfl fun k _ => h1 k, ← Finset.sum_smul, ← map_sum, hsum, map_one, one_smul]
    have key : ∀ l : M.lat ⟨centre z, h⟩,
        πW (ev l) ∈ Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩) := by
      intro l
      choose he hk using fun k => hact (e k) l
      let c : Fin n → regAt ξ ⟨centre z, h⟩ := fun k => ⟨inc (cf k), hreg _⟩
      let m : M.lat ⟨centre z, h⟩ := ∑ k, c k • (⟨ρ (e k) l, he k⟩ : M.lat ⟨centre z, h⟩)
      have hevm : ev m = πW (ev l) := by
        simp only [πW, LinearMap.sum_apply, LinearMap.smul_apply, m, map_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hsmul _ _ _ (hinc (cf k)), hk k]
      have hmv : (m : V) = ∑ k, inc (cf k) • ρ (e k) l := by
        simp only [m, AddSubmonoidClass.coe_finset_sum]
        exact Finset.sum_congr rfl fun _ _ => rfl
      have hme : (m : V) ∈ eigSp ρ (inc.comp σ) := mem_eigSp_iff.2 fun a => by
        rw [hmv]
        exact hπ a l
      have hmL : (m : V) ∈ (M.eigLat ρ (inc.comp σ)) ⟨centre z, h⟩ := ⟨m.2, hme⟩
      rw [hb.2] at hmL
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hmL
      choose t ht using fun i => hvalr (d i)
      have hm : m = ∑ i, d i • (⟨b i, hbl i⟩ : M.lat ⟨centre z, h⟩) := by
        apply Subtype.ext
        rw [← hd, AddSubmonoidClass.coe_finset_sum]
        exact Finset.sum_congr rfl fun _ _ => rfl
      rw [← hevm, hm, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [hsmul _ _ _ (ht i)]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    have hwt : w ∈ Submodule.span F (Set.range ev) := by
      rw [hspan]
      exact Submodule.mem_top
    rw [← hπw]
    refine Submodule.span_induction (p := fun y _ => πW y ∈
      Submodule.span F (Set.range fun i => ev ⟨b i, hbl i⟩)) ?_ ?_ ?_ ?_ hwt
    · rintro _ ⟨l, rfl⟩
      exact key l
    · rw [map_zero]
      exact Submodule.zero_mem _
    · intro x y _ _ hx hy
      rw [map_add]
      exact Submodule.add_mem _ hx hy
    · intro c x _ hx
      rw [map_smul]
      exact Submodule.smul_mem _ c hx

end GlobalTheory.CompanionTheory.Ar.ValueSpan
