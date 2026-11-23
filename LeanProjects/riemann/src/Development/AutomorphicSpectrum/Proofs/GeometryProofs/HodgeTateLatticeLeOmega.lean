import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.AdelicGroupAlgebraActionInjective
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GenMapFromSpecStalk

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar.HtHoriz

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {G : Over X} [GrpObj G]
  {E : Type} [AddCommGroup E] [Module Ω E] {R : Type} [CommRing R] {L : Type} [AddCommGroup L] [Module R L]

theorem map_add_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (a b : L) : j (a + b) = j a + j b := by
  have key : ∀ e, M.pt (j e) = LieCarrier.epsHom k x ξ hx ≫ M₀.pt e :=
    fun e => Over.OverMorphism.ext (hj e)
  apply M.inj
  rw [M.add, key, key, key, M₀.add, MonObj.comp_mul]

theorem map_smul_of_compat (M : LieModel G ξ E) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (M₀ : LieModel G x L) (j : L → E)
    (hj : ∀ e, (M.pt (j e)).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ (M₀.pt e).left)
    (c : R) (e : L) : j (c • e) = k c • j e := by
  apply M.inj
  apply Over.OverMorphism.ext
  rw [hj, M₀.smul, M.smul, hj, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, LieCarrier.dualMap_epsMul]

theorem isHT_add_natCast_smul {R : Type} [CommRing R] [IsDomain R] {T : Type} [CommGroup T] (Γ : BT.QFGroup R T)
    {S : Scheme.{0}} {G : Over S} [GrpObj G] {x : Spec (CommRingCat.of R) ⟶ S} {i : Γ.G.left ⟶ G.left}
    {L : Type} [AddCommGroup L] [Module R L] {M : LieModel G x L} {N : ℕ} {χ : T →* Rˣ}
    {w : Module.Dual R L} (h : Γ.IsHT i M N χ w) (u : Module.Dual R L) :
    Γ.IsHT i M N χ (w + (N : R) • u) := by
  obtain ⟨s, hs, h⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := h e
  refine ⟨v, h1, h2, h3.trans ?_⟩
  congr 2
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton]
  exact ⟨-u e, by simp⟩

theorem natCast_smul_isHTFormOver (M : LieModel G ξ E) (N : ℕ) {x : Spec (CommRingCat.of R) ⟶ X} {k : R →+* Ω}
    (hx : Spec.map (CommRingCat.ofHom k) ≫ x = ξ) (hk : Function.Injective k) (h : M.IsHTFormOver N x k 0)
    (w : Module.Dual Ω E)
    (hw : ∀ (e : E) (v : epsAt x ⟶ G), IsTanAt G x v →
      (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap k)) ≫ v.left → w e ∈ k.range) :
    M.IsHTFormOver N x k ((N : Ω) • w) := by
  obtain ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, ht, hj, hHT, h0⟩ := h
  have hreg : ∀ e, ∃ r, k r = w (j e) := fun e => hw (j e) (M₀.pt e) (M₀.tan e) (hj e)
  choose f hf using hreg
  let u : Module.Dual R L :=
    { toFun := f
      map_add' := fun a b => hk (by rw [map_add, hf, hf, hf, map_add_of_compat M hx M₀ j hj, map_add])
      map_smul' := fun c e => hk (by
        simp only [RingHom.id_apply, smul_eq_mul, map_mul]
        rw [hf, hf, map_smul_of_compat M M₀ j hj, map_smul, smul_eq_mul]) }
  refine ⟨hd, T, _, Γ, i, L, _, _, M₀, j, χ, w₀ + (N : R) • u, ht, hj, isHT_add_natCast_smul Γ hHT u, fun e => ?_⟩
  have h1 : k (w₀ e) = 0 := (h0 e).symm
  have h2 : k (u e) = w (j e) := hf e
  simp [h1, h2]

end GlobalTheory.CompanionTheory.Ar.HtHoriz

namespace GlobalTheory.CompanionTheory.Ar

theorem htLat_le_omLat_and_smul_mem : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G]
    [IsCommMonObj G] (V : Type) [AddCommGroup V] [Module Ω V] (M : LieModel G ξ V) (N : ℕ) (p : Cpt ξ),
    IsCptGen ξ → Smooth G.hom → M.htLat N p ≤ M.omLat p ∧
      (M.IsHTFormAt N p 0 → ∀ w ∈ M.omLat p, (N : Ω) • w ∈ M.htLat N p) := by
  intro X Ω _ ξ G _ _ V _ _ M N p hξ _
  refine ⟨?_, ?_⟩
  · refine Submodule.span_le.2 ?_
    rintro w ⟨_, T, _, Γ, i, L, _, _, M₀, j, χ, w₀, -, hj, -, hw⟩ e he
    obtain ⟨v, hv, hev⟩ := ((lieLat_carrier X G Ω ξ V M p).1 e).1 he
    obtain ⟨e₀, rfl⟩ := M₀.onto v hv
    have : j e₀ = e := M.inj (Over.OverMorphism.ext ((hj e₀).trans hev.symm))
    subst this
    exact ⟨w₀ e₀, (hw e₀).symm⟩
  · intro h w hw
    exact Submodule.subset_span (HtHoriz.natCast_smul_isHTFormOver M N (LieCarrier.genMap_fromSpecStalk p) (hξ.inj p) h w
      fun e v hv hev => hw e (Submodule.subset_span ⟨v, hv, hev⟩))

end GlobalTheory.CompanionTheory.Ar
