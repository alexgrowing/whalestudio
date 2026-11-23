import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.VanIdealHomog

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out MvPolynomial GlobalTheory.CompanionTheory.GE
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (PSpace Sp spMap)

namespace GlobalTheory.CompanionTheory.GE

theorem comp_app_eq_zero_iff {X Y Z : Scheme.{0}} (b : X ⟶ Y) [IsIso b] (g : Y ⟶ Z) (U : Z.Opens)
    (s : Γ(Z, U)) : ((b ≫ g).app U).hom s = 0 ↔ (g.app U).hom s = 0 := by
  rw [Scheme.Hom.comp_app]
  have hi : Function.Injective (b.app (g ⁻¹ᵁ U)).hom :=
    (ConcreteCategory.bijective_of_isIso (b.app (g ⁻¹ᵁ U))).1
  change (b.app (g ⁻¹ᵁ U)).hom ((g.app U).hom s) = 0 ↔ _
  exact map_eq_zero_iff _ hi

theorem mem_ker_thickι_iff {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal
        ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      ((GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))).app
        (GlobalTheory.ProjSpace.chart R N k)).hom s = 0 := by
  have h := GlobalTheory.ProjSpace.isPullback_baseChange N (Ideal.Quotient.mk (I ^ (e + 1)))
  have hb : h.isoPullback.hom ≫ thickι R I N e =
      GlobalTheory.ProjSpace.baseChange N (Ideal.Quotient.mk (I ^ (e + 1))) := h.isoPullback_hom_fst
  rw [Scheme.Hom.ker_apply, RingHom.mem_ker, ← hb]
  exact (comp_app_eq_zero_iff h.isoPullback.hom (thickι R I N e) _ s).symm

theorem formOn_eq_zero_iff {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    {V : (PSpace R N).Opens} (hV : V = GlobalTheory.ProjSpace.chart R N k) (hle : V ≤ GlobalTheory.ProjSpace.chart R N k)
    {n : ℕ} {f : MvPolynomial (Fin (N + 1)) R} (hf : f.IsHomogeneous n) :
    GlobalTheory.ProjSpace.formOn V k hle n f hf = 0 ↔ f = 0 := by
  subst hV
  rw [← GlobalTheory.ProjSpace.formOn_zero (U := GlobalTheory.ProjSpace.chart R N k) (i := k) (hi := le_rfl) (n := n)]
  exact GlobalTheory.ProjSpace.formOn_chart_inj R N k hf _

open scoped GlobalTheory.ProjSpace in
attribute [local instance] MvPolynomial.gradedAlgebra in

theorem exists_formOn_eq {R : Type} [CommRing R] {N : ℕ} (k : Fin (N + 1))
    (s : Γ(PSpace R N, GlobalTheory.ProjSpace.chart R N k)) :
    ∃ (n : ℕ) (f : MvPolynomial (Fin (N + 1)) R) (hf : f.IsHomogeneous n),
      s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n f hf := by
  obtain ⟨p, rfl⟩ := (GlobalTheory.ProjSpace.chartAlgEquiv R N k).surjective s
  obtain ⟨n, f, hf, h⟩ := HomogeneousLocalization.Away.mk_surjective _ (GlobalTheory.ProjSpace.X_mem R N k)
    (GlobalTheory.ProjSpace.polyEquivAway R N k p)
  have hf' : f.IsHomogeneous n := by simpa using hf
  refine ⟨n, f, hf', ?_⟩
  rw [← GlobalTheory.ProjSpace.chartAlgEquiv_dehom R N k hf']
  congr 1
  have h1 := GlobalTheory.ProjSpace.awayToPoly_mk R N k n f hf
  rw [h] at h1
  exact ((GlobalTheory.ProjSpace.polyEquivAway R N k).left_inv p).symm.trans h1

theorem ker_thickι_chart : ∀ {R : Type} [CommRing R] (I : Ideal R) (N e : ℕ) (k : Fin (N + 1)),
    (∀ s ∈ (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩,
      ∃ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
        t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) ∧
        s = GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht) ∧
    (∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) →
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩) := by
  intro R _ I N e k
  have hmem : ∀ (n : ℕ) (t : MvPolynomial (Fin (N + 1)) R) (ht : t.IsHomogeneous n),
      GlobalTheory.ProjSpace.formOn (GlobalTheory.ProjSpace.chart R N k) k le_rfl n t ht ∈
        (Scheme.Hom.ker (thickι R I N e)).ideal ⟨GlobalTheory.ProjSpace.chart R N k, GlobalTheory.ProjSpace.isAffineOpen_chart R N k⟩ ↔
      t ∈ (I ^ (e + 1)).map (C : R →+* MvPolynomial (Fin (N + 1)) R) := by
    intro n t ht
    rw [mem_ker_thickι_iff, GlobalTheory.ProjSpace.baseChange_app_formOn,
      formOn_eq_zero_iff k (GlobalTheory.ProjSpace.baseChange_preimage_chart N _ k), ← RingHom.mem_ker,
      MvPolynomial.ker_map, Ideal.mk_ker]
  refine ⟨fun s hs => ?_, fun n t ht h => (hmem n t ht).2 h⟩
  obtain ⟨n, t, ht, rfl⟩ := exists_formOn_eq k s
  exact ⟨n, t, ht, (hmem n t ht).1 hs, rfl⟩

end GlobalTheory.CompanionTheory.GE
