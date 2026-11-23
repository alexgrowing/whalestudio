import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.NormalAffineChartExistsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilOpenChartStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeTateWeilUniqueStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionEmbeddingGeometricPointsStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsHodgeTateFunctionalStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelFiniteBaseChangeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelBaseChangeMapStatement

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HTLift

theorem spMap_comp_spMap {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : B →+* C) (g : A →+* B) :
    spMap f ≫ spMap g = spMap (f.comp g) := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem exists_char_units {R Ω T : Type} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [Field Ω]
    (κ : FractionRing R ≃+* Ω) [CommGroup T] {n : ℕ} (hn : 1 ≤ n) (c : T →* Ωˣ) (hc : ∀ t, c t ^ n = 1) :
    ∃ χ : T →* Rˣ, ∀ t, κ (algebraMap R (FractionRing R) (χ t : R)) = (c t : Ω) := by
  have hex : ∀ t, ∃ r : R, algebraMap R (FractionRing R) r = κ.symm (c t : Ω) := by
    intro t
    refine IsIntegrallyClosed.isIntegral_iff.1 ?_
    refine ⟨Polynomial.X ^ n - Polynomial.C 1, Polynomial.monic_X_pow_sub_C 1 (by omega), ?_⟩
    have h1 : ((c t : Ω)) ^ n = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C, map_one]
    rw [← map_pow, h1]
    simp
  choose r hr using hex
  have hinj : Function.Injective (algebraMap R (FractionRing R)) := IsFractionRing.injective _ _
  let f : T →* R :=
    { toFun := r
      map_one' := hinj (by rw [hr]; simp)
      map_mul' := fun s t => hinj (by rw [map_mul, hr, hr, hr]; simp) }
  refine ⟨f.toHomUnits, fun t => ?_⟩
  have : ((f.toHomUnits t : Rˣ) : R) = r t := rfl
  rw [this, hr]
  simp

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {R : Type} [CommRing R] [IsDomain R]

abbrev Tors (G : Over X) [GrpObj G] [IsCommMonObj G] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (n : ℕ) :
    Subgroup (Over.mk ξ ⟶ G) :=
  (powMonoidHom n : (Over.mk ξ ⟶ G) →* (Over.mk ξ ⟶ G)).ker

theorem tors_pow {G : Over X} [GrpObj G] [IsCommMonObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {n : ℕ}
    (t : Tors G ξ n) : t.1 ^ n = 1 := t.2

theorem exists_tors [CharZero Ω] [IsNoetherianRing R] (G : Over X) [GrpObj G] [IsCommMonObj G]
    (hS : IsSemiAbelian G) (κ : FractionRing R ≃+* Ω) (x : Spec (CommRingCat.of R) ⟶ X) {n : ℕ} (hn : 1 ≤ n)
    (hF : FullTorsion G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n) :
    ∃ (Γ : BT.QFGroup R (Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n)) (i : Γ.G.left ⟶ G.left),
      Γ.IsTorsionAlong G x n i ∧ ∀ (t : Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n)
        (g : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G),
        spMap κ.toRingHom ≫ (Γ.pt t).left ≫ i = g.left → g = t.1 := by
  have : CharZero R := (κ.toRingHom.comp (algebraMap R (FractionRing R))).charZero
  have e1 : spMap κ.symm.toRingHom ≫ spMap (κ.toRingHom.comp (algebraMap R _)) =
      spMap (algebraMap R (FractionRing R)) := by
    rw [spMap_comp_spMap]
    congr 1
    ext r
    simp
  have e2 : spMap κ.toRingHom ≫ spMap κ.symm.toRingHom = 𝟙 _ := by
    rw [spMap_comp_spMap]
    have : κ.toRingHom.comp κ.symm.toRingHom = RingHom.id Ω := by
      ext r
      simp
    rw [this]
    simp [spMap]
  set ξ := spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x with hξ
  have e3 : spMap κ.symm.toRingHom ≫ ξ = (BT.genPt R).hom ≫ x := by
    rw [hξ, ← Category.assoc, e1]
    rfl
  have e4 : spMap κ.toRingHom ≫ (BT.genPt R).hom ≫ x = ξ := by
    rw [← e3, ← Category.assoc, e2, Category.id_comp]
  let a : Over.mk ((BT.genPt R).hom ≫ x) ⟶ Over.mk ξ := Over.homMk (spMap κ.symm.toRingHom) e3
  let b : Over.mk ξ ⟶ Over.mk ((BT.genPt R).hom ≫ x) := Over.homMk (spMap κ.toRingHom) e4
  have hba : b ≫ a = 𝟙 _ := Over.OverMorphism.ext e2
  let τ : Tors G ξ n →* (Over.mk ((BT.genPt R).hom ≫ x) ⟶ G) :=
    { toFun := fun t => a ≫ t.1
      map_one' := MonObj.comp_one a
      map_mul' := fun s t => MonObj.comp_mul a s.1 t.1 }
  have hinj : Function.Injective τ := by
    intro s t h
    have h' : a ≫ s.1 = a ≫ t.1 := h
    have h2 := congrArg (b ≫ ·) h'
    simp only [← Category.assoc, hba, Category.id_comp] at h2
    exact Subtype.ext h2
  have hpow : ∀ t, τ t ^ n = 1 := by
    intro t
    show (a ≫ t.1) ^ n = 1
    rw [← MonObj.comp_pow, tors_pow, MonObj.comp_one]
  have hgeo : ∀ (Ω' : Type) [Field Ω'] [IsAlgClosed Ω'] (α : FractionRing R →+* Ω')
      (g : Over.mk (Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x) ⟶ G), g ^ n = 1 →
      ∃ t, g.left = Spec.map (CommRingCat.ofHom α) ≫ (τ t).left := by
    intro Ω' _ _ α g hg
    have e5 : spMap (α.comp κ.symm.toRingHom) = spMap α ≫ spMap κ.symm.toRingHom :=
      (spMap_comp_spMap _ _).symm
    have e6 : spMap (α.comp κ.symm.toRingHom) ≫ ξ = Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x := by
      rw [e5, Category.assoc, e3]
    let c : Over.mk (spMap (α.comp κ.symm.toRingHom) ≫ ξ) ⟶
        Over.mk (Spec.map (CommRingCat.ofHom α) ≫ (BT.genPt R).hom ≫ x) :=
      Over.homMk (𝟙 _) (by simpa using e6.symm)
    have hg' : (c ≫ g) ^ n = 1 := by rw [← MonObj.comp_pow, hg, MonObj.comp_one]
    obtain ⟨y, hy⟩ := hF Ω' (α.comp κ.symm.toRingHom) (c ≫ g) hg'
    let ψ : Over.mk (spMap (α.comp κ.symm.toRingHom) ≫ ξ) ⟶ Over.mk ξ :=
      Over.homMk (spMap (α.comp κ.symm.toRingHom)) rfl
    have hψ : ψ ≫ y = c ≫ g := Over.OverMorphism.ext hy.symm
    have hepi : Epi (spMap (α.comp κ.symm.toRingHom)) := by
      have : Flat (spMap (α.comp κ.symm.toRingHom)) := by
        rw [spMap, Flat.SpecMap_iff]
        exact RingHom.Flat.of_isField (Field.toIsField Ω) _
      have : Surjective (spMap (α.comp κ.symm.toRingHom)) := ⟨Function.surjective_to_subsingleton _⟩
      exact Flat.epi_of_flat_of_surjective _
    have hy1 : y ^ n = 1 := by
      have h3 : ψ ≫ y ^ n = ψ ≫ 1 := by rw [MonObj.comp_pow, hψ, hg', MonObj.comp_one]
      refine Over.OverMorphism.ext ?_
      exact (cancel_epi (spMap (α.comp κ.symm.toRingHom))).1 (congrArg (·.left) h3)
    refine ⟨⟨y, hy1⟩, ?_⟩
    have h4 : g.left = spMap (α.comp κ.symm.toRingHom) ≫ y.left := by
      have : (c ≫ g).left = g.left := Category.id_comp _
      rw [← this, hy]
    rw [h4, e5, Category.assoc]
    rfl
  obtain ⟨Γ, i, h1, h2⟩ := GlobalTheory.T.torsion_embedding_geometric_points R (Tors G ξ n) X G hS x n hn τ hinj hpow hgeo
  refine ⟨Γ, i, h1, fun t g h => Over.OverMorphism.ext ?_⟩
  rw [← h, h2 t]
  show spMap κ.toRingHom ≫ spMap κ.symm.toRingHom ≫ t.1.left = _
  rw [← Category.assoc, e2, Category.id_comp]

theorem exists_form [IsIntegrallyClosed R] [IsNoetherianRing R] (G : Over X) [GrpObj G] [IsCommMonObj G]
    (hsm : Smooth G.hom) (κ : FractionRing R ≃+* Ω) (x : Spec (CommRingCat.of R) ⟶ X)
    {E : Type} [AddCommGroup E] [Module Ω E]
    (M : LieModel G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) E)
    {T : Type} [CommGroup T] [Finite T] (Γ : BT.QFGroup R T) (i : Γ.G.left ⟶ G.left) {n : ℕ}
    (hi : Γ.IsTorsionAlong G x n i) (χ : T →* Rˣ) :
    ∃ (L₀ : Type) (_ : AddCommGroup L₀) (_ : Module R L₀) (M₀ : LieModel G x L₀) (j : L₀ → E)
      (w₀ : Module.Dual R L₀) (w : Module.Dual Ω E),
      (∀ v, (M.pt (j v)).left = spMap (dualMap (κ.toRingHom.comp (algebraMap R _))) ≫ (M₀.pt v).left) ∧
        Γ.IsHT i M₀ n χ w₀ ∧ ∀ v, w (j v) = κ (algebraMap R _ (w₀ v)) := by
  obtain ⟨L₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G R x
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.exists_hodge_tate_functional R T Γ X G x n i hi hsm L₀ M₀ χ
  letI : Algebra R Ω := (κ.toRingHom.comp (algebraMap R (FractionRing R))).toAlgebra
  letI : Module R E := Module.compHom E (algebraMap R Ω)
  have : IsScalarTower R Ω E := ⟨fun a b c => by
    rw [Algebra.smul_def, mul_smul]
    rfl⟩
  obtain ⟨j, hj, hjs, -⟩ := GlobalTheory.T.lie_model_base_change_map X G R Ω x L₀ E M₀ M
  let β : L₀ →ₗ[R] E :=
    { toFun := j
      map_add' := map_add j
      map_smul' := fun a v => hjs a v }
  obtain ⟨-, -, hbc⟩ := GlobalTheory.T.lie_model_finite_base_change X G R x L₀ M₀
  have hb : IsBaseChange Ω β := hbc Ω E M β hj
  refine ⟨L₀, _, _, M₀, j, w₀, hb.lift ((Algebra.linearMap R Ω) ∘ₗ w₀), hj, hw₀, fun v => ?_⟩
  exact hb.lift_eq ((Algebra.linearMap R Ω) ∘ₗ w₀) v

end GlobalTheory.CompanionTheory.Ar.HTLift

namespace GlobalTheory.CompanionTheory.Ar

open GlobalTheory.CompanionTheory.Ar.HTLift in

theorem htLat_exists_lifts : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] [CharZero Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X), IsCptGen ξ → Flat.NormalCpt ξ → ∀ (G : Over X) [GrpObj G], IsSemiAbelian G → ∀ (L : LB G.left) (n : ℕ), 1 ≤ n → FullTorsion G ξ n → ∀ e, GenWeil G L ξ n e → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (q : Cpt ξ), (∃ U : X.Opens, q.1 ∈ U ∧ ∃ w : (Over.mk ξ ⟶ G) → Module.Dual Ω E, ∀ y, y ^ n = 1 → ∀ q' : Cpt ξ, q'.1 ∈ U → M.IsHTAt L n y q' (w y)) ∧ ∀ (y : Over.mk ξ ⟶ G) (w w' : Module.Dual Ω E), y ^ n = 1 → M.IsHTAt L n y q w → (M.IsHTAt L n y q w' ↔ ∃ u ∈ M.omLat q, w' = w + n • u) := by
  intro X _ Ω _ _ ξ hg hN G _ hS L n hn hF e hW E _ _ M q
  refine ⟨?_, fun y w w' hy hw => GlobalTheory.T.hodge_tate_weil_unique X Ω ξ hg hN G hS L n hn hF e hW E M y q w w' hy hw⟩
  obtain ⟨R, _, _, x, κ, hR, hI, hO, hq, -, hx⟩ := GlobalTheory.T.normal_affine_chart_exists X Ω ξ hg hN q
  have hc : IsCommMonObj G := hS.comm
  subst hx
  have key : ∀ y : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G, y ^ n = 1 →
      ∃ w : Module.Dual Ω E, ∀ q' : Cpt (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x),
        q'.1 ∈ Set.range x → M.IsHTAt L n y q' w := by
    intro y hy
    have hfin : Finite (Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n) := by
      have := hW.finite
      exact Finite.of_injective
        (fun t => (⟨t.1, tors_pow t⟩ : {z : Over.mk (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) ⟶ G // z ^ n = 1}))
        (fun s t h => Subtype.ext (congrArg Subtype.val h))
    obtain ⟨Γ, i, hi, ht⟩ := exists_tors G hS κ x hn hF
    let c : Tors G (spMap (κ.toRingHom.comp (algebraMap R _)) ≫ x) n →* Ωˣ :=
      MonoidHom.mk' (fun t => e y t.1) (fun s t => hW.mul_right y s.1 t.1 hy (tors_pow s) (tors_pow t))
    have hc1 : ∀ t, c t ^ n = 1 := by
      intro t
      rw [← map_pow]
      have : t ^ n = 1 := Subtype.ext (tors_pow t)
      rw [this, map_one]
    obtain ⟨χ, hχ⟩ := exists_char_units κ hn c hc1
    obtain ⟨L₀, _, _, M₀, j, w₀, w, hj, hH, hw⟩ := exists_form G hS.smooth κ x M Γ i hi χ
    refine ⟨w, fun q' hq' => GlobalTheory.T.hodge_tate_weil_open_chart X Ω _ hg hN G hS L n hn hF e hW E M R x κ rfl _ Γ i hi L₀ M₀ j hj y χ
      w₀ w hy ?_ hH hw q' hq'⟩
    intro t g h
    rw [ht t g h]
    exact hχ t
  choose! w hw using key
  exact ⟨x.opensRange, hq, w, fun y hy q' hq' => hw y hy q' hq'⟩

end GlobalTheory.CompanionTheory.Ar
