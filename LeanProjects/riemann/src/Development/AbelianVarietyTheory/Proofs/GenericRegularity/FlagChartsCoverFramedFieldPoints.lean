import Mathlib
import Development.AbelianVarietyTheory.Definitions.RegularCharts.Reframe
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import Formalism.LocalToGlobal.ProjectiveLattices.FrameCharts
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsFlagCellChartOverFramedAffineOpenStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralSmoothChartFrameModuliStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsTriangularReframeExistsAndUniqueStatement
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsIntegralPivotDecomposition

noncomputable section

namespace GlobalTheory.Reg

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Reg

theorem exists_perm_lower_upper {L : Type} [Field L] {n : ℕ} (g : Matrix (Fin n) (Fin n) L) (hg : IsUnit g.det) :
    ∃ (σ : Equiv.Perm (Fin n)) (u b : Matrix (Fin n) (Fin n) L),
      (∀ i j : Fin n, i < j → u (σ i) j = 0) ∧ (∀ i, u (σ i) i = 1) ∧
      (b.BlockTriangular id ∧ ∀ i, b i i ≠ 0) ∧ g = u * b := by
  have hli : LinearIndependent L g.transpose :=
    Matrix.linearIndependent_cols_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det g).mpr hg)
  obtain ⟨m, u, b, -, h0, h1, hb, hd, e⟩ := GlobalTheory.exists_integral_pivot_decomposition L ⊤ n n g hli
  exact ⟨Equiv.ofBijective m (Finite.injective_iff_bijective.mp m.injective), u, b, h0, h1, ⟨hb, hd⟩, e⟩

theorem exists_algHom_of_mem_range {K A L : Type} [Field K] [CommRing A] [Algebra K A] [Field L] [Algebra K L]
    {X : Scheme.{0}} (s : X ⟶ Sp K) (j : Sp A ⟶ X) [IsOpenImmersion j] (hj : j ≫ s = spMap (algebraMap K A))
    (q : Sp L ⟶ X) (hq : q ≫ s = spMap (algebraMap K L))
    (hp : q (IsLocalRing.closedPoint L) ∈ Set.range j) :
    ∃ f : A →ₐ[K] L, spMap f.toRingHom ≫ j = q := by
  have hr : Set.range q ⊆ Set.range j := by
    rintro _ ⟨a, rfl⟩
    have : a = IsLocalRing.closedPoint L := Subsingleton.elim (α := PrimeSpectrum L) _ _
    rw [this]
    exact hp
  let φ : CommRingCat.of A ⟶ CommRingCat.of L := Spec.preimage (IsOpenImmersion.lift j q hr)
  have hφ : Spec.map φ ≫ j = q := by
    rw [Spec.map_preimage, IsOpenImmersion.lift_fac]
  have hc : CommRingCat.ofHom (algebraMap K A) ≫ φ = CommRingCat.ofHom (algebraMap K L) := by
    apply Spec.map_injective
    rw [Spec.map_comp]
    show Spec.map φ ≫ spMap (algebraMap K A) = spMap (algebraMap K L)
    rw [← hj, ← Category.assoc, hφ, hq]
  exact ⟨{ φ.hom with commutes' := fun a => congrArg (fun t => t.hom a) hc }, hφ⟩

theorem atlas : ReciprocityTheory.ChartRestriction.G.Out.SecTwistSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l), FrBC Xo c → ∀ h : GenFrEx Xo c, Atlas h := by
  intro hS E _ _ _ H Dw l Xo c hBC h L _ _ y
  have hcond : y.x ≫ Xo.s =
      spMap (algebraMap c.F L) ≫ spMap (IntermediateField.inclusion c.le).toRingHom := by
    rw [y.x_over, spMap_comp_ring]
    rfl
  let q : Sp L ⟶ Xo.XF c := pullback.lift y.x (spMap (algebraMap c.F L)) hcond
  obtain ⟨A, _, _, _, j, yA, hj, hp, hjs, hsm, hyA⟩ :=
    GlobalTheory.T.exists_integral_smooth_chart_frame_moduli hS E H Dw l Xo c (q (IsLocalRing.closedPoint L))
  obtain ⟨f, hf⟩ := exists_algHom_of_mem_range (pullback.snd _ _) j hjs q (pullback.lift_snd _ _ _) hp
  obtain ⟨z₀, hz₀⟩ := hBC A L f yA
  have hx : y.x = z₀.x := by
    rw [hz₀.1, hyA, ← Category.assoc, hf]
    exact (pullback.lift_fst _ _ _).symm
  obtain ⟨g, ⟨hgu, hg⟩, -⟩ := (GlobalTheory.T.isTriangularReframe_exists_and_unique E H Dw l Xo c L z₀).2 y hx
  choose σ u b h0 h1 hb e using fun τ => exists_perm_lower_upper (g τ) (hgu τ)
  obtain ⟨C, hC⟩ := GlobalTheory.T.exists_flagCellChart_over_framedAffineOpen E H Dw l Xo c hBC h A j yA hj hjs hsm hyA σ
  let x : FlagVar Dw → L := fun v => u v.1 (σ v.1 v.2.1.2) v.2.1.1
  have hu : ∀ τ, (lowM x τ).submatrix (σ τ).symm id = u τ := by
    intro τ
    ext i k
    obtain ⟨i, rfl⟩ := (σ τ).surjective i
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply, id, lowM]
    split_ifs with h₁ h₂
    · rfl
    · rw [h₂, h1]
    · exact (h0 τ i k (lt_of_le_of_ne (not_lt.mp h₁) (Ne.symm h₂))).symm
  refine ⟨C, hC L f z₀ y x b hz₀ hb ?_⟩
  have : (fun τ => (lowM x τ).submatrix (σ τ).symm id * b τ) = g := funext fun τ => by rw [hu τ, ← e τ]
  rw [this]
  exact hg

end GlobalTheory.Reg
