import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NormMulLeOfIrreducible
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.AddHomExtSingle
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisTestLattice
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorsionValuesCoordsOperatorPermute
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPosIsGreatestNormMulVecOnKer
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqZeroOfPoints
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WeightSpaceIrreducibleResidue
import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

namespace GlobalTheory.ZH

open TestSpan in

theorem testLattice_eq_span_sections : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (l : u.Lab) (τ : S.Test p y₀) (σ : S.J → (u.H S.N).Sec) (cls : S.J → u.D.toPre.X) (md : Mod p u.j u.G S.g S.N l.q (u.H S.N) σ cls) (b : Matrix S.J S.J (FractionRing u.V)), S.Big → (∀ a : o, ‖y₀ (algebraMap o S.R a)‖ ≤ 1) → l.Match τ → u.Link σ b → b.det ≠ 0 → ∃ c : FractionRing u.V, c ≠ 0 ∧ τ.E = Submodule.span (OO p) (Set.range ((c • b).map (algebraMap _ (PadicAlgCl p)))) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u l τ σ cls md b hbig hint hmt hlink hdet
  obtain ⟨κ, hκ, hfr⟩ := FrameNorm.exists_pos_isGreatest_norm_mulVec_on_ker hLL o Ω S ρ p y₀ u l σ cls md b hbig hint hlink
  have hΛ := LatChar.mem_lattice_iff hLL o Ω S ρ p y₀ u l σ cls md b κ hbig hint hlink hdet hκ hfr
  let φ : o →+* OO p := (y₀.comp (algebraMap o S.R)).codRestrict (OO p) fun a => (mem_OO_iff _).2 (hint a)
  have hE := E_eq_bdd τ φ (fun _ => rfl) (EvCrd.ev_crd_act hLL o Ω S ρ).2
    (GlobalTheory.weightSpace_irreducible_residue hLL o Ω S ρ p φ _ τ.isoFree)
  have hker : ∀ a, a ∈ l.yy.ker ↔ a ∈ τ.yy.ker := fun a => by
    obtain ⟨e, -, he⟩ := hmt
    have h1 := he a 0
    rw [map_zero] at h1
    exact h1.symm
  obtain ⟨x, hx⟩ := τ.δ_max.1
  obtain ⟨i, hi⟩ := (hfr 0 (zero_mem _)).1
  let em := algebraMap (FractionRing u.V) (PadicAlgCl p)
  have hy : ∀ a, y₀ a = em (u.yK a) := fun a => (DFunLike.congr_fun u.fac a).symm
  let d : FractionRing u.V := u.yK ⟨S.th x, S.th_mem x⟩
  let k : FractionRing u.V := b.mulVec (fun i => u.yK ⟨S.ev 0 i, S.ev_mem 0 i⟩) i
  have hd : ‖em d‖ = τ.δ := (congrArg norm (hy _)).symm.trans hx
  have hk : ‖em k‖ = κ := by
    refine Eq.trans ?_ hi
    simp only [hy]
    exact congrArg norm (congrFun (map_mulVec' em b _) i).symm
  have hc : ‖em (d / k)‖ = τ.δ / κ := by rw [map_div₀, norm_div, hd, hk]
  have hc0 : em (d / k) ≠ 0 := norm_pos_iff.1 (hc ▸ div_pos τ.δ_pos hκ)
  refine ⟨d / k, fun h => hc0 (by rw [h, map_zero]), ?_⟩
  generalize d / k = c at hc hc0
  let m : (S.J → PadicAlgCl p) →ₗ[OO p] (S.J → PadicAlgCl p) :=
    (LinearMap.lsmul (PadicAlgCl p) (S.J → PadicAlgCl p) (em c)).restrictScalars (OO p)
  have hm : ∀ e, m e = em c • e := fun _ => rfl
  have hr : Set.range ((c • b).map em) = m '' Set.range (b.map em) := by
    have h1 : ∀ i, (c • b).map em i = m (b.map em i) := fun i => by
      rw [hm]
      funext j
      simp only [Matrix.map_apply, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, map_mul]
    ext w
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (h1 i).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, h1 i⟩
  clear_value m
  rw [hE]
  refine Eq.trans ?_ (congrArg (Submodule.span (OO p)) hr).symm
  rw [Submodule.span_image]
  ext e
  constructor
  · intro he
    refine ⟨(em c)⁻¹ • e, (hΛ _).2 fun a ha => ?_, by rw [hm, smul_inv_smul₀ hc0]⟩
    rw [smul_dotProduct, smul_eq_mul, norm_mul, norm_inv, hc, inv_div, div_mul_eq_mul_div, div_le_iff₀ τ.δ_pos]
    exact mul_le_mul_of_nonneg_left (he a ((hker a).1 ha)) hκ.le
  · rintro ⟨e, he, rfl⟩ a ha
    rw [hm, smul_dotProduct, smul_eq_mul, norm_mul, hc, div_mul_eq_mul_div, div_le_iff₀ hκ]
    exact mul_le_mul_of_nonneg_left ((hΛ _).1 he a ((hker a).2 ha)) τ.δ_pos.le

end GlobalTheory.ZH
