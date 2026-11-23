import Mathlib
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.CellAbs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.BochnerTheorem.RMKComplex

noncomputable section

open MeasureTheory Topology
open scoped ComplexOrder ComplexConjugate

namespace GlobalTheory.CompanionTheory.RswCell

open PositivityTheory.Rg.Rsw.Cell

variable {G : Type} [Group G] [TopologicalSpace G]

def secOf (P : Subgroup G) (h : G → ℝ) (F : G ⧸ P → ℂ) (g : G) : ℂ :=
  F (QuotientGroup.mk g⁻¹) * (h g : ℂ)

theorem mk_inv_mul {P : Subgroup G} {p : G} (hp : p ∈ P) (g : G) :
    (QuotientGroup.mk (p * g)⁻¹ : G ⧸ P) = QuotientGroup.mk g⁻¹ := by
  rw [mul_inv_rev]
  exact QuotientGroup.mk_mul_of_mem _ (P.inv_mem hp)

theorem div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hpos : ∀ g, 0 < h g) (hf : Sec P h f) (g : G) :
    f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) =
      f g / (h g : ℂ) := by
  obtain ⟨p, hp⟩ := QuotientGroup.mk_out_eq_mul P g⁻¹
  have hr : rp (QuotientGroup.mk g⁻¹ : G ⧸ P) = (p : G)⁻¹ * g := by
    show (Quotient.out (QuotientGroup.mk g⁻¹ : G ⧸ P))⁻¹ = _
    rw [hp, mul_inv_rev, inv_inv]
  rw [hr]
  have key := hf.2 (p : G)⁻¹ (P.inv_mem p.2) g
  have h1 : (h ((p : G)⁻¹ * g) : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (hpos _).ne'
  rw [div_eq_div_iff h1 h2]
  exact key

variable [IsTopologicalGroup G]

theorem secOf_sec {P : Subgroup G} {h : G → ℝ} (hc : Continuous h) {F : G ⧸ P → ℂ}
    (hF : Continuous F) : Sec P h (secOf P h F) := by
  refine ⟨?_, fun p hp g => ?_⟩
  · unfold secOf
    exact (hF.comp (QuotientGroup.continuous_mk.comp continuous_inv)).mul
      (Complex.continuous_ofReal.comp hc)
  · unfold secOf
    rw [mk_inv_mul hp g]
    ring

theorem compact_quot {P : Subgroup G}
    (hco : ∃ C : Set G, IsCompact C ∧ ∀ g, ∃ q ∈ P, ∃ c ∈ C, g = q * c) : CompactSpace (G ⧸ P) := by
  obtain ⟨C, hC, hcov⟩ := hco
  have huniv : (Set.univ : Set (G ⧸ P)) = (fun c => (QuotientGroup.mk c⁻¹ : G ⧸ P)) '' C := by
    ext x
    simp only [Set.mem_univ, Set.mem_image, true_iff]
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q, hq, c, hc, hac⟩ := hcov a⁻¹
    refine ⟨c, hc, ?_⟩
    have ha : a = c⁻¹ * q⁻¹ := by rw [← mul_inv_rev, ← hac, inv_inv]
    rw [ha, QuotientGroup.mk_mul_of_mem _ (P.inv_mem hq)]
  refine ⟨?_⟩
  rw [huniv]
  exact hC.image (QuotientGroup.continuous_mk.comp continuous_inv)

theorem continuous_div_rp {P : Subgroup G} {h : G → ℝ} {f : G → ℂ} (hc : Continuous h)
    (hpos : ∀ g, 0 < h g) (hf : Sec P h f) :
    Continuous fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ) := by
  rw [(QuotientGroup.isQuotientMap_mk P).continuous_iff]
  have hcomp : ((fun q : G ⧸ P => f (rp q) / (h (rp q) : ℂ)) ∘ QuotientGroup.mk) =
      fun a => f a⁻¹ / (h a⁻¹ : ℂ) := by
    funext a
    have := div_rp hpos hf a⁻¹
    rw [inv_inv] at this
    exact this
  rw [hcomp]
  exact (hf.1.comp continuous_inv).div (Complex.continuous_ofReal.comp (hc.comp continuous_inv))
    fun a => by exact_mod_cast (hpos _).ne'

theorem exists_repr [T2Space G] (P : Subgroup G) [MeasurableSpace (G ⧸ P)] [BorelSpace (G ⧸ P)]
    (h : G → ℝ) (mu : (G → ℂ) → ℂ) (S : Setup P h mu) : ∃ ν, Repr P h mu ν := by
  haveI : CompactSpace (G ⧸ P) := compact_quot S.cocpt
  haveI : IsClosed (P : Set G) := S.closed
  let Λ : C(G ⧸ P, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun F => mu (secOf P h F)
      map_add' := fun F F' => by
        have he : secOf P h ⇑(F + F') = secOf P h F + secOf P h F' := by
          funext g
          simp only [secOf, ContinuousMap.add_apply, Pi.add_apply]
          ring
        rw [he]
        exact S.add _ _ (secOf_sec S.cont F.continuous) (secOf_sec S.cont F'.continuous)
      map_smul' := fun c F => by
        have he : secOf P h ⇑(c • F) = c • secOf P h F := by
          funext g
          simp only [secOf, ContinuousMap.smul_apply, Pi.smul_apply, smul_eq_mul]
          ring
        rw [he]
        exact S.smul c _ (secOf_sec S.cont F.continuous) }
  have hpos : ∀ F : C(G ⧸ P, ℂ), 0 ≤ Λ (star F * F) := by
    intro F
    have hval : ∀ g, secOf P h ⇑(star F * F) g =
        ((Complex.normSq (F (QuotientGroup.mk g⁻¹)) * h g : ℝ) : ℂ) := by
      intro g
      simp only [secOf, ContinuousMap.mul_apply, ContinuousMap.star_apply]
      push_cast
      rw [Complex.normSq_eq_conj_mul_self]
      rfl
    have hnn := S.nonneg (secOf P h ⇑(star F * F)) (secOf_sec S.cont (star F * F).continuous)
      (fun g => by
        rw [hval g, Complex.ofReal_re, Complex.ofReal_im]
        exact ⟨mul_nonneg (Complex.normSq_nonneg _) (S.pos g).le, rfl⟩)
    exact Complex.nonneg_iff.2 ⟨hnn.1, hnn.2.symm⟩
  obtain ⟨ν, hfin, hrep⟩ := PI.Bochner.exists_measure_of_positive Λ hpos
  refine ⟨ν, hfin, fun f hf => ?_⟩
  let Fc : C(G ⧸ P, ℂ) := ⟨fun q => f (rp q) / (h (rp q) : ℂ), continuous_div_rp S.cont S.pos hf⟩
  have hsec : secOf P h ⇑Fc = f := by
    funext g
    show f (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) / (h (rp (QuotientGroup.mk g⁻¹ : G ⧸ P)) : ℂ) * (h g : ℂ) = f g
    rw [div_rp S.pos hf g]
    have h2 : (h g : ℂ) ≠ 0 := by exact_mod_cast (S.pos g).ne'
    field_simp
  refine ⟨?_, ?_⟩
  · exact Fc.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  · calc mu f = Λ Fc := by
          show mu f = mu (secOf P h ⇑Fc)
          rw [hsec]
      _ = ∫ q, Fc q ∂ν := hrep Fc

theorem riesz : Riesz := by
  intro G _ _ _ _ _ _ P _ _ h mu S
  exact exists_repr P h mu S

end GlobalTheory.CompanionTheory.RswCell
