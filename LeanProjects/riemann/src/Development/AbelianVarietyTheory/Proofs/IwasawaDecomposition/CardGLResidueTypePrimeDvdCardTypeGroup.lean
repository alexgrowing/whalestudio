import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CoreEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroWild
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG

namespace GlobalTheory.ZetaSer

theorem coeffRings_contain_rootsOfUnity_of_groupOrder (D : D7) (h : RootsLL D) : GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D := by
  obtain ⟨ζ, hζ⟩ := h
  intro i
  have hpos := D.what₂.restRowsFiniteGroupCard_pos
  have hz : IsPrimitiveRoot (D.nd.embK i ζ) D.what₂.restRowsFiniteGroupCard := hζ.map_of_injective (D.nd.embK i).injective
  have hint : IsIntegral (D.nd.O i) (D.nd.embK i ζ) := ⟨Polynomial.X ^ D.what₂.restRowsFiniteGroupCard - Polynomial.C 1,
    Polynomial.monic_X_pow_sub_C 1 hpos.ne', by simp [hz.pow_eq_one]⟩
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨y, ?_⟩
  rw [← hy] at hz
  exact hz.of_map_of_injective (IsFractionRing.injective _ _)

theorem trace_mem_fieldRange {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n) {ζ : L} (hζ : IsPrimitiveRoot ζ n)
    (f : Module.End ℂ V) (hf : f ^ n = 1) : LinearMap.trace ℂ V f ∈ e.fieldRange := by
  classical
  let b := Module.finBasis ℂ V
  rw [LinearMap.trace_eq_matrix_trace ℂ b, Matrix.trace_eq_sum_roots_charpoly]
  refine multiset_sum_mem _ fun μ hμ => ?_
  have hroot : (LinearMap.charpoly f).IsRoot μ := by
    rw [← LinearMap.charpoly_toMatrix f b]
    exact (Polynomial.mem_roots'.mp hμ).2
  obtain ⟨v, hv⟩ := ((Module.End.hasEigenvalue_iff_isRoot_charpoly f μ).2 hroot).exists_hasEigenvector
  have hpow : μ ^ n = 1 := by
    have h1 := hv.pow_apply n
    rw [hf, Module.End.one_apply] at h1
    have h2 : (μ ^ n - 1) • v = 0 := by rw [sub_smul, one_smul, ← h1, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp h2).resolve_right hv.2)
  have hζc := hζ.map_of_injective e.injective
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨j, -, hj⟩ := hζc.eq_pow_of_pow_eq_one hpow
  exact ⟨ζ ^ j, by rw [map_pow, hj]⟩

end GlobalTheory.ZetaSer

namespace GlobalTheory.ZetaSer

theorem card_GL_residue_typePrime_dvd_card_typeGroup (D : D7) (k : Fin 2) :
    Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) ∣ D.what₂.restRowsFiniteGroupCard := by
  rw [D.nd.restN_card_levelGroup_eq]
  have hf : D.R.f ≠ 0 := by
    unfold Formalism.BasicNotions.Ranks.f Formalism.BasicNotions.Ranks.n
    positivity
  exact (dvd_pow_self _ hf).trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ k))

theorem coeff_zIdem_mem {Γ : Type} [Group Γ] [Fintype Γ] {L : Type} [Field L] (e : L →+* ℂ) {n : ℕ} (hn : 0 < n)
    {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hΓ : Nat.card Γ ∣ n) (τ : FDRep ℂ Γ) (γ : Γ) :
    (Formalism.IrreducibleCountingLemmas.TYPES.zIdem τ).coeff γ ∈ e.fieldRange := by
  rw [Formalism.IrreducibleCountingLemmas.TYPES.zIdem_coeff]
  refine mul_mem (div_mem (natCast_mem _ _) (natCast_mem _ _)) (trace_mem_fieldRange e hn hζ _ ?_)
  obtain ⟨c, hc⟩ := hΓ
  rw [← map_pow, hc, pow_mul, pow_card_eq_one', one_pow, map_one]

theorem serLL_of_rootsLL (D : D7) (h : RootsLL D) (G : GrpSide D) : GlobalTheory.PendOf.SerLL D := by
  obtain ⟨ζ, hζ⟩ := h
  intro k f γ
  apply RingHom.mem_fieldRange.mp
  rw [G.eSer_def k f]
  unfold eSerO
  refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun z => ?_
  · simp
  · intro x y hx hy
    simpa using add_mem hx hy
  · refine finsum_induction (fun x : MonoidAlgebra ℂ (GL (Fin D.R.r) (ZMod (D.host.g k))) => x.coeff γ ∈ D.what₂.embLL.fieldRange) ?_ ?_ fun hz => ?_
    · simp
    · intro x y hx hy
      simpa using add_mem hx hy
    · obtain ⟨τ, -, rfl, -⟩ := hz
      exact coeff_zIdem_mem _ D.what₂.restRowsFiniteGroupCard_pos hζ (card_GL_residue_typePrime_dvd_card_typeGroup D k) τ γ

theorem rootsOfUnity_and_seriesIdempotent_rational : ∀ D : D7, RootsLL D → GlobalTheory.PendOf.CoeffRingsHaveRootsOfUnity D ∧ (GrpSide D → GlobalTheory.PendOf.SerLL D) :=
  fun D h => ⟨coeffRings_contain_rootsOfUnity_of_groupOrder D h, serLL_of_rootsLL D h⟩

end GlobalTheory.ZetaSer
