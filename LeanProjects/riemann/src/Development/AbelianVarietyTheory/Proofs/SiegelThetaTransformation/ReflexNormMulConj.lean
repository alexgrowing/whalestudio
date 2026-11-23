import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ThetaSpanAdjoint
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MultAddMultConjugate
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.NeBotOfNorm
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.DetIdealSelfDualLatticeAndInterStandardStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict GlobalTheory.Phase GlobalTheory.IndefiniteRowSideFullHecke.UnitaryAdjointCongruence

noncomputable section

namespace GlobalTheory.BetaChange

open GlobalTheory.IndefiniteRowSideFullHecke.ReflexNormIndexIdeal GlobalTheory.LatticeBetaCompare GlobalTheory.SW.Nbr
open scoped nonZeroDivisors

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem form_adj (h : Matrix (Fin n) (Fin n) E) (v w : Fin n → E) :
    ∑ j, IsCMField.complexConj E (v j) * h.mulVec w j =
      ∑ j, IsCMField.complexConj E ((adjM h).mulVec v j) * w j := by
  simp only [Matrix.mulVec, dotProduct, adjM, Matrix.of_apply, map_sum, map_mul,
    IsCMField.complexConj_apply_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem unimod_act {h : Matrix (Fin n) (Fin n) E} (hu : IsUnitaryM h) {Λ : GenLat E n} (hΛ : Λ.Unimod) :
    (actLat h Λ).Unimod := by
  have h1 : adjM h * h = 1 := hu
  have h2 : h * adjM h = 1 := mul_eq_one_comm.1 h1
  intro v
  have e : v ∈ (actLat h Λ).La ↔ (adjM h).mulVec v ∈ Λ.La := by
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (adjM h).mulVec (h.mulVec u) ∈ _
      rwa [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
    · intro hv
      refine ⟨_, hv, ?_⟩
      change h.mulVec _ = _
      rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  rw [e, hΛ]
  constructor
  · rintro hv _ ⟨u, hu, rfl⟩
    exact (form_adj h v u).symm ▸ hv u hu
  · intro hv w hw
    rw [← form_adj]
    exact hv _ ⟨w, hw, rfl⟩

variable {H : Host E} (Dw : Datum H) {l : Geo.Tor.Level H} (c : Coeff l)

theorem reflexNorm_mul_conj (g : 𝓞 E) :
    reflexNorm Dw c ((g * co g : 𝓞 E) : E) = ((Ideal.absNorm (Ideal.span {g}) ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  have h := (isBe_principal Dw c g).2 c.F.val.toRingHom
  apply c.F.val.toRingHom.injective
  rw [map_natCast]
  have e : c.F.val.toRingHom (reflexNorm Dw c ((g * co g : 𝓞 E) : E)) =
      c.F.val.toRingHom (reflexNorm Dw c (g : E)) * conj (c.F.val.toRingHom (reflexNorm Dw c (g : E))) := by
    simp only [reflexNorm, map_prod, map_pow, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_congr rfl fun σ _ => ?_
    congr 1
    change σ ((g : E) * IsCMField.complexConj E (g : E)) = σ g * conj (σ g)
    rw [map_mul, IsCMField.complexEmbedding_complexConj]
  rw [e, Complex.mul_conj', ← Complex.ofReal_pow, h]
  push_cast
  rfl

theorem isBe_mul_conj (J : Ideal (𝓞 E)) (hJ : J ≠ ⊥) :
    IsBe Dw c (J * conjI J) ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) := by
  let I₀ : (Ideal (𝓞 E))⁰ := ⟨J, mem_nonZeroDivisors_of_ne_zero hJ⟩
  obtain ⟨k, hk, e⟩ := (isOfFinOrder_of_finite (ClassGroup.mk0 I₀)).exists_pow_eq_one
  rw [← map_pow] at e
  obtain ⟨g, hg⟩ : (J ^ k).IsPrincipal := (ClassGroup.mk0_eq_one_iff (I₀ ^ k).2).1 e
  change J ^ k = Ideal.span {g} at hg
  refine isBe_of_pow hk ?_
  have e1 : (J * conjI J) ^ k = Ideal.span {g * co g} := by
    rw [mul_pow, conjI_eq, ← Ideal.map_pow, hg, Ideal.map_span, Set.image_singleton,
      Ideal.span_singleton_mul_span_singleton]
  have e2 : ((Ideal.absNorm J ^ (Dw.p + Dw.q) : ℕ) : c.F) ^ k = reflexNorm Dw c ((g * co g : 𝓞 E) : E) := by
    rw [reflexNorm_mul_conj, ← hg, map_pow, ← Nat.cast_pow, ← pow_mul, ← pow_mul, mul_comm k]
  rw [e1, e2]
  exact isBe_principal Dw c _

theorem isBe_of_isBeta {Λ : GenLat E n} (hΛ : Λ.Unimod) {b : c.F} (hb : IsBeta Dw c Λ b) {J : Ideal (𝓞 E)}
    (hN : Ideal.absNorm J = (Λ.Ln.toAddSubgroup.addSubgroupOf Λ.La.toAddSubgroup).index)
    (hJ : detSpan Λ.Ln = J • detSpan Λ.La) : IsBe Dw c J b := by
  have hu0 : IsUnit (detSpan Λ.La) :=
    isUnit_detSpan (GenusLatCompare.latEquiv.symm ⟨Λ, GenusLatCompare.isLat_of_unimod Λ hΛ⟩)
  have hu : IsUnit (∏ τ : E →+* ℂ, idealAt c Λ.La τ ^ Dw.mult τ) :=
    IsUnit.prod_iff.2 fun τ _ => by rw [idealAt_eq]; exact (hu0.map _).pow _
  obtain ⟨-, h1, h2⟩ := hb
  refine ⟨?_, fun s => by rw [hN]; exact h2 s⟩
  have e : ∀ τ, idealAt c Λ.Ln τ =
      coeI c.F (J.map (RingOfIntegers.mapRingHom (embF c τ))) * idealAt c Λ.La τ := fun τ => by
    rw [idealAt_eq, idealAt_eq, hJ, smul_eq_coeI_mul, map_mul, extend_coeI]
  rw [← span_eq_coeI_iff, coeI_reflexIdeal]
  rw [BetaIs] at h1
  simp only [e, mul_pow, Finset.prod_mul_distrib] at h1
  exact hu.mul_left_inj.1 h1

omit [IsCMField E] in
theorem map_mulLeft_eq (x : E) (M : Submodule (𝓞 E) E) :
    Submodule.map (LinearMap.mulLeft (𝓞 E) x) M = Submodule.span (𝓞 E) {x} * M := by
  ext y
  rw [Submodule.mem_span_singleton_mul]
  rfl

omit [IsCMField E] in
theorem coeI_span (u : 𝓞 E) : coeI E (Ideal.span {u}) = Submodule.span (𝓞 E) {(u : E)} :=
  IsLocalization.coeSubmodule_span_singleton E u

theorem beta_sq_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (c : Coeff l), ∀ (n : ℕ) (Λ : GenLat E n) (h : Matrix (Fin n) (Fin n) E) (b b' : c.F), Λ.Unimod → IsUnitaryM h → IsBeta Dw c Λ b → IsBeta Dw c (actLat h Λ) b' → ∃ m : ℕ, 0 < m ∧ (b ^ 2 * ((((actLat h Λ).Ln.toAddSubgroup.addSubgroupOf (actLat h Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F)) ^ m = (b' ^ 2 * ((((Λ).Ln.toAddSubgroup.addSubgroupOf (Λ).La.toAddSubgroup).index ^ (Dw.p + Dw.q) : ℕ) : c.F) * ∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) ^ m := by
  intro E _ _ _ H Dw l c n Λ h b b' hΛ hu hb hb'
  have hΛ' := unimod_act hu hΛ
  obtain ⟨J, hJ0, hN, hJ1, hJ2, hdet⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n Λ hΛ
  obtain ⟨J', hJ0', hN', hJ1', hJ2', -⟩ := GlobalTheory.T.detIdeal_selfDual_lattice_and_inter_standard E n _ hΛ'
  have hB := isBe_of_isBeta Dw c hΛ hb hN hJ1
  have hB' := isBe_of_isBeta Dw c hΛ' hb' hN' hJ1'
  obtain ⟨u, v, hv, huv⟩ := IsFractionRing.div_surjective (A := 𝓞 E) h.det
  have hv0 : v ≠ 0 := nonZeroDivisors.ne_zero hv
  have hvE : (v : E) ≠ 0 := by simpa using hv0
  have huv' : (u : E) = h.det * (v : E) := by
    rw [← huv]; exact (div_mul_cancel₀ _ hvE).symm
  have k1 : coeI E (conjI J) = coeI E J * detSpan Λ.La := by
    rw [← smul_eq_coeI_mul]; exact hJ2.symm.trans hJ1
  have k2 : coeI E (conjI J') = coeI E J' * (Submodule.span (𝓞 E) {h.det} * detSpan Λ.La) := by
    rw [← smul_eq_coeI_mul, ← map_mulLeft_eq]
    exact (hJ2'.symm.trans hJ1').trans (by rw [hdet]; rfl)
  have key : conjI J' * J * Ideal.span {v} = conjI J * J' * Ideal.span {u} := by
    apply IsFractionRing.coeSubmodule_injective (𝓞 E) E
    change coeI E _ = coeI E _
    simp only [map_mul, k1, k2, coeI_span]
    rw [huv', ← Set.singleton_mul_singleton, ← Submodule.span_mul_span]
    ring
  have a1 := isBe_mul (isBe_mul (isBe_pow hB 2) (isBe_mul_conj Dw c J' hJ0')) (isBe_principal Dw c v)
  have a2 := isBe_mul (isBe_mul (isBe_pow hB' 2) (isBe_mul_conj Dw c J hJ0)) (isBe_principal Dw c u)
  have e : J' ^ 2 * (J * conjI J) * Ideal.span {u} = J ^ 2 * (J' * conjI J') * Ideal.span {v} := by
    calc _ = J * J' * (conjI J * J' * Ideal.span {u}) := by ring
      _ = _ := by rw [← key]; ring
  rw [e] at a2
  have hc : conjI J' ≠ ⊥ := fun h0 => hJ0' (by
    rw [← conjI_conjI J', h0, conjI_eq, Ideal.map_bot])
  have hs : Ideal.span {v} ≠ (⊥ : Ideal (𝓞 E)) := by simpa using hv0
  obtain ⟨z, hz, ez⟩ := isBe_unique
    (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hJ0) (mul_ne_zero hJ0' hc)) hs) a2 a1
  obtain ⟨m, hm, hzm⟩ := hz.exists_pow_eq_one
  have hψ : reflexNorm Dw c (v : E) ≠ 0 := isBe_ne_zero hs (isBe_principal Dw c v)
  have hψu : reflexNorm Dw c (u : E) = (∏ τ : E →+* ℂ, embF c τ h.det ^ Dw.mult τ) * reflexNorm Dw c (v : E) := by
    simp only [huv', reflexNorm, map_mul, mul_pow, Finset.prod_mul_distrib]
  rw [hψu, ← _root_.mul_assoc, ← _root_.mul_assoc, hN, hN'] at ez
  have ez' := mul_right_cancel₀ hψ ez
  refine ⟨m, hm, ?_⟩
  rw [ez', _root_.mul_assoc z, mul_pow z, hzm, _root_.one_mul]

end GlobalTheory.BetaChange
