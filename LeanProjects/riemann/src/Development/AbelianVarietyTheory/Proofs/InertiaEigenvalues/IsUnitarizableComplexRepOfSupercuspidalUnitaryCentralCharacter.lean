import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SubsingletonJacquetOfPerm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsIrreducibleIffOfLinearEquiv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InSupportOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnitaryAdmissibleMatrixCoefficient
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Topology

noncomputable section

namespace GlobalTheory.SupercuspUnitary

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def scal (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) : Subgroup G where
  carrier := {h | ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ y, l (ρ h y) = c * l y}
  mul_mem' := by
    rintro a b ⟨c, hc, ha⟩ ⟨d, hd, hb⟩
    refine ⟨c * d, by rw [norm_mul, hc, hd, one_mul], fun y => ?_⟩
    rw [map_mul, Module.End.mul_apply, ha, hb, mul_assoc]
  one_mem' := ⟨1, by simp, fun y => by simp⟩
  inv_mem' := by
    rintro a ⟨c, hc, ha⟩
    have hc0 : c ≠ 0 := by rintro rfl; simp at hc
    refine ⟨c⁻¹, by rw [norm_inv, hc, inv_one], fun y => ?_⟩
    have h := ha (ρ a⁻¹ y)
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at h
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc0, one_mul]

def term (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) : ℂ :=
  l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))

theorem term_mul {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (v w : V) (g : G) {h : G}
    (hh : h ∈ scal ρ l) : term ρ l v w (g * h) = term ρ l v w g := by
  obtain ⟨c, hc, hl⟩ := (scal ρ l).inv_mem hh
  have h1 : c * starRingEnd ℂ c = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hc]; simp
  simp only [term, mul_inv_rev, map_mul, Module.End.mul_apply, hl]
  linear_combination (l (ρ g⁻¹ v) * starRingEnd ℂ (l (ρ g⁻¹ w))) * h1

theorem term_inv_mul (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (x g : G) :
    term ρ l v w (x⁻¹ * g) = term ρ l (ρ x v) (ρ x w) g := by
  simp only [term, mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]

def qterm (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (q : G ⧸ scal ρ l) : ℂ :=
  term ρ l v w q.out

theorem qterm_mk (ρ : Representation ℂ G V) (l : Module.Dual ℂ V) (v w : V) (g : G) :
    qterm ρ l v w (g : G ⧸ scal ρ l) = term ρ l v w g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (scal ρ l) g
  rw [qterm, hh, term_mul v w g h.2]

theorem center_le_scal {ρ : Representation ℂ G V} (l : Module.Dual ℂ V)
    (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) :
    Subgroup.center G ≤ scal ρ l := fun z hz' => by
  obtain ⟨c, hc, h⟩ := hz z hz'
  exact ⟨c, hc, fun y => by rw [h, map_smul, smul_eq_mul]⟩

variable [TopologicalSpace G] [IsTopologicalGroup G]

theorem isOpen_scal {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual) :
    IsOpen (scal ρ l : Set G) := by
  refine (scal ρ l).isOpen_of_mem_nhds (g := 1) (Filter.mem_of_superset ((show IsOpen
    {g : G | ρ.dual g l = l} from hl).mem_nhds (by
      simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply])) fun g hg => ⟨1, by simp, fun y => ?_⟩)
  have h1 : (ρ.dual g l) (ρ g y) = l (ρ g y) := by rw [show ρ.dual g l = l from hg]
  rw [Representation.dual_apply] at h1
  simp only [Module.Dual.transpose_apply, LinearMap.comp_apply, ← Module.End.mul_apply, ← map_mul,
    inv_mul_cancel, map_one, Module.End.one_apply] at h1
  rw [one_mul, h1]

theorem exists_finset {ρ : Representation ℂ G V} {l : Module.Dual ℂ V} (hl : l ∈ smoothPart ρ.dual)
    (hsc : IsSupercuspidal ρ) (hz : ∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v)
    (v : V) : ∃ s : Finset (G ⧸ scal ρ l), ∀ g : G, l (ρ g⁻¹ v) ≠ 0 → (g : G ⧸ scal ρ l) ∈ s := by
  obtain ⟨C, hC, hCz⟩ := hsc.2 v l hl
  haveI := QuotientGroup.discreteTopology (isOpen_scal hl)
  have hD : ((fun c : G => ((c⁻¹ : G) : G ⧸ scal ρ l)) '' C).Finite :=
    (hC.image (by fun_prop)).finite_of_discrete
  refine ⟨hD.toFinset, fun g hg => ?_⟩
  obtain ⟨z, hz', c, hc, e⟩ := hCz g⁻¹ hg
  rw [Set.Finite.mem_toFinset]
  refine ⟨c, hc, QuotientGroup.eq.2 ?_⟩
  have h2 : (c⁻¹)⁻¹ * g = z⁻¹ := by rw [← inv_inv g, e]; group
  rw [h2]
  exact center_le_scal l hz (inv_mem hz')

end GlobalTheory.SupercuspUnitary

namespace GlobalTheory

open GlobalTheory.SupercuspUnitary in

theorem isUnitarisable_of_isSupercuspidal : ∀ (G V : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (l : Module.Dual ℂ V), l ∈ smoothPart ρ.dual →
    l ≠ 0 → ρ.IsIrreducible → IsSupercuspidal ρ →
    (∀ z ∈ Subgroup.center G, ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ v, ρ z v = c • v) → IsUnitarisable ρ := by
  intro G V _ _ _ _ _ ρ l hl hl0 hirr hsc hz
  have hfin : ∀ v w, (Function.support (qterm ρ l v w)).Finite := fun v w => by
    obtain ⟨s, hs⟩ := exists_finset hl hsc hz v
    refine s.finite_toSet.subset fun q hq => ?_
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [Function.mem_support, qterm_mk] at hq
      exact hs g (left_ne_zero_of_mul hq)

  have hadd1 : ∀ v v' w q, qterm ρ l (v + v') w q = qterm ρ l v w q + qterm ρ l v' w q := by
    intro v v' w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add, add_mul]
  have hsmul1 : ∀ (a : ℂ) v w q, qterm ρ l (a • v) w q = a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_smul, smul_eq_mul, mul_assoc]
  have hadd2 : ∀ v w w' q, qterm ρ l v (w + w') q = qterm ρ l v w q + qterm ρ l v w' q := by
    intro v w w' q
    induction q using QuotientGroup.induction_on with
    | H g => simp only [qterm_mk, term, map_add, mul_add]
  have hsmul2 : ∀ (a : ℂ) v w q, qterm ρ l v (a • w) q = starRingEnd ℂ a * qterm ρ l v w q := by
    intro a v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_smul, smul_eq_mul, map_mul]
      ring
  have hconj : ∀ v w q, qterm ρ l w v q = starRingEnd ℂ (qterm ρ l v w q) := by
    intro v w q
    induction q using QuotientGroup.induction_on with
    | H g =>
      simp only [qterm_mk, term, map_mul, Complex.conj_conj]
      ring
  have hinv : ∀ (x : G) v w q, qterm ρ l (ρ x v) (ρ x w) q = qterm ρ l v w (x⁻¹ • q) := by
    intro x v w q
    induction q using QuotientGroup.induction_on with
    | H g => rw [MulAction.Quotient.smul_mk, smul_eq_mul, qterm_mk, qterm_mk, term_inv_mul]
  let B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun v w => ∑ᶠ q, qterm ρ l v w q)
    (fun v v' w => by simp only [hadd1]; exact finsum_add_distrib (hfin v w) (hfin v' w))
    (fun a v w => by simp only [hsmul1, RingHom.id_apply, smul_eq_mul, mul_finsum])
    (fun v w w' => by simp only [hadd2]; exact finsum_add_distrib (hfin v w) (hfin v w'))
    (fun a v w => by simp only [hsmul2, smul_eq_mul, mul_finsum])
  have hB : ∀ v w, B v w = ∑ᶠ q, qterm ρ l v w q := fun v w => LinearMap.mk₂'ₛₗ_apply _ _ _
  refine ⟨B, fun v w => ?_, fun v hv => ?_, fun x v w => ?_⟩
  · rw [hB, hB, map_finsum _ (hfin v w)]
    exact finsum_congr fun q => hconj v w q
  · have hex : ∃ g : G, l (ρ g v) ≠ 0 := by
      by_contra! h0
      let U : Subrepresentation ρ :=
        { toSubmodule := ⨅ g : G, LinearMap.ker (l ∘ₗ (ρ g : V →ₗ[ℂ] V))
          apply_mem_toSubmodule := fun g y hy => by
            simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hy ⊢
            intro g'
            rw [← Module.End.mul_apply, ← map_mul]
            exact hy _ }
      haveI := hirr
      rcases eq_bot_or_eq_top U with hU | hU
      · have hvU : v ∈ U.toSubmodule := by
          simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply]
          exact h0
        rw [hU] at hvU
        exact hv ((Submodule.mem_bot ℂ).1 hvU)
      · refine hl0 (LinearMap.ext fun y => ?_)
        have hyU : y ∈ U.toSubmodule := by rw [hU]; exact Submodule.mem_top
        simp only [U, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hyU
        simpa using hyU 1
    obtain ⟨g, hg⟩ := hex
    rw [hB, finsum_eq_sum _ (hfin v v), Complex.re_sum]
    refine Finset.sum_pos' (fun q _ => ?_) ⟨((g⁻¹ : G) : G ⧸ scal ρ l), ?_, ?_⟩
    · induction q using QuotientGroup.induction_on with
      | H g' =>
        rw [qterm_mk, term, Complex.mul_conj, Complex.ofReal_re]
        exact Complex.normSq_nonneg _
    · rw [Set.Finite.mem_toFinset, Function.mem_support, qterm_mk, term, inv_inv, Complex.mul_conj]
      exact_mod_cast (Complex.normSq_pos.2 hg).ne'
    · rw [qterm_mk, term, inv_inv, Complex.mul_conj, Complex.ofReal_re]
      exact Complex.normSq_pos.2 hg
  · rw [hB, hB]
    simp only [hinv]
    exact finsum_comp_equiv (MulAction.toPerm (x⁻¹ : G) : Equiv.Perm (G ⧸ scal ρ l))

end GlobalTheory
