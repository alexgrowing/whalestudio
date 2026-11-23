import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NormalFam
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.LocalToGlobal.Divisibility.ProjLemmas

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem conv_map_idem {K : Type} [Field K] {H : Type} [Group H] [Fintype H] (z : MonoidAlgebra K H) (hz : z * z = z)
    (σ : K →+* ℂ) (g : H) : ∑ a, σ (z.coeff a) * σ (z.coeff (a⁻¹ * g)) = σ (z.coeff g) := by
  conv_rhs => rw [← hz]
  rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype _ _ (by simp), map_sum]
  simp [map_mul]

theorem coeff_conj_central {K : Type} [Field K] {H : Type} [Group H] (z : MonoidAlgebra K H)
    (hz : ∀ b, b * z = z * b) (g h : H) : z.coeff (g * h * g⁻¹) = z.coeff h := by
  have e := congrArg (fun y : MonoidAlgebra K H => y.coeff (g * h)) (hz (MonoidAlgebra.single g 1))
  simpa [mul_assoc] using e.symm

theorem sum_rep_idem {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g, ∑ a, c a * c (a⁻¹ * g) = c g) :
    (∑ g, c g • ρ g) * (∑ g, c g • ρ g) = ∑ g, c g • ρ g := by
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum, smul_mul_smul_comm, ← map_mul]
  calc ∑ a, ∑ b, (c a * c b) • ρ (a * b) = ∑ a, ∑ g, (c a * c (a⁻¹ * g)) • ρ g := by
        refine Finset.sum_congr rfl fun a _ => ?_
        exact Fintype.sum_equiv (Equiv.mulLeft a) _ _ fun b => by simp
    _ = ∑ g, (∑ a, c a * c (a⁻¹ * g)) • ρ g := by
        rw [Finset.sum_comm]; simp_rw [Finset.sum_smul]
    _ = ∑ g, c g • ρ g := by simp_rw [hc]

theorem sum_rep_comm {H : Type} [Group H] [Fintype H] {Y : Type} [AddCommGroup Y] [Module ℂ Y]
    (ρ : Representation ℂ H Y) (c : H → ℂ) (hc : ∀ g h, c (g * h * g⁻¹) = c h) (g : H) :
    Commute (∑ h, c h • ρ h) (ρ g) := by
  unfold Commute SemiconjBy
  rw [Finset.sum_mul, Finset.mul_sum]
  simp_rw [smul_mul_assoc, mul_smul_comm, ← map_mul]
  symm
  refine Fintype.sum_equiv (MulAut.conj g).toEquiv _ _ fun h => ?_
  simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulAut.conj_apply, hc]
  congr 2
  group

theorem eH_laws : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), Core R F → (∀ χ ∈ A.X, IsAbsIrrChar χ) → ∀ i, eH R i * eH R i = eH R i ∧ (∀ g, Commute (eH R i) (R.gW i (sg0 D A) g)) ∧ (∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv) ∧ ∀ t y, eH R i (R.thG i t y) = R.thG i t y := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hC hX i
  have hc : ∀ g, ∑ a, RealDat.eC (A := A) (sg0 D A) a * RealDat.eC (A := A) (sg0 D A) (a⁻¹ * g) =
      RealDat.eC (A := A) (sg0 D A) g := fun g => conv_map_idem _ (idemOf_mul_self A.X hX) (sg0 D A) g
  have hcc : ∀ g h, RealDat.eC (A := A) (sg0 D A) (g * h * g⁻¹) = RealDat.eC (A := A) (sg0 D A) h := fun g h => by
    unfold RealDat.eC
    rw [coeff_conj_central _ (fun b => idemOf_central A.X hX b) g h]
  have happ : ∀ x v, (R.HW i (sg0 D A)).e (eH R i x) v = R.eWf i (sg0 D A) ((R.HW i (sg0 D A)).e x v) := fun x v => by
    unfold eH RealDat.eWf gaL
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, MultilinearMap.sum_apply,
      MultilinearMap.smul_apply]
    refine Finset.sum_congr rfl fun g _ => congrArg _ ?_
    rw [hC.models.gW i (sg0 D A) g x]; rfl
  have hinj := (hC.models.HW i (sg0 D A)).1
  have hrange := (hC.models.HW i (sg0 D A)).2.1
  have hfix : ∀ x, eH R i x = x ↔ (R.HW i _).e x ∈ R.Wat i (sg0 D A) R.triv := fun x => by
    rw [RealDat.Wat, mem_goodPart]
    constructor
    · intro h
      refine ⟨?_, fun v => ?_⟩
      · have : (R.HW i (sg0 D A)).e x ∈ R.Wall i (sg0 D A) := hrange ▸ LinearMap.mem_range_self _ x
        exact this
      · rw [← happ, h]
    · rintro ⟨_, h⟩
      apply hinj
      refine MultilinearMap.ext fun v => ?_
      rw [happ, h]
  have hI : eH R i * eH R i = eH R i := sum_rep_idem _ _ hc
  refine ⟨hI, fun g => sum_rep_comm _ _ hcc g, hfix, fun t y => ?_⟩
  have hm := hC.thP.thF_mem i t y
  rw [← hrange] at hm
  obtain ⟨x0, hx0⟩ := hm
  have e1 : R.thG i t y = eH R i x0 := by
    apply hinj
    rw [hC.thP.thG i t y, ← hx0]
    refine MultilinearMap.ext fun v => ?_
    rw [happ]
    exact (postOn_apply _ _ _ _).symm
  rw [e1, ← Module.End.mul_apply, hI]

end GlobalTheory.Hk3
