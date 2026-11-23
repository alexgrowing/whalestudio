import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.BridgeAd
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictAll
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ReHermitianCombinationNonpos

noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence Formalism.L2.SG.NormCut

namespace Formalism.L2.SG.Pf.BridgeRat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def hat (A : X.B.I.Gf) (y : (VS D).V) : VA X.B.I := X.B.I.fmat A⁻¹ *ᵥ incl X.B.I (X.crd y)

theorem hat_add (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y + z) = hat X A y + hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_add]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_add]

theorem hat_sub (A : X.B.I.Gf) (y z : (VS D).V) : hat X A (y - z) = hat X A y - hat X A z := by
  simp only [hat]
  rw [← Matrix.mulVec_sub]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_sub]

theorem hat_smul (A : X.B.I.Gf) (c : D.host.E) (y : (VS D).V) :
    hat X A (c • y) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm c) • hat X A y := by
  simp only [hat]
  rw [← Matrix.mulVec_smul]
  congr 1
  funext i
  simp [incl, Formalism.L2.SG.HidaSetting.HidaSetting.crd, crdOf, map_mul, smul_eq_mul]

theorem hat_sum (A : X.B.I.Gf) {ι : Type} (s : Finset ι) (f : ι → (VS D).V) :
    hat X A (∑ i ∈ s, f i) = ∑ i ∈ s, hat X A (f i) := by
  exact map_sum (AddMonoidHom.mk' (hat X A) (hat_add X A)) f s

theorem hat_ratLink (A : X.B.I.Gf) {b : X.B.I.GA} {β : (VS D).V ≃ₗ[D.host.E] (VS D).V} (h : RatLink X b β)
    (y : (VS D).V) : hat X A (β y) = X.B.I.fmat (A⁻¹ * b.2 * A) *ᵥ hat X A y := by
  obtain ⟨M, -, -, hfm, hcrd⟩ := h
  have hone : X.B.I.fmat 1 = 1 := by simp [AutInst.fmat]
  have hincl : incl X.B.I ((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F)) *ᵥ
        incl X.B.I (X.crd y) := by
    funext i
    simp [incl, Matrix.mulVec, dotProduct, map_sum, map_mul]
  simp only [hat]
  rw [hcrd y, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X, hfm,
    Matrix.mulVec_mulVec, mul_assoc _ (X.B.I.fmat A), ← Formalism.L2.SG.PoincareInHH.Cut.fmat_mul X,
    mul_inv_cancel, hone, mul_one, ← Matrix.mulVec_mulVec, hincl]

theorem hA_hat (A : X.B.I.Gf) (y z : (VS D).V) :
    hA X.B.I (hat X A y) (hat X A z) = Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm ((VS D).hT y z)) := by
  simp only [hat]
  rw [Formalism.L2.SG.PoincareInHH.Cut.hA_fmat X, Formalism.L2.SG.PoincareInHH.Cut.hA_crd X]

theorem mL_div {m : VA X.B.I} (hm : m ∈ mL X.B.I X.B.g) : ∃ x ∈ X.B.I.Lf, m = (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • x := by
  unfold mL at hm
  induction hm using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
  | add a b _ _ ha hb =>
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨x', hx', rfl⟩ := hb
    exact ⟨x + x', add_mem hx hx', (smul_add _ _ _).symm⟩
  | smul c a _ ha =>
    obtain ⟨x, hx, rfl⟩ := ha
    exact ⟨c • x, Submodule.smul_mem _ c hx, smul_comm c _ x⟩

theorem locP_of_InAt (A : X.B.I.Gf) {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf) {y : (VS D).V} (hy : InAt X.B.I X.B.g X.B.g (hat X A y))
    (P : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.E)) (hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal) :
    y ∈ (haveI := P.isPrime; Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ)) := by
  obtain ⟨c, hcop, hc⟩ := hy
  obtain ⟨x, hx, hcx⟩ := mL_div X hc
  have hgB : X.B.g = gS D := X.g_eq
  have hgE : ((gS D : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  set t : D.host.E := (c : D.host.E) / ((gS D : ℕ) : D.host.E) with ht_def
  have ht : hat X A (t • y) = x := by
    rw [hat_smul]
    have hg0 : ((X.B.g : ℕ) : X.B.I.E) ≠ 0 := by
      rw [hgB]
      exact Nat.cast_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
    have hcast : ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
        Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((X.B.g : ℕ) : X.B.I.E) := (map_natCast _ _).symm
    have hunit : IsUnit ((X.B.g : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) := by
      rw [hcast]
      exact (isUnit_iff_ne_zero.2 hg0).map _
    rw [← hunit.smul_left_cancel, ← hcx, smul_smul]
    congr 1
    rw [hcast, ← map_mul, show ((c : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) =
      Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((c : ℕ) : X.B.I.E) from (map_natCast _ _).symm]
    congr 1
    apply X.ιE.injective
    rw [map_mul, RingEquiv.apply_symm_apply, map_natCast, map_natCast, hgB, ht_def]
    field_simp
  have hty : t • y ∈ Λ := (hlat _).2 (ht ▸ hx)
  simp only [Formalism.HermitianLatticesTheory.localization₂]
  refine ⟨((c : ℕ) : 𝓞 D.host.E), ?_, ?_⟩
  · show ((c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal
    intro hcP
    have hcopZ : IsCoprime (c : ℤ) (X.B.g : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
    obtain ⟨a, b, hab⟩ := hcopZ.map (Int.castRingHom (𝓞 D.host.E))
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    refine Ideal.add_mem _ (Ideal.mul_mem_left _ _ ?_) (Ideal.mul_mem_left _ _ ?_)
    · simpa using hcP
    · rw [hgB]
      simpa using hP
  · have hsm : ∀ (o : 𝓞 D.host.E) (v : (VS D).V), o • v = (o : D.host.E) • v :=
      fun o v => (algebraMap_smul D.host.E o v).symm
    have hcy : ((c : ℕ) : 𝓞 D.host.E) • y = ((gS D : ℕ) : 𝓞 D.host.E) • (t • y) := by
      rw [hsm, hsm, smul_smul]
      congr 1
      push_cast
      rw [ht_def]
      field_simp
    rw [hcy]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hty

theorem Mo_le_Lf : Mo X.B.I X.B.g (Set.range X.e0) ≤ X.B.I.Lf := by
  refine sup_le (Submodule.span_le.2 ?_) (Submodule.span_le.2 ?_)
  · rintro _ ⟨a, rfl⟩
    exact (X.vectorsInLattice.1 a).1
  · rintro y ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx _

theorem ratFromAd (A : X.B.I.Gf) {u : D.what₂.Word} {Λ : Submodule (𝓞 D.host.E) (VS D).V}
    (hlat : ∀ y, y ∈ Λ ↔ hat X A y ∈ X.B.I.Lf)
    (hfixE : ∀ a, hat X A (X.eX a) = incl X.B.I (X.crd (X.eX a)))
    (hFC : IsFixedConv Λ (gS D) (lf D (X.Fu u))) (hTF : ∀ a, (X.Fu u).e a = X.eX a)
    {y : (VS D).V} (hy : hat X A y ∈ Mo X.B.I X.B.g (Set.range X.e0)) :
    y ∈ NgX Λ (gS D) (lf D (X.Fu u)) (lf D (X.Fu u)) := by
  have hyΛ : y ∈ Λ := (hlat y).2 (Mo_le_Lf X hy)

  obtain ⟨s, hs, m, hm, hsm⟩ := Submodule.mem_sup.1 hy
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (IntAf X.B.I.F X.B.I.E)).1 hs
  choose t c' hc' ht using fun a => PIW.AdelClassFin.dual_dense X.B.I.F X.B.I.E X.B.g
    (Nat.pos_of_ne_zero (Formalism.L2.SG.Pf.ChiNMul.gB_ne_zero X)) (c a : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (c a).2
  set r : (VS D).V := ∑ a, X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) • X.eX a with hr

  have hdiff : InAt X.B.I X.B.g X.B.g (hat X A (y - r)) := by
    have e1 : hat X A (y - r) = (∑ a, Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) •
        (X.e0 a - incl X.B.I (X.crd (X.eX a)))) +
        ((∑ a, ((X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a) + m) := by
      rw [hat_sub, ← hsm, ← hc, hr]
      simp only [hat_sum X A, hat_smul, RingEquiv.symm_apply_apply, hfixE]
      have e2 : ∀ a, (c a : IntAf X.B.I.F X.B.I.E) • X.e0 a =
          (Formalism.UG.inclE (F := X.B.I.F) (Af X.B.I.F) ((t a : 𝓞 X.B.I.E) : X.B.I.E) +
            (X.B.g : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * c' a) • X.e0 a := by
        intro a; rw [Subring.smul_def, ht a]
      simp only [e2, add_smul, Finset.sum_add_distrib, smul_sub, Finset.sum_sub_distrib]
      abel
    rw [e1]
    refine InAt_add X (InAt_sum X _ _ fun a _ => InAt_smul X (inclE_mem X.B.I ⟨t a, rfl⟩) (X.basisApprox a).1)
      (InAt_add X ⟨1, Nat.coprime_one_left _, ?_⟩ ⟨1, Nat.coprime_one_left _, by rw [Nat.cast_one, one_smul]; exact hm⟩)
    rw [Nat.cast_one, one_smul]
    refine sum_mem fun a _ => ?_
    rw [mul_smul]
    have : c' a • X.e0 a = (⟨_, hc' a⟩ : IntAf X.B.I.F X.B.I.E) • X.e0 a := rfl
    rw [this]
    exact smul_mem_mL X.B.I (Submodule.smul_mem _ _ (X.vectorsInLattice.1 a).1)
  refine Formalism.L2.SG.Pf.mem_of_forall_locP fun P => ?_
  haveI := P.isPrime
  by_cases hP : ((gS D : ℕ) : 𝓞 D.host.E) ∈ P.asIdeal
  ·
    have h1 := locP_of_InAt X A hlat hdiff P hP
    have h2 : r ∈ Formalism.HermitianLatticesTheory.localization₂ P.asIdeal (XLam Λ (lf D (X.Fu u))) := by
      obtain ⟨cc, -, hc1, hloc⟩ := hFC.1 P
      have hc1' := hc1 hP
      rw [hloc]
      rw [hr]
      refine sum_mem fun a _ => ?_
      have hmem : X.eX a ∈ Submodule.span (𝓞 D.host.E) (Set.range fun b => cc b • (lf D (X.Fu u)).fl.e b) :=
        Submodule.subset_span ⟨a, by simp [hc1' a, hTF a, lf]⟩
      have hint : X.ιE ((t a : 𝓞 X.B.I.E) : X.B.I.E) ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
        have := ((t a).2 : IsIntegral ℤ ((t a : 𝓞 X.B.I.E) : X.B.I.E)).map X.ιE.toRingHom.toIntAlgHom
        exact ⟨⟨_, this⟩, rfl⟩
      obtain ⟨o, ho⟩ := hint
      rw [← ho, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Formalism.L2.SG.Pf.mem_localization_of_mem' hmem)
    rw [show y = (y - r) + r by abel]
    exact add_mem (Formalism.L2.SG.Pf.localization_mono (le_sup_left.trans le_sup_left) h1)
      (Formalism.L2.SG.Pf.localization_mono (le_sup_right.trans le_sup_left) h2)
  ·
    refine ⟨((gS D : ℕ) : 𝓞 D.host.E), hP, ?_⟩
    exact (le_sup_left.trans le_sup_left : Ideal.span {((gS D : ℕ) : 𝓞 D.host.E)} • Λ ≤ _)
      (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) hyΛ)

end Formalism.L2.SG.Pf.BridgeRat
