import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiTopEqProd
import Formalism.LocalToGlobal.Columns.XtPhiTopGCongr
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DatumPeriodicMulLatticeFinal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsVectorPrescribedCosetsBadPrimesFramesStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartBaseCosetBoundedTypePrimesAndTwistStatement
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Col Formalism.MainNotions Formalism.L2.Ker GlobalTheory.TwU GlobalTheory.TwV GlobalTheory.TwTop
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {n : ℕ}

theorem core (q : E) (hq : q ≠ 0) (hqi : IntAt P q) (M Dd : ℕ) (hD : 2 * M ≤ Dd) (y0 V₀ V₁ : Sp E n) (g k : Sp E n →ₗ[E] Sp E n)
    (hgI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (g x l))
    (hkI : ∀ x : Sp E n, (∀ l, IntAt P (x l)) → ∀ l, IntAt P (k x l))
    (hkD : ∀ w : Sp E n, (∀ l, IntAt P (w l)) → ∀ l, IntAt P ((q ^ Dd)⁻¹ * (k w - w) l))
    (hgy : ∀ l, IntAt P ((q ^ M)⁻¹ * (g y0 - y0) l)) (hy0 : ∀ l, IntAt P (q ^ M * y0 l))
    (h0 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₀ - y0) l)) (h1 : ∀ l, IntAt P ((q ^ M)⁻¹ * (V₁ - y0) l)) :
    ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - V₀) l) := by
  have hqpow : ∀ m : ℕ, IntAt P (q ^ m) := fun m => mem_intS.1 ((intS P).pow_mem (mem_intS.2 hqi) m)
  obtain ⟨s, hs⟩ : ∃ s, Dd = 2 * M + s := ⟨Dd - 2 * M, by omega⟩

  have hA : ∀ l, IntAt P ((q ^ M)⁻¹ * (k y0 - y0) l) := by
    intro l
    have h := hkD ((q ^ M) • y0) (fun l => by simpa [smul_eq_mul] using hy0 l) l
    have e : (q ^ M)⁻¹ * (k y0 - y0) l = q ^ s * ((q ^ Dd)⁻¹ * (k ((q ^ M) • y0) - (q ^ M) • y0) l) := by
      simp only [map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      rw [hs, pow_add, pow_mul]
      field_simp
      ring
    rw [e]
    exact mem_intS.1 ((intS P).mul_mem (mem_intS.2 (hqpow s)) (mem_intS.2 h))

  have hB : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - k y0) l) := by
    intro l
    have h := hkI ((q ^ M)⁻¹ • (V₁ - y0)) (fun l => by simpa [smul_eq_mul] using h1 l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  have hC : ∀ l, IntAt P ((q ^ M)⁻¹ * (k V₁ - y0) l) := by
    intro l
    have e : (q ^ M)⁻¹ * (k V₁ - y0) l = (q ^ M)⁻¹ * (k V₁ - k y0) l + (q ^ M)⁻¹ * (k y0 - y0) l := by
      simp only [Pi.sub_apply]; ring
    rw [e]; exact (hB l).add (hA l)
  have hE : ∀ l, IntAt P ((q ^ M)⁻¹ * (g (k V₁) - g y0) l) := by
    intro l
    have h := hgI ((q ^ M)⁻¹ • (k V₁ - y0)) (fun l => by simpa [smul_eq_mul] using hC l) l
    rwa [map_smul, map_sub, Pi.smul_apply, smul_eq_mul] at h
  intro l
  have e : (q ^ M)⁻¹ * (g (k V₁) - V₀) l =
      (q ^ M)⁻¹ * (g (k V₁) - g y0) l + (q ^ M)⁻¹ * (g y0 - y0) l + (-1 : E) * ((q ^ M)⁻¹ * (V₀ - y0) l) := by
    simp only [Pi.sub_apply]; ring
  rw [e]
  exact mem_intS.1 ((intS P).add_mem ((intS P).add_mem (mem_intS.2 (hE l)) (mem_intS.2 (hgy l)))
    ((intS P).mul_mem ((intS P).neg_mem (intS P).one_mem) (mem_intS.2 (h0 l))))

end GlobalTheory.LocQCoset

namespace GlobalTheory.LocQCoset

open GlobalTheory.TopInv

theorem coset_agree : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a =>
  ∀ (hi : t.m2 + 1 ≤ D.R.m) (β : (St (t.m2 + 1) hi).Ch) (P : SB t μ), P.1 ∉ t.Pr.vGs →
  ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1)) (g k : Sp t.X.E (D.R.N (t.m2 + 1)) ≃ₗ[t.X.E] Sp t.X.E (D.R.N (t.m2 + 1))),
    g ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    SameCoset t.sel (t.tup μ) (t.cst μ) P (g (y0At A (t.m2 + 1) hi β P)) (y0At A (t.m2 + 1) hi β P) →
    k ∈ GLint t.X.E (D.R.N (t.m2 + 1)) P.1 →
    (∀ w ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1, ((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ • (k w - w) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) →
    (∀ w, frsF t.sel (t.tup μ) p₁ P w = frsF t.sel (t.tup μ) p P (g (k w))) →
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M) • (frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ∧
    ((qOf P.1 : t.X.E) ^ (t.cst μ).M)⁻¹ • ((frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) -
      (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p))) ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hP hTie hi β P hPG p p₁ g k hg hgy hk hkD hF
  have hok := t.idx_ok μ
  have hq := qOf_ne (E := t.X.E) P.1
  have hqi : IntAt P.1 ((qOf P.1 : ℕ) : t.X.E) := intAt_nat (P := P.1) _
  have memS : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), x ∈ stdAt t.X.E (D.R.N (t.m2 + 1)) P.1 ↔ ∀ l, IntAt P.1 (x l) :=
    fun x => mem_localization_standardLattice P.1 x
  have rep : ∀ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) (t.m2 + 1),
      SameCoset t.sel (t.tup μ) (t.cst μ) P ((frsF t.sel (t.tup μ) p' P).symm (repY (cosetOf A (t.m2 + 1) hi β p')))
        (y0At A (t.m2 + 1) hi β P) := by
    intro p'
    obtain ⟨r, hr⟩ := GlobalTheory.T.exists_vector_prescribed_cosets_badPrimes_frames t.sel (t.tup μ) (t.cst μ) (frsF t.sel (t.tup μ) p') (fun P => y0At A (t.m2 + 1) hi β P)
    have hrep : repY (cosetOf A (t.m2 + 1) hi β p') ∈ cosetOf A (t.m2 + 1) hi β p' :=
      Classical.epsilon_spec (p := fun y => y ∈ cosetOf A (t.m2 + 1) hi β p') ⟨r, hr⟩
    exact hrep P
  have unf : ∀ y y' : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y y' →
      ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M)⁻¹ * (y - y') l) := by
    intro y y' h
    unfold SameCoset at h
    simpa only [if_neg hPG] using h
  have bnd : ∀ y : Sp t.X.E (D.R.N (t.m2 + 1)), SameCoset t.sel (t.tup μ) (t.cst μ) P y (y0At A (t.m2 + 1) hi β P) →
      ∀ l, IntAt P.1 (((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).M * y l) :=
    fun y h => (GlobalTheory.T.chartBaseCoset_bounded_typePrimes_and_twist A dtU a hP hTie hi β P y h).2 hPG
  refine ⟨(memS _).2 fun l => ?_, (memS _).2 fun l => ?_, (memS _).2 fun l => ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p) l
  · simpa only [Pi.smul_apply, smul_eq_mul] using bnd _ (rep p₁) l
  · have hW : (frsF t.sel (t.tup μ) p P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)) =
        g (k ((frsF t.sel (t.tup μ) p₁ P).symm (repY (cosetOf A (t.m2 + 1) hi β p₁)))) := by
      apply (frsF t.sel (t.tup μ) p P).injective
      rw [LinearEquiv.apply_symm_apply, ← hF, LinearEquiv.apply_symm_apply]
    have hgI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (g.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hg x).2 ((memS x).2 hx))
    have hkI : ∀ x : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (x l)) → ∀ l, IntAt P.1 (k.toLinearMap x l) :=
      fun x hx => (memS _).1 ((hk x).2 ((memS x).2 hx))
    have hkD' : ∀ w : Sp t.X.E (D.R.N (t.m2 + 1)), (∀ l, IntAt P.1 (w l)) →
        ∀ l, IntAt P.1 ((((qOf P.1 : ℕ) : t.X.E) ^ (t.cst μ).D P)⁻¹ * (k.toLinearMap w - w) l) := by
      intro w hw l
      simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using (memS _).1 (hkD w ((memS w).2 hw)) l
    have hrefl : SameCoset t.sel (t.tup μ) (t.cst μ) P (y0At A (t.m2 + 1) hi β P) (y0At A (t.m2 + 1) hi β P) := by
      unfold SameCoset
      intro l
      rw [sub_self, Pi.zero_apply, mul_zero]
      simpa using intAt_nat (E := t.X.E) (P := P.1) 0
    have hy0 := bnd _ hrefl
    have := core _ hq hqi (t.cst μ).M ((t.cst μ).D P) (hok.depthQ P hPG) (y0At A (t.m2 + 1) hi β P) _ _
      g.toLinearMap k.toLinearMap hgI hkI hkD' (unf _ _ hgy) hy0 (unf _ _ (rep p)) (unf _ _ (rep p₁)) l
    rw [hW]
    simpa only [Pi.smul_apply, smul_eq_mul, LinearEquiv.coe_coe] using this

end GlobalTheory.LocQCoset

end
