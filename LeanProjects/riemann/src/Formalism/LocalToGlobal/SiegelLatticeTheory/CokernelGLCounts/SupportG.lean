import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SmoothBigCellSectionsExist

noncomputable section

namespace Formalism.L2.SG.SupportG

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Abstract

theorem supportClosure_matrix {ι Θ : Type*} [Fintype ι] [Fintype Θ] (v : Θ → ι → ℂ) (a dens : Θ → ℝ) (Dsup : ℝ) (n : ι → ℝ)
    (ha : ∀ θ, 0 ≤ a θ) (hd : ∀ θ, dens θ ≤ Dsup) (hn : ∀ x, 0 < n x)
    (hsupp : ∀ θ x y, v θ x ≠ 0 → v θ y ≠ 0 → n x = n y) :
    ((Dsup : ℂ) • (Matrix.of fun x y => ∑ θ, (a θ : ℂ) * v θ x * star (v θ y)) -
      Matrix.of fun x y => ((n x : ℂ) * ∑ θ, (dens θ : ℂ) * (a θ : ℂ) * v θ x * star (v θ y)) /
        ((Real.sqrt (n x * n y) : ℝ) : ℂ)).PosSemidef := by
  have key : ∀ θ x y, ((n x : ℂ) * ((dens θ : ℂ) * (a θ : ℂ) * v θ x * star (v θ y))) /
      ((Real.sqrt (n x * n y) : ℝ) : ℂ) = (dens θ : ℂ) * (a θ : ℂ) * v θ x * star (v θ y) := by
    intro θ x y
    by_cases hx : v θ x = 0
    · simp [hx]
    by_cases hy : v θ y = 0
    · simp [hy]
    rw [← hsupp θ x y hx hy, Real.sqrt_mul_self (hn x).le]
    have hx0 : (n x : ℂ) ≠ 0 := by exact_mod_cast (hn x).ne'
    rw [mul_div_cancel_left₀ _ hx0]
  have hM : ((Dsup : ℂ) • (Matrix.of fun x y => ∑ θ, (a θ : ℂ) * v θ x * star (v θ y)) -
      Matrix.of fun x y => ((n x : ℂ) * ∑ θ, (dens θ : ℂ) * (a θ : ℂ) * v θ x * star (v θ y)) /
        ((Real.sqrt (n x * n y) : ℝ) : ℂ)) =
      ∑ θ, (((Dsup - dens θ) * a θ : ℝ) : ℂ) • Matrix.vecMulVec (v θ) (star (v θ)) := by
    ext x y
    simp only [Matrix.sub_apply, Matrix.smul_apply, Matrix.of_apply, Matrix.sum_apply,
      Matrix.vecMulVec_apply, Pi.star_apply, smul_eq_mul]
    simp_rw [Finset.mul_sum, Finset.sum_div, key]
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun θ _ => ?_
    push_cast
    ring
  rw [hM]
  refine Matrix.posSemidef_sum _ fun θ _ => ?_
  exact (Matrix.posSemidef_vecMulVec_self_star (v θ)).smul
    (Complex.zero_le_real.mpr (mul_nonneg (sub_nonneg.mpr (hd θ)) (ha θ)))

theorem not_posSemidef_ones_sub_one_fin_two :
    ¬ (Matrix.of fun x y : Fin 2 => (1 : ℂ) - (1 : ℂ) * (if x = y then 1 else 0)).PosSemidef := by
  intro h
  have h2 := h.dotProduct_mulVec_nonneg ![1, -1]
  simp [dotProduct, Matrix.mulVec, Fin.sum_univ_two] at h2
  rw [Complex.le_def] at h2
  norm_num at h2

theorem supportClosure_inhabited : ∃ (v : Fin 2 → Fin 2 → ℂ) (n : Fin 2 → ℝ), n 0 ≠ n 1 ∧ (∀ x, 0 < n x) ∧
    (∀ θ x y, v θ x ≠ 0 → v θ y ≠ 0 → n x = n y) ∧ v 0 0 ≠ 0 ∧ v 1 1 ≠ 0 := by
  refine ⟨fun θ x => if θ = x then 1 else 0, ![1, 2], by norm_num, ?_, ?_, by simp, by simp⟩
  · intro x
    fin_cases x <;> norm_num
  · intro θ x y hx hy
    have h1 : θ = x := by
      by_contra h
      exact hx (if_neg h)
    have h2 : θ = y := by
      by_contra h
      exact hy (if_neg h)
    rw [← h1, ← h2]

end Abstract

variable {D : Formalism.BasicNotions.D7}

def normG (T T' : ℕ) (w : Point D.host.E (D.R.rS + 1)) : ℚ := |Algebra.norm ℚ (Gpt T T' w)|

def SupportLoc (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (p : PlF D), Agree δ M p →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)), kind w = kind w' → KtopP M δ T T' p w w' ≠ 0 →
    (M p).modK ((D.s.atP p).ιE (Dmin w (D.R.rS + 1))) = (M p).modK ((D.s.atP p).ιE (Dmin w' (D.R.rS + 1))) ∧
    (M p).modK ((D.s.atP p).ιE (Dmin w D.R.rS)) = (M p).modK ((D.s.atP p).ιE (Dmin w' D.R.rS))

def SupportLemma (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)),
    (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite →
    KtopG M δ T T' w w' ≠ 0 → normG T T' w = normG T T' w'

def SupportVec (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) →
  ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)) (κ : Option D.host.E)
    (th : ∀ p, Option ((M p).Cls D.R.rS)),
    (Function.mulSupport fun p => BBtop M δ T T' p w (th p)).Finite →
    (Function.mulSupport fun p => BBtop M δ T T' p w' (th p)).Finite →
    BBG M δ T T' w κ th ≠ 0 → BBG M δ T T' w' κ th ≠ 0 → normG T T' w = normG T T' w'

theorem n0_eq_of_normG_eq {T T' : ℕ} {w w' : Point D.host.E (D.R.rS + 1)} (h : normG T T' w = normG T T' w') (c : ℝ) :
    n0 c T T' w = n0 c T T' w' := by
  have e : |Algebra.norm ℚ (Gpt T T' w / ((Lat.gS D : D.host.E) ^ D.R.m))| =
      |Algebra.norm ℚ (Gpt T T' w' / ((Lat.gS D : D.host.E) ^ D.R.m))| := by
    unfold normG at h
    rw [div_eq_mul_inv, div_eq_mul_inv, map_mul, map_mul, abs_mul, abs_mul, h]
  unfold n0
  rw [← Rat.cast_abs, ← Rat.cast_abs, e]

theorem kind_eq_and_ktopP_ne_zero_of_ktopG_ne_zero {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {T T' : ℕ} {w w' : Point D.host.E (D.R.rS + 1)}
    (hf : (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite) (h : KtopG M δ T T' w w' ≠ 0) :
    kind w = kind w' ∧ ∀ p, KtopP M δ T T' p w w' ≠ 0 := by
  unfold KtopG at h
  by_cases hk : kind w = kind w'
  · rw [if_pos hk] at h
    refine ⟨hk, fun p hp => h ?_⟩
    rw [finprod_eq_prod _ hf]
    exact Finset.prod_eq_zero (by simp [hp]) hp
  · rw [if_neg hk] at h
    exact absurd rfl h

def NormProd (D : Formalism.BasicNotions.D7) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep),
    (∀ p, Agree δ M p) → ∀ x : D.host.E, x ≠ 0 →
      ∏ᶠ p, (M p).modK ((D.s.atP p).ιE x) = (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹

theorem norm_conjF (x : D.host.E) : Algebra.norm ℚ (D.conjF x) = Algebra.norm ℚ x := by
  exact Algebra.norm_eq_of_algEquiv
    (AlgEquiv.ofBijective (D.conjF.restrictScalars ℚ) (AlgHom.bijective _)) x

theorem absNorm_eq_of_prod (hN : NormProd D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {x y : D.host.E} (hx : x ≠ 0)
    (hy : y ≠ 0) (h : ∀ p, (M p).modK ((D.s.atP p).ιE x) = (M p).modK ((D.s.atP p).ιE y)) :
    |Algebra.norm ℚ x| = |Algebra.norm ℚ y| := by
  have e : (((|Algebra.norm ℚ x| : ℚ)) : ℝ)⁻¹ = (((|Algebra.norm ℚ y| : ℚ)) : ℝ)⁻¹ := by
    rw [← hN δ M hA x hx, ← hN δ M hA y hy]
    exact finprod_congr h
  exact_mod_cast inv_injective e

theorem supportLemma_of_loc (hL : SupportLoc D) (hN : NormProd D) : SupportLemma D := by
  intro δ M hA T T' w w' hf hK
  obtain ⟨hk, hp⟩ := kind_eq_and_ktopP_ne_zero_of_ktopG_ne_zero hf hK
  have hl := fun p => hL δ M p (hA p) T T' w w' hk (hp p)
  unfold normG Gpt
  unfold kind at hk
  by_cases h0 : Dmin w D.R.rS = 0
  · have h0' : Dmin w' D.R.rS = 0 := by
      by_contra h0'
      rw [if_pos h0, if_neg h0'] at hk
      simp at hk
    simp only [h0, h0', map_zero, mul_zero, sub_zero, map_mul, norm_conjF, abs_mul]
    rw [absNorm_eq_of_prod hN hA (Formalism.MainNotions.BridgeLemma.Dmin_top_ne w) (Formalism.MainNotions.BridgeLemma.Dmin_top_ne w')
      (fun p => (hl p).1)]
  · have h0' : Dmin w' D.R.rS ≠ 0 := by
      intro h0'
      rw [if_neg h0, if_pos h0'] at hk
      simp at hk
    rw [if_neg h0, if_neg h0'] at hk
    have hz : zetaOf w = zetaOf w' := Option.some_injective _ hk
    have ha : Dmin w (D.R.rS + 1) = zetaOf w * Dmin w D.R.rS := by
      unfold zetaOf
      rw [div_mul_cancel₀ _ h0]
    have ha' : Dmin w' (D.R.rS + 1) = zetaOf w' * Dmin w' D.R.rS := by
      unfold zetaOf
      rw [div_mul_cancel₀ _ h0']
    have hfac : ∀ z d : D.host.E, z * d * D.conjF (z * d) - (T : D.host.E) * T' * (d * D.conjF d) =
        (d * D.conjF d) * (z * D.conjF z - (T : D.host.E) * T') := by
      intro z d
      rw [map_mul]
      ring
    rw [ha, ha', hfac, hfac]
    simp only [map_mul, norm_conjF, abs_mul]
    rw [hz, absNorm_eq_of_prod hN hA h0 h0' (fun p => (hl p).2)]

theorem n0_eq_of_support (hS : SupportLemma D) {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} (hA : ∀ p, Agree δ M p) {T T' : ℕ}
    {w w' : Point D.host.E (D.R.rS + 1)} (hf : (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite)
    (h : KtopG M δ T T' w w' ≠ 0) (c : ℝ) : n0 c T T' w = n0 c T T' w' := by
  exact n0_eq_of_normG_eq (hS δ M hA T T' w w' hf h) c

def PartnerSum {Y : TermTie D} {δ : ∀ p : PlF D, (D.s.atP p).Fp}
    {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep} {u u' : D.what₂.Word} (X : TermLoc D Y δ M u u') : Prop :=
  ∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
  ∀ w' : Point D.host.E (D.R.rS + 1), Gpt (D.mem u).A.T (D.mem u').A.T w' ≠ 0 →
    HasSum (fun P : {P : D.s.Pair u u' // Formalism.MainNotions.S.scalarP D.s P ∧ D.s.pfst P = γ ∧ D.s.ptOf (D.s.psnd P) = w'} =>
        star (D.s.cTerm (D.s.psnd P.1)))
      (star (BBG M δ (D.mem u).A.T (D.mem u').A.T w' (kind (D.s.ptOf γ)) (thCls X γ)))

def SupportUnderDensityBound (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    {Y : TermTie D} (X : ∀ u u' : D.what₂.Word, TermLoc D Y δ M u u') (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  (∀ p, Agree δ M p) →
  ∀ u u' : D.what₂.Word, (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
  Formalism.MainNotions.LocalBesselAndTopKernel.GLOB.CNT (X u u') (cN u u') → PartnerSum (X u u') →
  ∀ ϖ : ∀ p : PlF D, 𝒪[(D.s.atP p).Fp], (∀ p, Irreducible (ϖ p)) →
  ∀ Dsup : ℝ, 0 ≤ Dsup →
    (∀ γ : D.s.Term u u', D.s.generic γ → Gpt (D.mem u).A.T (D.mem u').A.T (D.s.ptOf γ) ≠ 0 →
      densT (X u u') ϖ γ ≤ Dsup) →
    ∀ (ι : Type) [Fintype ι] (w : ι → Point D.host.E (D.R.rS + 1)),
      (∀ x, Gpt (D.mem u).A.T (D.mem u').A.T (w x) ≠ 0) →
      ((Dsup : ℂ) • (Matrix.of fun x y => KtopG M δ (D.mem u).A.T (D.mem u').A.T (w x) (w y)) -
        Matrix.of fun x y => Formalism.MainNotions.S.Kgs D.s u u' (w x) (w y) /
          ((Real.sqrt (n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w x) *
            n0 (cN u u') (D.mem u).A.T (D.mem u').A.T (w y)) : ℝ) : ℂ)).PosSemidef

def SupportUnderDensityBoundAllModels (D : Formalism.BasicNotions.D7) {Y : TermTie D} (Z : TermLocs D Y) (cN : D.what₂.Word → D.what₂.Word → ℝ) : Prop :=
  ∀ (δ : ∀ p : PlF D, (D.s.atP p).Fp) (M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep)
    (hA : ∀ p, Agree δ M p), SupportUnderDensityBound δ M (fun u u' => Z δ M hA u u') cN

theorem lemmaG2_of_supportProposition {δ : ∀ p : PlF D, (D.s.atP p).Fp} {M : ∀ p : PlF D, Loc.Model (D.s.atP p).Fp (D.s.atP p).Ep}
    {Y : TermTie D} {X : ∀ u u' : D.what₂.Word, TermLoc D Y δ M u u'} {cN : D.what₂.Word → D.what₂.Word → ℝ}
    (hA : ∀ p, Agree δ M p) (H : SupportUnderDensityBound δ M X cN)
    (hC : ∀ u u' : D.what₂.Word, (D.mem u).A.T ≡ (D.mem u').A.T [MOD (Lat.gS D) ^ 2] →
      Formalism.MainNotions.LocalBesselAndTopKernel.GLOB.CNT (X u u') (cN u u') ∧ PartnerSum (X u u'))
    (hfin : ∀ (T T' : ℕ) (w w' : Point D.host.E (D.R.rS + 1)),
      (Function.mulSupport fun p => KtopP M δ T T' p w w').Finite) :
    Formalism.MainNotions.LocalBesselAndTopKernel.GLOB.G2 δ M X cN := by
  intro u u' hT ϖ hϖ Dsup hD hdens ι _ w hw
  exact ⟨fun x y => hfin _ _ _ _, H hA u u' hT (hC u u' hT).1 (hC u u' hT).2 ϖ hϖ Dsup hD hdens ι w hw⟩

end Formalism.L2.SG.SupportG
