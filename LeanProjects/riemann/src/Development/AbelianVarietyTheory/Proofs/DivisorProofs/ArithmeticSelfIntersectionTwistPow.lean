import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackSmoothFunctionCInfAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticDegreeMixedLinearRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NontrivialIsomClassInt
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ENNReal Classical
open MvPolynomial GlobalTheory.ArInt
open CategoryTheory AlgebraicGeometry GlobalTheory GlobalTheory.Mean4O GlobalTheory.HermLB

open GlobalTheory.Points ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.MixPull

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {k' : Type} [CommRing k'] [Algebra k k']

theorem cInf_pull (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y) :
    ∀ σ (y : CxPts p σ), CxPts.CInfAt (fun y => c σ (PtsOver.map ρ hρ _ y)) y :=
  fun σ y => CxPts.CInfAt.pull ρ hρ (hc σ _)

theorem conj_pull (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ)
    (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) :
    ∀ σ σ', (Weight.ofFun (fun y : CxPts p σ => c σ (PtsOver.map ρ hρ _ y))).IsConj
      (Weight.ofFun (fun y : CxPts p σ' => c σ' (PtsOver.map ρ hρ _ y))) := by
  intro σ σ' i y y' h hy
  exact hcc σ σ' PUnit.unit _ _ (by simp [PtsOver.map_val, h]) CxPts.mem_ptsIn_top

end GlobalTheory.MixPull

namespace GlobalTheory.MixPull

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {k' : Type} [CommRing k'] [Algebra k k']

theorem isometric_pull_fnB (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y)
    (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) :
    ((fnB c hc hcc).pull ρ hρ).Isometric
      (fnB (fun σ y => c σ (PtsOver.map ρ hρ _ y)) (cInf_pull ρ hρ c hc) (conj_pull ρ hρ c hcc)) := by
  refine HermLB.isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top) (fun x j j' h h' => ?_)
    (fun σ j y _ => ?_)
  · refine (gm_linComb _ _ _ (𝟙 X) x j j' h h').trans ?_
    simp
    exact ((gm ρ x _).map_one).trans ((gm (𝟙 X) x _).map_one).symm
  · exact (Weight.pull_φ (Weight.ofFun (c σ)) ρ hρ j y).symm

end GlobalTheory.MixPull

namespace GlobalTheory.MixPull

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {k' : Type} [CommRing k'] [Algebra k k']

theorem isometric_comb_none {ι : Type} [Fintype ι] (ρ : X ⟶ Sp k') (hρ : ρ ≫ spMap (algebraMap k k') = p)
    (M : HermLB (spMap (algebraMap k k'))) (e : ℕ)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y)
    (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))) (hM : (fnB c hc hcc).Isometric (M.pow e))
    (L : ι → HermLB p) :
    (comb (fun o : Option ι => o.elim (M.pull ρ hρ) L) (Pi.single none (e : ℤ))).Isometric
      (fnB (fun σ y => c σ (PtsOver.map ρ hρ _ y)) (cInf_pull ρ hρ c hc) (conj_pull ρ hρ c hcc)) := by
  refine HermLB.icls_eq_iff.1 ?_
  rw [← HermLB.icls_eq_iff.2 (isometric_pull_fnB ρ hρ c hc hcc), HermLB.icls_pull,
    HermLB.icls_eq_iff.2 hM, HermLB.icls_pow, map_nsmul, ← HermLB.icls_pull, icls_comb,
    Finset.sum_eq_single (none : Option ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
  simp [natCast_zsmul]

end GlobalTheory.MixPull

namespace GlobalTheory.MixPull

theorem aeval_subst {ι : Type} [Fintype ι] (e : ℕ) (n : ι → ℤ) (D : ℕ) :
    aeval (fun j : Option ι => lin fun i => ((Pi.single j (j.elim (e : ℤ) fun _ => 1) : Option ι → ℤ) i : ℝ))
      (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
      (e : ℝ) • (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) := by
  have h1 : aeval (fun j : Option ι => lin fun i => ((Pi.single j (j.elim (e : ℤ) fun _ => 1) : Option ι → ℤ) i : ℝ))
      (rename some (lin fun i => (n i : ℝ))) = rename some (lin fun i => (n i : ℝ)) := by
    simp [lin, aeval_rename, map_sum, Fintype.sum_option, Pi.single_apply]
  rw [map_mul, map_pow, h1, aeval_X]
  simp [lin, Fintype.sum_option, Pi.single_apply, smul_eq_C_mul, mul_assoc]

end GlobalTheory.MixPull

namespace GlobalTheory.MixPull

theorem mix_pull_eq : GlobalTheory.Published.ArCalc → ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ),
    IsArithVar p D → ∀ (k' : Type) [CommRing k'] [IsDomain k'] [Algebra k k'] (ρ : X ⟶ Sp k')
    (hρ : ρ ≫ spMap (algebraMap k k') = p) (M : HermLB (spMap (algebraMap k k'))) (e : ℕ)
    (c : ∀ σ : k →+* ℂ, CxPts (spMap (algebraMap k k')) σ → ℝ) (hc : ∀ σ y, CxPts.CInfAt (c σ) y)
    (hcc : ∀ σ σ', (Weight.ofFun (c σ)).IsConj (Weight.ofFun (c σ'))), (fnB c hc hcc).Isometric (M.pow e) →
    ∀ (ι : Type) [Fintype ι] (L : ι → HermLB p) (Φ : MvPolynomial (Option ι) ℝ →ₗ[ℝ] ℝ),
      IsArFun (fun o : Option ι => o.elim (M.pull ρ hρ) L) D Φ → ∀ n : ι → ℤ,
        (e : ℝ) * Φ (MvPolynomial.X none * rename some (lin fun i => (n i : ℝ)) ^ D) =
          1 / 2 * chInt (comb L n) D (fun σ y => c σ (PtsOver.map ρ hρ _ y)) := by
  intro HA k _ X _ p D hX k' _ _ _ ρ hρ M e c hc hcc hM ι _ L Φ hΦ n
  classical
  have hiso := ((HA.arIso k X p D hX).2 (Option ι) _ Φ hΦ).2.2 (Option ι)
    (fun o : Option ι => o.elim (fnB (fun σ y => c σ (PtsOver.map ρ hρ _ y)) (cInf_pull ρ hρ c hc)
      (conj_pull ρ hρ c hcc)) L)
    (fun j => Pi.single j (j.elim (e : ℤ) fun _ => 1)) (fun j => ?_)
  · have h := HA.arChange k X p D hX ι L _ (cInf_pull ρ hρ c hc) (conj_pull ρ hρ c hcc) _ hiso n
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, aeval_subst, LinearMap.map_smul, smul_eq_mul] at h
    exact h
  · cases j with
    | none => exact isometric_comb_none ρ hρ M e c hc hcc hM L
    | some i => exact isometric_comb_single (fun o : Option ι => o.elim (M.pull ρ hρ) L) (some i)

end GlobalTheory.MixPull
