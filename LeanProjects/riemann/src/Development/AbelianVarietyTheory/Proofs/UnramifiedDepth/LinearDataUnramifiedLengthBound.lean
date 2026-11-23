import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.DualLattices.TowerZeroSurjective
import ReciprocityTheory.DualLattices.LinPairStatement
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
import ReciprocityTheory.DualLattices.SubMemOfCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsSeparatedOfIsQProjOver
import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
import ReciprocityTheory.DualLattices.FrobeniusOfGroupDivisorsRank
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenspaceDimAddSplitExactTranspose
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.HasLenExistsMonoFp
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicUnitQuotientPrincipalBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.EigenbasisRestrictionSurjectiveEquivariant
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TateModuleEigenspaceDimEqLieAlgebraSum
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsEigenIdem
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.DualNumberPointPreimageTopOfReduction
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.PadicPlaceBasisOfIdempotent
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsFreeGenerators

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem ofNat_succ_fin (n : ℕ) [NeZero n] (k : ℕ) :
    Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  ext
  simp [Fin.add_def, Fin.ofNat]

private theorem exp_bound (p : ℕ) [Fact p.Prime] (h : ℕ) (a b c : ℕ → ℕ) (D : ℕ)
    (hab : ∀ n, a n + b n = h) (hbc : ∀ n, b n ≤ c n) (hD : ∀ n, c n ≤ D) :
    (h : ℝ) / (p - 1) - ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (a n : ℝ) ≤
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (c n : ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have sa := summable_geom_p (p := p) (fun n => (a n : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun n => by exact_mod_cast (hab n ▸ Nat.le_add_right _ _ : a n ≤ h))
  have sc := summable_geom_p (p := p) (fun n => (c n : ℝ)) (fun _ => Nat.cast_nonneg _) D
    (fun n => by exact_mod_cast hD n)
  have sh := summable_geom_p (p := p) (fun _ => (h : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun _ => le_rfl)
  have e : (h : ℝ) / (p - 1) = ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (h : ℝ) := by
    rw [tsum_mul_right, tsum_geom_p]; ring
  rw [e, ← Summable.tsum_sub sh sa]
  refine Summable.tsum_le_tsum (fun n => ?_) (sh.sub sa) sc
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hp0 _)
  have h1 : (a n : ℝ) + b n = h := by exact_mod_cast hab n
  have h2 : (b n : ℝ) ≤ c n := by exact_mod_cast hbc n
  linarith

private theorem eigDim_le (C : Type) [Field C] {O OE : Type} [CommRing O] [Algebra O C] [CommRing OE]
    {d : ℕ} (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* C) : eigDim C ρ τ ≤ d := by
  unfold eigDim
  simpa using Submodule.finrank_le (⨅ a : OE, Module.End.eigenspace
    (Matrix.toLin' ((ρ a).map (algebraMap O C))) (τ a))

theorem linDat_unram_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ [IsLocalRing O], p ≠ 2 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e), (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a - (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ IsLocalRing.maximalIdeal O) → ∀ (rk : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (rk τ) → Fin d → O), (∀ τ, EigB ρG τ (W τ)) → ∀ j : Fin w.n, ∃ xs : NNReal, HasLen v O ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k))) xs ∧ v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) * (rk (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL _ hp2 hdisc w _ t ht
    rk W hW j
  obtain ⟨U, τ, ε, hsg, hr, -, -, hcj, hφ⟩ :=
    GlobalTheory.ChF.exists_unramData p C v O hv OE cp hS g H hL.noPad.1 hL.noPad.2 hdisc
  obtain ⟨hex, hmono, -⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  set ix : Fin w.n → Fin U.m := fun k => τ.symm ((t k : Emb (O := O) w.e) : OE →+* O) with hix
  have hτ : ∀ k, τ (ix k) = ((t k : Emb (O := O) w.e) : OE →+* O) := fun k => τ.apply_symm_apply _
  have hφ1 : ∀ k, U.φ (ix k) = ix (k + 1) := fun k => hφ _ _ (fun a => by rw [hτ, hτ]; exact ht k a)
  have hφn : ∀ n : ℕ, (U.φ ^ n) (ix j) = ix (j + Fin.ofNat w.n n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hφ1, ofNat_succ_fin, add_assoc]

  obtain ⟨-, -, α, b, -⟩ := GlobalTheory.PlaceMono.place_monogenic p OE w
  obtain ⟨h, y, hy1, hy2⟩ := GlobalTheory.LocalFactorFree.exists_free_generators p OE w b (Ix g) H.ρ
  have hh : ∀ k, U.r (ix k) + U.r (U.cj (ix k)) = h := by
    intro k
    have e1 := GlobalTheory.ChF.eigDim_eq_of_basis p C v O hv OE w b (Ix g) H.ρ h y hy1 hy2 _ (t k).2
    have e2 := GlobalTheory.ChF.eigDim_tate p C v O hv OE cp hS g H
      ((algebraMap O C).comp ((t k : Emb (O := O) w.e) : OE →+* O))
    rw [hr, hr, hcj, hτ, ← e1, e2, RingHom.comp_assoc]

  have hrk : ∀ σ : OE →+* O, eigDim C ρG ((algebraMap O C).comp σ) = rk σ := fun σ =>
    (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d (rk σ) ρG σ (W σ) (hW σ)).2.2
  have hle : ∀ i, U.r i ≤ rk (τ i) := by
    intro i
    have e := (GlobalTheory.EigAdd.eigDim_add_transpose C O OE d r g A B hL.exact ρG
      ((Int.castRingHom O).mapMatrix.comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp (τ i))).1
    rw [hr, ← hrk, e]
    exact Nat.le_add_left _ _
  have hD : ∀ σ, rk σ ≤ d := fun σ => hrk σ ▸ eigDim_le C _ _

  obtain ⟨V1, hV1⟩ := lenEx C v O hv g H.Ht (U.εL (ix j)) (U.εT (U.cj (ix j)))
  obtain ⟨f, hf⟩ := GlobalTheory.ChF.cokE_surj_res_quot p C v O hv OE cp hS g H d r m A B ρG N s hL U (ix j)
    ((t j : Emb (O := O) w.e) : OE →+* O) (fun x => by rw [hsg, hτ]) _ _ (hW _)
  obtain ⟨xs, hxs⟩ := hex ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k)))
    (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
  refine ⟨xs, hxs, ?_⟩
  have h1 := hmono _ _ f V1 xs hf hV1 hxs
  have h2 := up_full u7 p g C v O _ _ cp hp2 hS H U (ix j) _ (LinearEquiv.refl _ _) V1 hV1
  refine le_trans ?_ h1
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine le_trans ?_ h2
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · have e : ((U.r (ix j) : ℝ) + U.r (U.cj (ix j))) = h := by exact_mod_cast hh j
    rw [e]
    unfold frobSum
    refine exp_bound p h (fun n => U.r ((U.φ ^ (n + 1)) (ix j)))
      (fun n => U.r (U.cj (ix (j + Fin.ofNat w.n (n + 1))))) _ d (fun n => ?_) (fun n => ?_)
      (fun n => hD _)
    · rw [hφn]; exact hh _
    · have := hle (U.cj (ix (j + Fin.ofNat w.n (n + 1))))
      rwa [hcj, hτ] at this

end GlobalTheory.ChF
