import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]

theorem eval_charpolyRev_eq (M : Matrix n n E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

theorem cT_smul (σ : E →+* E) (c : E) (M : Matrix n n E) :
    Formalism.UG.cT σ (c • M) = σ c • Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_add (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_sub (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

theorem cT_cT (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n E) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

theorem cayley_unitary (σ : E →+* E) (J X : Matrix n n E) (t : E) (ht : σ t = t)
    (hX : Formalism.UG.cT σ X * J + J * X = 0) (hA : (1 - t • X).det ≠ 0) :
    Formalism.UG.cT σ ((2 : E) • (1 - t • X)⁻¹ - 1) * J * ((2 : E) • (1 - t • X)⁻¹ - 1) = J := by
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  set g : Matrix n n E := (2 : E) • P - 1
  have hgA : g * A = 1 + t • X := by
    rw [Matrix.sub_mul, Matrix.smul_mul, hPA, Matrix.one_mul, hAdef, two_smul]
    abel
  have hcA : Formalism.UG.cT σ A = 1 - t • Formalism.UG.cT σ X := by
    rw [hAdef, cT_sub, cT_smul, Formalism.UG.cT_one, ht]
  have hcPA : Formalism.UG.cT σ P * Formalism.UG.cT σ A = 1 := by
    rw [← Formalism.UG.cT_mul, hAP, Formalism.UG.cT_one]
  have hY : Formalism.UG.cT σ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have key : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ A * J * A := by
    have e1 : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ (g * A) * J * (g * A) := by
      rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    rw [e1, hgA, hcA, cT_add, cT_smul, Formalism.UG.cT_one, ht]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hY]
    rw [hAdef]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul]
    module
  calc Formalism.UG.cT σ g * J * g
      = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * (Formalism.UG.cT σ g * J * g) * (A * P) := by
        rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A) * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A) * P := by rw [key]
    _ = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * J * (A * P) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
variable {R : Type} [CommRing R] (ι : E →+* R)

theorem map_smulE (c : E) (M : Matrix n n E) : (c • M).map ι = ι c • M.map ι := by
  ext i j; simp

theorem map_subE (M N : Matrix n n E) : (M - N).map ι = M.map ι - N.map ι := by
  ext i j; simp

theorem map_addE (M N : Matrix n n E) : (M + N).map ι = M.map ι + N.map ι := by
  ext i j; simp

theorem map_oneE : (1 : Matrix n n E).map ι = 1 := Matrix.map_one _ (map_zero ι) (map_one ι)

theorem map_mulE (M N : Matrix n n E) : (M * N).map ι = M.map ι * N.map ι := Matrix.map_mul

theorem commute_skew (σ : E →+* E) (J : Matrix n n E) (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (X : Matrix n n E) (hX : Formalism.UG.cT σ X * J + J * X = 0) : Commute Z (X.map ι) := by
  classical
  have hp : X.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := X)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  obtain ⟨t, ht, hts⟩ := hF.exists_notMem_finset (insert 0 X.charpolyRev.roots.toFinset)
  have ht0 : t ≠ 0 := fun e => hts (by simp [e])
  have hdet : (1 - t • X).det ≠ 0 := by
    intro e
    apply hts
    rw [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_charpolyRev_eq]
    exact Or.inr e
  have hg := hZ _ (cayley_unitary σ J X t ht hX hdet)
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  have hP : Commute Z (P.map ι) := by
    have h1 : Commute Z (((2 : E) • P - 1).map ι + 1) := hg.add_right (Commute.one_right Z)
    rw [map_subE, map_smulE, map_oneE, sub_add_cancel] at h1
    have h3 := h1.smul_right (ι (2 : E)⁻¹)
    rwa [smul_smul, ← map_mul, inv_mul_cancel₀ h2, map_one, one_smul] at h3
  have hA : Commute Z (A.map ι) := by
    let u : (Matrix n n R)ˣ := ⟨P.map ι, A.map ι, by rw [← map_mulE, hPA, map_oneE], by rw [← map_mulE, hAP, map_oneE]⟩
    exact Commute.units_inv_right (u := u) hP
  have h4 : Commute Z (ι t • X.map ι) := by
    have := (Commute.one_right Z).sub_right hA
    rwa [hAdef, map_subE, map_oneE, map_smulE, sub_sub_cancel] at this
  have h5 := h4.smul_right (ι t⁻¹)
  rwa [smul_smul, ← map_mul, inv_mul_cancel₀ ht0, map_one, one_smul] at h5

theorem commute_all (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (M : Matrix n n E) : Commute Z (M.map ι) := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hcJi : Formalism.UG.cT σ J⁻¹ * J = 1 := by
    calc Formalism.UG.cT σ J⁻¹ * J = Formalism.UG.cT σ J⁻¹ * Formalism.UG.cT σ J := by rw [hJh]
      _ = 1 := by rw [← Formalism.UG.cT_mul, hJJi, Formalism.UG.cT_one]
  have skew : ∀ K : Matrix n n E, Formalism.UG.cT σ K = -K → Commute Z ((J⁻¹ * K).map ι) := by
    intro K hK
    refine commute_skew ι σ J hF h2 Z hZ _ ?_
    rw [Formalism.UG.cT_mul, hK, Matrix.mul_assoc, hcJi, ← Matrix.mul_assoc, hJJi]
    simp
  set K := J * M
  have hK1 : Formalism.UG.cT σ (K - Formalism.UG.cT σ K) = -(K - Formalism.UG.cT σ K) := by
    rw [cT_sub, cT_cT σ hσ]; abel
  have hK2 : Formalism.UG.cT σ (ξ • (K + Formalism.UG.cT σ K)) = -(ξ • (K + Formalism.UG.cT σ K)) := by
    rw [cT_smul, cT_add, cT_cT σ hσ, hξ, neg_smul, add_comm (Formalism.UG.cT σ K)]
  have c1 := skew _ hK1
  have c2 := (skew _ hK2).smul_right (ι ξ⁻¹)
  have c3 := (c1.add_right c2).smul_right (ι (2 : E)⁻¹)
  have e : M = (2 : E)⁻¹ • (J⁻¹ * (K - Formalism.UG.cT σ K) + ξ⁻¹ • (J⁻¹ * (ξ • (K + Formalism.UG.cT σ K)))) := by
    rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ0, one_smul, ← Matrix.mul_add, sub_add_add_cancel,
      ← two_smul E K, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hJiJ,
      Matrix.one_mul]
  rw [e, map_smulE, map_addE, map_smulE]
  exact c3

theorem eq_smul_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι)) :
    ∃ c : R, Z = c • (1 : Matrix n n R) := by
  have hs : Z ∈ Set.range (Matrix.scalar n) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    have := (commute_all ι σ hσ J hJh hJ ξ hξ hξ0 hF h2 Z hZ (Matrix.single i j 1)).symm
    have e : (Matrix.single i j (1 : E)).map ι = Matrix.single i j 1 := by
      ext a b; simp [Matrix.single_apply]
    rwa [e] at this
  obtain ⟨c, hc⟩ := hs
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

theorem exists_skew (D : D7) : ∃ ξ : D.host.E,
    (D.sp.cm.sig : D.host.E →+* D.host.E) ξ = -ξ ∧ ξ ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e : D.host.E, e ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      ext x
      simp only [Algebra.mem_bot, Algebra.mem_top, iff_true]
      exact h x
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  refine ⟨e - star e, ?_, ?_⟩
  · change star (e - star e) = -(e - star e)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    apply he
    exact (D.sp.cm.fixed e).1 (sub_eq_zero.1 h0).symm

theorem fixed_infinite (D : D7) :
    {t : D.host.E | (D.sp.cm.sig : D.host.E →+* D.host.E) t = t}.Infinite := by
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (algebraMap D.host.F D.host.E).injective)
  rintro _ ⟨a, rfl⟩
  exact D.sp.cm.sig.commutes a

theorem center_mt_eq_smul_one : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) →
    ∃ c : AE D, Formalism.L2.Theta.mt V z = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V z hz
  obtain ⟨ξ, hξ, hξ0⟩ := exists_skew D
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hσ : ∀ x, σ (σ x) = x := fun x => star_star x
  have hJh : Formalism.UG.cT σ V.gram = V.gram := Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)
  refine eq_smul_one (incA D) σ hσ V.gram hJh (Formalism.L2.Theta.gram_det_ne V) ξ hξ hξ0 (fixed_infinite D)
    two_ne_zero _ ?_
  intro g hg
  have hdet : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => Formalism.L2.Theta.gram_det_ne V ?_
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  let gG : GL (Fin V.rank) D.host.E := Matrix.nonsingInvUnit g hdet
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) = (Formalism.UG.cT σ g).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, σ]
  have hmem : Formalism.UG.bc (incA D) gG ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) * (V.gram.map (incA D)) * g.map (incA D) =
      V.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let w : GA D V := ⟨Formalism.UG.bc (incA D) gG, hmem⟩
  have hw : Formalism.L2.Theta.mt V w = g.map (incA D) := rfl
  have hzw : w * z = z * w := Subgroup.mem_center_iff.1 hz w
  have e1 : Formalism.L2.Theta.mt V (w * z) = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z := by
    simp [Formalism.L2.Theta.mt, map_mul]
  have e2 : Formalism.L2.Theta.mt V (z * w) = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w := by
    simp [Formalism.L2.Theta.mt, map_mul]
  rw [← hw]
  change Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z
  rw [← e1, ← e2, hzw]

end GlobalTheory.CenterScalar
