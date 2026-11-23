import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalFrameHermitianIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section

namespace GlobalTheory.UnitaryCentreLoc

open Matrix Formalism.UG

section Alg

variable {E R' : Type} [Field E] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]

def commSub (φ : E →+* R') (Z : Matrix n n R') : Submodule E (Matrix n n E) where
  carrier := {A | Z * A.map φ = A.map φ * Z}
  add_mem' {a b} ha hb := by
    simp only [Set.mem_setOf_eq] at *
    rw [Matrix.map_add _ (map_add φ), Matrix.mul_add, Matrix.add_mul, ha, hb]
  zero_mem' := by simp
  smul_mem' c a ha := by
    simp only [Set.mem_setOf_eq] at *
    have e : (c • a).map φ = φ c • a.map φ := by ext i j; simp
    rw [e, Matrix.mul_smul, Matrix.smul_mul, ha]

theorem mem_commSub {φ : E →+* R'} {Z : Matrix n n R'} {A : Matrix n n E} :
    A ∈ commSub φ Z ↔ Z * A.map φ = A.map φ * Z := Iff.rfl

theorem one_mem_commSub (φ : E →+* R') (Z : Matrix n n R') : (1 : Matrix n n E) ∈ commSub φ Z := by
  rw [mem_commSub, Matrix.map_one _ (map_zero φ) (map_one φ), Matrix.mul_one, Matrix.one_mul]

theorem mem_commSub_of_inv {φ : E →+* R'} {Z : Matrix n n R'} {A : Matrix n n E} (hA : IsUnit A.det)
    (h : A⁻¹ ∈ commSub φ Z) : A ∈ commSub φ Z := by
  rw [mem_commSub] at *
  have e1 : A.map φ * A⁻¹.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have e2 : A⁻¹.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, Matrix.nonsing_inv_mul _ hA, Matrix.map_one _ (map_zero φ) (map_one φ)]
  calc Z * A.map φ = A.map φ * (A⁻¹.map φ * Z) * A.map φ := by
        rw [← Matrix.mul_assoc (A.map φ), e1, Matrix.one_mul]
    _ = A.map φ * (Z * A⁻¹.map φ) * A.map φ := by rw [h]
    _ = A.map φ * Z := by simp only [Matrix.mul_assoc, e2, Matrix.mul_one]

variable (σ : E →+* E)

theorem cT_add' (A B : Matrix n n E) : cT σ (A + B) = cT σ A + cT σ B := by ext i j; simp [cT]
theorem cT_sub' (A B : Matrix n n E) : cT σ (A - B) = cT σ A - cT σ B := by ext i j; simp [cT]
theorem cT_smul' (c : E) (A : Matrix n n E) : cT σ (c • A) = σ c • cT σ A := by ext i j; simp [cT]
theorem det_cT' (A : Matrix n n E) : (cT σ A).det = σ A.det := by
  rw [cT, Matrix.det_transpose, RingHom.map_det]; rfl

end Alg

section Cayley

variable {E R' : Type} [Field E] [CharZero E] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]
  (σ : E →+* E) (J : Matrix n n E) (φ : E →+* R') (Z : Matrix n n R')

theorem cayley_mem (hZ : ∀ g ∈ UJ σ J, (g : Matrix n n E) ∈ commSub φ Z) (hJ : IsUnit J.det)
    {Y : Matrix n n E} (hY : cT σ Y * J = -(J * Y)) (hA : IsUnit (1 - Y).det) : Y ∈ commSub φ Z := by
  obtain ⟨A, rfl⟩ : ∃ A : Matrix n n E, A = 1 - Y := ⟨_, rfl⟩
  have hAB : (1 - Y) * (1 + Y) = (1 + Y) * (1 - Y) := by noncomm_ring
  have hcA : cT σ (1 - Y) * J = J * (1 + Y) := by
    rw [cT_sub', cT_one, Matrix.sub_mul, hY, Matrix.one_mul, Matrix.mul_add, Matrix.mul_one, sub_neg_eq_add]
  have hcB : cT σ (1 + Y) * J = J * (1 - Y) := by
    rw [cT_add', cT_one, Matrix.add_mul, hY, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, ← sub_eq_add_neg]
  have hB : IsUnit (1 + Y).det := by
    have h1 := congrArg Matrix.det hcA
    rw [Matrix.det_mul, Matrix.det_mul, det_cT'] at h1
    have h2 : (1 + Y).det = σ (1 - Y).det :=
      (mul_left_cancel₀ hJ.ne_zero (h1.symm.trans (mul_comm _ _))).trans rfl
    rw [h2]; exact hA.map σ
  have hAAi : (1 - Y) * (1 - Y)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hA
  have hgu : IsUnit ((1 + Y) * (1 - Y)⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul]
    exact hB.mul (Matrix.isUnit_nonsing_inv_det _ hA)
  obtain ⟨u, hu⟩ := hgu
  have hmem : u ∈ UJ σ J := by
    show cT σ (u : Matrix n n E) * J * (u : Matrix n n E) = J
    rw [hu]
    calc cT σ ((1 + Y) * (1 - Y)⁻¹) * J * ((1 + Y) * (1 - Y)⁻¹)
        = cT σ (1 - Y)⁻¹ * (cT σ (1 + Y) * J) * (1 + Y) * (1 - Y)⁻¹ := by
          rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - Y)⁻¹ * J * ((1 - Y) * (1 + Y)) * (1 - Y)⁻¹ := by
          rw [hcB]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - Y)⁻¹ * (J * (1 + Y)) * ((1 - Y) * (1 - Y)⁻¹) := by
          rw [hAB]; simp only [Matrix.mul_assoc]
      _ = cT σ (1 - Y)⁻¹ * cT σ (1 - Y) * J := by
          rw [hAAi, Matrix.mul_one, Matrix.mul_assoc (cT σ (1 - Y)⁻¹) (cT σ (1 - Y)) J, hcA]
      _ = J := by rw [← cT_mul, hAAi, cT_one, Matrix.one_mul]
  have hg : (1 + Y) * (1 - Y)⁻¹ ∈ commSub φ Z := by have := hZ u hmem; rwa [hu] at this
  have hsum : (1 + Y) * (1 - Y)⁻¹ + 1 = (2 : E) • (1 - Y)⁻¹ := by
    calc (1 + Y) * (1 - Y)⁻¹ + 1 = ((1 + Y) + (1 - Y)) * (1 - Y)⁻¹ := by
          rw [Matrix.add_mul (1 + Y) (1 - Y), hAAi]
      _ = ((2 : E) • (1 : Matrix n n E)) * (1 - Y)⁻¹ := by
          congr 1; rw [two_smul]; abel
      _ = (2 : E) • (1 - Y)⁻¹ := by rw [Matrix.smul_mul, Matrix.one_mul]
  have hAi : (1 - Y)⁻¹ ∈ commSub φ Z := by
    have e : (1 - Y)⁻¹ = (2 : E)⁻¹ • ((1 + Y) * (1 - Y)⁻¹ + 1) := by
      rw [hsum, smul_smul, inv_mul_cancel₀ (two_ne_zero), one_smul]
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.add_mem _ hg (one_mem_commSub _ _))
  have hAm := mem_commSub_of_inv hA hAi
  have e : Y = 1 - (1 - Y) := (sub_sub_cancel _ _).symm
  rw [e]
  exact Submodule.sub_mem _ (one_mem_commSub _ _) hAm

theorem eval_det_one_sub (X : Matrix n n E) (t : E) :
    X.charpolyRev.eval t = (1 - t • X).det := by
  rw [Matrix.charpolyRev, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm t]

theorem lie_mem (hZ : ∀ g ∈ UJ σ J, (g : Matrix n n E) ∈ commSub φ Z) (hJ : IsUnit J.det)
    {X : Matrix n n E} (hX : cT σ X * J = -(J * X)) : X ∈ commSub φ Z := by
  obtain ⟨t, ht0, htp⟩ : ∃ t : ℕ, (t : E) ≠ 0 ∧ IsUnit (1 - (t : E) • X).det := by
    by_contra hcon
    push_neg at hcon
    have hq : X.charpolyRev ≠ 0 := by
      intro h
      have := eval_det_one_sub X 0
      rw [h, zero_smul, sub_zero, Matrix.det_one] at this
      simp at this
    have hp : Polynomial.X * X.charpolyRev ≠ 0 := mul_ne_zero Polynomial.X_ne_zero hq
    apply hp
    apply Polynomial.eq_zero_of_infinite_isRoot
    refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (Nat.cast_injective (R := E)))
    rintro _ ⟨t, rfl⟩
    show Polynomial.eval _ _ = 0
    rw [Polynomial.eval_mul, Polynomial.eval_X]
    by_cases h0 : (t : E) = 0
    · rw [h0, zero_mul]
    · rw [eval_det_one_sub]
      have := hcon t h0
      rw [isUnit_iff_ne_zero, not_not] at this
      rw [this, mul_zero]
  have hY : cT σ ((t : E) • X) * J = -(J * ((t : E) • X)) := by
    rw [cT_smul', map_natCast, Matrix.smul_mul, hX, Matrix.mul_smul, smul_neg]
  have h1 := cayley_mem σ J φ Z hZ hJ hY htp
  have e : X = (t : E)⁻¹ • ((t : E) • X) := by rw [smul_smul, inv_mul_cancel₀ ht0, one_smul]
  rw [e]
  exact Submodule.smul_mem _ _ h1

end Cayley

section Span

variable {E R' : Type} [Field E] [CharZero E] [CommRing R'] {n : Type} [Fintype n] [DecidableEq n]
  (σ : E →+* E) (J : Matrix n n E) (φ : E →+* R') (Z : Matrix n n R')

theorem cT_cT' (hσσ : ∀ x, σ (σ x) = x) (A : Matrix n n E) : cT σ (cT σ A) = A := by
  ext i j; simp [cT, hσσ]

theorem all_mem (hσσ : ∀ x, σ (σ x) = x) {δ : E} (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) (hJh : cT σ J = J)
    (hJ : IsUnit J.det) (hZ : ∀ g ∈ UJ σ J, (g : Matrix n n E) ∈ commSub φ Z) (M : Matrix n n E) :
    M ∈ commSub φ Z := by
  have key : ∀ K : Matrix n n E, cT σ K = -K → K * J ∈ commSub φ Z := fun K hK =>
    lie_mem σ J φ Z hZ hJ (by rw [cT_mul, hJh, hK, Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc])
  have h2 : σ ((2 : E)⁻¹) = (2 : E)⁻¹ := by rw [map_inv₀, map_ofNat]
  set N := M * J⁻¹ with hN
  set K₁ := (2 : E)⁻¹ • (N - cT σ N) with hK₁
  set K₂ := ((2 : E)⁻¹ * δ⁻¹) • (N + cT σ N) with hK₂
  have c₁ : cT σ K₁ = -K₁ := by
    rw [hK₁, cT_smul', h2, cT_sub', cT_cT' σ hσσ, ← smul_neg, neg_sub]
  have c₂ : cT σ K₂ = -K₂ := by
    rw [hK₂, cT_smul', cT_add', cT_cT' σ hσσ, map_mul, h2, map_inv₀, hδ, ← smul_neg, add_comm (cT σ N),
      inv_neg, mul_neg, neg_smul, smul_neg]
  have hsum : N = K₁ + δ • K₂ := by
    rw [hK₁, hK₂, smul_smul, mul_comm δ, mul_assoc, inv_mul_cancel₀ hδ0, mul_one, ← smul_add]
    rw [sub_add_add_cancel, ← two_smul E N, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
  have hM : M = K₁ * J + δ • (K₂ * J) := by
    rw [← Matrix.smul_mul, ← Matrix.add_mul, ← hsum, hN, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hJ,
      Matrix.mul_one]
  rw [hM]
  exact Submodule.add_mem _ (key K₁ c₁) (Submodule.smul_mem _ _ (key K₂ c₂))

theorem map_single_one (i j : n) : (Matrix.single i j (1 : E)).map φ = Matrix.single i j 1 := by
  ext a b
  simp only [Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> simp

theorem scalar_of_comm (hσσ : ∀ x, σ (σ x) = x) {δ : E} (hδ0 : δ ≠ 0) (hδ : σ δ = -δ) (hJh : cT σ J = J)
    (hJ : IsUnit J.det) (hZ : ∀ g ∈ UJ σ J, (g : Matrix n n E) ∈ commSub φ Z) :
    ∃ ζ : R', Z = ζ • (1 : Matrix n n R') := by
  obtain ⟨ζ, hζ⟩ := Matrix.mem_range_scalar_of_commute_single (M := Z) (fun i j _ => by
    have h := all_mem σ J φ Z hσσ hδ0 hδ hJh hJ hZ (Matrix.single i j 1)
    rw [mem_commSub, map_single_one] at h
    exact h.symm)
  exact ⟨ζ, by rw [← hζ, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end Span

section Main

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU

theorem exists_sig_ne {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (cm : CMData F E) : ∃ a : E, cm.sig a ≠ a := by
  by_contra h
  push_neg at h
  have hall : ∀ a : E, a ∈ (algebraMap F E).range := fun a => (cm.fixed a).1 (h a)
  have htop : (⊥ : Subalgebra F E) = ⊤ := by
    refine eq_top_iff.2 fun a _ => ?_
    obtain ⟨b, rfl⟩ := hall a
    exact Subalgebra.algebraMap_mem _ b
  have := Subalgebra.bot_eq_top_iff_finrank_eq_one.1 htop
  rw [cm.deg2] at this
  exact absurd this (by norm_num)

theorem scalar_at_finite_place : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) → ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 D.host.F), ∃ ζ : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E, (GlobalTheory.AdelicU.matHom (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v) D.sp.cm.sig V.gram (GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram v z)).val = ζ • (1 : Matrix (Fin V.rank) (Fin V.rank) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Fv D.host.F v ⊗[D.host.F] D.host.E)) := by
  intro D V z hz v
  have hND := GlobalTheory.Mem.VolExists.isHermND D.sp.cm V
  have hσσ : ∀ x, (D.sp.cm.sig : D.host.E →+* D.host.E) (D.sp.cm.sig x) = x := fun x => star_star x
  obtain ⟨a, ha⟩ := exists_sig_ne D.sp.cm
  have hJh : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
    exact Matrix.ext fun i j => hND.1 i j
  refine scalar_of_comm (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (inclR (Fv D.host.F v)) _ hσσ
    (δ := a - D.sp.cm.sig a) (sub_ne_zero.2 (Ne.symm ha)) (by rw [map_sub, hσσ, neg_sub]; rfl) hJh
    (isUnit_iff_ne_zero.2 hND.2) ?_
  intro g hg
  let γ : GRat D.sp.cm.sig V.gram := ⟨g, hg⟩
  have hc := Subgroup.mem_center_iff.1 hz (ratEmb D.sp.cm.sig V.gram γ)
  have h1 := congrArg (fun x => (matHom _ D.sp.cm.sig V.gram (proj D.sp.cm.sig V.gram v x)).val) hc
  simp only [map_mul, proj_ratEmb, Units.val_mul] at h1
  have hm : (matHom _ D.sp.cm.sig V.gram (ratLoc D.sp.cm.sig V.gram v γ)).val =
      (g : Matrix (Fin V.rank) (Fin V.rank) D.host.E).map (inclR (Fv D.host.F v)) := by
    ext r s; rfl
  rw [mem_commSub, ← hm]
  exact h1.symm

end Main

end GlobalTheory.UnitaryCentreLoc
