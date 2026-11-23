import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticTraceFromModelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmDataIsCMExtAndGramIsHermND
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp
open scoped TensorProduct

namespace GlobalTheory.IdemIsotropic

open Matrix Formalism.UG

variable {D : D7}

theorem hT_eq_hform (V : HSp D) (x y : V.V) :
    V.hT x y = hform (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram (V.frame.repr x) (V.frame.repr y) := by
  conv_lhs => rw [← V.frame.sum_repr x, ← V.frame.sum_repr y]
  simp only [map_sum, map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul, hform,
    HSpace.gram, Finset.mul_sum, RingHom.id_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show _ = star _ * _ * _
  rw [starRingEnd_apply]
  ring

theorem hform_mulVec {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A)
    (J M N : Matrix n n A) (a b : n → A) :
    hform σ J (M *ᵥ a) (N *ᵥ b) = hform σ (cT σ M * J * N) a b := by
  have h2 : (fun i => σ ((M *ᵥ a) i)) = (M.map σ) *ᵥ (fun i => σ (a i)) := by
    funext i; simp [Matrix.mulVec, dotProduct]
  rw [GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.hform_eq, h2, Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.dotProduct_mulVec, ← Matrix.vecMul_transpose,
    Matrix.vecMul_vecMul, cT, Matrix.mul_assoc]

theorem hform_zero {A : Type} [CommRing A] {n : Type} [Fintype n] (σ : A →+* A) (a b : n → A) :
    hform σ (0 : Matrix n n A) a b = 0 := by
  simp [hform]

theorem cT_sub' {A : Type} [CommRing A] {n : Type} (σ : A →+* A) (M N : Matrix n n A) :
    cT σ (M - N) = cT σ M - cT σ N := by
  ext i j; simp [cT]

theorem hT_toLin (V : HSp D) (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V) :
    V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
      hform (D.sp.cm.sig : D.host.E →+* D.host.E) (cT (D.sp.cm.sig : D.host.E →+* D.host.E) M * V.gram * N)
        (V.frame.repr a) (V.frame.repr b) := by
  rw [hT_eq_hform, Matrix.repr_toLin, Matrix.repr_toLin, hform_mulVec]

theorem gram_herm (V : HSp D) : cT (D.sp.cm.sig : D.host.E →+* D.host.E) V.gram = V.gram := by
  refine Matrix.ext fun i j => ?_
  show star (V.hT (V.frame j) (V.frame i)) = V.hT (V.frame i) (V.frame j)
  exact V.herm.eq (V.frame j) (V.frame i)

theorem idem_isotropic_pair : ∀ {D : D7} {V : HSp D} (γ : GF V) (ε : Matrix (Fin V.rank) (Fin V.rank) D.host.E), ε ∈ GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms.genAlg γ.1.1 → ε * ε = ε → ε ≠ 0 → Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) ε * V.gram * ε = 0 → ∃ X X' : Submodule D.host.E V.V, X ≠ ⊥ ∧ X ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X ∧ X' ≤ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V X' ∧ (∀ x ∈ X, GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X) ∧ (∀ x ∈ X', GlobalTheory.Cusp.ratAct D.sp.cm V γ x ∈ X') ∧ (∀ x ∈ X, (∀ y ∈ X', V.hD x y = 0) → x = 0) ∧ (∀ y ∈ X', (∀ x ∈ X, V.hD x y = 0) → y = 0) := by
  intro D V γ ε hmem hidem hne hiso
  set σ := (D.sp.cm.sig : D.host.E →+* D.host.E) with hσ
  set J := V.gram with hJdef
  have hdet : IsUnit J.det := isUnit_iff_ne_zero.2 (GlobalTheory.Mem.Vol.hspace_gram_det_ne_zero V)
  have hJJ : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hJJ' : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul _ hdet
  have cancel : ∀ A B : Matrix (Fin V.rank) (Fin V.rank) D.host.E, J * A = J * B → A = B := by
    intro A B h
    rw [← Matrix.one_mul A, ← Matrix.one_mul B, ← hJJ', Matrix.mul_assoc, h, ← Matrix.mul_assoc]
  set ε' := J⁻¹ * cT σ ε * J with hε'
  have hR : J * ε' = cT σ ε * J := by
    rw [hε', ← Matrix.mul_assoc, ← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  clear_value ε'
  have hTL : ∀ (M N : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (a b : V.V),
      V.hT (Matrix.toLin V.frame V.frame M a) (Matrix.toLin V.frame V.frame N b) =
        hform σ (cT σ M * J * N) (V.frame.repr a) (V.frame.repr b) := hT_toLin V
  have hσσ : ∀ e, σ (σ e) = e := fun e => star_star e
  have cTcT : ∀ M : Matrix (Fin V.rank) (Fin V.rank) D.host.E, cT σ (cT σ M) = M := by
    intro M; ext i j; simp [cT, hσσ]
  have herm : cT σ J = J := gram_herm V
  have hR' : cT σ ε' * J = J * ε := by
    have h := congrArg (cT σ) hR
    rw [cT_mul, cT_mul, herm, cTcT] at h
    exact h
  have h0 : ε' * ε = 0 := cancel _ _ (by rw [← Matrix.mul_assoc, hR, hiso, Matrix.mul_zero])
  set g := (γ.1 : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hg
  set gi := ((γ.1⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) with hgi
  have hγ : cT σ g * J * g = J := γ.2
  have hggi : g * gi = 1 := Units.mul_inv γ.1
  have hgig : gi * g = 1 := Units.inv_mul γ.1
  have hmem' : ε ∈ Algebra.adjoin D.host.E {g} := hmem
  have hJg : J * g = cT σ gi * J := by
    calc J * g = cT σ (g * gi) * J * g := by rw [hggi, cT_one, Matrix.one_mul]
      _ = cT σ gi * (cT σ g * J * g) := by rw [cT_mul]; simp only [Matrix.mul_assoc]
      _ = cT σ gi * J := by rw [hγ]
  have hεgi : Commute gi ε :=
    Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (by rw [Commute, SemiconjBy, hgig, hggi])
  have hε'g : ε' * g = g * ε' := cancel _ _ (by
    rw [← Matrix.mul_assoc, hR, Matrix.mul_assoc, hJg, ← Matrix.mul_assoc J g, hJg, Matrix.mul_assoc, hR,
      ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul, ← cT_mul, hεgi.eq])
  have hcomm : Commute ε' ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' hε'g
  have hgε : Commute g ε := Algebra.commute_of_mem_adjoin_singleton_of_commute hmem' (Commute.refl g)
  have h1 : ε * ε' = 0 := by rw [← hcomm.eq, h0]
  have mA : cT σ (1 - ε - ε') * J * ε = 0 := by
    rw [cT_sub', cT_sub', cT_one, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul, Matrix.sub_mul,
      Matrix.one_mul, hiso, hR', Matrix.mul_assoc, hidem, sub_zero, sub_self]
  have mB : cT σ ε' * J * (1 - ε - ε') = 0 := by
    rw [hR', Matrix.mul_sub, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc, Matrix.mul_assoc,
      hidem, h1, Matrix.mul_zero, sub_self, sub_zero]
  have mC : cT σ ε' * J * ε' = 0 := by rw [hR', Matrix.mul_assoc, h1, Matrix.mul_zero]
  have split : ∀ v : V.V, v = Matrix.toLin V.frame V.frame ε v + Matrix.toLin V.frame V.frame ε' v +
      Matrix.toLin V.frame V.frame (1 - ε - ε') v := by
    intro v
    simp only [map_sub, Matrix.toLin_one, LinearMap.sub_apply, LinearMap.id_apply]
    abel
  have mem_perp : ∀ (W : Submodule D.host.E V.V) (y : V.V),
      y ∈ GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp V W ↔ ∀ w ∈ W, V.hT w y = 0 := by
    intro W y
    simp [GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.perp, Submodule.mem_iInf, LinearMap.mem_ker]
  have ratAct_eq : ∀ x, GlobalTheory.Cusp.ratAct D.sp.cm V γ x = Matrix.toLin V.frame V.frame g x := fun _ => rfl
  refine ⟨LinearMap.range (Matrix.toLin V.frame V.frame ε), LinearMap.range (Matrix.toLin V.frame V.frame ε'),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro h
    rw [LinearMap.range_eq_bot] at h
    exact hne ((Matrix.toLin V.frame V.frame).map_eq_zero_iff.1 h)
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, hiso, hform_zero]
  · rintro _ ⟨b, rfl⟩
    rw [mem_perp]
    rintro _ ⟨a, rfl⟩
    rw [hTL, mC, hform_zero]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hgε.eq]
  · rintro _ ⟨a, rfl⟩
    refine ⟨Matrix.toLin V.frame V.frame g a, ?_⟩
    rw [ratAct_eq, ← LinearMap.comp_apply, ← LinearMap.comp_apply, ← Matrix.toLin_mul, ← Matrix.toLin_mul,
      hε'g]
  · rintro _ ⟨a, rfl⟩ hy
    refine V.nondeg.2 _ fun v => ?_
    rw [split v, map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, hTL ε ε, hiso, hform_zero,
      hTL (1 - ε - ε') ε, mA, hform_zero, zero_add, add_zero]
    exact hy _ ⟨v, rfl⟩
  · rintro _ ⟨b, rfl⟩ hx
    refine V.nondeg.1 _ fun v => ?_
    have e1 : V.hT (Matrix.toLin V.frame V.frame ε' b) v =
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) +
        V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) := by
      conv_lhs => rw [split v]
      simp only [map_add]
    have e2 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε' v) = 0 := by
      rw [hTL, mC, hform_zero]
    have e3 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame (1 - ε - ε') v) = 0 := by
      rw [hTL, mB, hform_zero]
    have e4 : V.hT (Matrix.toLin V.frame V.frame ε' b) (Matrix.toLin V.frame V.frame ε v) = 0 := hx _ ⟨v, rfl⟩
    linear_combination e1 + e2 + e3 + e4

end GlobalTheory.IdemIsotropic
