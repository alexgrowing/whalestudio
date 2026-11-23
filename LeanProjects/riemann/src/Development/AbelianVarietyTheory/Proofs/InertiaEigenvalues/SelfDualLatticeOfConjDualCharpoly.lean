import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TripleAtt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.OffRange
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CcSymmAlgebraMapHost
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLinearMapOfTraceEq

noncomputable section

namespace GlobalTheory.LatticeSelfDual

open GlobalTheory.TripleGal Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.MainNotions.BlochKatoReduction Formalism.MainNotions.BlochKatoReduction.Gen Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial
open GlobalTheory.AntiRamConj

theorem trace_eq_of_charpoly_eq' {K : Type} [CommRing K] [Nontrivial K] {n : ℕ} {A B : Matrix (Fin n) (Fin n) K}
    (h : A.charpoly = B.charpoly) : A.trace = B.trace := by
  rcases n with _ | n
  · simp [Matrix.trace]
  · rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, h]

def conjC (D : D7) : Gen.GE D.nd →* Gen.GE D.nd where
  toFun := conjAut D.ntw.cc (fun x => ⟨_, cc_symm_algebraMap_host D x⟩)
  map_one' := by ext x; simp [conjAut_apply]
  map_mul' g h := by ext x; simp [conjAut_apply]

theorem conjC_apply (D : D7) (g : Gen.GE D.nd) (x : D.nd.Om) :
    conjC D g x = D.ntw.cc (g (D.ntw.cc.symm x)) := rfl

section
variable {D : D7} {N : NData D.R D.host D.what₂} {X : NTw D.R D.host D.what₂ D.LL0 N}

theorem tmat_one (i : X.Tw) (s : X.Sig i) : Tmat i s 1 = 1 := by
  rw [← Tgl_coe, map_one, Units.val_one]

theorem tmat_mul (i : X.Tw) (s : X.Sig i) (g h : Gen.GE N) : Tmat i s (g * h) = Tmat i s g * Tmat i s h := by
  rw [← Tgl_coe, ← Tgl_coe, ← Tgl_coe, map_mul, Units.val_mul]

def twistHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := (((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g
  map_one' := by simp [tmat_one]
  map_mul' g h := by
    rw [tmat_mul, map_mul, Units.val_mul, mul_pow, Matrix.smul_mul, Matrix.mul_smul, smul_smul]

def dualHom (i : X.Tw) (s : X.Sig i) : Gen.GE N →* Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i) where
  toFun g := Tdual i s g
  map_one' := by simp [Tdual, tmat_one]
  map_mul' g h := by
    simp only [Tdual]
    rw [tmat_mul, map_mul, Units.val_mul, Matrix.mul_inv_rev, Matrix.transpose_mul, Matrix.smul_mul,
      Matrix.mul_smul, smul_smul]

theorem span_twist (i : X.Tw) (s : X.Sig i)
    (h : Submodule.span (IsLocalRing.ResidueField (X.O0 i)) (Set.range (rbar X i s)) = ⊤) :
    Submodule.span (IsLocalRing.ResidueField (X.O0 i))
      (Set.range fun g => (twistHom i s g).map (IsLocalRing.residue (X.O0 i))) = ⊤ := by
  rw [eq_top_iff, ← h, Submodule.span_le]
  rintro _ ⟨g, rfl⟩
  let u : (X.O0 i)ˣ := (eps0 X i g ^ D.R.t * (chiS i s g)⁻¹)⁻¹
  have e : rbar X i s g = IsLocalRing.residue (X.O0 i) (u : X.O0 i) •
      (twistHom i s g).map (IsLocalRing.residue (X.O0 i)) := by
    have e2 : ((X.rhoS i s g : GL (Fin D.R.r) (X.O0 i)) : Matrix (Fin D.R.r) (Fin D.R.r) (X.O0 i)) =
        (u : X.O0 i) • twistHom i s g := by
      show _ = (u : X.O0 i) • ((((eps0 X i g : (X.O0 i)ˣ) : X.O0 i) ^ D.R.t) • Tmat i s g)
      rw [Tmat, smul_smul, smul_smul, mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← Units.val_mul,
        inv_mul_cancel, Units.val_one, one_smul]
    rw [rbar, e2]
    ext a b
    simp
  rw [e]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g, rfl⟩)

end

theorem selfDual_of_charDual : ∀ (D : D7) (i : D.ntw.Tw) (s : D.ntw.Sig i), ValuationStabilityAtRing D.ntw i s → CharDual i s → SelfDual i s := by
  intro D i s h2 hc
  have : CharZero (FractionRing (D.ntw.O0 i)) := charZero_of_injective_ringHom (D.ntw.emb0 i).injective
  have : CharZero (D.ntw.O0 i) :=
    ((algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i))).charZero_iff (IsFractionRing.injective _ _)).2 inferInstance
  obtain ⟨U, hU⟩ := GlobalTheory.TraceConj.exists_gl_conj_of_trace_eq (D.ntw.O0 i) (Gen.GE D.nd) D.R.r (twistHom i s).toHomUnits
    ((dualHom i s).comp (conjC D)).toHomUnits (span_twist i s h2.1)
    (fun g => trace_eq_of_charpoly_eq' (hc g (conjC D g) (conjC_apply D g)))
  refine ⟨U, fun g g' hg => ?_⟩
  obtain rfl : g' = conjC D g := by ext x; rw [hg, conjC_apply]
  have := congrArg Units.val (eq_mul_inv_of_mul_eq (hU g))
  rw [Units.val_mul, Units.val_mul] at this
  exact this

end GlobalTheory.LatticeSelfDual

end
