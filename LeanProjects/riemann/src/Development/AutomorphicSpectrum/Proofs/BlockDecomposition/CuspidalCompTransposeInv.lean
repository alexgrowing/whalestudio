import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TransposeInverseLocal

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.TiCusp

variable {r s : ℕ} {R : Type*} [CommRing R]

def sw (h : r + s = 3) (p : UPos 3 s) : UPos 3 r :=
  ⟨(Fin.rev p.1.2, Fin.rev p.1.1), by
    have h1 := p.2.1
    have h2 := p.2.2
    have h3 := p.1.1.2
    have h4 := p.1.2.2
    simp only [Fin.val_rev]
    omega⟩

theorem sw_sw (h : r + s = 3) (h' : s + r = 3) (p : UPos 3 s) : sw h' (sw h p) = p := by
  apply Subtype.ext
  simp [sw]

def swE (h : r + s = 3) : UPos 3 s ≃ UPos 3 r :=
  ⟨sw h, sw (by omega), sw_sw h _, sw_sw _ h⟩

def tX (h : r + s = 3) (X : UPos 3 r → R) : UPos 3 s → R := fun p => -X (sw h p)

theorem tX_tX (h : r + s = 3) (h' : s + r = 3) (X : UPos 3 r → R) : tX h' (tX h X) = X := by
  funext p
  simp [tX, sw_sw]

theorem tX_add (h : r + s = 3) (X Y : UPos 3 r → R) : tX h (X + Y) = tX h X + tX h Y := by
  funext p
  simp [tX, add_comm]

theorem longWeyl_mul_apply (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (((w3 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) * M) i j = M (Fin.rev i) j := by
  fin_cases i <;> simp [w3, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

theorem mul_longWeyl_apply (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3) :
    (M * ((w3 : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)) i j = M i (Fin.rev j) := by
  fin_cases j <;> simp [w3, Matrix.mul_apply, Fin.sum_univ_three, Fin.rev]

theorem longWeyl_transposeInv_unipotent (h : r + s = 3) (X : UPos 3 r → R) :
    w3 * ti (unipGL X) = unipGL (tX h X) * w3 := by
  apply Units.ext
  ext i j
  rw [Units.val_mul, Units.val_mul, longWeyl_mul_apply, mul_longWeyl_apply]
  change ((unipGL X)⁻¹ : GL (Fin 3) R).val j (Fin.rev i) = (unipMatrix (tX h X)) i (Fin.rev j)
  rw [coe_unipGL_inv]
  simp only [unipMatrix, Matrix.add_apply, blockEntry_apply, Matrix.one_apply]
  have e1 : (j = Fin.rev i) ↔ (i = Fin.rev j) := by
    constructor
    · rintro rfl; simp
    · rintro rfl; simp
  have e2 : ((j : ℕ) < r ∧ r ≤ (Fin.rev i : ℕ)) ↔ ((i : ℕ) < s ∧ s ≤ (Fin.rev j : ℕ)) := by
    have := i.2
    have := j.2
    simp only [Fin.val_rev]
    omega
  by_cases c : (j : ℕ) < r ∧ r ≤ (Fin.rev i : ℕ)
  · rw [dif_pos c, dif_pos (e2.1 c)]
    simp only [e1, tX, Pi.neg_apply]
    congr 2
    congr 1
    apply Subtype.ext
    simp [sw]
  · rw [dif_neg c, dif_neg (fun d => c (e2.2 d))]
    simp only [e1]

def tE (h : r + s = 3) : (UPos 3 r → 𝔸[ℚ]) ≃ᵐ (UPos 3 s → 𝔸[ℚ]) where
  toFun := tX h
  invFun := tX (by omega)
  left_inv X := tX_tX h _ X
  right_inv X := tX_tX _ h X
  measurable_toFun := measurable_pi_lambda _ fun p => (measurable_pi_apply _).neg
  measurable_invFun := measurable_pi_lambda _ fun p => (measurable_pi_apply _).neg

theorem tE_apply (h : r + s = 3) (X : UPos 3 r → 𝔸[ℚ]) : tE h X = tX h X := rfl

theorem mp_tE (h : r + s = 3) :
    MeasurePreserving (tE h) (unipMeasure ℚ 3 r) (unipMeasure ℚ 3 s) := by
  refine ⟨(tE h).measurable, ?_⟩
  symm
  refine Measure.pi_eq fun S hS => ?_
  rw [Measure.map_apply (tE h).measurable (MeasurableSet.univ_pi hS)]
  have e : (tE h) ⁻¹' (Set.univ.pi S) =
      Set.univ.pi (fun p : UPos 3 r => Neg.neg ⁻¹' S ((swE h).symm p)) := by
    ext X
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff, tE_apply]
    constructor
    · intro H p
      have := H ((swE h).symm p)
      have e2 : sw h ((swE h).symm p) = p := (swE h).apply_symm_apply p
      simpa [tX, e2] using this
    · intro H q
      have := H (swE h q)
      simpa [tX, swE, sw_sw] using this
  rw [e, Measure.pi_pi]
  exact Fintype.prod_equiv (swE h).symm _ _ fun p => Measure.measure_preimage_neg _ _

theorem isFD_preimage (h : r + s = 3) :
    IsAddFundamentalDomain (unipLattice ℚ 3 s) ((tE h).symm ⁻¹' unipFundamentalDomain ℚ 3 r)
      (unipMeasure ℚ 3 s) := by
  have h' : s + r = 3 := by omega
  have hmem : ∀ {a b : ℕ} (k : a + b = 3) (ξ : unipLattice ℚ 3 a), tX k ξ.1 ∈ unipLattice ℚ 3 b := by
    rintro a b k ⟨_, ξ, rfl⟩
    refine ⟨tX k ξ, ?_⟩
    funext p
    simp [tX]
  refine isAddFundamentalDomain_unipFundamentalDomain.preimage_of_equiv
    (mp_tE h).symm.quasiMeasurePreserving (e := fun ξ => ⟨tX h ξ.1, hmem h ξ⟩) ?_ ?_
  · constructor
    · intro ξ η e
      have := congrArg (fun z : unipLattice ℚ 3 s => tX h' z.1) e
      simp only [tX_tX] at this
      exact Subtype.ext this
    · intro η
      exact ⟨⟨tX h' η.1, hmem h' η⟩, Subtype.ext (tX_tX h' h η.1)⟩
  · intro ξ Y
    change tX h' (tX h ξ.1 + Y) = ξ.1 + tX h' Y
    rw [tX_add, tX_tX]

theorem diagonal_weyl_GL3 : AdelicGLn.diagonal ℚ 3 w3 = (w3 : G3) := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;> simp [AdelicGLn.diagonal_apply, w3]

theorem constantTerm_ti {φ : G3 → ℂ} (hφ : IsLeftInvariant φ) (h : r + s = 3) (g : G3) :
    constantTerm r (fun g : G3 => φ (ti g)) g = constantTerm s φ (w3 * ti g) := by
  rw [constantTerm_eq_setIntegral hφ (isFD_preimage h)]
  rw [← (mp_tE h).setIntegral_preimage_emb (tE h).measurableEmbedding]
  have e : (tE h) ⁻¹' ((tE h).symm ⁻¹' unipFundamentalDomain ℚ 3 r) =
      unipFundamentalDomain ℚ 3 r := by
    ext X
    simp
  rw [e, constantTerm]
  refine setIntegral_congr_fun measurableSet_unipFundamentalDomain fun X _ => ?_
  change φ (ti (unipGL X * g)) = φ (unipGL (tX h X) * (w3 * ti g))
  rw [← mul_assoc, ← longWeyl_transposeInv_unipotent h, GlobalTheory.CompanionTheory.TransposeInverse.ti_mul, mul_assoc,
    ← diagonal_weyl_GL3, hφ]

theorem isCuspidal_comp_ti :
    ∀ φ : G3 → ℂ, IsLeftInvariant φ → IsCuspidal φ → IsCuspidal (fun g : G3 => φ (ti g)) := by
  intro φ hφ hc r hr hr3 g
  rw [constantTerm_ti hφ (s := 3 - r) (by omega)]
  exact hc (3 - r) (by omega) (by omega) _

end GlobalTheory.CompanionTheory.TiCusp

end
