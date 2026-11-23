import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.RationalPrimesBelowPlaces
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DetThreePointsEqExpansion
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerAdditiveCharacterEquivariance
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerSmoothness
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WhittakerWellDefined
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecSet
open NumberField IsDedekindDomain MeasureTheory Topology GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Global.AdicLiesOver
open scoped ValuativeRel
open GlobalTheory.CompanionTheory.SmallSec

noncomputable section

namespace GlobalTheory.CompanionTheory.SintSec

section
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

theorem ball_iff {y : F} {m : ℕ} :
    y ∈ valBall F (m : ℤ) ↔
      ValuativeRel.valuation F y ≤ ValuativeRel.valuation F (GLnLocal.uniformizer F : F) ^ m := by
  rw [← map_pow, ← normalizedValuation_le_iff, map_pow,
    normalizedValuation_uniformizer (GLnLocal.irreducible_uniformizer F), ← WithZero.exp_nsmul,
    mem_valBall]
  simp

theorem modulus_of_sub_one {x : F} (h : x - 1 ∈ valBall F 1) : modulus x = 1 := by
  have := modulus_add_eq (x := (1 : F)) (d := x - 1) one_ne_zero (by rw [ord_one]; simpa using h)
  simpa using this

theorem inv_mem_zero {x : F} (h : x - 1 ∈ valBall F 1) : x⁻¹ ∈ valBall F 0 := by
  obtain ⟨h0, ho⟩ := modulus_eq_one_iff.1 (modulus_of_sub_one h)
  rw [mem_valBall_iff_le_ord (inv_ne_zero h0), ord_inv h0, ho]
  simp

theorem one_mem_zero : (1 : F) ∈ valBall F 0 :=
  mem_valBall_zero_iff.2 (one_mem _)

theorem mem_zero_of_mem {x : F} {m : ℤ} (hm : 0 ≤ m) (h : x ∈ valBall F m) : x ∈ valBall F 0 :=
  valBall_antitone hm h

theorem mem_zero_of_sub {x : F} {m : ℤ} (hm : 0 ≤ m) (h : x - 1 ∈ valBall F m) :
    x ∈ valBall F 0 := by
  have := add_mem (mem_zero_of_mem hm h) one_mem_zero
  simpa using this

theorem mul_zero_mem {m : ℤ} {x y : F} (hx : x ∈ valBall F m) (hy : y ∈ valBall F 0) :
    x * y ∈ valBall F m := by
  simpa using mul_mem_valBall hx hy

theorem det_sub_one {m : ℕ} {A : Matrix (Fin 2) (Fin 2) F}
    (h00 : A 0 0 - 1 ∈ valBall F (m : ℤ)) (h01 : A 0 1 ∈ valBall F (m : ℤ))
    (h10 : A 1 0 ∈ valBall F (m : ℤ)) (h11 : A 1 1 - 1 ∈ valBall F (m : ℤ)) :
    A.det - 1 ∈ valBall F (m : ℤ) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have e : A.det - 1 = (A 0 0 - 1) * A 1 1 + (A 1 1 - 1) - A 0 1 * A 1 0 := by
    rw [Matrix.det_fin_two]; ring
  rw [e]
  exact sub_mem (add_mem (mul_zero_mem h00 (mem_zero_of_sub hm0 h11)) h11)
    (mul_zero_mem h01 (mem_zero_of_mem hm0 h10))

theorem mem_K_iff {m : ℕ} (hm : 1 ≤ m) (g : GL (Fin 2) F) :
    g ∈ GLnLocal.congruenceSubgroup F 2 m ↔
      g.val 0 0 - 1 ∈ valBall F (m : ℤ) ∧ g.val 0 1 ∈ valBall F (m : ℤ) ∧
        g.val 1 0 ∈ valBall F (m : ℤ) ∧ g.val 1 1 - 1 ∈ valBall F (m : ℤ) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  constructor
  · intro hg
    have h := ((GLnLocal.mem_congruenceSubgroup_iff F 2).1 hg).2
    refine ⟨ball_iff.2 ?_, ball_iff.2 ?_, ball_iff.2 ?_, ball_iff.2 ?_⟩
    · simpa using h 0 0
    · simpa using h 0 1
    · simpa using h 1 0
    · simpa using h 1 1
  · rintro ⟨h00, h01, h10, h11⟩
    have hd := det_sub_one h00 h01 h10 h11
    have hdi : (g.val).det⁻¹ ∈ valBall F 0 := inv_mem_zero (valBall_antitone hm1 hd)
    have z00 := mem_zero_of_sub hm0 h00
    have z01 := mem_zero_of_mem hm0 h01
    have z10 := mem_zero_of_mem hm0 h10
    have z11 := mem_zero_of_sub hm0 h11
    have hinv : (g⁻¹ : GL (Fin 2) F).val =
        (g.val).det⁻¹ • !![g.val 1 1, -g.val 0 1; -g.val 1 0, g.val 0 0] := by
      rw [Matrix.coe_units_inv, Matrix.inv_def, Matrix.adjugate_fin_two, Ring.inverse_eq_inv']
    have hmul : ∀ {x : F}, x ∈ valBall F 0 → (g.val).det⁻¹ * x ∈ 𝒪[F] := fun hx =>
      mem_valBall_zero_iff.1 (by simpa using mul_mem_valBall hdi hx)
    refine (GLnLocal.mem_congruenceSubgroup_iff F 2).2
      ⟨(GLnLocal.mem_integralGL_iff F 2).2 ⟨?_, ?_⟩, ?_⟩
    · intro i j
      fin_cases i <;> fin_cases j
      · exact mem_valBall_zero_iff.1 z00
      · exact mem_valBall_zero_iff.1 z01
      · exact mem_valBall_zero_iff.1 z10
      · exact mem_valBall_zero_iff.1 z11
    · intro i j
      change (g⁻¹ : GL (Fin 2) F).val i j ∈ 𝒪[F]
      rw [hinv]
      fin_cases i <;> fin_cases j
      · simpa using hmul z11
      · simpa using hmul (neg_mem z01)
      · simpa using hmul (neg_mem z10)
      · simpa using hmul z00
    · intro i j
      fin_cases i <;> fin_cases j
      · simpa using ball_iff.1 h00
      · simpa using ball_iff.1 h01
      · simpa using ball_iff.1 h10
      · simpa using ball_iff.1 h11

def RowOK (m : ℕ) (h : GL (Fin 2) F) : Prop :=
  h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)

theorem rowOK_mul {m : ℕ} (hm : 1 ≤ m) {h k : GL (Fin 2) F} (hh : RowOK m h)
    (hk : k ∈ GLnLocal.congruenceSubgroup F 2 m) : RowOK m (h * k) := by
  have hm0 : (0 : ℤ) ≤ (m : ℤ) := by omega
  obtain ⟨h00, h01, h10, h11⟩ := (mem_K_iff hm k).1 hk
  obtain ⟨a, b⟩ := hh
  have e0 : (h * k).val 1 0 =
      h.val 1 0 * k.val 0 0 + ((h.val 1 1 - 1) * k.val 1 0 + k.val 1 0) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  have e1 : (h * k).val 1 1 - 1 =
      h.val 1 0 * k.val 0 1 + ((h.val 1 1 - 1) * k.val 1 1 + (k.val 1 1 - 1)) := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]; ring
  refine ⟨?_, ?_⟩
  · rw [e0]
    exact add_mem (mul_zero_mem a (mem_zero_of_sub hm0 h00))
      (add_mem (mul_zero_mem b (mem_zero_of_mem hm0 h10)) h10)
  · rw [e1]
    exact add_mem (mul_zero_mem a (mem_zero_of_mem hm0 h01))
      (add_mem (mul_zero_mem b (mem_zero_of_sub hm0 h11)) h11)

theorem rowOK_mul_inv_iff {m : ℕ} (hm : 1 ≤ m) {h g : GL (Fin 2) F}
    (hg : g ∈ GLnLocal.congruenceSubgroup F 2 m) : RowOK m (h * g⁻¹) ↔ RowOK m h := by
  constructor
  · intro hh
    simpa using rowOK_mul hm hh hg
  · intro hh
    exact rowOK_mul hm hh (inv_mem hg)

theorem mp_det_of_mem {m : ℕ} (hm : 1 ≤ m) {g : GL (Fin 2) F}
    (hg : g ∈ GLnLocal.congruenceSubgroup F 2 m) :
    mp (Matrix.GeneralLinearGroup.det g) (1 / 2) = 1 := by
  have hm1 : (1 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  obtain ⟨h00, h01, h10, h11⟩ := (mem_K_iff hm g).1 hg
  have hmod : modulus (g.val).det = 1 :=
    modulus_of_sub_one (valBall_antitone hm1 (det_sub_one h00 h01 h10 h11))
  simp [mp, hmod]

end

theorem main : ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [MeasurableSpace F] [BorelSpace F] (ψ : AddChar F Circle), IsStd ψ → ∀ (W' : GL (Fin 2) F → ℂ) (m : ℕ), 1 ≤ m →
  (∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, W' (g * u) = W' g) →
  ∀ Φ ∈ LFS.SB F, ∀ V : ℂ,
  (∀ (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F), (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ Φ A ξ = V) →
  (∀ (A : Matrix (Fin 2) (Fin 2) F) (ξ : Fin 2 → F), ¬ (A 0 0 - 1 ∈ valBall F (m : ℤ) ∧ A 0 1 ∈ valBall F (m : ℤ) ∧ A 1 0 ∈ valBall F (m : ℤ) ∧ A 1 1 - 1 ∈ valBall F (m : ℤ) ∧ ξ 0 ∈ valBall F (m : ℤ) ∧ ξ 1 - 1 ∈ valBall F (m : ℤ)) → GL2LocalData.pFT ψ Φ A ξ = 0) →
  (∀ h : GL (Fin 2) F, h.val 1 0 ∈ valBall F (m : ℤ) → h.val 1 1 - 1 ∈ valBall F (m : ℤ) →
    LFS.Wp ψ W' Φ (GL2LocalData.em h) = (V * (((LFS.hG ψ).real (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) : ℝ) : ℂ)) * mp (Matrix.GeneralLinearGroup.det h) (1 / 2) * W' h) ∧
  (∀ h : GL (Fin 2) F, ¬ (h.val 1 0 ∈ valBall F (m : ℤ) ∧ h.val 1 1 - 1 ∈ valBall F (m : ℤ)) → LFS.Wp ψ W' Φ (GL2LocalData.em h) = 0) := by
  intro F _ _ _ _ _ _ ψ hψ W' m hm hW Φ hΦ V hV h0
  have hmeas : MeasurableSet (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)) :=
    (GLnLocal.isOpen_congruenceSubgroup F 2 m).measurableSet
  have key := fun h => GlobalTheory.CompanionTheory.KTwoWhittakerSubgroup.main F ψ hψ W' Φ hΦ h
  refine ⟨fun h h1 h2 => ?_, fun h hn => ?_⟩
  · have hrow : RowOK m h := ⟨h1, h2⟩
    have hf : (fun g : GL (Fin 2) F => GL2LocalData.pFT ψ Φ g.val (GL2LocalData.e2r (h * g⁻¹)) *
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) * W' (h * g⁻¹)) =
        (GLnLocal.congruenceSubgroup F 2 m : Set (GL (Fin 2) F)).indicator
          (fun _ => V * W' h) := by
      funext g
      by_cases hg : g ∈ GLnLocal.congruenceSubgroup F 2 m
      · rw [Set.indicator_of_mem (show g ∈ (GLnLocal.congruenceSubgroup F 2 m : Set _) from hg)]
        obtain ⟨a00, a01, a10, a11⟩ := (mem_K_iff hm g).1 hg
        obtain ⟨r0, r1⟩ := (rowOK_mul_inv_iff hm hg).2 hrow
        rw [hV g.val (GL2LocalData.e2r (h * g⁻¹)) ⟨a00, a01, a10, a11, r0, r1⟩, mp_det_of_mem hm hg,
          hW h g⁻¹ (inv_mem hg), mul_one]
      · rw [Set.indicator_of_notMem (show g ∉ (GLnLocal.congruenceSubgroup F 2 m : Set _) from hg),
          h0 g.val (GL2LocalData.e2r (h * g⁻¹))
            (fun c => hg ((mem_K_iff hm g).2 ⟨c.1, c.2.1, c.2.2.1, c.2.2.2.1⟩))]
        simp
    rw [key h, hf, integral_indicator_const _ hmeas, Complex.real_smul]
    ring
  · have hf : (fun g : GL (Fin 2) F => GL2LocalData.pFT ψ Φ g.val (GL2LocalData.e2r (h * g⁻¹)) *
        mp (Matrix.GeneralLinearGroup.det g) (1 / 2) * W' (h * g⁻¹)) = fun _ => 0 := by
      funext g
      rw [h0 g.val (GL2LocalData.e2r (h * g⁻¹)) ?_]
      · simp
      · rintro ⟨a00, a01, a10, a11, r0, r1⟩
        have hg := (mem_K_iff hm g).2 ⟨a00, a01, a10, a11⟩
        exact hn ((rowOK_mul_inv_iff hm hg).1 ⟨r0, r1⟩)
    rw [key h, hf]
    simp

end GlobalTheory.CompanionTheory.SintSec
