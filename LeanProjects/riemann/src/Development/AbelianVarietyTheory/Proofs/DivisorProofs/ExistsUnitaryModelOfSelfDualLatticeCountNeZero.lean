import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjRelEquiv
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ValIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixedIntegralUnitEqNormUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SelfDualLatticeOrthogonalUnitNormExtensionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfOrthonormalBasisStatement

open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT GlobalTheory.KapLat
open scoped Classical

noncomputable section

namespace GlobalTheory.KapLat

theorem exists_orthonormal_of_selfDual (K : GlobalTheory.UnitLemma.UQ) (V : Type) [AddCommGroup V] [Module K.E V]
    [Module K.O V] [IsScalarTower K.O K.E V] [FiniteDimensional K.E V] (h : V → V → K.E)
    (hadd : ∀ y y' z, h (y + y') z = h y z + h y' z) (hsmul : ∀ (a : K.E) y z, h (a • y) z = a * h y z)
    (hsym : ∀ y z, h z y = K.c (h y z)) (L : Submodule K.O V) (hfg : L.FG)
    (hsp : Submodule.span K.E (L : Set V) = ⊤) (hsd : ∀ y, y ∈ L ↔ ∀ z ∈ L, h y z ∈ (algebraMap K.O K.E).range) :
    ∃ b : Module.Basis (Fin (Module.finrank K.E V)) K.E V, ∀ i j, h (b i) (b j) = if i = j then 1 else 0 := by
  have key : ∀ k, k ≤ Module.finrank K.E V → ∃ f : Fin k → V, (∀ i, f i ∈ L) ∧
      (∀ i j, i ≠ j → h (f i) (f j) = 0) ∧ ∀ i, ∃ t : K.O, IsUnit t ∧ h (f i) (f i) = algebraMap K.O K.E t := by
    intro k
    induction k with
    | zero => intro _; exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    | succ k ih =>
      intro hk
      obtain ⟨f, hfL, hfo, hfu⟩ := ih (by omega)
      obtain ⟨y, hyL, hyo, hyu⟩ := GlobalTheory.T.selfDual_lattice_orthogonal_unit_norm_extension K V h hadd hsmul hsym L hfg hsp hsd k f hfL hfo hfu (by omega)
      refine ⟨Fin.snoc f y, ?_, ?_, ?_⟩
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyL
        | cast i => simpa using hfL i
      · intro i j hij
        induction i using Fin.lastCases with
        | last =>
          induction j using Fin.lastCases with
          | last => exact absurd rfl hij
          | cast j => simpa using hyo j
        | cast i =>
          induction j using Fin.lastCases with
          | last => simp only [Fin.snoc_castSucc, Fin.snoc_last]; rw [hsym, hyo i, map_zero]
          | cast j =>
            simp only [Fin.snoc_castSucc]
            exact hfo i j fun e => hij (by rw [e])
      · intro i
        induction i using Fin.lastCases with
        | last => simpa using hyu
        | cast i => simpa using hfu i
  obtain ⟨f, -, hfo, hfu⟩ := key _ le_rfl
  choose t ht hft using hfu
  choose v hv using fun i => GlobalTheory.T.fixed_integral_unit_eq_norm_unramified K (t i) (ht i) (by rw [← hft, ← hsym])
  have hsmul2 : ∀ (a : K.E) y z, h y (a • z) = K.c a * h y z := by
    intro a y z
    rw [hsym, hsmul, map_mul, hsym z y]
  have ht0 : ∀ i, algebraMap K.O K.E (t i) ≠ 0 := fun i =>
    (map_ne_zero_iff _ (IsFractionRing.injective K.O K.E)).2 (ht i).ne_zero
  have hv0 : ∀ i, v i ≠ 0 := by
    intro i h0
    apply ht0 i
    rw [← hv i, h0, zero_mul]
  let g : Fin (Module.finrank K.E V) → V := fun i => (v i)⁻¹ • f i
  have hg : ∀ i j, h (g i) (g j) = if i = j then 1 else 0 := by
    intro i j
    simp only [g, hsmul, hsmul2]
    by_cases hij : i = j
    · subst hij
      rw [if_pos rfl, hft, ← hv i, map_inv₀]
      have : K.c (v i) ≠ 0 := by simpa using hv0 i
      field_simp
      exact div_self (hv0 i)
    · rw [if_neg hij, hfo i j hij, mul_zero, mul_zero]
  let φ : V → V →ₗ[K.E] K.E := fun z =>
    { toFun := fun y => h y z
      map_add' := fun y y' => hadd y y' z
      map_smul' := fun a y => by simp [hsmul] }
  have hli : LinearIndependent K.E g := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have := congrArg (φ (g i)) hc
    simp only [map_sum, map_smul, map_zero] at this
    simpa [φ, hg] using this
  refine ⟨Module.Basis.mk hli (hli.span_eq_top_of_card_eq_finrank' (by simp)).ge, fun i j => ?_⟩
  rw [Module.Basis.mk_apply, Module.Basis.mk_apply]
  exact hg i j

theorem X_nonempty_of_N_ne_zero {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (x : B.A) (hN : B.N x ≠ 0) :
    (B.X x).Nonempty := by
  by_contra hX
  rw [Set.not_nonempty_iff_eq_empty] at hX
  apply hN
  haveI : IsEmpty (GlobalTheory.UnitLemma.Orb K.O B.T (B.X x)) :=
    ⟨fun o => by
      induction o using Quot.ind with
      | mk L => exact Set.eq_empty_iff_forall_notMem.1 hX L.1 L.2⟩
  unfold GlobalTheory.UnitLemma.InvAlg.N GlobalTheory.UnitLemma.orbSum
  exact finsum_of_isEmpty _

theorem exists_model_of_N_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), Bridge w K e → ∀ (n : ℕ) (Q : (w.adicCompletion E)[X]) (B : GlobalTheory.UnitLemma.InvAlg K) (u x : B.A), Fits w e B Q u → Q.natDegree = n → B.σ x = x → IsUnit x → B.N x ≠ 0 → ∃ γ : GLw n w, γ ∈ UL n w ∧ IsModel w e B u x γ := by
  intro E _ _ _ w hw K e hB n Q B u x hF hn hσx _ hN
  obtain ⟨L, hlat, -, hsd⟩ := X_nonempty_of_N_ne_zero B x hN
  obtain ⟨b, hb⟩ := exists_orthonormal_of_selfDual K B.A (B.herm x)
    (fun y y' z => by unfold GlobalTheory.UnitLemma.InvAlg.herm; rw [mul_add, add_mul, map_add])
    (fun a y z => GlobalTheory.UnitLemma.Basic.herm_smul_left B x y z a)
    (fun y z => GlobalTheory.UnitLemma.Basic.herm_symm B x hσx y z) L hlat.1 hlat.2 hsd
  have hd : Module.finrank K.E B.A = n := hF.2.2.1.trans hn
  refine GlobalTheory.T.exists_hermitianModel_of_orthonormal_basis E w hw K e hB n B u x hF.2.2.2 (b.reindex (finCongr hd)) fun i j => ?_
  simp only [Module.Basis.reindex_apply, hb, EmbeddingLike.apply_eq_iff_eq]

end GlobalTheory.KapLat
