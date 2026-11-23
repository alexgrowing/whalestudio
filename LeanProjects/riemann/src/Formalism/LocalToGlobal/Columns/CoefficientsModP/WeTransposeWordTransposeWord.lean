import Formalism.GradedWeylDivisibility.FinalD
import Formalism.GradedWeylDivisibility.StatementE
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQHW
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.FockQWordAdj
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.PieriBlockIdeals.PieriColumnMinors.LowerTriangularIntegral
import Formalism.PieriBlockIdeals.PieriColumnMinors.LrfcApplyWordAppendSingle
import Formalism.HermitianLattices.HermitianLatticesProofs.DualLattice

open MvPolynomial

noncomputable section

namespace Formalism.L2.DIV

open Formalism.GradedWeylDivisibility

theorem we_intQ_apply (r n : ℕ) (P : MvPolynomial (Fin r × Fin n) ℤ) :
    intQ r n P = MvPolynomial.map (Int.castRingHom ℚ) P := rfl

theorem we_applyWord_mem (R : Type) [CommRing R] (r n : ℕ) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ))
    (f : MvPolynomial (Fin r × Fin n) R) (hf : f ∈ dualWeyl R r n ν) : applyWord R w f ∈ dualWeyl R r n ν := by
  induction w with
  | nil => exact hf
  | cons x w ih => exact rowDivStable R r n ν _ _ _ _ ih

theorem we_fock_symm {σ : Type} (f g : MvPolynomial σ ℚ) : fockQ f g = fockQ g f := (fockQPos σ f g).1

theorem we_fock_add_left {σ : Type} (f f' g : MvPolynomial σ ℚ) : fockQ (f + f') g = fockQ f g + fockQ f' g :=
  (fockQBilin σ f f' g 0).1

theorem we_fock_smul_left {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ (c • f) g = c * fockQ f g :=
  (fockQBilin σ f 0 g c).2

theorem we_fock_add_right {σ : Type} (f g g' : MvPolynomial σ ℚ) : fockQ f (g + g') = fockQ f g + fockQ f g' := by
  rw [we_fock_symm, we_fock_add_left, we_fock_symm g, we_fock_symm g']

theorem we_fock_smul_right {σ : Type} (c : ℚ) (f g : MvPolynomial σ ℚ) : fockQ f (c • g) = c * fockQ f g := by
  rw [we_fock_symm, we_fock_smul_left, we_fock_symm g]

theorem we_fock_zero_right {σ : Type} (f : MvPolynomial σ ℚ) : fockQ f 0 = 0 := by
  have := we_fock_smul_right 0 f 0
  simpa using this

theorem we_hw_norm_ne {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) : fockQ (hw ℚ hn ν) (hw ℚ hn ν) ≠ 0 :=
  ne_of_gt ((fockQPos _ (hw ℚ hn ν) (hw ℚ hn ν)).2 (hwNe ℚ r n hn ν))

theorem we_eval_idFrame_map {r n : ℕ} (G : MvPolynomial (Fin r × Fin n) ℤ) :
    eval (idFrame ℚ r n) (MvPolynomial.map (Int.castRingHom ℚ) G) = ((eval (idFrame ℤ r n) G : ℤ) : ℚ) := by
  have h : idFrame ℚ r n = fun v => (Int.castRingHom ℚ) (idFrame ℤ r n v) := by
    funext v
    unfold idFrame
    split_ifs <;> simp
  rw [h, eval_map, ← eval₂_id]
  exact (eval₂_comp_left (Int.castRingHom ℚ) (RingHom.id ℤ) (idFrame ℤ r n) G).symm

theorem we_intQ_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (w : List (Fin r × Fin r × ℕ)) :
    intQ r n (applyWord ℤ w (hw ℤ hn ν)) = applyWord ℚ w (hw ℚ hn ν) := by
  rw [we_intQ_apply, ← lclosedeq_applyWord_map, lclosedeq_hw_map]

theorem we_fock_word {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ) (hν : Antitone ν) (w : List (Fin r × Fin r × ℕ))
    (P : MvPolynomial (Fin r × Fin n) ℚ) (hP : P ∈ dualWeyl ℚ r n ν) :
    fockQ P (applyWord ℚ w (hw ℚ hn ν)) =
      eval (idFrame ℚ r n) (applyWord ℚ (transposeWord w) P) * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := by
  rw [we_fock_symm, fock_space_word_adjoint r n w,
    fock_space_highest_weight r n hn ν hν _ (we_applyWord_mem ℚ r n ν _ P hP)]

theorem we_transposeWord_transposeWord {r : ℕ} (w : List (Fin r × Fin r × ℕ)) :
    transposeWord (transposeWord w) = w := by
  unfold transposeWord
  rw [List.map_reverse, List.reverse_reverse, List.map_map]
  simp [Function.comp_def]

theorem nabla_eq_dual_weyl_holds : NablaEqDualWeyl := by
  intro r n hn ν hν
  ext P
  constructor
  · rintro ⟨P0, hP0, rfl⟩
    have hPQ : intQ r n P0 ∈ dualWeyl ℚ r n ν := dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν P0 hP0
    refine ⟨hPQ, ?_⟩
    rintro _ ⟨Q0, hQ0, rfl⟩
    replace hQ0 : Q0 ∈ weyl ℤ r n hn ν := hQ0
    unfold weyl at hQ0
    induction hQ0 using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨w, rfl⟩ := hx
      refine ⟨eval (idFrame ℤ r n) (applyWord ℤ (transposeWord w) P0), ?_⟩
      simp only
      rw [we_intQ_word, we_fock_word hn ν hν w _ hPQ, we_intQ_apply, lclosedeq_applyWord_map, we_eval_idFrame_map]
    | zero => exact ⟨0, by rw [map_zero, we_fock_zero_right]; simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨a, ha⟩ := hx
      obtain ⟨b, hb⟩ := hy
      exact ⟨a + b, by rw [map_add, we_fock_add_right, ha, hb]; push_cast; ring⟩
    | smul c x _ hx =>
      obtain ⟨a, ha⟩ := hx
      refine ⟨c * a, ?_⟩
      rw [map_smul, ← Int.cast_smul_eq_zsmul ℚ, we_fock_smul_right, ha]
      push_cast; ring
  · rintro ⟨hP, hdual⟩
    have hc := we_hw_norm_ne hn ν
    obtain ⟨Q', hQ'⟩ := Formalism.CohomologicalDescent.LR.lower_triangular_integral r n ν P hP (fun e he => by
      by_cases hcol : ∀ s : Fin n, ∑ a : Fin r, e (a, s) = ν s
      · have hhom : IsWeightedHomogeneous (colW r n) P ν := hP.1
        rw [Formalism.CohomologicalDescent.LR.coefficient_word ℚ r n ν P e hhom he hcol]
        obtain ⟨z, hz⟩ := hdual (intQ r n (applyWord ℤ (transposeWord (wordOf e)) (hw ℤ hn ν)))
          (Submodule.mem_map_of_mem (Submodule.subset_span ⟨_, rfl⟩))
        rw [we_intQ_word, we_fock_word hn ν hν _ P hP, we_transposeWord_transposeWord] at hz
        exact ⟨z, mul_right_cancel₀ hc hz⟩
      · refine ⟨0, ?_⟩
        rw [Int.cast_zero]
        by_contra h
        exact hcol (colSums ℚ r n ν P hP e (mem_support_iff.mpr h)))
    refine ⟨Q', (dualWeylIntRat r n ν Q').2 ?_, hQ'.symm⟩
    rw [← we_intQ_apply, ← hQ']
    exact hP

section Double

variable {r n : ℕ} (hn : n ≤ r) (ν : Fin n → ℕ)

def weForm : (dualWeyl ℚ r n ν) →ₗ⋆[ℚ] (dualWeyl ℚ r n ν) →ₗ[ℚ] ℚ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℚ) (RingHom.id ℚ)
    (fun x y => fockQ x.1 y.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν))
    (by intro x x' y; simp only [Submodule.coe_add, we_fock_add_left, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_left, starRingEnd_apply, star_trivial, smul_eq_mul, mul_div_assoc])
    (by intro x y y'; simp only [Submodule.coe_add, we_fock_add_right, add_div])
    (by
      intro c x y
      simp only [Submodule.coe_smul, we_fock_smul_right, RingHom.id_apply, smul_eq_mul, mul_div_assoc])

theorem weForm_apply (x y : dualWeyl ℚ r n ν) :
    weForm hn ν x y = fockQ x.1 y.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν) := rfl

theorem we_form_symm : (weForm hn ν).IsSymm := by
  rw [LinearMap.isSymm_def]
  intro x y
  rw [weForm_apply, weForm_apply, starRingEnd_apply, star_trivial, we_fock_symm]

theorem we_form_self_eq_zero (x : dualWeyl ℚ r n ν) (h : weForm hn ν x x = 0) : x = 0 := by
  rw [weForm_apply, div_eq_zero_iff] at h
  have h1 := h.resolve_right (we_hw_norm_ne hn ν)
  by_contra hx
  have hx' : x.1 ≠ 0 := fun h0 => hx (Subtype.ext h0)
  exact ne_of_gt ((fockQPos _ x.1 x.1).2 hx') h1

theorem we_form_nondeg : (weForm hn ν).Nondegenerate :=
  ⟨fun x hx => we_form_self_eq_zero hn ν x (hx x), fun x hx => we_form_self_eq_zero hn ν x (hx x)⟩

theorem we_finiteDimensional (r n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℚ (dualWeyl ℚ r n ν) := by
  obtain ⟨b, hb, -⟩ := sSBasis ℚ r n ν
  have : Finite (ssIdx r n ν) := (sSIdxFinite r n ν).to_subtype
  rw [← hb.2.1]
  exact FiniteDimensional.span_of_finite ℚ (Set.finite_range b)

def weCut (r n : ℕ) (ν : Fin n → ℕ) (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) :
    Submodule ℤ (dualWeyl ℚ r n ν) :=
  S.comap ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)

theorem we_cut_inj {S S' : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)} (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν)
    (hS' : ∀ x ∈ S', x ∈ dualWeyl ℚ r n ν) (h : weCut r n ν S = weCut r n ν S') : S = S' := by
  ext x
  constructor
  · intro hx
    have h1 : (⟨x, hS x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S := hx
    rw [h] at h1
    exact h1
  · intro hx
    have h1 : (⟨x, hS' x hx⟩ : dualWeyl ℚ r n ν) ∈ weCut r n ν S' := hx
    rw [← h] at h1
    exact h1

theorem we_cut_bDual (S : Submodule ℤ (MvPolynomial (Fin r × Fin n) ℚ)) (hS : ∀ x ∈ S, x ∈ dualWeyl ℚ r n ν) :
    weCut r n ν (bDual r n hn ν S) = Formalism.HermitianLatticesTheory.dual (weForm hn ν) (weCut r n ν S) := by
  have hc := we_hw_norm_ne hn ν
  ext x
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, LinearMap.coe_restrictScalars,
    Submodule.mem_one, weForm_apply]
  constructor
  · rintro ⟨-, h⟩ y hy
    obtain ⟨z, hz⟩ := h y.1 hy
    replace hz : fockQ x.1 y.1 = z * fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    refine ⟨z, ?_⟩
    rw [we_fock_symm, hz, mul_div_assoc, div_self hc, mul_one]
    rfl
  · intro h
    refine ⟨x.2, fun Q hQ => ?_⟩
    obtain ⟨z, hz⟩ := h ⟨Q, hS Q hQ⟩ hQ
    refine ⟨z, ?_⟩
    show fockQ x.1 Q = _
    rw [we_fock_symm]
    have hz' : (z : ℚ) = fockQ Q x.1 / fockQ (hw ℚ hn ν) (hw ℚ hn ν) := hz
    rw [hz', div_mul_cancel₀ _ hc]

theorem we_weyl_le (hν : Antitone ν) : ∀ x ∈ (weyl ℤ r n hn ν).map (intQ r n), x ∈ dualWeyl ℚ r n ν := by
  rintro _ ⟨f, hf, rfl⟩
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν f (weylLeDual ℤ r n hn ν hν hf)

theorem we_nabla_le : ∀ x ∈ (dualWeyl ℤ r n ν).map (intQ r n), x ∈ dualWeyl ℚ r n ν := by
  rintro _ ⟨f, hf, rfl⟩
  exact dualWeylMap ℤ ℚ (Int.castRingHom ℚ) r n ν f hf

theorem we_nabla_fg (r n : ℕ) (ν : Fin n → ℕ) : (dualWeyl ℤ r n ν).FG := by
  obtain ⟨b, hb, -⟩ := sSBasis ℤ r n ν
  have : Finite (ssIdx r n ν) := (sSIdxFinite r n ν).to_subtype
  rw [← hb.2.1]
  exact Submodule.fg_span (Set.finite_range b)

theorem we_span_weyl (hν : Antitone ν) :
    Submodule.span ℚ (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) =
      dualWeyl ℚ r n ν := by
  rw [← weylEqNablaQ r n hn ν hν]
  unfold weyl
  rw [Submodule.map_span, Submodule.span_span_of_tower, ← Set.range_comp]
  congr 2
  funext w
  exact we_intQ_word hn ν w

theorem we_weyl_lattice (hν : Antitone ν) :
    Submodule.IsLattice ℚ (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))) := by
  have himg : (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n))).map
      ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ) = (weyl ℤ r n hn ν).map (intQ r n) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, we_weyl_le hn ν hν x hx⟩, hx, rfl⟩
  constructor
  · refine Submodule.fg_of_fg_map_injective ((dualWeyl ℚ r n ν).subtype.restrictScalars ℤ)
      (dualWeyl ℚ r n ν).injective_subtype ?_
    rw [himg]
    exact (Submodule.FG.of_le (we_nabla_fg r n ν) (weylLeDual ℤ r n hn ν hν)).map _
  · apply Submodule.map_injective_of_injective (f := (dualWeyl ℚ r n ν).subtype) (dualWeyl ℚ r n ν).injective_subtype
    rw [Submodule.map_top, Submodule.range_subtype, Submodule.map_span]
    have h2 : ((dualWeyl ℚ r n ν).subtype '' (weCut r n ν ((weyl ℤ r n hn ν).map (intQ r n)) : Set (dualWeyl ℚ r n ν))) =
        (((weyl ℤ r n hn ν).map (intQ r n) : Submodule ℤ _) : Set (MvPolynomial (Fin r × Fin n) ℚ)) := by
      conv_rhs => rw [← himg]
      rfl
    rw [h2, we_span_weyl hn ν hν]

end Double

theorem weyl_eq_dual_nabla_holds : WeylEqDualNabla := by
  intro r n hn ν hν
  have hfd := we_finiteDimensional r n ν
  have hdd := (Formalism.HermitianLatticesTheory.dualLattice ℤ ℚ (dualWeyl ℚ r n ν) (weForm hn ν) (we_form_symm hn ν) (we_form_nondeg hn ν)
    (fun z => ⟨z, by simp⟩) _ (we_weyl_lattice hn ν hν)).2.1
  refine we_cut_inj (ν := ν) (we_weyl_le hn ν hν) (fun x hx => hx.1) ?_
  rw [we_cut_bDual hn ν _ (we_nabla_le ν), nabla_eq_dual_weyl_holds r n hn ν hν,
    we_cut_bDual hn ν _ (we_weyl_le hn ν hν), hdd]

end Formalism.L2.DIV
