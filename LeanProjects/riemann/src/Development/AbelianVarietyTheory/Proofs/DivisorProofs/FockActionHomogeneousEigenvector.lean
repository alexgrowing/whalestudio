import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
import Development.AbelianVarietyTheory.Definitions.Foundations.HarmonicAllOfCompact

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

theorem injective_of_isFockIP {σ : Type} [DecidableEq σ] {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ι : MvPolynomial σ ℂ →ₗ[ℂ] H} (hι : IsFockIP ι) :
    Function.Injective ι := by
  have key : ∀ (α : σ →₀ ℕ) (P : MvPolynomial σ ℂ), inner ℂ (ι (monomial α 1)) (ι P) =
      coeff α P * α.prod (fun _ k => (k.factorial : ℂ)) := by
    intro α P
    induction P using MvPolynomial.induction_on' with
    | add P P' h h' => simp only [map_add, inner_add_right, h, h', coeff_add, add_mul]
    | monomial β c =>
      rw [monomial_eq_smul β c, map_smul, inner_smul_right, hι, coeff_smul, coeff_monomial]
      by_cases e : α = β
      · subst e; simp
      · simp [e, Ne.symm e]
  refine (injective_iff_map_eq_zero ι).2 fun P hP => ?_
  ext α
  have h := key α P
  rw [hP, inner_zero_right, eq_comm, mul_eq_zero] at h
  refine h.resolve_right ?_
  exact Finset.prod_ne_zero_iff.2 fun i _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add, ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem upOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    upOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).1, hc Y hY, map_smul]

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

theorem eq_zero_of_lowering {x : ℚ} {e e₀ : ℕ} {g v : Pol p q r s} (hg0 : g ≠ 0)
    (hg : g ∈ homog (Ln p q r s) e₀) (hgc : g ∈ charSub p q r s x) (he : e₀ < e)
    (hv : v ∈ homog (Ln p q r s) e) (hvc : v ∈ charSub p q r s x)
    (hd : ∀ Z : Mat r s, IsPC Z → dnOp (kron2 p q Z) v = 0) : v = 0 := by
  by_contra h0
  have h1 := isSide_one.degW_le Function.bijective_id hg (isHW_of_mem hg0 hgc)
  obtain ⟨d, hd1, hd2⟩ := isSide_one.homog_of_hw Function.bijective_id (isHW_of_mem h0 hvc)
    ((mem_harm1 v).1 fun Z hZ => by
      rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) v).2, hd Z hZ])
  obtain rfl : d = e := IsHomogeneous.inj_right hd2 hv h0
  rw [← hd1, Nat.cast_le] at h1
  omega

theorem mem_span_raising : ∀ (P Q R S : ℕ) (x : ℚ) (e e₀ : ℕ) (f g : Pol P Q R S),
    f ∈ homog (Ln P Q R S) e →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y f = ((x : ℂ) * Y.trace) • f) →
    g ≠ 0 → g ∈ homog (Ln P Q R S) e₀ →
    (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g = ((x : ℂ) * Y.trace) • g) →
    e₀ < e →
    f ∈ Submodule.span ℂ {f' | ∃ Z : Mat R S, IsPC Z ∧
      ∃ g' ∈ homog (Ln P Q R S) (e - 2),
        (∀ Y : Mat P Q, IsKC Y → fockAct1 P Q R S Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 P Q R S Z) g'} := by
  intro p q r s x e e₀ f g hf hfc hg0 hg hgc he
  by_cases h2 : e < 2
  · rw [eq_zero_of_lowering hg0 hg hgc he hf hfc fun Z _ => dnOp_low _ e h2 f hf]
    exact Submodule.zero_mem _
  have hι := GlobalTheory.FockAlg.Model.isFockIsometry_fockEmb (Ln p q r s)
  have hinj := injective_of_isFockIP hι
  set U := Submodule.span ℂ {f' | ∃ Z : Mat r s, IsPC Z ∧
      ∃ g' ∈ homog (Ln p q r s) (e - 2),
        (∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y g' = ((x : ℂ) * Y.trace) • g') ∧
        f' = plusPart (fockAct2 p q r s Z) g'} with hU
  have hle : U ≤ homog (Ln p q r s) e ⊓ charSub p q r s x := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨Z, hZ, g', h1, h3, rfl⟩
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ) g').1]
    refine ⟨?_, upOp_mem_charSub hZ h1 h3⟩
    have := upOp_homog (kron2 p q Z) _ g' h1
    rwa [show e - 2 + 2 = e by omega] at this
  have := Submodule.finiteDimensional_of_le (hle.trans inf_le_left)
  obtain ⟨u, hu, ho⟩ := exists_orth (GlobalTheory.FockAlg.Model.fockEmb (Ln p q r s)) U f
  have hh := Submodule.sub_mem _ hf (hle hu).1
  have hc : f - u ∈ charSub p q r s x := Submodule.sub_mem _ hfc (hle hu).2
  have h0 : f - u = 0 := eq_zero_of_lowering hg0 hg hgc he hh hc fun Z hZ => by
    have hZ' := isPC_conjTranspose hZ
    have h1 := ho _ (Submodule.subset_span ⟨_, hZ', _, dnOp_homog (kron2 p q Z) e _ hh,
      dnOp_mem_charSub hZ hh hc, rfl⟩)
    rw [fockAct2_eq, (parts_omAct (odd_kron2 hZ') _).1, inner_upOp hι (odd_kron2 hZ'),
      ← lineKroneckerRightMatrix_conjTranspose, neg_eq_zero, inner_self_eq_zero] at h1
    exact hinj (h1.trans (map_zero _).symm)
  rw [sub_eq_zero.1 h0]
  exact hu

end GlobalTheory.FockScalarType
