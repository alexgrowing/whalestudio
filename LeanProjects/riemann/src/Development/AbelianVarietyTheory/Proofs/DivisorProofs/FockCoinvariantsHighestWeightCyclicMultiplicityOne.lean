import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ActAtApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNontrivialLiftModule
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointShapeGenerated
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoinvTopOrRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHighestWeightLiftModStableSubspaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionIsLocallyBlockUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HighestWeightLeSpanSupFockCoinvariantsStatement

open scoped TensorProduct
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.HoweR

noncomputable section

namespace GlobalTheory.HoweR.Cyc

theorem coinv_eq_rel (P Q R S : ℕ) (x : ℚ) : coinv P Q R S (x : ℂ) = GlobalTheory.FockQuot.rel P Q R S x := rfl

theorem fockAct2_good (P Q R S : ℕ) : Good (fockAct2 P Q R S) :=
  ⟨(fock_lie_and_commute P Q R S).2.2.1, fun v => ((GlobalTheory.FockPolGK.pol_locFin_weights P Q R S).2 v).2,
    GlobalTheory.T.fockAction_isLocallyBlockUnitary P Q R S⟩

theorem rel_stab (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (y : Pol P Q R S) (hy : y ∈ GlobalTheory.FockQuot.rel P Q R S x) :
    fockAct2 P Q R S Y y ∈ GlobalTheory.FockQuot.rel P Q R S x := by
  have h := GlobalTheory.FockQuot.fockTraceCharacterRelations_le_comap_secondAction P Q R S x 0 Y hy
  rw [Submodule.mem_comap, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply] at h
  simpa using h

theorem actQ_zero_mk (P Q R S : ℕ) (x : ℚ) (Y : Mat R S) (f : Pol P Q R S) :
    GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) =
      Submodule.Quotient.mk (fockAct2 P Q R S Y f) := by
  rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; simp

theorem genSub_stable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (T : Set V) (Z : Mat p q) (y : V) (hy : y ∈ genSub act T) : act Z y ∈ genSub act T := by
  unfold genSub at hy ⊢
  rw [Submodule.mem_sInf] at hy ⊢
  intro N hN
  exact hN.2 Z y (hy N hN)

theorem mem_genSub_self {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (v : V) : v ∈ genSub act {v} := by
  unfold genSub
  rw [Submodule.mem_sInf]
  intro N hN
  exact hN.1 rfl

theorem cycMod_rel (P Q R S : ℕ) (x : ℚ) (hne : GlobalTheory.FockQuot.rel P Q R S x ≠ ⊤) :
    CycMod (fockAct2 P Q R S) (GlobalTheory.FockQuot.rel P Q R S x) := by
  set C := GlobalTheory.FockQuot.rel P Q R S x with hC
  have hnt : Nontrivial (GlobalTheory.FockQuot.gkQ P Q R S x 0).V := by
    show Nontrivial (Pol P Q R S ⧸ C)
    exact Submodule.Quotient.nontrivial_iff.2 hne
  have hlift : IsLift x 0 (GlobalTheory.FockQuot.gkQ P Q R S x 0) C.mkQ := by
    refine ⟨Submodule.mkQ_surjective _, fun X f => GlobalTheory.FockQuot.mk_fockFirstAction_eq_trace_smul P Q R S x X f, fun Y f => ?_⟩
    show GlobalTheory.FockQuot.actQ P Q R S x 0 Y (Submodule.Quotient.mk f) = _
    rw [GlobalTheory.FockQuot.actQ_mk, GlobalTheory.FockQuot.fockSecondActionTraceShift_apply]; rfl
  obtain ⟨μ', hJ, w, ⟨hw0, hwhw⟩, hgen⟩ :=
    GlobalTheory.RealLift.GenLift.genBy_of_isLift P Q R S x 0 _ _ hlift hnt
  change w ∈ hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) _ at hwhw
  change genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {w} = ⊤ at hgen
  obtain ⟨f₁, rfl⟩ := Submodule.Quotient.mk_surjective C w
  change (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ≠ 0 at hw0
  have hwhw' : (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) ∈
      hwSub (GlobalTheory.FockQuot.actQ P Q R S x 0) (fun c => μ' c + 0) := hwhw
  obtain ⟨hwt0, hpos0⟩ := Submodule.mem_inf.1 hwhw'
  have hwt : ∀ c, GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c c) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) =
      (((μ' c + 0 : ℚ)) : ℂ) • (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) := fun c => by
    unfold wtSub at hwt0
    have h := (Submodule.mem_iInf _).1 hwt0 c
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero] at h
    simpa using h
  have hpos : ∀ c d, posC c d →
      GlobalTheory.FockQuot.actQ P Q R S x 0 (Eab c d) (Submodule.Quotient.mk f₁ : Pol P Q R S ⧸ C) = 0 := fun c d hcd => by
    have h := (Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 ((Submodule.mem_iInf _).1 hpos0 c) d) hcd
    exact h
  have hKC : KStable (fockAct2 P Q R S) C := fun X _ y hy => rel_stab P Q R S x X y hy
  have hKT : KStable (fockAct2 P Q R S) (⊤ : Submodule ℂ (Pol P Q R S)) := fun _ _ _ _ => Submodule.mem_top
  have h1 : ∀ c, fockAct2 P Q R S (Eab c c) f₁ - ((μ' c : ℚ) : ℂ) • f₁ ∈ C := by
    intro c
    rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul,
      ← actQ_zero_mk, hwt c]
    simp
  have h2 : ∀ c d, posC c d → fockAct2 P Q R S (Eab c d) f₁ ∈ C := by
    intro c d hcd
    rw [← Submodule.Quotient.mk_eq_zero, ← actQ_zero_mk]
    exact hpos c d hcd
  obtain ⟨v, -, hv, hfv⟩ :=
    GlobalTheory.T.exists_highestWeight_lift_mod_stable_subspace R S (Pol P Q R S) (fockAct2 P Q R S) (fockAct2_good P Q R S) C ⊤ hKC hKT μ' f₁
      Submodule.mem_top h1 h2
  have hmk : (Submodule.Quotient.mk v : Pol P Q R S ⧸ C) = Submodule.Quotient.mk f₁ :=
    ((Submodule.Quotient.eq C).2 hfv).symm
  refine ⟨μ', v, hv, ?_, ?_⟩
  ·
    set N := genSub (fockAct2 P Q R S) {v} ⊔ C with hN
    have hNst : ∀ Z, ∀ y ∈ N, fockAct2 P Q R S Z y ∈ N := by
      intro Z y hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
      rw [map_add]
      exact N.add_mem (Submodule.mem_sup_left (genSub_stable _ _ Z a ha))
        (Submodule.mem_sup_right (rel_stab P Q R S x Z b hb))
    have hle : genSub (GlobalTheory.FockQuot.actQ P Q R S x 0) {Submodule.Quotient.mk f₁} ≤ N.map C.mkQ := by
      refine sInf_le ⟨?_, ?_⟩
      · rw [Set.singleton_subset_iff, ← hmk]
        exact ⟨v, Submodule.mem_sup_left (mem_genSub_self _ v), rfl⟩
      · rintro Z _ ⟨n, hn, rfl⟩
        refine ⟨fockAct2 P Q R S Z n, hNst Z n hn, ?_⟩
        simp only [Submodule.mkQ_apply]
        rw [actQ_zero_mk]
    have hle2 : N.map C.mkQ = ⊤ := top_le_iff.1 (le_trans (le_of_eq hgen.symm) hle)
    rw [eq_top_iff]
    intro f _
    have hf : Submodule.Quotient.mk f ∈ N.map C.mkQ := by rw [hle2]; exact Submodule.mem_top
    obtain ⟨n, hn, hnf⟩ := hf
    have hd : n - f ∈ C := (Submodule.Quotient.eq C).1 hnf
    have : f = n - (n - f) := by abel
    rw [this]
    exact N.sub_mem hn (Submodule.mem_sup_right hd)
  ·
    obtain ⟨f₀, hf₀⟩ := GlobalTheory.T.highestWeight_le_span_sup_fockCoinvariants P Q R S x μ' hJ
    rw [coinv_eq_rel] at hf₀
    obtain ⟨y, hy, c, hc, hyc⟩ := Submodule.mem_sup.1 (hf₀ hv)
    obtain ⟨z, rfl⟩ := Submodule.mem_span_singleton.1 hy
    have hz : z ≠ 0 := by
      rintro rfl
      apply hw0
      rw [← hmk, Submodule.Quotient.mk_eq_zero, ← hyc]
      simpa using hc
    have hf₀mem : f₀ ∈ Submodule.span ℂ {v} ⊔ C := by
      have : f₀ = z⁻¹ • v - z⁻¹ • c := by
        rw [← hyc, smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul, add_sub_cancel_right]
      rw [this]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)))
        (Submodule.mem_sup_right (C.smul_mem _ hc))
    refine hf₀.trans (sup_le ?_ le_sup_right)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact hf₀mem

end GlobalTheory.HoweR.Cyc

theorem GlobalTheory.HoweR.coinv_cycMod : ∀ (P Q R S : ℕ) (x : ℂ), CycMod (fockAct2 P Q R S) (coinv P Q R S x) := by
  intro P Q R S x
  rcases GlobalTheory.HoweR.coinv_top_or_rat P Q R S x with h | ⟨x', h⟩
  · rw [h]
    refine ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
  · rw [h, GlobalTheory.HoweR.Cyc.coinv_eq_rel] at *
    by_cases hne : GlobalTheory.FockQuot.rel P Q R S x' = ⊤
    · rw [hne]
      exact ⟨0, 0, Submodule.zero_mem _, by simp, by simp⟩
    · exact GlobalTheory.HoweR.Cyc.cycMod_rel P Q R S x' hne
