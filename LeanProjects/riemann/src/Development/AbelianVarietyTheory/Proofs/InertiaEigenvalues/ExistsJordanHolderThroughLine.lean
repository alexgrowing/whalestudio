import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistedModelAdmissibleCocycles
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.OnePlusPowerAssembly
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSeriesOfExact
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSimplePiecesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelObjAndAbcStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPushOfSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicityAdditiveExactSequenceStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ModelPreimageOfInjectiveFinDimRepModelHomStatement

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models.ThroughLine

variable {k G : Type} [Field k] [Group G]

theorem exists_ker (A B : Ob k G) (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (K : Ob k G) (f : (Fin K.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom K A f ∧ Function.Injective f ∧ Function.Exact f p := by
  obtain ⟨K, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) (fun g x hx => by
    rw [Submodule.mem_comap, LinearMap.mem_ker, hp g x, LinearMap.mem_ker.mp hx, map_zero]))
  refine ⟨K, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (LinearMap.ker p).subtype_injective.comp e.symm.injective, fun y => ⟨fun hy => ?_, ?_⟩⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [← he]
    simp
  · exact ⟨e ⟨y, hy⟩, by simp⟩
  · rintro ⟨x, rfl⟩
    exact (e.symm x).2

theorem exists_coker (A B : Ob k G) (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (Q : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin Q.m → k)),
      IsHom B Q q ∧ Function.Surjective q ∧ Function.Exact j q := by
  obtain ⟨Q, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) (fun g x hx => by
    obtain ⟨y, rfl⟩ := hx
    exact ⟨A.ρ g y, hj g y⟩))
  refine ⟨Q, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => he g (Submodule.Quotient.mk x),
    e.surjective.comp (LinearMap.range j).mkQ_surjective, fun y => ?_⟩
  simp [Submodule.Quotient.mk_eq_zero]

theorem simple_chr (χ : G →* kˣ) : IsSimpleModule (MonoidAlgebra k G) (chr χ).ρ.asModule := by
  rw [← Representation.irreducible_iff_isSimpleModule_asModule]
  have h : IsSimpleModule k (Fin 1 → k) := isSimpleModule_iff_finrank_eq_one.mpr (by simp)
  refine { exists_pair_ne := ⟨⊥, ⊤, fun h' => ?_⟩, eq_bot_or_eq_top := fun S => ?_ }
  · exact bot_ne_top (α := Submodule k (Fin 1 → k)) (congrArg Subrepresentation.toSubmodule h')
  · rcases eq_bot_or_eq_top S.toSubmodule with h' | h'
    · exact Or.inl (Subrepresentation.toSubmodule_injective h')
    · exact Or.inr (Subrepresentation.toSubmodule_injective h')

theorem sameSS_three {s t u : ℕ} {M : Type} [AddCommGroup M] [Module k M] {π : Representation k G M}
    (C : (Fin s ⊕ Unit) ⊕ Fin t → Ob k G) (e : Fin u ≃ (Fin s ⊕ Unit) ⊕ Fin t)
    (h : SameSS π (((piRep fun a => (C (.inl (.inl a))).ρ).prod (C (.inl (.inr ()))).ρ).prod
      (piRep fun a => (C (.inr a)).ρ))) : SameSS π (piRep fun a => (C (e a)).ρ) := by
  have h1 : SameSS π (piRep fun a => (C a).ρ) := by
    refine h.congr_right
      ((((LinearEquiv.refl k _).prodCongr (LinearEquiv.piUnique k (fun a : Unit => Fin (C (.inl (.inr a))).m → k)).symm).trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s) Unit (fun a => Fin (C (.inl a)).m → k)).symm).prodCongr
          (LinearEquiv.refl k _) |>.trans
        (LinearEquiv.sumPiEquivProdPi k (Fin s ⊕ Unit) (Fin t) (fun a => Fin (C a).m → k)).symm) ?_
    intro g x
    funext a
    rcases a with (a | a) | a <;> rfl
  refine h1.congr_right (LinearEquiv.piCongrLeft k (fun a => Fin (C a).m → k) e).symm ?_
  intro g x
  rfl

end GlobalTheory.Models.ThroughLine

open GlobalTheory.Models.ThroughLine in

theorem GlobalTheory.Models.ModTh.exists_jordanHolder_through_line : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) {r : ℕ} {Dt : TopData n r} (M : ModTh F Dt) (B A₁ : Ob k G) (χ : G →* kˣ) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin 1 → k)) (N : Lats k n B.m), M.Model B N → IsHom A₁ B j → Function.Injective j → IsHom A₁ (chr χ) p → Function.Surjective p → ∃ (s : ℕ) (C : Fin s → Ob k G) (L : ∀ a, Lats k n (C a).m) (a₀ : Fin s), (∀ a, M.Model (C a) (L a)) ∧ (∀ a, IsSimpleModule (MonoidAlgebra k G) (C a).ρ.asModule) ∧ SameSS B.ρ (piRep fun a => (C a).ρ) ∧ (∀ i x, sen ((F.D B).γ i) (N i) x = ∑ a, sen ((F.D (C a)).γ i) (L a i) x) ∧ (⟨C a₀, L a₀⟩ : Σ A : Ob k G, Lats k n A.m) = ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩ := by
  intro k G _ _ l n _ _ _ R F r Dt M B A₁ χ j p N hN hj hji hp hps
  obtain ⟨K, f, hf, hfi, hfe⟩ := exists_ker A₁ (chr χ) p hp
  obtain ⟨Q, q, hq, hqs, hqe⟩ := exists_coker A₁ B j hj
  have hA := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M A₁ B j N hj hji hN
  have hK := GlobalTheory.T.model_preimage_of_injective_finDimRepModelHom F M K A₁ f _ hf hfi hA
  have hL := GlobalTheory.Models.ModTh.model_push_of_surjective F M A₁ (chr χ) p _ hp hps hA
  have hQ := GlobalTheory.Models.ModTh.model_push_of_surjective F M B Q q _ hq hqs hN
  obtain ⟨s, C, L, c1, c2, c3, c4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M K _ hK
  obtain ⟨t, C', L', d1, d2, d3, d4⟩ := GlobalTheory.T.exists_simple_pieces_sen_sum F M Q _ hQ
  obtain ⟨oB, lB, -, cB⟩ := GlobalTheory.T.obj_and_abc_of_model F M B N hN
  obtain ⟨oA, lA, -, cA⟩ := GlobalTheory.T.obj_and_abc_of_model F M A₁ _ hA
  let S : (Fin s ⊕ Unit) ⊕ Fin t → Σ A : Ob k G, Lats k n A.m :=
    Sum.elim (Sum.elim (fun a => ⟨C a, L a⟩) fun _ => ⟨chr χ, F.push A₁ (chr χ) p (F.pre A₁ B j N)⟩)
      fun a => ⟨C' a, L' a⟩
  let e := (Fintype.equivFin ((Fin s ⊕ Unit) ⊕ Fin t)).symm
  have hfl : ∀ m : ℕ, IsFiniteLength k (Fin m → k) := fun m =>
    isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  refine ⟨_, fun a => (S (e a)).1, fun a => (S (e a)).2, e.symm (.inl (.inr ())), fun a => ?_, fun a => ?_,
    ?_, fun i x => ?_, ?_⟩
  · show M.Model (S (e a)).1 (S (e a)).2
    rcases e a with (b | b) | b
    exacts [c1 b, hL, d1 b]
  · show IsSimpleModule (MonoidAlgebra k G) (S (e a)).1.ρ.asModule
    rcases e a with (b | b) | b
    exacts [c2 b, simple_chr χ, d2 b]
  · refine sameSS_three (fun a => (S a).1) e ?_
    exact (SameSS.of_exact hj hq hji hqs hqe (hfl _)).trans
      (((SameSS.of_exact hf hp hfi hps hfe (hfl _)).trans (c3.prod (SameSS.refl _ (hfl _)))).prod d3)
  · rw [Equiv.sum_comp e (fun a => sen ((F.D (S a).1).γ i) ((S a).2 i) x), Fintype.sum_sum_type,
      Fintype.sum_sum_type, Fintype.sum_unique (ι := Unit),
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F A₁ B Q j q N oB hj hq hji hqs hqe i (lB i) (cB i) x,
      GlobalTheory.T.senMultiplicity_additive_exact_sequence F K A₁ (chr χ) f p _ oA hf hp hfi hps hfe i (lA i) (cA i) x, c4, d4]
    rfl
  · show S (e (e.symm _)) = _
    rw [Equiv.apply_symm_apply]
    rfl
