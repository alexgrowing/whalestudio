import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSplitFinMulSplitInf
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNeZeroWeightTensorIntertwiningAutRepStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpanInfinitePlacesWeightRepresentationEqTopStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDefiniteUnitaryRationalPointFiniteAndInfinStatement

open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.BCT.TrKer
open scoped Classical TensorProduct

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def infHom (lam : InfinitePlace E → DomWeight n) : Submodule ℂ (Wsp lam →ₗ[ℂ] (UA E n → ℂ)) where
  carrier := {T | ∀ x ∈ infU E n, ∀ w, T (wInf lam x w) = RU E n x (T w)}
  add_mem' ha hb x hx w := by
    simp only [LinearMap.add_apply, ha x hx, hb x hx, map_add]
  zero_mem' x _ w := by simp
  smul_mem' c T hT x hx w := by
    simp only [LinearMap.smul_apply, hT x hx, map_smul]

theorem RU_mul (a b : UA E n) (φ : UA E n → ℂ) : RU E n (a * b) φ = RU E n a (RU E n b φ) := by
  rw [map_mul]; rfl

theorem comp_mem_infHom (lam : InfinitePlace E → DomWeight n) {T : Wsp lam →ₗ[ℂ] (UA E n → ℂ)} (hT : T ∈ infHom lam)
    (k : finU E n) : RU E n k.1 ∘ₗ T ∈ infHom lam := by
  intro x hx w
  simp only [LinearMap.comp_apply, hT x hx, ← RU_mul, GlobalTheory.DefU.fin_mul_inf k.2 hx]

theorem exists_op (lam : InfinitePlace E → DomWeight n) (A : Module.End ℂ (Wsp lam)) :
    ∃ P : Module.End ℂ (UA E n → ℂ), ∀ T ∈ infHom lam, ∀ w, T (A w) = P (T w) := by
  have hA : A ∈ Submodule.span ℂ (Set.range fun x : infU E n => wInf lam (x : UA E n)) := by
    rw [GlobalTheory.T.span_infinitePlacesWeightRepresentation_eq_top E n lam]; exact Submodule.mem_top
  induction hA using Submodule.span_induction with
  | mem A h =>
    obtain ⟨x, rfl⟩ := h
    exact ⟨RU E n x.1, fun T hT w => hT x.1 x.2 w⟩
  | zero => exact ⟨0, fun T _ w => by simp⟩
  | add A B _ _ hA hB =>
    obtain ⟨P, hP⟩ := hA
    obtain ⟨Q, hQ⟩ := hB
    exact ⟨P + Q, fun T hT w => by simp [hP T hT, hQ T hT]⟩
  | smul c A _ hA =>
    obtain ⟨P, hP⟩ := hA
    exact ⟨c • P, fun T hT w => by simp [hP T hT]⟩

theorem eq_zero_of_sum (lam : InfinitePlace E → DomWeight n) {ι : Type} [Fintype ι] (b : Module.Basis ι ℂ (Wsp lam))
    (T : ι → Wsp lam →ₗ[ℂ] (UA E n → ℂ)) (hT : ∀ j, T j ∈ infHom lam) (h : ∑ j, T j (b j) = 0) (k : ι) :
    T k = 0 := by
  refine b.ext fun m => ?_
  obtain ⟨P, hP⟩ := exists_op lam ((b.coord k).smulRight (b m))
  have := congrArg P h
  rw [map_sum, map_zero] at this
  rw [LinearMap.zero_apply, ← this]
  rw [Finset.sum_eq_single k]
  · rw [← hP _ (hT k)]; simp
  · intro j _ hj
    rw [← hP _ (hT j)]
    simp [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply, hj]
  · simp

end GlobalTheory.BCT.TrKer

namespace GlobalTheory.BCT.TrKer

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem mem_span_values (lam : InfinitePlace E → DomWeight n) (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π)
    (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v)) {φ : UA E n → ℂ} (hφ : φ ∈ π) :
    φ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ} := by
  set Sv := Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ}
  have hle : Sv ≤ π := Submodule.span_le.2 (by rintro _ ⟨T, -, hT, w, rfl⟩; exact hT w)
  have hst : ∀ g, ∀ ψ ∈ Sv, RU E n g ψ ∈ Sv := by
    intro g ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      rw [eq_splitFin_mul_splitInf g, RU_mul, ← hT _ (splitInf E n g).2]
      exact Submodule.subset_span ⟨_, comp_mem_infHom lam hT (splitFin E n g),
        fun w' => hπ.stable _ _ (hTπ w'), _, rfl⟩
    | zero => simp
    | add a c _ _ ha hc => rw [map_add]; exact add_mem ha hc
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  obtain ⟨T, hT0, hTπ, hT⟩ := GlobalTheory.T.exists_ne_zero_weightTensor_intertwining_autRep E n lam π hπ hW
  obtain ⟨w, hw⟩ := DFunLike.ne_iff.1 hT0
  rcases hπ.irred Sv hle hst with h | h
  · have hm : T w ∈ Sv := Submodule.subset_span ⟨T, hT, hTπ, w, rfl⟩
    rw [h, Submodule.mem_bot] at hm
    exact absurd hm hw
  · rw [h]; exact hφ

theorem mem_range_of_mem (S : Set (Pl E)) (K' : ∀ w : Pl E, Subgroup (UL n w)) (lam : InfinitePlace E → DomWeight n)
    (π : Submodule ℂ (UA E n → ℂ)) (hπ : IsAutRepU π) (hW : ∀ v : InfinitePlace E, HasWeightAt π v.embedding (lam v))
    {φ : UA E n → ℂ} (hφ : φ ∈ π) (hfix : φ ∈ fixed (RF E n) (globLev S K')) :
    φ ∈ LinearMap.range (Phi S lam K') := by
  classical
  let b := Module.finBasis ℂ (Wsp lam)
  have hdec : ∀ ψ ∈ Submodule.span ℂ {ψ | ∃ T ∈ infHom lam, (∀ w, T w ∈ π) ∧ ∃ w, T w = ψ},
      ∃ T : Fin (Module.finrank ℂ (Wsp lam)) → (Wsp lam →ₗ[ℂ] (UA E n → ℂ)),
        (∀ j, T j ∈ infHom lam) ∧ (∀ j w, T j w ∈ π) ∧ ψ = ∑ j, T j (b j) := by
    intro ψ hψ
    induction hψ using Submodule.span_induction with
    | mem ψ h =>
      obtain ⟨T, hT, hTπ, w, rfl⟩ := h
      refine ⟨fun j => b.repr w j • T, fun j => Submodule.smul_mem _ _ hT, fun j w' => π.smul_mem _ (hTπ w'), ?_⟩
      calc T w = T (∑ j, b.repr w j • b j) := by rw [b.sum_repr]
        _ = ∑ j, (b.repr w j • T) (b j) := by simp only [map_sum, map_smul, LinearMap.smul_apply]
    | zero => exact ⟨0, fun _ => zero_mem _, fun _ _ => π.zero_mem, by simp⟩
    | add a c _ _ ha hc =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      obtain ⟨C, hC, hCπ, rfl⟩ := hc
      exact ⟨A + C, fun j => add_mem (hA j) (hC j), fun j w => π.add_mem (hAπ j w) (hCπ j w),
        by simp [Finset.sum_add_distrib]⟩
    | smul c a _ ha =>
      obtain ⟨A, hA, hAπ, rfl⟩ := ha
      exact ⟨c • A, fun j => Submodule.smul_mem _ c (hA j), fun j w => π.smul_mem c (hAπ j w),
        by simp [Finset.smul_sum]⟩
  obtain ⟨T, hT, hTπ, rfl⟩ := hdec φ (mem_span_values lam π hπ hW hφ)
  have hfixT : ∀ k ∈ globLev S K', ∀ j, RU E n k.1 ∘ₗ T j = T j := by
    intro k hk j
    have h1 : RU E n k.1 (∑ j, T j (b j)) = ∑ j, T j (b j) := by
      have := hfix ⟨k, hk⟩
      simpa [RF] using this
    have h2 : ∑ i, (RU E n k.1 ∘ₗ T i - T i) (b i) = 0 := by
      simp only [LinearMap.sub_apply, LinearMap.comp_apply, Finset.sum_sub_distrib, ← map_sum, h1, sub_self]
    exact sub_eq_zero.1 (eq_zero_of_sum lam b _ (fun i => sub_mem (comp_mem_infHom lam (hT i) k) (hT i)) h2 j)
  obtain ⟨F, hFa⟩ : ∃ F : Fin (Module.finrank ℂ (Wsp lam)) → finU E n → Module.Dual ℂ (Wsp lam),
      ∀ j x w, F j x w = T j w x.1 :=
    ⟨fun j x => LinearMap.proj (R := ℂ) (φ := fun _ : UA E n => ℂ) x.1 ∘ₗ T j, fun _ _ _ => rfl⟩
  have hphi : ∀ j, phiFun lam (F j) = T j := by
    intro j
    refine LinearMap.ext fun w => funext fun g => ?_
    rw [phiFun_apply, hFa]
    have hg := eq_splitFin_mul_splitInf g
    have hw : wInf lam g = wInf lam (splitInf E n g).1 := by
      conv_lhs => rw [hg]
      rw [map_mul, wInf_fin, one_mul]
    rw [hw, hT j _ (splitInf E n g).2]
    change T j w ((splitFin E n g).1 * (splitInf E n g).1) = T j w g
    rw [← hg]
  have hF : ∀ j, F j ∈ vecM S lam K' := by
    intro j
    refine ⟨fun γ x => ?_, fun k hk x => ?_⟩
    · refine LinearMap.ext fun w => ?_
      rw [LinearMap.dualMap_apply, hFa, hFa]
      obtain ⟨r, hr, hrf, hrc⟩ := GlobalTheory.T.exists_definiteUnitaryRationalPoint_finite_and_infinite_parts E n γ
      set i := splitInf E n r
      have hri : r = (finPt γ).1 * i.1 := by rw [← hrf]; exact eq_splitFin_mul_splitInf r
      have hc : ∀ v : InfinitePlace E, cEmb v.embedding (i.1⁻¹) = GeneralLinearGroup.map v.embedding (γ⁻¹).1 := by
        intro v
        have : i.1⁻¹ = r⁻¹ * (finPt γ).1 := by rw [hri]; group
        rw [this, map_mul, map_inv, hrc v, cEmb_fin, mul_one, Subgroup.coe_inv, map_inv]
      have hwi : wInf lam i.1⁻¹ = wAt lam γ⁻¹ := by
        change PiTensorProduct.map (fun v => GlobalTheory.Branching.sqRep ℂ n (lam v) (cEmb v.embedding i.1⁻¹)) = _
        unfold wAt
        simp only [hc]
      have hl := (hπ.aut _ (hTπ j w)).left r hr (i.1⁻¹ * x.1)
      rw [← hwi, hT j _ (inv_mem i.2)]
      change T j w ((finPt γ).1 * x.1) = T j w (x.1 * i.1⁻¹)
      rw [GlobalTheory.DefU.fin_mul_inf x.2 (inv_mem i.2), ← hl, hri]
      congr 1
      group
    · refine LinearMap.ext fun w => ?_
      rw [hFa, hFa]
      change T j w (x.1 * k.1) = T j w x.1
      exact congrFun (LinearMap.congr_fun (hfixT k hk j) w) x.1
  refine ⟨∑ j, ⟨F j, hF j⟩ ⊗ₜ b j, ?_⟩
  simp [map_sum, Phi_tmul, hphi]

theorem forms_le_range : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ (lam : InfinitePlace E → DomWeight n) (K' : ∀ w : Pl E, Subgroup (UL n w)), IsLevelFam (fun w : Pl E => MonoidHom.id (UL n w)) (KL n) K' → forms S lam K' ≤ LinearMap.range (Phi S lam K') := by
  intro E _ _ _ _ n _ S _ lam K' _
  refine iSup_le fun π => iSup_le fun hπ => ?_
  rintro φ ⟨hφ, hfix⟩
  exact mem_range_of_mem S K' lam π hπ.1 hπ.2 hφ hfix

end GlobalTheory.BCT.TrKer

end
