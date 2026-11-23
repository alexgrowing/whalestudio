import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BrauerDegreeZero
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfRepresentation
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldRestrictClassFunctionOne
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducible
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MemVirtualCharactersIffSubCharacters
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IrreducibleCharacterLinearOrInducedAbelianByPrim
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.VirtualCharactersMulComapConjIndLinear
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IndMulClassFunEqIndMulRestrict
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.OneMemClosureInducedCentralByPrimePower
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionFromSubgroupTransStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedClassFunctionMemInducedDegreeOneCharDiffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InducedOneSubIndexMemDegreeOneCharacterDiffStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLtCommutatorMemOfNeTopStatement

noncomputable section
open GlobalTheory.BI

namespace GlobalTheory.BrauerZero

theorem step_ind_ind {G : Type} [Group G] [Finite G] (K A : Subgroup G) (hKA : K ≤ A) (ψ : K → ℂ) :
    ind A (ind (K.subgroupOf A) (fun k => ψ ⟨((k : A) : G), k.2⟩)) = ind K ψ :=
  GlobalTheory.T.inducedClassFunctionFromSubgroup_trans K A hKA ψ

theorem inducedClassFunction_mem_degreeOneCharacterDiff {G : Type} [Group G] [Finite G] (E : Subgroup G) (f : E → ℂ) (hf : f ∈ D0 E) :
    ind E f ∈ D0 G :=
  GlobalTheory.T.inducedClassFunction_mem_inducedDegreeOneCharDiff E f hf

theorem step_ind_one_sub_index_of_comm {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hc : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G :=
  GlobalTheory.T.induced_one_sub_index_mem_degreeOneCharacterDiff K hc

theorem step_exists_gt_commutators_le {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] (K : Subgroup G)
    (hK : K ≠ ⊤) : ∃ A : Subgroup G, K < A ∧ ∀ a ∈ A, ∀ b ∈ A, a * b * a⁻¹ * b⁻¹ ∈ K :=
  GlobalTheory.T.exists_gt_commutator_mem_of_ne_whole K hK

theorem ind_one_sub_index_mem_degreeOneDiff_nilpotent {G : Type} [Group G] [Finite G] [Group.IsNilpotent G] :
    ∀ (n : ℕ) (K : Subgroup G), K.index ≤ n →
      ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  intro n
  induction n with
  | zero => intro K hK; have := K.index_ne_zero_of_finite; omega
  | succ n ih =>
    intro K hK
    by_cases hKt : K = ⊤
    · subst hKt
      have e : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => 1 :=
        ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
      rw [e, Subgroup.index_top]
      simp
    · obtain ⟨A, hKA, hc⟩ := step_exists_gt_commutators_le K hKt
      have h1 : ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ)) ∈ D0 A :=
        step_ind_one_sub_index_of_comm (K.subgroupOf A) (fun a b => by
          rw [Subgroup.mem_subgroupOf]; simpa using hc a a.2 b b.2)
      have h2 := inducedClassFunction_mem_degreeOneCharacterDiff A _ h1
      have hrel := Subgroup.relIndex_mul_index hKA.le
      have hlt : 1 < K.relIndex A := by
        have h0 : (K.subgroupOf A).index ≠ 0 := Subgroup.index_ne_zero_of_finite
        have h1' : (K.subgroupOf A).index ≠ 1 := fun h =>
          hKA.not_ge (Subgroup.subgroupOf_eq_top.1 (Subgroup.index_eq_one.1 h))
        unfold Subgroup.relIndex; omega
      have hA0 : A.index ≠ 0 := A.index_ne_zero_of_finite
      have h3 := ih A (by nlinarith)
      have t := step_ind_ind K A hKA.le (fun _ => (1 : ℂ))
      have key : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) =
          ind A (ind (K.subgroupOf A) (fun _ => (1 : ℂ)) - (fun _ => ((K.subgroupOf A).index : ℂ))) +
            ((K.subgroupOf A).index : ℤ) • (ind A (fun _ => (1 : ℂ)) - (fun _ => (A.index : ℂ))) := by
        rw [ind_sub, ← t, ← hrel]
        funext g
        have hc1 := ind_const A (((K.subgroupOf A).index : ℕ) : ℂ) g
        simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, hc1, zsmul_eq_mul]
        simp only [Pi.mul_apply, Pi.sub_apply, Pi.intCast_apply, Pi.natCast_apply, Int.cast_natCast]
        simp only [Subgroup.relIndex]
        push_cast
        ring
      rw [key]
      exact add_mem h2 (zsmul_mem h3 _)

theorem mem_degreeOneDiff_of_forall_centralByPrime (G : Type) [Group G] [Finite G] (f : G → ℂ)
    (hf : ∀ g x : G, f (x⁻¹ * g * x) = f g)
    (h : ∀ E : Subgroup G, (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) →
      ∀ ψ ∈ Virt ℂ ℂ E, ind E (fun e => ψ e * f e) ∈ D0 G) : f ∈ D0 G := by
  have key : ∀ φ ∈ AddSubgroup.closure {φ : G → ℂ | ∃ (E : Subgroup G) (ψ : E → ℂ),
      (∃ l : ℕ, l.Prime ∧ ∀ y : E, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center E) ∧
        ψ ∈ Virt ℂ ℂ E ∧ φ = ind E ψ}, φ * f ∈ D0 G := by
    intro φ hφ
    induction hφ using AddSubgroup.closure_induction with
    | mem φ hφ =>
      obtain ⟨E, ψ, hl, hψ, rfl⟩ := hφ
      rw [ind_mul_classFun_eq_ind_mul_restrict G E ψ f hf]
      exact h E hl ψ hψ
    | zero => rw [zero_mul]; exact zero_mem _
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | neg a _ ha => rw [neg_mul]; exact neg_mem ha
  simpa using key 1 (one_mem_closure_ind_centralByPrime G)

theorem central_case (G : Type) [Group G] [Finite G]
    (hG : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G)
    (IH : ∀ T : Subgroup G, T ≠ ⊤ → ∀ f ∈ Virt ℂ ℂ T, f 1 = 0 → f ∈ D0 T) :
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  classical
  obtain ⟨l, hl, hc⟩ := hG
  have : Fact l.Prime := ⟨hl⟩
  have hq : IsPGroup l (G ⧸ Subgroup.center G) := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨j, hj⟩ := hc y
    exact ⟨j, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hj⟩
  have := hq.isNilpotent
  haveI : Group.IsNilpotent G :=
    Subgroup.isNilpotent_of_ker_le_center (QuotientGroup.mk' (Subgroup.center G)) (by simp)
  have hab : AbByP G := ⟨l, hl, Subgroup.center G, inferInstance,
    fun a _ b hb => Subgroup.mem_center_iff.1 hb a, fun g => hc g⟩
  have C : ∀ χ : G → ℂ, IsChar ℂ ℂ χ → χ - (fun _ => χ 1) ∈ D0 G := by
    refine isChar_induction ℂ ℂ G (fun χ => χ - (fun _ => χ 1) ∈ D0 G) ?_ ?_
    · have e : (0 : G → ℂ) - (fun _ => (0 : G → ℂ) 1) = 0 := by funext g; simp
      rw [e]; exact zero_mem _
    · intro φ c hφ _ hQ
      have e : (φ + c) - (fun _ => (φ + c) 1) = (φ - fun _ => φ 1) + (c - fun _ => c 1) := by
        funext g; simp only [Pi.add_apply, Pi.sub_apply]; ring
      rw [e]
      refine add_mem ?_ hQ
      rcases irrChar_linear_or_induced ℂ G φ hab hφ with ⟨lam, hlam⟩ | ⟨T, hT, ψ, hψ, rfl⟩
      · have hφc : IsChar ℂ ℂ φ := by obtain ⟨n, ρ, -, h⟩ := hφ; exact ⟨n, ρ, h⟩
        have hcl := (isChar_restrict_conj_one ℂ ℂ G φ hφc).2.1
        refine AddSubgroup.subset_closure ⟨⊤, lam.comp (⊤ : Subgroup G).subtype, ?_⟩
        have e1 : (fun h : (⊤ : Subgroup G) => ((lam.comp (⊤ : Subgroup G).subtype h : ℂˣ) : ℂ)) =
            fun h : (⊤ : Subgroup G) => φ (h : G) := by
          funext h; simp [hlam]
        rw [e1, ind_top φ hcl, ind_top (fun _ : G => (1 : ℂ)) (fun _ _ => rfl)]
        funext g; simp [hlam]
      · obtain ⟨n, hn, -⟩ := (isChar_restrict_conj_one ℂ ℂ T ψ hψ).2.2
        have hψV : ψ - (fun _ => ψ 1) ∈ Virt ℂ ℂ T := by
          refine sub_mem (isChar_mem_virt_complex hψ) ?_
          have e2 : (fun _ : T => ψ 1) = n • (fun _ : T => (1 : ℂ)) := by funext; simp [hn]
          rw [e2]; exact nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ T)) n
        have h1 := inducedClassFunction_mem_degreeOneCharacterDiff T _ (IH T hT _ hψV (by simp))
        have h2 := ind_one_sub_index_mem_degreeOneDiff_nilpotent T.index T le_rfl
        have key : ind T ψ - (fun _ => ind T ψ 1) = ind T (ψ - fun _ => ψ 1) +
            (n : ℤ) • (ind T (fun _ => (1 : ℂ)) - fun _ => (T.index : ℂ)) := by
          rw [ind_sub]; funext g
          simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, ind_apply_one, hn, ind_const T (n : ℂ) g,
            zsmul_eq_mul, Pi.mul_apply, Pi.intCast_apply, Pi.natCast_apply]
          push_cast; ring
        rw [key]; exact add_mem h1 (zsmul_mem h2 _)
  intro f hf hf1
  obtain ⟨a, b, ha, hb, rfl⟩ := (mem_virt_iff_sub ℂ ℂ G f).1 hf
  have hab1 : a 1 = b 1 := by simpa [sub_eq_zero] using hf1
  have e : a - b = (a - fun _ => a 1) - (b - fun _ => b 1) := by funext g; simp [hab1]
  rw [e]; exact sub_mem (C a ha) (C b hb)

theorem virtualCharacter_degreeZero_mem_degreeOneDiff : ∀ (n : ℕ) (G : Type) [Group G] [Finite G], Nat.card G ≤ n →
    ∀ f ∈ Virt ℂ ℂ G, f 1 = 0 → f ∈ D0 G := by
  intro n
  induction n with
  | zero => intro G _ _ hG; have := Nat.card_pos (α := G); omega
  | succ n ih =>
    intro G _ _ hG f hf hf1
    have hcl : ∀ g x : G, f (x⁻¹ * g * x) = f g := (virt_mul_comap_conj_ind_linear G).2.2.1 f hf
    refine mem_degreeOneDiff_of_forall_centralByPrime G f hcl ?_
    intro E hE ψ hψ
    have hV : (fun e : E => ψ e * f e) ∈ Virt ℂ ℂ E :=
      (virt_mul_comap_conj_ind_linear E).1 ψ hψ _
        ((virt_mul_comap_conj_ind_linear G).2.1 f hf E E.subtype)
    have h1 : (fun e : E => ψ e * f e) 1 = 0 := by simp [hf1]
    by_cases hlt : Nat.card E < Nat.card G
    · exact inducedClassFunction_mem_degreeOneCharacterDiff E _ (ih E (by omega) _ hV h1)
    · have htop : E = ⊤ := (Subgroup.card_eq_iff_eq_top E).1
        (le_antisymm (Subgroup.card_le_card_group E) (not_lt.1 hlt))
      have hVG : ind E (fun e => ψ e * f e) ∈ Virt ℂ ℂ G :=
        (virt_mul_comap_conj_ind_linear G).2.2.2.1 E _ hV
      have hG1 : ind E (fun e => ψ e * f e) 1 = 0 := by rw [ind_apply_one]; simp [hf1]
      subst htop
      obtain ⟨l, hl, hc⟩ := hE
      have hG' : ∃ l : ℕ, l.Prime ∧ ∀ y : G, ∃ j : ℕ, y ^ l ^ j ∈ Subgroup.center G := by
        refine ⟨l, hl, fun y => ?_⟩
        obtain ⟨j, hj⟩ := hc ⟨y, Subgroup.mem_top y⟩
        refine ⟨j, Subgroup.mem_center_iff.2 fun z => ?_⟩
        have := Subgroup.mem_center_iff.1 hj ⟨z, Subgroup.mem_top z⟩
        simpa using congrArg Subtype.val this
      refine central_case G hG' (fun T hT g hg hg1 => ih T ?_ g hg hg1) _ hVG hG1
      have := Subgroup.card_le_card_group T
      have hne : Nat.card T ≠ Nat.card G := fun h => hT ((Subgroup.card_eq_iff_eq_top T).1 h)
      omega

theorem exists_sum_induced_characters_of_mem_degreeOneDiff {G : Type} [Group G] [Fintype G] {f : G → ℂ} (hf : f ∈ D0 G) :
    ∃ (r : ℕ) (H : Fin r → Subgroup G) (χ : ∀ i, H i →* ℂˣ) (c : Fin r → ℤ), ∀ g : G,
      f g = ∑ i, (c i : ℂ) * (GlobalTheory.Published.indFun (H i) (fun x => (χ i x : ℂ)) g -
        GlobalTheory.Published.indFun (H i) (fun _ => 1) g) := by
  rw [D0, ← Submodule.span_int_eq_addSubgroupClosure, Submodule.mem_toAddSubgroup,
    Submodule.mem_span_set'] at hf
  obtain ⟨n, c, s, hs⟩ := hf
  choose H χ hHχ using fun i => (s i).2
  refine ⟨n, H, χ, c, fun g => ?_⟩
  rw [← hs, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Pi.smul_apply, hHχ i, zsmul_eq_mul, indFun_eq_ind, indFun_eq_ind]
  rfl

theorem brauerDegreeZero : GlobalTheory.Published.BrauerDegreeZero := by
  intro G _ _ V _ _ _ ρ
  classical
  have hchar := (isChar_and_isIrrChar_of_rep ℂ ℂ G V ρ).1
  have hV : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) ∈ Virt ℂ ℂ G := by
    have e : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) =
        (fun g => algebraMap ℂ ℂ (ρ.character g)) - (Module.finrank ℂ V) • (fun _ => (1 : ℂ)) := by
      funext g; simp [Representation.character]
    rw [e]
    exact sub_mem (isChar_mem_virt_complex hchar)
      (nsmul_mem (isChar_mem_virt_complex (isChar_one ℂ ℂ G)) _)
  have h1 : (fun g => LinearMap.trace ℂ V (ρ g) - (Module.finrank ℂ V : ℂ)) 1 = 0 := by simp
  exact exists_sum_induced_characters_of_mem_degreeOneDiff (virtualCharacter_degreeZero_mem_degreeOneDiff _ G le_rfl _ hV h1)

end GlobalTheory.BrauerZero

end
