import Mathlib
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnlinkedGL.UnlinkedRealize
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NontrivialOfIrreducible

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.RgGu
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.GenExists

section General

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

theorem isSmooth_subQuot [TopologicalSpace G] [IsTopologicalGroup G] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ)
    (A B : Subrepresentation ρ) : IsSmooth (subQuot A B) := by
  have stab : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (σ : Representation ℂ G W) (w : W),
      ∃ H : Subgroup G, ∀ g, g ∈ H ↔ σ g w = w := by
    intro W _ _ σ w
    refine ⟨{ carrier := {g | σ g w = w}, mul_mem' := ?_, one_mem' := ?_, inv_mem' := ?_ }, fun g => Iff.rfl⟩
    · intro a b ha hb
      replace ha : σ a w = w := ha
      replace hb : σ b w = w := hb
      show σ (a * b) w = w
      rw [map_mul, Module.End.mul_apply, hb, ha]
    · show σ 1 w = w
      rw [map_one, Module.End.one_apply]
    · intro a ha
      replace ha : σ a w = w := ha
      show σ a⁻¹ w = w
      conv_lhs => rw [← ha]
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  intro v
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
  obtain ⟨H₁, hH₁⟩ := stab ρ (x : V)
  obtain ⟨H₂, hH₂⟩ := stab (subQuot A B) (Submodule.Quotient.mk x)
  have hle : H₁ ≤ H₂ := by
    intro g hg
    rw [hH₁] at hg
    rw [hH₂]
    show Submodule.Quotient.mk (A.toRepresentation g x) = Submodule.Quotient.mk x
    congr 1
    exact Subtype.ext hg
  have e₁ : (H₁ : Set G) = {g | ρ g x = x} := Set.ext hH₁
  have e₂ : (H₂ : Set G) = {g | (subQuot A B) g (Submodule.Quotient.mk x) = Submodule.Quotient.mk x} :=
    Set.ext hH₂
  rw [← e₂]
  exact Subgroup.isOpen_mono hle (e₁ ▸ hρ x)

theorem nontrivial_twJacquet_subQuot {ρ : Representation ℂ G V} (N : Subgroup G) (χ : N →* ℂˣ)
    (A B : Subrepresentation ρ) (hB : B.toSubmodule ≤ twKer ρ N χ) (hA : ¬ A.toSubmodule ≤ twKer ρ N χ) :
    Nontrivial (TwJacquet (subQuot A B) N χ) := by
  obtain ⟨a, haA, hak⟩ := SetLike.not_le_iff_exists.mp hA
  let φ : A.toSubmodule →ₗ[ℂ] V ⧸ twKer ρ N χ := (twKer ρ N χ).mkQ ∘ₗ A.toSubmodule.subtype
  have hφ : Submodule.comap A.toSubmodule.subtype B.toSubmodule ≤ LinearMap.ker φ := by
    intro x hx
    rw [LinearMap.mem_ker]
    show Submodule.Quotient.mk (x : V) = (0 : V ⧸ twKer ρ N χ)
    rw [Submodule.Quotient.mk_eq_zero]
    exact hB (Submodule.mem_comap.mp hx)
  let Ψ := (Submodule.comap A.toSubmodule.subtype B.toSubmodule).liftQ φ hφ
  have hker : twKer (subQuot A B) N χ ≤ LinearMap.ker Ψ := by
    apply Submodule.span_le.mpr
    rintro w ⟨n, v, rfl⟩
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ v
    rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_smul]
    show Submodule.Quotient.mk (ρ n (x : V)) - (χ n : ℂ) • Submodule.Quotient.mk (x : V) =
      (0 : V ⧸ twKer ρ N χ)
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_sub, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span ⟨n, (x : V), rfl⟩
  refine ⟨⟨(Submodule.Quotient.mk (Submodule.Quotient.mk ⟨a, haA⟩ :
      A.toSubmodule ⧸ Submodule.comap A.toSubmodule.subtype B.toSubmodule) :
      _ ⧸ twKer (subQuot A B) N χ), 0, ?_⟩⟩
  intro h
  rw [Submodule.Quotient.mk_eq_zero] at h
  have h' := hker h
  rw [LinearMap.mem_ker] at h'
  have h'' : Submodule.Quotient.mk a = (0 : V ⧸ twKer ρ N χ) := h'
  exact hak ((Submodule.Quotient.mk_eq_zero _).mp h'')

end General

theorem exists_generic_subQuot : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (N : ℕ) {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin N) k) V), IsSmooth ρ → GlobalTheory.SmGL.HasFiniteLength ρ →
    IsGenericFor ψ ρ → ∃ A B : Subrepresentation ρ, B ≤ A ∧ (subQuot A B).IsIrreducible ∧
      IsSmooth (subQuot A B) ∧ IsGenericFor ψ (subQuot A B) := by
  intro k _ _ _ _ ψ hψ N V _ _ ρ hρ hfl hgen
  have hNA := isFiniteLength_iff_isNoetherian_isArtinian.mp hfl
  haveI := hNA.1
  haveI := hNA.2
  have hle : ∀ S T : Subrepresentation ρ, S.asSubmodule ≤ T.asSubmodule ↔ S ≤ T := fun S T => Iff.rfl
  have hsm : StrictMono (fun S : Subrepresentation ρ => S.asSubmodule) := fun S T h =>
    lt_of_le_of_ne ((hle S T).mpr h.le)
      (fun he => h.ne (le_antisymm ((hle S T).mp he.le) ((hle T S).mp he.ge)))
  have wfl : WellFounded (fun S T : Subrepresentation ρ => S < T) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_lt)
  have wfg : WellFounded (fun S T : Subrepresentation ρ => T < S) :=
    Subrelation.wf (fun {S T} h => hsm h) (InvImage.wf (fun S : Subrepresentation ρ => S.asSubmodule) wellFounded_gt)
  have hgen' : Nontrivial (V ⧸ twKer ρ (unipB k (Fin N)) (whitChar ψ N)) := hgen
  let T0 : Subrepresentation ρ := ⟨⊤, fun _ _ _ => Submodule.mem_top⟩
  have htop : ¬ T0.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    intro h
    obtain ⟨x, y, hxy⟩ := hgen'.exists_pair_ne
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    apply hxy
    rw [Submodule.Quotient.eq]
    exact h Submodule.mem_top
  obtain ⟨A, hAP, hAmin⟩ := wfl.has_min {A | ¬ A.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N)} ⟨T0, htop⟩
  let Z : Subrepresentation ρ := ⟨⊥, fun g v hv => by
    rw [Submodule.mem_bot] at hv ⊢
    rw [hv, map_zero]⟩
  have hZk : Z.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := bot_le
  have hZA : Z < A := by
    refine lt_of_le_of_ne ?_ ?_
    · intro x hx
      have hx0 : x = 0 := (Submodule.mem_bot ℂ).mp hx
      rw [hx0]
      exact A.toSubmodule.zero_mem
    · intro h
      rw [← h] at hAP
      exact hAP hZk
  obtain ⟨B, hBA, hBmax⟩ := wfg.has_min {B | B < A} ⟨Z, hZA⟩
  have hcov : B ⋖ A := ⟨hBA, fun C hBC hCA => hBmax C hCA hBC⟩
  have hBk : B.toSubmodule ≤ twKer ρ (unipB k (Fin N)) (whitChar ψ N) := by
    by_contra h
    exact hAmin B h hBA
  exact ⟨A, B, hBA.le, GlobalTheory.SmGL.isIrreducible_subQuot hcov, GlobalTheory.CompanionTheory.GenExists.isSmooth_subQuot hρ A B,
    GlobalTheory.CompanionTheory.GenExists.nontrivial_twJacquet_subQuot _ _ A B hBk hAP⟩

end GlobalTheory.CompanionTheory.GenExists

end
