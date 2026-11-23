import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary

noncomputable section

open GlobalTheory.WeilM
open scoped TensorProduct

namespace GlobalTheory.HoweTrivial

theorem chain_bound_of_finiteLength {R M : Type} [Ring R] [AddCommGroup M] [Module R M] (h : IsFiniteLength R M) :
    ∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule R M), StrictMono N → m ≤ L := by
  obtain ⟨h1, h2⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  obtain ⟨l, hl⟩ := ENat.ne_top_iff_exists.1 (Module.length_ne_top (R := R) (M := M))
  refine ⟨l + 1, fun m N hN => ?_⟩
  rcases m with _ | m
  · omega
  have h3 := Order.LTSeries.length_le_krullDim (LTSeries.mk m N hN)
  rw [← Module.coe_length, ← hl] at h3
  have h4 : m ≤ l := by exact_mod_cast h3
  omega

theorem sup_ne_top {H T : Type} [Group H] [AddCommGroup T] [Module ℂ T] (Θ : Representation ℂ H T)
    (h : IsFiniteLength (MonoidAlgebra ℂ H) Θ.asModule)
    (hc : ∀ N N' : Subrepresentation Θ, IsCoatom N → IsCoatom N' → N = N')
    (A B : Subrepresentation Θ) (hA : A ≠ ⊤) (hB : B ≠ ⊤) : A ⊔ B ≠ ⊤ := by
  obtain ⟨h1, -⟩ := isFiniteLength_iff_isNoetherian_isArtinian.1 h
  have hw : WellFoundedGT (Subrepresentation Θ) :=
    (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono.wellFoundedGT
  have hco : IsCoatomic (Subrepresentation Θ) := inferInstance
  obtain ⟨C, hC, hAC⟩ := (eq_top_or_exists_le_coatom A).resolve_left hA
  obtain ⟨C', hC', hBC⟩ := (eq_top_or_exists_le_coatom B).resolve_left hB
  obtain rfl := hc C C' hC hC'
  exact ne_top_of_le_ne_top hC.1 (sup_le hAC hBC)

theorem trivial_irreducible (G : Type) [Group G] : (Representation.trivial ℂ G ℂ).IsIrreducible := by
  have hnt : Nontrivial (Subrepresentation (Representation.trivial ℂ G ℂ)) := by
    refine ⟨⊥, ⊤, fun h => ?_⟩
    have := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top (α := Submodule ℂ ℂ) this
  refine { eq_bot_or_eq_top := fun a => ?_ }
  rcases eq_bot_or_eq_top a.toSubmodule with h | h
  · exact Or.inl (Subrepresentation.toSubmodule_injective h)
  · exact Or.inr (Subrepresentation.toSubmodule_injective h)

theorem trivial_admissible (G : Type) [Group G] [TopologicalSpace G] :
    GlobalTheory.PRep.IsAdmissible (Representation.trivial ℂ G ℂ) := by
  refine ⟨fun v => ?_, fun K _ _ => inferInstance⟩
  simp

section

variable {Y G H T : Type} [Group G] [Group H] [TopologicalSpace Y] [AddCommGroup T] [Module ℂ T]

theorem mem_span_of_eq_zero (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (φ : SB Y) (hφ : p φ = 0) :
    (φ : Y → ℂ) ∈ Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} := by
  set A := Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} with hA
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  refine (hp.2.2 φ).1 hφ (f ∘ₗ A.mkQ ∘ₗ (SB Y).subtype) fun g ψ ψ₁ h => ?_
  have : A.mkQ (ψ₁ : Y → ℂ) = A.mkQ ψ := by
    rw [h]
    exact (Submodule.Quotient.eq A).2 (Submodule.subset_span ⟨g, ψ, ψ.2, rfl⟩)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply, this, Representation.trivial_apply]

def image (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsPairHom om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) : Subrepresentation Θ where
  toSubmodule := (N.comap (SB Y).subtype).map ((TensorProduct.lid ℂ T).toLinearMap ∘ₗ p)
  apply_mem_toSubmodule h := by
    rintro _ ⟨φ, hφ, rfl⟩
    refine ⟨⟨om (1, h) φ, hom _ _ φ.2⟩, hN h _ hφ, ?_⟩
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hp 1 h φ _ rfl]
    generalize p φ = x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => simp
    | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_image_iff (om : G × H →* Module.End ℂ (Y → ℂ)) (hom : ∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y)
    {Θ : Representation ℂ H T} {p : SB Y →ₗ[ℂ] ℂ ⊗[ℂ] T}
    (hp : GlobalTheory.Published.IsBigTheta om (Representation.trivial ℂ G ℂ) Θ p) (N : Submodule ℂ (Y → ℂ))
    (hA : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N)
    (hN : ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) (φ : SB Y) :
    TensorProduct.lid ℂ T (p φ) ∈ (image om hom hp.1 N hN).toSubmodule ↔ (φ : Y → ℂ) ∈ N := by
  refine ⟨?_, fun h => ⟨φ, h, rfl⟩⟩
  rintro ⟨ψ, hψ, e⟩
  have e1 : p ψ = p φ := (TensorProduct.lid ℂ T).injective e
  have e2 : p (φ - ψ) = 0 := by rw [map_sub, e1, sub_self]
  have h3 := N.add_mem (hA (mem_span_of_eq_zero om hom hp _ e2)) hψ
  simpa using h3

end

theorem chain_bounded_and_sup_proper :
    ∀ {Y G H : Type} [Group G] [Group H] [TopologicalSpace G] [TopologicalSpace H] [TopologicalSpace Y]
    (om : G × H →* Module.End ℂ (Y → ℂ)), GlobalTheory.Published.HoweDualityFor om → (∀ x, ∀ φ ∈ SB Y, om x φ ∈ SB Y) →
    (∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (Y → ℂ)), StrictMono N →
      (∀ i, Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N i ∧ N i ≤ SB Y ∧
        ∀ h, ∀ φ ∈ N i, om (1, h) φ ∈ N i) → m ≤ L) ∧
    ∀ N N' : Submodule ℂ (Y → ℂ),
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧ ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N) →
      (Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N' ∧ N' ≤ SB Y ∧ ∀ h, ∀ φ ∈ N', om (1, h) φ ∈ N') →
      N ≠ SB Y → N' ≠ SB Y → N ⊔ N' ≠ SB Y := by
  intro Y G H _ _ _ _ _ om hH hom
  obtain ⟨⟨T, _, _, Θ, p, hp, -, hfl, hco⟩, -⟩ :=
    hH ℂ (Representation.trivial ℂ G ℂ) (trivial_irreducible G) (trivial_admissible G)
  constructor
  · obtain ⟨L, hL⟩ := chain_bound_of_finiteLength hfl
    refine ⟨L, fun m N hN hs => hL m (fun i => Subrepresentation.subrepresentationSubmoduleOrderIso
      (image om hom hp.1 (N i) (hs i).2.2)) fun i j hij => ?_⟩
    refine (Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := Θ)).strictMono ?_
    have hlt := hN hij
    refine lt_of_le_of_ne ?_ fun e => hlt.not_ge fun φ hφ => ?_
    · exact Submodule.map_mono (Submodule.comap_mono hlt.le)
    · have h1 := (mem_image_iff om hom hp (N j) (hs j).1 (hs j).2.2 ⟨φ, (hs j).2.1 hφ⟩).2 hφ
      rw [← e] at h1
      exact (mem_image_iff om hom hp (N i) (hs i).1 (hs i).2.2 _).1 h1
  · have key : ∀ (N : Submodule ℂ (Y → ℂ))
        (hs : Submodule.span ℂ {z | ∃ g, ∃ φ ∈ SB Y, z = om (g, 1) φ - φ} ≤ N ∧ N ≤ SB Y ∧
          ∀ h, ∀ φ ∈ N, om (1, h) φ ∈ N), N ≠ SB Y → image om hom hp.1 N hs.2.2 ≠ ⊤ := by
      intro N hs hne e
      refine hne (le_antisymm hs.2.1 fun φ hφ => ?_)
      refine (mem_image_iff om hom hp N hs.1 hs.2.2 ⟨φ, hφ⟩).1 ?_
      rw [e]
      exact Submodule.mem_top
    intro N N' hs hs' hne hne' e
    refine sup_ne_top Θ hfl hco _ _ (key N hs hne) (key N' hs' hne') ?_
    refine Subrepresentation.toSubmodule_injective (eq_top_iff.2 fun t _ => ?_)
    obtain ⟨φ, hφ⟩ := hp.2.1 ((TensorProduct.lid ℂ T).symm t)
    have hm : (φ : Y → ℂ) ∈ N ⊔ N' := by rw [e]; exact φ.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hm
    have e1 : φ = (⟨a, hs.2.1 ha⟩ : SB Y) + ⟨b, hs'.2.1 hb⟩ := Subtype.ext hab.symm
    have e2 : t = TensorProduct.lid ℂ T (p ⟨a, hs.2.1 ha⟩) + TensorProduct.lid ℂ T (p ⟨b, hs'.2.1 hb⟩) := by
      rw [← map_add, ← map_add, ← e1, hφ, LinearEquiv.apply_symm_apply]
    rw [e2]
    exact Submodule.add_mem_sup ⟨_, ha, rfl⟩ ⟨_, hb, rfl⟩

end GlobalTheory.HoweTrivial

end
