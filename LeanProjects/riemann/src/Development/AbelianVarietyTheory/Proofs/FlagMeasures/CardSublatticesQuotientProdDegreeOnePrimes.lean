import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime

open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.SublatCount

section Abstract

variable {O N : Type} [CommRing O] [AddCommGroup N] [Module O N]

def Ker (I : Ideal O) (N : Type) [AddCommGroup N] [Module O N] : Set (Submodule O N) :=
  {L | ∃ f : N →ₗ[O] O ⧸ I, Function.Surjective f ∧ LinearMap.ker f = L}

theorem encard_eq_of_bijOn {α β : Type} {s : Set α} {t : Set β} {f : α → β} (h : Set.BijOn f s t) :
    s.encard = t.encard := by
  rw [← h.image_eq, h.injOn.encard_image]

theorem mem_ker_iff (I : Ideal O) (L : Submodule O N) :
    L ∈ Ker I N ↔ Nonempty ((N ⧸ L) ≃ₗ[O] (O ⧸ I)) := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    exact ⟨f.quotKerEquivOfSurjective hf⟩
  · rintro ⟨e⟩
    refine ⟨e.toLinearMap ∘ₗ L.mkQ, e.surjective.comp L.mkQ_surjective, ?_⟩
    rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem smul_quot {I : Ideal O} {c : O} (hc : c ∈ I) (y : O ⧸ I) : c • y = 0 := by
  have : algebraMap O (O ⧸ I) c = 0 := Ideal.Quotient.eq_zero_iff_mem.2 hc
  rw [Algebra.smul_def, this, zero_mul]

theorem smul_mem {I : Ideal O} {L : Submodule O N} (h : L ∈ Ker I N) {c : O} (hc : c ∈ I)
    (x : N) : c • x ∈ L := by
  obtain ⟨f, -, rfl⟩ := h
  rw [LinearMap.mem_ker, map_smul, smul_quot hc]

noncomputable def crt (I J : Ideal O) (h : IsCoprime I J) :
    (O ⧸ I * J) ≃ₗ[O] (O ⧸ I) × (O ⧸ J) :=
  { Ideal.quotientMulEquivQuotientProd I J h with
    map_smul' := fun c x => by
      obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
      rfl }

theorem encard_mul (I J : Ideal O) (h : IsCoprime I J) :
    (Ker (I * J) N).encard = (Ker I N).encard * (Ker J N).encard := by
  obtain ⟨a, ha, b, hb, hab⟩ := Ideal.isCoprime_iff_exists.1 h
  have key : ∀ {I J : Ideal O} {a b : O}, a ∈ I → b ∈ J → a + b = 1 →
      ∀ {L₁ L₂ L₁' L₂' : Submodule O N}, L₂ ∈ Ker J N → L₁' ∈ Ker I N →
      L₁ ⊓ L₂ = L₁' ⊓ L₂' → L₁ ≤ L₁' := by
    intro I J a b ha hb hab L₁ L₂ L₁' L₂' h2 h1' he x hx
    have h3 : b • x ∈ L₁ ⊓ L₂ := ⟨L₁.smul_mem b hx, smul_mem h2 hb x⟩
    rw [he] at h3
    have := L₁'.add_mem (smul_mem h1' ha x) h3.1
    rwa [← add_smul, hab, one_smul] at this
  rw [← Set.encard_prod]
  symm
  refine encard_eq_of_bijOn (f := fun p => p.1 ⊓ p.2) ⟨?_, ?_, ?_⟩
  · rintro ⟨_, _⟩ ⟨⟨f, hf, rfl⟩, ⟨g, hg, rfl⟩⟩
    refine ⟨(crt I J h).symm.toLinearMap ∘ₗ f.prod g, (crt I J h).symm.surjective.comp ?_, ?_⟩
    · rintro ⟨x, y⟩
      obtain ⟨u, rfl⟩ := hf x
      obtain ⟨v, rfl⟩ := hg y
      refine ⟨b • u + a • v, Prod.ext ?_ ?_⟩
      · change f (b • u + a • v) = f u
        rw [map_add, map_smul, map_smul, smul_quot ha, ← smul_quot ha (f u), ← add_smul,
          add_comm, hab, one_smul]
      · change g (b • u + a • v) = g v
        rw [map_add, map_smul, map_smul, smul_quot hb, ← smul_quot hb (g v), ← add_smul,
          add_comm, hab, one_smul]
    · rw [LinearEquiv.ker_comp, LinearMap.ker_prod]
  · rintro ⟨L₁, L₂⟩ ⟨h1, h2⟩ ⟨L₁', L₂'⟩ ⟨h1', h2'⟩ he
    have he : L₁ ⊓ L₂ = L₁' ⊓ L₂' := he
    have he' : L₂ ⊓ L₁ = L₂' ⊓ L₁' := by rw [inf_comm, he, inf_comm]
    have hba : b + a = 1 := by rw [add_comm, hab]
    exact Prod.ext (le_antisymm (key ha hb hab h2 h1' he) (key ha hb hab h2' h1 he.symm))
      (le_antisymm (key hb ha hba h1 h2' he') (key hb ha hba h1' h2 he'.symm))
  · rintro _ ⟨f, hf, rfl⟩
    let g := (crt I J h).toLinearMap ∘ₗ f
    have hg : Function.Surjective g := (crt I J h).surjective.comp hf
    refine ⟨(LinearMap.ker (LinearMap.fst O _ _ ∘ₗ g), LinearMap.ker (LinearMap.snd O _ _ ∘ₗ g)),
      ⟨⟨_, Prod.fst_surjective.comp hg, rfl⟩, ⟨_, Prod.snd_surjective.comp hg, rfl⟩⟩, ?_⟩
    change LinearMap.ker _ ⊓ LinearMap.ker _ = _
    rw [← LinearMap.ker_prod, ← LinearEquiv.ker_comp (crt I J h) f]
    rfl

theorem encard_top : (Ker (⊤ : Ideal O) N).encard = 1 := by
  rw [Set.encard_eq_one]
  refine ⟨⊤, Set.eq_singleton_iff_unique_mem.2 ⟨⟨0, fun y => ⟨0, Subsingleton.elim _ _⟩, by simp⟩, ?_⟩⟩
  intro L hL
  rw [eq_top_iff]
  intro x _
  simpa using smul_mem hL (c := 1) trivial x

theorem encard_max [IsDomain O] [Module.Finite O N] [Module.Projective O N] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    (Ker P N).encard =
      ((∑ i ∈ Finset.range (Module.finrank O N), Nat.card (O ⧸ P) ^ i : ℕ) : ℕ∞) := by
  have : Nontrivial (O ⧸ P) := Ideal.Quotient.nontrivial_iff.2 hP.ne_top
  have he : Ker P N = {L : Submodule O N | ∃ f : N →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = L} := by
    ext L
    refine exists_congr fun f => and_congr_left fun _ => ⟨fun hf h0 => ?_, fun hf y => ?_⟩
    · obtain ⟨v, hv⟩ := hf 1
      rw [h0] at hv
      exact zero_ne_one hv
    · obtain ⟨v, hv⟩ := GlobalTheory.SW.Hyper.surj_of_ne P f hf
      obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective y
      exact ⟨c • v, by rw [map_smul, hv, Algebra.smul_def, mul_one]; rfl⟩
  obtain ⟨hf, hc⟩ := GlobalTheory.SW.Hyper.count (M := N) P
  rw [he, ← hf.cast_ncard_eq]
  congr 1
  have h1 : 1 < Nat.card (O ⧸ P) := Finite.one_lt_card
  refine Nat.eq_of_mul_eq_mul_right (m := Nat.card (O ⧸ P) - 1) (by omega) ?_
  rw [hc, geom_sum_mul_of_one_le h1.le]

theorem encard_prod [IsDomain O] [Module.Finite O N] [Module.Projective O N] (T : ℕ) (hT : T ≠ 0)
    (s : Finset (Ideal O)) (hs : ∀ P ∈ s, P.IsMaximal ∧ Nat.card (O ⧸ P) = T) :
    (Ker (∏ P ∈ s, P) N).encard =
      (((∑ i ∈ Finset.range (Module.finrank O N), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, Ideal.one_eq_top, encard_top]; simp
  | insert P s hP ih =>
    obtain ⟨hm, hc⟩ := hs P (Finset.mem_insert_self _ _)
    have : Finite (O ⧸ P) := Nat.finite_of_card_ne_zero (hc ▸ hT)
    have hco : IsCoprime P (∏ Q ∈ s, Q) := IsCoprime.prod_right fun Q hQ =>
      Ideal.isCoprime_iff_sup_eq.2 (hm.coprime_of_ne (hs Q (Finset.mem_insert_of_mem hQ)).1
        fun h => hP (h ▸ hQ))
    rw [Finset.prod_insert hP, encard_mul _ _ hco, ih fun Q hQ => hs Q (Finset.mem_insert_of_mem hQ),
      encard_max, hc, Finset.card_insert_of_notMem hP, pow_succ', Nat.cast_mul]

end Abstract

theorem finrank_lattice {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V)
    (hM : Submodule.IsLattice K M) : Module.finrank (𝓞 K) M = Module.finrank K V := by
  have hr : Module.rank (𝓞 K) V = Module.rank K V :=
    (IsLocalization.rank_eq K (nonZeroDivisors (𝓞 K)) le_rfl).symm
  have : Module.rank (𝓞 K) M = Module.rank K V := by
    apply le_antisymm
    · rw [← hr]; exact Submodule.rank_le M
    · obtain ⟨s, hsM, hspan, hli⟩ := exists_linearIndependent K (M : Set V)
      rw [hM.span_eq_top] at hspan
      have h1 : Module.rank K V = Cardinal.mk s := by
        rw [← rank_top, ← hspan, rank_span_set hli]
      have h2 : LinearIndependent (𝓞 K) (fun x : s => (⟨x.1, hsM x.2⟩ : M)) := by
        apply LinearIndependent.of_comp M.subtype
        exact (LinearIndependent.iff_fractionRing (𝓞 K) K).mpr hli
      rw [h1]
      exact h2.cardinal_le_rank
  simp only [Module.finrank, this]

theorem main : ∀ (K V : Type) [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (M : Submodule (𝓞 K) V), Submodule.IsLattice K M → ∀ (T : ℕ) (s : Finset (Ideal (𝓞 K))), T.Prime → (∀ P ∈ s, P.IsMaximal ∧ Ideal.absNorm P = T) → {L : Submodule (𝓞 K) V | L ≤ M ∧ Nonempty ((↥M ⧸ L.comap M.subtype) ≃ₗ[𝓞 K] (𝓞 K ⧸ ∏ P ∈ s, P))}.encard = (((∑ i ∈ Finset.range (Module.finrank K V), T ^ i) ^ s.card : ℕ) : ℕ∞) := by
  intro K V _ _ _ _ _ _ _ M hM T s hT hs
  have : Module.IsTorsionFree (𝓞 K) V := Module.IsTorsionFree.trans_faithfulSMul (𝓞 K) K V
  have : Module.FinitePresentation (𝓞 K) M := Module.finitePresentation_of_finite _ _
  have : Module.Projective (𝓞 K) M := Module.Flat.projective_of_finitePresentation
  rw [← finrank_lattice M hM, ← encard_prod (N := M) T hT.ne_zero s fun P hP =>
    ⟨(hs P hP).1, by rw [← (hs P hP).2, Ideal.absNorm_apply, Submodule.cardQuot_apply]⟩]
  refine encard_eq_of_bijOn (f := fun L => L.comap M.subtype) ⟨?_, ?_, ?_⟩
  · intro L hL
    exact (mem_ker_iff _ _).2 hL.2
  · intro L hL L' hL' h
    have := congrArg (Submodule.map M.subtype) h
    rwa [Submodule.map_comap_subtype, Submodule.map_comap_subtype, inf_eq_right.2 hL.1,
      inf_eq_right.2 hL'.1] at this
  · intro L hL
    have h : (L.map M.subtype).comap M.subtype = L := Submodule.comap_map_eq_of_injective M.injective_subtype L
    refine ⟨L.map M.subtype, ⟨Submodule.map_subtype_le _ _, ?_⟩, h⟩
    rw [h]
    exact (mem_ker_iff _ _).1 hL

end GlobalTheory.SublatCount
