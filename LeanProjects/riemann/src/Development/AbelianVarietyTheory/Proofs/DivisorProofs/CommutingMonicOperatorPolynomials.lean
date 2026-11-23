import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFiniteMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonicFactorFinite
open Matrix GlobalTheory.LeviHC
open Formalism.REAL (GlRel qdet)

noncomputable section

namespace GlobalTheory.LeviHC.FactorMod

variable {M : Type} [AddCommGroup M] [Module ℂ M]

theorem finMod_mono {K₁ K₂ : Submodule ℂ M} (h : K₁ ≤ K₂) {A : Subalgebra ℂ (Module.End ℂ M)} {v : M}
    (hf : FinMod K₁ A v) : FinMod K₂ A v := by
  unfold FinMod at *
  have e : Submodule.span ℂ {y : M ⧸ K₂ | ∃ a ∈ A, y = K₂.mkQ (a v)} =
      (Submodule.span ℂ {y : M ⧸ K₁ | ∃ a ∈ A, y = K₁.mkQ (a v)}).map (Submodule.factor h) := by
    rw [Submodule.map_span]
    congr 1
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨K₁.mkQ (a v), ⟨a, ha, rfl⟩, Submodule.factor_mk h _⟩
    · rintro ⟨_, ⟨a, ha, rfl⟩, rfl⟩
      exact ⟨a, ha, Submodule.factor_mk h _⟩
  rw [e]
  infer_instance

theorem comm_of_mem_adjoin {s : Set (Module.End ℂ M)} {f b : Module.End ℂ M} (hb : b ∈ Algebra.adjoin ℂ s)
    (h : ∀ g ∈ s, Commute f g) : Commute f b := by
  have hle : Algebra.adjoin ℂ s ≤ Subalgebra.centralizer ℂ {f} :=
    Algebra.adjoin_le fun g hg => (Subalgebra.mem_centralizer_iff ℂ).2 fun y hy => by
      rw [Set.mem_singleton_iff.1 hy]; exact (h g hg)
  exact (((Subalgebra.mem_centralizer_iff ℂ).1 (hle hb)) f rfl)

def core (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : Submodule ℂ M where
  carrier := {x | ∀ b ∈ S, b x ∈ K}
  add_mem' := fun hx hy b hb => by rw [map_add]; exact K.add_mem (hx b hb) (hy b hb)
  zero_mem' := fun b _ => by rw [map_zero]; exact K.zero_mem
  smul_mem' := fun c x hx b hb => by rw [map_smul]; exact K.smul_mem c (hx b hb)

theorem core_le (K : Submodule ℂ M) (S : Subalgebra ℂ (Module.End ℂ M)) : core K S ≤ K := fun x hx => by
  simpa using hx 1 S.one_mem

theorem finMod_factor : ∀ (M : Type) [AddCommGroup M] [Module ℂ M] (M' K : Submodule ℂ M) (c p q : ℂ → Module.End ℂ M),
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, p u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∃ (d : ℕ) (a : ℕ → Module.End ℂ M), a d = 1 ∧ ∀ u, q u = ∑ i ∈ Finset.range (d + 1), u ^ i • a i) →
 (∀ u u', Commute (p u) (p u')) → (∀ u u', Commute (q u) (q u')) → (∀ u u', Commute (p u) (q u')) → (∀ u u', Commute (c u) (q u')) →
 (∀ u, ∀ x ∈ M', c u x ∈ M' ∧ p u x ∈ M' ∧ q u x ∈ M') → (∀ u, ∀ x ∈ K, p u x ∈ K) →
 (∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K) →
 ∀ v ∈ M', FinMod ⊥ (Algebra.adjoin ℂ (Set.range c)) v → FinMod K (Algebra.adjoin ℂ (Set.range p)) v := by
  intro M _ _ M' K c p q hp hq hpp hqq hpq hcq hM hK hrel v hv hfin
  set S := Algebra.adjoin ℂ (Set.range q) with hS

  have cb : ∀ u, ∀ b ∈ S, Commute (c u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hcq u u')
  have pb : ∀ u, ∀ b ∈ S, Commute (p u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hpq u u')
  have qb : ∀ u, ∀ b ∈ S, Commute (q u) b := fun u b hb =>
    comm_of_mem_adjoin hb (by rintro _ ⟨u', rfl⟩; exact hqq u u')

  have hSM : ∀ b ∈ S, ∀ x ∈ M', b x ∈ M' := by
    have hle : S ≤ GlobalTheory.LeviHC.MidBlock.stab M' :=
      Algebra.adjoin_le (by rintro _ ⟨u, rfl⟩ x hx; exact (hM u x hx).2.2)
    intro b hb x hx
    exact hle hb x hx
  set K' := core K S
  have hK'p : ∀ u, ∀ x ∈ K', p u x ∈ K' ∧ q u x ∈ K' := by
    intro u x hx
    refine ⟨fun b hb => ?_, fun b hb => ?_⟩
    · have e : b (p u x) = p u (b x) := by
        have := (pb u b hb).eq
        exact (congrArg (fun f : Module.End ℂ M => f x) this).symm
      rw [e]; exact hK u _ (hx b hb)
    · have : b * q u ∈ S := S.mul_mem hb (Algebra.subset_adjoin ⟨u, rfl⟩)
      exact hx _ this
  have hrel' : ∀ u, ∀ x ∈ M', c u x - p u (q u x) ∈ K' := by
    intro u x hx b hb
    have e1 : b (c u x) = c u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (cb u b hb).eq).symm
    have e2 : b (q u x) = q u (b x) := (congrArg (fun f : Module.End ℂ M => f x) (qb u b hb).eq).symm
    have e3 : b (p u (q u x)) = p u (b (q u x)) :=
      (congrArg (fun f : Module.End ℂ M => f (q u x)) (pb u b hb).eq).symm
    rw [map_sub, e1, e3, e2]
    exact hrel u _ (hSM b hb x hx)
  have h1 : FinMod K' (Algebra.adjoin ℂ (Set.range c)) v := finMod_mono bot_le hfin
  have h2 := GlobalTheory.LeviHC.QuotMonic.monicFactorFiniteMod_of GlobalTheory.LeviHC.monicFactorFinite M M' K' c p q hp hq hpp hqq hpq
    hM hK'p hrel' v hv h1
  exact finMod_mono (core_le K S) h2

end GlobalTheory.LeviHC.FactorMod

end
