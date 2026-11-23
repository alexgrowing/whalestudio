import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.NormalRepresentationLattice
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LatticeBounds
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsValuationEqZpow
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulMemOfHatCosetIndNeZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlatNeZeroOfMemR
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TwistSupportPeriodicLevels

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.NormalRepresentationLattice

namespace GlobalTheory.LatClass

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem lat_of_coset {n : Type} [Fintype n] [DecidableEq n] {c : ℕ} {J : Subgroup (GL (n ⊕ Fin c) k)}
    (hJ : J ≤ KO k _) {a b : GL (n ⊕ Fin c) k}
    (h : DoubleCoset.mk (R k n c 1) J a = DoubleCoset.mk (R k n c 1) J b) :
    ∃ r ∈ R k n c 1, latOf b = latOf (r * a) := by
  obtain ⟨r, hr, w, hw, rfl⟩ := (DoubleCoset.eq _ _ _ _).1 h
  exact ⟨r, hr, by rw [latOf_mul_congr _ (latOf_eq_of_KO (hJ hw)), mul_one]⟩

variable [MeasurableSpace k] [BorelSpace k]
variable {s : ℕ} {X : ℕ → Type} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)] {Z : Type} [Fintype Z] [DecidableEq Z]
  {T : Chain k s X Z} {ϖ : kˣ} {ψ : AddChar k Circle} {ν : Measure k} [ν.IsAddHaarMeasure]
  (hϖ : valuation k (ϖ : k) = uniformizer k) (hψ : HasConductor ψ 1)
  (hb : ∀ j c h, latOf (T.bas j c h) = latOf 1)
  (hs : ∀ j c h x, T.Phi j c h x ≠ 0 → IntM x)
  (hp : ∀ j c h x y, MaxM y → T.Phi j c h (x + y) = T.Phi j c h x)
  (hJ : ∀ j c h, (T.lev j c h).J ≤ KO k (X j ⊕ Fin c))

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem lat_bas {j c h} (g : GL (X j ⊕ Fin c) k) : latOf (g * T.bas j c h) = latOf g := by
  rw [latOf_mul_congr _ (hb j c h), mul_one]

omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] in
include hb in
theorem normal_one (c : ℕ) (h : 0 + c = s) : IsNormalRep T ϖ 0 c h 1 := by
  refine ⟨0, 0, fun i => by simp, fun i => zero_mem _, ?_⟩
  rw [lat_bas hb]
  ext y
  simp [mem_normal, mem_latOf_one, mem_pow_zero]

include hϖ hψ hb hs hp hJ

theorem exists_normal {A : RepFam k s X} (hA : T.IsRepSystem A ψ ν) (j : ℕ) :
    ∀ c h, ∀ g ∈ A j c h, ∃ r ∈ R k (X j) (c + 1) 1, IsNormalRep T ϖ j c h (r * g) := by
  induction j with
  | zero =>
    intro c h g hg
    rw [hA.zero] at hg
    obtain rfl : g = 1 := hg
    exact ⟨1, one_mem _, by rw [one_mul]; exact normal_one hb c h⟩
  | succ j ih =>
    intro c h g' hg'
    obtain ⟨g, hg, a, ha, hf⟩ := Set.mem_iUnion₂.1 ((hA.bij j c h).mapsTo hg')
    obtain ⟨r, hr, e', z', he', hz', hl⟩ := ih _ _ g hg
    rw [lat_bas hb, ← nfBasis_one] at hl
    obtain ⟨x₀, h0⟩ := Function.ne_iff.1 (GlobalTheory.FlatSourceStable.flat_ne_zero_of_mem_R k _ _ c ψ ν _ _ g a hf r hr)
    obtain ⟨r₂, hr₂, e, z, he, hz, hl₂⟩ := step_normal (NormalForm.normalFormModN k) hϖ hψ he' hz'
      (hl ▸ om_supp (hs _ _ _) (r * g) a) (hl ▸ om_per hϖ (hp _ _ _) (r * g) a) h0
    obtain ⟨r₃, hr₃, hl₃⟩ := lat_of_coset (hJ _ _ _) ha
    refine ⟨r₂ * r₃⁻¹, mul_mem hr₂ (inv_mem hr₃), e, z, he, hz, ?_⟩
    rw [lat_bas hb, latOf_mul_congr _ hl₃, ← hl₂]
    congr 1
    group

end GlobalTheory.LatClass
