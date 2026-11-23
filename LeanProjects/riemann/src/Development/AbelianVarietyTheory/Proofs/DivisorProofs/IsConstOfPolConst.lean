import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzOrbitContinuousStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatchingExistsStatement

noncomputable section

namespace GlobalTheory.ThKConst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  obtain ⟨c₁, t₁⟩ := h₁
  obtain ⟨c₂, t₂⟩ := h₂
  have e : ⇑(χ₁ / χ₂) = fun x => χ₁ x / χ₂ x := funext fun x => MonoidHom.div_apply χ₁ χ₂ x
  exact And.intro (by rw [e]; exact c₁.div' c₂) fun x => by rw [MonoidHom.div_apply, t₁ x, t₂ x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂]
  split_ifs
  · norm_num
  · rcases Nat.even_or_odd n₁ with h | h
    · rw [h.neg_one_pow, ((Nat.even_add.mp he).mp h).neg_one_pow, hn.neg_one_pow]
      norm_num
    · have h' : Odd n₂ := Nat.not_even_iff_odd.mp fun h'' => (Nat.not_even_iff_odd.mpr h) ((Nat.even_add.mp he).mpr h'')
      rw [h.neg_one_pow, h'.neg_one_pow, hn.neg_one_pow]
      norm_num

variable {a a' : ℕ}

theorem isPair_big {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M X.β (X.β / X.α) om (a - G.p) G.p (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV
    skew := h.geo.hW
    good := h.geo.hM
    hX := h.chars.heckeβ
    hW := isHecke_div h.chars.heckeβ h.chars.heckeα
    resX := h.chars.resβ
    resW := resEtaPow_div h.chars.resβ h.chars.resα h.geo.even h.geo.even
    weil := h.weil }

theorem isPair_small {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_div h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_div h.chars.resα h.chars.resβ (Nat.even_add.mpr (Nat.even_add.mp h.geo.even).symm) h.geo.even
    weil := h.weil' }

theorem thetaSum_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ?_) ?_
  · simp [thetaSum]
  · intro k s hk ih hf
    have hs : ∀ j ∈ s, f j ∈ schA F κ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      thetaSum_add F (hf k (Finset.mem_insert_self k s)) (Submodule.sum_mem _ hs), ih hs]

end GlobalTheory.ThKConst
