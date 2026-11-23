import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ConcreteLevelAdelicSubset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EvalActIntertwines
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicUnimodularity.NatSmulMulEq
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.AutomorphicEvaluation Formalism.L2.DIV Formalism.L2.SG.RowDict Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowLevelMatch Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting MeasureTheory NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.SRe
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.SRe.ConvStep
variable {D : D7}

theorem kset_one (X : HidaSetting D) : (1 : X.B.I.Gf) ∈ X.B.I.Kset := by
  show ((1 : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [OneMemClass.coe_one]
  exact (Formalism.UG.stabGL X.B.I.Lf).one_mem

theorem kset_mul (X : HidaSetting D) {x y : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hy : y ∈ X.B.I.Kset) :
    x * y ∈ X.B.I.Kset := by
  show ((x * y : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_mul]
  exact mul_mem hx hy

theorem kset_inv (X : HidaSetting D) {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) : x⁻¹ ∈ X.B.I.Kset := by
  show ((x⁻¹ : X.B.I.Gf) : GL _ _) ∈ Formalism.UG.stabGL X.B.I.Lf
  rw [Subgroup.coe_inv]
  exact inv_mem hx

theorem red_one (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) : red 1 = 1 := by
  have h := hr.2.1 1 (kset_one X) 1 (kset_one X)
  rw [one_mul] at h
  exact mul_left_cancel (a := red 1) (by rw [mul_one]; exact h.symm)

theorem fibre_iff (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) (x : X.B.I.Gf) :
    (x ∈ X.B.I.Kset ∧ red x = red s) ↔ s⁻¹ * x ∈ X.B.I.Kg X.B.g := by
  have hsi : s⁻¹ ∈ X.B.I.Kset := kset_inv X hs
  have hinv : red s⁻¹ = (red s)⁻¹ := by
    have h1 := hr.2.1 s⁻¹ hsi s hs
    rw [inv_mul_cancel, red_one X hr] at h1
    exact eq_inv_of_mul_eq_one_left h1.symm
  constructor
  · rintro ⟨hx, hrx⟩
    have hk : s⁻¹ * x ∈ X.B.I.Kset := kset_mul X hsi hx
    refine (hr.2.2.2 _ hk).1 ?_
    rw [hr.2.1 _ hsi _ hx, hinv, hrx, inv_mul_cancel]
  · intro hk
    have hkK : s⁻¹ * x ∈ X.B.I.Kset := hk.1
    have hr1 : red (s⁻¹ * x) = 1 := (hr.2.2.2 _ hkK).2 hk
    have h2 := kset_mul X hs hkK
    rw [mul_inv_cancel_left] at h2
    refine ⟨h2, ?_⟩
    have h3 := hr.2.1 _ hs _ hkK
    rw [mul_inv_cancel_left, hr1, mul_one] at h3
    exact h3

theorem one_le_g (X : HidaSetting D) : 1 ≤ X.B.g := by
  rw [X.g_eq]
  exact Nat.one_le_iff_ne_zero.2 (mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)

theorem kg_open (X : HidaSetting D) : IsOpen (X.B.I.Kg X.B.g) := X.B.I.topf_open X.B.g (one_le_g X)

theorem kg_pos_fin (X : HidaSetting D) : 0 < X.B.μf (X.B.I.Kg X.B.g) ∧ X.B.μf (X.B.I.Kg X.B.g) < ⊤ := by
  have hne : (X.B.I.Kg X.B.g).Nonempty := ⟨1, by
    refine ⟨kset_one X, fun y _ => ⟨0, zero_mem _, ?_⟩⟩
    simp [Formalism.MainNotions.S.AutInst.fmat]⟩
  refine ⟨(kg_open X).measure_pos X.B.μf hne, ?_⟩
  exact lt_of_le_of_lt (measure_mono fun x hx => hx.1) (PI.WAU.Cpt.isCompact_Kset X.B.I).measure_lt_top

theorem fibre_meas (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red) {s : X.B.I.Gf}
    (hs : s ∈ X.B.I.Kset) :
    MeasurableSet {x | x ∈ X.B.I.Kset ∧ red x = red s} ∧
      X.B.μf {x | x ∈ X.B.I.Kset ∧ red x = red s} = X.B.μf (X.B.I.Kg X.B.g) := by
  have e : {x | x ∈ X.B.I.Kset ∧ red x = red s} = (fun x => s⁻¹ * x) ⁻¹' (X.B.I.Kg X.B.g) := by
    ext x; exact fibre_iff X hr hs x
  rw [e]
  refine ⟨((kg_open X).preimage (continuous_mul_left s⁻¹)).measurableSet, ?_⟩
  exact measure_preimage_mul X.B.μf s⁻¹ _

open scoped InnerProductSpace in
theorem top_expand [Fintype (G0g D.nd)] (X : HidaSetting D) {red : X.B.I.Gf → G0g D.nd} (hr : IsRedHom X red)
    (s0 : G0g D.nd → X.B.I.Gf) (hs0 : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ) (a : G0g D.nd → ℂ)
    (Top : L2X X →L[ℂ] L2X X)
    (hT : X.B.I.IsRConvF X.B.μf X.B.fund X.B.R
      (fun x => if x ∈ X.B.I.Kset then a (red x) / ((X.B.μf (X.B.I.Kg X.B.g)).toReal : ℂ) else 0) Top)
    (y : L2X X) (hy : ∀ k ∈ X.B.I.Kset, X.B.R (1, k) y = X.B.R (1, s0 (red k)) y) :
    Top y = ∑ γ, a γ • X.B.R (1, s0 γ) y := by
  apply ext_inner_left ℂ
  intro x
  rw [hT.2 x y, inner_sum]
  simp only [inner_smul_right]
  set V : ℝ := (X.B.μf (X.B.I.Kg X.B.g)).toReal with hV
  have hVpos : 0 < V := ENNReal.toReal_pos (kg_pos_fin X).1.ne' (kg_pos_fin X).2.ne
  have hV0 : (V : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hVpos.ne'
  let Fb : G0g D.nd → Set X.B.I.Gf := fun γ => {z | z ∈ X.B.I.Kset ∧ red z = γ}
  have hFb : ∀ γ, MeasurableSet (Fb γ) ∧ X.B.μf (Fb γ) = X.B.μf (X.B.I.Kg X.B.g) := by
    intro γ
    have := fibre_meas X hr (hs0 γ).1
    rw [(hs0 γ).2] at this
    exact this
  let cf : G0g D.nd → ℂ := fun γ => a γ / (V : ℂ) * ⟪x, X.B.R (1, s0 γ) y⟫_ℂ
  have hpt : ∀ g : X.B.I.Gf,
      (if g ∈ X.B.I.Kset then a (red g) / (V : ℂ) else 0) * ⟪x, X.B.R (1, g) y⟫_ℂ =
        ∑ γ, (Fb γ).indicator (fun _ => cf γ) g := by
    intro g
    by_cases hg : g ∈ X.B.I.Kset
    · rw [if_pos hg, Finset.sum_eq_single (red g)]
      · rw [Set.indicator_of_mem (show g ∈ Fb (red g) from ⟨hg, rfl⟩), hy g hg]
      · intro b _ hb
        exact Set.indicator_of_notMem (fun hm => hb hm.2.symm) _
      · intro h1; exact absurd (Finset.mem_univ _) h1
    · rw [if_neg hg, zero_mul]
      symm
      refine Finset.sum_eq_zero fun b _ => ?_
      exact Set.indicator_of_notMem (fun hm => hg hm.1) _
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl fun γ _ => ?_
    rw [integral_indicator_const _ (hFb γ).1, measureReal_def, (hFb γ).2, ← hV]
    simp only [cf, Complex.real_smul]
    field_simp
  · intro γ _
    refine (integrable_indicator_iff (hFb γ).1).2 ?_
    refine integrableOn_const ?_
    rw [(hFb γ).2]; exact (kg_pos_fin X).2.ne

theorem R_star_fibre [Fintype (G0g D.nd)] {G' : Type} [Group G'] [Fintype G'] {Pl0 T : Type}
    {A : FamIn D.what₂.LL G' Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]
    (R : RealDat D A Ks) (F : Face D A) (X : HidaSetting D) (h : X.B.I = Formalism.L2.SG.InstExistsPf.instOf D)
    (t : GA D (D.sp.Y 0)) (v₀ : (MP R).Vec) (σ : G0g D.nd ≃* G') (red : X.B.I.Gf → G0g D.nd)
    (hB : LevelMatchB R F X h t σ red) (S : MMap (MP R)) (hS : S ∈ MultR R F) (f : L2X X)
    (hf : f =ᵐ[muX X] fun x => ev (MP R) v₀ S ((iotaX X h).symm x * t))
    (hGQ : ∀ γ ∈ GQ (D.sp.Y 0), ∀ g, S v₀ (γ * g) = S v₀ g)
    (s0 : G0g D.nd → X.B.I.Gf) (hs0 : ∀ γ, s0 γ ∈ X.B.I.Kset ∧ red (s0 γ) = γ) :
    ∀ k ∈ X.B.I.Kset, X.B.R (1, k) (star f) = X.B.R (1, s0 (red k)) (star f) := by
  intro k hk
  let a : G0g D.nd → ℂ := fun γ => if γ = red k then 1 else 0
  let s1 : G0g D.nd → X.B.I.Gf := Function.update s0 (red k) k
  have hs1 : ∀ γ, s1 γ ∈ X.B.I.Kset ∧ red (s1 γ) = γ := by
    intro γ
    by_cases hγ : γ = red k
    · subst hγ
      refine ⟨?_, ?_⟩ <;> simp [s1, hk]
    · simp only [s1, Function.update_of_ne hγ]
      exact hs0 γ
  have red_sum : ∀ s : G0g D.nd → X.B.I.Gf,
      (∑ γ, star (a γ) • star (X.B.R (1, s γ) (star f)) : L2X X) = star (X.B.R (1, s (red k)) (star f)) := by
    intro s
    rw [Finset.sum_eq_single (red k)]
    · simp [a]
    · intro b _ hb
      simp [a, hb]
    · intro h1; exact absurd (Finset.mem_univ _) h1
  have e1 := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB S hS f hf hGQ a s1 hs1
  have e0 := GlobalTheory.Mem.SRe.evalAct_intertwines D G' Pl0 T A Ks R F X h t v₀ σ red hB S hS f hf hGQ a s0 hs0
  rw [red_sum] at e1 e0
  have e2 := Lp.ext (e1.trans e0.symm)
  have e3 := congrArg star e2
  simp only [star_star, s1, Function.update_self] at e3
  exact e3

end GlobalTheory.Mem.SRe.ConvStep

namespace GlobalTheory.Mem.SRe

end GlobalTheory.Mem.SRe
