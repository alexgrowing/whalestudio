import Formalism.HermitianCurvature.HermitianCurvatureProofs.ParamCommF

open Matrix Filter Topology
open scoped ComplexConjugate ContDiff

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.WirtingerOperators

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.P.LevelPointCoordinates

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {j : ℕ}

theorem cont_ofSnd : Continuous fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := continuous_snd

theorem contDiff_ofSnd : ContDiff ℝ ∞ fun q : ℂ × (Fin j → Fin j → ℂ) => (Matrix.of q.2 : MJ j) := contDiff_snd

theorem contDiff_pair (τ : ℂ) : ContDiff ℝ ∞ fun Z : MJ j => ((τ, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) :=
  contDiff_const.prodMk contDiff_id

theorem isOpen_inv : IsOpen {Z : MJ j | Z.det ≠ 0} :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem diffAt_fst {G : ℂ × (Fin j → Fin j → ℂ) → E} {U : Set (ℂ × (Fin j → Fin j → ℂ))} (hU : IsOpen U)
    (hG : ContDiffOn ℝ ∞ G U) {q : ℂ × (Fin j → Fin j → ℂ)} (hq : q ∈ U) :
    DifferentiableAt ℝ (fun τ : ℂ => G (τ, q.2)) q.1 := by
  have hd : DifferentiableAt ℝ G q := (hG.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hq)
  exact hd.comp q.1 ((differentiableAt_id).prodMk (differentiableAt_const _))

theorem dz_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dz (fun s => F s + G s) τ = PBP.dz F τ + PBP.dz G τ := by
  unfold PBP.dz
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dzb_add {F G : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (hG : DifferentiableAt ℝ G τ) :
    PBP.dzb (fun s => F s + G s) τ = PBP.dzb F τ + PBP.dzb G τ := by
  unfold PBP.dzb
  rw [show (fun s => F s + G s) = F + G from rfl, (hF.hasFDerivAt.add hG.hasFDerivAt).fderiv]
  simp only [_root_.add_apply]
  module

theorem dz_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dz (fun s => c • F s) τ = c • PBP.dz F τ := by
  unfold PBP.dz
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dzb_smul {F : ℂ → E} {τ : ℂ} (hF : DifferentiableAt ℝ F τ) (c : ℂ) :
    PBP.dzb (fun s => c • F s) τ = c • PBP.dzb F τ := by
  unfold PBP.dzb
  rw [show (fun s => c • F s) = c • F from rfl, (hF.hasFDerivAt.const_smul c).fderiv]
  simp only [_root_.smul_apply]
  module

theorem dz_const (v : E) (τ : ℂ) : PBP.dz (fun _ : ℂ => v) τ = 0 := by simp [PBP.dz]

theorem dzb_const (v : E) (τ : ℂ) : PBP.dzb (fun _ : ℂ => v) τ = 0 := by simp [PBP.dzb]

theorem zop_id : ZOp (E := E) (j := j) (fun h => h) := by
  refine ⟨fun h₁ h₂ Z h => h.eq_of_nhds, fun _ _ _ _ _ _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl, ?_⟩
  intro U κ _ _ hκ
  exact ⟨hκ, fun q _ => ⟨rfl, rfl⟩⟩

theorem zop_zero : ZOp (E := E) (j := j) (fun _ _ => 0) := by
  refine ⟨fun _ _ _ _ => rfl, fun _ _ _ _ _ _ _ _ _ => by simp, fun _ _ _ _ _ _ _ _ => by simp, ?_⟩
  intro U κ _ _ _
  exact ⟨contDiffOn_const, fun q _ => ⟨dz_const _ _, dzb_const _ _⟩⟩

theorem ZOp.smooth {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {V : Set (MJ j)} (hV : IsOpen V)
    (hVi : V ⊆ {Z | Z.det ≠ 0}) {h : MJ j → E} (hh : ContDiffOn ℝ ∞ h V) : ContDiffOn ℝ ∞ (T h) V := by
  let U : Set (ℂ × (Fin j → Fin j → ℂ)) := {q | (Matrix.of q.2 : MJ j) ∈ V}
  have hU : IsOpen U := hV.preimage cont_ofSnd
  have hUi : U ⊆ {q | (Matrix.of q.2).det ≠ 0} := fun q hq => hVi hq
  have hκ : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => (fun _ : ℂ => h) q.1 (Matrix.of q.2)) U :=
    hh.comp contDiff_ofSnd.contDiffOn (fun q hq => hq)
  have h1 := (hT.par U (fun _ => h) hU hUi hκ).1
  exact h1.comp (contDiff_pair 0).contDiffOn (fun Z hZ => hZ)

theorem ZOp.add' {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) :
    ZOp (fun h Z => T h Z + S h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h, hS.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, hS.add V h₁ h₂ hV hVi s₁ s₂ Z hZ]; abel
  · intro V c h hV hVi s Z hZ
    rw [hT.smul V c h hV hVi s Z hZ, hS.smul V c h hV hVi s Z hZ, smul_add]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    refine ⟨t1.add s1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    have d2 := diffAt_fst hU s1 hq
    refine ⟨?_, ?_⟩
    · rw [dz_add d1 d2, (t2 q hq).1, (s2 q hq).1]
    · rw [dzb_add d1 d2, (t2 q hq).2, (s2 q hq).2]

theorem ZOp.cmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) {c : MJ j → ℂ}
    (hc : ContDiffOn ℝ ∞ c {Z | Z.det ≠ 0}) : ZOp (fun h Z => c Z • T h Z) := by
  refine ⟨fun h₁ h₂ Z h => by rw [hT.loc _ _ Z h], ?_, ?_, ?_⟩
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    rw [hT.add V h₁ h₂ hV hVi s₁ s₂ Z hZ, smul_add]
  · intro V c' h hV hVi s Z hZ
    rw [hT.smul V c' h hV hVi s Z hZ, smul_comm]
  · intro U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U κ hU hUi hκ
    have hc' : ContDiffOn ℝ ∞ (fun q : ℂ × (Fin j → Fin j → ℂ) => c (Matrix.of q.2)) U :=
      hc.comp contDiff_ofSnd.contDiffOn (fun q hq => hUi hq)
    refine ⟨hc'.smul t1, fun q hq => ?_⟩
    have d1 := diffAt_fst hU t1 hq
    exact ⟨by rw [dz_smul d1, (t2 q hq).1], by rw [dzb_smul d1, (t2 q hq).2]⟩

theorem ZOp.csmul {T : (MJ j → E) → MJ j → E} (hT : ZOp T) (c : ℂ) : ZOp (fun h Z => c • T h Z) :=
  hT.cmul (c := fun _ => c) contDiffOn_const

theorem ZOp.comp {T S : (MJ j → E) → MJ j → E} (hT : ZOp T) (hS : ZOp S) : ZOp (fun h => T (S h)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h₁ h₂ Z h
    apply hT.loc
    filter_upwards [h.eventually_nhds] with Z' hZ'
    exact hS.loc _ _ Z' hZ'
  · intro V h₁ h₂ hV hVi s₁ s₂ Z hZ
    have e : S (h₁ + h₂) =ᶠ[𝓝 Z] S h₁ + S h₂ := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.add V h₁ h₂ hV hVi s₁ s₂ Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.add V (S h₁) (S h₂) hV hVi (hS.smooth hV hVi s₁) (hS.smooth hV hVi s₂) Z hZ
  · intro V c h hV hVi s Z hZ
    have e : S (c • h) =ᶠ[𝓝 Z] c • S h := by
      filter_upwards [hV.mem_nhds hZ] with Z' hZ'
      exact hS.smul V c h hV hVi s Z' hZ'
    rw [hT.loc _ _ Z e]
    exact hT.smul V c (S h) hV hVi (hS.smooth hV hVi s) Z hZ
  · intro U κ hU hUi hκ
    obtain ⟨s1, s2⟩ := hS.par U κ hU hUi hκ
    obtain ⟨t1, t2⟩ := hT.par U (fun τ => S (κ τ)) hU hUi s1
    refine ⟨t1, fun q hq => ?_⟩
    have hsl : IsOpen {Z : MJ j | ((q.1, (Z : Fin j → Fin j → ℂ)) : ℂ × (Fin j → Fin j → ℂ)) ∈ U} :=
      hU.preimage (contDiff_pair q.1).continuous
    have e1 : (fun Z => PBP.dz (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dz (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).1
    have e2 : (fun Z => PBP.dzb (fun τ => S (κ τ) Z) q.1) =ᶠ[𝓝 (Matrix.of q.2)]
        S (fun Z => PBP.dzb (fun τ => κ τ Z) q.1) := by
      filter_upwards [hsl.mem_nhds (show (q.1, q.2) ∈ U from hq)] with Z hZ
      exact (s2 (q.1, (Z : Fin j → Fin j → ℂ)) hZ).2
    exact ⟨by rw [(t2 q hq).1, hT.loc _ _ _ e1], by rw [(t2 q hq).2, hT.loc _ _ _ e2]⟩

theorem zop_sum {ι : Type*} (s : Finset ι) {T : ι → (MJ j → E) → MJ j → E} (hT : ∀ i ∈ s, ZOp (T i)) :
    ZOp (fun h Z => ∑ i ∈ s, T i h Z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (zop_zero (E := E) (j := j))
  | insert a s ha ih =>
    have h1 := (hT a (by simp)).add' (ih (fun i hi => hT i (by simp [hi])))
    simpa [Finset.sum_insert ha] using h1

theorem zop_foldr : ∀ L : List ((MJ j → E) → MJ j → E), (∀ T ∈ L, ZOp T) →
    ZOp (fun f => L.foldr (fun T h => T h) f)
  | [], _ => zop_id
  | T :: L, h => by
    simp only [List.foldr_cons]
    exact (h T (by simp)).comp (zop_foldr L (fun T' hT' => h T' (by simp [hT'])))

end Formalism.FourierDecayAlt.P.WirtingerOperators
