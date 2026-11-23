import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.TraceMulEqZero
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.IsClosedGzS
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CompactOrbits.NilpotentOrbits.OrbitIntegrals.ModulusInduction.Imports

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker MulAction

open scoped Pointwise

namespace PositivityTheory.RgUd.T.Nil.Orb.BStep

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.T.Nil.Orb

set_option linter.unusedSectionVars false

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

attribute [local instance] t2Sp lcSp tdSp contSMul lcH tdH scH contSMulH

theorem act_inv_act (h : GL (Fin n) k) (q : Sp k n) : act h⁻¹ (act h q) = q := by
  rw [← act_mul, inv_mul_cancel, act_one]

theorem act_snd_ne (h : GL (Fin n) k) {q : Sp k n} (hq : q.2 ≠ 0) : (act h q).2 ≠ 0 := by
  intro h0
  apply hq
  rw [← act_inv_act h q]
  show ((h⁻¹ : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) *ᵥ (act h q).2 = 0
  rw [h0, mulVec_zero]

def toT (p : Sp k n) : SpT k n := p

theorem smulH_eq (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (h : GzS Z) (q : SpT k n) :
    h • q = (act (h : GL (Fin n) k) q : Sp k n) := rfl

theorem mem_orbit_iff' (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) {p q : Sp k n} :
    toT q ∈ orbit (GzS Z) (toT p) ↔ q ∈ orb Z p := by
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g, g.2, ?_⟩
    dsimp only at hg
    rw [smulH_eq] at hg
    exact hg
  · rintro ⟨g, hg, hgq⟩
    have hg' : g ∈ GzS Z := hg
    refine ⟨⟨g, hg'⟩, ?_⟩
    show (⟨g, hg'⟩ : GzS Z) • toT p = toT q
    rw [smulH_eq]
    exact hgq

theorem lift_on_C' {U₁ C O : Set (Sp k n)} (hO : U₁ ∩ C = O) {P : Set (SpT k n)} (hP : ∀ x, toT x ∈ P → x ∈ O)
    {F : Sp k n → ℂ} (hF : F ∈ supportedIn U₁) (hFO : ∀ x ∈ O, F x = P.indicator 1 (toT x)) :
    ∀ x ∈ C, F x = P.indicator 1 (toT x) := by
  intro x hx
  by_cases hxU : x ∈ U₁
  · exact hFO x (by rw [← hO]; exact ⟨hxU, hx⟩)
  · have hF0 : F x = 0 := by
      by_contra hne
      exact hxU ((mem_supportedIn.1 hF).2 hne)
    have hxP : toT x ∉ P := by
      intro hP'
      have hxO := hP x hP'
      rw [← hO] at hxO
      exact hxU hxO.1
    rw [hF0, Set.indicator_of_notMem hxP]

theorem xi_eq {ξ : (Sp k n → ℂ) →ₗ[ℂ] ℂ} {C : Set (Sp k n)} (hξC : SuppU ξ C) {a b : Sp k n → ℂ}
    (ha : a ∈ supportedIn UU) (hb : b ∈ supportedIn UU) (h : ∀ q ∈ C, a q = b q) : ξ a = ξ b := by
  have := hξC (a - b) (Submodule.sub_mem _ ha hb) (fun q hq => by simp [h q hq])
  rwa [map_sub, sub_eq_zero] at this

def sigH [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ) : Sp k n ≃ₜ Sp k n where
  toFun := sig Z t
  invFun := sig Z t⁻¹
  left_inv := sig_inv_sig Z hZ t
  right_inv q := by simpa using sig_inv_sig Z hZ t⁻¹ q
  continuous_toFun := continuous_sig Z hZ t
  continuous_invFun := continuous_sig Z hZ t⁻¹

theorem comp_sig_mem [CharZero k] (Z : Subalgebra k (Matrix (Fin n) (Fin n) k)) (hZ : CR Z) (t : kˣ)
    {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) : (fun q => f (sig Z t q)) ∈ supportedIn UU := by
  rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous (continuous_sig Z hZ t), hcs.comp_homeomorph (sigH Z hZ t)⟩, ?_⟩
  intro q hq
  have h1 : (sig Z t q).2 ≠ 0 := hsu (show sig Z t q ∈ Function.support f from hq)
  exact h1

theorem comp_act_mem (h : GL (Fin n) k) {f : Sp k n → ℂ} {V : Set (Sp k n)} (hf : f ∈ supportedIn V) :
    (fun q => f (act h q)) ∈ supportedIn ((fun q => act h⁻¹ q) '' V) := by
  have hc : ∀ g : GL (Fin n) k, Continuous (fun q : Sp k n => act g q) := by
    intro g
    unfold act
    fun_prop
  let e : Sp k n ≃ₜ Sp k n :=
    { toFun := fun q => act h q
      invFun := fun q => act h⁻¹ q
      left_inv := fun q => act_inv_act h q
      right_inv := fun q => by simpa using act_inv_act h⁻¹ q
      continuous_toFun := hc h
      continuous_invFun := hc h⁻¹ }
  rw [mem_supportedIn, GroundTheory.Automorphic.mem_locallyConstantCompactSupport] at hf ⊢
  obtain ⟨⟨hlc, hcs⟩, hsu⟩ := hf
  refine ⟨⟨hlc.comp_continuous (hc h), hcs.comp_homeomorph e⟩, ?_⟩
  intro q hq
  exact ⟨act h q, hsu hq, act_inv_act h q⟩

theorem comp_act_memUU (h : GL (Fin n) k) {f : Sp k n → ℂ} (hf : f ∈ supportedIn UU) :
    (fun q => f (act h q)) ∈ supportedIn UU := by
  refine supportedIn_mono ?_ (comp_act_mem h hf)
  rintro _ ⟨q, hq, rfl⟩
  exact act_snd_ne h⁻¹ hq

end PositivityTheory.RgUd.T.Nil.Orb.BStep
