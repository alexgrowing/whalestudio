import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.GodementSection (localChar adeleAt glAt)
open GroundTheory.Automorphic.GL2Classical
open GroundTheory.Automorphic.AdelicGLn
open CongruenceSubgroup
open scoped NumberField.AdeleRing ValuativeRel MatrixGroups ModularForm Classical
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RSLift

local notation "𝔸f" => FiniteAdeleRing (𝓞 ℚ) ℚ

set_option linter.unusedSectionVars false
set_option linter.unnecessarySimpa false

variable (N : ℕ) [NeZero N]

theorem levelIdeal_sub_int {x : 𝔸f} (hx : x ∈ levelIdeal N) : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact mul_mem (by simpa using intCast_mem_integralFiniteAdeles (N : ℤ)) ht

theorem levelIdeal_add {x y : 𝔸f} (hx : x ∈ levelIdeal N) (hy : y ∈ levelIdeal N) : x + y ∈ levelIdeal N := by
  simpa using mul_add_mul_mem_levelIdeal (one_mem _) (one_mem _) hx hy

theorem levelIdeal_neg {x : 𝔸f} (hx : x ∈ levelIdeal N) : -x ∈ levelIdeal N := by
  obtain ⟨t, ht, rfl⟩ := hx
  exact ⟨-t, neg_mem ht, by ring⟩

theorem exists_int_sub_mem {x : 𝔸f} (hx : x ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    ∃ n : ℤ, x - (n : 𝔸f) ∈ levelIdeal N := by
  have hd : DenseRange (algebraMap ℚ 𝔸f) := denseRange_algebraMap_finiteAdeleRing ℚ
  have ho : IsOpen ((fun y : 𝔸f => x - y) ⁻¹' levelIdeal N) :=
    (isOpen_levelIdeal N).preimage (continuous_const.sub continuous_id)
  obtain ⟨q, hq⟩ := hd.exists_mem_open ho ⟨x, by simpa using zero_mem_levelIdeal N⟩
  have hq' : x - algebraMap ℚ 𝔸f q ∈ levelIdeal N := hq
  have hi : algebraMap ℚ 𝔸f q ∈ integralFiniteAdeles (𝓞 ℚ) ℚ := by
    have := sub_mem hx (levelIdeal_sub_int N hq')
    simpa using this
  obtain ⟨m, rfl⟩ := exists_int_of_mem_integralFiniteAdeles hi
  exact ⟨m, by simpa using hq'⟩

def res (x : 𝔸f) : ZMod N :=
  if h : ∃ n : ℤ, x - (n : 𝔸f) ∈ levelIdeal N then ((h.choose : ℤ) : ZMod N) else 0

variable {N}

theorem res_eq {x : 𝔸f} {n : ℤ} (h : x - (n : 𝔸f) ∈ levelIdeal N) : res N x = (n : ZMod N) := by
  have hex : ∃ n : ℤ, x - (n : 𝔸f) ∈ levelIdeal N := ⟨n, h⟩
  rw [res, dif_pos hex]
  have h2 := hex.choose_spec
  set m := hex.choose
  have h3 : ((n - m : ℤ) : 𝔸f) ∈ levelIdeal N := by
    have := levelIdeal_add N h2 (levelIdeal_neg N h)
    have e : x - (m : 𝔸f) + -(x - (n : 𝔸f)) = ((n - m : ℤ) : 𝔸f) := by push_cast; ring
    rwa [e] at this
  have h4 : algebraMap ℚ 𝔸f ((n - m : ℤ) : ℚ) ∈ levelIdeal N := by simpa using h3
  obtain ⟨t, ht⟩ := exists_int_of_mem_levelIdeal N h4
  have h5 : n - m = N * t := by exact_mod_cast ht
  have h6 : ((n - m : ℤ) : ZMod N) = 0 := by rw [h5]; simp
  push_cast at h6
  exact (sub_eq_zero.1 h6).symm

theorem res_intCast (n : ℤ) : res N (n : 𝔸f) = (n : ZMod N) :=
  res_eq (by simpa using zero_mem_levelIdeal N)

theorem res_one : res N (1 : 𝔸f) = 1 := by simpa using res_intCast (N := N) 1

theorem res_add_mul {a b c d : 𝔸f} (ha : a ∈ levelIdeal N) (hb : b ∈ integralFiniteAdeles (𝓞 ℚ) ℚ)
    (hc : c ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) (hd : d ∈ integralFiniteAdeles (𝓞 ℚ) ℚ) :
    res N (a * b + c * d) = res N c * res N d := by
  obtain ⟨n, hn⟩ := exists_int_sub_mem N hc
  obtain ⟨m, hm⟩ := exists_int_sub_mem N hd
  have h : a * b + c * d - ((n * m : ℤ) : 𝔸f) ∈ levelIdeal N := by
    have h1 := mul_add_mul_mem_levelIdeal hc (intCast_mem_integralFiniteAdeles m) hm hn
    have h2 := mul_mem_levelIdeal hb ha
    have := levelIdeal_add N h1 h2
    have e : c * (d - (m : 𝔸f)) + (m : 𝔸f) * (c - (n : 𝔸f)) + b * a =
      a * b + c * d - ((n * m : ℤ) : 𝔸f) := by push_cast; ring
    rwa [e] at this
  rw [res_eq h, res_eq hn, res_eq hm]
  push_cast
  rfl

section Lift

variable (χ : DirichletCharacter ℂ N)

def eta (u : FiniteAdelicGL ℚ 2) : ℂ := (χ (res N ((u : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1)))⁻¹

theorem entry_int {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (i j : Fin 2) :
    (u : Matrix (Fin 2) (Fin 2) 𝔸f) i j ∈ integralFiniteAdeles (𝓞 ℚ) ℚ :=
  ((mem_integralFiniteGL_iff ℚ 2).1 hu.1).1 i j

theorem eta_mul {u u' : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (hu' : u' ∈ Gamma0Level N) :
    eta χ (u * u') = eta χ u * eta χ u' := by
  rw [eta, eta, eta, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two,
    res_add_mul hu.2 (entry_int hu' 0 1) (entry_int hu 1 1) (entry_int hu' 1 1), map_mul, mul_inv]

theorem eta_one : eta χ 1 = 1 := by simp [eta, res_one]

theorem eta_diag (s : SL(2, ℤ)) :
    eta χ (finiteDiagonal ℚ 2 (Matrix.SpecialLinearGroup.mapGL ℚ s)) = (χ ((s 1 1 : ℤ) : ZMod N))⁻¹ := by
  rw [eta, finiteDiagonal_apply, mapGL_apply, map_intCast, res_intCast]

theorem chi_ne {s : SL(2, ℤ)} (hs : s ∈ Gamma0 N) : χ ((s 1 1 : ℤ) : ZMod N) ≠ 0 := by
  have h0 : ((s 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.1 hs
  have hd : (s 0 0) * (s 1 1) - (s 0 1) * (s 1 0) = 1 := by
    have := s.det_coe
    rwa [Matrix.det_fin_two] at this
  have hd' : ((s 0 0 : ℤ) : ZMod N) * ((s 1 1 : ℤ) : ZMod N) = 1 := by
    have := congrArg (Int.cast : ℤ → ZMod N) hd
    push_cast at this
    rw [h0] at this
    simpa using this
  exact ((IsUnit.of_mul_eq_one _ (by rw [mul_comm]; exact hd')).map χ).ne_zero

variable (N) in

def decU (g : AdelicGL ℚ 2) : FiniteAdelicGL ℚ 2 :=
  (decompGL_spec N g).2.choose_spec.choose

theorem decU_spec (g : AdelicGL ℚ 2) : decU N g ∈ Gamma0Level N ∧
    ∃ γ : GL (Fin 2) ℚ, g = diagonal ℚ 2 γ * realEmb (decompGL N g) * finEmb ℚ 2 (decU N g) :=
  ⟨(decompGL_spec N g).2.choose_spec.choose_spec.1, _, (decompGL_spec N g).2.choose_spec.choose_spec.2⟩

def Auto (A : GL (Fin 2) ℝ → ℂ) : Prop :=
  ∀ s ∈ Gamma0 N, ∀ h : GL (Fin 2) ℝ, 0 < h.det.val →
    A (Matrix.SpecialLinearGroup.mapGL ℝ s * h) = χ ((s 1 1 : ℤ) : ZMod N) * A h

def lift (A : GL (Fin 2) ℝ → ℂ) (g : AdelicGL ℚ 2) : ℂ := A (decompGL N g) * eta χ (decU N g)

variable {χ} {A : GL (Fin 2) ℝ → ℂ}

theorem eq_of_decomp (hA : Auto χ A)
    {γ₁ γ₂ : GL (Fin 2) ℚ} {h₁ h₂ : GL (Fin 2) ℝ} {u₁ u₂ : FiniteAdelicGL ℚ 2}
    (hpos₁ : 0 < h₁.det.val) (hpos₂ : 0 < h₂.det.val) (hu₁ : u₁ ∈ Gamma0Level N)
    (hu₂ : u₂ ∈ Gamma0Level N)
    (heq : diagonal ℚ 2 γ₁ * realEmb h₁ * finEmb ℚ 2 u₁ =
      diagonal ℚ 2 γ₂ * realEmb h₂ * finEmb ℚ 2 u₂) :
    A h₁ * eta χ u₁ = A h₂ * eta χ u₂ := by
  have hc := congrArg (prodEquiv ℚ 2) heq
  simp only [map_mul, diagonal_eq, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one,
    one_mul, Prod.mk.injEq] at hc
  obtain ⟨δ, hδdef⟩ : ∃ δ, δ = γ₂⁻¹ * γ₁ := ⟨_, rfl⟩
  have hreal : toReal δ * h₁ = h₂ := realInf_injective (by
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.1, inv_mul_cancel_left])
  have hfin : finiteDiagonal ℚ 2 δ = u₂ * u₁⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    simp only [hδdef, map_mul, map_inv, mul_assoc, hc.2, inv_mul_cancel_left]
  have hδ : finiteDiagonal ℚ 2 δ ∈ Gamma0Level N := hfin ▸ mul_mem hu₂ (inv_mem hu₁)
  have hdetδ : 0 < (δ.det.val : ℚ) := by
    have hprod : (toReal δ).det.val * h₁.det.val = h₂.det.val := by
      rw [← hreal, MonoidHom.map_mul Matrix.GeneralLinearGroup.det, Units.val_mul]
    rw [det_toReal] at hprod
    have hb : 0 < ((δ.det.val : ℚ) : ℝ) * h₁.det.val := hprod ▸ hpos₂
    have : (0 : ℝ) < ((δ.det.val : ℚ) : ℝ) := by
      by_contra hneg
      push Not at hneg
      nlinarith
    exact_mod_cast this
  obtain ⟨s, hs, hsδ⟩ := exists_mem_Gamma0_of_mem N hδ hdetδ
  have hu₂' : u₂ = finiteDiagonal ℚ 2 δ * u₁ := by rw [hfin, inv_mul_cancel_right]
  rw [hu₂', eta_mul χ hδ hu₁, ← hsδ, eta_diag, ← hreal, ← hsδ, toReal_mapGL, hA s hs h₁ hpos₁]
  have := chi_ne χ hs
  field_simp

theorem lift_apply (hA : Auto χ A) (γ : GL (Fin 2) ℚ) {h : GL (Fin 2) ℝ} (hpos : 0 < h.det.val)
    {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) :
    lift χ A (diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u) = A h * eta χ u := by
  set g := diagonal ℚ 2 γ * realEmb h * finEmb ℚ 2 u with hg
  obtain ⟨hu', γ', heq⟩ := decU_spec (N := N) g
  exact eq_of_decomp hA (decompGL_spec N g).1 hpos hu' hu (heq.symm.trans hg)

theorem lift_real (hA : Auto χ A) {x : GL (Fin 2) ℝ} (hx : 0 < x.det.val) :
    lift χ A (realEmb x) = A x := by
  have := lift_apply hA 1 hx (one_mem (Gamma0Level N))
  rwa [map_one, map_one, one_mul, mul_one, eta_one, mul_one] at this

theorem lift_left (hA : Auto χ A) (δ : GL (Fin 2) ℚ) (g : AdelicGL ℚ 2) :
    lift χ A (diagonal ℚ 2 δ * g) = lift χ A g := by
  obtain ⟨hu, γ, hg⟩ := decU_spec (N := N) g
  have hpos := (decompGL_spec N g).1
  conv_lhs => rw [hg, ← mul_assoc, ← mul_assoc, ← map_mul]
  rw [lift_apply hA _ hpos hu]
  rfl

theorem lift_fin (hA : Auto χ A) (g : AdelicGL ℚ 2) {v : FiniteAdelicGL ℚ 2} (hv : v ∈ Gamma0Level N) :
    lift χ A (g * finEmb ℚ 2 v) = eta χ v * lift χ A g := by
  obtain ⟨hu, γ, hg⟩ := decU_spec (N := N) g
  have hpos := (decompGL_spec N g).1
  conv_lhs => rw [hg, mul_assoc, ← map_mul]
  rw [lift_apply hA _ hpos (mul_mem hu hv), eta_mul χ hu hv, lift]
  ring

theorem lift_mul_real (hA : Auto χ A) (g : AdelicGL ℚ 2) {y : GL (Fin 2) ℝ} (hy : 0 < y.det.val) {c : ℂ}
    (hc : ∀ h : GL (Fin 2) ℝ, 0 < h.det.val → A (h * y) = c * A h) :
    lift χ A (g * realEmb y) = c * lift χ A g := by
  obtain ⟨hu, γ, hg⟩ := decU_spec (N := N) g
  have hpos := (decompGL_spec N g).1
  have e : g * realEmb y = diagonal ℚ 2 γ * realEmb (decompGL N g * y) * finEmb ℚ 2 (decU N g) := by
    conv_lhs => rw [hg]
    rw [map_mul, mul_assoc _ (finEmb ℚ 2 (decU N g)), ← realEmb_mul_finEmb_comm, ← mul_assoc,
      mul_assoc (diagonal ℚ 2 γ)]
  have hpos' : 0 < (decompGL N g * y).det.val := by
    rw [map_mul, Units.val_mul]
    exact mul_pos hpos hy
  rw [e, lift_apply hA _ hpos' hu, hc _ hpos, lift]
  ring

end Lift

section Cont

variable {χ : DirichletCharacter ℂ N} {A : GL (Fin 2) ℝ → ℂ}

theorem continuous_realPartGL : Continuous (realPart : AdelicGL ℚ 2 → GL (Fin 2) ℝ) := by
  have h1 : Continuous (Matrix.GeneralLinearGroup.map (n := Fin 2) RationalIdeles.realEquiv.toRingHom :
      GL (Fin 2) (InfiniteAdeleRing ℚ) → GL (Fin 2) ℝ) :=
    Continuous.units_map _ (Continuous.matrix_map continuous_id RationalIdeles.continuous_realEquiv)
  exact h1.comp (continuous_fst.comp (prodEquiv ℚ 2).continuous)

theorem lift_cont (hA : Auto χ A) (hc : ContinuousOn A {h | 0 < h.det.val}) :
    Continuous (lift χ A) := by
  refine continuous_iff_continuousAt.2 fun g₀ => ?_
  obtain ⟨hu, γ, hg⟩ := decU_spec (N := N) g₀
  have hpos := (decompGL_spec N g₀).1
  set x₀ := decompGL N g₀ with hx₀
  set u₀ := decU N g₀ with hu₀
  obtain ⟨n, hn⟩ := exists_int_sub_mem N (entry_int hu 1 1)
  let R : AdelicGL ℚ 2 → GL (Fin 2) ℝ := fun g => realPart (diagonal ℚ 2 γ⁻¹ * g)
  let F : AdelicGL ℚ 2 → FiniteAdelicGL ℚ 2 := fun g => (prodEquiv ℚ 2 (diagonal ℚ 2 γ⁻¹ * g)).2
  have hL : Continuous fun g : AdelicGL ℚ 2 => diagonal ℚ 2 γ⁻¹ * g := continuous_const.mul continuous_id
  have hR : Continuous R := continuous_realPartGL.comp hL
  have hF : Continuous F := continuous_snd.comp ((prodEquiv ℚ 2).continuous.comp hL)
  have hdec : ∀ g, g = diagonal ℚ 2 γ * realEmb (R g) * finEmb ℚ 2 (F g) := by
    intro g
    rw [mul_assoc, realEmb_realPart_mul_finEmb, map_inv, mul_inv_cancel_left]
  have hg' : diagonal ℚ 2 γ⁻¹ * g₀ = realEmb x₀ * finEmb ℚ 2 u₀ := by
    conv_lhs => rw [hg]
    rw [map_inv, mul_assoc, inv_mul_cancel_left]
  have hp0 : prodEquiv ℚ 2 (diagonal ℚ 2 γ⁻¹ * g₀) = (realInf x₀, u₀) := by
    rw [hg', map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  have hF0 : F g₀ = u₀ := congrArg Prod.snd hp0
  have hR0 : R g₀ = x₀ := realInf_injective ((realInf_realPart _).trans (congrArg Prod.fst hp0))
  have hdetc : Continuous fun g => ((R g).det.val : ℝ) :=
    Units.continuous_val.comp (Matrix.GeneralLinearGroup.continuous_det.comp hR)
  have hentry : Continuous fun g => ((F g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 - (n : 𝔸f)) :=
    ((Units.continuous_val.comp hF).matrix_elem 1 1).sub continuous_const
  have hW1 : ∀ᶠ g in 𝓝 g₀, 0 < (R g).det.val :=
    (isOpen_lt continuous_const hdetc).mem_nhds (by simpa [hR0] using hpos)
  have hW2 : ∀ᶠ g in 𝓝 g₀, F g ∈ Gamma0Level N :=
    ((isOpen_Gamma0Level N).preimage hF).mem_nhds (by simpa [hF0] using hu)
  have hW3 : ∀ᶠ g in 𝓝 g₀, (F g : Matrix (Fin 2) (Fin 2) 𝔸f) 1 1 - (n : 𝔸f) ∈ levelIdeal N :=
    ((isOpen_levelIdeal N).preimage hentry).mem_nhds (by simpa [hF0] using hn)
  have hAt : ContinuousAt (fun g => A (R g) * (χ (n : ZMod N))⁻¹) g₀ := by
    have h1 : ContinuousAt A (R g₀) := hc.continuousAt
      ((isOpen_lt continuous_const (Units.continuous_val.comp
        Matrix.GeneralLinearGroup.continuous_det)).mem_nhds (by simpa [hR0] using hpos))
    exact (ContinuousAt.comp (f := R) h1 hR.continuousAt).mul continuousAt_const
  refine hAt.congr ?_
  filter_upwards [hW1, hW2, hW3] with g h1 h2 h3
  conv_rhs => rw [hdec g]
  rw [lift_apply hA γ h1 h2, eta, res_eq h3]

end Cont

section Form

variable {k : ℕ} {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} {a : ℕ → ℂ}

theorem form_apply (hf : IsForm k N χ f a) {s : SL(2, ℤ)} (hs : s ∈ Gamma0 N) (z : UpperHalfPlane) :
    (f : UpperHalfPlane → ℂ) (Matrix.SpecialLinearGroup.mapGL ℝ s • z) =
      χ ((s 1 1 : ℤ) : ZMod N) * UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ s) (z : ℂ) ^ (k : ℤ) *
        (f : UpperHalfPlane → ℂ) z := by
  have h : ((f : UpperHalfPlane → ℂ) ∣[(k : ℤ)] (Matrix.SpecialLinearGroup.mapGL ℝ s)) z =
      χ ((s 1 1 : ℤ) : ZMod N) * (f : UpperHalfPlane → ℂ) z := by
    have := congrFun (hf.char s hs) z
    rw [ModularForm.SL_slash] at this
    exact this
  have hg1 : (Matrix.SpecialLinearGroup.mapGL ℝ s).det.val = 1 := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]; rfl
  have hgpos : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ s).det.val := by rw [hg1]; exact one_pos
  rw [ModularForm.slash_apply, σ_of_det_pos hgpos, hg1, abs_one, Complex.ofReal_one,
    _root_.one_zpow, mul_one] at h
  have hne := UpperHalfPlane.denom_ne_zero (Matrix.SpecialLinearGroup.mapGL ℝ s) z
  rw [_root_.zpow_neg, ← div_eq_mul_inv, div_eq_iff (zpow_ne_zero _ hne)] at h
  rw [h]
  ring

theorem archLift_auto (hf : IsForm k N χ f a) : Auto χ (archLift (k : ℤ) (f : UpperHalfPlane → ℂ)) := by
  intro s hs h hpos
  have hdet : (Matrix.SpecialLinearGroup.mapGL ℝ s * h).det.val = h.det.val := by
    rw [map_mul, Matrix.SpecialLinearGroup.det_mapGL, one_mul]
  have hne : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ≠ 0 :=
    UpperHalfPlane.denom_ne_zero _ _
  have hA : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ (k : ℤ) *
      UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ s) ((h • UpperHalfPlane.I : UpperHalfPlane) : ℂ) ^ (-(k : ℤ)) = 1 := by
    rw [← zpow_add₀ hne, add_neg_cancel, zpow_zero]
  rw [archLift, archLift, hdet, mul_smul, form_apply hf hs, denom_mul_of_det_pos _ hpos, mul_zpow]
  linear_combination (χ ((s 1 1 : ℤ) : ZMod N) * (Real.sqrt h.det.val : ℂ) ^ (k : ℤ) * f (h • UpperHalfPlane.I) *
    UpperHalfPlane.denom h (UpperHalfPlane.I : ℂ) ^ (-(k : ℤ))) * hA

theorem archLift_cont : ContinuousOn (archLift (k : ℤ) (f : UpperHalfPlane → ℂ)) {h | 0 < h.det.val} := by
  have hop : IsOpen {h : GL (Fin 2) ℝ | 0 < h.det.val} := isOpen_lt continuous_const
    (Units.continuous_val.comp Matrix.GeneralLinearGroup.continuous_det)
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  have hF : DifferentiableOn ℂ ((f : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) {z | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.1 f.holo'
  have hm : 0 < (x : Matrix (Fin 2) (Fin 2) ℝ) 0 0 * (x : Matrix (Fin 2) (Fin 2) ℝ) 1 1 -
      (x : Matrix (Fin 2) (Fin 2) ℝ) 0 1 * (x : Matrix (Fin 2) (Fin 2) ℝ) 1 0 := by
    have : 0 < x.det.val := hx
    rwa [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at this
  have h1 := (contDiffAt_entryLift (k : ℤ) hF hm).continuousAt
  have h2 : Continuous fun h : GL (Fin 2) ℝ => ((h : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ) :=
    Units.continuous_val
  have h3 : ContinuousAt (fun h : GL (Fin 2) ℝ =>
      entryLift (k : ℤ) ((f : UpperHalfPlane → ℂ) ∘ UpperHalfPlane.ofComplex) (h : Matrix (Fin 2) (Fin 2) ℝ)) x :=
    ContinuousAt.comp (f := fun h : GL (Fin 2) ℝ => ((h : Matrix (Fin 2) (Fin 2) ℝ) : Fin 2 → Fin 2 → ℝ)) h1 h2.continuousAt
  refine h3.congr ?_
  filter_upwards [hop.mem_nhds hx] with h hh
  exact (archLift_eq_entryLift _ _ hh).symm

end Form

section Local

theorem ord_of_unit (v : Pl) (x : (Qv v)ˣ) (h1 : (x : Qv v) ∈ v.adicCompletionIntegers ℚ)
    (h2 : ((x⁻¹ : (Qv v)ˣ) : Qv v) ∈ v.adicCompletionIntegers ℚ) : ord (x : Qv v) = 0 := by
  have m1 : (x : Qv v) ∈ 𝒪[Qv v] := (mem_valuationInteger_iff v _).2 h1
  have m2 : ((x⁻¹ : (Qv v)ˣ) : Qv v) ∈ 𝒪[Qv v] := (mem_valuationInteger_iff v _).2 h2
  let u : 𝒪[Qv v]ˣ := ⟨⟨x, m1⟩, ⟨_, m2⟩, Subtype.ext (by simp), Subtype.ext (by simp)⟩
  exact ord_unit u

variable {χ : DirichletCharacter ℂ N} {ω : HeckeCharacter ℚ}

theorem om_eq_eta (hω : Om N χ ω) {u : FiniteAdelicGL ℚ 2} (hu : u ∈ Gamma0Level N) (d : 𝔸fˣ)
    (h1 : ∀ v, ord (lf v d : Qv v) = 0)
    (h2 : ∀ v, pOf v ∣ N → (lf v d : Qv v) = glAt v u 1 1) :
    (ω.toIdele (IdeleGroup.ofFinite d) : ℂ) = eta χ u := by
  obtain ⟨n, hn⟩ := exists_int_sub_mem N (entry_int hu 1 1)
  have key := hω.val d n h1 (fun v hv => ?_)
  · rw [eta, res_eq hn]
    exact eq_inv_of_mul_eq_one_left key
  · obtain ⟨t, ht, e⟩ := hn
    have e' : (glAt v u 1 1 : Qv v) - (n : Qv v) = (N : Qv v) * t v := by
      have := congrArg (adeleAt v) e
      rw [map_sub, map_mul, map_intCast, map_natCast] at this
      exact this
    have hN : (N : Qv v) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
    rw [h2 v hv, e', inv_mul_cancel_left₀ hN]
    exact (mem_valuationInteger_iff v _).2 (ht v)

end Local

theorem rot_eq (r : GL (Fin 2) ℝ) (h1 : r.val * r.valᵀ = 1) (h2 : r.det.val = 1) :
    ∃ (w : ℂ) (hw : w ≠ 0), r = kGL w hw ∧ ‖w‖ = 1 := by
  have e00 := congrFun (congrFun h1 0) 0
  have e01 := congrFun (congrFun h1 0) 1
  have e11 := congrFun (congrFun h1 1) 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.transpose_apply, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide)] at e00 e01 e11
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two] at h2
  set a := r.val 0 0
  set b := r.val 0 1
  set c := r.val 1 0
  set d := r.val 1 1
  have hd : d = a := by linear_combination (-d) * e00 + b * e01 + a * h2
  have hb : b = -c := by linear_combination a * e01 - b * h2 - c * e00
  have hn : Complex.normSq (⟨a, c⟩ : ℂ) = 1 := by
    rw [Complex.normSq_mk]
    rw [hb] at e00
    linarith
  have hw : (⟨a, c⟩ : ℂ) ≠ 0 := by
    intro h
    rw [h] at hn
    simp at hn
  refine ⟨⟨a, c⟩, hw, Matrix.GeneralLinearGroup.ext fun i j => ?_, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [coe_kGL] <;> first | rfl | exact hb | exact hd
  · have : ‖(⟨a, c⟩ : ℂ)‖ ^ 2 = 1 := by rw [← Complex.normSq_eq_norm_sq, hn]
    nlinarith [norm_nonneg (⟨a, c⟩ : ℂ)]

section Cen

def ofInf (x : (InfiniteAdeleRing ℚ)ˣ) : Jd := (IdeleGroup.prodEquiv ℚ).symm (x, 1)

theorem ofInf_mul (x y : (InfiniteAdeleRing ℚ)ˣ) : ofInf (x * y) = ofInf x * ofInf y := by
  simp only [ofInf, ← map_mul, Prod.mk_mul_mk, mul_one]

theorem ofInf_pow (x : (InfiniteAdeleRing ℚ)ˣ) (m : ℕ) : ofInf (x ^ m) = ofInf x ^ m := by
  induction m with
  | zero => simp [ofInf]
  | succ m ih => rw [pow_succ, ofInf_mul, ih, pow_succ]

theorem hecke_pos {c : HeckeCharacter ℚ} (hc : IsOfFinOrder c) (x : (InfiniteAdeleRing ℚ)ˣ)
    (hx : 0 < ((RationalIdeles.realUnitsEquiv x : ℝˣ) : ℝ)) : c.toIdele (ofInf x) = 1 := by
  obtain ⟨m, hm, hcm⟩ := isOfFinOrder_iff_pow_eq_one.1 hc
  set t : ℝ := ((RationalIdeles.realUnitsEquiv x : ℝˣ) : ℝ)
  have hs : 0 < t ^ ((m : ℝ)⁻¹) := Real.rpow_pos_of_pos hx _
  let s : ℝˣ := Units.mk0 _ hs.ne'
  let y : (InfiniteAdeleRing ℚ)ˣ := RationalIdeles.realUnitsEquiv.symm s
  have hy : y ^ m = x := by
    apply RationalIdeles.realUnitsEquiv.injective
    rw [map_pow, ContinuousMulEquiv.apply_symm_apply]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0]
    exact Real.rpow_inv_natCast_pow hx.le hm.ne'
  have h1 : (c ^ m).toIdele (ofInf y) = 1 := by rw [hcm]; rfl
  have h2 : (c ^ m).toIdele (ofInf y) = c.toIdele (ofInf y) ^ m := by
    rw [HeckeCharacter.toIdele_apply, HeckeCharacter.toIdele_apply]
    simp
  rw [← hy, ofInf_pow, map_pow, ← h2, h1]

theorem central_diagonal_commute {R : Type*} [CommRing R] (x : Rˣ) (g : GL (Fin 2) R) : dg2 x x * g = g * dg2 x x := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two, mul_comm]

theorem scalar_diagonal_mul {R : Type*} [CommRing R] (x y : Rˣ) : dg2 (x * y) (x * y) = dg2 x x * dg2 y y := by
  apply Units.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [dg2, Matrix.mul_apply, Fin.sum_univ_two]

theorem diagonal_embedding_scalar_diagonal (a : ℚˣ) : diagonal ℚ 2 (dg2 a a) = dg2 (IdeleGroup.diagonal ℚ a) (IdeleGroup.diagonal ℚ a) := by
  apply Units.ext
  ext i j : 2
  rw [diagonal_apply]
  fin_cases i <;> fin_cases j <;> simp [dg2, IdeleGroup.coe_diagonal]

theorem scalar_diagonal_archimedean_finite_split (p : Jd) (ht : (RationalIdeles.realPart p : ℝ) ≠ 0) :
    dg2 p p = realEmb (kGL (((RationalIdeles.realPart p : ℝˣ) : ℝ) : ℂ) (by exact_mod_cast ht)) *
      finEmb ℚ 2 (dg2 (IdeleGroup.toFinite ℚ p) (IdeleGroup.toFinite ℚ p)) := by
  apply (prodEquiv ℚ 2).injective
  rw [map_mul, prodEquiv_realEmb, prodEquiv_finEmb, Prod.mk_mul_mk, mul_one, one_mul]
  refine Prod.ext (Units.ext (Matrix.ext fun i j => ?_)) (Units.ext (Matrix.ext fun i j => ?_))
  · rw [prodEquiv_apply_fst]
    change _ = RationalIdeles.realEquiv.symm _
    fin_cases i <;> fin_cases j <;> simp [dg2, RationalIdeles.coe_realPart]
  · rw [prodEquiv_apply_snd]
    fin_cases i <;> fin_cases j <;> simp [dg2] <;> rfl

end Cen

section Cen2

theorem cen_decomp (z : Jd) : ∃ (a : ℚˣ) (t : ℝ) (ht : (t : ℂ) ≠ 0) (d : 𝔸fˣ), 0 < t ∧ d ∈ IdeleGroup.finiteLevel 0 ∧
    (∀ c : HeckeCharacter ℚ, IsOfFinOrder c → c.toIdele z = c.toIdele (IdeleGroup.ofFinite d)) ∧
    ∀ g : G2, dg2 z z * g = diagonal ℚ 2 (dg2 a a) * g * realEmb (kGL (t : ℂ) ht) * finEmb ℚ 2 (dg2 d d) := by
  have hz : z ∈ RationalIdeles.positiveSubgroup ⊔ (IdeleGroup.diagonal ℚ).range := by
    rw [RationalIdeles.positiveSubgroup_sup_diagonal_range]
    exact Subgroup.mem_top z
  obtain ⟨p, hp, _, ⟨a, rfl⟩, rfl⟩ := Subgroup.mem_sup.1 hz
  obtain ⟨hp1, hp2⟩ := RationalIdeles.mem_positiveSubgroup.1 hp
  have ht : (((RationalIdeles.realPart p : ℝˣ) : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp2.ne'
  refine ⟨a, _, ht, IdeleGroup.toFinite ℚ p, hp2,
    (IdeleGroup.mem_standardOpenSubgroup_iff_toFinite_mem p).1 hp1, fun c hc => ?_, fun g => ?_⟩
  · have hdec : p = ofInf (IdeleGroup.toInfinite ℚ p) * IdeleGroup.ofFinite (IdeleGroup.toFinite ℚ p) := by
      apply (IdeleGroup.prodEquiv ℚ).injective
      have a1 : ∀ x, IdeleGroup.prodEquiv ℚ (ofInf x) = (x, 1) := fun x =>
        (IdeleGroup.prodEquiv ℚ).apply_symm_apply _
      have a2 : ∀ y, IdeleGroup.prodEquiv ℚ (IdeleGroup.ofFinite y) = (1, y) := fun y =>
        (IdeleGroup.prodEquiv ℚ).apply_symm_apply _
      rw [map_mul, a1, a2, Prod.mk_mul_mk, mul_one, one_mul]
      rfl
    have h1 := hecke_pos hc (IdeleGroup.toInfinite ℚ p) hp2
    rw [map_mul, HeckeCharacter.toIdele_diagonal, mul_one]
    conv_lhs => rw [hdec]
    rw [map_mul, h1, one_mul]
  · rw [scalar_diagonal_mul, diagonal_embedding_scalar_diagonal, mul_assoc (_ * _) _ _, ← scalar_diagonal_archimedean_finite_split p hp2.ne', ← central_diagonal_commute, mul_assoc,
      central_diagonal_commute p g, ← mul_assoc]

theorem unit_at {d : 𝔸fˣ} (hd : d ∈ IdeleGroup.finiteLevel 0) (v : Pl) :
    (d : 𝔸f) v ∈ v.adicCompletionIntegers ℚ ∧ ((d⁻¹ : 𝔸fˣ) : 𝔸f) v ∈ v.adicCompletionIntegers ℚ := by
  have h := IdeleGroup.mem_finiteLevel.1 hd v
  rw [Pi.zero_apply, unitsLevel_zero, Submonoid.mem_units_iff] at h
  refine ⟨h.1, ?_⟩
  have h2 := h.2
  rwa [← map_inv] at h2

theorem scalar_diagonal_mem_level_zero {d : 𝔸fˣ} (hd : d ∈ IdeleGroup.finiteLevel 0) : dg2 d d ∈ Gamma0Level N := by
  refine ⟨(mem_integralFiniteGL_iff ℚ 2).2 ⟨fun i j => ?_, fun i j => ?_⟩, ?_⟩
  · fin_cases i <;> fin_cases j <;> first
      | exact fun v => (unit_at hd v).1
      | exact zero_mem _
  · fin_cases i <;> fin_cases j <;> first
      | exact fun v => (unit_at hd v).2
      | exact zero_mem _
  · exact zero_mem_levelIdeal N

theorem ord_lf {d : 𝔸fˣ} (hd : d ∈ IdeleGroup.finiteLevel 0) (v : Pl) : ord (lf v d : Qv v) = 0 :=
  ord_of_unit v (lf v d) (unit_at hd v).1 (unit_at hd v).2

end Cen2

section Parity

variable {k : ℕ} {χ : DirichletCharacter ℂ N} {f : CuspForm (Gamma1 N) (k : ℤ)} {a : ℕ → ℂ}

theorem coeff_zero {b : ℕ → ℂ} {r : ℝ} (hr : 0 < r) (hb : Summable fun n => b n * (r : ℂ) ^ n)
    (q : ℕ → ℂ) (hq0 : ∀ m, q m ≠ 0) (hq : Tendsto q atTop (𝓝 0))
    (hs : ∀ m, HasSum (fun n => b n * q m ^ n) 0) (n : ℕ) : b n = 0 := by
  set p : FormalMultilinearSeries ℂ ℂ ℂ := FormalMultilinearSeries.ofScalars ℂ b with hp
  have hrad : 0 < p.radius := by
    have hsum : Summable fun n => ‖p n‖ * (⟨r, hr.le⟩ : NNReal) ^ n := by
      have := summable_norm_iff.2 hb
      refine this.congr fun n => ?_
      rw [hp, FormalMultilinearSeries.ofScalars_norm, norm_mul, norm_pow, Complex.norm_real,
        Real.norm_of_nonneg hr.le]
    refine lt_of_lt_of_le ?_ (p.le_radius_of_summable_norm hsum)
    exact ENNReal.coe_pos.2 (NNReal.coe_pos.1 hr)
  have hfp := p.hasFPowerSeriesOnBall hrad
  have han : AnalyticAt ℂ p.sum 0 := hfp.analyticAt
  have hsumz : ∀ m, p.sum (q m) = 0 := by
    intro m
    rw [FormalMultilinearSeries.sum, ← (hs m).tsum_eq]
    refine tsum_congr fun n => ?_
    rw [hp, FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]
  have hqt : Tendsto q atTop (𝓝[≠] 0) :=
    tendsto_nhdsWithin_iff.2 ⟨hq, Eventually.of_forall hq0⟩
  have hfreq : ∃ᶠ z in 𝓝[≠] (0 : ℂ), p.sum z = 0 :=
    hqt.frequently (Frequently.of_forall hsumz)
  have hev := han.frequently_zero_iff_eventually_zero.1 hfreq
  have h0 : HasFPowerSeriesAt (0 : ℂ → ℂ) p 0 := hfp.hasFPowerSeriesAt.congr hev
  have hz := h0.eq_zero
  have := congrArg (fun P : FormalMultilinearSeries ℂ ℂ ℂ => P n fun _ => 1) hz
  simpa [hp, FormalMultilinearSeries.ofScalars_apply_eq] using this

theorem form_ne (hf : IsForm k N χ f a) (h1 : a 1 = 1) : ∃ z, (f : UpperHalfPlane → ℂ) z ≠ 0 := by
  by_contra hall
  push Not at hall
  have hexp : ∀ (y : ℝ) (hy : 0 < y) (n : ℕ),
      Complex.exp (2 * Real.pi * Complex.I * n * ((⟨y * Complex.I, by simpa using hy⟩ : UpperHalfPlane) : ℂ)) =
        ((Real.exp (-2 * Real.pi * y) : ℝ) : ℂ) ^ n := by
    intro y hy n
    rw [Complex.ofReal_exp, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    linear_combination (2 * Real.pi * y * n) * Complex.I_sq
  have hz := fun (y : ℝ) (hy : 0 < y) => hf.exp ⟨y * Complex.I, by simpa using hy⟩
  have key : a 1 = 0 := by
    refine coeff_zero (b := a) (r := Real.exp (-2 * Real.pi * 1)) (Real.exp_pos _) ?_
      (fun m => ((Real.exp (-2 * Real.pi * (m + 1)) : ℝ) : ℂ)) (fun m => ?_) ?_ (fun m => ?_) 1
    · have := (hz 1 one_pos).summable
      simpa only [hexp 1 one_pos] using this
    · exact_mod_cast (Real.exp_pos _).ne'
    · have h1 : Tendsto (fun m : ℕ => Real.exp (-2 * Real.pi * ((m : ℝ) + 1))) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have h2 : Tendsto (fun m : ℕ => (m : ℝ) + 1) atTop atTop :=
          tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
        exact h2.const_mul_atTop_of_neg (by nlinarith [Real.pi_pos])
      have := (Complex.continuous_ofReal.tendsto 0).comp h1
      rw [Complex.ofReal_zero] at this
      exact this
    · have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      have := hz _ hm
      rw [hall] at this
      simpa only [hexp _ hm] using this
  rw [h1] at key
  exact one_ne_zero key

theorem even_im_hermitian_sub (hf : IsForm k N χ f a) (h1 : a 1 = 1) : χ (-1) = (-1) ^ k := by
  obtain ⟨z, hz⟩ := form_ne hf h1
  have hs : (-1 : SL(2, ℤ)) ∈ Gamma0 N := by
    rw [Gamma0_mem]
    simp
  have h := form_apply hf hs z
  have e2 : UpperHalfPlane.denom (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ))) (z : ℂ) = -1 := by
    simp [UpperHalfPlane.denom]
  have hdet : 0 < (Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ))).det.val := by
    rw [Matrix.SpecialLinearGroup.det_mapGL]
    exact one_pos
  have e1 : Matrix.SpecialLinearGroup.mapGL ℝ (-1 : SL(2, ℤ)) • z = z := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_smul_of_det_pos hdet, e2]
    simp [UpperHalfPlane.num]
  have e3 : (((-1 : SL(2, ℤ)) 1 1 : ℤ) : ZMod N) = -1 := by simp
  rw [e1, e2, e3] at h
  have h2 : χ (-1) * (-1 : ℂ) ^ k = 1 := by
    have : (f : UpperHalfPlane → ℂ) z * (1 - χ (-1) * (-1 : ℂ) ^ k) = 0 := by
      rw [zpow_natCast] at h
      linear_combination h
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hz
    · linear_combination -h0
  have h3 : ((-1 : ℂ) ^ k) * (-1 : ℂ) ^ k = 1 := by
    rw [← mul_pow]; simp
  linear_combination ((-1 : ℂ) ^ k) * h2 - χ (-1) * h3

end Parity

theorem adelic_lift_exists : Ad3.R.B0 → Ad3.R.F1 := by
  intro _ k N _ χ f a hf h1 ω hω
  refine ⟨even_im_hermitian_sub hf h1, lift χ (archLift (k : ℤ) (f : UpperHalfPlane → ℂ)), ?_⟩
  have hA := archLift_auto hf
  refine ⟨lift_cont hA archLift_cont, fun γ g => lift_left hA γ g, fun z g => ?_,
    fun x hx => lift_real hA hx, fun r hr hd => ?_, fun u hu d h1 h2 g => ?_⟩
  · obtain ⟨b, t, ht, d, htp, hd, hc, hdec⟩ := cen_decomp z
    have hm : dg2 d d ∈ Gamma0Level N := scalar_diagonal_mem_level_zero hd
    have hone : ∀ h : GL (Fin 2) ℝ, 0 < h.det.val →
        archLift (k : ℤ) (f : UpperHalfPlane → ℂ) (h * kGL (t : ℂ) ht) =
          1 * archLift (k : ℤ) (f : UpperHalfPlane → ℂ) h := by
      intro h hh
      rw [archLift_mul_kGL _ _ hh _ ht, Complex.norm_real, Real.norm_of_nonneg htp.le, div_self ht,
        _root_.one_zpow]
    rw [hdec g, lift_fin hA _ hm, lift_mul_real hA _ (det_kGL_pos _ ht) hone, one_mul, lift_left hA,
      ← om_eq_eta hω hm d (ord_lf hd) (fun v _ => rfl), hc ω hω.fin]
  · obtain ⟨w, hw, rfl, hn⟩ := rot_eq r hr hd
    refine ⟨(w / (‖w‖ : ℂ)) ^ (-(k : ℤ)), ?_, fun g => ?_⟩
    · rw [norm_zpow, norm_div, hn]
      simp
    · exact lift_mul_real hA g (det_kGL_pos w hw) fun h hh => archLift_mul_kGL _ _ hh w hw
  · rw [lift_fin hA g hu, om_eq_eta hω hu d h1 h2]

end GlobalTheory.CompanionTheory.RSLift

end
