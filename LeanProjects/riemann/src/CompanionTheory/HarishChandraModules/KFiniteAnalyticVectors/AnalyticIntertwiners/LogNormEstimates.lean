import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AnalyticIntertwiners.Clause1
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Upqcpt

open Matrix
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace CompanionTheory.D.gk.HC

open Formalism.BasicNotions.TH

section Adj

variable {p q : ℕ}

def sgD : Ix p q → ℂ := Sum.elim (fun _ => (1 : ℂ)) (fun _ => -1)

theorem Jm_eq_diagD : Jm p q = diagonal (sgD (p := p) (q := q)) := by
  unfold Jm sgD
  exact Formalism.UG.P.Jpq_eq_diagonal p q

theorem Jm_mul_selfD : Jm p q * Jm p q = 1 := Formalism.UG.P.Jpq_mul_self p q

theorem Jm_hermD : (Jm p q)ᴴ = Jm p q := by
  simp [Jm, Formalism.UG.Jpq, Matrix.fromBlocks_conjTranspose]

theorem adjZ_adjZD (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  have h := Jm_mul_selfD (p := p) (q := q)
  simp only [adjZ, conjTranspose_mul, conjTranspose_conjTranspose, Jm_hermD, ← Matrix.mul_assoc, h, Matrix.one_mul]
  rw [Matrix.mul_assoc, h, Matrix.mul_one]

theorem adjZ_addD (X Y : Mat p q) : adjZ (X + Y) = adjZ X + adjZ Y := by
  simp [adjZ, conjTranspose_add, Matrix.mul_add, Matrix.add_mul]

theorem adjZ_smulD (c : ℂ) (X : Mat p q) : adjZ (c • X) = star c • adjZ X := by
  simp [adjZ, conjTranspose_smul, Matrix.mul_smul, Matrix.smul_mul]

theorem mem_upq_of_adjZD {Y : Mat p q} (h : adjZ Y = -Y) : Y ∈ upq p q := by
  show Yᴴ * Jm p q + Jm p q * Y = 0
  have h2 : Jm p q * adjZ Y = -(Jm p q * Y) := by rw [h, Matrix.mul_neg]
  have h3 : Jm p q * adjZ Y = Yᴴ * Jm p q := by
    simp only [adjZ, ← Matrix.mul_assoc, Jm_mul_selfD, Matrix.one_mul]
  rw [← h3, h2, neg_add_cancel]

theorem adjZ_singleD (a b : Ix p q) (h : sameBlock a b) : adjZ (Eab a b) = Eab b a := by
  ext i j
  simp only [adjZ, Eab, Jm_eq_diagD, conjTranspose_single, star_one, mul_diagonal, diagonal_mul, single_apply]
  split_ifs with hij
  · obtain ⟨rfl, rfl⟩ := hij
    rcases a with a | a <;> rcases b with b | b <;> simp_all [sgD, sameBlock]
  · simp

theorem sameBlock_symmD {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [sameBlock]

theorem sameBlock_reflD (a : Ix p q) : sameBlock a a := by rcases a with a | a <;> trivial

theorem sameBlock_of_posCD {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]

theorem isKC_EabD {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := fun c d hcd => by
  simp only [Eab, single_apply]
  split_ifs with h1
  · obtain ⟨rfl, rfl⟩ := h1; exact absurd h hcd
  · rfl

end Adj

section Forms

variable {p q : ℕ} (M : GKMod p q) {H₁ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]

def SkewD (ι : M.V →ₗ[ℂ] H₁) : Prop :=
  ∀ Y ∈ upq p q, ∀ v w, ⟪ι (M.act Y v), ι w⟫_ℂ = -⟪ι v, ι (M.act Y w)⟫_ℂ

variable {M}

theorem adj_ruleD {ι : M.V →ₗ[ℂ] H₁} (h : SkewD M ι) (Z : Mat p q) (v w : M.V) :
    ⟪ι (M.act Z v), ι w⟫_ℂ = ⟪ι v, ι (M.act (adjZ Z) w)⟫_ℂ := by
  set Y₁ : Mat p q := (1 / 2 : ℂ) • (Z - adjZ Z)
  set Y₂ : Mat p q := (-Complex.I / 2) • (Z + adjZ Z)
  have hs : ∀ X : Mat p q, adjZ (-X) = -adjZ X := fun X => by
    rw [show -X = (-1 : ℂ) • X by simp, adjZ_smulD]; simp
  have h1 : adjZ Y₁ = -Y₁ := by
    simp only [Y₁, adjZ_smulD, sub_eq_add_neg, adjZ_addD, hs, adjZ_adjZD]
    rw [show star (1 / 2 : ℂ) = 1 / 2 by simp]
    rw [← smul_neg]; congr 1; abel
  have h2 : adjZ Y₂ = -Y₂ := by
    simp only [Y₂, adjZ_smulD, adjZ_addD, adjZ_adjZD]
    rw [show star (-Complex.I / 2) = Complex.I / 2 by simp [Complex.conj_I], add_comm (adjZ Z)]
    module
  have eZ : Z = Y₁ + Complex.I • Y₂ := by
    simp only [Y₁, Y₂, smul_smul]
    rw [show Complex.I * (-Complex.I / 2) = 1 / 2 by ring_nf; simp [Complex.I_sq]; ring, ← smul_add]
    rw [show Z - adjZ Z + (Z + adjZ Z) = (2 : ℂ) • Z by rw [two_smul]; abel, smul_smul]; norm_num
  clear_value Y₁ Y₂
  have eA : adjZ Z = -Y₁ + Complex.I • Y₂ := by
    rw [eZ, adjZ_addD, adjZ_smulD, h1, h2, show star Complex.I = -Complex.I from Complex.conj_I]
    simp [neg_smul, smul_neg]
  rw [eA]
  conv_lhs => rw [eZ]
  simp only [map_add, map_smul, map_neg, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
    inner_add_left, inner_smul_left, inner_add_right, inner_smul_right, inner_neg_right,
    h Y₁ (mem_upq_of_adjZD h1), h Y₂ (mem_upq_of_adjZD h2), Complex.conj_I]
  ring

end Forms

section Weights

variable {p q : ℕ} {M : GKMod p q}

theorem mem_wtSubD {μ : Ix p q → ℚ} {y : M.V} : y ∈ wtSub M.act μ ↔ ∀ a, M.act (Eab a a) y = ((μ a : ℚ) : ℂ) • y := by
  simp only [wtSub, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem comm_EabD (c a b : Ix p q) :
    Eab c c * Eab a b - Eab a b * Eab c c = ((if c = a then 1 else 0) - (if c = b then 1 else 0) : ℂ) • Eab a b := by
  simp only [Eab]
  by_cases ha : c = a <;> by_cases hb : c = b
  · subst ha; subst hb; simp [single_mul_single_same]
  · subst ha; simp [single_mul_single_same, Ne.symm hb, hb]
  · subst hb; simp [single_mul_single_same, ha]
  · simp [Ne.symm hb, ha, hb]

def shD (μ : Ix p q → ℚ) (a b : Ix p q) : Ix p q → ℚ := μ + Pi.single a 1 - Pi.single b 1

theorem raiseD {μ : Ix p q → ℚ} {y : M.V} (hy : y ∈ wtSub M.act μ) (a b : Ix p q) :
    M.act (Eab a b) y ∈ wtSub M.act (shD μ a b) := by
  rw [mem_wtSubD] at hy ⊢
  intro c
  have h := congrArg (fun T : Module.End ℂ M.V => T y) (M.lie (Eab c c) (Eab a b))
  simp only [comm_EabD, map_smul, LinearMap.smul_apply, Module.End.mul_apply, LinearMap.sub_apply, hy c,
    map_smul] at h
  rw [eq_sub_iff_add_eq] at h
  rw [← h]
  simp only [shD, Pi.add_apply, Pi.sub_apply, Pi.single_apply]
  split_ifs <;> push_cast <;> module

theorem shD_shD (μ : Ix p q → ℚ) (a b : Ix p q) : shD (shD μ a b) b a = μ := by
  funext c; simp only [shD, Pi.add_apply, Pi.sub_apply]; ring

end Weights

section Main

variable {p q : ℕ} {M : GKMod p q} {H₁ H₂ : Type} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]

def cwD : Ix p q → ℚ := Sum.elim (fun i => -(i : ℚ)) (fun j => -(j : ℚ))

theorem cwD_lt {a b : Ix p q} (h : posC a b) : cwD b < cwD a := by
  rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, cwD] <;> exact_mod_cast h

def ellD (μ : Ix p q → ℚ) : ℚ := ∑ a, cwD a * μ a

theorem ellD_shD (μ : Ix p q → ℚ) (a b : Ix p q) : ellD (shD μ a b) = ellD μ + cwD a - cwD b := by
  simp only [ellD, shD, Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

theorem exists_hwD (hn : Nontrivial M.V) : ∃ μ, ∃ y ∈ hwSub M.act μ, y ≠ 0 := by
  classical
  obtain ⟨v, hv⟩ := exists_ne (0 : M.V)
  obtain ⟨μ₀, y₀, hy₀, hy₀0⟩ : ∃ μ₀, ∃ y₀ ∈ wtSub M.act μ₀, y₀ ≠ 0 := by
    by_contra hc
    push_neg at hc
    have : (⨆ μ, wtSub M.act μ) = ⊥ := iSup_eq_bot.2 fun μ => (Submodule.eq_bot_iff _).2 (hc μ)
    exact hv ((Submodule.mem_bot ℂ).1 (this ▸ M.wts v))
  obtain ⟨W, hWf, hyW, hWs⟩ := M.kfin y₀
  let L : Module.End ℂ M.V := ∑ a, ((cwD a : ℚ) : ℂ) • M.act (Eab a a)
  have hLW : ∀ w ∈ W, L w ∈ W := fun w hw => by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply]
    exact W.sum_mem fun a _ => W.smul_mem _ (hWs _ (isKC_EabD (sameBlock_reflD a)) w hw)
  have hLwt : ∀ ν, ∀ y ∈ wtSub M.act ν, L y = ((ellD ν : ℚ) : ℂ) • y := fun ν y hy => by
    rw [mem_wtSubD] at hy
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, hy, smul_smul]
    rw [← Finset.sum_smul]
    congr 1
    unfold ellD
    push_cast
    rfl
  let LW : Module.End ℂ W := L.restrict hLW
  let S : Set ℚ := {r | ∃ ν, ∃ y ∈ W, y ∈ wtSub M.act ν ∧ y ≠ 0 ∧ ellD ν = r}
  have hSf : S.Finite := by
    refine (LW.finite_hasEigenvalue.preimage (f := fun r : ℚ => ((r : ℚ) : ℂ))
      (fun a _ b _ h => Rat.cast_injective h)).subset ?_
    rintro r ⟨ν, y, hyW, hy, hy0, rfl⟩
    show LW.HasEigenvalue _
    refine Module.End.hasEigenvalue_of_hasEigenvector (x := ⟨y, hyW⟩) ⟨?_, fun h => hy0 (congrArg Subtype.val h)⟩
    rw [Module.End.mem_eigenspace_iff]
    exact Subtype.ext (hLwt ν y hy)
  obtain ⟨r, ⟨ν, y, hyW, hy, hy0, rfl⟩, hmax⟩ := hSf.exists_maximal ⟨_, μ₀, y₀, hyW, hy₀, hy₀0, rfl⟩
  refine ⟨ν, y, ?_, hy0⟩
  simp only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
  refine ⟨hy, fun a b hab => ?_⟩
  by_contra hz
  have h1 := hmax ⟨shD ν a b, _, hWs _ (isKC_EabD (sameBlock_of_posCD hab)) y hyW, raiseD hy a b, hz, rfl⟩
  rw [ellD_shD] at h1
  have := cwD_lt hab
  have h2 : ellD ν + cwD a - cwD b ≤ ellD ν := h1 (by linarith)
  linarith

theorem form_propD (ι₁ : M.V →ₗ[ℂ] H₁) (ι₂ : M.V →ₗ[ℂ] H₂) (h₁ : Function.Injective ι₁)
    (h₂ : Function.Injective ι₂) (s₁ : SkewD M ι₁) (s₂ : SkewD M ι₂) (hI : Formalism.MainNotions.SchurIrreducible.IrrGK M)
    (hA : Formalism.MainNotions.SchurIrreducible.AdmGK M) : ∃ c : ℝ, 0 < c ∧ ∀ v w, ⟪ι₂ v, ι₂ w⟫_ℂ = (c : ℂ) * ⟪ι₁ v, ι₁ w⟫_ℂ := by
  classical
  obtain ⟨μ, v, hvY, hv0⟩ := exists_hwD hI.1

  set Y := hwSub M.act μ
  haveI : FiniteDimensional ℂ Y := hA μ
  set Y₁ : Submodule ℂ H₁ := Y.map ι₁
  let e₁ : Y ≃ₗ[ℂ] Y₁ := Submodule.equivMapOfInjective ι₁ h₁ Y
  have he₁ : ∀ y : Y, ((e₁ y : Y₁) : H₁) = ι₁ y := fun y => rfl
  haveI : FiniteDimensional ℂ Y₁ := LinearEquiv.finiteDimensional e₁
  haveI : Nontrivial Y₁ := ⟨⟨e₁ ⟨v, hvY⟩, 0, fun h => hv0 (by
    have := congrArg Subtype.val (e₁.injective (h.trans e₁.map_zero.symm)); exact this)⟩⟩
  let β : Y₁ → Y₁ → ℂ := fun x x' => ⟪ι₂ (e₁.symm x), ι₂ (e₁.symm x')⟫_ℂ
  let f : Y₁ → (Y₁ →L[ℂ] ℂ) := fun x => LinearMap.toContinuousLinearMap
    { toFun := fun x' => β x x'
      map_add' := fun a b => by simp [β, inner_add_right]
      map_smul' := fun c a => by simp [β, inner_smul_right] }
  let T : Y₁ →ₗ[ℂ] Y₁ :=
    { toFun := fun x => (InnerProductSpace.toDual ℂ Y₁).symm (f x)
      map_add' := fun a b => ext_inner_right ℂ fun z => by
        simp only [InnerProductSpace.toDual_symm_apply, inner_add_left, f, β, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_mk, AddHom.coe_mk, map_add, Submodule.coe_add]
      map_smul' := fun c a => ext_inner_right ℂ fun z => by
        simp only [InnerProductSpace.toDual_symm_apply, inner_smul_left, f, β, LinearMap.coe_toContinuousLinearMap',
          LinearMap.coe_mk, AddHom.coe_mk, map_smul, RingHom.id_apply, Submodule.coe_smul, inner_smul_left] }
  have hT : ∀ x x', ⟪T x, x'⟫_ℂ = β x x' := fun x x' => InnerProductSpace.toDual_symm_apply
  have hTs : T.IsSymmetric := fun x x' => by
    rw [hT, ← inner_conj_symm, hT]
    simp only [β, inner_conj_symm]
  obtain ⟨x₀, hx₀⟩ := (hTs.hasEigenvalue_iSup_of_finiteDimensional).exists_hasEigenvector
  set lam : ℝ := ⨆ x : { x : Y₁ // x ≠ 0 }, RCLike.re ⟪T x, x⟫_ℂ / ‖(x : Y₁)‖ ^ 2
  have hTx : T x₀ = (lam : ℂ) • x₀ := Module.End.mem_eigenspace_iff.1 hx₀.1
  set v₀ : Y := e₁.symm x₀
  have hv₀0 : (v₀ : M.V) ≠ 0 := fun h => hx₀.2 (by
    have : v₀ = 0 := Subtype.ext h
    simpa [v₀] using congrArg e₁ this)
  have hx₀v : (x₀ : H₁) = ι₁ (v₀ : M.V) := by rw [← he₁]; simp [v₀]
  have key2 : ∀ y ∈ Y, ⟪ι₂ (v₀ : M.V), ι₂ y⟫_ℂ = (lam : ℂ) * ⟪ι₁ (v₀ : M.V), ι₁ y⟫_ℂ := fun y hy => by
    have h := hT x₀ (e₁ ⟨y, hy⟩)
    rw [hTx, inner_smul_left, Complex.conj_ofReal] at h
    simp only [β, LinearEquiv.symm_apply_apply] at h
    rw [← h, Submodule.coe_inner, he₁, hx₀v]
  have hpos : 0 < lam := by
    have h := key2 v₀ v₀.2
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
    have n1 : 0 < ‖ι₂ (v₀ : M.V)‖ := norm_pos_iff.2 fun h' => hv₀0 (h₂ (h'.trans (map_zero ι₂).symm))
    have n2 : 0 < ‖ι₁ (v₀ : M.V)‖ := norm_pos_iff.2 fun h' => hv₀0 (h₁ (h'.trans (map_zero ι₁).symm))
    have h' : ‖ι₂ (v₀ : M.V)‖ ^ 2 = lam * ‖ι₁ (v₀ : M.V)‖ ^ 2 := by
      apply Complex.ofReal_injective; push_cast; exact h
    nlinarith [pow_pos n1 2, pow_pos n2 2]

  have hv₀hw : ∀ a b, posC a b → M.act (Eab a b) (v₀ : M.V) = 0 := fun a b hab => by
    have := v₀.2
    simp only [Y, hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker] at this
    exact this.2 a b hab
  have hv₀wt : (v₀ : M.V) ∈ wtSub M.act μ := (Submodule.mem_inf.1 v₀.2).1
  let F : M.V →ₗ[ℂ] ℂ :=
    { toFun := fun w => ⟪ι₂ (v₀ : M.V), ι₂ w⟫_ℂ - (lam : ℂ) * ⟪ι₁ (v₀ : M.V), ι₁ w⟫_ℂ
      map_add' := fun a b => by simp only [map_add, inner_add_right]; ring
      map_smul' := fun c a => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring }
  have hFZ : ∀ Z w, F (M.act Z w) = ⟪ι₂ (M.act (adjZ Z) (v₀ : M.V)), ι₂ w⟫_ℂ -
      (lam : ℂ) * ⟪ι₁ (M.act (adjZ Z) (v₀ : M.V)), ι₁ w⟫_ℂ := fun Z w => by
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk]
    rw [adj_ruleD s₂, adj_ruleD s₁, adjZ_adjZD]
  have hR : ∀ a b, posC a b → ∀ u, F (M.act (Eab b a) u) = 0 := fun a b hab u => by
    rw [hFZ, adjZ_singleD b a (sameBlock_symmD (sameBlock_of_posCD hab)), hv₀hw a b hab]
    simp
  have hne : ∀ ν, ν ≠ μ → ∀ w ∈ wtSub M.act ν, F w = 0 := by
    intro ν hν w hw
    obtain ⟨a, ha⟩ := Function.ne_iff.1 hν
    have e1 := hFZ (Eab a a) w
    have hc : conj (((μ a : ℚ) : ℂ)) = ((μ a : ℚ) : ℂ) := by
      rw [show ((μ a : ℚ) : ℂ) = (((μ a : ℚ) : ℝ) : ℂ) by push_cast; rfl, Complex.conj_ofReal]
    rw [adjZ_singleD a a (sameBlock_reflD a), (mem_wtSubD.1 hv₀wt) a, (mem_wtSubD.1 hw) a] at e1
    simp only [map_smul, inner_smul_left, hc] at e1
    have e2 : ((ν a : ℚ) : ℂ) * F w = ((μ a : ℚ) : ℂ) * F w := by
      rw [← smul_eq_mul, e1]; simp only [F, LinearMap.coe_mk, AddHom.coe_mk]; ring
    have hne' : ((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ) ≠ 0 := sub_ne_zero.2 fun h => ha (Rat.cast_injective h)
    have e3 : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) * F w = 0 := by rw [sub_mul, e2, sub_self]
    exact (mul_eq_zero.1 e3).resolve_left hne'
  have heq : ∀ w ∈ wtSub M.act μ, F w = 0 := by
    intro w hw
    obtain ⟨W, hWf, hwW, hWs⟩ := M.kfin w
    let Rsp : Submodule ℂ M.V := Submodule.span ℂ {x | ∃ a b, posC a b ∧ ∃ u ∈ W, x = M.act (Eab b a) u}
    let Lw : Submodule ℂ M.V := W ⊓ wtSub M.act μ ⊓ Rsp
    haveI : FiniteDimensional ℂ Lw := Submodule.finiteDimensional_of_le (inf_le_left.trans inf_le_left)
    set L₁ : Submodule ℂ H₁ := Lw.map ι₁
    haveI : FiniteDimensional ℂ L₁ := Module.Finite.map _ _
    have hP : L₁.starProjection (ι₁ w) ∈ L₁ := (L₁.orthogonalProjectionOnto (ι₁ w)).2
    obtain ⟨l, hl, hlP⟩ := Submodule.mem_map.1 hP
    have hperp : ∀ x ∈ Lw, ⟪ι₁ (w - l), ι₁ x⟫_ℂ = 0 := fun x hx => by
      rw [map_sub, hlP]
      exact Submodule.starProjection_inner_eq_zero _ _ (Submodule.mem_map_of_mem hx)
    have hlL := (Submodule.mem_inf.1 (Submodule.mem_inf.1 hl).1)
    have hyW : w - l ∈ W := W.sub_mem hwW hlL.1
    have hywt : w - l ∈ wtSub M.act μ := Submodule.sub_mem _ hw hlL.2
    have hyhw : w - l ∈ hwSub M.act μ := by
      simp only [hwSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker]
      refine ⟨hywt, fun a b hab => ?_⟩
      set z := M.act (Eab a b) (w - l)
      have hzW : z ∈ W := hWs _ (isKC_EabD (sameBlock_of_posCD hab)) _ hyW
      have hbz : M.act (Eab b a) z ∈ Lw := by
        refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨hWs _ (isKC_EabD (sameBlock_symmD (sameBlock_of_posCD hab))) _ hzW, ?_⟩,
          Submodule.subset_span ⟨a, b, hab, z, hzW, rfl⟩⟩
        have := raiseD (raiseD hywt a b) b a
        rwa [shD_shD] at this
      have h0 : ⟪ι₁ z, ι₁ z⟫_ℂ = 0 := by
        rw [adj_ruleD s₁, adjZ_singleD a b (sameBlock_of_posCD hab)]
        exact hperp _ hbz
      exact h₁ ((inner_self_eq_zero.1 h0).trans (map_zero ι₁).symm)
    have hFl : F l = 0 := by
      have hlR := (Submodule.mem_inf.1 hl).2
      refine Submodule.span_induction (p := fun x _ => F x = 0) ?_ (map_zero F) (fun x y _ _ hx hy => by
        rw [map_add, hx, hy, add_zero]) (fun c x _ hx => by rw [map_smul, hx, smul_zero]) hlR
      rintro x ⟨a, b, hab, u, -, rfl⟩
      exact hR a b hab u
    have hFy : F (w - l) = 0 := by
      simp only [F, LinearMap.coe_mk, AddHom.coe_mk]
      rw [key2 _ hyhw, sub_self]
    have : w = (w - l) + l := by abel
    rw [this, map_add, hFy, hFl, add_zero]
  have hall : ∀ w, F w = 0 := fun w => by
    refine Submodule.iSup_induction (fun ν => wtSub M.act ν) (motive := fun x => F x = 0) (M.wts w)
      (fun ν x hx => ?_) (map_zero F) (fun x y hx hy => by simp only [map_add, hx, hy, add_zero])
    by_cases h : ν = μ
    · subst h; exact heq x hx
    · exact hne ν h x hx

  let R : Submodule ℂ M.V :=
    { carrier := {x | ∀ w, ⟪ι₂ x, ι₂ w⟫_ℂ = (lam : ℂ) * ⟪ι₁ x, ι₁ w⟫_ℂ}
      add_mem' := fun {a b} ha hb w => by simp only [Set.mem_setOf_eq, map_add, inner_add_left, ha w, hb w]; ring
      zero_mem' := fun w => by simp
      smul_mem' := fun c a ha w => by simp only [Set.mem_setOf_eq, map_smul, inner_smul_left, ha w]; ring }
  have hRst : ∀ Z, ∀ y ∈ R, M.act Z y ∈ R := fun Z y hy w => by
    rw [adj_ruleD s₂, hy, adj_ruleD s₁]
  have hv₀R : (v₀ : M.V) ∈ R := fun w => by
    have := hall w
    simp only [F, LinearMap.coe_mk, AddHom.coe_mk] at this
    exact sub_eq_zero.1 this
  rcases hI.2 R hRst with h | h
  · exact absurd ((Submodule.eq_bot_iff R).1 h _ hv₀R) hv₀0
  · exact ⟨lam, hpos, fun v w => (h ▸ Submodule.mem_top : v ∈ R) w⟩

end Main

end CompanionTheory.D.gk.HC
