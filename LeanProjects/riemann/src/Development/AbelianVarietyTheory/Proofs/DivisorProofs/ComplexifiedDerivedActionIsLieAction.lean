import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSmoothVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjInvol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

namespace GlobalTheory.HolDict.LieAct

section

open Matrix Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.HolDict
open scoped InnerProductSpace ContDiff Topology

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {G : Mt n} {π : Mt n → (H →L[ℂ] H)}

theorem unit_of (hd : G.det ≠ 0) : IsUnit G := (Matrix.isUnit_iff_isUnit_det G).2 hd.isUnit

theorem exists_coef (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (y : H) :
    ∃ D : Mt n →ₗ[ℝ] ℂ, ∀ X ∈ SmVec.lieG G, ⟪y, dRep π X v⟫_ℂ = D X := by
  have hG := unit_of hd
  have hH : ∀ τ : Unit, ((fun _ => G : Unit → Mt n) τ).IsHermitian ∧ ((fun _ => G : Unit → Mt n) τ).det ≠ 0 :=
    fun _ => ⟨hh, hd⟩
  let ev : Chart.Alg n Unit →* Mt n := Pi.evalMonoidHom (fun _ : Unit => Mt n) ()
  have hev : ∀ (t : ℝ) (Y : Chart.Alg n Unit), ev (NormedSpace.exp (t • Y)) = NormedSpace.exp (t • Y ()) :=
    fun t Y => Chart.exp_alg _ _
  obtain ⟨-, D, h1, -⟩ := Chart.chain (Chart.adj_anti hH) (Chart.adj_one hH) (Chart.adj_invol hH) Set.univ
    (by simp) (fun u => ⟪y, π (ev u) v⟫_ℂ)
    (fun k Y _ u hu => by
      have hY : ∀ i, (Y i : Chart.Alg n Unit) () ∈ SmVec.lieG G := fun i =>
        (Chart.skew_iff hH _).1 ((Chart.mem_skew _).1 (Y i).2) ()
      have hu' : ev u ∈ Formalism.QuantumDeterminants.UH G := (Chart.unit_iff hH _).1 hu ()
      simp only [map_mul, map_list_prod, List.map_ofFn, Function.comp_def, hev,
        SmVec.rep_mul hπ hu' (SmVec.expProd_mem_UH hG hY _)]
      exact contDiff_const.inner ℂ (((π (ev u)).restrictScalars ℝ).contDiff.comp (hv k _ hY)))
    (E := ℝ) (γ := fun _ => 1) (x := 0) contDiffAt_const
    (Filter.Eventually.of_forall fun _ => by rw [Chart.adj_one hH, mul_one])
  let c : Mt n →ₗ[ℝ] Chart.Alg n Unit := LinearMap.pi fun _ : Unit => (LinearMap.id : Mt n →ₗ[ℝ] Mt n)
  refine ⟨D.toLinearMap ∘ₗ c, fun X hX => ?_⟩
  have h2 := h1 (c X) ((Chart.skew_iff hH _).2 fun _ => hX)
  simp only [one_mul, hev] at h2
  have h3 := (hasDerivAt_const (0 : ℝ) y).inner ℂ (SmVec.hasDerivAt_dRep hv hX)
  rw [inner_zero_left, add_zero] at h3
  exact h3.deriv.symm.trans h2

theorem add_mem_lie {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) : X + Y ∈ SmVec.lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  have h2 : Yᴴ * G + G * Y = 0 := hY
  show (X + Y)ᴴ * G + G * (X + Y) = 0
  rw [conjTranspose_add, add_mul, mul_add, add_add_add_comm, h1, h2, add_zero]

theorem smul_mem_lie (c : ℝ) {X : Mt n} (hX : X ∈ SmVec.lieG G) : c • X ∈ SmVec.lieG G := by
  have h1 : Xᴴ * G + G * X = 0 := hX
  show (c • X)ᴴ * G + G * (c • X) = 0
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, h1, smul_zero]

theorem neg_mem_lie {X : Mt n} (hX : X ∈ SmVec.lieG G) : -X ∈ SmVec.lieG G := by
  simpa using smul_mem_lie (-1) hX

theorem dRep_lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (a : ℝ) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    dRep π (a • X + Y) v = (a : ℂ) • dRep π X v + dRep π Y v := by
  refine ext_inner_left ℂ fun y => ?_
  obtain ⟨D, hD⟩ := exists_coef hh hd hπ hv y
  rw [inner_add_right, inner_smul_right, hD _ (add_mem_lie (smul_mem_lie a hX) hY), hD _ hX, hD _ hY, map_add,
    map_smul, Complex.real_smul]

theorem conjH_parts (hd : G.det ≠ 0) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    conjH G (X + Complex.I • Y) = X + Complex.I • (-Y) := by
  have h : ∀ W ∈ SmVec.lieG G, G⁻¹ * Wᴴ * G = -W := fun W hW => by
    have h1 : Wᴴ * G + G * W = 0 := hW
    rw [Matrix.mul_assoc, eq_neg_of_add_eq_zero_left h1, Matrix.mul_neg,
      nonsing_inv_mul_cancel_left _ _ hd.isUnit]
  rw [conjH, conjTranspose_add, conjTranspose_smul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
    Matrix.smul_mul, h X hX, h Y hY]
  simp [add_comm]

theorem dRepC_parts (hd : G.det ≠ 0) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) (v : H) :
    dRepC G π (X + Complex.I • Y) v = dRep π X v + Complex.I • dRep π Y v := by
  have e1 : (1 / 2 : ℂ) • (X + Complex.I • Y + (X + Complex.I • (-Y))) = X := by module
  have e2 : (1 / (2 * Complex.I)) • (X + Complex.I • Y - (X + Complex.I • (-Y))) = Y := by
    have : X + Complex.I • Y - (X + Complex.I • (-Y)) = (2 * Complex.I) • Y := by module
    rw [this, smul_smul, one_div_mul_cancel (by simp), one_smul]
  rw [dRepC, conjH_parts hd hX hY, e1, e2]

theorem exists_parts (hh : G.IsHermitian) (hd : G.det ≠ 0) (Z : Mt n) :
    ∃ X ∈ SmVec.lieG G, ∃ Y ∈ SmVec.lieG G, Z = X + Complex.I • Y := by
  refine ⟨_, (SmVec.parts_mem (unit_of hd) hh Z).1, _, (SmVec.parts_mem (unit_of hd) hh Z).2, ?_⟩
  have : Complex.I * (1 / (2 * Complex.I)) = 1 / 2 := by field_simp
  rw [smul_smul, this]
  module

theorem zero_mem_lie : (0 : Mt n) ∈ SmVec.lieG G := by simp [SmVec.lieG]

theorem dRepC_real (hd : G.det ≠ 0) {X : Mt n} (hX : X ∈ SmVec.lieG G) (v : H) : dRepC G π X v = dRep π X v := by
  have := dRepC_parts (π := π) hd hX zero_mem_lie v
  simpa [dRep] using this

theorem dRepC_lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (a : ℂ) (Z Z' : Mt n) :
    dRepC G π (a • Z + Z') v = a • dRepC G π Z v + dRepC G π Z' v := by
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  obtain ⟨X', hX', Y', hY', rfl⟩ := exists_parts hh hd Z'
  obtain ⟨p, q, rfl⟩ : ∃ p q : ℝ, a = p + q * Complex.I := ⟨a.re, a.im, (Complex.re_add_im a).symm⟩
  have e : ((p : ℂ) + q * Complex.I) • (X + Complex.I • Y) + (X' + Complex.I • Y') =
      (p • X + ((-q) • Y + X')) + Complex.I • (q • X + (p • Y + Y')) := by
    simp only [← Complex.coe_smul]
    match_scalars <;> first | ring1 | (push_cast; linear_combination (q : ℂ) * Complex.I_mul_I)
  have m1 := add_mem_lie (smul_mem_lie (-q) hY) hX'
  have m2 := add_mem_lie (smul_mem_lie p hY) hY'
  rw [e, dRepC_parts hd (add_mem_lie (smul_mem_lie p hX) m1) (add_mem_lie (smul_mem_lie q hX) m2),
    dRepC_parts hd hX hY, dRepC_parts hd hX' hY', dRep_lin hh hd hπ hv p hX m1, dRep_lin hh hd hπ hv q hX m2,
    dRep_lin hh hd hπ hv _ hY hX', dRep_lin hh hd hπ hv _ hY hY']
  match_scalars <;> first | ring1 | (push_cast; linear_combination (-q : ℂ) * Complex.I_mul_I)

theorem dRepC_vec (hh : G.IsHermitian) (hd : G.det ≠ 0) {v w : H} (hv : v ∈ SmVec.smSub G π)
    (hw : w ∈ SmVec.smSub G π) (a : ℂ) (Z : Mt n) :
    dRepC G π Z (a • v + w) = a • dRepC G π Z v + dRepC G π Z w := by
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hav := (SmVec.smSub G π).smul_mem a hv
  simp only [dRepC_parts hd hX hY, SmVec.dRep_add hav hw hX, SmVec.dRep_add hav hw hY, SmVec.dRep_smul a hv hX,
    SmVec.dRep_smul a hv hY]
  module

def lin (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) : Mt n →ₗ[ℂ] H where
  toFun Z := dRepC G π Z v
  map_add' Z Z' := by simpa using dRepC_lin hh hd hπ hv 1 Z Z'
  map_smul' a Z := by
    have h0 : dRepC G π 0 v = 0 := by rw [dRepC_real hd zero_mem_lie]; simp [dRep]
    simpa [h0] using dRepC_lin hh hd hπ hv a Z 0

attribute [local instance] Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra in
theorem hasDerivAt_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] (L : Mt n →ₗ[ℂ] E) (X Y : Mt n) :
    HasDerivAt (fun t : ℝ => L (NormedSpace.exp (t • -X) * Y * NormedSpace.exp (t • X))) (L (Y * X - X * Y)) 0 := by
  have h := ((hasDerivAt_exp_smul_const (𝕂 := ℝ) (-X) 0).mul_const Y).mul (hasDerivAt_exp_smul_const (𝕂 := ℝ) X 0)
  have h2 := ((LinearMap.toContinuousLinearMap L).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0 h
  have e : NormedSpace.exp ((0 : ℝ) • -X) * -X * Y * NormedSpace.exp ((0 : ℝ) • X) +
      NormedSpace.exp ((0 : ℝ) • -X) * Y * (NormedSpace.exp ((0 : ℝ) • X) * X) = Y * X - X * Y := by
    simp [sub_eq_add_neg, add_comm]
  rw [← e]
  exact h2

theorem dRepC_bracket_real (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) {X Y : Mt n} (hX : X ∈ SmVec.lieG G) (hY : Y ∈ SmVec.lieG G) :
    dRepC G π (Y * X - X * Y) v = dRep π Y (dRep π X v) - dRep π X (dRep π Y v) := by
  have hG := unit_of hd
  have hXv := SmVec.dRep_mem hG hπ hv hX
  have hYv := SmVec.dRep_mem hG hπ hv hY
  have key : ∀ y ∈ SmVec.smSub G π,
      ⟪y, dRepC G π (Y * X - X * Y) v - (dRep π Y (dRep π X v) - dRep π X (dRep π Y v))⟫_ℂ = 0 := by
    intro y hy
    have h1 := (SmVec.hasDerivAt_dRep hy (neg_mem_lie hX)).inner ℂ (hasDerivAt_conj (lin hh hd hπ hv) X Y)
    have h2 := ((hasDerivAt_const (0 : ℝ) (dRep π Y y)).inner ℂ (SmVec.hasDerivAt_dRep hv hX)).neg
    have e : (fun t : ℝ => ⟪π (NormedSpace.exp (t • -X)) y,
        lin hh hd hπ hv (NormedSpace.exp (t • -X) * Y * NormedSpace.exp (t • X))⟫_ℂ) =
        -fun t : ℝ => ⟪dRep π Y y, π (NormedSpace.exp (t • X)) v⟫_ℂ := by
      funext t
      have hg := SmVec.exp_mem_UH hG hX t
      have hi : NormedSpace.exp (t • -X) = (NormedSpace.exp (t • X))⁻¹ := by rw [smul_neg, Matrix.exp_neg]
      have hu := (Matrix.isUnit_iff_isUnit_det _).1 (SmVec.isUnit_of_mem_UH hG hg)
      show ⟪_, dRepC G π _ v⟫_ℂ = -⟪_, _⟫_ℂ
      rw [hi, dRepC_real hd (SmVec.conj_mem_lieG hG hg hY), ← SmVec.rep_inner hπ hg,
        ← SmVec.rep_mul hπ hg (SmVec.inv_mem_UH hG hg), mul_nonsing_inv _ hu, SmVec.rep_one hπ,
        ← SmVec.dRep_rep hG hπ hv hg hY, SmVec.inner_dRep hG hπ hy (SmVec.rep_mem hG hπ hv hg) hY]
    rw [e] at h1
    have h3 := h1.unique h2
    have hn : dRep π (-X) y = -dRep π X y := by
      have := dRep_lin hh hd hπ hy (-1) hX zero_mem_lie
      simpa [show dRep π 0 y = 0 by simp [dRep]] using this
    simp only [zero_smul, NormedSpace.exp_zero, SmVec.rep_one hπ, inner_zero_left, add_zero, Matrix.one_mul,
      Matrix.mul_one, hn, inner_neg_left] at h3
    change ⟪y, dRepC G π _ v⟫_ℂ + -⟪_, dRepC G π Y v⟫_ℂ = _ at h3
    rw [dRepC_real hd hY] at h3
    rw [inner_sub_right, inner_sub_right, SmVec.inner_dRep hG hπ hy hXv hY, SmVec.inner_dRep hG hπ hy hYv hX]
    linear_combination h3
  refine sub_eq_zero.1 (inner_self_eq_zero.1 (key _ ?_))
  exact sub_mem (SmVec.dRepC_mem hG hh hπ _ hv) (sub_mem (SmVec.dRep_mem hG hπ hXv hY) (SmVec.dRep_mem hG hπ hYv hX))

theorem dRepC_bracket (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) (Z Z' : Mt n) :
    dRepC G π (Z * Z' - Z' * Z) v = dRepC G π Z (dRepC G π Z' v) - dRepC G π Z' (dRepC G π Z v) := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  obtain ⟨X', hX', Y', hY', rfl⟩ := exists_parts hh hd Z'
  have e : (X + Complex.I • Y) * (X' + Complex.I • Y') - (X' + Complex.I • Y') * (X + Complex.I • Y) =
      (X * X' - X' * X) + Complex.I • (X * Y' - Y' * X) + Complex.I • (Y * X' - X' * Y) +
        (Complex.I * Complex.I) • (Y * Y' - Y' * Y) := by
    simp only [add_mul, mul_add, smul_mul_assoc, mul_smul_comm]
    module
  have hl : ∀ W, dRepC G π W v = lin hh hd hπ hv W := fun _ => rfl
  have hs : ∀ {A B C : Mt n}, A ∈ SmVec.lieG G → B ∈ SmVec.lieG G → C ∈ SmVec.lieG G →
      dRep π A (dRep π B v + Complex.I • dRep π C v) = dRep π A (dRep π B v) + Complex.I • dRep π A (dRep π C v) :=
    fun hA hB hC => by
      rw [SmVec.dRep_add (SmVec.dRep_mem hG hπ hv hB) (Submodule.smul_mem _ _ (SmVec.dRep_mem hG hπ hv hC)) hA,
        SmVec.dRep_smul _ (SmVec.dRep_mem hG hπ hv hC) hA]
  rw [e, hl, map_add, map_add, map_add, map_smul, map_smul, map_smul, ← hl, ← hl, ← hl, ← hl,
    dRepC_bracket_real hh hd hπ hv hX' hX, dRepC_bracket_real hh hd hπ hv hY' hX,
    dRepC_bracket_real hh hd hπ hv hX' hY, dRepC_bracket_real hh hd hπ hv hY' hY]
  simp only [dRepC_parts hd hX hY, dRepC_parts hd hX' hY', hs hX hX' hY', hs hY hX' hY', hs hX' hX hY, hs hY' hX hY]
  module

theorem rep_dRepC (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v : H}
    (hv : v ∈ SmVec.smSub G π) {g : Mt n} (hg : g ∈ Formalism.QuantumDeterminants.UH G) (Z : Mt n) :
    π g (dRepC G π Z v) = dRepC G π (g * Z * g⁻¹) (π g v) := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hu := (Matrix.isUnit_iff_isUnit_det _).1 (SmVec.isUnit_of_mem_UH hG hg)
  have hc : ∀ W ∈ SmVec.lieG G, g * W * g⁻¹ ∈ SmVec.lieG G := fun W hW => by
    have := SmVec.conj_mem_lieG hG (SmVec.inv_mem_UH hG hg) hW
    rwa [nonsing_inv_nonsing_inv _ hu] at this
  have he : ∀ W : Mt n, g⁻¹ * (g * W * g⁻¹) * g = W := fun W => by
    simp only [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one, nonsing_inv_mul_cancel_left _ _ hu]
  rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, dRepC_parts hd hX hY, dRepC_parts hd (hc X hX) (hc Y hY),
    SmVec.dRep_rep hG hπ hv hg (hc X hX), SmVec.dRep_rep hG hπ hv hg (hc Y hY), he, he, map_add, map_smul]

theorem inner_dRepC (hh : G.IsHermitian) (hd : G.det ≠ 0) (hπ : IsURepOn (Formalism.QuantumDeterminants.UH G) π) {v w : H}
    (hv : v ∈ SmVec.smSub G π) (hw : w ∈ SmVec.smSub G π) (Z : Mt n) :
    ⟪dRepC G π Z v, w⟫_ℂ = -⟪v, dRepC G π (conjH G Z) w⟫_ℂ := by
  have hG := unit_of hd
  obtain ⟨X, hX, Y, hY, rfl⟩ := exists_parts hh hd Z
  have hn : dRep π (-Y) w = -dRep π Y w := by
    have := dRep_lin hh hd hπ hw (-1) hY zero_mem_lie
    simpa [show dRep π 0 w = 0 by simp [dRep]] using this
  rw [conjH_parts hd hX hY, dRepC_parts hd hX hY, dRepC_parts hd hX (neg_mem_lie hY), hn, inner_add_left,
    inner_add_right, inner_smul_left, inner_smul_right, inner_neg_right, SmVec.inner_dRep hG hπ hv hw hX,
    SmVec.inner_dRep hG hπ hv hw hY, Complex.conj_I]
  ring

end

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem main : ∀ (n : ℕ) (Hm : Mt n) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mt n → (H →L[ℂ] H)), Hm.IsHermitian → Hm.det ≠ 0 → IsURepOn (Formalism.QuantumDeterminants.UH Hm) σ → ∀ v v', SmoothVec (lieH Hm) σ v → SmoothVec (lieH Hm) σ v' → (∀ (a : ℂ) (Z Z' : Mt n), dRepC Hm σ (a • Z + Z') v = a • dRepC Hm σ Z v + dRepC Hm σ Z' v ∧ dRepC Hm σ Z (a • v + v') = a • dRepC Hm σ Z v + dRepC Hm σ Z v' ∧ dRepC Hm σ (Z * Z' - Z' * Z) v = dRepC Hm σ Z (dRepC Hm σ Z' v) - dRepC Hm σ Z' (dRepC Hm σ Z v)) ∧ (∀ X ∈ lieH Hm, dRepC Hm σ X v = dRep σ X v) ∧ (∀ g ∈ Formalism.QuantumDeterminants.UH Hm, ∀ Z, σ g (dRepC Hm σ Z v) = dRepC Hm σ (g * Z * g⁻¹) (σ g v)) ∧ ∀ Z, ⟪dRepC Hm σ Z v, v'⟫_ℂ = -⟪v, dRepC Hm σ (conjH Hm Z) v'⟫_ℂ := by
  intro n Hm H _ _ _ σ hh hd hσ v v' hv hv'
  exact ⟨fun a Z Z' => ⟨dRepC_lin hh hd hσ hv a Z Z', dRepC_vec hh hd hv hv' a Z, dRepC_bracket hh hd hσ hv Z Z'⟩,
    fun X hX => dRepC_real hd hX v, fun g hg Z => rep_dRepC hh hd hσ hv hg Z, inner_dRepC hh hd hσ hv hv'⟩

end GlobalTheory.HolDict.LieAct
