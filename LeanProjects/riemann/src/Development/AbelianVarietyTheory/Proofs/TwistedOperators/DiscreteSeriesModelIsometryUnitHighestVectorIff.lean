import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtremalLowestKtypeKilledByCompactRoots

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

noncomputable section

namespace GlobalTheory.ArchRec.HighTie

open GlobalTheory.RealPar.TorusWt GlobalTheory.RealPar.KStabLie GlobalTheory.CoverKGen

variable {p q n : ℕ} {T : GrpData p q}

theorem torus_iff (R : DSRep T) (ν : Ix p q → ℝ) (v : R.HK.V) :
    (∀ θ : Ix p q → ℝ, R.U.π (T.expt (torX θ)) (R.ι v) =
      Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) • R.ι v) ↔
    ∀ a, R.HK.act (Eab a a) v = ((ν a : ℝ) : ℂ) • v := by
  constructor
  · intro h a
    set θ : Ix p q → ℝ := Pi.single a 1 with hθ
    have h0 := R.der _ (torX_mem θ) v
    have h1 : (fun t : ℝ => R.U.π (T.expt (t • torX θ)) (R.ι v)) =
        fun t : ℝ => Complex.exp ((ν a * Complex.I) * t) • R.ι v := by
      funext t
      rw [smul_torX, h]
      congr 2
      rw [Finset.sum_eq_single a]
      · simp [hθ]; ring
      · intro c _ hc; simp [hθ, hc]
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((ν a * Complex.I) * t) • R.ι v)
        ((ν a * Complex.I) • R.ι v) 0 := by
      have : HasDerivAt (fun t : ℝ => ((ν a * Complex.I) * (t : ℂ))) (ν a * Complex.I) 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (ν a * Complex.I))
      simpa using this.cexp.smul_const (R.ι v)
    rw [h1] at h0
    have h3 := h0.unique h2
    rw [← map_smul] at h3
    have h4 := R.ι_inj h3
    have h5 : torX θ = Complex.I • Eab a a := by
      rw [torX_eq_sum, Finset.sum_eq_single a]
      · simp [hθ]
      · intro c _ hc; simp [hθ, hc]
      · simp
    rw [h5, map_smul, LinearMap.smul_apply, mul_comm, mul_smul] at h4
    exact smul_right_injective _ Complex.I_ne_zero h4
  · intro h θ
    apply flow_eq R (torX_mem _)
    rw [torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h, smul_smul, ← Finset.sum_smul]
    congr 1
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

def sb (b : Bool) : ℝ := if b then -1 else 1

theorem sb_mul_self (b : Bool) : sb b * sb b = 1 := by cases b <;> simp [sb]

theorem sg_eq (br cj : Bool) : sg br cj = sb br * sb cj := by cases br <;> cases cj <;> simp [sb, sg]

theorem cjc_exp (cj : Bool) (r : ℝ) :
    cjc cj (Complex.exp ((r : ℂ) * Complex.I)) = Complex.exp (((sb cj * r : ℝ) : ℂ) * Complex.I) := by
  cases cj <;> simp [cjc, sb, ← Complex.exp_conj]

theorem cjc_cjc (cj : Bool) (z : ℂ) : cjc cj (cjc cj z) = z := by cases cj <;> simp [cjc]

theorem phi_torus (br : Bool) (e : Ix p q ≃ Fin n) (θ : Ix p q → ℝ) :
    phi br e ((T.cov (T.expt (torX θ)) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun j => Complex.exp (((sb br * θ (e.symm j) : ℝ) : ℂ) * Complex.I) := by
  rw [cov_expt_torX]
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  by_cases h : a = b
  · subst h
    cases br <;> simp [phi, sb, barMat, plainMat, ← Complex.exp_conj]
  · cases br <;> simp [phi, sb, barMat, plainMat, h]

theorem phi_mem_Kset {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) {x : T.G}
    (hx : x ∈ T.Kset) : phi br e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) ∈ Formalism.REAL.Kset ε := by
  have h0 := (GlobalTheory.RealPar.mem_Upq _).1 (T.cov_mem x)
  have h1 : Formalism.REAL.inUJ ε (phi br e ((T.cov x : GL (Ix p q) ℂ) : Mat p q)) := by
    cases br
    · exact GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat_mem h h0
    · exact GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat_mem h h0
  have h3 : phi br e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) * Formalism.REAL.Jm ε =
      Formalism.REAL.Jm ε * phi br e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) := by
    ext i j
    obtain ⟨a, rfl⟩ := e.surjective i
    obtain ⟨b, rfl⟩ := e.surjective j
    rw [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, h a, h b]
    by_cases hab : sameBlock a b
    · have : a.isLeft = b.isLeft := by cases a <;> cases b <;> simp_all [sameBlock]
      rw [this, mul_comm]
    · have := hx a b hab
      cases br <;> simp [phi, barMat, plainMat, this]
  refine ⟨?_, h3⟩
  generalize phi br e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) = g at h1 h3
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose]
  unfold Formalism.REAL.inUJ at h1
  rw [Matrix.mul_assoc, ← h3, ← Matrix.mul_assoc] at h1
  have h4 := congrArg (· * Formalism.REAL.Jm ε) h1
  simpa only [Matrix.mul_assoc, Formalism.REAL.Jm_mul_self, Matrix.mul_one] using h4

theorem Eab_bracket (x a b : Ix p q) : Eab x x * Eab a b - Eab a b * Eab x x =
    (((if x = a then 1 else 0) - (if x = b then 1 else 0) : ℝ) : ℂ) • Eab a b := by
  unfold Eab
  rw [Complex.ofReal_sub, sub_smul]
  congr 1
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ h]
  · split_ifs with h
    · subst h; simp
    · simp [Matrix.single_mul_single_of_ne _ _ _ _ (Ne.symm h)]

variable {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} {M : DSModel V S} {τ : D.what₂.Tau} {R : DSRep T}
  {br cj : Bool} {e : Ix p q ≃ Fin V.rank} {m : ℤ} {U : M.H τ → R.U.H}

theorem tie_zero (h : Comparison₂ R M τ br cj e m U) : U 0 = 0 := by
  rw [← norm_eq_zero, h.norm, norm_zero]

theorem tie_orth (h : Comparison₂ R M τ br cj e m U) {x y : M.H τ} (hxy : ⟪x, y⟫_ℂ = 0) : ⟪U x, U y⟫_ℂ = 0 := by
  have key : ∀ z : ℂ, (z * ⟪U x, U y⟫_ℂ).re = 0 := by
    intro z
    have h1 := norm_add_sq (𝕜 := ℂ) (U x) (U (cjc cj z • y))
    have h2 := norm_add_sq (𝕜 := ℂ) x (cjc cj z • y)
    rw [← h.add, h.norm, h.norm, h.norm, h2, h.smul, cjc_cjc, inner_smul_right, inner_smul_right, hxy] at h1
    simp only [mul_zero, map_zero, RCLike.re_to_complex] at h1
    linarith
  have k1 := key 1
  have k2 := key Complex.I
  apply Complex.ext
  · simpa using k1
  · simpa using k2

theorem wt_iff (h : Comparison₂ R M τ br cj e m U) {c : ℚ} (hm : (m : ℚ) = 2 * c) {μ : Fin V.rank → ℝ} {ν : Ix p q → ℝ}
    (hν : ∀ a, μ (e a) = sg br cj * (ν a + c)) {y : M.H τ} {w : R.HK.V} (hy : U y = R.ι w) :
    IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) μ y ↔ ∀ a, R.HK.act (Eab a a) w = ((ν a : ℝ) : ℂ) • w := by
  have hm' : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast congrArg (fun x : ℚ => (x : ℂ)) hm
  have hs : ∀ θ : Ix p q → ℝ, Complex.exp ((∑ a, (θ a : ℂ)) * Complex.I / 2) ^ (-m) *
      cjc cj (Complex.exp (((∑ j, μ j * (sb br * θ (e.symm j)) : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (((∑ a, ν a * θ a : ℝ) : ℂ) * Complex.I) := by
    intro θ
    rw [cjc_exp, ← Complex.exp_int_mul, ← Complex.exp_add, ← e.sum_comp]
    congr 1
    have : sb cj * ∑ a, μ (e a) * (sb br * θ (e.symm (e a))) = ∑ a, ν a * θ a + c * ∑ a, θ a := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hν, sg_eq, Equiv.symm_apply_apply]
      have h1 := sb_mul_self br
      have h2 := sb_mul_self cj
      calc _ = (sb br * sb br) * (sb cj * sb cj) * ((ν a + c) * θ a) := by ring
        _ = _ := by rw [h1, h2]; ring
    rw [this]
    push_cast
    rw [hm']
    ring
  rw [← torus_iff]
  constructor
  · intro hw θ
    rw [← hy, h.grp, phi_torus, hw _ (diag_mem_Kset _ _), h.smul, smul_smul, sq_expt_torX, hs]
  · intro hw θ _
    have h1 := hw fun a => sb br * θ (e a)
    have h2 := hs fun a => sb br * θ (e a)
    rw [← hy, h.grp, phi_torus, sq_expt_torX, ← h2, mul_smul, ← h.smul] at h1
    have h3 := h.bij.1 (smul_right_injective _ (zpow_ne_zero _ (Complex.exp_ne_zero _)) h1)
    simpa only [Equiv.apply_symm_apply, ← mul_assoc (sb br), sb_mul_self, one_mul] using h3

theorem orth_act (h : Comparison₂ R M τ br cj e m U) (he : SignCompat (M.ε τ) e) {F : Submodule ℂ (M.H τ)}
    (hF : IsKStableOn (M.ε τ) (M.σ τ) F) {x y : M.H τ} (hx : x ∈ F) (hy : ∀ z ∈ F, ⟪y, z⟫_ℂ = 0) {v : R.HK.V}
    (hv : U x = R.ι v) {Z : Mat p q} (hZ : IsKC Z) : ⟪U y, R.ι (R.HK.act Z v)⟫_ℂ = 0 := by
  have key : ∀ X ∈ upq p q, IsKC X → ⟪U y, R.ι (R.HK.act X v)⟫_ℂ = 0 := by
    intro X hX hXK
    have h3 := ((innerSL ℂ (U y)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) (R.der X hX v)
    have h4 : (((innerSL ℂ (U y)).restrictScalars ℝ) ∘ fun t : ℝ => R.U.π (T.expt (t • X)) (R.ι v)) = fun _ => 0 := by
      funext t
      change ⟪U y, R.U.π (T.expt (t • X)) (R.ι v)⟫_ℂ = 0
      rw [← hv, h.grp, inner_smul_right,
        tie_orth h (hy _ (hF _ (phi_mem_Kset he br (expt_mem T hX hXK t)) _ hx)), mul_zero]
    rw [h4] at h3
    exact h3.unique (hasDerivAt_const _ _)
  obtain ⟨X, Y, hX, hXK, hY, hYK, rfl⟩ := exists_decomp hZ
  rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, inner_add_right,
    inner_smul_right, key X hX hXK, key Y hY hYK, mul_zero, add_zero]

theorem mem_hwSub {lam : Ix p q → ℚ} {c : ℚ} (hp : IsParam lam) (ho : IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e)
    (hm : (m : ℚ) = 2 * c) (h : Comparison₂ R M τ br cj e m U) {x : M.H τ} {v : R.HK.V} (hv : U x = R.ι v)
    (hx : x ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ))
    (hw : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) x) :
    v ∈ hwSub R.HK.act (blattner lam) := by
  have hσ := (M.ds τ).2.2.1
  have h1 := (wt_iff h hm (ν := fun a => (blattner lam a : ℝ)) (fun a => by rw [ho.2.2 a]; push_cast; rfl) hv).1 hw
  simp only [hwSub, wtSub, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
  refine ⟨fun a => by simpa using h1 a, fun a b hab => ?_⟩
  obtain ⟨y, hy⟩ := h.bij.2 (R.ι (R.HK.act (Eab a b) v))
  have h2 : IsWtOn (Formalism.REAL.Kset (M.ε τ)) (M.σ τ)
      (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) + sg br cj • Formalism.REAL.root (e a) (e b)) y := by
    refine (wt_iff h hm (ν := fun x => (blattner lam x : ℝ) +
      ((if x = a then 1 else 0) - (if x = b then 1 else 0))) (fun x => ?_) hy).2 fun x => ?_
    · rw [Pi.add_apply, ho.2.2 x]
      simp only [Formalism.REAL.root, Pi.smul_apply, Pi.sub_apply, Pi.single_apply, EmbeddingLike.apply_eq_iff_eq,
        smul_eq_mul]
      push_cast
      ring
    · have := congrArg (fun f : Module.End ℂ R.HK.V => f v) (R.HK.lie (Eab x x) (Eab a b))
      simp only [Eab_bracket, map_smul, LinearMap.smul_apply, LinearMap.sub_apply, Module.End.mul_apply, h1] at this
      rw [Complex.ofReal_add, add_smul, this]
      abel
  have hlt : ((lam b + c : ℚ) : ℝ) < ((lam a + c : ℚ) : ℝ) := by
    have := hp.2.1 a b hab
    exact_mod_cast (by linarith : lam b + c < lam a + c)
  have hanti : StrictAnti (M.lam τ) := (M.enum τ).1
  have h3 : ¬ CDom (M.ε τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ) + sg br cj • Formalism.REAL.root (e a) (e b))
      (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) := by
    have ha := ho.2.1 a
    have hb := ho.2.1 b
    by_cases hs : br = cj
    · have s1 : sg br cj = 1 := if_pos hs
      rw [s1] at ha hb ⊢
      rw [one_smul]
      exact GlobalTheory.HolDict.BorelK.not_cdom _ (hanti.lt_iff_gt.1 (by linarith))
    · have s1 : sg br cj = -1 := if_neg hs
      rw [s1] at ha hb ⊢
      rw [show (-1 : ℝ) • Formalism.REAL.root (e a) (e b) = Formalism.REAL.root (e b) (e a) by simp [Formalism.REAL.root]]
      exact GlobalTheory.HolDict.BorelK.not_cdom _ (hanti.lt_iff_gt.1 (by linarith))
  have hK : IsKC (Eab a b) := by
    intro x y hxy
    refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
    rintro ⟨rfl, rfl⟩
    cases a <;> cases b <;> simp_all [posC, sameBlock]
  have h4 := orth_act h ho.1 GlobalTheory.HolDict.BorelK.stable_sSup hx
    (GlobalTheory.HolDict.BorelK.orth_of_not_cdom hσ h2 h3) hv hK
  rw [hy, inner_self_eq_zero] at h4
  exact R.ι_inj (by rw [h4, map_zero])

theorem highestUnit_iff : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → Module.finrank ℂ ↥(hwSub R.HK.act (blattner lam)) = 1 → ∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v) := by
  intro D V S M τ p q T R lam c br cj e m U hp ho hm h h1 x v hv
  have hn : ‖R.ι v‖ = ‖x‖ := by rw [← hv, h.norm]
  constructor
  · rintro ⟨a, b, d⟩
    refine ⟨⟨?_, mem_hwSub hp ho hm h hv b d⟩, hn.trans a⟩
    rintro rfl
    simp [a] at hn
  · rintro ⟨⟨-, a⟩, b⟩
    obtain ⟨F, hF⟩ := (M.ds τ).2.2.2.2.2.1
    obtain ⟨w, hwF, hw0, hw⟩ := hF.2.2.2.1
    have hwl : w ∈ lowKSub (M.ε τ) (M.lam τ) (M.σ τ) :=
      (le_sSup (s := {S | IsKTypeOf (M.ε τ) (M.σ τ) (Formalism.QuantumDeterminants.lowK (M.ε τ) (M.lam τ)) S}) hF) hwF
    obtain ⟨u, hu⟩ := (h.kfin w).1 ⟨F, hF.1, hwF, hF.2.1⟩
    have hu1 := mem_hwSub hp ho hm h hu.symm hwl hw
    have hu0 : (⟨u, hu1⟩ : hwSub R.HK.act (blattner lam)) ≠ 0 := by
      intro h0
      have : u = 0 := congrArg Subtype.val h0
      apply hw0
      rw [← norm_eq_zero, ← h.norm, ← hu, this, map_zero, norm_zero]
    obtain ⟨z, hz⟩ := (finrank_eq_one_iff_of_nonzero' _ hu0).1 h1 ⟨v, a⟩
    have hz' : z • u = v := congrArg Subtype.val hz
    have hx : x = cjc cj z • w := h.bij.1 (by rw [hv, h.smul, cjc_cjc, ← hu, ← map_smul, hz'])
    refine ⟨hn.symm.trans b, hx ▸ Submodule.smul_mem _ _ hwl, fun θ hθ => ?_⟩
    rw [hx, map_smul, hw θ hθ, smul_comm]

end GlobalTheory.ArchRec.HighTie

end
