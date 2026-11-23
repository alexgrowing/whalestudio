import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SchwartzBruhatMixedFamilies
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RealSizeNonneg
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
open scoped ComplexConjugate Matrix NNReal ENNReal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.Cusp GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalVolumeLift (FinPl RealMat Lat IsFockVec IsSphOff HidaSetting volQ)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalZero (ip delta swSec sZero IsKFinVec ThetaClause SectionClause CoefClause)
open GlobalTheory.Mem.Th (CptF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Core.Rk.IP GlobalTheory.Core.Rk.SWLaw
open GlobalTheory.Core.Rk.SW
open scoped ContDiff

namespace GlobalTheory.SchwartzDeriv

section General

variable {X : Type} [AddCommGroup X] [TopologicalSpace X] [IsTopologicalAddGroup X] [T2Space X]

theorem addHom_eq_zero (F : Type) [DivisionRing F] [CharZero F] [Module F X] (h : ℝ →+ X) (hc : Continuous h) {b : ℝ}
    (hb : b ≠ 0) (h0 : h b = 0) (t : ℝ) : h t = 0 := by

  have hq : ∀ q : ℚ, h ((q : ℝ) * b) = 0 := by
    intro q
    have hn : (q.den : F) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
    have hnum : (q.den : ℝ) * ((q : ℝ) * b) = (q.num : ℝ) * b := by
      rw [← mul_assoc]
      congr 1
      have : ((q.den : ℚ) * q : ℚ) = q.num := by rw [mul_comm]; exact Rat.mul_den_eq_num q
      exact_mod_cast this
    have h1 : q.den • h ((q : ℝ) * b) = 0 := by
      rw [← map_nsmul, nsmul_eq_mul, hnum, ← zsmul_eq_mul, map_zsmul, h0, smul_zero]
    have h2 : h ((q : ℝ) * b) = (q.den : F)⁻¹ • ((q.den : F) • h ((q : ℝ) * b)) := by
      rw [smul_smul, inv_mul_cancel₀ hn, one_smul]
    rw [h2, Nat.cast_smul_eq_nsmul, h1, smul_zero]
  have hsurj : Function.Surjective fun y : ℝ => y * b := fun y => ⟨y / b, div_mul_cancel₀ y hb⟩
  have hdense : DenseRange fun q : ℚ => (q : ℝ) * b :=
    hsurj.denseRange.comp Rat.denseRange_cast (continuous_mul_const b)
  exact hdense.induction_on t (isClosed_eq hc continuous_const) hq

theorem hasDerivAt_line {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (G : SchwartzMap E ℂ) (c s : E) :
    HasDerivAt (fun t : ℝ => G (s + t • c)) ((LineDeriv.lineDerivOp c G : SchwartzMap E ℂ) s) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => s + t • c) c 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const c).const_add s
  have h2 : HasFDerivAt (G : E → ℂ) (fderiv ℝ (G : E → ℂ) (s + (0 : ℝ) • c)) (s + (0 : ℝ) • c) :=
    G.differentiableAt.hasFDerivAt
  have h3 := h2.comp_hasDerivAt (0 : ℝ) h1
  simp only [zero_smul, add_zero] at h3
  rw [SchwartzMap.lineDerivOp_apply_eq_fderiv]
  exact h3

theorem exists_schwartz_deriv (F : Type) [DivisionRing F] [CharZero F] [Module F X] (P : X → Prop)
    (hP : ∀ a b, P a → P b → P (a + b)) (φ : X → ℂ)
    (hφ : ∀ (k : ℕ) (L : (Fin k → ℝ) →+ X), (Continuous L ∧ ∀ t, P (L t)) → Function.Injective L →
      ∀ x, ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ t, g t = φ (x + L t))
    (M : ℝ →+ X) (hM : Continuous M) (hMP : ∀ t, P (M t)) {k : ℕ} (L : (Fin k → ℝ) →+ X)
    (hL : Continuous L ∧ ∀ t, P (L t)) (hi : Function.Injective L) (x : X) :
    ∃ g : SchwartzMap (Fin k → ℝ) ℂ, ∀ s, HasDerivAt (fun t : ℝ => φ (x + L s + M t)) (g s) 0 := by
  obtain ⟨hLc, hLP⟩ := hL

  let A : (Fin (k + 1) → ℝ) →+ (Fin k → ℝ) :=
    (LinearMap.funLeft ℝ ℝ (Fin.castSucc : Fin k → Fin (k + 1))).toAddMonoidHom
  let B : (Fin (k + 1) → ℝ) →+ ℝ := Pi.evalAddMonoidHom (fun _ => ℝ) (Fin.last k)
  let L' : (Fin (k + 1) → ℝ) →+ X := L.comp A + M.comp B
  have hA : Continuous A := continuous_pi fun i => continuous_apply _
  have hB : Continuous B := continuous_apply _
  have hL'c : Continuous L' := (hLc.comp hA).add (hM.comp hB)
  have hL'P : ∀ u, P (L' u) := fun u => hP _ _ (hLP _) (hMP _)
  have hL'apply : ∀ u, L' u = L (fun i => u (Fin.castSucc i)) + M (u (Fin.last k)) := fun u => rfl
  by_cases hinj : Function.Injective L'
  ·
    obtain ⟨H, hH⟩ := hφ (k + 1) L' ⟨hL'c, hL'P⟩ hinj x
    let e : Fin (k + 1) → ℝ := Pi.single (Fin.last k) 1
    let j : (Fin k → ℝ) →L[ℝ] (Fin (k + 1) → ℝ) :=
      ContinuousLinearMap.pi (Fin.lastCases (motive := fun _ => (Fin k → ℝ) →L[ℝ] ℝ) 0
        fun i => ContinuousLinearMap.proj i)
    have hj_cs : ∀ s i, j s (Fin.castSucc i) = s i := by intro s i; simp [j]
    have hj_last : ∀ s, j s (Fin.last k) = 0 := by intro s; simp [j]
    have hup : ∃ (n : ℕ) (C : ℝ), ∀ s, ‖s‖ ≤ C * (1 + ‖j s‖) ^ n := by
      refine ⟨1, 1, fun s => ?_⟩
      rw [one_mul, pow_one]
      refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
      calc ‖s i‖ = ‖j s (Fin.castSucc i)‖ := by rw [hj_cs]
        _ ≤ ‖j s‖ := norm_le_pi_norm _ _
        _ ≤ 1 + ‖j s‖ := by linarith
    refine ⟨SchwartzMap.compCLM ℝ j.hasTemperateGrowth hup (LineDeriv.lineDerivOp e H), fun s => ?_⟩
    have hd := hasDerivAt_line H e (j s)
    have heq : (fun t : ℝ => H (j s + t • e)) = fun t => φ (x + L s + M t) := by
      funext t
      have e1 : (fun i => (j s + t • e) (Fin.castSucc i)) = s := by
        funext i
        simp [e, hj_cs, Fin.castSucc_ne_last]
      have e2 : (j s + t • e) (Fin.last k) = t := by simp [e, hj_last]
      rw [hH, hL'apply, e1, e2, add_assoc]
    rw [heq] at hd
    exact hd
  ·
    obtain ⟨u, hu, hu0⟩ : ∃ u, L' u = 0 ∧ u ≠ 0 := by
      rw [injective_iff_map_eq_zero] at hinj
      push Not at hinj
      exact hinj
    rw [hL'apply] at hu
    have ht0 : u (Fin.last k) ≠ 0 := by
      intro h
      rw [h, map_zero, add_zero] at hu
      have hs : (fun i => u (Fin.castSucc i)) = 0 := hi (by rw [hu, map_zero])
      apply hu0
      funext i
      refine Fin.lastCases ?_ (fun i => ?_) i
      · exact h
      · exact congrFun hs i
    let v : Fin k → ℝ := -((u (Fin.last k))⁻¹ • fun i => u (Fin.castSucc i))
    let Lv : ℝ →+ (Fin k → ℝ) := AddMonoidHom.mk' (fun t => t • v) fun a b => add_smul a b v
    have hMv : ∀ t, M t = L (t • v) := by
      intro t
      have h1 := addHom_eq_zero F (M - L.comp Lv)
        (hM.sub (hLc.comp (continuous_id.smul continuous_const))) ht0 ?_ t
      · simpa [sub_eq_zero, Lv] using h1
      · simp only [AddMonoidHom.sub_apply, AddMonoidHom.comp_apply, AddMonoidHom.mk'_apply, Lv, v, smul_neg,
          smul_smul, mul_inv_cancel₀ ht0, one_smul, map_neg, sub_neg_eq_add]
        rw [add_comm]
        exact hu
    obtain ⟨G, hG⟩ := hφ k L ⟨hLc, hLP⟩ hi x
    refine ⟨LineDeriv.lineDerivOp v G, fun s => ?_⟩
    have hd := hasDerivAt_line G v s
    have heq : (fun t : ℝ => G (s + t • v)) = fun t => φ (x + L s + M t) := by
      funext t
      rw [hG, hMv, map_add, add_assoc]
    rw [heq] at hd
    exact hd

end General

open GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies

variable {D : D7} {m n : ℕ}

theorem isSchwartzBruhat_add {φ φ' : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (h' : IsSchwartzBruhat φ') :
    IsSchwartzBruhat (φ + φ') where
  level := by
    obtain ⟨U, hU, hφU⟩ := h.level
    obtain ⟨U', hU', hφU'⟩ := h'.level
    refine ⟨U ⊓ U', by simpa [AddSubgroup.coe_inf] using hU.inter hU', fun u hu hu0 x => ?_⟩
    have hu' := AddSubgroup.mem_inf.mp hu
    simp [hφU u hu'.1 hu0 x, hφU' u hu'.2 hu0 x]
  supp := by
    obtain ⟨K, hK, hφK⟩ := h.supp
    obtain ⟨K', hK', hφK'⟩ := h'.supp
    refine ⟨K ∪ K', hK.union hK', fun x hx => ?_⟩
    by_cases h1 : φ x = 0
    · have h2 : φ' x ≠ 0 := by simpa [h1] using hx
      exact Or.inr (hφK' x h2)
    · exact Or.inl (hφK x h1)
  schwartz := by
    intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x
    obtain ⟨g', hg'⟩ := h'.schwartz k L hL hi x
    exact ⟨g + g', fun t => by simp [hg, hg']⟩

theorem isSchwartzBruhat_linear_mul {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (ℓ : Mx D m n →+ ℂ) (hc : Continuous ℓ)
    (h0 : ∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) : IsSchwartzBruhat fun x => ℓ x * φ x where
  level := by
    obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    show ℓ (x + u) * φ (x + u) = ℓ x * φ x
    rw [map_add, h0 u hu0, add_zero, hφU u hu hu0 x]
  supp := by
    obtain ⟨K, hK, hφK⟩ := h.supp
    exact ⟨K, hK, fun x hx => hφK x (right_ne_zero_of_mul hx)⟩
  schwartz := by
    intro k L hL hi x
    obtain ⟨g, hg⟩ := h.schwartz k L hL hi x

    let A : (Fin k → ℝ) →L[ℝ] ℂ := (ℓ.comp L).toRealLinearMap (hc.comp hL.1)
    have ht : (fun t => ℓ x + A t).HasTemperateGrowth := by fun_prop
    refine ⟨SchwartzMap.smulLeftCLM ℂ (fun t => ℓ x + A t) g, fun t => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply ht, hg]
    simp [A, smul_eq_mul]

theorem exists_isSchwartzBruhat_deriv {φ : Mx D m n → ℂ} (h : IsSchwartzBruhat φ) (M : ℝ →+ Mx D m n) (hM : Continuous M)
    (hM0 : ∀ t, (M t).map (finPart D) = 0) :
    ∃ φ', IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0 := by
  have : T2Space (Mx D m n) := (lattice_Mx D m n).2.2.2.1
  have hP : ∀ a b : Mx D m n, a.map (finPart D) = 0 → b.map (finPart D) = 0 → (a + b).map (finPart D) = 0 := by
    intro a b ha hb
    rw [Matrix.map_add _ (map_add _), ha, hb, add_zero]

  have hdiff : ∀ y, HasDerivAt (fun t : ℝ => φ (y + M t)) (deriv (fun t : ℝ => φ (y + M t)) 0) 0 := by
    intro y
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 (k := 0) 0 ⟨continuous_const, fun t => by simp⟩ (fun a b _ => Subsingleton.elim a b) y
    have hg0 := hg 0
    simp only [AddMonoidHom.zero_apply, add_zero] at hg0
    exact hg0.differentiableAt.hasDerivAt
  refine ⟨fun x => deriv (fun t : ℝ => φ (x + M t)) 0, ⟨?_, ?_, ?_⟩, hdiff⟩
  · obtain ⟨U, hU, hφU⟩ := h.level
    refine ⟨U, hU, fun u hu hu0 x => ?_⟩
    simp only [add_right_comm x u, hφU u hu hu0]
  · obtain ⟨K, hK, hφK⟩ := h.supp
    refine ⟨K, hK, fun x hx => ?_⟩
    by_contra hxK
    apply hx
    have hz : (fun t : ℝ => φ (x + M t)) = fun _ => 0 := by
      funext t
      by_contra ht
      apply hxK
      have := hφK _ ht
      rwa [Matrix.map_add _ (map_add _), hM0, add_zero] at this
    simp only [hz, deriv_const]
  · intro k L hL hi x
    obtain ⟨g, hg⟩ := exists_schwartz_deriv D.host.F (fun u : Mx D m n => u.map (finPart D) = 0) hP φ h.schwartz
      M hM hM0 L hL hi x
    exact ⟨g, fun s => (hg s).deriv.symm⟩

theorem isSchwartzBruhat_closed : ∀ (D : D7) (m n : ℕ) (φ : Mx D m n → ℂ), GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ → (∀ M : ℝ →+ Mx D m n, Continuous M → (∀ t, (M t).map (finPart D) = 0) → ∃ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' ∧ ∀ x, HasDerivAt (fun t : ℝ => φ (x + M t)) (φ' x) 0) ∧ (∀ ℓ : Mx D m n →+ ℂ, Continuous ℓ → (∀ u : Mx D m n, u.map (infPart D) = 0 → ℓ u = 0) → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat fun x => ℓ x * φ x) ∧ ∀ φ', GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat φ' → GlobalTheory.IndefiniteRowSideFullHecke.SchwartzBruhatMixedFamilies.IsSchwartzBruhat (φ + φ') := fun _ _ _ _ hφ =>
  ⟨fun M hM hM0 => exists_isSchwartzBruhat_deriv hφ M hM hM0, fun ℓ hc h0 => isSchwartzBruhat_linear_mul hφ ℓ hc h0,
    fun _ h' => isSchwartzBruhat_add hφ h'⟩

end GlobalTheory.SchwartzDeriv
