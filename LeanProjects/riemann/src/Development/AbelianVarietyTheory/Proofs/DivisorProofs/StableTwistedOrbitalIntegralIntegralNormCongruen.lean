import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StableTwistedOrbitalProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsBallSubset
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.BCT.StTwLevel

theorem finsum_const_mul {ι : Type} (c : ℂ) (g : ι → ℂ) : ∑ᶠ i, c * g i = c * ∑ᶠ i, g i := by
  by_cases hc : c = 0
  · simp [hc]
  by_cases h : (Function.support g).Finite
  · exact (mul_finsum _ _).symm
  · have hs : Function.support (fun i => c * g i) = Function.support g := by
      ext i; simp [hc]
    rw [finsum_of_infinite_support h, mul_zero, finsum_of_infinite_support (by rwa [hs])]

theorem avg_const_mul {H : Type} [Group H] (c : ℂ) (u : H → ℂ) : avg (fun h => c * u h) = c * avg u := by
  by_cases hc : c = 0
  · simp [hc, avg]
  have hR : rStab (fun h => c * u h) = rStab u := by
    ext k
    simp only [GlobalTheory.TwOrbConj.mem_rStab, mul_right_inj' hc]
  unfold avg
  rw [hR, finsum_const_mul]
  ring

theorem twOrb_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (δ : G) (c : ℂ)
    (f : G → ℂ) : twOrb θ K δ (fun x => c * f x) = c * twOrb θ K δ f := by
  unfold twOrb
  simp_rw [avg_const_mul]
  rw [← finsum_const_mul]
  refine finsum_congr fun q => ?_
  ring

theorem clSum_const_mul {G : Type} [Group G] [TopologicalSpace G] (θ : G →* G) (K : Subgroup G) (S : Set G)
    (wt : G → ℂ) (c : ℂ) (f : G → ℂ) : clSum θ K S wt (fun x => c * f x) = c * clSum θ K S wt f := by
  unfold clSum
  rw [← finsum_const_mul]
  refine finsum_congr fun d => ?_
  split_ifs
  · rw [twOrb_const_mul]; ring
  · simp

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem stTw2_const_mul (a b : ℕ) (w : Pl E) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ)
    (φ : GLw a w × GLw b w → ℂ) : stTw2 a b w Q₁ Q₂ (fun y => c * φ y) = c * stTw2 a b w Q₁ Q₂ φ := by
  unfold stTw2
  exact clSum_const_mul _ _ _ _ _ _

def lev (n : ℕ) (w : Pl E) (k : ℕ) (y : GLw n w) : ℂ :=
  if y ∈ GlobalTheory.LFun.KGL w n ∧ nrmL n w y ∈ GlobalTheory.PrincCong.congSub w n k then 1 else 0

theorem nrm_eq {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) (y : GLw n w) : nrmL n w y = y * thL n w y := by
  unfold nrmL thL
  rw [if_neg hw, if_neg hw]

theorem thL_KGL {w : Pl E} (hw : ¬ IsSplitAt w) (n : ℕ) {g : GLw n w} (hg : g ∈ GlobalTheory.LFun.KGL w n) :
    thL n w g ∈ GlobalTheory.LFun.KGL w n := by
  have ht : thL n w = thetaGL n (cj w) := by unfold thL; rw [if_neg hw]
  rw [ht]
  obtain ⟨h, rfl⟩ := hg
  let c' : Ov E w →+* Ov E w := (cj w).restrict (Ov E w) (Ov E w) (GlobalTheory.PrincCong.cj_mem_Ov w)
  exact ⟨thetaGL n c' h, GlobalTheory.ThetaPull.map_thetaGL (Ov E w).subtype c' (cj w) (fun x => rfl) h⟩

theorem conj_mem_congSub {w : Pl E} {n k : ℕ} {h g : GLw n w} (hh : h ∈ GlobalTheory.LFun.KGL w n)
    (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) : h * g * h⁻¹ ∈ GlobalTheory.PrincCong.congSub w n k := by
  obtain ⟨h', rfl⟩ := hh
  obtain ⟨g', hg', rfl⟩ := hg
  exact ⟨h' * g' * h'⁻¹, (MonoidHom.normal_ker _).conj_mem g' hg' h', by simp only [map_mul, map_inv]⟩

end GlobalTheory.BCT.StTwLevel

namespace GlobalTheory.BCT.StTwLevel

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem congSub_le {w : Pl E} {n k : ℕ} {g : GLw n w} (hg : g ∈ GlobalTheory.PrincCong.congSub w n k) :
    g ∈ GlobalTheory.LFun.KGL w n := ((GlobalTheory.PrincCong.mem_congSub_iff w n k g).1 hg).1

theorem lev_level {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsLevel (thL n w) (GlobalTheory.LFun.KGL w n) (GlobalTheory.PrincCong.congSub w n k) :=
  ⟨GlobalTheory.PrincCong.isOpen_congSub w n k, fun _ hg => congSub_le hg, GlobalTheory.PrincCong.thL_mem_congSub w hw n k⟩

theorem lev_hecke {w : Pl E} (hw : ¬ IsSplitAt w) (n k : ℕ) :
    IsHecke (GlobalTheory.PrincCong.congSub w n k) (lev n w k) := by
  refine ⟨?_, fun x hx y => ⟨?_, ?_⟩⟩
  · have hc := GlobalTheory.LFun.SatCompare.isOpen_isCompact_KGL w n
    refine HasCompactSupport.intro' hc.2 (Subgroup.isClosed_of_isOpen _ hc.1) fun y hy => ?_
    unfold lev
    exact if_neg fun h => hy h.1
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
    · have hxy : x * y ∈ GlobalTheory.LFun.KGL w n := mul_mem hxK hy
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * thL n w x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hθx
      have e : nrmL n w (x * y) = x * nrmL n w y * ((thL n w y)⁻¹ * thL n w x * thL n w y) := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hm, Subgroup.mul_mem_cancel_left _ hx]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : x * y ∉ GlobalTheory.LFun.KGL w n := fun h => hy (by simpa using mul_mem (inv_mem hxK) h)
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩
  · have hxK := congSub_le hx
    have hθx := GlobalTheory.PrincCong.thL_mem_congSub w hw n k x hx
    unfold lev
    refine if_congr ?_ rfl rfl
    by_cases hy : y ∈ GlobalTheory.LFun.KGL w n
    · have hxy : y * x ∈ GlobalTheory.LFun.KGL w n := mul_mem hy hxK
      have hθy := thL_KGL hw n hy
      have hm : (thL n w y)⁻¹ * x * thL n w y ∈ GlobalTheory.PrincCong.congSub w n k := by
        simpa using conj_mem_congSub (inv_mem hθy) hx
      have e : nrmL n w (y * x) = nrmL n w y * ((thL n w y)⁻¹ * x * thL n w y) * thL n w x := by
        rw [nrm_eq hw, nrm_eq hw, map_mul]; group
      rw [e, Subgroup.mul_mem_cancel_right _ hθx, Subgroup.mul_mem_cancel_right _ hm]
      exact ⟨fun h => ⟨hy, h.2⟩, fun h => ⟨hxy, h.2⟩⟩
    · have hxy : y * x ∉ GlobalTheory.LFun.KGL w n := fun h => hy (by simpa using mul_mem h (inv_mem hxK))
      exact ⟨fun h => absurd h.1 hxy, fun h => absurd h.1 hy⟩

theorem lev_eq {w : Pl E} (n k : ℕ) :
    (fun y : GLw n w => if y ∈ GlobalTheory.LFun.KGL w n ∧ nrmL n w y ∈ {g : GLw n w | g ∈ GlobalTheory.LFun.KGL w n ∧ ∀ i j,
      Valued.v (g.val i j - (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))}
      then (1 : ℂ) else 0) = lev n w k := by
  funext y
  unfold lev
  exact if_congr (and_congr Iff.rfl (GlobalTheory.PrincCong.mem_congSub_iff w n k _).symm) rfl rfl

theorem stTw2_lev : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E), ¬ IsSplitAt w → ∀ (a b k : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]) (c : ℂ), Q₁.Monic → Q₂.Monic → Q₁.natDegree = a → Q₂.natDegree = b → (Q₁ * Q₂).Separable → stTw2 a b w Q₁ Q₂ (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) = c * (stTw a w Q₁ (fun y : GLw a w => if y ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0) * stTw b w Q₂ (fun y : GLw b w => if y ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then 1 else 0)) := by
  intro E _ _ _ w hw a b k Q₁ Q₂ c _ _ _ _ _
  rw [lev_eq a k, lev_eq b k]
  have e : (fun y : GLw a w × GLw b w => c * (if y.1 ∈ GlobalTheory.LFun.KGL w a ∧ nrmL a w y.1 ∈ {g : GLw a w | g ∈ GlobalTheory.LFun.KGL w a ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin a) (Fin a) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} ∧ y.2 ∈ GlobalTheory.LFun.KGL w b ∧ nrmL b w y.2 ∈ {g : GLw b w | g ∈ GlobalTheory.LFun.KGL w b ∧ ∀ i j, Valued.v (g.val i j - (1 : Matrix (Fin b) (Fin b) (w.adicCompletion E)) i j) ≤ WithZero.exp (-(k : ℤ))} then (1 : ℂ) else 0)) =
      fun y => c * GlobalTheory.BCT.tens (lev a w k) (lev b w k) y := by
    funext y
    congr 1
    have h1 := congrFun (lev_eq (w := w) a k) y.1
    have h2 := congrFun (lev_eq (w := w) b k) y.2
    rw [GlobalTheory.BCT.tens, ← h1, ← h2, ite_zero_mul_ite_zero, mul_one]
    exact if_congr and_assoc.symm rfl rfl
  rw [e, stTw2_const_mul, GlobalTheory.BCT.StTwTens.stTw2_tens E a b w Q₁ Q₂ _ _ _ _ (lev_level hw a k) (lev_level hw b k)
    (lev_hecke hw a k) (lev_hecke hw b k)]

end GlobalTheory.BCT.StTwLevel
