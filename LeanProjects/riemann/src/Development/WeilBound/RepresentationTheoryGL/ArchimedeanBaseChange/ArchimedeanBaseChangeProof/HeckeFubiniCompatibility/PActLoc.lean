import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.CompatFub
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.PSplit
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.MultHasCompactSupport

noncomputable section

open NumberField Matrix MeasureTheory Topology
open GlobalTheory.CuspRep PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC.Bridge (along atW)
open scoped ContDiff Classical

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace PositivityTheory.Rg.BcB.CG

section Gel

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem isOpen_GLs : IsOpen (GLs n) :=
  isOpen_ne_fun (Continuous.matrix_det continuous_id) continuous_const

theorem contDiffOn_Rd (X : Mat n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) : ContDiffOn ℝ ∞ (Rd X f) (GLs n) := by
  have hm : ContDiff ℝ ∞ fun g : Mat n => g * X :=
    (LinearMap.toContinuousLinearMap (LinearMap.mulRight ℝ X : Mat n →ₗ[ℝ] Mat n)).contDiff
  exact (hf.fderiv_of_isOpen isOpen_GLs (by simp)).clm_apply hm.contDiffOn

theorem contDiffOn_Eu (s : Bool) (a b : Fin n) {f : Mat n → V} (hf : ContDiffOn ℝ ∞ f (GLs n)) :
    ContDiffOn ℝ ∞ (Eu s a b f) (GLs n) :=
  ((contDiffOn_Rd _ hf).add ((contDiffOn_Rd _ hf).const_smul _)).const_smul _

theorem contDiffOn_Epow (s : Bool) (m : ℕ) : ∀ (a b : Fin n) {f : Mat n → V}, ContDiffOn ℝ ∞ f (GLs n) →
    ContDiffOn ℝ ∞ (Epow s m a b f) (GLs n) := by
  induction m with
  | zero =>
    intro a b f hf
    show ContDiffOn ℝ ∞ (if a = b then f else 0) (GLs n)
    by_cases h : a = b
    · rw [if_pos h]; exact hf
    · rw [if_neg h]; exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : Mat n => (0 : V)) (GLs n))
  | succ m ih =>
    intro a b f hf
    have e : Epow s (m + 1) a b f = fun x => ∑ c, Eu s a c (Epow s m c b f) x := by
      funext x; simp only [Epow, Finset.sum_apply]
    rw [e]
    exact ContDiffOn.sum fun c _ => contDiffOn_Eu s a c (ih c b hf)

theorem Rd_congr (X : Mat n) {f₁ f₂ : Mat n → V} (h : Set.EqOn f₁ f₂ (GLs n)) : Set.EqOn (Rd X f₁) (Rd X f₂) (GLs n) :=
  fun g hg => by
    have e : f₁ =ᶠ[𝓝 g] f₂ := Filter.eventually_of_mem (isOpen_GLs.mem_nhds hg) h
    simp only [Rd, e.fderiv_eq]

theorem Eu_congr (s : Bool) (a b : Fin n) {f₁ f₂ : Mat n → V} (h : Set.EqOn f₁ f₂ (GLs n)) :
    Set.EqOn (Eu s a b f₁) (Eu s a b f₂) (GLs n) :=
  fun g hg => by
    simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_congr _ h hg]

theorem Rd_sum {ι : Type} [Fintype ι] (X : Mat n) (φ : ι → Mat n → ℂ) (b : ι → V) {g : Mat n}
    (hd : ∀ j, DifferentiableAt ℝ (φ j) g) :
    Rd X (fun x => ∑ j, φ j x • b j) g = ∑ j, Rd X (φ j) g • b j := by
  have h : HasFDerivAt (fun x => ∑ j, φ j x • b j) (∑ j, (fderiv ℝ (φ j) g).smulRight (b j)) g :=
    HasFDerivAt.fun_sum fun j _ => (hd j).hasFDerivAt.smul_const (b j)
  simp only [Rd, h.fderiv, ContinuousLinearMap.sum_apply, Finset.sum_apply, ContinuousLinearMap.smulRight_apply]

theorem Eu_sum {ι : Type} [Fintype ι] (s : Bool) (a c : Fin n) (φ : ι → Mat n → ℂ) (b : ι → V) {g : Mat n}
    (hd : ∀ j, DifferentiableAt ℝ (φ j) g) :
    Eu s a c (fun x => ∑ j, φ j x • b j) g = ∑ j, Eu s a c (φ j) g • b j := by
  simp only [Eu, Pi.smul_apply, Pi.add_apply, Rd_sum _ φ b hd]
  rw [Finset.smul_sum, ← Finset.sum_add_distrib, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [smul_eq_mul, smul_add, add_smul, mul_smul]

theorem Epow_sum {ι : Type} [Fintype ι] (s : Bool) (φ : ι → Mat n → ℂ) (b : ι → V)
    (hφ : ∀ j, ContDiffOn ℝ ∞ (φ j) (GLs n)) (m : ℕ) : ∀ a c : Fin n,
    Set.EqOn (Epow s m a c (fun x => ∑ j, φ j x • b j)) (fun x => ∑ j, Epow s m a c (φ j) x • b j) (GLs n) := by
  induction m with
  | zero =>
    intro a c x _
    by_cases h : a = c
    · simp [Epow, h]
    · simp [Epow, h]
  | succ m ih =>
    intro a c x hx
    simp only [Epow, Finset.sum_apply]
    have e : ∀ d, Eu s a d (Epow s m d c fun x => ∑ j, φ j x • b j) x = ∑ j, Eu s a d (Epow s m d c (φ j)) x • b j := by
      intro d
      rw [Eu_congr s a d (ih d c) hx]
      exact Eu_sum s a d _ b fun j =>
        ((contDiffOn_Epow s m d c (hφ j)).contDiffAt (isOpen_GLs.mem_nhds hx)).differentiableAt (by simp)
    simp only [e, Finset.sum_smul]
    exact Finset.sum_comm

theorem gel_sum {ι : Type} [Fintype ι] (s : Bool) (m : ℕ) (φ : ι → Mat n → ℂ) (b : ι → V)
    (hφ : ∀ j, ContDiffOn ℝ ∞ (φ j) (GLs n)) {g : Mat n} (hg : g ∈ GLs n) :
    gel s m (fun x => ∑ j, φ j x • b j) g = ∑ j, gel s m (φ j) g • b j := by
  simp only [gel, Finset.sum_apply, Epow_sum s φ b hφ m _ _ hg, Finset.sum_smul]
  exact Finset.sum_comm

theorem isEig_sum {ι : Type} [Fintype ι] (χ : Inf n) (φ : ι → Mat n → ℂ) (b : ι → V)
    (hφ : ∀ j, ContDiffOn ℝ ∞ (φ j) (GLs n)) (he : ∀ j, IsEig χ (φ j)) : IsEig χ (fun x => ∑ j, φ j x • b j) := by
  intro s m g hg
  rw [gel_sum s m φ b hφ hg, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [he j s m g hg, smul_eq_mul, mul_smul]

end Gel

section Chart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

abbrev infU (n : ℕ) (y : InfinitePlace E → G n) : GL (Fin n) (Cinf E) :=
  Units.map (Matrix.piRingEquiv (n := Fin n) (β := fun _ : InfinitePlace E => ℂ)).symm.toMonoidHom
    (MulEquiv.piUnits.symm y)

theorem atW_val (v : InfinitePlace E) (t : G n) : atW v t.val = toL (infU n (Pi.mulSingle v t)).val := by
  funext i j w
  show (if w = v then t.val i j else (1 : Mat n) i j) = (((Pi.mulSingle v t : InfinitePlace E → G n) w : G n) : Mat n) i j
  by_cases hw : w = v
  · subst hw; rw [if_pos rfl, Pi.mulSingle_eq_same]
  · rw [if_neg hw, Pi.mulSingle_eq_of_ne hw, Units.val_one]

theorem along_val (v : InfinitePlace E) (g : GA E n) (φ : GA E n → ℂ) (t : G n) :
    along v g φ t.val = φ (g * infP n (Pi.mulSingle v t)) := by
  show chart φ g (atW v t.val) = _
  rw [atW_val, chart_val]
  rfl

theorem infinitePart_one : infP (E := E) n 1 = 1 := by
  simp [infP]

def unitOf {x : Mat n} (hx : x ∈ GLs n) : G n :=
  ((Matrix.isUnit_iff_isUnit_det x).2 (isUnit_iff_ne_zero.2 hx)).unit

theorem unitOf_val {x : Mat n} (hx : x ∈ GLs n) : (unitOf hx).val = x :=
  IsUnit.unit_spec _

def atWL (v : InfinitePlace E) : Mat n →ₗ[ℝ] Lie E n where
  toFun x := fun i j w => if w = v then x i j else 0
  map_add' x y := by funext i j w; by_cases h : w = v <;> simp [h]
  map_smul' c x := by funext i j w; by_cases h : w = v <;> simp [h]

theorem contDiff_atW (v : InfinitePlace E) : ContDiff ℝ ∞ (atW (a := n) v) := by
  have e : atW (a := n) v = fun x => atWL v x + atW v 0 := by
    funext x i j w
    simp only [atW, atWL, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply]
    split_ifs <;> simp
  rw [e]
  exact (LinearMap.toContinuousLinearMap (atWL (n := n) v)).contDiff.add contDiff_const

theorem contDiffOn_along (v : InfinitePlace E) (g : GA E n) {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) :
    ContDiffOn ℝ ∞ (along v g φ) (GLs n) := by
  have hm : Set.MapsTo (atW (a := n) v) (GLs n) (invSet E n) := fun x hx => by
    rw [← unitOf_val hx, atW_val]
    exact val_mem_invSet _
  exact (hφ g).comp (contDiff_atW v).contDiffOn hm

theorem sm_cont_infP {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g₀ : GA E n) :
    Continuous fun y : InfinitePlace E → G n => φ (g₀ * infP n y) := by
  have e : (fun y : InfinitePlace E → G n => φ (g₀ * infP n y)) = fun y => chart φ g₀ (toL (infU n y).val) :=
    funext fun y => (chart_val φ g₀ _).symm
  rw [e]
  have hc : Continuous fun y : InfinitePlace E → G n => toL (infU (E := E) n y).val :=
    continuous_pi fun i => continuous_pi fun j => continuous_pi fun w =>
      (Units.continuous_val.matrix_elem i j).comp (continuous_apply w)
  exact (hφ g₀).continuousOn.comp_continuous hc fun y => val_mem_invSet _

theorem loc_cont {φ : GA E n → ℂ} (hφ : φ ∈ Sm E n) (g₀ : GA E n) (v : InfinitePlace E) :
    Continuous fun t : G n => φ (g₀ * infP n (Pi.mulSingle v t)) := by
  have h : Continuous fun t : G n => (Pi.mulSingle v t : InfinitePlace E → G n) := by
    refine continuous_pi fun w => ?_
    by_cases hw : w = v
    · subst hw; simp only [Pi.mulSingle_eq_same]; exact continuous_id
    · simp only [Pi.mulSingle_eq_of_ne hw]; exact continuous_const
  exact (sm_cont_infP hφ g₀).comp h

end Chart

section Loc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem loc_act (hMA : MultAlg) [MeasurableSpace (G n)] [BorelSpace (G n)] (μ : Measure (G n)) [μ.IsHaarMeasure]
    (M : KMod n) (k : Mat n → (M.V →L[ℂ] M.V)) (val : Inf n → ℂ) (T : ℝ) (hk : IsMult μ M k val T) (χ : Inf n)
    (v : InfinitePlace E) (Φ : Ix M → GA E n → ℂ) (hsm : ∀ j, Φ j ∈ Sm E n)
    (heq : ∀ (h : GA E n) (u : Matrix.unitaryGroup (Fin n) ℂ) l,
      Φ l (h * infP n (Pi.mulSingle v (Unitary.toUnits u))) = ∑ j, ent M (M.ρ u⁻¹) l j * Φ j h)
    (heig : ∀ j g, IsEig χ (along v g (Φ j))) (g₀ : GA E n) (l : Ix M) :
    ∑ j, ∫ t : G n, ent M (k t.val) l j * Φ j (g₀ * infP n (Pi.mulSingle v t)) ∂μ = val χ * Φ l g₀ := by
  set b := stdOrthonormalBasis ℂ M.V with hb
  set φ : Ix M → Mat n → ℂ := fun j => along v g₀ (Φ j) with hφdef
  have hφ : ∀ j, ContDiffOn ℝ ∞ (φ j) (GLs n) := fun j => contDiffOn_along v g₀ (hsm j)
  set F : Mat n → M.V := fun x => ∑ j, φ j x • b j with hF
  have hFs : ContDiffOn ℝ ∞ F (GLs n) := ContDiffOn.sum fun j _ => (hφ j).smul contDiffOn_const
  have hCE : F ∈ CE M := by
    refine ⟨hFs, fun g hg u => ?_⟩
    set t := unitOf hg
    set hh := g₀ * infP n (Pi.mulSingle v t)
    have e1 : g * u.1 = (t * Unitary.toUnits u).val := by rw [Units.val_mul, unitOf_val]; rfl
    have e2 : ∀ j, φ j (g * u.1) = ∑ i, ent M (M.ρ u⁻¹) j i * Φ i hh := by
      intro j
      rw [e1]
      show along v g₀ (Φ j) _ = _
      rw [along_val, Pi.mulSingle_mul, infinitePart_mul, ← mul_assoc, heq]
    have e3 : ∀ j, φ j g = Φ j hh := by
      intro j
      show along v g₀ (Φ j) g = _
      rw [← unitOf_val hg, along_val]
    simp only [hF, e2, e3, map_sum, map_smul]
    have e4 : ∀ i, M.ρ u⁻¹ (b i) = ∑ j, ent M (M.ρ u⁻¹) j i • b j := fun i => (b.sum_repr' _).symm
    simp only [e4, Finset.smul_sum, smul_smul, Finset.sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    rw [mul_comm]
  have hEig : IsEig χ F := isEig_sum χ φ b hφ fun j => heig j g₀
  have hact := (hMA n μ M k k val val T T hk hk).2.2.2 χ F hCE hEig 1 (by simp [GLs])
  have hcont : ∀ j, Continuous fun t : G n => φ j t.val := by
    intro j
    have e : (fun t : G n => φ j t.val) = fun t => Φ j (g₀ * infP n (Pi.mulSingle v t)) :=
      funext fun t => along_val v g₀ (Φ j) t
    rw [e]; exact loc_cont (hsm j) g₀ v
  have hkc := mult_continuous hk
  have hks := mult_hasCompactSupport hk
  have hFc : Continuous fun t : G n => F t.val := continuous_finsetSum _ fun j _ => (hcont j).smul continuous_const
  have hint : Integrable (fun y : G n => k y.val (F (1 * y.val))) μ := by
    simp only [one_mul]
    refine (hkc.clm_apply hFc).integrable_of_hasCompactSupport ?_
    exact hks.mono fun y hy h0 => hy (by simp [h0])
  have hin := congrArg (fun w : M.V => inner ℂ (b l) w) hact
  simp only [PositivityTheory.RgBcC.act] at hin
  rw [← integral_inner hint] at hin
  have e5 : ∀ y : G n, inner ℂ (b l) (k y.val (F (1 * y.val))) =
      ∑ j, ent M (k y.val) l j * Φ j (g₀ * infP n (Pi.mulSingle v y)) := by
    intro y
    simp only [one_mul, hF, map_sum, map_smul, inner_sum, inner_smul_right]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [mul_comm]
    simp only [ent, hb, hφdef, along_val]
  simp only [e5] at hin
  rw [integral_finsetSum _ fun j _ => ?_] at hin
  · rw [hin, inner_smul_right]
    have e6 : inner ℂ (b l) (F 1) = φ l 1 := b.orthonormal.inner_right_fintype _ l
    rw [e6]
    have e7 : φ l 1 = Φ l g₀ := by
      have := along_val v g₀ (Φ l) (1 : G n)
      simp only [Units.val_one, Pi.mulSingle_one, infinitePart_one, mul_one] at this
      exact this
    rw [e7]
  · refine ((mult_ent hk l j).1.mul (loc_cont (hsm j) g₀ v)).integrable_of_hasCompactSupport ?_
    exact (mult_ent hk l j).2.mul_right

end Loc

end PositivityTheory.Rg.BcB.CG

end
