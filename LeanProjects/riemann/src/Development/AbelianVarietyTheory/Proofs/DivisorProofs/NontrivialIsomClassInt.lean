import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ArInt GlobalTheory.Cartier GlobalTheory.CxPts GlobalTheory.CechPic GlobalTheory.Points GlobalTheory.ChartGlue

namespace GlobalTheory

variable {k : Type} [CommRing k] {X Y : Scheme.{0}} {p : X ⟶ Sp k} {q : Y ⟶ Sp k} {σ : k →+* ℂ}

namespace CxPts

variable {y : CxPts p σ} {U W : X.Opens}

def logSq (y : CxPts p σ) (U : X.Opens) (u : Γ(X, U)ˣ) : ℝ := Real.log (‖ev p σ U u.val y‖ ^ 2)

theorem logSq_mul (h : y ∈ ptsIn p σ U) (u v : Γ(X, U)ˣ) :
    logSq y U (u * v) = logSq y U u + logSq y U v := by
  rw [logSq, Units.val_mul, ev_mul, log_normSq_mul (ev_ne_zero h u.isUnit) (ev_ne_zero h v.isUnit)]
  rfl

theorem logSq_one (h : y ∈ ptsIn p σ U) : logSq y U 1 = 0 := by
  rw [logSq, Units.val_one, ev_one h, norm_one, one_pow, Real.log_one]

theorem logSq_inv (h : y ∈ ptsIn p σ U) (u : Γ(X, U)ˣ) : logSq y U u⁻¹ = -logSq y U u := by
  rw [logSq, ev_inv h, norm_inv, inv_pow, Real.log_inv, logSq]

theorem logSq_res (e : W ≤ U) (h : y ∈ ptsIn p σ W) (u : Γ(X, U)ˣ) :
    logSq y W (res e u) = logSq y U u := congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_res e h u.val)

end CxPts

namespace HermLB

variable {L M N L' M' : HermLB p}

theorem isometric_of_local {J : Type} (W : J → X.Opens) (hW : ∀ x, ∃ j, x ∈ W j) (a : J → M.B.ι)
    (b : J → L.B.ι) (ha : ∀ j, W j ≤ M.B.U (a j)) (hb : ∀ j, W j ≤ L.B.U (b j)) (u : ∀ j, Γ(X, W j)ˣ)
    (hu : ∀ (x : X) j j', x ∈ W j → x ∈ W j' → gm (𝟙 X) x (W j) (u j) =
      gm (𝟙 X) x _ (M.B.g (a j) (a j')) * (gm (𝟙 X) x _ (L.B.g (b j) (b j')))⁻¹ * gm (𝟙 X) x (W j') (u j'))
    (hφ : ∀ (σ : k →+* ℂ) j (y : CxPts p σ), y ∈ ptsIn p σ (W j) →
      (M.φ σ).φ (a j) y = (L.φ σ).φ (b j) y + logSq y (W j) (u j)) : L.Isometric M := by
  let v (c : M.B.ι × L.B.ι) (j : J) : Γ(X, M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j)ˣ :=
    res (inf_le_inf inf_le_left (ha j)) (M.B.g c.1 (a j)) *
      (res (inf_le_inf inf_le_right (hb j)) (L.B.g c.2 (b j)))⁻¹ * res inf_le_right (u j)
  have hv (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (v c j) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    simp only [v, map_mul, map_inv, gm_res (𝟙 X) x _ hx]
  have key : ∀ {G : Type} [CommGroup G] (a b c d e : G), a * b * (c * d)⁻¹ * e = a * c⁻¹ * (b * d⁻¹ * e) := by
    intro G _ a b c d e
    simp only [mul_inv]
    ac_rfl
  have hg (c : M.B.ι × L.B.ι) : ∃ s : Γ(X, M.B.U c.1 ⊓ L.B.U c.2)ˣ, ∀ j, res inf_le_left s = v c j := by
    refine glue_unit _ _ _ (fun x hx => ?_) (v c) fun j j' x hx => ?_
    · obtain ⟨j, hj⟩ := hW x
      exact Opens.mem_iSup.2 ⟨j, hx, hj⟩
    · rw [hv c j x hx.1, hv c j' x hx.2, hu x j j' hx.1.2 hx.2.2,
        ← gm_cocycle M.isLB (𝟙 X) x hx.1.1.1 (ha j hx.1.2) (ha j' hx.2.2),
        ← gm_cocycle L.isLB (𝟙 X) x hx.1.1.2 (hb j hx.1.2) (hb j' hx.2.2), key]
  choose s hs using hg
  have hs' (c j) (x : X) (hx : x ∈ M.B.U c.1 ⊓ L.B.U c.2 ⊓ W j) : gm (𝟙 X) x _ (s c) =
      gm (𝟙 X) x _ (M.B.g c.1 (a j)) * (gm (𝟙 X) x _ (L.B.g c.2 (b j)))⁻¹ * gm (𝟙 X) x _ (u j) := by
    rw [← hv c j x hx, ← hs, gm_res (𝟙 X) x _ hx]
  refine ⟨⟨s⟩, (isGen_iff_germ _).2 fun x c c' hc hc' => ?_, fun σ a₀ b₀ y h₁ h₂ => ?_⟩
  · obtain ⟨j, hj⟩ := hW x
    refine (hs' c j x ⟨hc, hj⟩).trans (Eq.trans ?_ (congrArg₂ (· * ·)
      (gm_div' M.B L.B (𝟙 X) x c c' hc hc') (hs' c' j x ⟨hc', hj⟩)).symm)
    rw [← gm_cocycle M.isLB (𝟙 X) x hc.1 hc'.1 (ha j hj),
      ← gm_cocycle L.isLB (𝟙 X) x hc.2 hc'.2 (hb j hj), key]
  · obtain ⟨j, hj⟩ := hW (under y)
    have hj' : y ∈ ptsIn p σ (W j) := mem_ptsIn.2 hj
    have hy : y ∈ ptsIn p σ (M.B.U a₀ ⊓ L.B.U b₀ ⊓ W j) := by simp [*]
    have e : logSq y _ (s (a₀, b₀)) = logSq y _ (M.B.g a₀ (a j)) + -logSq y _ (L.B.g b₀ (b j)) +
        logSq y _ (u j) := by
      rw [← logSq_res inf_le_left hy, hs (a₀, b₀) j]
      simp only [v, logSq_mul hy, logSq_inv hy, logSq_res _ hy]
    have e₁ : _ = _ - logSq y _ (M.B.g a₀ (a j)) := (M.φ σ).trans a₀ (a j) y h₁ (ptsIn_mono (ha j) hj')
    have e₂ : _ = _ - logSq y _ (L.B.g b₀ (b j)) := (L.φ σ).trans b₀ (b j) y h₂ (ptsIn_mono (hb j) hj')
    have e₃ := hφ σ j y hj'
    change _ = _ + logSq y _ (s (a₀, b₀))
    linarith

theorem isometric_of_chart (a : L.B.ι → M.B.ι) (ha : ∀ j, L.B.U j ≤ M.B.U (a j))
    (hg : ∀ (x : X) j j', x ∈ L.B.U j → x ∈ L.B.U j' →
      gm (𝟙 X) x _ (L.B.g j j') = gm (𝟙 X) x _ (M.B.g (a j) (a j')))
    (hφ : ∀ (σ : k →+* ℂ) j (y : CxPts p σ), y ∈ ptsIn p σ (L.B.U j) →
      (M.φ σ).φ (a j) y = (L.φ σ).φ j y) : L.Isometric M :=
  isometric_of_local L.B.U (exists_chart L.isLB) a id ha (fun _ => le_rfl) (fun _ => 1)
    (fun x j j' h h' => by rw [map_one, map_one, ← hg x j j' h h', mul_one]; exact (mul_inv_cancel _).symm)
    fun σ j y h => by rw [logSq_one h, add_zero]; exact hφ σ j y h

theorem Isometric.exists_units (h : L.Isometric M) :
    ∃ w : ∀ a b, Γ(X, M.B.U a ⊓ L.B.U b)ˣ,
      (∀ (Z : Scheme.{0}) (f : Z ⟶ X) (z : Z) a a' b b', f z ∈ M.B.U a → f z ∈ M.B.U a' → f z ∈ L.B.U b →
        f z ∈ L.B.U b' → gm f z _ (w a b) =
          gm f z _ (M.B.g a a') * (gm f z _ (L.B.g b b'))⁻¹ * gm f z _ (w a' b')) ∧
      ∀ (σ : k →+* ℂ) a b (y : CxPts p σ), y ∈ ptsIn p σ (M.B.U a) → y ∈ ptsIn p σ (L.B.U b) →
        (M.φ σ).φ a y = (L.φ σ).φ b y + logSq y _ (w a b) :=
  have ⟨w, hw, h⟩ := h
  ⟨fun a b => w.s (a, b), fun _ f z a a' b b' => gm_isGen hw f z a a' b b', h⟩

theorem Isometric.symm (h : L.Isometric M) : M.Isometric L := by
  obtain ⟨w, hw, h⟩ := h.exists_units
  refine isometric_of_local (fun c : M.B.ι × L.B.ι => M.B.U c.1 ⊓ L.B.U c.2) (fun x => ?_) Prod.snd Prod.fst
    (fun _ => inf_le_right) (fun _ => inf_le_left) (fun c => (w c.1 c.2)⁻¹) (fun x c c' hc hc' => ?_)
    fun σ c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.isLB x
    obtain ⟨b, hb⟩ := exists_chart L.isLB x
    exact ⟨(a, b), ha, hb⟩
  · rw [map_inv, map_inv, hw _ (𝟙 X) x _ c'.1 _ c'.2 hc.1 hc'.1 hc.2 hc'.2,
      mul_inv, mul_inv, inv_inv]
    exact congrArg (· * _) (mul_comm _ _)
  · rw [logSq_inv hy, h σ c.1 c.2 y (mem_ptsIn_inf.1 hy).1 (mem_ptsIn_inf.1 hy).2]
    ring

theorem Isometric.trans (h : L.Isometric M) (h' : M.Isometric N) : L.Isometric N := by
  obtain ⟨w, hw, h⟩ := h.exists_units
  obtain ⟨w', hw', h'⟩ := h'.exists_units
  refine isometric_of_local
    (fun c : N.B.ι × M.B.ι × L.B.ι => N.B.U c.1 ⊓ M.B.U c.2.1 ⊓ (M.B.U c.2.1 ⊓ L.B.U c.2.2))
    (fun x => ?_) (·.1) (·.2.2) (fun _ => inf_le_left.trans inf_le_left)
    (fun _ => inf_le_right.trans inf_le_right)
    (fun c => res inf_le_left (w' c.1 c.2.1) * res inf_le_right (w c.2.1 c.2.2))
    (fun x c c' hc hc' => ?_) fun σ c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart N.isLB x
    obtain ⟨b, hb⟩ := exists_chart M.isLB x
    obtain ⟨c, hc⟩ := exists_chart L.isLB x
    exact ⟨(a, b, c), ⟨ha, hb⟩, hb, hc⟩
  · rw [map_mul, map_mul, gm_res (𝟙 X) x _ hc, gm_res (𝟙 X) x _ hc, gm_res (𝟙 X) x _ hc',
      gm_res (𝟙 X) x _ hc', hw _ (𝟙 X) x _ c'.2.1 _ c'.2.2 hc.2.1 hc'.2.1 hc.2.2 hc'.2.2,
      hw' _ (𝟙 X) x _ c'.1 _ c'.2.1 hc.1.1 hc'.1.1 hc.1.2 hc'.1.2]
    have key : ∀ {G : Type} [CommGroup G] (a b c d e : G),
        a * b⁻¹ * c * (b * d * e) = a * d * (c * e) := by
      intro G _ a b c d e
      rw [← mul_right_inj b, mul_right_comm a, ← mul_assoc b, mul_comm b, inv_mul_cancel_right]
      ac_rfl
    exact key _ _ _ _ _
  · have hy' := hy
    simp only [mem_ptsIn_inf] at hy'
    rw [logSq_mul hy, logSq_res _ hy, logSq_res _ hy, h' σ _ _ y hy'.1.1 hy'.1.2, h σ _ _ y hy'.2.1 hy'.2.2]
    ring

theorem Isometric.tens_right (h : L.Isometric M) (N : HermLB p) : (L.tens N).Isometric (M.tens N) := by
  obtain ⟨w, hw, h⟩ := h.exists_units
  refine isometric_of_local
    (fun c : M.B.ι × L.B.ι × N.B.ι => M.B.U c.1 ⊓ L.B.U c.2.1 ⊓ N.B.U c.2.2)
    (fun x => ?_) (fun c => (c.1, c.2.2)) (·.2) (fun _ _ h => ⟨h.1.1, h.2⟩) (fun _ _ h => ⟨h.1.2, h.2⟩)
    (fun c => res inf_le_left (w c.1 c.2.1)) (fun x c c' hc hc' => ?_) fun σ c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.isLB x
    obtain ⟨b, hb⟩ := exists_chart L.isLB x
    obtain ⟨c, hc⟩ := exists_chart N.isLB x
    exact ⟨(a, b, c), ⟨ha, hb⟩, hc⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_tens M.B N.B (𝟙 X) x (c.1, c.2.2) (c'.1, c'.2.2) ⟨hc.1.1, hc.2⟩ ⟨hc'.1.1, hc'.2⟩)
      (gm_tens L.B N.B (𝟙 X) x c.2 c'.2 ⟨hc.1.2, hc.2⟩ ⟨hc'.1.2, hc'.2⟩))).symm
    rw [gm_res (𝟙 X) x _ hc, gm_res (𝟙 X) x _ hc', hw _ (𝟙 X) x _ c'.1 _ c'.2.1 hc.1.1 hc'.1.1 hc.1.2 hc'.1.2,
      ← div_eq_mul_inv, ← div_eq_mul_inv, mul_div_mul_right_eq_div]
  · have hy' := hy
    simp only [mem_ptsIn_inf] at hy'
    rw [logSq_res _ hy]
    change (M.φ σ).φ _ y + (N.φ σ).φ _ y = (L.φ σ).φ _ y + (N.φ σ).φ _ y + _
    rw [h σ _ _ y hy'.1.1 hy'.1.2]
    ring

theorem Isometric.pull (h : L.Isometric M) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).Isometric (M.pull π hπ) := by
  obtain ⟨w, hw, h⟩ := h.exists_units
  refine isometric_of_local (fun c : M.B.ι × L.B.ι => π ⁻¹ᵁ (M.B.U c.1 ⊓ L.B.U c.2))
    (fun x => ?_) (fun c _ => c.1) (fun c _ => c.2) (fun _ _ h => mem_pull.2 h.1)
    (fun _ _ h => mem_pull.2 h.2) (fun c => pullU π _ (w c.1 c.2)) (fun x c c' hc hc' => ?_)
    fun σ c y hy => ?_
  · obtain ⟨a, ha⟩ := exists_chart M.isLB (π x)
    obtain ⟨b, hb⟩ := exists_chart L.isLB (π x)
    exact ⟨(a, b), ha, hb⟩
  · refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹)
      (gm_pull_g M.B π (𝟙 Y) x (fun _ => c.1) (fun _ => c'.1) (mem_pull.2 hc.1) (mem_pull.2 hc'.1))
      (gm_pull_g L.B π (𝟙 Y) x (fun _ => c.2) (fun _ => c'.2) (mem_pull.2 hc.2) (mem_pull.2 hc'.2)))).symm
    rw [gm_pull (𝟙 Y) π x _ hc, gm_pull (𝟙 Y) π x _ hc']
    exact hw _ _ x _ _ _ _ hc.1 hc'.1 hc.2 hc'.2
  · have hy' : PtsOver.map π hπ _ y ∈ ptsIn p σ (M.B.U c.1 ⊓ L.B.U c.2) := hy
    refine ((M.φ σ).pull_φ π hπ _ y).trans ((h σ _ _ _ (mem_ptsIn_inf.1 hy').1 (mem_ptsIn_inf.1 hy').2).trans
      (congrArg₂ (· + ·) ((L.φ σ).pull_φ π hπ (fun _ => c.2) y).symm ?_))
    exact congrArg (fun z => Real.log (‖z‖ ^ 2)) (ev_app π hπ _ _ y).symm

variable (L M N)

theorem isometric_tens_comm : (L.tens M).Isometric (M.tens L) :=
  isometric_of_chart (fun c => (c.2, c.1)) (fun _ _ h => ⟨h.2, h.1⟩)
    (fun x c c' h h' => (gm_tens L.B M.B (𝟙 X) x c c' h h').trans ((mul_comm _ _).trans
      (gm_tens M.B L.B (𝟙 X) x (c.2, c.1) (c'.2, c'.1) ⟨h.2, h.1⟩ ⟨h'.2, h'.1⟩).symm))
    fun _ _ _ _ => add_comm _ _

theorem isometric_tens_assoc : ((L.tens M).tens N).Isometric (L.tens (M.tens N)) :=
  isometric_of_chart (fun c => (c.1.1, c.1.2, c.2)) (fun _ _ h => ⟨h.1.1, h.1.2, h.2⟩)
    (fun x c c' h h' => ((gm_tens (CechPic.tens L.B M.B) N.B (𝟙 X) x c c' h h').trans
      (congrArg (· * _) (gm_tens L.B M.B (𝟙 X) x c.1 c'.1 h.1 h'.1))).trans ((mul_assoc _ _ _).trans
      ((gm_tens L.B (CechPic.tens M.B N.B) (𝟙 X) x (c.1.1, c.1.2, c.2) (c'.1.1, c'.1.2, c'.2)
        ⟨h.1.1, h.1.2, h.2⟩ ⟨h'.1.1, h'.1.2, h'.2⟩).trans (congrArg (_ * ·)
        (gm_tens M.B N.B (𝟙 X) x (c.1.2, c.2) (c'.1.2, c'.2) ⟨h.1.2, h.2⟩ ⟨h'.1.2, h'.2⟩))).symm))
    fun _ _ _ _ => (add_assoc _ _ _).symm

theorem isometric_tens_fnB (u : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) (hu : ∀ σ y, CInfAt (u σ) y)
    (hc : ∀ σ σ', (Weight.ofFun (u σ)).IsConj (Weight.ofFun (u σ'))) :
    (M.tens (fnB u hu hc)).Isometric (M.raise u hu hc) :=
  isometric_of_chart (fun c => c.1) (fun _ _ h => h.1)
    (fun x c c' h h' => (gm_tens M.B (LB.triv X) (𝟙 X) x c c' h h').trans
      ((congrArg (_ * ·) (map_one _)).trans (mul_one _)))
    fun _ _ _ _ => rfl

theorem isometric_tens_triv : (L.tens (triv p)).Isometric L :=
  isometric_of_chart (fun c => c.1) (fun _ _ h => h.1)
    (fun x c c' h h' => (gm_tens L.B (LB.triv X) (𝟙 X) x c c' h h').trans
      ((congrArg (_ * ·) (map_one _)).trans (mul_one _)))
    fun _ _ _ _ => (add_zero _).symm

theorem isometric_triv_tens : ((triv p).tens L).Isometric L :=
  (isometric_tens_comm _ _).trans L.isometric_tens_triv

theorem isometric_dual_tens : (L.dual.tens L).Isometric (triv p) :=
  isometric_of_local L.B.U (exists_chart L.isLB) (fun _ => PUnit.unit) (fun j => (j, j)) (fun _ => le_top)
    (fun _ _ h => ⟨h, h⟩) (fun _ => 1) (fun x j j' h h' => by
      have e := (gm_tens (CechPic.dual L.B) L.B (𝟙 X) x (j, j) (j', j') ⟨h, h⟩ ⟨h', h'⟩).trans
        ((congrArg (· * _) (map_inv _ _)).trans (inv_mul_cancel _))
      refine Eq.trans ?_ (congrArg (· * _) (congrArg₂ (fun a b => a * b⁻¹) (map_one _) e)).symm
      rw [map_one, map_one, inv_one, mul_one, mul_one])
    fun σ j y h => by rw [logSq_one h, add_zero]; exact (neg_add_cancel _).symm

theorem isometric_pow_zero : (L.pow 0).Isometric (triv p) :=
  isometric_of_chart (fun _ => PUnit.unit) (fun _ => le_top)
    (fun x j j' h h' => (gm_linComb L.B _ _ (𝟙 X) x j j' h h').trans
      ((Fintype.prod_unique _).trans ((zpow_zero _).trans (map_one _).symm)))
    fun σ j y _ => (((L.φ σ).zpow_φ _ j y).trans (by simp; rfl)).symm

theorem isometric_pow_succ (m : ℕ) : (L.pow (m + 1)).Isometric ((L.pow m).tens L) :=
  isometric_of_chart (fun j => (j, j PUnit.unit)) (fun _ _ h => ⟨h, Set.mem_iInter.1 h PUnit.unit⟩)
    (fun x j j' h h' => by
      refine (gm_linComb L.B _ _ (𝟙 X) x j j' h h').trans (Eq.trans ?_
        ((gm_tens (lbPow L.B m) L.B (𝟙 X) x (j, j PUnit.unit) (j', j' PUnit.unit)
          ⟨h, Set.mem_iInter.1 h PUnit.unit⟩ ⟨h', Set.mem_iInter.1 h' PUnit.unit⟩).trans
          (congrArg (· * _) (gm_linComb L.B _ _ (𝟙 X) x j j' h h'))).symm)
      rw [Fintype.prod_unique, Fintype.prod_unique, Nat.cast_succ, zpow_add_one]
      rfl)
    fun σ j y _ => ((congrArg (· + _) ((L.φ σ).zpow_φ _ j y)).trans (by push_cast; ring)).trans
      ((L.φ σ).zpow_φ _ j y).symm

theorem isometric_pull_tens (π : Y ⟶ X) (hπ : π ≫ p = q) :
    ((L.tens M).pull π hπ).Isometric ((L.pull π hπ).tens (M.pull π hπ)) :=
  isometric_of_chart (fun j => (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2))
    (fun _ _ h => ⟨mem_pull.2 (mem_pull.1 h).1, mem_pull.2 (mem_pull.1 h).2⟩)
    (fun x j j' h h' => by
      have e := mem_pull.1 h
      have e' := mem_pull.1 h'
      refine ((gm_pull_g (CechPic.tens L.B M.B) π (𝟙 Y) x j j' h h').trans
        (gm_tens L.B M.B (𝟙 Y ≫ π) x _ _ e e')).trans (Eq.symm ?_)
      exact (gm_tens (L.B.pull π) (M.B.pull π) (𝟙 Y) x (fun _ => (j PUnit.unit).1, fun _ => (j PUnit.unit).2)
        (fun _ => (j' PUnit.unit).1, fun _ => (j' PUnit.unit).2) ⟨mem_pull.2 e.1, mem_pull.2 e.2⟩
        ⟨mem_pull.2 e'.1, mem_pull.2 e'.2⟩).trans (congrArg₂ (· * ·)
          (gm_pull_g L.B π (𝟙 Y) x _ _ (mem_pull.2 e.1) (mem_pull.2 e'.1))
          (gm_pull_g M.B π (𝟙 Y) x _ _ (mem_pull.2 e.2) (mem_pull.2 e'.2))))
    fun σ j y _ => (congrArg₂ (· + ·) ((L.φ σ).pull_φ π hπ _ y) ((M.φ σ).pull_φ π hπ _ y)).trans
      (((L.tens M).φ σ).pull_φ π hπ j y).symm

theorem shift_eq_raise (t : (k →+* ℂ) → ℝ) (ht : ∀ σ, t ((starRingEnd ℂ).comp σ) = t σ) :
    L.shift t ht = L.raise (fun σ _ => 2 * t σ) (fun _ => cInfAt_const _) fun σ _ _ _ _ h _ =>
      congrArg (2 * ·) ((congrArg t (eq_conj_of_conj h)).trans (ht σ)) := rfl

variable {L M N}

theorem Isometric.tens (h : L.Isometric M) (h' : L'.Isometric M') : (L.tens L').Isometric (M.tens M') :=
  (h.tens_right L').trans ((isometric_tens_comm _ _).trans ((h'.tens_right M).trans (isometric_tens_comm _ _)))

theorem Isometric.dual (h : L.Isometric M) : L.dual.Isometric M.dual :=
  (isometric_triv_tens _).symm.trans <| (M.isometric_dual_tens.symm.tens_right _).trans <|
    (isometric_tens_assoc _ _ _).trans <| ((Isometric.refl _).tens ((h.symm.tens_right _).trans
      ((isometric_tens_comm _ _).trans L.isometric_dual_tens))).trans (isometric_tens_triv _)

variable (p) in

def isometrySetoid : Setoid (HermLB p) := ⟨Isometric, Isometric.refl, Isometric.symm, Isometric.trans⟩

variable (p) in

def IsomClass : Type 1 := Quotient (isometrySetoid p)

def icls (L : HermLB p) : IsomClass p := Quotient.mk _ L

theorem icls_eq_iff : L.icls = M.icls ↔ L.Isometric M := Quotient.eq (r := isometrySetoid p)

instance : Add (IsomClass p) := ⟨Quotient.map₂ tens fun _ _ h _ _ h' => Isometric.tens h h'⟩

instance : Zero (IsomClass p) := ⟨(triv p).icls⟩

instance : Neg (IsomClass p) := ⟨Quotient.map dual fun _ _ h => Isometric.dual h⟩

instance : AddGroup (IsomClass p) := AddGroup.ofLeftAxioms
  (by rintro ⟨L⟩ ⟨M⟩ ⟨N⟩; exact icls_eq_iff.2 (isometric_tens_assoc L M N))
  (by rintro ⟨L⟩; exact icls_eq_iff.2 L.isometric_triv_tens)
  (by rintro ⟨L⟩; exact icls_eq_iff.2 L.isometric_dual_tens)

instance : AddCommGroup (IsomClass p) where
  add_comm := by rintro ⟨L⟩ ⟨M⟩; exact icls_eq_iff.2 (isometric_tens_comm L M)

theorem icls_tens (L M : HermLB p) : (L.tens M).icls = L.icls + M.icls := rfl

theorem icls_dual (L : HermLB p) : L.dual.icls = -L.icls := rfl

theorem icls_triv : (triv p).icls = 0 := rfl

theorem nontrivial_isomClass_int : Nontrivial (IsomClass (𝟙 (Sp ℤ))) :=
  ⟨(ArithBase.trivShift 0).icls, (ArithBase.trivShift 1).icls, fun h =>
    zero_ne_one (eq_of_isometric_trivShift (icls_eq_iff.1 h))⟩

theorem icls_pow (L : HermLB p) (m : ℕ) : (L.pow m).icls = m • L.icls := by
  induction m with
  | zero => rw [zero_nsmul]; exact icls_eq_iff.2 L.isometric_pow_zero
  | succ m ih => rw [succ_nsmul, ← ih]; exact icls_eq_iff.2 (L.isometric_pow_succ m)

theorem Isometric.pow (h : L.Isometric M) (m : ℕ) : (L.pow m).Isometric (M.pow m) :=
  icls_eq_iff.1 (by rw [icls_pow, icls_pow, icls_eq_iff.2 h])

def IsomClass.pull (π : Y ⟶ X) (hπ : π ≫ p = q) : IsomClass p →+ IsomClass q :=
  AddMonoidHom.mk' (Quotient.map (fun L => L.pull π hπ) fun _ _ h => Isometric.pull h π hπ)
    (by rintro ⟨L⟩ ⟨M⟩; exact icls_eq_iff.2 (isometric_pull_tens L M π hπ))

theorem icls_pull (L : HermLB p) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (L.pull π hπ).icls = IsomClass.pull π hπ L.icls := rfl

end HermLB

namespace ArInt

open HermLB

variable {ι : Type} [Fintype ι]

theorem icls_zp (L : HermLB p) (n : ℤ) : (zp L n).icls = n • L.icls := by
  rw [zp, icls_tens, icls_dual, icls_pow, icls_pow, ← natCast_zsmul, ← natCast_zsmul, ← sub_eq_add_neg,
    ← sub_smul, Int.toNat_sub_toNat_neg]

theorem icls_comb (L : ι → HermLB p) (n : ι → ℤ) : (comb L n).icls = ∑ i, n i • (L i).icls := by
  rw [← Finset.sum_map_toList, comb]
  induction (Finset.univ : Finset ι).toList with
  | nil => rfl
  | cons i l ih => rw [List.foldr_cons, icls_tens, ih, icls_zp, List.map_cons, List.sum_cons]

theorem isometric_comb_single [DecidableEq ι] (L : ι → HermLB p) (i : ι) :
    (comb L (Pi.single i 1)).Isometric (L i) :=
  icls_eq_iff.1 (by simp [icls_comb, Pi.single_apply])

theorem isometric_comb_add (L : ι → HermLB p) (n n' : ι → ℤ) :
    (comb L (n + n')).Isometric ((comb L n).tens (comb L n')) :=
  icls_eq_iff.1 (by simp [icls_comb, icls_tens, add_smul, Finset.sum_add_distrib])

theorem isometric_comb_pull (L : ι → HermLB p) (n : ι → ℤ) (π : Y ⟶ X) (hπ : π ≫ p = q) :
    (comb (fun i => (L i).pull π hπ) n).Isometric ((comb L n).pull π hπ) :=
  icls_eq_iff.1 (by simp [icls_comb, icls_pull])

theorem isometric_comb_congr {L M : ι → HermLB p} (h : ∀ i, (L i).Isometric (M i)) (n : ι → ℤ) :
    (comb L n).Isometric (comb M n) :=
  icls_eq_iff.1 (by simp only [icls_comb, fun i => icls_eq_iff.2 (h i)])

theorem isometric_comb_comb {κ : Type} [Fintype κ] (L : ι → HermLB p) (A : κ → ι → ℤ) (m : κ → ℤ) :
    (comb L fun i => ∑ j, m j * A j i).Isometric (comb (fun j => comb L (A j)) m) :=
  icls_eq_iff.1 (by
    simp only [icls_comb, Finset.sum_smul, Finset.smul_sum, mul_smul]
    exact Finset.sum_comm)

end ArInt

namespace HermLB

variable {L M : HermLB p} {D : ℕ}

theorem Isometric.hess_eq (h : L.Isometric M) (c : AlgChart p σ D) {y : CxPts p σ} (hy : y ∈ c.e.source)
    {a : M.B.ι} {b : L.B.ι} (ha : y ∈ ptsIn p σ (M.B.U a)) (hb : y ∈ ptsIn p σ (L.B.U b)) :
    c.hess (M.φ σ) a y = c.hess (L.φ σ) b y := by
  obtain ⟨w, -, h⟩ := h.exists_units
  have ho := isOpen_over c.e (isOpen_ptsIn (p := p) (σ := σ) (M.B.U a ⊓ L.B.U b))
  have hm := mem_over c.e hy (mem_ptsIn_inf.2 ⟨ha, hb⟩)
  have hg := c.holo _ (w a b).val
  have h0 : ∀ v ∈ c.e.target ∩ c.e.symm ⁻¹' ptsIn p σ (M.B.U a ⊓ L.B.U b),
      (ev p σ _ (w a b).val ∘ c.e.symm) v ≠ 0 := fun v hv => ev_ne_zero hv.2 (w a b).isUnit
  have e := ReciprocityTheory.L2DbarEstimates.I.MongeAmpereIntegrability.cHess_add_smul ho
    ((contDiffOn_chart (L.cInf σ b) c).mono fun v hv => ⟨hv.1, (mem_ptsIn_inf.1 hv.2).2⟩)
    (contDiffOn_log_normSq ho hg h0) 1 hm
  have e₀ : ReciprocityTheory.L2DbarEstimates.cHess D
      (fun v => ((Real.log (‖(ev p σ _ (w a b).val ∘ c.e.symm) v‖ ^ 2) : ℝ) : ℂ)) (c.e y) = 0 := by
    ext i j
    exact ReciprocityTheory.L2DbarEstimates.Y.cmpa_hess_log ho hm hg h0 i j
  rw [e₀, smul_zero, add_zero] at e
  refine Eq.trans (ReciprocityTheory.L2DbarEstimates.Y.cmpb_cHess_congr ?_) e
  filter_upwards [ho.mem_nhds hm] with v hv
  rw [h σ a b _ (mem_ptsIn_inf.1 hv.2).1 (mem_ptsIn_inf.1 hv.2).2, one_mul]
  rfl

theorem Isometric.chernPart_eq (h : L.Isometric M) (σ : k →+* ℂ) (D : ℕ) (ε : ℤˣ) :
    (L.φ σ).chernPart D ε = (M.φ σ).chernPart D ε := by
  refine iSup_congr fun c => congrArg (MeasureTheory.Measure.map _) (MeasureTheory.withDensity_congr_ae
    (MeasureTheory.ae_restrict_of_forall_mem c.e.open_target.measurableSet fun v hv => ?_))
  simp only [Function.comp_apply, AlgChart.chernDens,
    h.hess_eq c (c.e.map_target hv) (mem_pick (M.φ σ).isLB _) (mem_pick (L.φ σ).isLB _)]

theorem Isometric.chernInt_eq (h : L.Isometric M) (σ : k →+* ℂ) (D : ℕ) :
    (L.φ σ).chernInt D = (M.φ σ).chernInt D := by
  funext S f
  rw [Weight.chernInt, Weight.chernInt, h.chernPart_eq, h.chernPart_eq]

theorem Isometric.chernIntegrableOn_eq (h : L.Isometric M) (σ : k →+* ℂ) (D : ℕ) :
    (L.φ σ).ChernIntegrableOn D = (M.φ σ).ChernIntegrableOn D := by
  funext S f
  rw [Weight.ChernIntegrableOn, Weight.ChernIntegrableOn, h.chernPart_eq, h.chernPart_eq]

theorem Isometric.chInt_eq (h : L.Isometric M) (D : ℕ) (f : ∀ σ : k →+* ℂ, CxPts p σ → ℝ) :
    chInt L D f = chInt M D f := by
  simp only [chInt, h.chernInt_eq]

theorem Isometric.gdeg_eq (h : L.Isometric M) (D : ℕ) : gdeg L D = gdeg M D := h.chInt_eq D _

theorem Isometric.exists_isRatSec [IsIntegral X] (h : L.Isometric M) {r : L.B.ι → X.functionFieldˣ}
    (hr : IsRatSec L.B r) : ∃ (r' : M.B.ι → X.functionFieldˣ) (hr' : IsRatSec M.B r'), M.div hr' = L.div hr ∧
      ∀ σ, Set.EqOn (logNorm (M.φ σ) r') (logNorm (L.φ σ) r) (offSupp p σ (L.div hr)) := by
  classical
  obtain ⟨w, hw, h⟩ := h.exists_units
  obtain ⟨b₀, h₀⟩ := exists_chart L.isLB (genericPoint X)
  let F (U : X.Opens) (u : Γ(X, U)ˣ) : X.functionFieldˣ := gm (𝟙 X) (genericPoint X) U u
  have hF (U : X.Opens) (u : Γ(X, U)ˣ) (hU : genericPoint X ∈ U) : (F U u : X.functionField) = fnOf U hU u.val :=
    gm_val (𝟙 X) _ U hU u
  have hw' (a a' b b') (h₁ : genericPoint X ∈ M.B.U a) (h₂ : genericPoint X ∈ M.B.U a')
      (h₃ : genericPoint X ∈ L.B.U b) (h₄ : genericPoint X ∈ L.B.U b') :
      F _ (w a b) = F _ (M.B.g a a') * (F _ (L.B.g b b'))⁻¹ * F _ (w a' b') :=
    hw _ (𝟙 X) _ a a' b b' h₁ h₂ h₃ h₄
  have hM (a) (h₁ : genericPoint X ∈ M.B.U a) : F _ (M.B.g a a) = 1 := gm_self M.isLB (𝟙 X) _ h₁
  have hL : F _ (L.B.g b₀ b₀) = 1 := gm_self L.isLB (𝟙 X) _ h₀
  have hr' : IsRatSec M.B fun a => F _ (w a b₀) * r b₀ := fun a a' h' => by
    beta_reduce
    rw [← hF, ← Units.val_mul, hw' a a' b₀ b₀ h'.1 h'.2 h₀ h₀, hL, inv_one, mul_one, mul_assoc]
  have key (a b) (h' : genericPoint X ∈ M.B.U a ⊓ L.B.U b) :
      ((F _ (w a b₀) * r b₀ : X.functionFieldˣ) : X.functionField) = fnOf _ h' (w a b).val * r b := by
    rw [← hF, hr b b₀ (memInf h'.2 h₀), ← hF _ (L.B.g b b₀), ← Units.val_mul, ← Units.val_mul, hw' a a b b₀ h'.1 h'.1 h'.2 h₀,
      hM a h'.1, one_mul, mul_comm (F _ (L.B.g b b₀))⁻¹, mul_assoc, inv_mul_cancel_left]
  have hd : M.div hr' = L.div hr := CartierDiv.ext_of_isEqn fun x => by
    obtain ⟨a, ha⟩ := exists_chart M.isLB x
    obtain ⟨b, hb⟩ := exists_chart L.isLB x
    refine ⟨_, (presents_divOfRatSec _ hr').isEqn a x ha,
      ((presents_divOfRatSec _ hr).isEqn b x hb).iff_unitAt.2 ?_⟩
    rw [key a b (gen_mem (memInf ha hb)), mul_div_cancel_right₀ _ (r b).ne_zero]
    exact unitAt_fnOf (memInf ha hb) _ _
  refine ⟨_, hr', hd, fun σ y hy => ?_⟩
  have ha := mem_pick (M.φ σ).isLB y
  have hb := mem_pick (L.φ σ).isLB y
  have hab := mem_ptsIn_inf.2 ⟨ha, hb⟩
  have hu := hr.unitAt L.isLB hy hb
  rw [logNorm, logNorm, key _ _ (gen_mem (mem_ptsIn.1 hab)),
    ratVal_mul (regAt_fnOf (mem_ptsIn.1 hab) _ _) hu.regAt, ratVal_fnOf hab, h σ _ _ y ha hb, logSq,
    norm_mul, Real.log_mul (norm_ne_zero_iff.2 (ev_ne_zero hab (Units.isUnit _)))
      (norm_ne_zero_iff.2 (ratVal_ne_zero hu)), Real.log_pow]
  push_cast
  ring

end HermLB

theorem IsArithVar.under_eq_genericPoint [IsIntegral X] (hX : IsArithVar p 0) (y : CxPts p σ) :
    under y = genericPoint X := by
  obtain ⟨Z, i, _, _, hi⟩ := exists_isClosedImmersion_genericPoint (under y)
  have hc : CharZero Γ(Z, ⊤) := charZero_of_inj_zero fun n hn => by_contra fun h0 => by
    have h₁ : ev p σ ⊤ (n : Γ(X, ⊤)) y ≠ 0 := by
      rw [ev_eq mem_ptsIn_top, map_natCast]
      exact Nat.cast_ne_zero.2 h0
    have h₂ : genericPoint Z ∈ i ⁻¹ᵁ X.basicOpen (n : Γ(X, ⊤)) := by
      have := mem_ptsIn.1 ((mem_ptsIn_basicOpen mem_ptsIn_top _).2 h₁)
      change i (genericPoint Z) ∈ X.basicOpen _
      rw [hi]
      exact this
    rw [Scheme.preimage_basicOpen_top, map_natCast, hn, Scheme.basicOpen_zero] at h₂
    exact h₂
  have hr : closure {under y} = Set.range i := by
    have h₁ := (genericPoint_spec Z).image i.continuous
    rw [Set.image_univ, i.isClosedEmbedding.isClosed_range.closure_eq, hi] at h₁
    exact h₁
  rcases Order.krullDim_le_one_iff.1 (show Order.krullDim (IrreducibleCloseds X) ≤ 1 from hX.dim_eq.le)
    ⟨closure {under y}, isIrreducible_singleton.closure, isClosed_closure⟩ with h | h
  · obtain ⟨d, hd⟩ := hX.exists_dim_eq i
    have h0 : topologicalKrullDim Z ≤ 0 := Order.krullDim_nonpos_iff_forall_isMax.2 fun T T' _ z _ => by
      have := @h ⟨i '' T, T.isIrreducible.image i i.continuous.continuousOn,
        i.isClosedEmbedding.isClosedMap _ T.isClosed⟩ ((Set.image_subset_range _ _).trans hr.ge)
        (i z) (hr.ge ⟨z, rfl⟩)
      exact (i.isClosedEmbedding.injective.mem_set_image).1 this
    refine absurd (le_antisymm h0 ?_) (hX.dim_ne_zero i hc)
    rw [hd]
    exact Nat.cast_nonneg d
  · exact IsGenericPoint.eq (Set.eq_univ_of_univ_subset (@h
      ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩ (Set.subset_univ _))) (genericPoint_spec X)

namespace HermLB

variable {L M : HermLB p} {D : ℕ}

theorem Isometric.isArithHeight (hX : IsArithVar p D) (e : L.Isometric M) {h : X → ℝ} (H : L.IsArithHeight h) :
    M.IsArithHeight h where
  vertical Z i _ _ κ _ _ _ d hd := by
    have ⟨w, hw, _⟩ := e.pull i rfl
    have e' : topSelfIntersection κ (L.B.pull i) d = topSelfIntersection κ (M.B.pull i) d := interNum_congr_lbIso κ _
      (fun _ => (L.restr i).isLB) (fun _ => (M.restr i).isLB) fun _ => ⟨w, hw⟩
    rw [H.vertical Z i κ d hd, e']
  point Z i _ _ _ hc hd r hr := by
    obtain ⟨r', hr', h₁, h₂⟩ := (e.pull i rfl).symm.exists_isRatSec hr
    have hZ : IsArithVar (i ≫ p) 0 := hX.of_isClosedImmersion i hc hd
    rw [H.point Z i hc hd r' hr', curveDeg, curveDeg, h₁]
    refine congrArg _ (finsum_congr fun σ => finsum_congr fun y => h₂ σ (mem_offSupp.2 ?_))
    rw [hZ.under_eq_genericPoint]
    exact CartierDiv.genericPoint_notMem_supp _
  recursion Z i _ _ _ hc d hd hd' m r hr := by
    obtain ⟨r', hr', h₁, h₂⟩ := ((e.pull i rfl).pow m).symm.exists_isRatSec hr
    obtain ⟨h₃, h₄⟩ := H.recursion Z i hc d hd hd' m r' hr'
    simp only [ArchIntegrable, archInt, h₁, (e.pull i rfl).chernInt_eq,
      (e.pull i rfl).chernIntegrableOn_eq] at h₃ h₄
    exact ⟨fun σ => (h₃ σ).congr (isOpen_offSupp _).measurableSet (h₂ σ), h₄.trans (congrArg _
      (finsum_congr fun σ => Weight.chernInt_congr (isOpen_offSupp _).measurableSet (h₂ σ)))⟩

theorem Isometric.isSelfInter [IsIntegral X] (hX : IsArithVar p D) (e : L.Isometric M) {a : ℝ}
    (H : L.IsSelfInter a) : M.IsSelfInter a :=
  have ⟨h, H₁, H₂⟩ := H
  ⟨h, e.isArithHeight hX H₁, H₂⟩

end HermLB

namespace ArInt

variable {ι κ : Type} [Fintype ι] [Fintype κ]

theorem isHomogeneous_lin (n : ι → ℝ) : (lin n).IsHomogeneous 1 :=
  IsHomogeneous.sum _ _ _ fun i _ => isHomogeneous_C_mul_X _ i

theorem aeval_lin (A : κ → ι → ℝ) (m : κ → ℝ) :
    aeval (fun j => lin (A j)) (lin m) = lin fun i => ∑ j, m j * A j i := by
  simp only [lin, map_sum, map_mul, aeval_C, aeval_X, algebraMap_eq, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

theorem lin_single [DecidableEq ι] (i : ι) :
    (lin fun j => ((Pi.single i 1 : ι → ℤ) j : ℝ)) = MvPolynomial.X i := by
  simp [lin, Pi.single_apply, apply_ite C]

end ArInt

theorem Published.arIso_holds : Published.ArIso := by
  intro k _ X _ p D hX
  refine ⟨fun L M h e H => e.isArithHeight hX H, fun ι _ L Φ hΦ => ⟨fun i => ?_, fun M e => ⟨fun n => ?_, hΦ.2⟩,
    fun κ _ M A e => ⟨fun m => ?_, fun P d hd hP => ?_⟩⟩⟩
  · classical
    rw [← lin_single i]
    exact (isometric_comb_single L i).isSelfInter hX (hΦ.1 _)
  · exact (isometric_comb_congr e n).isSelfInter hX (hΦ.1 n)
  · have h := ((isometric_comb_comb L A m).trans (isometric_comb_congr e m)).isSelfInter hX (hΦ.1 _)
    rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, map_pow, aeval_lin]
    simpa only [Int.cast_sum, Int.cast_mul] using h
  · exact hΦ.2 _ d hd (by simpa using hP.aeval _ fun j => isHomogeneous_lin _)

end GlobalTheory
