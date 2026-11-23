import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso

noncomputable section

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor

open LBGerm

variable {X Y Y' Z : Scheme.{0}}

section ChartSec

variable {A' : LB Y'} {A : LB Y} {h : Y' ⟶ Y}

def chartSec (a : ChartPull A' A h) (s : A.Sec) : A'.Sec :=
  secOfGerm (fun i => (h.appLE _ _ (a.le i)).hom (s.f (a.idx i))) fun y i j hi hj => by
    rw [a.g y i j hi hj, gs_appLE h _ _ _ (𝟙 _) y hi, gs_appLE h _ _ _ (𝟙 _) y hj, Category.id_comp]
    exact gs_compat s h y (a.le i hi) (a.le j hj)

theorem chartSec_f (a : ChartPull A' A h) (s : A.Sec) (i : A'.ι) :
    (chartSec a s).f i = (h.appLE _ _ (a.le i)).hom (s.f (a.idx i)) := rfl

theorem gs_chartSec (a : ChartPull A' A h) (s : A.Sec) (r : Z ⟶ Y') (z : Z) (i : A'.ι) (hz : r z ∈ A'.U i) :
    gs r z _ ((chartSec a s).f i) = gs (r ≫ h) z _ (s.f (a.idx i)) := by
  rw [chartSec_f]
  exact gs_appLE h _ _ (a.le i) r z hz _

theorem nonzeroLocus_chartSec (a : ChartPull A' A h) (s : A.Sec)
    (hc : ∀ (y : Y') j, h y ∈ A.U j → ∃ i, y ∈ A'.U i) :
    nonzeroLocus (chartSec a s) = h ⁻¹ᵁ nonzeroLocus s := by
  refine SetLike.ext fun y => ?_
  have key : ∀ i, y ∈ A'.U i → (y ∈ nonzeroLocus (chartSec a s) ↔ h y ∈ nonzeroLocus s) := fun i hi => by
    rw [mem_nonzeroLocus_iff_isUnit _ hi, mem_nonzeroLocus_iff_pull s h y (a.le i hi), gs_chartSec a s (𝟙 Y') y i hi,
      Category.id_comp]
  constructor
  · intro hy
    obtain ⟨i, hi⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key i hi).1 hy
  · intro hy
    obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus (show h y ∈ nonzeroLocus s from hy)
    obtain ⟨i, hi⟩ := hc y j hj
    exact (key i hi).2 hy

theorem nonzeroLocus_chartSec_id {B B' : LB Y} (a : ChartPull B' B (𝟙 Y)) (s : B.Sec)
    (hc : ∀ (y : Y) j, y ∈ B.U j → ∃ i, y ∈ B'.U i) : nonzeroLocus (chartSec a s) = nonzeroLocus s := by
  rw [nonzeroLocus_chartSec a s hc]
  exact SetLike.ext fun _ => Iff.rfl

private theorem lbIso_g_cocycle_on_inter_of_pairs (hA : A.IsLB) (p₁ p₂ q₁ q₂ : A.ι) :
    res (inf_le_left : A.U p₁ ⊓ A.U p₂ ⊓ (A.U q₁ ⊓ A.U q₂) ≤ A.U p₁ ⊓ A.U p₂) (A.g p₁ p₂) =
      res (inf_le_inf inf_le_left inf_le_left : A.U p₁ ⊓ A.U p₂ ⊓ (A.U q₁ ⊓ A.U q₂) ≤ A.U p₁ ⊓ A.U q₁) (A.g p₁ q₁) *
        (res (inf_le_inf inf_le_right inf_le_right : A.U p₁ ⊓ A.U p₂ ⊓ (A.U q₁ ⊓ A.U q₂) ≤ A.U p₂ ⊓ A.U q₂)
          (A.g p₂ q₂))⁻¹ *
      res (inf_le_right : A.U p₁ ⊓ A.U p₂ ⊓ (A.U q₁ ⊓ A.U q₂) ≤ A.U q₁ ⊓ A.U q₂) (A.g q₁ q₂) := by
  refine unit_ext fun y hy => ?_
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy, gm_res (𝟙 Y) y _ hy,
    gm_res (𝟙 Y) y _ hy]
  have c₁ := gm_cocycle hA (𝟙 Y) y hy.1.1 hy.2.1 hy.2.2
  have c₂ := gm_cocycle hA (𝟙 Y) y hy.1.1 hy.1.2 hy.2.2
  rw [eq_mul_inv_of_mul_eq c₂, ← c₁, mul_right_comm]

theorem lbIso_refl (hA : A.IsLB) : LBIso A A := ⟨⟨fun p => A.g p.1 p.2⟩, fun p q => lbIso_g_cocycle_on_inter_of_pairs hA p.1 p.2 q.1 q.2⟩

private theorem lbIso_of_chartPull_lemma {B B' : LB Y} (a : ChartPull B' B (𝟙 Y)) {y : Y} {p₁ q₁ : B.ι}
    {p₂ q₂ : B'.ι} (hp₁ : y ∈ B.U p₁) (hp₂ : y ∈ B'.U p₂) (hq₁ : y ∈ B.U q₁) (hq₂ : y ∈ B'.U q₂) :
    gm (𝟙 Y) y (B.U p₁ ⊓ B'.U p₂ ⊓ (B.U q₁ ⊓ B'.U q₂))
        (res (inf_le_inf inf_le_left inf_le_left : B.U p₁ ⊓ B'.U p₂ ⊓ (B.U q₁ ⊓ B'.U q₂) ≤ B.U p₁ ⊓ B.U q₁) (B.g p₁ q₁) *
          (res (inf_le_inf inf_le_right inf_le_right : B.U p₁ ⊓ B'.U p₂ ⊓ (B.U q₁ ⊓ B'.U q₂) ≤ B'.U p₂ ⊓ B'.U q₂)
            (B'.g p₂ q₂))⁻¹) =
      gm (𝟙 Y) y (B.U p₁ ⊓ B.U (a.idx p₂) ⊓ (B.U q₁ ⊓ B.U (a.idx q₂)))
        (res (inf_le_inf inf_le_left inf_le_left :
            B.U p₁ ⊓ B.U (a.idx p₂) ⊓ (B.U q₁ ⊓ B.U (a.idx q₂)) ≤ B.U p₁ ⊓ B.U q₁) (B.g p₁ q₁) *
          (res (inf_le_inf inf_le_right inf_le_right :
            B.U p₁ ⊓ B.U (a.idx p₂) ⊓ (B.U q₁ ⊓ B.U (a.idx q₂)) ≤ B.U (a.idx p₂) ⊓ B.U (a.idx q₂))
            (B.g (a.idx p₂) (a.idx q₂)))⁻¹) := by
  have hV : y ∈ B.U p₁ ⊓ B'.U p₂ ⊓ (B.U q₁ ⊓ B'.U q₂) := ⟨⟨hp₁, hp₂⟩, ⟨hq₁, hq₂⟩⟩
  have hW : y ∈ B.U p₁ ⊓ B.U (a.idx p₂) ⊓ (B.U q₁ ⊓ B.U (a.idx q₂)) := ⟨⟨hp₁, a.le p₂ hp₂⟩, ⟨hq₁, a.le q₂ hq₂⟩⟩
  rw [map_mul, map_mul, map_inv, map_inv, gm_res (𝟙 Y) y _ hV, gm_res (𝟙 Y) y _ hV, gm_res (𝟙 Y) y _ hW,
    gm_res (𝟙 Y) y _ hW, a.g y p₂ q₂ hp₂ hq₂]

theorem lbIso_of_chartPull {B B' : LB Y} (a : ChartPull B' B (𝟙 Y)) (hB : B.IsLB) : LBIso B' B := by
  have cp : ChartPull (B.div B') (B.div B) (𝟙 Y) :=
    { idx := fun p => (p.1, a.idx p.2)
      le := fun p y hy => (show y ∈ B.U p.1 ⊓ B.U (a.idx p.2) from ⟨hy.1, a.le p.2 hy.2⟩)
      g := fun y p q hp hq => lbIso_of_chartPull_lemma a hp.1 hp.2 hq.1 hq.2 }
  obtain ⟨w, hw⟩ := lbIso_refl hB
  obtain ⟨t, ht⟩ := gen_chartPull cp w hw
  exact ⟨t, ht⟩

end ChartSec

section Pull

variable {L : LB X}

def chartPullPull (L : LB X) (f : Y ⟶ X) : ChartPull (L.pull f) L f where
  idx J := J PUnit.unit
  le _ _ hy := mem_pull.1 hy
  g y J J' hJ hJ' := (gm_pull_g L f (𝟙 Y) y J J' hJ hJ').trans (by rw [Category.id_comp])

def secPull (s : L.Sec) (f : Y ⟶ X) : (L.pull f).Sec := chartSec (chartPullPull L f) s

theorem nonzeroLocus_secPull (s : L.Sec) (f : Y ⟶ X) : nonzeroLocus (secPull s f) = f ⁻¹ᵁ nonzeroLocus s := nonzeroLocus_chartSec _ s fun _ j hy => ⟨fun _ => j, mem_pull.2 hy⟩

variable {K K' : Type} [Fintype K] [Fintype K']

theorem nonzeroLocus_pullSec (φ : K → (Y ⟶ X)) (ε : K → ℤ) (s : (LB.LinComb L φ ε).Sec) (h : Z ⟶ Y) :
    nonzeroLocus (DVR.pullSec L φ ε s h) = h ⁻¹ᵁ nonzeroLocus s := by
  refine SetLike.ext fun y => ?_
  have key : ∀ j : K → L.ι, y ∈ LB.wchart L (fun k => h ≫ φ k) j →
      (y ∈ nonzeroLocus (DVR.pullSec L φ ε s h) ↔ h y ∈ nonzeroLocus s) := fun j hj => by
    have hj' : h y ∈ LB.wchart L φ j := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k
    have e : gs (𝟙 Z) y (LB.wchart L (fun k => h ≫ φ k) j) ((DVR.pullSec L φ ε s h).f j) =
        gs h y (LB.wchart L φ j) (s.f j) :=
      (gs_res (𝟙 Z) y _ hj _).trans ((gs_pull (𝟙 Z) h y _ hj' _).trans (by rw [Category.id_comp]))
    rw [mem_nonzeroLocus_iff_isUnit (DVR.pullSec L φ ε s h) hj, mem_nonzeroLocus_iff_pull s h y hj']
    exact (congrArg IsUnit e).to_iff
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key j hj).1 hy
  · intro hy
    obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus (show h y ∈ nonzeroLocus s from hy)
    exact (key j (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)).2 hy

theorem nonzeroLocus_mulSec (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K' → (Y ⟶ X)) (ε' : K' → ℤ)
    (s : (LB.LinComb L φ ε).Sec) (s' : (LB.LinComb L φ' ε').Sec) :
    nonzeroLocus (DVR.mulSec L φ ε φ' ε' s s') = nonzeroLocus s ⊓ nonzeroLocus s' := by
  refine SetLike.ext fun y => ?_
  have key : ∀ j : K ⊕ K' → L.ι, y ∈ LB.wchart L (Sum.elim φ φ') j →
      (y ∈ nonzeroLocus (DVR.mulSec L φ ε φ' ε' s s') ↔ y ∈ nonzeroLocus s ⊓ nonzeroLocus s') := fun j hj => by
    have h₁ : y ∈ LB.wchart L φ (j ∘ Sum.inl) := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj (Sum.inl k)
    have h₂ : y ∈ LB.wchart L φ' (j ∘ Sum.inr) := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj (Sum.inr k)
    have e : gs (𝟙 Y) y (LB.wchart L (Sum.elim φ φ') j) ((DVR.mulSec L φ ε φ' ε' s s').f j) =
        gs (𝟙 Y) y (LB.wchart L φ (j ∘ Sum.inl)) (s.f (j ∘ Sum.inl)) *
          gs (𝟙 Y) y (LB.wchart L φ' (j ∘ Sum.inr)) (s'.f (j ∘ Sum.inr)) :=
      (gs_mul (𝟙 Y) y _ hj _ _).trans (congrArg₂ (· * ·) (gs_res _ y _ hj _) (gs_res _ y _ hj _))
    rw [mem_nonzeroLocus_iff_isUnit (DVR.mulSec L φ ε φ' ε' s s') hj, Opens.mem_inf,
      mem_nonzeroLocus_iff_isUnit s h₁, mem_nonzeroLocus_iff_isUnit s' h₂]
    exact (congrArg IsUnit e).to_iff.trans IsUnit.mul_iff
  constructor
  · intro hy
    obtain ⟨j, hj⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key j hj).1 hy
  · intro hy
    obtain ⟨j₁, hj₁⟩ := exists_chart_of_mem_nonzeroLocus (Opens.mem_inf.1 hy).1
    obtain ⟨j₂, hj₂⟩ := exists_chart_of_mem_nonzeroLocus (Opens.mem_inf.1 hy).2
    refine (key (Sum.elim j₁ j₂) (Set.mem_iInter.2 fun k => ?_)).2 hy
    cases k with
    | inl k => exact Set.mem_iInter.1 hj₁ k
    | inr k => exact Set.mem_iInter.1 hj₂ k

end Pull

section Pow

variable {L : LB X} {l m n : ℕ}

abbrev powChart (L : LB X) (J : PUnit → L.ι) : X.Opens := LB.wchart L (fun _ : PUnit => 𝟙 X) J

theorem mem_powChart {J : PUnit → L.ι} {x : X} : x ∈ powChart L J ↔ x ∈ L.U (J PUnit.unit) := ⟨fun h => Set.mem_iInter.1 h PUnit.unit, fun h => Set.mem_iInter.2 fun _ => h⟩

theorem powChart_eq (J : PUnit → L.ι) : powChart L J = L.U (J PUnit.unit) := SetLike.ext fun _ => mem_powChart

theorem isLB_lbPow (hL : L.IsLB) (n : ℕ) : (lbPow L n).IsLB := LB.isLB_linComb hL _ _

theorem gm_lbPow_g (n : ℕ) (r : Z ⟶ X) (z : Z) (J J' : PUnit → L.ι) (hJ : r z ∈ powChart L J)
    (hJ' : r z ∈ powChart L J') :
    gm r z ((lbPow L n).U J ⊓ (lbPow L n).U J') ((lbPow L n).g J J') =
      gm r z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit)) ^ n := by
  refine (gm_linComb L _ _ r z J J' hJ hJ').trans ?_
  simp only [Fintype.prod_unique, Category.comp_id, zpow_natCast]

def powFn (s : (lbPow L n).Sec) (J : PUnit → L.ι) : Γ(X, powChart L J) := s.f J

theorem gs_powFn_compat (s : (lbPow L n).Sec) (r : Z ⟶ X) (z : Z) (J J' : PUnit → L.ι) (hJ : r z ∈ powChart L J)
    (hJ' : r z ∈ powChart L J') :
    gs r z _ (powFn s J) =
      (gm r z (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit))).val ^ n *
        gs r z _ (powFn s J') := by
  have e := gs_compat s r z hJ hJ'
  rw [gm_lbPow_g n r z J J' hJ hJ', Units.val_pow_eq_pow_val] at e
  exact e

def powSecOfGerm (n : ℕ) (f : ∀ J : PUnit → L.ι, Γ(X, powChart L J))
    (h : ∀ (y : X) (J J' : PUnit → L.ι), y ∈ powChart L J → y ∈ powChart L J' → gs (𝟙 X) y _ (f J) =
      (gm (𝟙 X) y (L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit)) (L.g (J PUnit.unit) (J' PUnit.unit))).val ^ n *
        gs (𝟙 X) y _ (f J')) : (lbPow L n).Sec :=
  secOfGerm (M := lbPow L n) f fun y J J' hJ hJ' => by
    rw [gm_lbPow_g n (𝟙 X) y J J' hJ hJ', Units.val_pow_eq_pow_val]
    exact h y J J' hJ hJ'

theorem mem_nonzeroLocus_iff_powFn (s : (lbPow L n).Sec) {y : X} {J : PUnit → L.ι} (hJ : y ∈ powChart L J) :
    y ∈ nonzeroLocus s ↔ IsUnit (gs (𝟙 X) y _ (powFn s J)) := mem_nonzeroLocus_iff_isUnit s hJ

theorem nonzeroLocus_pow_eq_of (s : (lbPow L n).Sec) (W : X.Opens) (hW : ∀ y ∈ W, ∃ J, y ∈ powChart L J)
    (h : ∀ (y : X) J, y ∈ powChart L J → (IsUnit (gs (𝟙 X) y _ (powFn s J)) ↔ y ∈ W)) : nonzeroLocus s = W := nonzeroLocus_eq_of s W hW h

def secMul (s : (lbPow L m).Sec) (t : (lbPow L n).Sec) : (lbPow L (m + n)).Sec :=
  powSecOfGerm (m + n) (fun J => powFn s J * powFn t J) fun y J J' hJ hJ' => by
    rw [gs_mul _ y _ hJ, gs_mul _ y _ hJ', gs_powFn_compat s (𝟙 X) y J J' hJ hJ',
      gs_powFn_compat t (𝟙 X) y J J' hJ hJ']
    ring

@[simp] theorem powFn_secMul (s : (lbPow L m).Sec) (t : (lbPow L n).Sec) (J : PUnit → L.ι) :
    powFn (secMul s t) J = powFn s J * powFn t J := rfl

theorem nonzeroLocus_secMul (s : (lbPow L m).Sec) (t : (lbPow L n).Sec) :
    nonzeroLocus (secMul s t) = nonzeroLocus s ⊓ nonzeroLocus t := by
  refine SetLike.ext fun y => ?_
  have key : ∀ J, y ∈ powChart L J → (y ∈ nonzeroLocus (secMul s t) ↔ y ∈ nonzeroLocus s ⊓ nonzeroLocus t) :=
    fun J hJ => by
      rw [mem_nonzeroLocus_iff_powFn _ hJ, powFn_secMul, gs_mul _ y _ hJ, IsUnit.mul_iff, Opens.mem_inf,
        mem_nonzeroLocus_iff_powFn s hJ, mem_nonzeroLocus_iff_powFn t hJ]
  constructor
  · intro hy
    obtain ⟨J, hJ⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key J hJ).1 hy
  · intro hy
    obtain ⟨J, hJ⟩ := exists_chart_of_mem_nonzeroLocus (Opens.mem_inf.1 hy).1
    exact (key J hJ).2 hy

def secPow (s : (lbPow L m).Sec) (k : ℕ) : (lbPow L (m * k)).Sec :=
  powSecOfGerm (m * k) (fun J => powFn s J ^ k) fun y J J' hJ hJ' => by
    rw [gs_pow _ y _ hJ, gs_pow _ y _ hJ', gs_powFn_compat s (𝟙 X) y J J' hJ hJ']
    ring

@[simp] theorem powFn_secPow (s : (lbPow L m).Sec) (k : ℕ) (J : PUnit → L.ι) :
    powFn (secPow s k) J = powFn s J ^ k := rfl

theorem nonzeroLocus_secPow (s : (lbPow L m).Sec) {k : ℕ} (hk : 1 ≤ k) : nonzeroLocus (secPow s k) = nonzeroLocus s := by
  refine SetLike.ext fun y => ?_
  have key : ∀ J, y ∈ powChart L J → (y ∈ nonzeroLocus (secPow s k) ↔ y ∈ nonzeroLocus s) := fun J hJ => by
    rw [mem_nonzeroLocus_iff_powFn _ hJ, mem_nonzeroLocus_iff_powFn s hJ, powFn_secPow, gs_pow _ y _ hJ,
      isUnit_pow_iff (by omega)]
  constructor
  · intro hy
    obtain ⟨J, hJ⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key J hJ).1 hy
  · intro hy
    obtain ⟨J, hJ⟩ := exists_chart_of_mem_nonzeroLocus hy
    exact (key J hJ).2 hy

def secCast (h : m = n) (s : (lbPow L m).Sec) : (lbPow L n).Sec :=
  powSecOfGerm n (powFn s) fun y J J' hJ hJ' => h ▸ gs_powFn_compat s (𝟙 X) y J J' hJ hJ'

@[simp] theorem powFn_secCast (h : m = n) (s : (lbPow L m).Sec) (J : PUnit → L.ι) :
    powFn (secCast h s) J = powFn s J := rfl

theorem nonzeroLocus_secCast (h : m = n) (s : (lbPow L m).Sec) : nonzeroLocus (secCast h s) = nonzeroLocus s := rfl

def secOfFn (L : LB X) (c : Γ(X, ⊤)) : (lbPow L 0).Sec :=
  powSecOfGerm 0 (fun _ => resG X le_top c) fun y J J' hJ hJ' => by
    rw [gs_res _ y _ hJ, gs_res _ y _ hJ', pow_zero, one_mul]

@[simp] theorem powFn_secOfFn (c : Γ(X, ⊤)) (J : PUnit → L.ι) : powFn (secOfFn L c) J = resG X le_top c := rfl

theorem nonzeroLocus_secOfFn (hL : L.IsLB) (c : Γ(X, ⊤)) : nonzeroLocus (secOfFn L c) = X.basicOpen c := by
  refine nonzeroLocus_pow_eq_of _ _ (fun y _ => ?_) fun y J hJ => ?_
  · obtain ⟨i, hi⟩ := exists_chart hL y
    exact ⟨fun _ => i, mem_powChart.2 hi⟩
  · rw [powFn_secOfFn, gs_res _ y le_top hJ, isUnit_gs_iff (𝟙 X) y ⊤ (by simp) c]
    exact Iff.rfl

def powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i))
    (h : ∀ i j, resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (f i) =
      (L.g i j).val ^ n * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (f j)) : (lbPow L n).Sec :=
  powSecOfGerm n (fun J => resG X (powChart_eq J).le (f (J PUnit.unit))) fun y J J' hJ hJ' => by
    have hy : y ∈ L.U (J PUnit.unit) ⊓ L.U (J' PUnit.unit) := ⟨mem_powChart.1 hJ, mem_powChart.1 hJ'⟩
    have e := congrArg (gs (𝟙 X) y _) (h (J PUnit.unit) (J' PUnit.unit))
    rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
    rw [gs_res _ y _ hJ, gs_res _ y _ hJ', e]

@[simp] theorem powFn_powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i)) (h) (J : PUnit → L.ι) :
    powFn (powSecMk n f h) J = resG X (powChart_eq J).le (f (J PUnit.unit)) := rfl

theorem nonzeroLocus_powSecMk (n : ℕ) (f : ∀ i, Γ(X, L.U i)) (h) :
    nonzeroLocus (powSecMk n f h) = ⨆ i, X.basicOpen (f i) := by
  refine nonzeroLocus_pow_eq_of _ _ (fun y hy => ?_) fun y J hJ => ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 hy
    exact ⟨fun _ => i, mem_powChart.2 (X.basicOpen_le _ hi)⟩
  · rw [powFn_powSecMk, gs_res _ y _ hJ, isUnit_gs_iff (𝟙 X) y _ (mem_powChart.1 hJ), Opens.mem_iSup]
    constructor
    · exact fun hy => ⟨_, hy⟩
    · rintro ⟨i, hi⟩
      have hy : y ∈ L.U i ⊓ L.U (J PUnit.unit) := ⟨X.basicOpen_le _ hi, mem_powChart.1 hJ⟩
      have e := congrArg (gs (𝟙 X) y _) (h i (J PUnit.unit))
      rw [gs_res _ y _ hy, gs_mul _ y _ hy, gs_res _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy] at e
      have hu := (isUnit_gs_iff (𝟙 X) y _ hy.1 (f i)).2 hi
      rw [e] at hu
      exact (isUnit_gs_iff (𝟙 X) y _ hy.2 _).1 (IsUnit.mul_iff.1 hu).2

def powSecFn (s : (lbPow L n).Sec) (i : L.ι) : Γ(X, L.U i) :=
  resG X (powChart_eq (fun _ => i)).ge (powFn s fun _ => i)

theorem powSecFn_compat (s : (lbPow L n).Sec) (i j : L.ι) :
    resG X (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (powSecFn s i) =
      (L.g i j).val ^ n * resG X (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (powSecFn s j) := fn_ext fun y hy => by
  have hi : y ∈ powChart L (fun _ => i) := mem_powChart.2 hy.1
  have hj : y ∈ powChart L (fun _ => j) := mem_powChart.2 hy.2
  rw [gs_mul _ y _ hy, gs_pow _ y _ hy, gs_unit _ y _ hy, gs_res _ y _ hy, gs_res _ y _ hy]
  unfold powSecFn
  rw [gs_res _ y _ hy.1, gs_res _ y _ hy.2]
  exact gs_powFn_compat s (𝟙 X) y _ _ hi hj

theorem nonzeroLocus_inf_powSecFn (s : (lbPow L n).Sec) (i : L.ι) :
    nonzeroLocus s ⊓ L.U i = X.basicOpen (powSecFn s i) := by
  refine SetLike.ext fun y => ?_
  rw [Opens.mem_inf]
  constructor
  · rintro ⟨hs, hy⟩
    refine (isUnit_gs_iff (𝟙 X) y _ hy (powSecFn s i)).1 ?_
    unfold powSecFn
    rw [gs_res _ y _ hy]
    exact (mem_nonzeroLocus_iff_powFn s (mem_powChart.2 hy)).1 hs
  · intro hy
    have hU : y ∈ L.U i := X.basicOpen_le _ hy
    refine ⟨?_, hU⟩
    rw [mem_nonzeroLocus_iff_powFn s (J := fun _ => i) (mem_powChart.2 hU)]
    have hu := (isUnit_gs_iff (𝟙 X) y _ hU (powSecFn s i)).2 hy
    unfold powSecFn at hu
    rwa [gs_res _ y _ hU] at hu

def secToPow (s : L.Sec) (n : ℕ) : (lbPow L n).Sec :=
  powSecMk n (fun i => s.f i ^ n) fun i j => by
    rw [map_pow, map_pow, ← mul_pow]
    exact congrArg (· ^ n) (s.compat i j)

theorem nonzeroLocus_secToPow (s : L.Sec) (hn : 1 ≤ n) : nonzeroLocus (secToPow s n) = nonzeroLocus s := by
  unfold secToPow
  rw [nonzeroLocus_powSecMk]
  exact iSup_congr fun i => X.basicOpen_pow (s.f i) hn

def secOfPowOne (s : (lbPow L 1).Sec) : L.Sec where
  f := powSecFn s
  compat i j := (powSecFn_compat s i j).trans (by rw [pow_one])

theorem nonzeroLocus_secOfPowOne (s : (lbPow L 1).Sec) : nonzeroLocus (secOfPowOne s) = nonzeroLocus s := by
  refine SetLike.ext fun y => ?_
  change y ∈ ⨆ i, X.basicOpen (powSecFn s i) ↔ y ∈ nonzeroLocus s
  rw [Opens.mem_iSup]
  constructor
  · rintro ⟨i, hi⟩
    rw [← nonzeroLocus_inf_powSecFn] at hi
    exact (Opens.mem_inf.1 hi).1
  · intro hy
    obtain ⟨J, hJ⟩ := exists_chart_of_mem_nonzeroLocus hy
    refine ⟨J PUnit.unit, ?_⟩
    rw [← nonzeroLocus_inf_powSecFn]
    exact Opens.mem_inf.2 ⟨hy, mem_powChart.1 hJ⟩

end Pow

section PowCharts

variable {L : LB X} {m n : ℕ}

def chartPullPowPull (L : LB X) (f : Y ⟶ X) (n : ℕ) : ChartPull (lbPow (L.pull f) n) (lbPow L n) f where
  idx J := fun _ => J PUnit.unit PUnit.unit
  le _ _ hy := mem_powChart.2 (mem_pull.1 (mem_powChart.1 hy))
  g y J J' hJ hJ' := by
    have h₁ := mem_powChart.1 hJ
    have h₂ := mem_powChart.1 hJ'
    refine (gm_lbPow_g n (𝟙 Y) y J J' hJ hJ').trans (Eq.trans ?_ (gm_lbPow_g n f y _ _
      (mem_powChart.2 (mem_pull.1 h₁)) (mem_powChart.2 (mem_pull.1 h₂))).symm)
    rw [gm_pull_g L f (𝟙 Y) y _ _ h₁ h₂, Category.id_comp]

def secPowPull (s : (lbPow L n).Sec) (f : Y ⟶ X) : (lbPow (L.pull f) n).Sec := chartSec (chartPullPowPull L f n) s

theorem nonzeroLocus_secPowPull (s : (lbPow L n).Sec) (f : Y ⟶ X) :
    nonzeroLocus (secPowPull s f) = f ⁻¹ᵁ nonzeroLocus s := nonzeroLocus_chartSec _ s fun _ J hy => ⟨fun _ _ => J PUnit.unit, mem_powChart.2 (mem_pull.2 (mem_powChart.1 hy))⟩

def chartPullPowPow (L : LB X) (m n : ℕ) : ChartPull (lbPow (lbPow L m) n) (lbPow L (m * n)) (𝟙 X) where
  idx J := J PUnit.unit
  le _ _ hy := mem_powChart.1 hy
  g y J J' hJ hJ' := by
    have h₁ := mem_powChart.1 hJ
    have h₂ := mem_powChart.1 hJ'
    refine (gm_lbPow_g n (𝟙 X) y J J' hJ hJ').trans (Eq.trans ?_ (gm_lbPow_g (m * n) (𝟙 X) y _ _ h₁ h₂).symm)
    rw [gm_lbPow_g m (𝟙 X) y _ _ h₁ h₂, pow_mul]

def chartPullPowMul (L : LB X) (m n : ℕ) : ChartPull (lbPow L (m * n)) (lbPow (lbPow L m) n) (𝟙 X) where
  idx J := fun _ => J
  le _ _ hy := mem_powChart.2 hy
  g y J J' hJ hJ' := by
    refine (gm_lbPow_g (m * n) (𝟙 X) y J J' hJ hJ').trans (Eq.trans ?_ (gm_lbPow_g (L := lbPow L m) n (𝟙 X) y
      (fun _ => J) (fun _ => J') (mem_powChart.2 hJ) (mem_powChart.2 hJ')).symm)
    rw [gm_lbPow_g m (𝟙 X) y _ _ hJ hJ', pow_mul]

def secToPowPow (s : (lbPow L (m * n)).Sec) : (lbPow (lbPow L m) n).Sec := chartSec (chartPullPowPow L m n) s

def secOfPowPow (s : (lbPow (lbPow L m) n).Sec) : (lbPow L (m * n)).Sec := chartSec (chartPullPowMul L m n) s

theorem nonzeroLocus_secToPowPow (s : (lbPow L (m * n)).Sec) : nonzeroLocus (secToPowPow s) = nonzeroLocus s := nonzeroLocus_chartSec_id _ s fun _ j hy => ⟨fun _ => j, mem_powChart.2 hy⟩

theorem nonzeroLocus_secOfPowPow (s : (lbPow (lbPow L m) n).Sec) : nonzeroLocus (secOfPowPow s) = nonzeroLocus s := nonzeroLocus_chartSec_id _ s fun _ j hy => ⟨j PUnit.unit, mem_powChart.1 hy⟩

def chartPullPowOne (L : LB X) : ChartPull (lbPow L 1) L (𝟙 X) where
  idx J := J PUnit.unit
  le _ _ hy := mem_powChart.1 hy
  g y J J' hJ hJ' := (gm_lbPow_g 1 (𝟙 X) y J J' hJ hJ').trans (pow_one _)

def chartPullPowFin (L : LB X) (f : Y ⟶ X) (n : ℕ) :
    ChartPull (lbPow (L.pull f) n) (LB.LinComb L (K := Fin n) (fun _ => f) (fun _ => 1)) (𝟙 Y) where
  idx J := fun _ => J PUnit.unit PUnit.unit
  le _ _ hy := Set.mem_iInter.2 fun _ => mem_pull.1 (mem_powChart.1 hy)
  g y J J' hJ hJ' := by
    have h₁ := mem_powChart.1 hJ
    have h₂ := mem_powChart.1 hJ'
    refine (gm_lbPow_g n (𝟙 Y) y J J' hJ hJ').trans (Eq.trans ?_ (gm_linComb L (fun _ : Fin n => f) (fun _ => 1)
      (𝟙 Y) y _ _ (Set.mem_iInter.2 fun _ => mem_pull.1 h₁) (Set.mem_iInter.2 fun _ => mem_pull.1 h₂)).symm)
    rw [gm_pull_g L f (𝟙 Y) y _ _ h₁ h₂, Finset.prod_const, Finset.card_univ, Fintype.card_fin, zpow_one]

def secOfFinPow {f : Y ⟶ X} (s : (LB.LinComb L (K := Fin n) (fun _ => f) (fun _ => 1)).Sec) :
    (lbPow (L.pull f) n).Sec := chartSec (chartPullPowFin L f n) s

theorem nonzeroLocus_secOfFinPow {f : Y ⟶ X} (hn : 1 ≤ n)
    (s : (LB.LinComb L (K := Fin n) (fun _ => f) (fun _ => 1)).Sec) :
    nonzeroLocus (secOfFinPow s) = nonzeroLocus s := nonzeroLocus_chartSec_id _ s fun _ j hy => ⟨fun _ _ => j ⟨0, hn⟩, mem_powChart.2 (mem_pull.2 (Set.mem_iInter.1 hy ⟨0, hn⟩))⟩

theorem lbIso_lbPow_one (hL : L.IsLB) : LBIso (lbPow L 1) L := lbIso_of_chartPull (chartPullPowOne L) hL

theorem lbIso_lbPow_lbPow (hL : L.IsLB) (m n : ℕ) : LBIso (lbPow (lbPow L m) n) (lbPow L (m * n)) := lbIso_of_chartPull (chartPullPowPow L m n) (isLB_lbPow hL _)

theorem lbIso_lbPow_pull (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) : LBIso (lbPow (L.pull f) n) ((lbPow L n).pull f) := by
  have le : ∀ J : PUnit → (L.pull f).ι,
      (lbPow (L.pull f) n).U J ≤ (𝟙 Y) ⁻¹ᵁ ((lbPow L n).pull f).U (fun _ _ => J PUnit.unit PUnit.unit) :=
    fun J y hy => mem_pull.2 (mem_powChart.2 (mem_pull.1 (mem_powChart.1 hy)))
  have cp : ChartPull (lbPow (L.pull f) n) ((lbPow L n).pull f) (𝟙 Y) :=
    { idx := fun J _ _ => J PUnit.unit PUnit.unit
      le := le
      g := fun y J J' hJ hJ' => by
        have h₁ : (𝟙 Y ≫ f) y ∈ L.U (J PUnit.unit PUnit.unit) := mem_pull.1 (mem_powChart.1 hJ)
        have h₂ : (𝟙 Y ≫ f) y ∈ L.U (J' PUnit.unit PUnit.unit) := mem_pull.1 (mem_powChart.1 hJ')
        rw [gm_lbPow_g n (𝟙 Y) y J J' hJ hJ', gm_pull_g L f (𝟙 Y) y _ _ (mem_powChart.1 hJ) (mem_powChart.1 hJ'),
          gm_pull_g (lbPow L n) f (𝟙 Y) y _ _ (le J hJ) (le J' hJ'),
          gm_lbPow_g n (𝟙 Y ≫ f) y _ _ (mem_powChart.2 h₁) (mem_powChart.2 h₂)] }
  exact lbIso_of_chartPull cp (pull_isLB (isLB_lbPow hL n) f)

theorem lbIso_lbPow_finPow (hL : L.IsLB) (f : Y ⟶ X) (n : ℕ) :
    LBIso (lbPow (L.pull f) n) (LB.LinComb L (K := Fin n) (fun _ => f) (fun _ => 1)) := lbIso_of_chartPull (chartPullPowFin L f n) (LB.isLB_linComb hL _ _)

private theorem lbIso_lbPow_lemma {M : LB X} (n : ℕ) (P₁ Q₁ : PUnit → M.ι) (P₂ Q₂ : PUnit → L.ι)
    (uP : Γ(X, M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit))ˣ) (uQ : Γ(X, M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit))ˣ)
    (hu : res (inf_le_left : M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit) ⊓ (M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) ≤
          M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit)) uP =
        res (inf_le_inf inf_le_left inf_le_left : M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit) ⊓
            (M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) ≤ M.U (P₁ PUnit.unit) ⊓ M.U (Q₁ PUnit.unit))
          (M.g (P₁ PUnit.unit) (Q₁ PUnit.unit)) *
          (res (inf_le_inf inf_le_right inf_le_right : M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit) ⊓
            (M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) ≤ L.U (P₂ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit))
            (L.g (P₂ PUnit.unit) (Q₂ PUnit.unit)))⁻¹ *
        res (inf_le_right : M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit) ⊓ (M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) ≤
          M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) uQ)
    (leP : (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ ≤ M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit))
    (leQ : (lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂ ≤ M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) :
    res (inf_le_left : (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ ⊓ ((lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂) ≤
        (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂) (res leP uP ^ n) =
      res (inf_le_inf inf_le_left inf_le_left : (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ ⊓
          ((lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂) ≤ (lbPow M n).U P₁ ⊓ (lbPow M n).U Q₁) ((lbPow M n).g P₁ Q₁) *
        (res (inf_le_inf inf_le_right inf_le_right : (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ ⊓
          ((lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂) ≤ (lbPow L n).U P₂ ⊓ (lbPow L n).U Q₂) ((lbPow L n).g P₂ Q₂))⁻¹ *
      res (inf_le_right : (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ ⊓ ((lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂) ≤
        (lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂) (res leQ uQ ^ n) := by
  refine unit_ext fun y hy => ?_
  have hy₁ : y ∈ (lbPow M n).U P₁ ⊓ (lbPow L n).U P₂ := hy.1
  have hy₂ : y ∈ (lbPow M n).U Q₁ ⊓ (lbPow L n).U Q₂ := hy.2
  have hPQ : y ∈ M.U (P₁ PUnit.unit) ⊓ L.U (P₂ PUnit.unit) ⊓ (M.U (Q₁ PUnit.unit) ⊓ L.U (Q₂ PUnit.unit)) :=
    ⟨leP hy₁, leQ hy₂⟩
  have hM₁ : y ∈ (lbPow M n).U P₁ := hy₁.1
  have hM₂ : y ∈ (lbPow M n).U Q₁ := hy₂.1
  have hL₁ : y ∈ (lbPow L n).U P₂ := hy₁.2
  have hL₂ : y ∈ (lbPow L n).U Q₂ := hy₂.2
  have e := congrArg (gm (𝟙 X) y _) hu
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 X) y _ hPQ, gm_res (𝟙 X) y _ hPQ, gm_res (𝟙 X) y _ hPQ,
    gm_res (𝟙 X) y _ hPQ] at e
  rw [map_mul, map_mul, map_inv, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy, gm_res (𝟙 X) y _ hy,
    gm_res (𝟙 X) y _ hy, map_pow, map_pow, gm_res (𝟙 X) y _ hy₁, gm_res (𝟙 X) y _ hy₂,
    gm_lbPow_g n (𝟙 X) y P₁ Q₁ hM₁ hM₂, gm_lbPow_g n (𝟙 X) y P₂ Q₂ hL₁ hL₂, e, mul_pow, mul_pow, inv_pow]

theorem lbIso_lbPow {M : LB X} (H : LBIso L M) (n : ℕ) : LBIso (lbPow L n) (lbPow M n) := by
  obtain ⟨w, hw⟩ := H
  have le : ∀ P : (PUnit → M.ι) × (PUnit → L.ι),
      (lbPow M n).U P.1 ⊓ (lbPow L n).U P.2 ≤ M.U (P.1 PUnit.unit) ⊓ L.U (P.2 PUnit.unit) :=
    fun P y hy => ⟨mem_powChart.1 hy.1, mem_powChart.1 hy.2⟩
  exact ⟨⟨fun P => res (le P) (w.s (P.1 PUnit.unit, P.2 PUnit.unit)) ^ n⟩, fun P Q =>
    lbIso_lbPow_lemma n P.1 Q.1 P.2 Q.2 (w.s (P.1 PUnit.unit, P.2 PUnit.unit)) (w.s (Q.1 PUnit.unit, Q.2 PUnit.unit))
      (hw (P.1 PUnit.unit, P.2 PUnit.unit) (Q.1 PUnit.unit, Q.2 PUnit.unit)) (le P) (le Q)⟩

end PowCharts

end GlobalTheory
