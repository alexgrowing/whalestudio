import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HypLattice

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E]

omit [NumberField E] in

theorem star_mem_int {x : E} (h : x ∈ (algebraMap (𝓞 E) E).range) : star x ∈ (algebraMap (𝓞 E) E).range := by
  obtain ⟨b, rfl⟩ := h
  have hb : IsIntegral ℤ (algebraMap (𝓞 E) E b) := b.isIntegral_coe
  have := hb.map (starRingEnd E).toIntAlgHom
  exact ⟨⟨_, this⟩, rfl⟩

omit [NumberField E] [StarRing E] in
theorem mem_one_iff_range {x : E} :
    x ∈ (1 : FractionalIdeal (𝓞 E)⁰ E) ↔ x ∈ (algebraMap (𝓞 E) E).range := by
  rw [FractionalIdeal.mem_one_iff]; rfl

theorem star_mem_pow {I : FractionalIdeal (𝓞 E)⁰ E} (hI : ∀ x ∈ I, star x ∈ I) (n : ℕ) :
    ∀ x ∈ I ^ n, star x ∈ I ^ n := by
  induction n with
  | zero =>
    intro x hx
    rw [pow_zero, mem_one_iff_range] at *
    exact star_mem_int hx
  | succ n ih =>
    intro x hx
    rw [pow_succ] at *
    refine FractionalIdeal.mul_induction_on hx (fun a ha b hb => ?_) (fun a b ha hb => ?_)
    · rw [star_mul']
      exact FractionalIdeal.mul_mem_mul (ih a ha) (hI b hb)
    · rw [star_add]
      exact (I ^ n * I).1.add_mem ha hb

theorem star_mem_inv {I : FractionalIdeal (𝓞 E)⁰ E} (h0 : I ≠ 0) (hI : ∀ x ∈ I, star x ∈ I) :
    ∀ x ∈ I⁻¹, star x ∈ I⁻¹ := by
  intro x hx
  rw [FractionalIdeal.mem_inv_iff h0] at *
  intro y hy
  have := star_mem_int (mem_one_iff_range.1 (hx _ (hI y hy)))
  rw [star_mul', star_star] at this
  exact mem_one_iff_range.2 this

def idealSum (Y : HSpace E) {ρ : ℕ} (v : Fin ρ → Y.V) (J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) :
    Submodule (𝓞 E) Y.V :=
  ⨆ i : Fin ρ, (J i : Submodule (𝓞 E) E).map ((LinearMap.toSpanSingleton E Y.V (v i)).restrictScalars (𝓞 E))

variable {Y : HSpace E} {ρ : ℕ}

theorem smul_mem_idealSum (v : Fin ρ → Y.V) {J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E} (i : Fin ρ) {a : E}
    (ha : a ∈ J i) : a • v i ∈ idealSum Y v J :=
  Submodule.mem_iSup_of_mem i ⟨a, ha, rfl⟩

theorem mem_idealSum {v : Fin ρ → Y.V} {J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E} {y : Y.V} :
    y ∈ idealSum Y v J ↔ ∃ β : Fin ρ → E, (∀ i, β i ∈ J i) ∧ y = ∑ i, β i • v i := by
  constructor
  · intro hy
    refine Submodule.iSup_induction _ (motive := fun y => ∃ β : Fin ρ → E, (∀ i, β i ∈ J i) ∧ y = ∑ i, β i • v i)
      hy ?_ ?_ ?_
    · rintro i x ⟨a, ha, rfl⟩
      refine ⟨Pi.single i a, fun j => ?_, ?_⟩
      · by_cases h : j = i
        · subst h; simpa using ha
        · rw [Pi.single_eq_of_ne h]; exact (J j).zero_mem
      · rw [Finset.sum_eq_single i (fun j _ h => by rw [Pi.single_eq_of_ne h, zero_smul]) (by simp)]
        simp
    · exact ⟨0, fun i => (J i).zero_mem, by simp⟩
    · rintro x y ⟨β, hβ, rfl⟩ ⟨γ, hγ, rfl⟩
      refine ⟨β + γ, fun i => (J i).1.add_mem (hβ i) (hγ i), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
  · rintro ⟨β, hβ, rfl⟩
    exact Submodule.sum_mem _ fun i _ => smul_mem_idealSum v i (hβ i)

theorem fg_idealSum (v : Fin ρ → Y.V) (J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E) : (idealSum Y v J).FG :=
  Submodule.fg_iSup _ fun i => (FractionalIdeal.fg_of_isNoetherianRing le_rfl (J i)).map _

theorem mem_span_idealSum (v : Fin ρ → Y.V) {J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E} (hJ : ∀ i, J i ≠ 0) (i : Fin ρ) :
    v i ∈ Submodule.span E (idealSum Y v J : Set Y.V) := by
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ J i, a ≠ 0 := by
    by_contra h
    push Not at h
    exact hJ i (FractionalIdeal.eq_zero_iff.2 h)
  have := Submodule.smul_mem _ a⁻¹ (Submodule.subset_span (R := E) (smul_mem_idealSum v i ha))
  rwa [smul_smul, inv_mul_cancel₀ ha0, one_smul] at this

theorem hT_swap (Y : HSpace E) (x y : Y.V) : Y.hT x y = star (Y.hT y x) := (Y.herm.eq y x).symm

structure IsHyp (Y : HSpace E) (U : Submodule E Y.V) (e f : Fin ρ → Y.V) : Prop where
  ee : ∀ i j, Y.hT (e i) (e j) = 0
  ff : ∀ i j, Y.hT (f i) (f j) = 0
  fe : ∀ i j, Y.hT (f i) (e j) = if i = j then 1 else 0
  mem : ∀ y, y ∈ U ↔ ∀ i, Y.hT (e i) y = 0 ∧ Y.hT (f i) y = 0

variable {U : Submodule E Y.V} {e f : Fin ρ → Y.V}

theorem hT_ef (fe : ∀ i j, Y.hT (f i) (e j) = if i = j then 1 else 0) (i j : Fin ρ) :
    Y.hT (e i) (f j) = if i = j then 1 else 0 := by
  rw [hT_swap, fe]
  by_cases h : i = j
  · simp [h]
  · simp [h, Ne.symm h]

theorem IsHyp.proj_mem (H : IsHyp Y U e f) (y : Y.V) :
    y - ∑ i, Y.hT (f i) y • e i - ∑ i, Y.hT (e i) y • f i ∈ U := by
  rw [H.mem]
  intro i
  simp [map_sum, H.ee, H.ff, H.fe, hT_ef H.fe]

theorem IsHyp.pairing (H : IsHyp Y U e f) (β γ β' γ' : Fin ρ → E) {w w' : Y.V} (hw : w ∈ U) (hw' : w' ∈ U) :
    Y.hT (∑ i, β' i • e i + w' + ∑ i, γ' i • f i) (∑ i, β i • e i + w + ∑ i, γ i • f i) =
      ∑ i, star (β' i) * γ i + Y.hT w' w + ∑ i, star (γ' i) * β i := by
  have h1 : ∀ i, Y.hT (e i) w = 0 := fun i => ((H.mem w).1 hw i).1
  have h2 : ∀ i, Y.hT (f i) w = 0 := fun i => ((H.mem w).1 hw i).2
  have h3 : ∀ i, Y.hT w' (e i) = 0 := fun i => by rw [hT_swap, ((H.mem w').1 hw' i).1, star_zero]
  have h4 : ∀ i, Y.hT w' (f i) = 0 := fun i => by rw [hT_swap, ((H.mem w').1 hw' i).2, star_zero]
  simp [map_sum, LinearMap.sum_apply, H.ee, H.ff, H.fe, hT_ef H.fe, h1, h2, h3, h4, mul_comm, starRingEnd_apply]

theorem IsHyp.selfDual (H : IsHyp Y U e f) {L : Submodule (𝓞 E) Y.V} (hfg : L.FG)
    (hsp : Submodule.span E (L : Set Y.V) = U)
    (hL : ∀ y ∈ U, y ∈ L ↔ ∀ x ∈ L, Y.hD x y ∈ (algebraMap (𝓞 E) E).range)
    {J : Fin ρ → FractionalIdeal (𝓞 E)⁰ E} (hJ0 : ∀ i, J i ≠ 0) (hJ : ∀ i, ∀ x ∈ J i, star x ∈ J i) :
    Submodule.IsLattice E (idealSum Y e J ⊔ L ⊔ idealSum Y f fun i => (J i)⁻¹) ∧
      ∀ y, y ∈ (idealSum Y e J ⊔ L ⊔ idealSum Y f fun i => (J i)⁻¹) ↔
        ∀ x ∈ (idealSum Y e J ⊔ L ⊔ idealSum Y f fun i => (J i)⁻¹), Y.hT x y ∈ (algebraMap (𝓞 E) E).range := by
  have hLU : ∀ x ∈ L, x ∈ U := fun x hx => hsp ▸ Submodule.subset_span hx
  have hdec : ∀ y : Y.V, y = ∑ i, Y.hT (f i) y • e i + (y - ∑ i, Y.hT (f i) y • e i - ∑ i, Y.hT (e i) y • f i) +
      ∑ i, Y.hT (e i) y • f i := fun y => by abel
  have hmem : ∀ y, y ∈ (idealSum Y e J ⊔ L ⊔ idealSum Y f fun i => (J i)⁻¹) →
      ∃ β γ : Fin ρ → E, ∃ w ∈ L, (∀ i, β i ∈ J i) ∧ (∀ i, γ i ∈ (J i)⁻¹) ∧
        y = ∑ i, β i • e i + w + ∑ i, γ i • f i := by
    intro y hy
    obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨b, hb, w, hw, rfl⟩ := Submodule.mem_sup.1 ha
    obtain ⟨β, hβ, rfl⟩ := mem_idealSum.1 hb
    obtain ⟨γ, hγ, rfl⟩ := mem_idealSum.1 hc
    exact ⟨β, γ, w, hw, hβ, hγ, rfl⟩
  refine ⟨⟨((fg_idealSum e J).sup hfg).sup (fg_idealSum f _), ?_⟩, fun y => ⟨fun hy x hx => ?_, fun hy => ?_⟩⟩
  · rw [eq_top_iff]
    intro y _
    rw [hdec y]
    refine add_mem (add_mem (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_) ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 (le_sup_left.trans le_sup_left)) (mem_span_idealSum e hJ0 i)
    · have := H.proj_mem y
      rw [← hsp] at this
      exact Submodule.span_mono (SetLike.coe_subset_coe.2 (le_sup_right.trans le_sup_left)) this
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_right)
        (mem_span_idealSum f (fun i => inv_ne_zero (hJ0 i)) i)
  · obtain ⟨β, γ, w, hw, hβ, hγ, rfl⟩ := hmem y hy
    obtain ⟨β', γ', w', hw', hβ', hγ', rfl⟩ := hmem x hx
    rw [H.pairing β γ β' γ' (hLU w hw) (hLU w' hw')]
    refine add_mem (add_mem (sum_mem fun i _ => ?_) ?_) (sum_mem fun i _ => ?_)
    · rw [mul_comm]
      exact mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff (hJ0 i)).1 (hγ i) _ (hJ i _ (hβ' i)))
    · exact (hL w' (hLU w' hw')).1 hw' w hw
    · exact mem_one_iff_range.1 ((FractionalIdeal.mem_inv_iff (hJ0 i)).1
        (star_mem_inv (hJ0 i) (hJ i) _ (hγ' i)) _ (hβ i))
  · rw [hdec y]
    refine add_mem (Submodule.mem_sup_left (add_mem (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right ?_)))
      (Submodule.mem_sup_right ?_)
    · refine mem_idealSum.2 ⟨_, fun i => ?_, rfl⟩
      rw [← inv_inv (J i), FractionalIdeal.mem_inv_iff (inv_ne_zero (hJ0 i))]
      intro a ha
      have := hy (star a • f i) (Submodule.mem_sup_right
        (smul_mem_idealSum f (J := fun i => (J i)⁻¹) i (star_mem_inv (hJ0 i) (hJ i) _ ha)))
      rw [mem_one_iff_range, mul_comm]
      simpa only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul] using this
    · rw [hL _ (H.proj_mem y)]
      intro x hx
      have := star_mem_int (hy x (Submodule.mem_sup_left (Submodule.mem_sup_right hx)))
      have h1 : ∀ i, Y.hT (e i) x = 0 := fun i => ((H.mem x).1 (hLU x hx) i).1
      have h2 : ∀ i, Y.hT (f i) x = 0 := fun i => ((H.mem x).1 (hLU x hx) i).2
      rw [← hT_swap] at this
      have h3 : Y.hD x (y - ∑ i, Y.hT (f i) y • e i - ∑ i, Y.hT (e i) y • f i) = Y.hT y x := by
        simp [HSpace.hD, map_sum, LinearMap.sum_apply, h1, h2]
      rwa [h3]
    · refine mem_idealSum.2 ⟨_, fun i => ?_, rfl⟩
      rw [FractionalIdeal.mem_inv_iff (hJ0 i)]
      intro a ha
      have := hy (star a • e i) (Submodule.mem_sup_left (Submodule.mem_sup_left
        (smul_mem_idealSum e i (hJ i _ ha))))
      rw [mem_one_iff_range, mul_comm]
      simpa only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul] using this

theorem isHyp_of_finrank (ee : ∀ i j, Y.hT (e i) (e j) = 0) (ff : ∀ i j, Y.hT (f i) (f j) = 0)
    (fe : ∀ i j, Y.hT (f i) (e j) = if i = j then 1 else 0)
    (hU : ∀ y ∈ U, ∀ i, Y.hT (e i) y = 0 ∧ Y.hT (f i) y = 0)
    (hr : Y.rank ≤ Module.finrank E U + 2 * ρ) : IsHyp Y U e f := by
  let φ : Y.V →ₗ[E] (Fin ρ → E) × (Fin ρ → E) :=
    (LinearMap.pi fun i => Y.hT (e i)).prod (LinearMap.pi fun i => Y.hT (f i))
  have hk : ∀ y, y ∈ LinearMap.ker φ ↔ ∀ i, Y.hT (e i) y = 0 ∧ Y.hT (f i) y = 0 := by
    intro y
    simp [φ, LinearMap.mem_ker, funext_iff, forall_and]
  have hs : LinearMap.range φ = ⊤ := by
    rw [LinearMap.range_eq_top]
    rintro ⟨a, b⟩
    refine ⟨∑ i, b i • e i + ∑ i, a i • f i, ?_⟩
    ext i <;> simp [φ, map_sum, ee, ff, fe, hT_ef fe]
  have hd := LinearMap.finrank_range_add_finrank_ker φ
  rw [hs, finrank_top, Y.rank_eq] at hd
  simp only [Module.finrank_prod, Module.finrank_fin_fun] at hd
  have hle : U ≤ LinearMap.ker φ := fun y hy => (hk y).2 (hU y hy)
  have heq : U = LinearMap.ker φ := Submodule.eq_of_le_of_finrank_le hle (by omega)
  exact ⟨ee, ff, fe, fun y => heq ▸ hk y⟩

end General

open GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents Formalism.L2.Herm

variable {D : D7}

theorem isSelfDualC_crdLat (Y : HSp D) {Λ : Submodule (𝓞 D.host.E) Y.V} (h : Submodule.IsLattice D.host.E Λ)
    (hd : ∀ y, y ∈ Λ ↔ ∀ x ∈ Λ, Y.hT x y ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    Formalism.IndefR.Datum.IsSelfDualC Y (crdLat Y Λ) := by
  have hm : ∀ y, crd Y y ∈ crdLat Y Λ ↔ y ∈ Λ := fun y =>
    ⟨fun ⟨x, hx, hxy⟩ => (crd Y).injective hxy ▸ hx, fun hy => ⟨y, hy, rfl⟩⟩
  refine ⟨⟨h.fg.map _, ?_⟩, fun y => ?_⟩
  · have h1 : (crdLat Y Λ : Set (Fin Y.rank → D.host.E)) = Y.frame.equivFun.toLinearMap '' (Λ : Set Y.V) := rfl
    rw [h1, ← Submodule.map_span, h.span_eq_top, Submodule.map_top, LinearEquiv.range]
  · obtain ⟨y, rfl⟩ := (crd Y).surjective y
    rw [hm, hd]
    constructor
    · rintro H _ ⟨x, hx, rfl⟩
      obtain ⟨b, hb⟩ := H x hx
      exact ⟨b, hb.trans (hT_crd D.sp.cm Y x y)⟩
    · intro H x hx
      obtain ⟨b, hb⟩ := H (crd Y x) ((hm x).2 hx)
      exact ⟨b, hb.trans (hT_crd D.sp.cm Y x y).symm⟩

theorem isHyp_flatSp {Y X : HSp D} {ι : X.V →ₗ[D.host.E] Y.V} {z : Y.V} {ρ : ℕ} {e f : Fin ρ → Y.V} {c : D.host.E}
    (hc : c ≠ 0) (H : IsDec Y X ι (fun _ : Fin 1 => z) c e f) : IsHyp Y (flatSp Y X ι z) e f := by
  refine isHyp_of_finrank (fun i j => H.ee j i) (fun i j => H.ff j i) (fun i j => ?_) (fun y hy i => ?_) ?_
  · have := H.ef j i
    rw [HSpace.hD] at this
    rw [this]
    simp only [eq_comm]
  · obtain ⟨_, ⟨x, rfl⟩, b, hb, rfl⟩ := Submodule.mem_sup.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hb
    have h1 := H.hyp_X i x
    have h2 := H.hyperbolicDecomp_hyp_orthogonal_line i 0
    simp only [HSpace.hD] at h1 h2
    simp [h1.1, h1.2, h2.1, h2.2]
  · have hinj : Function.Injective ι := by
      rw [injective_iff_map_eq_zero]
      intro x hx
      refine X.nondeg.1 x fun y => ?_
      rw [← H.isom x y, hx]
      simp
    have hlt : LinearMap.range ι < flatSp Y X ι z := by
      refine lt_of_le_of_ne le_sup_left fun h => hc ?_
      have hz : z ∈ LinearMap.range ι := h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self z)
      obtain ⟨x, hx⟩ := hz
      rw [← H.z_norm 0, ← H.z_X 0 x, hx]
    have h1 := Submodule.finrank_lt_finrank_of_lt hlt
    rw [LinearMap.finrank_range_of_inj hinj, X.rank_eq] at h1
    have := H.rank
    omega

theorem isSelfDualC_lamN : ∀ (D : D7) (u : D.what₂.Word) (Y X : HSp D) (ι : X.V →ₗ[D.host.E] Y.V) (z : Y.V) (ρ : ℕ) (e f : Fin ρ → Y.V), GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsDec Y X ι (fun _ : Fin 1 => z) (-GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.Tu D u) e f → ∀ L, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsSDIn Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.flatSp Y X ι z) L → ∀ nn, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.IsCStable nn → Formalism.IndefR.Datum.IsSelfDualC Y (Formalism.L2.Herm.crdLat Y (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.lamN Y e f L nn)) := by
  intro D u Y X ι z ρ e f H L hL nn hn
  have hc : -Tu D u ≠ 0 := neg_ne_zero.2 (Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero)
  have h := (isHyp_flatSp hc H).selfDual hL.1 hL.2.1 hL.2.2 (J := fun i => nn ^ (ρ - i.val))
    (fun i => pow_ne_zero _ hn.1) (fun i => star_mem_pow (fun x hx => (hn.2 x).1 hx) _)
  exact isSelfDualC_crdLat Y h.1 h.2

end GlobalTheory.HypLattice
