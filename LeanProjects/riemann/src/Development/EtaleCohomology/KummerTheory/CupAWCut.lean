import Development.EtaleCohomology.KummerTheory.InjSlice
import Development.EtaleCohomology.KummerTheory.CupAWCutEv
import Development.EtaleCohomology.TateTwists.CupflipWdPf
import Development.EtaleCohomology.TateTwists.CupflipAwExistsPfCochain
import Development.EtaleCohomology.TateTwists.EtaleChainCochainExistsOfEvalData

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.KummerTheory.AW
variable {R : Type} [CommRing R] {E : Spc} {I J K : Cx R} {n m k : ℤ} {U : Scheme.{0}}

def ev0 (α : Cochain ((chains R).obj E) I n) (s : ℤ) (U : Scheme.{0}) (p : ℕ) (x : Sx E p U) : Sec (I.X s) U :=
  if h : -(p : ℤ) + n = s then ev α p s h U x else 0

theorem ev_delta {m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (p : ℕ) (s t : ℤ)
    (hs : -(p : ℤ) + n = s) (ht : -(p : ℤ) + m = t) (x : Sx E p U) :
    ev (δ n m α) p t ht U x = Sec.map (I.d s t) (ev α p s hs U x) + m.negOnePow • bd (ev0 α t U) p x := by
  cases p with
  | zero => rw [ev_delta_zero hm α s t hs]; simp [bd]
  | succ p =>
    rw [ev_delta_succ hm α p s t hs]
    congr 2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos]

def pr (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m) (w : ℤ) (U : Scheme.{0})
    (p q : ℕ) (y : Sx E p U) (z : Sx E q U) : Sec (K.X w) U :=
  if h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w then μ.mul U _ _ w h (ev α p _ rfl U y) (ev β q _ rfl U z) else 0

variable (μ : Pair I J K) (α : Cochain ((chains R).obj E) I n) (β : Cochain ((chains R).obj E) J m)

theorem mul_ev {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (ev β q t ht U z) = pr μ α β w U p q y z := by
  subst hs ht
  rw [pr, dif_pos h]

theorem mul_bd_left {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + (n + 1) = s) (ht : -(q : ℤ) + m = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (bd (ev0 α s U) p y) (ev β q t ht U z) = bd (fun a y => pr μ α β w U a q y z) p y := by
  cases p with
  | zero => simp [bd]
  | succ p =>
    simp only [bd, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos (by omega), mul_ev]

theorem mul_bd_right {s t w : ℤ} (h : s + t = w) {p q : ℕ} (hs : -(p : ℤ) + n = s) (ht : -(q : ℤ) + (m + 1) = t) (y : Sx E p U)
    (z : Sx E q U) : μ.mul U s t w h (ev α p s hs U y) (bd (ev0 β t U) q z) = bd (fun b z => pr μ α β w U p b y z) q z := by
  cases q with
  | zero => simp [bd]
  | succ q =>
    simp only [bd, map_sum, map_zsmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [ev0, dif_pos (by omega), mul_ev]

theorem d_pr {w : ℤ} {p q : ℕ} (h : (-(p : ℤ) + n) + (-(q : ℤ) + m) = w) (y : Sx E p U) (z : Sx E q U) :
    Sec.map (K.d w (w + 1)) (pr μ α β w U p q y z) =
      (pr μ (δ n (n + 1) α) β (w + 1) U p q y z -
        (((n + 1).negOnePow : ℤˣ) : ℤ) • bd (fun a y => pr μ α β (w + 1) U a q y z) p y) +
      (((-(p : ℤ) + n).negOnePow : ℤˣ) : ℤ) • (pr μ α (δ m (m + 1) β) (w + 1) U p q y z -
        (((m + 1).negOnePow : ℤˣ) : ℤ) • bd (fun b z => pr μ α β (w + 1) U p b y z) q z) := by
  rw [pr, dif_pos h, μ.leibniz, Units.smul_def]
  congr 1
  · rw [← mul_ev μ (δ n (n + 1) α) β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      ev_delta rfl α p _ _ rfl, ← mul_bd_left μ α β (s := -(p : ℤ) + n + 1) (t := -(q : ℤ) + m) (by omega) (by omega) rfl,
      map_add, Units.smul_def, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply, add_sub_cancel_right]
  · rw [← mul_ev μ α (δ m (m + 1) β) (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      ev_delta rfl β q _ _ rfl, ← mul_bd_right μ α β (s := -(p : ℤ) + n) (t := -(q : ℤ) + m + 1) (by omega) rfl (by omega),
      map_add, Units.smul_def, map_zsmul, add_sub_cancel_right]

variable {μ α β} in
theorem aw_eq {hk : n + m = k} {γ : Cochain ((chains R).obj E) K k} (hγ : μ.IsAW hk α β γ) (N : ℕ) (w : ℤ)
    (h : -(N : ℤ) + k = w) (x : Sx E N U) : ev γ N w h U x = ∑ p : Fin (N + 1), (((m * (p : ℕ)).negOnePow : ℤˣ) : ℤ) •
      pr μ α β w U p (N - p) (x.sub 0 p (by omega)) (x.sub p (N - p) (by omega)) := by
  rw [hγ N w h U x]
  exact Finset.sum_congr rfl fun p _ => by rw [mul_ev, Units.smul_def]

theorem leibniz : LateralTheory.EtaleFoundations.cupflip_aw_leibniz := by
  intro R _ I J K μ E n m k hk α β γ γ₁ γ₂ h h1 h2
  refine ev_ext _ _ fun M w' hw' U x => ?_
  obtain ⟨w, rfl⟩ : ∃ w, w' = w + 1 := ⟨w' - 1, by omega⟩
  have hw : -(M : ℤ) + k = w := by omega
  have hb : bd (ev0 γ (w + 1) U) M x = _ :=
    (bd_congr (fun N y e => by rw [ev0, dif_pos (by omega), aw_eq h]) x).trans
      (bd_aw (pr μ α β (w + 1) U) (fun p => (((m * p).negOnePow : ℤˣ) : ℤ))
        (fun p => ((m.negOnePow * (m * p).negOnePow : ℤˣ) : ℤ)) (fun p => by
          push_cast
          rw [mul_add, mul_one, Int.negOnePow_add]
          rcases Int.units_eq_one_or m.negOnePow with e | e <;> simp [e]) M x)
  rw [ev_delta rfl γ M w _ hw, ev_add, ev_units_smul, aw_eq h, aw_eq h1, aw_eq h2, hb, Sec.map, map_sum,
    Units.smul_def, Units.smul_def, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  have := p.2
  have hd := d_pr μ α β (w := w) (p := p) (q := M - p) (by omega) (x.sub 0 p (by omega)) (x.sub p (M - p) (by omega))
  rw [Sec.map] at hd
  rw [map_zsmul, hd]
  have e : (-1 : ℤ) ^ (p : ℕ) = ((((p : ℕ) : ℤ).negOnePow : ℤˣ) : ℤ) := by simp [Int.coe_negOnePow_natCast]
  rw [e, ← hk, add_mul, one_mul]
  simp only [Int.negOnePow_add, Int.negOnePow_neg, Int.negOnePow_one]
  generalize (m * (p : ℕ)).negOnePow = c
  generalize ((p : ℕ) : ℤ).negOnePow = d
  generalize n.negOnePow = a
  rcases Int.units_eq_one_or m.negOnePow with e | e <;> rw [e] <;> push_cast <;> module

theorem aw_cochain : LateralTheory.EtaleFoundations.cupflip_aw_cochain :=
  LateralTheory.EtaleFoundations.cupflip_aw_cochain_of LateralTheory.EtaleFoundations.etale_chain_cochain_exists_of_eval_data
    (fun _ _ _ _ _ α p s h _ _ g x => ev_res α p s h g x) LateralTheory.EtaleFoundations.cupflip_sub_res_holds

theorem aw_exists : LateralTheory.EtaleFoundations.cupflip_aw_exists := LateralTheory.EtaleFoundations.cupflip_aw_exists_of aw_cochain leibniz

variable {μ α β} in
theorem aw_unique {hk : n + m = k} {γ γ' : Cochain ((chains R).obj E) K k} (h : μ.IsAW hk α β γ) (h' : μ.IsAW hk α β γ') :
    γ = γ' := ev_ext _ _ fun N w hw U x => (h N w hw U x).trans (h' N w hw U x).symm

theorem wd_aw : LateralTheory.EtaleFoundations.cupflip_wd_aw := by
  intro R _ I J K μ E n m k hk
  refine ⟨aw_exists R μ E hk, fun _ _ _ _ => aw_unique, fun α α' β γ γ' h h' N w hw U x => ?_,
    fun α β β' γ γ' h h' N w hw U x => ?_⟩ <;>
  · rw [ev_add, h, h', ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp only [ev_add, map_add, LinearMap.add_apply, smul_add]

theorem wd_cobdry : LateralTheory.EtaleFoundations.cupflip_wd_cobdry := by
  rintro R _ I J K μ E n m k hk α β γ h (⟨n', hn, η, hη⟩ | ⟨m', hm, η, hη⟩)
  · subst hn
    obtain rfl : k = n' + m + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl η β.1
    refine ⟨n' + m, rfl, θ, ?_⟩
    rw [leibniz R μ rfl η β.1 θ γ.1 0 hθ (by rw [hη]; exact h)
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_right μ _ _), smul_zero, add_zero]
  · subst hm
    obtain rfl : k = n + m' + 1 := by omega
    obtain ⟨θ, hθ⟩ := aw_cochain R μ E rfl α.1 η
    refine ⟨n + m', rfl, n.negOnePow • θ, ?_⟩
    rw [δ_units_smul, leibniz R μ rfl α.1 η θ 0 γ.1 hθ
      (by rw [Cocycle.δ_eq_zero]; exact LateralTheory.EtaleFoundations.isAW_zero_left μ _ _) (by rw [hη]; exact h), zero_add, smul_smul,
      Int.units_mul_self, one_smul]

theorem wd : LateralTheory.EtaleFoundations.cupflip_wd := LateralTheory.EtaleFoundations.cupflip_wd_of wd_aw wd_cobdry

theorem cup_mk {hk : n + m = k} (α : Cocycle ((chains R).obj E) I n) (β : Cocycle ((chains R).obj E) J m)
    (γ : Cocycle ((chains R).obj E) K k) (h : μ.IsAW hk α.1 β.1 γ.1) :
    μ.cup E hk (CohomologyClass.mk α) (CohomologyClass.mk β) = CohomologyClass.mk γ :=
  pick_spec (wd R μ E hk) α β γ h

end LateralTheory.KummerTheory.AW

theorem LateralTheory.KummerTheory.CupAW_of : LateralTheory.KummerTheory.CupAW := by
  intro R _ I J K μ E n m k hk α β
  obtain ⟨γ, hγ⟩ := AW.aw_exists R μ E hk α β
  exact ⟨γ, hγ, AW.cup_mk μ α β γ hγ⟩

end
