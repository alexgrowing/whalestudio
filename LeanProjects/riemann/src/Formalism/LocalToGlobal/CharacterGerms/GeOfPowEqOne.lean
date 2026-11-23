import Formalism.LocalToGlobal.CharacterGerms.NegMem

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C]

def InL (l : ℕ) (f : PowerSeries C) : Prop := ∀ m, ¬ l ∣ m → PowerSeries.coeff m f = 0

def dnL (l : ℕ) (f : PowerSeries C) : PowerSeries C := PowerSeries.mk fun n => PowerSeries.coeff (l * n) f

theorem coeff_dnL (l : ℕ) (f : PowerSeries C) (n : ℕ) :
    PowerSeries.coeff n (dnL l f) = PowerSeries.coeff (l * n) f := by
  unfold dnL
  rw [PowerSeries.coeff_mk]

theorem InL.eq_subst {l : ℕ} (hl : 0 < l) {f : PowerSeries C} (hf : InL l f) :
    f = PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (dnL l f) := by
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl, coeff_dnL]
  · rw [coeff_subst_X_pow_of_not_dvd hl _ _ hm, hf m hm]

theorem inL_subst {l : ℕ} (hl : 0 < l) (f : PowerSeries C) :
    InL l (PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f) :=
  fun m hm => coeff_subst_X_pow_of_not_dvd hl f m hm

theorem subst_X_pow_inj {l : ℕ} (hl : 0 < l) {f g : PowerSeries C}
    (h : PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) g) : f = g := by
  ext n
  have e := congrArg (PowerSeries.coeff (l * n)) h
  rwa [coeff_subst_X_pow hl, coeff_subst_X_pow hl] at e

theorem InL.add {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f + g) :=
  fun m hm => by rw [map_add, hf m hm, hg m hm, add_zero]

theorem InL.sub {l : ℕ} {f g : PowerSeries C} (hf : InL l f) (hg : InL l g) : InL l (f - g) :=
  fun m hm => by rw [map_sub, hf m hm, hg m hm, sub_zero]

theorem InL.smul {l : ℕ} {f : PowerSeries C} (hf : InL l f) (c : C) : InL l (c • f) :=
  fun m hm => by rw [PowerSeries.coeff_smul, hf m hm, smul_zero]

theorem InL.zero {l : ℕ} : InL l (0 : PowerSeries C) :=
  fun m _ => map_zero _

theorem InL.sum {l : ℕ} {ι : Type} (s : Finset ι) (f : ι → PowerSeries C) (hf : ∀ i ∈ s, InL l (f i)) :
    InL l (∑ i ∈ s, f i) :=
  fun m hm => by
    rw [map_sum]
    exact Finset.sum_eq_zero fun i hi => hf i hi m hm

private theorem coeff_tyS_pow_eq_of_two_le {l : ℕ} (hl : 2 ≤ l) (b : ℕ → C) (s : ℕ) :
    PowerSeries.coeff (l ^ s) (tyS l b) = b s := by
  simp only [tyS, PowerSeries.coeff_mk]
  rw [Finset.sum_eq_single s]
  · rw [if_pos rfl]
  · intro t _ ht
    rw [if_neg]
    intro e
    exact ht (Nat.pow_right_injective hl e)
  · intro hs
    exfalso
    apply hs
    rw [Finset.mem_range]
    have := Nat.lt_pow_self (by omega : 1 < l) (n := s)
    omega

private theorem coeff_tyS_eq_zero_of_ne_pow {l : ℕ} (b : ℕ → C) (m : ℕ) (hm : ∀ s, l ^ s ≠ m) :
    PowerSeries.coeff m (tyS l b) = 0 := by
  simp only [tyS, PowerSeries.coeff_mk]
  exact Finset.sum_eq_zero fun s _ => if_neg (hm s)

theorem tyS_Vpow {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) :
    tyS l (fun s => if s < 1 then 0 else a (s - 1)) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l a) := by
  have hl0 : 0 < l := by omega
  ext m
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [coeff_subst_X_pow hl0]
    by_cases hk : ∃ t, l ^ t = k
    · obtain ⟨t, rfl⟩ := hk
      rw [← pow_succ', coeff_tyS_pow_eq_of_two_le hl, coeff_tyS_pow_eq_of_two_le hl]
      simp
    · push_neg at hk
      have hk' : ∀ s, l ^ s ≠ l * k := by
        intro s hs
        rcases s with _ | s
        · rw [pow_zero] at hs
          have h1 : l ∣ 1 := ⟨k, hs⟩
          have := Nat.le_of_dvd one_pos h1
          omega
        · rw [pow_succ'] at hs
          exact hk s (Nat.eq_of_mul_eq_mul_left hl0 hs)
      rw [coeff_tyS_eq_zero_of_ne_pow _ _ hk', coeff_tyS_eq_zero_of_ne_pow _ _ hk]
  · rw [coeff_subst_X_pow_of_not_dvd hl0 _ _ hm]
    simp only [tyS, PowerSeries.coeff_mk]
    apply Finset.sum_eq_zero
    intro s _
    split_ifs with h1 h2
    · rfl
    · exfalso
      apply hm
      rw [← h1]
      exact dvd_pow_self l (by omega)
    · rfl

theorem inL_of_rescale {l : ℕ} {ζ : C} (hζ : IsPrimitiveRoot ζ l) {f : PowerSeries C}
    (h : PowerSeries.rescale ζ f = f) : InL l f := by
  intro m hm
  have h1 := congrArg (PowerSeries.coeff m) h
  rw [PowerSeries.coeff_rescale] at h1
  have h2 : ζ ^ m ≠ 1 := fun e => hm ((hζ.pow_eq_one_iff_dvd m).mp e)
  have h3 : (ζ ^ m - 1) * PowerSeries.coeff m f = 0 := by
    rw [sub_mul, h1, one_mul, sub_self]
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd (sub_eq_zero.mp h4) h2
  · exact h4

theorem InL.rescale {l : ℕ} {ζ : C} (hζ : ζ ^ l = 1) {f : PowerSeries C} (hf : InL l f) :
    PowerSeries.rescale ζ f = f := by
  ext m
  rw [PowerSeries.coeff_rescale]
  by_cases hm : l ∣ m
  · obtain ⟨k, rfl⟩ := hm
    rw [pow_mul, hζ, one_pow, one_mul]
  · rw [hf m hm, mul_zero]

theorem VF.ge_of_pow_eq_one (V : VF C) {ζ : C} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : V.Ge 0 ζ := by
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hn] at h
    exact zero_ne_one h
  have h1 : n • V.v ζ = 0 := by
    rw [← AddValuation.map_pow, h, AddValuation.map_one]
  have ht : V.v ζ ≠ ⊤ := by
    rw [Ne, AddValuation.top_iff]
    exact hζ0
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp ht
  rw [← hr, ← WithTop.coe_nsmul, WithTop.coe_eq_zero, nsmul_eq_mul, mul_eq_zero] at h1
  have hr0 : r = 0 := h1.resolve_left (Nat.cast_ne_zero.mpr hn)
  unfold VF.Ge
  rw [← hr]
  exact WithTop.coe_le_coe.mpr hr0.ge

namespace RawChart

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)

theorem lg_inj (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {γ γ' : κ → PowerSeries C} (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0)
    (hγ' : ∀ i, PowerSeries.constantCoeff (γ' i) = 0)
    (h : ∀ i, alongCv γ (X.lg i) = alongCv γ' (X.lg i)) : γ = γ' := by
  have key : ∀ (δ : κ → PowerSeries C), (∀ i, PowerSeries.constantCoeff (δ i) = 0) → ∀ i,
      δ i = MvPowerSeries.subst (fun j => alongCv δ (X.lg j)) (X.ex i) := by
    intro δ hδ i
    have hS := MvPowerSeries.hasSubst_of_constantCoeff_zero hδ
    have e1 : MvPowerSeries.subst δ (MvPowerSeries.subst X.lg (X.ex i)) = δ i := by
      rw [hexlg i, MvPowerSeries.subst_X hS]
    rw [← e1, MvPowerSeries.subst_comp_subst_apply (MvPowerSeries.hasSubst_of_constantCoeff_zero hlg0) hS]
    rfl
  funext i
  rw [key γ hγ i, key γ' hγ' i]
  simp only [h]

theorem unV_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l) (z : ℕ → I g ⊕ JJ I g → C) (hz : Vpow 1 z ∈ X.TySet V g) :
    z ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  have hl0 : 0 < V.l := by omega
  obtain ⟨γ, lam, hγ, hlam, h1, h2⟩ := hz
  have hXl : PowerSeries.constantCoeff ((PowerSeries.X : PowerSeries C) ^ V.l) = 0 := by simp [hl0.ne']
  have hS := PowerSeries.HasSubst.of_constantCoeff_zero' hXl
  have hty : ∀ n, tyS V.l (fun s => Vpow 1 z s n) =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (tyS V.l fun s => z s n) :=
    fun n => tyS_Vpow hl2 (fun s => z s n)

  have hLin : ∀ i, InL V.l (alongCv γ (X.lg i)) := by
    intro i
    rw [h1 i]
    refine InL.sum _ _ fun c _ => InL.smul ?_ _
    rw [hty]
    exact inL_subst hl0 _

  have hζX : PowerSeries.constantCoeff (ζ • (PowerSeries.X : PowerSeries C)) = 0 := by simp
  have hγζ : (fun i => PowerSeries.subst (ζ • (PowerSeries.X : PowerSeries C)) (γ i)) = γ := by
    apply X.lg_inj hlg0 hexlg
    · intro i
      exact constantCoeff_subst_zero (σ := Unit) (fun _ => hζX) (hγ i).1
    · exact fun i => (hγ i).1
    · intro i
      rw [alongCv_repar (fun i => (hγ i).1) hζX, ← PowerSeries.rescale_eq_subst]
      exact (hLin i).rescale hζ.pow_eq_one
  have hγL : ∀ i, InL V.l (γ i) := by
    intro i
    apply inL_of_rescale hζ
    rw [PowerSeries.rescale_eq_subst]
    exact congrFun hγζ i
  have hδ : IsCv V fun i => dnL V.l (γ i) := by
    intro i
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hγ i).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hγ i).2 _
  have hγδ : γ = fun i => PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (dnL V.l (γ i)) :=
    funext fun i => (hγL i).eq_subst hl0
  have hal : ∀ f : MvPowerSeries κ C, alongCv γ f =
      PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ V.l) (alongCv (fun i => dnL V.l (γ i)) f) := by
    intro f
    rw [← alongCv_repar (fun i => (hδ i).1) hXl, ← hγδ]

  have hlamEq : ∀ q, lam q = tyS V.l (fun s => Vpow 1 z s (Sum.inr q)) + alongCv γ (X.sg (X.u (1 - g) q)) -
      ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
        X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => Vpow 1 z s (Sum.inl c)) else 0) := by
    intro q
    rw [h2 q]
    abel
  have hlamL : ∀ q, InL V.l (lam q) := by
    intro q
    rw [hlamEq q]
    refine InL.sub (InL.add ?_ ?_) (InL.sum _ _ fun c _ => ?_)
    · rw [hty]; exact inL_subst hl0 _
    · rw [hal]; exact inL_subst hl0 _
    · split_ifs
      · rw [hty]; exact (inL_subst hl0 _).smul _
      · exact InL.zero
  have hlam' : IsCv V fun q => dnL V.l (lam q) := by
    intro q
    refine ⟨?_, fun n => ?_⟩
    · show PowerSeries.constantCoeff (dnL V.l _) = 0
      rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_dnL, mul_zero,
        PowerSeries.coeff_zero_eq_constantCoeff_apply]
      exact (hlam q).1
    · show V.Ge 0 (PowerSeries.coeff n (dnL V.l _))
      rw [coeff_dnL]
      exact (hlam q).2 _
  refine ⟨fun i => dnL V.l (γ i), fun q => dnL V.l (lam q), hδ, hlam', ?_, ?_⟩
  · intro i
    apply subst_X_pow_inj hl0
    rw [← hal, h1 i, ← PowerSeries.coe_substAlgHom hS, map_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_smul, PowerSeries.coe_substAlgHom hS, hty]
  · intro q
    apply subst_X_pow_inj hl0
    rw [← hty, h2 q, ← PowerSeries.coe_substAlgHom hS, map_add, map_sub, map_sum,
      PowerSeries.coe_substAlgHom hS, ← hal, ← (hlamL q).eq_subst hl0]
    congr 1
    refine Finset.sum_congr rfl fun c _ => ?_
    split_ifs
    · rw [← PowerSeries.coe_substAlgHom hS, map_smul, PowerSeries.coe_substAlgHom hS, hty]
    · rw [← PowerSeries.coe_substAlgHom hS, map_zero]

theorem F_mem (V : VF C) (g : Fin 2) (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = (MvPowerSeries.X i : MvPowerSeries κ C))
    {ζ : C} (hζ : IsPrimitiveRoot ζ V.l)
    (h0 : (0 : ℕ → I g ⊕ JJ I g → C) ∈ X.TySet V g)
    (hadd : ∀ x y, x ∈ X.TySet V g → y ∈ X.TySet V g → x + y ∈ X.TySet V g)
    (x : ℕ → I g ⊕ JJ I g → C) (hx : x ∈ X.TySet V g) : Fs V.l x ∈ X.TySet V g := by
  have hl2 := V.l_prime.two_le
  apply X.unV_mem V g hlg0 hexlg hζ
  have hsum : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x ∈ X.TySet V g :=
    X.sum_mem V g h0 hadd _ _ fun k _ =>
      X.teich_mem V g _ ((V.ge_of_pow_eq_one (by omega) hζ.pow_eq_one).pow k) x hx
  have e : ∑ k ∈ Finset.range V.l, teich V.l (ζ ^ k) x = Vpow 1 (Fs V.l x) := by
    funext i n
    rw [Finset.sum_apply, Finset.sum_apply]
    show ∑ k ∈ Finset.range V.l, (ζ ^ k) ^ (V.l ^ i) * x i n = if i < 1 then 0 else (V.l : C) * x (i - 1 + 1) n
    rw [← Finset.sum_mul]
    cases i with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ i =>
      have h1 : ∀ k, (ζ ^ k) ^ (V.l ^ (i + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  rwa [e] at hsum

end RawChart

end Formalism.L2.FormalSeriesBounds
