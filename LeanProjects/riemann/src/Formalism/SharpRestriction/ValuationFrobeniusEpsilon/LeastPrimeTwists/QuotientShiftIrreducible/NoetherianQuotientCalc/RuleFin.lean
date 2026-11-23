import Formalism.SharpRestriction.ValuationFrobeniusEpsilon.LeastPrimeTwists.QuotientShiftIrreducible.NoetherianQuotientCalc.EulerVanishingBelowDimension

noncomputable section

namespace Formalism.MainNotions.V.Pf.V2.Calc

open IsLocalRing Filter

section Len

variable {B : Type} [CommRing B] [IsLocalRing B]

theorem length_ne_top_of_max {M : Type} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (h : ∀ b ∈ maximalIdeal B, ∀ y : M, b • y = 0) : Module.length B M ≠ ⊤ := by
  have hM : Module.IsTorsionBySet B M (maximalIdeal B : Set B) := by
    intro y b
    exact h b.1 b.2 y
  let : Module (B ⧸ maximalIdeal B) M := hM.module
  have : IsScalarTower B (B ⧸ maximalIdeal B) M := hM.isScalarTower
  let : Field (B ⧸ maximalIdeal B) := Ideal.Quotient.field _
  have : Module.Finite (B ⧸ maximalIdeal B) M := Module.Finite.of_restrictScalars_finite B _ M
  rw [Module.length_eq_of_surjective (R := B ⧸ maximalIdeal B) Ideal.Quotient.mk_surjective]
  exact Module.length_ne_top

theorem length_ne_top_of_pow [IsNoetherianRing B] (N : ℕ) :
    ∀ {M : Type} [AddCommGroup M] [Module B M] [Module.Finite B M],
      (∀ b ∈ maximalIdeal B ^ N, ∀ y : M, b • y = 0) → Module.length B M ≠ ⊤ := by
  induction N with
  | zero =>
    intro M _ _ _ h
    have : Subsingleton M := ⟨fun x y => by
      have hx := h 1 (by simp) x
      have hy := h 1 (by simp) y
      rw [one_smul] at hx hy
      rw [hx, hy]⟩
    rw [Module.length_eq_zero]
    simp
  | succ N ih =>
    intro M _ _ _ h
    let P : Submodule B M := maximalIdeal B • ⊤
    have h1 : Module.length B P ≠ ⊤ := by
      apply ih
      rintro b hb ⟨y, hy⟩
      apply Subtype.ext
      show b • y = 0
      refine Submodule.smul_induction_on hy ?_ ?_
      · intro a ha z _
        rw [smul_smul]
        exact h _ (by rw [pow_succ]; exact Ideal.mul_mem_mul hb ha) z
      · intro x y hx hy
        rw [smul_add, hx, hy, add_zero]
    have h2 : Module.length B (M ⧸ P) ≠ ⊤ := by
      apply length_ne_top_of_max
      intro b hb y
      obtain ⟨z, rfl⟩ := P.mkQ_surjective y
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact Submodule.smul_mem_smul hb trivial
    rw [Module.length_eq_add_of_exact P.subtype P.mkQ P.injective_subtype P.mkQ_surjective
      (LinearMap.exact_subtype_mkQ P)]
    simp [h1, h2]

end Len

section Degs

variable {k : ℕ}

theorem e_nonneg (i : Fin k) : (0 : Deg k) ≤ e i := by
  intro j
  by_cases hj : j = i
  · subst hj; simp [e]
  · simp [e, Pi.single_eq_of_ne hj]

theorem sum_e : ∑ i, e i = (fun _ => 1 : Deg k) :=
  Finset.univ_sum_single (fun _ : Fin k => (1 : ℤ))

theorem deg_induction {P : Deg k → Prop} (h0 : P 0)
    (hs : ∀ m i, 0 ≤ m → P m → P (m + e i)) : ∀ m, 0 ≤ m → P m := by
  have key : ∀ n : ℕ, ∀ m : Deg k, 0 ≤ m → ∑ i, m i = (n : ℤ) → P m := by
    intro n
    induction n with
    | zero =>
      intro m hm hsum
      have : m = 0 := by
        funext i
        exact (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hm i)).1 (by simpa using hsum) i
          (Finset.mem_univ i)
      rw [this]
      exact h0
    | succ n ih =>
      intro m hm hsum
      have hex : ∃ i, 0 < m i := by
        by_contra hcon
        push Not at hcon
        have h1 : ∑ i, m i ≤ 0 := Finset.sum_nonpos (fun i _ => hcon i)
        rw [hsum] at h1
        push_cast at h1
        omega
      obtain ⟨i, hi⟩ := hex
      have h1 : 0 ≤ m - e i := by
        intro j
        by_cases hj : j = i
        · subst hj
          simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_same]
          omega
        · simp only [e, Pi.zero_apply, Pi.sub_apply, Pi.single_eq_of_ne hj, sub_zero]
          exact hm j
      have h2 : ∑ j, (m - e i) j = (n : ℤ) := by
        have h3 : ∑ j, (e i : Deg k) j = 1 := by
          simp [e, Finset.sum_pi_single']
        simp only [Pi.sub_apply, Finset.sum_sub_distrib, hsum, h3]
        push_cast
        ring
      have h4 := hs (m - e i) i h1 (ih _ h1 h2)
      rwa [sub_add_cancel] at h4
  intro m hm
  have hnn : 0 ≤ ∑ i, m i := Finset.sum_nonneg (fun i _ => hm i)
  exact key (∑ i, m i).toNat m hm (by rw [Int.toNat_of_nonneg hnn])

end Degs

section Ring

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable {𝒜 : Deg k → Submodule B R}

theorem Std.fg_all [IsLocalRing B] (h : Std 𝒜) (m : Deg k) : (𝒜 m).FG := by
  by_cases hm : 0 ≤ m
  · refine deg_induction (P := fun m => (𝒜 m).FG) ?_ ?_ m hm
    · rw [h.zero, LinearMap.range_eq_map]
      exact Submodule.FG.map _ Module.Finite.fg_top
    · intro m i hm ih
      rw [h.gen m i hm]
      exact ih.mul (h.fg i)
  · rw [h.nonneg m hm]
    exact Submodule.fg_bot

theorem Std.span_add_e [IsLocalRing B] (h : Std 𝒜) (m : Deg k) (i : Fin k) (hm : 0 ≤ m) :
    Ideal.span (𝒜 (m + e i) : Set R) ≤
      Ideal.span (𝒜 m : Set R) * Ideal.span (𝒜 (e i) : Set R) := by
  rw [Ideal.span_le, h.gen m i hm]
  intro x hx
  refine Submodule.mul_induction_on hx ?_ ?_
  · intro a ha b hb
    exact Ideal.mul_mem_mul (Ideal.subset_span ha) (Ideal.subset_span hb)
  · intro a b ha hb
    exact Ideal.add_mem _ ha hb

theorem Std.span_add_sum [IsLocalRing B] (h : Std 𝒜) (S : Finset (Fin k)) :
    ∀ m, 0 ≤ m → Ideal.span (𝒜 (m + ∑ i ∈ S, e i) : Set R) ≤
      Ideal.span (𝒜 m : Set R) * ∏ i ∈ S, Ideal.span (𝒜 (e i) : Set R) := by
  induction S using Finset.induction_on with
  | empty => intro m _; simp
  | insert i S hi ih =>
    intro m hm
    rw [Finset.sum_insert hi, Finset.prod_insert hi]
    have h1 : m + (e i + ∑ j ∈ S, e j) = (m + ∑ j ∈ S, e j) + e i := by abel
    rw [h1]
    have hnn : 0 ≤ m + ∑ j ∈ S, e j :=
      add_nonneg hm (Finset.sum_nonneg fun j _ => e_nonneg j)
    calc Ideal.span (𝒜 (m + ∑ j ∈ S, e j + e i) : Set R)
        ≤ Ideal.span (𝒜 (m + ∑ j ∈ S, e j) : Set R) * Ideal.span (𝒜 (e i) : Set R) :=
          h.span_add_e _ _ hnn
      _ ≤ (Ideal.span (𝒜 m : Set R) * ∏ j ∈ S, Ideal.span (𝒜 (e j) : Set R)) *
            Ideal.span (𝒜 (e i) : Set R) := Ideal.mul_mono_left (ih m hm)
      _ = _ := by rw [mul_assoc, mul_comm (∏ j ∈ S, Ideal.span (𝒜 (e j) : Set R))]

theorem Std.span_le_irr_pow [IsLocalRing B] (h : Std 𝒜) (N : ℕ) :
    ∀ m, 0 ≤ m → Ideal.span (𝒜 (m + N • ∑ i, e i) : Set R) ≤ Irr 𝒜 ^ N := by
  induction N with
  | zero => intro m _; simp
  | succ N ih =>
    intro m hm
    have h1 : m + (N + 1) • ∑ i, e i = (m + N • ∑ i, e i) + ∑ i, e i := by
      rw [succ_nsmul, add_assoc]
    have hu : (0 : Deg k) ≤ ∑ i, e i := Finset.sum_nonneg fun j _ => e_nonneg j
    have hnn : 0 ≤ m + N • ∑ i, e i := add_nonneg hm (nsmul_nonneg hu N)
    rw [h1, pow_succ]
    exact (h.span_add_sum Finset.univ _ hnn).trans (Ideal.mul_mono_left (ih m hm))

theorem Std.mem_irr_pow [IsLocalRing B] (h : Std 𝒜) (N : ℕ) (n : Deg k)
    (hn : ∀ i, (N : ℤ) ≤ n i) {a : R} (ha : a ∈ 𝒜 n) : a ∈ Irr 𝒜 ^ N := by
  have h0 : 0 ≤ n - N • ∑ i, e i := by
    intro i
    rw [sum_e]
    rw [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul, mul_one]
    exact sub_nonneg.2 (hn i)
  have h1 := h.span_le_irr_pow N _ h0
  rw [sub_add_cancel] at h1
  exact h1 (Ideal.subset_span ha)

end Ring

section Gens

variable {k : ℕ} {B R : Type} [CommRing B] [CommRing R] [Algebra B R]
variable {𝒜 : Deg k → Submodule B R}

theorem eq_of_le_of_iSup_eq_top {ι M : Type} [AddCommGroup M] [Module B M]
    {G H : ι → Submodule B M} (hle : ∀ i, G i ≤ H i) (hind : iSupIndep H)
    (htop : ⨆ i, G i = ⊤) (i : ι) : G i = H i := by
  classical
  apply le_antisymm (hle i)
  intro x hx
  have h1 : x ∈ G i ⊔ ⨆ (j) (_ : j ≠ i), G j := by
    have h2 : (⨆ j, G j) ≤ G i ⊔ ⨆ (j) (_ : j ≠ i), G j := iSup_le fun j => by
      by_cases h : j = i
      · subst h; exact le_sup_left
      · exact le_sup_of_le_right (le_iSup₂_of_le j h le_rfl)
    exact h2 (htop ▸ trivial)
  obtain ⟨g, hg, y, hy, rfl⟩ := Submodule.mem_sup.1 h1
  have h2 : y ∈ ⨆ (j) (_ : j ≠ i), H j := (iSup₂_mono fun j _ => hle j) hy
  have h3 : y ∈ H i := by
    have := (H i).sub_mem hx (hle i hg)
    simpa using this
  have h4 : y = 0 := by
    have := (hind i).le_bot ⟨h3, h2⟩
    simpa using this
  rw [h4, add_zero]
  exact hg

theorem GMod.IsGr.exists_gens {F : GMod B R k} (hF : F.IsGr 𝒜) :
    ∃ T : Finset F.M, (∀ x ∈ T, ∃ m, x ∈ F.gr m) ∧ Submodule.span R (T : Set F.M) = ⊤ := by
  have htop : Submodule.span R {x : F.M | ∃ m, x ∈ F.gr m} = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ ⨆ m, F.gr m := by
      rw [hF.internal.submodule_iSup_eq_top]; trivial
    refine Submodule.iSup_induction _
      (motive := fun y => y ∈ Submodule.span R {x : F.M | ∃ m, x ∈ F.gr m}) hy ?_ ?_ ?_
    · intro m x hx
      exact Submodule.subset_span ⟨m, hx⟩
    · exact zero_mem _
    · intro a b ha hb
      exact add_mem ha hb
  have hfg : (Submodule.span R {x : F.M | ∃ m, x ∈ F.gr m}).FG := by
    rw [htop]; exact hF.fin.fg_top
  obtain ⟨T, hT, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  exact ⟨T, fun x hx => hT hx, by rw [← hspan, htop]⟩

def genPiece (𝒜 : Deg k → Submodule B R) (F : GMod B R k) (T : Finset F.M) (dg : F.M → Deg k)
    (m : Deg k) : Submodule B F.M :=
  ⨆ x ∈ T, (𝒜 (m - dg x)).map ((LinearMap.toSpanSingleton R F.M x).restrictScalars B)

theorem genPiece_le {F : GMod B R k} {T : Finset F.M} {dg : F.M → Deg k} {m : Deg k}
    {W : Submodule B F.M} (h : ∀ x ∈ T, ∀ a ∈ 𝒜 (m - dg x), a • x ∈ W) :
    genPiece 𝒜 F T dg m ≤ W := by
  refine iSup₂_le fun x hx => ?_
  rw [Submodule.map_le_iff_le_comap]
  intro a ha
  exact h x hx a ha

theorem mem_genPiece {F : GMod B R k} {T : Finset F.M} {dg : F.M → Deg k} {m : Deg k}
    {x : F.M} (hx : x ∈ T) {a : R} (ha : a ∈ 𝒜 (m - dg x)) : a • x ∈ genPiece 𝒜 F T dg m :=
  Submodule.mem_iSup_of_mem x (Submodule.mem_iSup_of_mem hx ⟨a, ha, rfl⟩)

theorem GMod.IsGr.genPiece_eq {F : GMod B R k} (hF : F.IsGr 𝒜) (h𝒜 : ⨆ d, 𝒜 d = ⊤)
    {T : Finset F.M} {dg : F.M → Deg k} (hdg : ∀ x ∈ T, x ∈ F.gr (dg x))
    (hspan : Submodule.span R (T : Set F.M) = ⊤) (m : Deg k) :
    genPiece 𝒜 F T dg m = F.gr m := by
  refine eq_of_le_of_iSup_eq_top (G := genPiece 𝒜 F T dg) (H := F.gr) ?_
    hF.internal.submodule_iSupIndep ?_ m
  · intro m
    refine genPiece_le fun x hx a ha => ?_
    have := hF.smul_mem ha (hdg x hx)
    rwa [sub_add_cancel] at this
  · rw [eq_top_iff]
    intro y _
    have key : ∀ x ∈ T, ∀ a : R, a • x ∈ ⨆ m, genPiece 𝒜 F T dg m := by
      intro x hx a
      have ha : a ∈ ⨆ d, 𝒜 d := by rw [h𝒜]; trivial
      refine Submodule.iSup_induction _
        (motive := fun a => a • x ∈ ⨆ m, genPiece 𝒜 F T dg m) ha ?_ ?_ ?_
      · intro d a ha
        refine Submodule.mem_iSup_of_mem (d + dg x) (mem_genPiece hx ?_)
        rwa [add_sub_cancel_right]
      · rw [zero_smul]; exact zero_mem _
      · intro a b ha hb
        rw [add_smul]; exact add_mem ha hb
    have hy : y ∈ Submodule.span R (T : Set F.M) := by rw [hspan]; trivial
    have hall : ∀ a : R, a • y ∈ ⨆ m, genPiece 𝒜 F T dg m := by
      refine Submodule.span_induction
        (p := fun y _ => ∀ a : R, a • y ∈ ⨆ m, genPiece 𝒜 F T dg m) ?_ ?_ ?_ ?_ hy
      · intro x hx a
        exact key x hx a
      · intro a
        rw [smul_zero]; exact zero_mem _
      · intro x y _ _ hx hy a
        rw [smul_add]; exact add_mem (hx a) (hy a)
      · intro r x _ hx a
        rw [smul_smul]; exact hx _
    simpa using hall 1

theorem genPiece_fg [IsLocalRing B] (h : Std 𝒜) (F : GMod B R k) (T : Finset F.M)
    (dg : F.M → Deg k) (m : Deg k) : (genPiece 𝒜 F T dg m).FG :=
  Submodule.fg_biSup T _ fun _ _ => (h.fg_all _).map _

theorem GMod.IsGr.exists_gens_deg {F : GMod B R k} (hF : F.IsGr 𝒜) :
    ∃ (T : Finset F.M) (dg : F.M → Deg k), (∀ x ∈ T, x ∈ F.gr (dg x)) ∧
      Submodule.span R (T : Set F.M) = ⊤ := by
  classical
  obtain ⟨T, hT, hspan⟩ := hF.exists_gens
  refine ⟨T, fun x => if h : ∃ m, x ∈ F.gr m then h.choose else 0, fun x hx => ?_, hspan⟩
  beta_reduce
  rw [dif_pos (hT x hx)]
  exact (hT x hx).choose_spec

theorem GMod.IsGr.finite_gr [IsLocalRing B] (h : Std 𝒜) (h𝒜 : ⨆ d, 𝒜 d = ⊤) {F : GMod B R k}
    (hF : F.IsGr 𝒜) (m : Deg k) : Module.Finite B (F.gr m) := by
  obtain ⟨T, dg, hdg, hspan⟩ := hF.exists_gens_deg
  rw [Module.Finite.iff_fg, ← hF.genPiece_eq h𝒜 hdg hspan m]
  exact genPiece_fg h F T dg m

theorem GMod.IsGr.eventually_gr_le [IsLocalRing B] (h : Std 𝒜) (h𝒜 : ⨆ d, 𝒜 d = ⊤)
    {F : GMod B R k} (hF : F.IsGr 𝒜) (N : ℕ) :
    ∀ᶠ m in atTop, ∀ y ∈ F.gr m, y ∈ (Irr 𝒜 ^ N • (⊤ : Submodule R F.M)) := by
  obtain ⟨T, dg, hdg, hspan⟩ := hF.exists_gens_deg
  have hev : ∀ᶠ m in atTop, ∀ x ∈ T, dg x + (fun _ => (N : ℤ)) ≤ m :=
    (Filter.eventually_all_finset T).2 fun x _ => eventually_ge_atTop _
  filter_upwards [hev] with m hm
  have hle : genPiece 𝒜 F T dg m ≤ (Irr 𝒜 ^ N • (⊤ : Submodule R F.M)).restrictScalars B := by
    refine genPiece_le fun x hx a ha => ?_
    have ha' : a ∈ Irr 𝒜 ^ N := by
      refine h.mem_irr_pow N _ (fun i => ?_) ha
      have := hm x hx i
      simp only [Pi.add_apply, Pi.sub_apply] at this ⊢
      omega
    rw [Submodule.restrictScalars_mem]
    exact Submodule.smul_mem_smul ha' Submodule.mem_top
  intro y hy
  rw [← hF.genPiece_eq h𝒜 hdg hspan m] at hy
  exact hle hy

end Gens

theorem HidaSetting.iSup_eq_top {k : ℕ} (X : HidaSetting k) : ⨆ d, X.𝒜 d = ⊤ :=
  (DirectSum.Decomposition.isInternal X.𝒜).submodule_iSup_eq_top

theorem ruleFin : RuleFin := by
  intro k X F hF
  refine ⟨fun m => hF.finite_gr X.std X.iSup_eq_top m, ?_⟩
  rintro ⟨N, hN⟩
  have hN' : ((maximalIdeal X.B).map (algebraMap X.B X.R) * Irr X.𝒜) ^ N ≤ F.Ann := by
    refine hN.trans ?_
    simp [secs]
  have := X.std.noeth
  filter_upwards [hF.eventually_gr_le X.std X.iSup_eq_top N] with m hm
  have := hF.finite_gr X.std X.iSup_eq_top m
  apply length_ne_top_of_pow N
  rintro b hb ⟨y, hy⟩
  apply Subtype.ext
  show b • y = 0
  refine Submodule.smul_induction_on (hm y hy) ?_ ?_
  · intro a ha z _
    have h1 : algebraMap X.B X.R b * a ∈ F.Ann := by
      apply hN'
      rw [mul_pow, ← Ideal.map_pow]
      exact Ideal.mul_mem_mul (Ideal.mem_map_of_mem _ hb) ha
    have h2 := Module.mem_annihilator.1 h1 z
    rwa [mul_smul, algebraMap_smul] at h2
  · intro x y hx hy
    rw [smul_add, hx, hy, add_zero]

end Formalism.MainNotions.V.Pf.V2.Calc
