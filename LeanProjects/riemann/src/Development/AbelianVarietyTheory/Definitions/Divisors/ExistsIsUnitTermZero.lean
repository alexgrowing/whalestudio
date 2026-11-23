import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums

noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

open TateSys

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem term_mem (y : Φ.Y) (mu : Fin s → Φ.X y) (c : Φ.Q) (j : ℕ) (h : (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) :
    Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  refine Ideal.mul_mem_left _ _ ?_
  have h0 : ∀ i, 0 ≤ qW W (Φ.δ y i) mu := fun i => qW_nonneg Φ.posW (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h1 : mono W (Φ.t y) (Φ.δ y) mu ∈ maximalIdeal (Φ.V y) ^ ∑ i, (qW W (Φ.δ y i) mu).toNat := by
    rw [← Finset.prod_pow_eq_pow_sum]
    exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Φ.t_mem y i).1 _
  refine Ideal.pow_le_pow_right ?_ h1
  have : ((∑ i, (qW W (Φ.δ y i) mu).toNat : ℕ) : ℤ) = ∑ i, qW W (Φ.δ y i) mu := by
    rw [Nat.cast_sum]; exact Finset.sum_congr rfl fun i _ => Int.toNat_of_nonneg (h0 i)
  omega

theorem isClassSum_unique (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) {x x' : Φ.V y}
    (h : Φ.IsClassSum y N κ c (RingHom.id _) x) (h' : Φ.IsClassSum y N κ c (RingHom.id _) x') : x = x' := by
  classical
  haveI : IsNoetherianRing (Φ.V y) := (Φ.cn y).1
  have hb := Ideal.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal (Φ.V y)) (maximalIdeal.isMaximal _).ne_top
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← hb, Ideal.mem_iInf]
  intro j
  obtain ⟨S, a1, a2, a3⟩ := h j
  obtain ⟨S', b1, b2, b3⟩ := h' j
  simp only [RingHom.id_apply] at a3 b3
  have e1 := Finset.sum_sdiff (f := fun mu => Φ.term y mu c) (Finset.inter_subset_left (s₁ := S) (s₂ := S'))
  have e2 := Finset.sum_sdiff (f := fun mu => Φ.term y mu c) (Finset.inter_subset_right (s₁ := S) (s₂ := S'))
  have m1 : ∑ mu ∈ S \ (S ∩ S'), Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := Ideal.sum_mem _ fun mu hmu => by
    obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
    exact term_mem Φ y mu c j (b2 mu (a1 mu p) fun r => p' (Finset.mem_inter.2 ⟨p, r⟩))
  have m2 : ∑ mu ∈ S' \ (S ∩ S'), Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := Ideal.sum_mem _ fun mu hmu => by
    obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
    exact term_mem Φ y mu c j (a2 mu (b1 mu p) fun r => p' (Finset.mem_inter.2 ⟨r, p⟩))
  have : x - x' = (x - ∑ mu ∈ S, Φ.term y mu c) - (x' - ∑ mu ∈ S', Φ.term y mu c) +
      ∑ mu ∈ S \ (S ∩ S'), Φ.term y mu c - ∑ mu ∈ S' \ (S ∩ S'), Φ.term y mu c := by
    rw [← e1, ← e2]; ring
  rw [this]
  exact sub_mem (add_mem (sub_mem a3 b3) m1) m2

theorem exists_isUnit_term_zero (y : Φ.Y) : ∃ c : Φ.Q, IsUnit (Φ.term y (0 : Fin s → Φ.X y) c) := by
  obtain ⟨c, hc⟩ := Φ.u_unit y 0
  exact ⟨c, by simpa [VPre.term, mono, qW] using hc⟩

theorem exists_rescale : ∃ v : ∀ y, (Φ.V y)ˣ, ∀ y : (Φ.rescale v).Y, ∃ c : (Φ.rescale v).Q,
    (Φ.rescale v).term y (0 : Fin s → (Φ.rescale v).X y) c = 1 := by
  choose c hc using fun y => Φ.u_unit y 0
  have key : ∀ y : Φ.Y, Φ.u y 0 (c y) * ((hc y).unit⁻¹ : (Φ.V y)ˣ) * mono W (Φ.t y) (Φ.δ y) 0 = 1 := fun y => by
    simp [mono, qW]
  exact ⟨fun y => (hc y).unit⁻¹, fun y => ⟨c y, key y⟩⟩

theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

theorem exists_sum (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : ∃ x : Φ.V y, ∀ j : ℕ,
    ∃ S : Finset (Fin s → Φ.X y), (∀ mu ∈ S, P mu) ∧ (∀ mu, P mu → mu ∉ S → (j : ℤ) ≤ ∑ i, qW W (Φ.δ y i) mu) ∧
      x - ∑ mu ∈ S, Φ.term y mu c ∈ maximalIdeal (Φ.V y) ^ j := by
  classical
  haveI : IsAdicComplete (maximalIdeal (Φ.V y)) (Φ.V y) := (Φ.cn y).2.2.1
  let S : ℕ → Finset (Fin s → Φ.X y) := fun j => (low_finite Φ y P j).toFinset
  have hS : ∀ j mu, mu ∈ S j ↔ P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ) := fun j mu => Set.Finite.mem_toFinset _
  obtain ⟨x, hx⟩ := IsPrecomplete.prec (I := maximalIdeal (Φ.V y)) (M := Φ.V y) inferInstance
    (f := fun j => ∑ mu ∈ S j, Φ.term y mu c) (by
      intro m n hmn
      have hsub : S m ⊆ S n := fun mu hmu => by
        rw [hS] at hmu ⊢; exact ⟨hmu.1, hmu.2.trans_le (by exact_mod_cast hmn)⟩
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, ← Finset.sum_sdiff hsub, sub_add_cancel_right]
      refine neg_mem (Ideal.sum_mem _ fun mu hmu => ?_)
      obtain ⟨p, p'⟩ := Finset.mem_sdiff.1 hmu
      refine term_mem Φ y mu c m ?_
      by_contra h
      exact p' ((hS m mu).2 ⟨((hS n mu).1 p).1, by omega⟩))
  refine ⟨x, fun j => ⟨S j, fun mu h => ((hS j mu).1 h).1, fun mu h hn => ?_, ?_⟩⟩
  · by_contra h'
    exact hn ((hS j mu).2 ⟨h, by omega⟩)
  · have := (hx j).symm
    rwa [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at this

def lim (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (c : Φ.Q) : Φ.V y := (exists_sum Φ y P c).choose

theorem isClassSum_lim (y : Φ.Y) (N : ℕ) (κ : Fin s → Φ.X y) (c : Φ.Q) :
    Φ.IsClassSum y N κ c (RingHom.id _) (lim Φ y (fun mu => ∀ v, CongMod N (mu v) (κ v)) c) :=
  (exists_sum Φ y _ c).choose_spec
end

theorem tate_exact (N : ℕ) : VSys.tate.pre.Exact N := fun y κ c => ⟨_, isClassSum_lim _ y N κ c⟩

theorem tate_classSums (N₁ : ℕ) (hN : 1 ≤ N₁) : VSys.tate.pre.ClassSums N₁ := by
  intro y₀ N₀
  let A := PowerSeries ℚ
  let L := FractionRing A
  have hbij : Function.Bijective (algebraMap A (integralClosure A L)) := by
    refine ⟨fun a b h => IsFractionRing.injective A L (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨a, ha⟩ := (IsIntegrallyClosed.isIntegral_iff (R := A) (K := L)).1 x.2
    exact ⟨a, Subtype.ext ha⟩
  let E : A ≃+* integralClosure A L := RingEquiv.ofBijective _ hbij
  let M := N₁ * (N₀ + 1)
  refine ⟨M, by show N₀ ≤ N₁ * (N₀ + 1); nlinarith, by show 1 ≤ N₁ * (N₀ + 1); nlinarith, dvd_mul_right _ _, fun _ => (LinearMap.id : ℤ →ₗ[ℤ] ℤ), rfl,
    fun _ => ⟨fun c x => ⟨0, by rw [smul_zero, add_zero]; rfl⟩, LinearEquiv.refl ℤ ℤ, by
      show _ ∣ LinearMap.det ((LinearEquiv.refl ℤ ℤ).toLinearMap ∘ₗ (LinearMap.id : ℤ →ₗ[ℤ] ℤ)) - 1
      simp⟩,
    L, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
    (maximalIdeal A).comap E.symm.toRingHom,
    fun κ c => E (lim VSys.tate.pre y₀ (fun mu => ∀ v, CongMod M (mu v) (κ v)) c),
    Ideal.comap_isMaximal_of_surjective _ E.symm.surjective, ?_, ?_, ?_⟩
  · intro κ κ' c h
    have hP : (fun mu : Fin 1 → VSys.tate.pre.X y₀ => ∀ v, CongMod M (mu v) (κ v)) =
        (fun mu => ∀ v, CongMod M (mu v) (κ' v)) := by
      funext mu
      refine propext (forall_congr' fun u => ⟨fun h' => GlobalTheory.Poinc.OrbTrace.cm_trans h' (h u),
        fun h' => GlobalTheory.Poinc.OrbTrace.cm_trans h' (GlobalTheory.Poinc.OrbTrace.cm_symm (h u))⟩)
    show E (lim _ _ _ c) = E (lim _ _ _ c)
    rw [hP]
  · intro y
    refine ⟨VSys.tate.pre.V y, inferInstance, inferInstance, RingHom.id _, (E.symm.toRingHom : integralClosure A L →+* VSys.tate.pre.V y),
      RingHom.Finite.id _, inferInstance, fun I => by rw [Ideal.map_id, Ideal.comap_id], RingHom.ext fun a => E.symm_apply_apply a, rfl,
      fun κ c => ?_⟩
    obtain rfl : y = y₀ := rfl
    have key := isClassSum_lim VSys.tate.pre y M κ c
    have e : (E.symm (E (lim VSys.tate.pre y (fun mu => ∀ v, CongMod M (mu v) (κ v)) c)) : VSys.tate.pre.V y) =
        lim VSys.tate.pre y (fun mu => ∀ v, CongMod M (mu v) (κ v)) c := E.symm_apply_apply _
    exact (congrArg (VSys.tate.pre.IsClassSum y M κ c (RingHom.id _)) e).mpr key
  · intro σ _
    refine ⟨(LinearMap.id : ℤ →ₗ[ℤ] ℤ), fun c (x : ℤ) => (⟨0, by simp⟩ : CongMod _ (c • x) (c • x)),
      (by simp : ((M : ℕ) : ℤ) ∣ LinearMap.det (LinearMap.id : ℤ →ₗ[ℤ] ℤ) - 1),
      fun (x : ℤ) => (⟨0, by simp⟩ : CongMod N₁ x x), fun κ c => σ.commutes _⟩

def const : VPre (O := ℤ) id 1 !![1] ℚ :=
  { posW := VSys.tate.posW, Y := PUnit, V := fun _ => PowerSeries ℚ, cn := fun y => VSys.tate.cn y
    ev := fun _ => PowerSeries.C
    ev_loc := fun _ => ⟨fun a ha => by
      rcases eq_or_ne a 0 with rfl | h
      · simp at ha
      · exact h.isUnit⟩
    X := fun _ => ℤ, rank_le := fun _ => by simp, m := fun _ => 1, t := fun _ _ => PowerSeries.X
    t_mem := fun y => VSys.tate.t_mem y, δ := fun _ _ => LinearMap.mul ℤ ℤ, bal := fun y => VSys.tate.bal y
    nonneg := fun y => VSys.tate.nonneg y, pos := fun y => VSys.tate.pos y, Q := Unit, u := fun _ _ _ => 1
    u_unit := fun _ _ => ⟨(), isUnit_one⟩ }

def cpt : const.Y := PUnit.unit

def toZ (x : const.X cpt) : ℤ := x

theorem not_lam : ¬ const.abelian₂ := by
  rintro ⟨C, hC⟩
  obtain ⟨h, hh, hd⟩ := hC cpt rfl (0 : Fin 1) (show const.X cpt from (1 : ℤ)) (one_ne_zero : (1 : ℤ) ≠ 0)
  have h0 : h = 0 := by rwa [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at hh
  subst h0
  rw [map_zero, zero_dvd_iff] at hd
  exact pow_ne_zero _ (PowerSeries.X_ne_zero (R := ℚ)) hd

theorem not_exact : ¬ const.Exact 3 := by
  classical
  intro hE
  let κ : Fin 1 → const.X cpt := fun _ => show const.X cpt from (1 : ℤ)
  obtain ⟨h, hh⟩ := hE cpt κ ()
  obtain ⟨S, a1, a2, a3⟩ := hh 2
  have hone : κ ∈ S := by
    by_contra hn
    have h2 := a2 κ (fun _ => ⟨0, by simp⟩) hn
    have h3 : ∑ i : Fin (const.m cpt), qW !![1] (const.δ cpt i) κ = 1 := by
      show ∑ i : Fin 1, qW !![1] (LinearMap.mul ℤ ℤ) (fun _ => (1 : ℤ)) = 1
      simp [qW]
    omega
  have a4 : const.ev cpt h - ∑ mu ∈ S, const.term cpt mu () ∈ maximalIdeal (const.V cpt) ^ 2 := a3
  rw [← Finset.add_sum_erase _ _ hone] at a4
  have a5 : ∑ mu ∈ S.erase κ, const.term cpt mu () ∈ maximalIdeal (const.V cpt) ^ 2 := by
    refine Ideal.sum_mem _ fun mu hmu => term_mem const cpt mu () 2 ?_
    obtain ⟨p, p'⟩ := Finset.mem_erase.1 hmu
    obtain ⟨w, hw⟩ := a1 mu p' (0 : Fin 1)
    have hw' : toZ (mu 0) = 1 + 3 * toZ w := by
      have : toZ (mu 0) = (1 : ℤ) + (3 : ℕ) • toZ w := hw
      rw [this, nsmul_eq_mul]; push_cast; ring
    have hw0 : toZ w ≠ 0 := by
      intro h0
      apply p
      funext a
      rw [Subsingleton.elim a 0]
      show toZ (mu 0) = 1
      rw [hw', h0]; ring
    show ((2 : ℕ) : ℤ) ≤ ∑ i : Fin 1, qW !![1] (LinearMap.mul ℤ ℤ) (fun v => toZ (mu v))
    simp only [Finset.univ_unique, Finset.sum_singleton, qW_mul]
    rw [hw']
    push_cast
    rcases lt_or_gt_of_ne hw0 with h | h <;> nlinarith
  have a6 : const.term cpt κ () = (show const.V cpt from PowerSeries.X) := by
    show (1 : PowerSeries ℚ) * mono !![1] (fun _ : Fin 1 => PowerSeries.X) (fun _ => LinearMap.mul ℤ ℤ) (fun _ => (1 : ℤ)) = PowerSeries.X
    simp only [mono, qW]
    simp
    exact (one_mul _).trans ((pow_one _).trans (pow_one _))
  have a7 : const.ev cpt h - (show const.V cpt from PowerSeries.X) ∈ maximalIdeal (const.V cpt) ^ 2 := by
    have := add_mem a4 a5
    rw [a6] at this
    convert this using 1
    ring
  change (PowerSeries.C h : PowerSeries ℚ) - PowerSeries.X ∈ maximalIdeal (PowerSeries ℚ) ^ 2 at a7
  have a8 : (PowerSeries.C h - PowerSeries.X : PowerSeries ℚ) ∈ Ideal.span {PowerSeries.X ^ 2} := by
    rw [← Ideal.span_singleton_pow, ← PowerSeries.maximalIdeal_eq_span_X]; exact a7
  rw [Ideal.mem_span_singleton, PowerSeries.X_pow_dvd_iff] at a8
  simpa [PowerSeries.coeff_C] using a8 1 (by norm_num)

end GlobalTheory.Poinc.PreModel
