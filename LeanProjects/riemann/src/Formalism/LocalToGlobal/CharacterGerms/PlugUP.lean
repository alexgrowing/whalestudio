import Formalism.LocalToGlobal.CharacterGerms.CharacteristicFromRanks
import ReciprocityTheory.DualLattices.LengthDegreeAbelianVariety
import ReciprocityTheory.DualLattices.U10
import ReciprocityTheory.DualLattices.KilledGen
import ReciprocityTheory.DualLattices.IdemGen
import ReciprocityTheory.DualLattices.LenEx
import Formalism.SharpRestriction.GrowthBounds.FittingIdeal.DetMulMemFitt0

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace ValuationFitting

open ReciprocityTheory.PGsh.Up CharacteristicFromRanks

variable {C : Type} [Field C]

instance factL (V : VF C) : Fact V.l.Prime := ⟨V.l_prime⟩

def ValTie (V : VF C) (vm : Valuation C NNReal) : Prop :=
  ∀ x : C, x ≠ 0 → ∃ t : ℝ, V.v x = (t : WithTop ℝ) ∧ (vm x : ℝ) = (vm (V.l : C) : ℝ) ^ t

structure Comparison₂ {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H) where
  val : ValTie V vm
  ix : Fin 2 → ZMod d → Fin U.m
  ix_frob : ∀ g a, U.φ (ix g a) = ix g (a + 1)
  ix_conj : ∀ g a, U.cj (ix g a) = ix (1 - g) a
  rank : ∀ g a, U.r (ix g a) + rh = pT G g a
  e : ∀ g a, Fin (pT G g a) ≃ {x : I g // (G g).ty (Sum.inl x) = a}
  αR : ∀ g a, Matrix (Fin (pT G g a)) (Fin (h g)) R
  αR_eq : ∀ g a c i, algebraMap R C (αR g a c i) = ht g i (e g a c)
  bad : ∀ g a, big g a → Nonempty (cokE H.Ht U.εT U.εL (ix g a) (U.cj (ix g a)) ≃ₗ[R]
    ((Fin (pT G g a) → R) ⧸ LinearMap.range (αR g a).mulVecLin))

def FittGe : Prop :=
  ∀ (C : Type) [Field C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C],
    v.Integers R → ∀ (m h : ℕ) (α : Matrix (Fin m) (Fin h) R) (x : NNReal),
    HasLen v R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x →
    ∃ y ∈ S4.fitt0 α, v (algebraMap R C y) = x

section Val

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

def vA (V : VF C) (R : Type) [CommRing R] [Algebra R C] : AddValuation R (WithTop ℝ) :=
  V.v.comap (algebraMap R C)

theorem vA_apply (x : R) : vA V R x = V.v (algebraMap R C x) := rfl

theorem vA_nonneg (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) : ∀ x : R, 0 ≤ vA V R x := by
  intro x
  rw [vA_apply]
  by_cases hx : algebraMap R C x = 0
  · rw [hx, V.v.map_zero]; exact le_top
  · obtain ⟨t, ht1, ht2⟩ := hT _ hx
    rw [ht1]
    have hle : (vm (algebraMap R C x) : ℝ) ≤ 1 := by exact_mod_cast hv.map_le_one x
    have : 0 ≤ t := by
      by_contra hneg
      have := Real.one_lt_rpow_of_pos_of_lt_one_of_neg h0 h1 (not_le.mp hneg)
      rw [← ht2] at this
      linarith
    exact_mod_cast this

theorem lenCoker_vA {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) :
    S4.lenCoker (vA V R) α = S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) := by
  unfold S4.lenCoker
  congr 1
  funext g
  rw [vA_apply, RingHom.map_det]
  rfl

end Val

theorem pow_frob {m : ℕ} {d : ℕ} (φ : Equiv.Perm (Fin m)) (ix : ZMod d → Fin m)
    (hφ : ∀ a, φ (ix a) = ix (a + 1)) (a : ZMod d) : ∀ k : ℕ, (φ ^ k) (ix a) = ix (a + (k : ZMod d))
  | 0 => by simp
  | k + 1 => by
    rw [pow_succ', Equiv.Perm.mul_apply, pow_frob φ ix hφ a k, hφ]
    congr 1
    push_cast
    ring

theorem rpow_neg_succ {l : ℕ} (hl : 0 < l) (n : ℕ) :
    (l : ℝ) ^ (-((n : ℝ) + 1)) = ((l : ℝ) ^ (n + 1))⁻¹ := by
  have h0 : (0 : ℝ) ≤ l := by positivity
  rw [Real.rpow_neg h0, ← Nat.cast_succ, Real.rpow_natCast]

theorem lenCoker_le (hF : FittGe) [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ}
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh r : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (l_odd : V.l ≠ 2)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) (g : Fin 2) (a : ZMod d) (ha : big g a)
    (hr : pT G (1 - g) a + pT G g a = r) :
    S4.lenCoker V.v (Matrix.of fun c i => ht g i (T.e g a c)) ≤
      (((pT G g a : ℝ) / ((V.l : ℝ) - 1) - S4.frobSum V.l (pT G g) a +
        ((r : ℝ) - pT G g a - rh) / ((V.l : ℝ) - 1) : ℝ) : WithTop ℝ) := by
  obtain ⟨E⟩ := T.bad g a ha
  obtain ⟨V1, hV1⟩ := lenEx C vm R hS.integers gB H.Ht (U.εL (T.ix g a)) (U.εT (U.cj (T.ix g a)))
  have hN : HasLen vm R ((Fin (pT G g a) → R) ⧸ LinearMap.range (T.αR g a).mulVecLin) V1 :=
    hasLen_of_equiv E.symm hV1
  have hrc : (((fun j => U.r j + rh) (U.cj (T.ix g a)) : ℕ) : ℝ) =
      (r : ℝ) - ((fun j => U.r j + rh) (T.ix g a) : ℕ) := by
    show ((U.r (U.cj (T.ix g a)) + rh : ℕ) : ℝ) = (r : ℝ) - ((U.r (T.ix g a) + rh : ℕ) : ℝ)
    rw [T.ix_conj, T.rank, T.rank, ← hr]
    push_cast
    ring
  have hb := up_shift u7 V.l gB C vm R O σ cp l_odd hS H U (T.ix g a) rh r
    (fun j => U.r j + rh) (fun _ => rfl) hrc _ E V1 hN
  have hcast : algebraMap R C ((V.l : ℕ) : R) = (V.l : C) := map_natCast _ _
  have hb0 : 0 < (vm (V.l : C) : ℝ) := by
    rw [← hcast]; exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 hS.p_ne)
  have hb1 : (vm (V.l : C) : ℝ) < 1 := by
    rw [← hcast]; exact_mod_cast hS.p_lt
  have hsum : (∑' n : ℕ, (V.l : ℝ) ^ (-((n : ℝ) + 1)) *
      (((fun j => U.r j + rh) ((U.φ ^ (n + 1)) (T.ix g a)) : ℕ) : ℝ)) =
      S4.frobSum V.l (pT G g) a := by
    unfold S4.frobSum
    refine tsum_congr fun n => ?_
    rw [pow_frob U.φ (T.ix g) (T.ix_frob g) a (n + 1), rpow_neg_succ V.l_prime.pos]
    show _ * ((U.r (T.ix g (a + ((n + 1 : ℕ) : ZMod d))) + rh : ℕ) : ℝ) = _
    rw [T.rank]
  have hri : (((fun j => U.r j + rh) (T.ix g a) : ℕ) : ℝ) = (pT G g a : ℝ) := by
    show ((U.r (T.ix g a) + rh : ℕ) : ℝ) = _
    rw [T.rank]
  rw [hsum, hri, hcast] at hb
  obtain ⟨y, hy, hyV⟩ := hF C vm R hS.integers _ _ (T.αR g a) V1 hN
  have hpos : 0 < (V1 : ℝ) := lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) hb
  have hy0 : algebraMap R C y ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hyV
    rw [← hyV] at hpos
    simp at hpos
  obtain ⟨t, ht1, ht2⟩ := T.val _ hy0
  rw [← hyV, ht2, Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hb1] at hb
  have hmat : (Matrix.of fun c i => ht g i (T.e g a c)) =
      Matrix.of fun c i => algebraMap R C (T.αR g a c i) := by
    ext c i
    exact (T.αR_eq g a c i).symm
  rw [hmat, ← lenCoker_vA]
  refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg T.val hS.integers hb0 hb1) _ hy) ?_
  rw [vA_apply, ht1]
  exact_mod_cast hb

theorem CH_of_HTD_of (hF : FittGe) [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ} [NeZero d]
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ) (r_eq : r = n + j + j')
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (l_odd : V.l ≠ 2) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U)
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  have hl1 : 1 < V.l := V.l_prime.one_lt
  have hL : (1 : ℝ) < V.l := by exact_mod_cast hl1
  have hL1 : (0 : ℝ) < (V.l : ℝ) - 1 := by linarith
  have h1 := S4.one_div_eq_gam_add_rho hl1
  have hdiv : ∀ x : ℝ, x / ((V.l : ℝ) - 1) = x * (S4.gam V.l + S4.rho V.l) := fun x => by
    rw [← h1]; ring
  have hgr : 0 ≤ S4.gam V.l + S4.rho V.l := by rw [← h1]; positivity
  have hrh : 0 ≤ (rh : ℝ) * (S4.gam V.l + S4.rho V.l) := mul_nonneg (Nat.cast_nonneg _) hgr
  refine CH_of_UP G n j j' big big_compl h ht ht_int (fun g a ha => ⟨T.e g a, fun hA => ?_,
    fun hB => ?_⟩) hGerm
  · have hr : pT G (1 - g) a + pT G g a = r := by
      rw [rk_big g a ha, rk_small (1 - g) a (fun hh => (big_compl g a).mp hh ha), r_eq]; ring
    refine le_trans (lenCoker_le hF G big rh r h ht l_odd vm R O σ cp gB hS H U T g a ha hr)
      (WithTop.coe_le_coe.mpr ?_)
    rw [S4.frobSum_alt hl1 n j j' (big g) (alt_step big big_compl hA g) (pT G g) (rk_big g)
      (rk_small g) a ha, rk_big g a ha, r_eq]
    have hg : gam V.l = S4.gam V.l := rfl
    unfold upB
    rw [hg]
    simp only [hdiv]
    push_cast
    linarith
  · have hr : pT G (1 - g) a + pT G g a = r := by
      rw [rk_big g a ha, rk_small (1 - g) a (fun hh => (big_compl g a).mp hh ha), r_eq]; ring
    refine le_trans (lenCoker_le hF G big rh r h ht l_odd vm R O σ cp gB hS H U T g a ha hr)
      (WithTop.coe_le_coe.mpr ?_)
    rw [S4.frobSum_const hl1 (n + j) (pT G g) (fun τ => rk_big g τ (hB τ)) a, rk_big g a ha, r_eq]
    unfold upB
    simp only [hdiv]
    push_cast
    linarith

theorem fittGe : FittGe := fun _ _ _ _ _ _ hv _ _ α _ hx => Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx

theorem CH_of_HTD [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ} [NeZero d]
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ) (r_eq : r = n + j + j')
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (l_odd : V.l ≠ 2) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U)
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big :=
  CH_of_HTD_of fittGe G n j j' rh r r_eq big big_compl rk_big rk_small l_odd h ht ht_int vm R O σ cp
    gB hS H U T hGerm

section Val2

variable {V : VF C} {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C]

theorem lenCoker_eq_logb (hT : ValTie V vm) (hv : vm.Integers R) (h0 : 0 < (vm (V.l : C) : ℝ))
    (h1 : (vm (V.l : C) : ℝ) < 1) {m h : ℕ} (α : Matrix (Fin m) (Fin h) R) {x : NNReal}
    (hx : HasLen vm R ((Fin m → R) ⧸ LinearMap.range α.mulVecLin) x) (hpos : 0 < (x : ℝ)) :
    S4.lenCoker V.v (Matrix.of fun i k => algebraMap R C (α i k)) =
      ((Real.logb (vm (V.l : C) : ℝ) x : ℝ) : WithTop ℝ) := by
  have hxb : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x = x :=
    Real.rpow_logb h0 (ne_of_lt h1) hpos
  rw [← lenCoker_vA]
  apply le_antisymm
  · obtain ⟨y, hy, hyV⟩ := Formalism.MainNotions.G.ValuationFitting.fitt_ge hv α hx
    have hy0 : algebraMap R C y ≠ 0 := by
      intro hz
      rw [hz, map_zero] at hyV
      rw [← hyV] at hpos
      simp at hpos
    obtain ⟨t, ht1, ht2⟩ := hT _ hy0
    refine le_trans (S4.lenCoker_le_of_mem (vA V R) (vA_nonneg hT hv h0 h1) _ hy) ?_
    rw [vA_apply, ht1]
    have : (vm (V.l : C) : ℝ) ^ Real.logb (vm (V.l : C) : ℝ) x ≤ (vm (V.l : C) : ℝ) ^ t := by
      rw [hxb, ← ht2, hyV]
    rw [Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at this
    exact_mod_cast this
  · unfold S4.lenCoker
    refine Finset.le_inf fun g _ => ?_
    rw [vA_apply]
    by_cases hz : algebraMap R C (α.submatrix id g).det = 0
    · rw [hz, V.v.map_zero]; exact le_top
    · obtain ⟨t, ht1, ht2⟩ := hT _ hz
      rw [ht1]
      have hle : (vm (algebraMap R C (α.submatrix id g).det) : ℝ) ≤ x := by
        exact_mod_cast Formalism.MainNotions.G.ValuationFitting.fitt_le hv α hx g
      rw [ht2, ← hxb, Real.rpow_le_rpow_left_iff_of_base_lt_one h0 h1] at hle
      exact_mod_cast hle

end Val2

theorem frobSum_shift {V : VF C} {d : ℕ} {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    {G : ∀ g, Cart V d (I g) (J g)} {big : Fin 2 → ZMod d → Prop} {rh : ℕ} {h : Fin 2 → ℕ}
    {ht : ∀ g, Fin (h g) → I g → C}
    {vm : Valuation C NNReal} {R : Type} [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    {O : Type} [CommRing O] [Algebra ℤ_[V.l] O] {σ : O ≃ₐ[ℤ_[V.l]] O} {cp : R} {gB : ℕ}
    {H : HodgeTateDatum V.l gB vm R O σ cp} {U : UnramData V.l gB vm R O σ cp H}
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) (g : Fin 2) (a : ZMod d) :
    ReciprocityTheory.PGsh.Up.frobSum U (T.ix g a) =
      S4.frobSum V.l (pT G g) a - (rh : ℝ) / ((V.l : ℝ) - 1) := by
  obtain ⟨B, hB⟩ : ∃ B : ℝ, ∀ k : Fin U.m, ((U.r k + rh : ℕ) : ℝ) ≤ B :=
    ⟨∑ k, ((U.r k + rh : ℕ) : ℝ), fun k => Finset.single_le_sum
      (f := fun k => ((U.r k + rh : ℕ) : ℝ)) (fun k _ => Nat.cast_nonneg _) (Finset.mem_univ k)⟩
  have hsG := summable_geom_p (p := V.l)
    (fun n => ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ))
    (fun n => Nat.cast_nonneg _) B (fun n => hB _)
  have hsρ := summable_geom_p (p := V.l) (fun _ => (rh : ℝ)) (fun _ => Nat.cast_nonneg _) rh
    (fun _ => le_rfl)
  have hsum : (∑' n : ℕ, (V.l : ℝ) ^ (-((n : ℝ) + 1)) *
      ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ)) = S4.frobSum V.l (pT G g) a := by
    unfold S4.frobSum
    refine tsum_congr fun n => ?_
    rw [pow_frob U.φ (T.ix g) (T.ix_frob g) a (n + 1), rpow_neg_succ V.l_prime.pos, T.rank]
  unfold ReciprocityTheory.PGsh.Up.frobSum
  have e1 : ∀ n : ℕ, (V.l : ℝ) ^ (-((n : ℝ) + 1)) * (U.r ((U.φ ^ (n + 1)) (T.ix g a)) : ℝ) =
      (V.l : ℝ) ^ (-((n : ℝ) + 1)) * ((U.r ((U.φ ^ (n + 1)) (T.ix g a)) + rh : ℕ) : ℝ) -
        (V.l : ℝ) ^ (-((n : ℝ) + 1)) * rh := by
    intro n; push_cast; ring
  simp_rw [e1]
  rw [Summable.tsum_sub hsG hsρ, tsum_mul_right, tsum_geom_p, hsum]
  ring

theorem rank_inputs_of_hodge_tate [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ}
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    (G : ∀ g, Cart V d (I g) (J g)) (big : Fin 2 → ZMod d → Prop) (rh r : ℕ) (h : Fin 2 → ℕ)
    (ht : ∀ g, Fin (h g) → I g → C) (l_odd : V.l ≠ 2)
    (hr : ∀ g a, big g a → pT G (1 - g) a + pT G g a = r)
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U) :
    ∃ l1 l2 : Fin 2 → ZMod d → ℝ,
      (∀ g a, big g a → S4.CorDET V.l (pT G g) (l1 g) (l2 g) a) ∧
      (∀ g a, big g a → S4.ThmAi V.l r rh (pT G g) (l2 g) a) ∧
      (∀ g a, big g a → S4.ThmAiii V.v (Matrix.of fun c i => ht g i (T.e g a c)) (l1 g a)) := by
  have hcast : algebraMap R C ((V.l : ℕ) : R) = (V.l : C) := map_natCast _ _
  have hb0 : 0 < (vm (V.l : C) : ℝ) := by
    rw [← hcast]; exact NNReal.coe_pos.2 (pos_iff_ne_zero.2 hS.p_ne)
  have hb1 : (vm (V.l : C) : ℝ) < 1 := by
    rw [← hcast]; exact_mod_cast hS.p_lt
  have hL : (1 : ℝ) < V.l := by exact_mod_cast V.l_prime.one_lt
  have hL1 : (V.l : ℝ) - 1 ≠ 0 := by linarith
  have ex1 := fun (g : Fin 2) (a : ZMod d) =>
    lenEx C vm R hS.integers gB H.Ht (U.εL (T.ix g a)) (U.εT (U.cj (T.ix g a)))
  have ex2 := fun (g : Fin 2) (a : ZMod d) =>
    lenEx C vm R hS.integers gB H.Ht (U.εL (U.cj (T.ix g a))) (U.εT (T.ix g a))
  choose W1 hW1 using ex1
  choose W2 hW2 using ex2

  have hA : ∀ g a, (vm (V.l : C) : ℝ) ^ ((U.r (U.cj (T.ix g a)) : ℝ) / ((V.l : ℝ) - 1)) ≤
      (W2 g a : ℝ) := by
    intro g a
    have hidem : U.εL (U.cj (T.ix g a)) * U.εL (U.cj (T.ix g a)) = U.εL (U.cj (T.ix g a)) := by
      rw [U.εL_orth, if_pos rfl]
    obtain ⟨y, hy⟩ := idemGen R gB _ _ hidem (U.rank (U.cj (T.ix g a)))
    have hkg := killedGen C vm R hS.integers _ (W2 g a) _ cp (hW2 g a) ⟨_, span_mk_top _ y hy⟩
      (up_kill hS H U (T.ix g a))
    rw [← hcast, vp_rpow hS]
    exact_mod_cast hkg
  have hW2pos : ∀ g a, 0 < (W2 g a : ℝ) := fun g a =>
    lt_of_lt_of_le (Real.rpow_pos_of_pos hb0 _) (hA g a)
  have h7 : ∀ g a, (W1 g a : ℝ) = W2 g a * (vm (V.l : C) : ℝ) ^
      ((U.r (T.ix g a) : ℝ) / ((V.l : ℝ) - 1) - ReciprocityTheory.PGsh.Up.frobSum U (T.ix g a)) := by
    intro g a
    have := u7 V.l gB C vm R O σ cp l_odd hS H U (T.ix g a) (W1 g a) (W2 g a) (hW1 g a) (hW2 g a)
    rwa [hcast] at this
  have hW1pos : ∀ g a, 0 < (W1 g a : ℝ) := fun g a => by
    rw [h7]; exact mul_pos (hW2pos g a) (Real.rpow_pos_of_pos hb0 _)
  have hrk : ∀ g a, (U.r (T.ix g a) : ℝ) = (pT G g a : ℝ) - rh := fun g a => by
    rw [← T.rank g a]; push_cast; ring
  refine ⟨fun g a => Real.logb (vm (V.l : C) : ℝ) (W1 g a),
    fun g a => Real.logb (vm (V.l : C) : ℝ) (W2 g a), fun g a _ => ?_, fun g a ha => ?_,
    fun g a ha => ?_⟩
  · unfold S4.CorDET
    show Real.logb _ (W1 g a : ℝ) - Real.logb _ (W2 g a : ℝ) = _
    rw [h7, Real.logb_mul (ne_of_gt (hW2pos g a)) (ne_of_gt (Real.rpow_pos_of_pos hb0 _)),
      Real.logb_rpow hb0 (ne_of_lt hb1), frobSum_shift T g a, hrk]
    field_simp
    ring
  · unfold S4.ThmAi
    show Real.logb _ (W2 g a : ℝ) ≤ _
    have h2 := hA g a
    rw [← Real.rpow_logb hb0 (ne_of_lt hb1) (hW2pos g a),
      Real.rpow_le_rpow_left_iff_of_base_lt_one hb0 hb1, T.ix_conj, hrk] at h2
    refine le_trans h2 (le_of_eq ?_)
    congr 1
    rw [← hr g a ha]
    push_cast
    ring
  · unfold S4.ThmAiii
    obtain ⟨E⟩ := T.bad g a ha
    have hN : HasLen vm R ((Fin (pT G g a) → R) ⧸ LinearMap.range (T.αR g a).mulVecLin) (W1 g a) :=
      hasLen_of_equiv E.symm (hW1 g a)
    have hmat : (Matrix.of fun c i => ht g i (T.e g a c)) =
        Matrix.of fun c i => algebraMap R C (T.αR g a c i) := by
      ext c i
      exact (T.αR_eq g a c i).symm
    rw [hmat]
    exact lenCoker_eq_logb T.val hS.integers hb0 hb1 _ hN (hW1pos g a)

theorem chart_hypothesis_of_hodge_tate [IsAlgClosed C] [CharZero C] {V : VF C} {d : ℕ} [NeZero d]
    {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
    (G : ∀ g, Cart V d (I g) (J g)) (n j j' rh r : ℕ) (r_eq : r = n + j + j')
    (big : Fin 2 → ZMod d → Prop) (big_compl : ∀ g a, big (1 - g) a ↔ ¬ big g a)
    (rk_big : ∀ g a, big g a → pT G g a = n + j)
    (rk_small : ∀ g a, ¬ big g a → pT G g a = j')
    (rk_fil : ∀ g a, (Finset.univ.filter fun κ : J g => (G g).ty (Sum.inr κ) = a).card + rh +
      pT G g a = r)
    (l_odd : V.l ≠ 2) (h : Fin 2 → ℕ) (hh : ∀ g, h g + rh = r)
    (ht : ∀ g, Fin (h g) → I g → C) (ht_int : ∀ g i x, V.Ge 0 (ht g i x))
    (vm : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C] [Algebra ℤ_[V.l] R]
    (O : Type) [CommRing O] [Algebra ℤ_[V.l] O] (σ : O ≃ₐ[ℤ_[V.l]] O) (cp : R) (gB : ℕ)
    (hS : HodgeTateSetting V.l vm R O σ cp)
    (H : HodgeTateDatum V.l gB vm R O σ cp) (U : UnramData V.l gB vm R O σ cp H)
    (T : Comparison₂ G big rh h ht vm R O σ cp gB H U)
    (hGerm : ∀ g (i : Fin (h g)) (S : ∀ g, Sys (G g)) (t : ∀ g, I g → MvPowerSeries (I g) C),
      (∀ g, (S g).IsT (t g)) →
      upG g (mvExp (∑ x : I g, ht g i x • (MvPowerSeries.X x : MvPowerSeries (I g) C))) ∈
        IntGerm V t) :
    CHProp G n j j' big := by
  obtain ⟨l1, l2, hD, hAi, hAiii⟩ := rank_inputs_of_hodge_tate G big rh r h ht l_odd
    (fun g a ha => by
      rw [rk_big g a ha, rk_small (1 - g) a (fun hh => (big_compl g a).mp hh ha), r_eq]; ring)
    vm R O σ cp gB hS H U T
  exact characteristic_of_rank_split G n j j' rh r r_eq big big_compl rk_big rk_small rk_fil l_odd h hh ht ht_int l1 l2
    hD hAi (fun g a ha => ⟨T.e g a, hAiii g a ha⟩) hGerm

end ValuationFitting

end Formalism.L2.FormalSeriesBounds
