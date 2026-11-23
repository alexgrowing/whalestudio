import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamEqZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsFamRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExistsCeil

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing QForm

def RepsXSt : Prop := ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (k : ℕ), 1 ≤ k →
    ∃ rep : (Fin (Module.finrank ℤ X) → Fin k) → X,
      (∀ χ : X, ∃ a mu, rep a + k • mu = χ) ∧
      (∀ a a' (mu mu' : X), rep a + k • mu = rep a' + k • mu' → a = a') ∧
      (∀ x y : X, k • x = k • y → x = y)

def CeilSt : Prop := ∀ (F : Type) [Field F] (v : AddValuation F (WithTop ℚ)) (π : F), v π = 1 →
    (IsAlgClosed F ∨ ∃ d : ℕ, 1 ≤ d ∧ ∀ x : F, x ≠ 0 → ∃ n : ℤ, v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) →
    ∀ q : ℚ, ∃ l : F, l ≠ 0 ∧ ∀ x : F, (((q : ℚ) : WithTop ℚ) ≤ v x ↔ v l ≤ v x)

theorem uu_of (hG : GlobalFnsSt) (hT : TwistBaseChangeStatement) (hR : RepsXSt) (hC : CeilSt) : UUStatement := by
  intro V _ _ _ ϖ hϖ D Q hQ F _ _ v hv hF k hk
  classical
  have hL := D.toPre.P.isLB
  obtain ⟨rep, hcov, hdis, hinj⟩ := hR D.toPre.X k hk
  have hπ : v (algVF (F := F) ϖ) = 1 := by
    have e := hv (algebraMap V (FractionRing V) ϖ) 1 ⟨1, by simp⟩
    simpa [algVF] using e
  choose lam hlam0 hlam using fun a => hC F v (algVF ϖ) hπ hF ((Q (rep a) : ℚ) / k)
  have exb : ∀ a, ∃ b : Fin (k ^ D.toPre.P.g) → D.toPre.SecB k (rep a),
      ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin (k ^ D.toPre.P.g) → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre (rep a) i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre (rep a)) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b' := fun a => by
    obtain ⟨m, b, hm, hb⟩ := hT V D.toPre k hk (rep a)
    subst hm
    exact ⟨b, hb⟩
  choose b hb using exb
  have exF : ∀ a i, ∃ t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F (rep a)) (DegPre.famε k)),
      ∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        sval t (𝟙 _) y J = sval (b a i) (DegPre.prB D.toPre F).left y J := fun a i => by
    obtain ⟨t, ht⟩ := exists_sec hL (hformF k (rep a))
      (pullSec D.toPre.P.L (DegPre.famφB D.toPre (rep a)) (DegPre.famε k) (b a i) (DegPre.prB D.toPre F).left)
    exact ⟨t, fun y J hJ => (ht _ (𝟙 _) y J hJ).trans ((sval_pullSec _ _ _ _ _ y hJ).trans (by rw [Category.id_comp]))⟩
  choose bF hbF using exF
  have hEU := fun a => coordsF (b a) (hb a) (bF a) (hbF a)
  have hcls : ∀ a (x y : D.toPre.X), rep a + k • x = rep a + k • y → x = y := fun a x y e => hinj x y (add_left_cancel e)
  choose Fm hFm0 hFm1 using fun (p : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) =>
    exists_fam_rep (D := D.toPre) (F := F) hG D.tau_bimult k (rep p.1) (hcls p.1) (bF p.1 p.2)
  have hoff : ∀ (p : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) a₀, p.1 ≠ a₀ → ∀ j,
      ((Fm p).s (rep a₀)).f j = 0 := fun p a₀ hne =>
    hFm1 p _ (fun mu e => hne (hdis p.1 a₀ mu 0 (by rw [e, smul_zero, add_zero])))
  have comp : ∀ (c : (Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g) → F) a₀ j,
      ((∑ p, c p • (lam p.1 • Fm p)).s (rep a₀)).f j =
        ∑ i, resTop _ (gF D.toPre F (c (a₀, i) * lam a₀)) * (bF a₀ i).f j := by
    intro c a₀ j
    rw [fam_sum_f, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single a₀ (fun a _ hne => Finset.sum_eq_zero fun i _ => by
      rw [DVR.smul_f, hoff (a, i) a₀ hne j, MulZeroClass.mul_zero, MulZeroClass.mul_zero]) (by simp)]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 := hFm0 (a₀, i)
    dsimp only at h0
    rw [DVR.smul_f, h0, map_mul, resTop, resTop, resTop, map_mul, _root_.mul_assoc]
  have hcard : Fintype.card ((Fin D.toPre.rank → Fin k) × Fin (k ^ D.toPre.P.g)) = k ^ (D.toPre.rank + D.toPre.P.g) := by
    simp [Fintype.card_prod, Fintype.card_fun, pow_add]
  let e := Fintype.equivFinOfCardEq hcard
  let S : Finset D.toPre.X := Finset.univ.image rep
  have hS : ∀ χ : D.toPre.X, ∃ α ∈ S, ∃ m0, χ = α + k • m0 := fun χ => by
    obtain ⟨a, mu, h⟩ := hcov χ
    exact ⟨rep a, Finset.mem_image_of_mem _ (Finset.mem_univ _), mu, h.symm⟩
  have hre : ∀ (c : Fin (k ^ (D.toPre.rank + D.toPre.P.g)) → F),
      ∑ t, c t • (lam (e.symm t).1 • Fm (e.symm t)) = ∑ p, c (e p) • (lam p.1 • Fm p) := fun c => by
    rw [← Equiv.sum_comp e.symm (fun p => c (e p) • (lam p.1 • Fm p))]
    simp only [Equiv.apply_symm_apply]
  have hql : ∀ a, ((((Q (rep a) : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v (lam a) := fun a => ((hlam a (lam a)).2 le_rfl)
  refine ⟨fun t => lam (e.symm t).1 • Fm (e.symm t), ?_, fun t => ?_, fun s => ⟨fun hs => ?_, ?_⟩⟩
  · rw [Fintype.linearIndependent_iff]
    intro g hg t
    rw [hre] at hg
    set p := e.symm t with hp
    have h0 : ∀ j, ((0 : Fam D.toPre F k).s (rep p.1)).f j =
        ∑ i, resTop _ (gF D.toPre F (g (e (p.1, i)) * lam p.1)) * (bF p.1 i).f j := fun j => by
      rw [← comp (fun q => g (e q)) p.1 j, hg]
    have hz := (hEU p.1).2 (fun i => g (e (p.1, i)) * lam p.1) fun y J hJ => by
      have e0 := sval_lin (fun i => gF D.toPre F (g (e (p.1, i)) * lam p.1)) (bF p.1) h0 (𝟙 _) y hJ
      rw [← e0]
      exact sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)
    have := congrFun hz p.2
    simp only [Pi.zero_apply, mul_eq_zero, hlam0, or_false] at this
    rwa [show (p.1, p.2) = p from rfl, hp, Equiv.apply_symm_apply] at this
  · refine (n1a V ϖ hϖ D Q hQ F v hv k hk S hS _ 0).2 fun α hα => ?_
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hα
    rw [zero_add]
    by_cases h : (e.symm t).1 = a₀
    · subst h
      refine ⟨1, fun _ => lam (e.symm t).1, fun _ => b _ (e.symm t).2, fun _ => bF _ (e.symm t).2,
        fun _ => secScal_of_sval hL fun y J hJ => ?_, fun _ => hql _, fun j => ?_⟩
      · rw [Category.id_comp]; exact (hbF _ _ y J hJ).symm
      · rw [Fin.sum_univ_one, DVR.smul_f, hFm0]; rfl
    · exact vge_of_zero (fun j => by rw [DVR.smul_f, hoff _ a₀ h j, MulZeroClass.mul_zero]) _
  · have hs' := (n1a V ϖ hϖ D Q hQ F v hv k hk S hS s 0).1 hs
    choose c hc using fun a => (hEU a).1 (s.s (rep a))
    have hcv : ∀ a i, ((((Q (rep a) : ℚ) / k : ℚ)) : WithTop ℚ) ≤ v (c a i) := fun a =>
      vge_coords hϖ hv (b a) (hb a) (bF a) (hbF a) (hEU a).2 (hc a)
        (by simpa using hs' (rep a) (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
    refine ⟨fun t => c (e.symm t).1 (e.symm t).2 / lam (e.symm t).1, fun t => ?_, ?_⟩
    · obtain ⟨ql, hql'⟩ := wt_coe_of_ne (v := v) (hlam0 (e.symm t).1)
      show (0 : WithTop ℚ) ≤ v (c (e.symm t).1 (e.symm t).2 / lam (e.symm t).1)
      rw [div_eq_mul_inv, AddValuation.map_mul, v_inv_coe (v := v) (hlam0 _) hql']
      have hle := (hlam (e.symm t).1 (c (e.symm t).1 (e.symm t).2)).1 (hcv _ _)
      rw [hql'] at hle
      induction h : v (c (e.symm t).1 (e.symm t).2) using WithTop.recTopCoe with
      | top => simp
      | coe qc =>
        rw [h] at hle
        have : ql ≤ qc := by exact_mod_cast hle
        exact_mod_cast (show (0 : ℚ) ≤ qc + -ql by linarith)
    · rw [hre]
      refine sub_eq_zero.1 (fam_eq_zero hG (fun α => ∃ a, rep a = α) (fun χ => by
        obtain ⟨a, mu, h⟩ := hcov χ; exact ⟨rep a, mu, ⟨a, rfl⟩, h⟩) _ fun α ⟨a₀, ha⟩ j => ?_)
      subst ha
      rw [sub_eq_add_neg, DVR.add_f, DVR.neg_f, comp, chart_of_point hL (s.s (rep a₀)) (fun i => gF D.toPre F (c a₀ i))
        (bF a₀) (hc a₀) j, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Equiv.symm_apply_apply, div_mul_cancel₀ _ (hlam0 a₀), sub_self]
  · rintro ⟨c, hcv, rfl⟩
    refine (n1a V ϖ hϖ D Q hQ F v hv k hk S hS _ 0).2 fun α hα => ?_
    obtain ⟨a₀, -, rfl⟩ := Finset.mem_image.1 hα
    rw [zero_add]
    refine ⟨k ^ D.toPre.P.g, fun i => c (e (a₀, i)) * lam a₀, b a₀, bF a₀,
      fun i => secScal_of_sval hL fun y J hJ => ?_, fun i => ?_, fun j => ?_⟩
    · rw [Category.id_comp]; exact (hbF _ _ y J hJ).symm
    · rw [AddValuation.map_mul]
      calc (((Q (rep a₀) : ℚ) / k : ℚ) : WithTop ℚ) = 0 + (((Q (rep a₀) : ℚ) / k : ℚ) : WithTop ℚ) := (zero_add _).symm
        _ ≤ v (c (e (a₀, i))) + v (lam a₀) := add_le_add (hcv _) (hql a₀)
    · rw [hre, comp]; rfl

private theorem repsX_statement : RepsXSt := by
  intro X _ _ _ k hk
  set b := Module.finBasis ℤ X
  have hk0 : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨fun a => b.equivFun.symm fun i => ((a i : ℕ) : ℤ), ?_, ?_, ?_⟩
  · intro χ
    refine ⟨fun i => ⟨(b.equivFun χ i % k).toNat, ?_⟩, b.equivFun.symm fun i => b.equivFun χ i / k, ?_⟩
    · have h1 := Int.emod_nonneg (b.equivFun χ i) hk0.ne'
      have h2 := Int.emod_lt_of_pos (b.equivFun χ i) hk0
      omega
    · apply b.equivFun.injective
      ext i
      simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hk0.ne')]
      first
        | exact Int.emod_add_mul_ediv _ _
        | exact Int.emod_add_ediv _ _
        | (rw [Int.emod_def]; ring)
        | (have := Int.mul_ediv_add_emod (b.equivFun χ i) (k : ℤ); linarith)
  · intro a a' mu mu' h
    funext i
    have h' := congrArg (fun x => b.equivFun x i) h
    simp only [map_add, map_nsmul, LinearEquiv.apply_symm_apply, Pi.add_apply, Pi.smul_apply,
      nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply] at h'
    have e1 : ((a i : ℕ) : ℤ) = (((a i : ℕ) : ℤ) + k * b.equivFun mu i) % k := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a i).isLt)]
    have e2 : ((a' i : ℕ) : ℤ) = (((a' i : ℕ) : ℤ) + k * b.equivFun mu' i) % k := by
      rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast (a' i).isLt)]
    have e3 : ((a i : ℕ) : ℤ) = ((a' i : ℕ) : ℤ) := by rw [e1, e2, h']
    exact Fin.ext (by exact_mod_cast e3)
  · intro x y h
    rw [← Nat.cast_smul_eq_nsmul ℤ, ← Nat.cast_smul_eq_nsmul ℤ] at h
    exact smul_right_injective X hk0.ne' h

private theorem ceil_statement : CeilSt := by
  intro F _ v π hπ hF q
  classical
  have hfin : ∀ x : F, x ≠ 0 → ∃ t : ℚ, (t : WithTop ℚ) = v x := fun x hx =>
    WithTop.ne_top_iff_exists.mp (v.top_iff.not.mpr hx)
  have hπ1 : v π = ((1 : ℚ) : WithTop ℚ) := by rw [hπ, WithTop.coe_one]
  have hπ0 : π ≠ 0 := by
    intro h
    rw [h, v.map_zero] at hπ
    first
      | simp at hπ
      | exact absurd hπ (by rw [← WithTop.coe_one]; exact WithTop.top_ne_coe)
  have hpow : ∀ (x : F) (t : ℚ) (k : ℕ), v x = t → v (x ^ k) = ((k * t : ℚ) : WithTop ℚ) := by
    intro x t k ht
    rw [v.map_pow, ht, ← WithTop.coe_nsmul, nsmul_eq_mul]
  have hinv : ∀ x : F, x ≠ 0 → ∀ t : ℚ, v x = t → v x⁻¹ = ((-t : ℚ) : WithTop ℚ) := by
    intro x hx t ht
    obtain ⟨s, hs⟩ := hfin x⁻¹ (inv_ne_zero hx)
    have h1 : v (x * x⁻¹) = 0 := by rw [mul_inv_cancel₀ hx, v.map_one]
    rw [v.map_mul, ht, ← hs, ← WithTop.coe_add] at h1
    have h2 : t + s = 0 := by exact_mod_cast h1
    rw [← hs]
    congr 1
    linarith
  have hvz : ∀ m : ℤ, v (π ^ m) = ((m : ℚ) : WithTop ℚ) := by
    intro m
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · rw [zpow_natCast, hpow π 1 k hπ1]
      congr 1
      push_cast
      ring
    · rw [zpow_neg, zpow_natCast, hinv _ (pow_ne_zero _ hπ0) _ (hpow π 1 k hπ1)]
      congr 1
      push_cast
      ring
  rcases hF with hac | ⟨d, hd, hval⟩
  · obtain ⟨l, hl⟩ := IsAlgClosed.exists_pow_nat_eq (π ^ q.num) q.den_pos
    have hl0 : l ≠ 0 := by
      intro h
      rw [h, zero_pow q.den_pos.ne'] at hl
      exact zpow_ne_zero _ hπ0 hl.symm
    obtain ⟨t, ht⟩ := hfin l hl0
    have h1 := hpow l t q.den ht.symm
    rw [hl, hvz] at h1
    have h2 : (q.num : ℚ) = q.den * t := by exact_mod_cast h1
    have h3 : t = q := by
      have hd0 : (q.den : ℚ) ≠ 0 := by positivity
      rw [← Rat.num_div_den q, h2]
      field_simp
    refine ⟨l, hl0, fun x => ?_⟩
    rw [← ht, h3]
  · have hd0 : (0 : ℚ) < d := by exact_mod_cast hd
    have hd0' : (d : ℚ) ≠ 0 := hd0.ne'
    let P : ℤ → Prop := fun n =>
      (∃ x : F, x ≠ 0 ∧ v x = (((n : ℚ) / d : ℚ) : WithTop ℚ)) ∧ q ≤ (n : ℚ) / d
    obtain ⟨n0, ⟨⟨l, hl0, hl⟩, hq⟩, hmin⟩ := Int.exists_least_of_bdd (P := P)
      ⟨⌊q * d⌋, fun z hz => by
        have h4 := hz.2
        rw [le_div_iff₀ hd0] at h4
        have h5 : (⌊q * d⌋ : ℚ) ≤ z := le_trans (Int.floor_le _) h4
        exact_mod_cast h5⟩
      ⟨⌈q⌉ * d, ⟨π ^ ⌈q⌉, zpow_ne_zero _ hπ0, by
          rw [hvz]
          congr 1
          push_cast
          field_simp⟩, by
        push_cast
        rw [mul_div_assoc, div_self hd0', _root_.mul_one]
        exact Int.le_ceil q⟩
    refine ⟨l, hl0, fun x => ⟨fun hx => ?_, fun hx => le_trans ?_ hx⟩⟩
    · by_cases hx0 : x = 0
      · rw [hx0, v.map_zero]
        exact le_top
      · obtain ⟨m, hm⟩ := hval x hx0
        have hPm : P m := ⟨⟨x, hx0, hm⟩, by rw [hm] at hx; exact_mod_cast hx⟩
        have h6 := hmin m hPm
        have h6' : (n0 : ℚ) ≤ m := by exact_mod_cast h6
        have h7 : (n0 : ℚ) / d ≤ (m : ℚ) / d := by gcongr
        rw [hl, hm]
        exact_mod_cast h7
    · rw [hl]
      exact_mod_cast hq

theorem uu (hL : Laws) (hT : TwistBaseChangeStatement) : UUStatement := by
  exact uu_of hL.globalFns hT repsX_statement ceil_statement

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
