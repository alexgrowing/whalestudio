import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.SCWick

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.SCPf

variable {R : Type} [CommRing R] {d : ℕ} {O : Type} [CommRing O] [StarRing O]
variable {k : Type} [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k) (l l' : ι) : k :=
  if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0

theorem kapW_eq_kapH (m : ℕ) {ι π : Type} [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) :
    kapW m s (fun l => (u l, 0)) (fun l => (0, φ l)) = kapH m c s u φ := by
  funext l l'
  show (if s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0) =
    (if c l = c l' ∧ s l = true ∧ s l' = false then (m : k) * betaH k (0, φ l) (u l', 0) else 0)
  by_cases hs : s l = true ∧ s l' = false
  · rw [if_pos hs]
    by_cases hc : c l = c l'
    · rw [if_pos ⟨hc, hs⟩]
    · rw [if_neg (fun h => hc h.1), hFU l l' (fun h => hc h.1), mul_zero]
  · rw [if_neg hs, if_neg (fun h => hs h.2)]

theorem rename_qsmul {ι τ : Type} (e : ι → τ) (q : ℚ) (X : MvPolynomial ι k) :
    MvPolynomial.rename e (q • X) = q • MvPolynomial.rename e X := by
  exact map_rat_smul (MvPolynomial.rename e) q X

theorem ordNabla_expand (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d) (m : ℕ) {ι π : Type}
    [Fintype ι] [DecidableEq π] (c : ι → π) (s : ι → Bool) (u φ : ι → Fin d → k)
    (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        nablaPoly k B h m u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) (liftX k g) := by
  classical
  have hb0 : ∀ l, ((fun l => ((0 : Fin d → k), φ l)) l).1 = 0 := fun l => rfl
  have haa : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (u l', 0) = 0 := by
    intro l l' _
    simp [betaH]
  have hab : ∀ l l', s l = s l' → betaH k (u l, (0 : Fin d → k)) (0, φ l') = 0 :=
    fun l l' hs => hUF l l' (fun h => h.2 hs)
  have hw := ordNabla_wick hN2 hN3 B h m s (fun l => (u l, 0)) (fun l => (0, φ l)) hb0 haa hab Q g
  simp only [Prod.mk_add_mk, add_zero, zero_add] at hw
  have hdeg : (MvPolynomial.rename (sideE s) Q).totalDegree = Q.totalDegree :=
    MvPolynomial.totalDegree_renameEquiv (R := k) (sideE s) Q
  rw [hw, kapW_eq_kapH m c s u φ hFU, hdeg]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← rename_qsmul, ← ordNabla_eq B h m s (fun l => (u l, 0)) ?_, ordNabla_u hN2]
  intro l l' _
  exact nablaL_comm hN2 B h m _ _ (by simp [betaH])

theorem ordNabla_value_expand (hV : ValueSt) (hN2 : ConnectionCommutator) (hN3 : ConnectionKillsSeries) (B : FB R d O) (h : PS k 2 d)
    (hax : ev (n := 1) ![0, pt k d 0] h = 0) (m : ℕ) {ι π : Type} [Fintype ι] [DecidableEq π] (c : ι → π)
    (s : ι → Bool) (u φ : ι → Fin d → k) (hUF : OppositePairVanishing k c s (fun l => (u l, 0)) (fun l => (0, φ l)))
    (hFU : OppositePairVanishing k c s (fun l => (0, φ l)) (fun l => (u l, 0))) (Q : MvPolynomial ι k) (g : PS k 1 d) :
    constantCoeff (ordNabla k B h m s (fun l => (u l, φ l)) Q (liftX k g)) =
      ∑ n ∈ Finset.range (Q.totalDegree + 1),
        constantCoeff (DpolyOf (B.FK k) u (((n.factorial : ℚ)⁻¹) • (secondOrder k (kapH m c s u φ))^[n] Q) g) := by
  rw [ordNabla_expand hN2 hN3 B h m c s u φ hUF hFU Q g, map_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact hV R d O k B h hax m ι u _ g

end ReciprocityTheory.ChartRestriction.G.TB.SCPf
