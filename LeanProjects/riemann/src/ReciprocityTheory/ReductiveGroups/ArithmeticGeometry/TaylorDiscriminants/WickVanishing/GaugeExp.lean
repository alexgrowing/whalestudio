import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.GaugeExp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.WickOperatorVanishing

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace ReciprocityTheory.ChartRestriction.G.TB.GE

def DofCommSt : Prop :=
  ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (k : Type) [CommRing k]
    [Algebra ℚ k] [Algebra R k] (B : FB R d O) (u v : Fin d → k) (g : PS k 1 d),
    Dof (B.FK k) u (Dof (B.FK k) v g) = Dof (B.FK k) v (Dof (B.FK k) u g)

def WickExpSt : Prop :=
  ∀ (k : Type) [CommRing k] [Algebra ℚ k] (d : ℕ) (F : Fin d → PS k 2 d) (ι : Type) [Fintype ι]
    (u : ι → Fin d → k) (c : ι → ι → k) (P : MvPolynomial ι k) (q : PS k 1 d),
    (∀ l l', c l l' = c l' l) → constantCoeff q = 0 → (∀ l, constantCoeff (Dof F (u l) q) = 0) →
    (∀ l l', Dof F (u l) (Dof F (u l') q) = C (c l l')) →
    ∀ (t : k) (G : PS k 1 d),
      constantCoeff (DpolyOf F u P (G * FB.expS k (t • q))) =
        constantCoeff (DpolyOf F u (expSecond k c (t * algebraMap ℚ k (1 / 2)) P.totalDegree P) G)

open G2 in
theorem gaugeExp_of (hA : ExpAddZeroConstant) (hE : ConstantCoeffSubstitution) (hG : CanonicalGaugeDiffBiadditive) (hQ : QuadraticFormDerivatives)
    (hW : WickExpSt) : GaugeExpSt := by
  intro R _ d O _ _ k _ _ _ B h h' hh hh' w0 m ι _ u Q f
  have ha0 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff
      ((![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j
    · simp [pt]
    · show MvPowerSeries.constantCoeff (ev ![pt k d 0] (B.actK k w0 i)) = 0
      rw [hE k d 1 1 ![pt k d 0] (B.actK k w0 i) (by intro j i; fin_cases j; simp [pt])]
      show MvPowerSeries.constantCoeff (MvPowerSeries.map (algebraMap R k) (B.A.act w0 i)) = 0
      rw [MvPowerSeries.constantCoeff_map, B.A.const, map_zero]
  have hc0 : ∀ (j : Fin 2) (i : Fin d), MvPowerSeries.constantCoeff
      ((![0, pt k d 0] : Fin 2 → Pt k 1 d) j i) = 0 := by
    intro j i
    fin_cases j <;> simp [pt]
  have hsub : MvPowerSeries.HasSubst (fun p : Fin 2 × Fin d =>
      (![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] : Fin 2 → Pt k 1 d) p.1 p.2) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero (fun p => ha0 p.1 p.2)
  have hlin : B.hL k h' w0 = B.hL k h w0 +
      ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h) := by
    simp only [FB.hL, ev]
    rw [MvPowerSeries.subst_sub hsub]
    abel
  have hch : MvPowerSeries.constantCoeff h = 0 := by
    rw [← hE k d 2 1 ![0, pt k d 0] h hc0, hh.ax0, map_zero]
  have hcL : MvPowerSeries.constantCoeff (B.hL k h w0) = 0 := by
    simp only [FB.hL]
    rw [hE k d 2 1 _ h ha0, hch]
  have hq := hQ R d O k B (h' - h) (hG R d O k B h h' hh hh') w0
  have hcm1 : MvPowerSeries.constantCoeff ((m : k) • B.hL k h w0) = 0 := by
    first
    | simp [hcL]
    | (rw [MvPowerSeries.smul_eq_C_mul]; simp [hcL])
  have hcm2 : MvPowerSeries.constantCoeff ((m : k) •
      ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] (h' - h)) = 0 := by
    first
    | simp [hq.1]
    | (rw [MvPowerSeries.smul_eq_C_mul]; simp [hq.1])
  simp only [FB.nabVal]
  rw [hlin, smul_add, hA k 1 d _ _ hcm1 hcm2, ← mul_assoc]
  exact hW k d (B.FK k) ι u _ Q _ (fun l l' => add_comm _ _) hq.1 (fun l => hq.2.1 (u l))
    (fun l l' => hq.2.2 (u l) (u l')) (m : k) _

end ReciprocityTheory.ChartRestriction.G.TB.GE
