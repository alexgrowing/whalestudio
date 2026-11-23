import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.RepFUnique

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj

attribute [local instance] Over.cartesianMonoidalCategory

namespace ReciprocityTheory.ChartRestriction.G.DVR.UUA

open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor TWO TWM SectionScalarValuation IsLocalRing

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
  {D : DegData V (maximalIdeal V)} {F : Type} [Field F] [Algebra (FractionRing V) F]

theorem fam_sum_f {k : ℕ} {Ix : Type} [Fintype Ix] (c : Ix → F) (s : Ix → Fam D.toPre F k) (α : D.toPre.X) (j) :
    ((∑ i, c i • s i).s α).f j = ∑ i, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
  classical
  have key : ∀ t : Finset Ix, ((∑ i ∈ t, c i • s i).s α).f j =
      ∑ i ∈ t, resTop _ (gF D.toPre F (c i)) * ((s i).s α).f j := by
    intro t
    induction t using Finset.induction_on with
    | empty => simp
    | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, add_f, smul_f, ih]
  exact key Finset.univ

theorem fam_eq_zero (hG : GlobalFnsSt) {k : ℕ} (P : D.toPre.X → Prop) (hP : ∀ χ, ∃ α mu, P α ∧ α + k • mu = χ)
    (s : Fam D.toPre F k) (h0 : ∀ α, P α → ∀ j, (s.s α).f j = 0) : s = 0 := by
  have hL := D.toPre.P.isLB
  refine DVR.fam_ext fun χ j => ?_
  obtain ⟨α, mu, hα, rfl⟩ := hP χ
  obtain ⟨⟨u, hu, hc⟩, -⟩ := gen_fe (D := D.toPre) (F := F) hG k mu α
  have hrel := s.fe mu α u hu hc
  refine sec_ext_val hL (s' := (0 : Fam D.toPre F k).s (α + k • mu)) (fun y J hJ => ?_) j
  rw [(secRel_iff hL _ _ _ _ _ _ _ _ _ u).1 hrel _ (𝟙 _) y J hJ, sval_zero_of (h0 α hα) _ y J (hJ.mem _ _),
    MulZeroClass.zero_mul, sval_zero_of (fun j => rfl) _ y J (hJ.mem _ _)]

theorem vge_coords {ϖ : V} (hϖ : Irreducible ϖ) {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v)
    {k : ℕ} {ρ : D.toPre.X} {m : ℕ} (b : Fin m → D.toPre.SecB k ρ)
    (hb : ∀ (R' : Type) [CommRing R'] (f : V →+* R'),
      ∀ b' : Fin m → LB.Sec (LB.LinComb D.toPre.P.L
          (fun i => (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left ≫ DegPre.famφB D.toPre ρ i)
          (DegPre.famε k)),
        (∀ i, IsPullSecLC D.toPre.P.L (DegPre.famφB D.toPre ρ) (DegPre.famε k)
          (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.toPre.P.A).left (b i) (b' i)) →
        IsSecBasis (T := Over.mk (Spec.map (CommRingCat.ofHom f))) (A := D.toPre.P.A) _ b')
    (bF : Fin m → LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k)))
    (hbF : ∀ i (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
      sval (bF i) (𝟙 _) y J = sval (b i) (DegPre.prB D.toPre F).left y J)
    (hU : ∀ c : Fin m → F, (∀ (y : (DegPre.BF D.toPre F).left) J, Good D.toPre.P.L y J →
        ∑ i, gs (𝟙 _) y ⊤ (gF D.toPre F (c i)) * sval (bF i) (𝟙 _) y J = 0) → c = 0)
    {t : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre F ρ) (DegPre.famε k))} {c : Fin m → F}
    (hc : RepF bF t c) {r : ℚ} (ht : VGe D F v k ρ t r) : ∀ i, ((r : ℚ) : WithTop ℚ) ≤ v (c i) := by
  obtain ⟨n, a, σ, σF, hscal, hva, hsum⟩ := ht
  have hσ : ∀ l, ∃ c' : Fin m → F, (∀ i, (0 : WithTop ℚ) ≤ v (c' i)) ∧ RepF bF (σF l) c' := fun l =>
    coordsO hϖ hv b hb bF hbF (σ l) (σF l) fun y J hJ => by
      rw [← secScal_sval (hscal l) (𝟙 _) y hJ, Category.id_comp]
  choose c' hc'v hc' using hσ
  have hrep : RepF bF t (fun i => ∑ l, a l * c' l i) := fun y J hJ => by
    rw [sval_lin (fun l => gF D.toPre F (a l)) σF (fun j => hsum j) (𝟙 _) y hJ]
    simp only [map_sum, map_mul, gs_sum _ y ⊤ trivial, gs_mul _ y ⊤ trivial, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hc' l y J hJ, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have e := repF_unique hU hc hrep
  intro i
  rw [e]
  refine AddValuation.map_le_sum v fun l _ => ?_
  rw [AddValuation.map_mul]
  calc ((r : ℚ) : WithTop ℚ) = (r : WithTop ℚ) + 0 := (add_zero _).symm
    _ ≤ v (a l) + v (c' l i) := add_le_add (hva l) (hc'v l i)

end ReciprocityTheory.ChartRestriction.G.DVR.UUA
