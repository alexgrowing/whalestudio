import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialDegenerationUnitPartExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMonomialTauParamsSymm
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.RigChart
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnitTauSymm

theorem exps_eq {σ k : Type} [Field k] [IsDomain (MvPowerSeries σ k)] {m : ℕ} (v : Fin m → σ)
    (hv : Function.Injective v) (A B : Fin m → ℤ) {x x' : MvPowerSeries σ k} (hx : IsUnit x) (hx' : IsUnit x')
    (he : (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ A i) *
        algebraMap _ _ x =
      (∏ i, algebraMap (MvPowerSeries σ k) (FractionRing (MvPowerSeries σ k)) (MvPowerSeries.X (v i)) ^ B i) *
        algebraMap _ _ x') :
    A = B := by
  set K := FractionRing (MvPowerSeries σ k)
  let n : Fin m → ℕ := fun i => (A i).natAbs + (B i).natAbs
  have hne : ∀ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ≠ 0 := fun i => by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (v i) 1)) e0
    simp [MvPowerSeries.coeff_X] at this
  have H : ∀ C : Fin m → ℤ, (∀ i, 0 ≤ C i + n i) →
      (∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ C i) *
        ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i =
        algebraMap _ K (∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ (C i + n i).toNat) := by
    intro C hC
    rw [← Finset.prod_mul_distrib, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_pow, ← zpow_natCast, ← zpow_natCast, ← zpow_add₀ (hne i), Int.toNat_of_nonneg (hC i)]
  have hA : ∀ i, 0 ≤ A i + n i := fun i => by simp only [n]; omega
  have hB : ∀ i, 0 ≤ B i + n i := fun i => by simp only [n]; omega
  have he' := congrArg (· * ∏ i, algebraMap _ K (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ n i) he
  rw [mul_right_comm, H A hA, mul_right_comm, H B hB, ← map_mul, ← map_mul] at he'
  have he'' := IsFractionRing.injective _ K he'
  have hmon : ∀ a : Fin m → ℕ, ∏ i, (MvPowerSeries.X (v i) : MvPowerSeries σ k) ^ a i =
      MvPowerSeries.monomial (∑ i, Finsupp.single (v i) (a i)) 1 := by
    intro a
    simp_rw [MvPowerSeries.X_pow_eq]
    rw [MvPowerSeries.prod_monomial]
    simp
  have happ : ∀ (a : Fin m → ℕ) (i : Fin m), (∑ j, Finsupp.single (v j) (a j)) (v i) = a i := by
    classical
    intro a i
    rw [Finsupp.finset_sum_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [Finsupp.single_apply, if_neg]
      exact fun e => hj (hv e)
    · simp
  rw [hmon, hmon] at he''
  have hPM := GlobalTheory.MumFam.monomial_eq_of_mul_unit hx hx' he''
  funext i
  have := congrArg (fun f => f (v i)) hPM
  simp only [happ] at this
  have a1 := Int.toNat_of_nonneg (hA i)
  have b1 := Int.toNat_of_nonneg (hB i)
  omega

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart ReciprocityTheory.ChartRestriction.G.Out.InhTate

theorem commGroup_four_factor_rearrange {G : Type} [CommGroup G] (a b c A B C D : G) :
    a * A * (b * B)⁻¹ * (c * C)⁻¹ * D⁻¹ = a * b⁻¹ * c⁻¹ * (A * B⁻¹ * C⁻¹ * D⁻¹) := by
  simp only [mul_inv]
  ac_rfl

theorem exists_units_rel {R : Type} [CommRing R] [IsDomain R] (Q : DegPre R) {m : ℕ} (t : Fin m → R)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (y z : Q.X) (n1 n2 n3 : Fin m → ℕ)
    (p1 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c (y + z)).left) fun _ => -1))
    (p2 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c y).left) fun _ => -1))
    (p3 : LB.Gen (LB.LinComb Q.P.L (K := PUnit) (fun _ => (Q.c z).left) fun _ => -1))
    (hp1 : IsUnitPart Q t gam (y + z) n1 p1) (hp2 : IsUnitPart Q t gam y n2 p2) (hp3 : IsUnitPart Q t gam z n3 p3)
    (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left]
      ![-1, 1, 1, -1])) (hτ : τ₀.IsGen) (e : (FractionRing R)ˣ)
    (hv : ∀ zz J, Good Q.P.L zz J →
      val (Q.tau y z) (𝟙 _) zz J = gm (𝟙 (TK R).left) zz ⊤ (unitOn e) * val τ₀ (toUnit (TK R)).left zz J) :
    ∃ x x' : R, IsUnit x ∧ IsUnit x' ∧ (e : FractionRing R) * algebraMap R _ x =
      algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
        (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ * algebraMap R _ x' := by
  obtain ⟨hg1, -, e1, he1, hv1⟩ := hp1
  obtain ⟨hg2, -, e2, he2, hv2⟩ := hp2
  obtain ⟨hg3, -, e3, he3, hv3⟩ := hp3
  have hc0 : Q.c 0 = η[Q.P.A] := by
    have h := Q.c_add 0 0
    rw [add_zero] at h
    have h' : Q.c 0 * Q.c 0 = Q.c 0 := h.symm
    have h1 : Q.c 0 = 1 := mul_eq_left.1 h'
    rw [h1, Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  have hc0' : (Q.c 0).left = eSec Q.P.A := by rw [hc0]; rfl
  let T := LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ (LB.mulGen Q.P.L _ _ _ _ p1 (LB.invGen Q.P.L _ _ p2))
    (LB.invGen Q.P.L _ _ p3)) (LB.invGen Q.P.L _ _ Q.rig)
  have hT : T.IsGen :=
    LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _
      (LB.isGen_mulGen (L := Q.P.L) _ _ _ _ _ _ hg1 (LB.isGen_invGen (L := Q.P.L) _ _ _ hg2))
      (LB.isGen_invGen (L := Q.P.L) _ _ _ hg3)) (LB.isGen_invGen (L := Q.P.L) _ _ _ Q.rig_gen)
  have hF : FormEq (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (Q.c (y + z)).left) (fun _ : PUnit => (Q.c y).left))
      (fun _ : PUnit => (Q.c z).left)) (fun _ : PUnit => eSec Q.P.A))
      (Sum.elim (Sum.elim (Sum.elim (fun _ : PUnit => (-1 : ℤ)) (fun _ : PUnit => -(-1 : ℤ))) (fun _ : PUnit => -(-1 : ℤ)))
        (fun _ : PUnit => -(1 : ℤ)))
      (K' := Fin 4) ![(Q.c (y + z)).left, (Q.c y).left, (Q.c z).left, (Q.c 0).left] ![-1, 1, 1, -1] := by
    intro U _ h
    simp only [Fintype.prod_sum_type, Fin.prod_univ_four, Finset.univ_unique, Finset.prod_singleton, Sum.elim_inl,
      Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, hc0', neg_neg]
    simp [Matrix.vecHead, Matrix.vecTail, hc0']
  obtain ⟨W', hW', hvW⟩ := exists_gen Q.P.isLB hF T hT
  let E : (FractionRing R)ˣ := e1 * e2⁻¹ * e3⁻¹
  have hu : ∀ a b : (FractionRing R)ˣ, unitOn (a * b) = unitOn a * unitOn b := fun a b => map_mul (Units.map _) a b
  have hui : ∀ a : (FractionRing R)ˣ, unitOn a⁻¹ = (unitOn a)⁻¹ := fun a => map_inv (Units.map _) a
  have hvE : ∀ zz J, Good Q.P.L zz J → val (Q.tau y z) (𝟙 _) zz J =
      gm (𝟙 (TK R).left) zz ⊤ (unitOn E) * val W' (toUnit (TK R)).left zz J := by
    intro zz J hJ
    rw [hvW _ _ zz J hJ]
    simp only [DegPre.tau, DegPre.rigK, T, val_mul hJ, val_inv, val_pull hJ]
    rw [hv1 zz J hJ, hv2 zz J hJ, hv3 zz J hJ, Category.id_comp]
    rw [hu, hu, hui, hui, map_mul, map_mul, map_inv, map_inv]
    exact commGroup_four_factor_rearrange _ _ _ _ _ _ _
  obtain ⟨w, hw⟩ := GlobalTheory.ValueTwoGen.exists_unit_gen _ (TLinPf.linComb_cover Q.P.L Q.P.isLB _ _) τ₀ W' hτ hW'
  have key : ∀ zz J, Good Q.P.L zz J → val W' (toUnit (TK R)).left zz J =
      gm (toUnit (TK R)).left zz ⊤ w * val τ₀ (toUnit (TK R)).left zz J := by
    intro zz J hJ
    have hs : ∀ j, W'.s j = res le_top w * τ₀.s j := fun j => Units.ext (hw j)
    show gm _ zz _ (W'.s _) = _ * gm _ zz _ (τ₀.s _)
    erw [hs, MonoidHom.map_mul, gm_res _ zz le_top (hJ.mem _ _)]
  have k₁ : unitOn e * pullTop (jK R) (1 : Γ(Sp R, ⊤)ˣ) = unitOn E * pullTop (jK R) w :=
      GlobalTheory.TauLocal.eq_of_gm Q.P.isLB fun zz J hJ => by
    have s := (hv zz J hJ).symm.trans (hvE zz J hJ)
    rw [key zz J hJ, ← _root_.mul_assoc] at s
    have hg : gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _) zz ⊤ (pullTop (jK R) w) :=
      (show gm (toUnit (TK R)).left zz ⊤ w = gm (𝟙 _ ≫ jK R) zz ⊤ w from rfl).trans
        (gm_pull (𝟙 _) (jK R) zz ⊤ trivial w).symm
    rw [map_mul, map_mul, ← hg, map_one, map_one, _root_.mul_one]
    exact mul_right_cancel s
  have nat := fun v : Γ(Sp R, ⊤)ˣ => congrArg (fun g => g.hom v.val)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (algebraMap R (FractionRing R))))
  have e₂ := congrArg (fun v => (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).hom.hom v.val) k₁
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom (1 : Γ(Sp R, ⊤)ˣ).val,
    (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val, (1 : Γ(Sp R, ⊤)ˣ).isUnit.map _, w.isUnit.map _, ?_⟩
  have hE : (E : FractionRing R) = algebraMap R _ (∏ i, t i ^ n1 i) * (algebraMap R _ (∏ i, t i ^ n2 i))⁻¹ *
      (algebraMap R _ (∏ i, t i ^ n3 i))⁻¹ := by
    simp only [E, Units.val_mul, Units.val_inv_eq_inv_val, he1, he2, he3]
  rw [← hE]
  refine Eq.trans ?_ (e₂.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat w))))
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ (nat 1)))
    exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply e.val
  · exact (Scheme.ΓSpecIso (CommRingCat.of (FractionRing R))).inv_hom_id_apply E.val

end GlobalTheory.UnitTauSymm

namespace GlobalTheory.UnitTauSymm

open GlobalTheory.LogKSChart

theorem gam_symm_of_isUnitTau : ∀ (k : Type) [Field k] (m d : ℕ) (Q : DegPre (ChartRing k m d)) (gam : Fin m → LinearMap.BilinForm ℤ Q.X), IsMonomial Q (bdParam k m d) gam → ∀ (mu α : Q.X) (τ₀ : LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (mu + α)).left, (Q.c mu).left, (Q.c α).left, (Q.c 0).left] ![-1, 1, 1, -1])), IsUnitTau Q (bdParam k m d) gam mu α τ₀ → ∀ i, gam i mu α = gam i α mu := by
  intro k _ m d Q gam hM mu α τ₀ hτ i
  obtain ⟨n1, p1, hp1⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM (mu + α)
  obtain ⟨n2, p2, hp2⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM mu
  obtain ⟨n3, p3, hp3⟩ := GlobalTheory.UnitPart.exists_isUnitPart Q (bdParam k m d) gam hM α
  have hn1 := hp1.2.1 i
  have hn2 := hp2.2.1 i
  have hn3 := hp3.2.1 i
  obtain ⟨hτg, e, he, hv⟩ := hτ
  obtain ⟨x, x', hx, hx', hrel⟩ := exists_units_rel Q _ gam mu α n1 n2 n3 p1 p2 p3 hp1 hp2 hp3 τ₀ hτg e hv
  set K := FractionRing (ChartRing k m d)
  let a : Fin m → K := fun i => algebraMap (ChartRing k m d) K (bdParam k m d i)
  have hne : ∀ i, a i ≠ 0 := fun i => by
    simp only [a]
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective _ K)]
    intro e0
    have := congrArg (MvPowerSeries.coeff (Finsupp.single (Sum.inl i : Fin m ⊕ Fin d) 1)) e0
    simp [bdParam, MvPowerSeries.coeff_X] at this
  have hP : ∀ n : Fin m → ℕ, algebraMap (ChartRing k m d) K (∏ i, bdParam k m d i ^ n i) = ∏ i, a i ^ n i := fun n => by
    rw [map_prod]
    exact Finset.prod_congr rfl fun i _ => map_pow _ _ _
  have hP0 : ∀ n : Fin m → ℕ, ∏ i, a i ^ n i ≠ 0 := fun n =>
    Finset.prod_ne_zero_iff.2 fun i _ => pow_ne_zero _ (hne i)
  rw [he, hP, hP, hP] at hrel
  have key : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) * algebraMap _ K x =
      (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) * algebraMap _ K x' := by
    have e1 : (∏ i, a i ^ (fun i => gam i mu α + n2 i + n3 i) i) =
        (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * ∏ i, a i ^ n3 i := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [zpow_add₀ (hne i), zpow_add₀ (hne i), zpow_natCast, zpow_natCast]
    have e2 : (∏ i, a i ^ (fun i => (n1 i : ℤ)) i) = ∏ i, a i ^ n1 i := by
      refine Finset.prod_congr rfl fun i _ => ?_
      exact zpow_natCast _ _
    have hrel' : (∏ i, a i ^ gam i mu α) * algebraMap _ K x =
        (∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x' := hrel
    rw [e1, e2]
    calc (∏ i, a i ^ gam i mu α) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) * algebraMap _ K x
        = ((∏ i, a i ^ gam i mu α) * algebraMap _ K x) * (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by ring
      _ = ((∏ i, a i ^ n1 i) * (∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n3 i)⁻¹ * algebraMap _ K x') *
          (∏ i, a i ^ n2 i) * (∏ i, a i ^ n3 i) := by rw [hrel']
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' * ((∏ i, a i ^ n2 i)⁻¹ * (∏ i, a i ^ n2 i)) *
          ((∏ i, a i ^ n3 i)⁻¹ * (∏ i, a i ^ n3 i)) := by ring
      _ = (∏ i, a i ^ n1 i) * algebraMap _ K x' := by
        rw [inv_mul_cancel₀ (hP0 n2), inv_mul_cancel₀ (hP0 n3), _root_.mul_one, _root_.mul_one]
  have hAB := congrFun (exps_eq (σ := Fin m ⊕ Fin d) (k := k) Sum.inl Sum.inl_injective _ _ hx hx' key) i
  simp only [map_add, LinearMap.add_apply] at hn1
  linarith

end GlobalTheory.UnitTauSymm
