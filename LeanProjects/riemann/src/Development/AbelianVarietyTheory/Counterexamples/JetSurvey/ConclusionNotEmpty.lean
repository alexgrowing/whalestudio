import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowerRosatiTauBalAction
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.PremisesMetRankOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.InhTate

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Out.InhTate

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoxPowerProbe

theorem both_hold : BoxRosatiSt ∧ BoxTauBalSt :=
  ⟨GlobalTheory.powerRosati_tauBal_action.1, GlobalTheory.powerRosati_tauBal_action.2.1⟩

section General

variable {R : Type} [CommRing R] [IsDomain R]

theorem conclusion_not_empty {D' D : DegPre R} {n : ℕ} (pD : IsPowDeg D' D n) (f g : D.P.A ⟶ D.P.A)
    (f' g' : D'.P.A ⟶ D'.P.A) (hf : IsMonHom f) (hg : IsMonHom g)
    (ef : ∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) (eg : ∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g)
    (hr : RosatiAdj D.P.A D.P.L f g) :
    ∃ u : LB.Gen (LB.LinComb D'.P.L (rosatiφ D'.P.A f' g') rosatiε), u.IsGen ∧
      LB.Gen.Corr D'.P.L _ _ _ _ (LB.pullGen D'.P.L _ _ u (zero2 D'.P.A)) (LB.oneGen D'.P.L) := by
  have := GlobalTheory.BoxTauLin.isMonHom_of_coord pD.pw f f' ef
  have := GlobalTheory.BoxTauLin.isMonHom_of_coord pD.pw g g' eg
  exact exists_ros GlobalTheory.globalFns_holds D'.P.isAb D'.P.isLB _ _
    (both_hold.1 R D' D n pD f g f' g' hf hg ef eg hr)

theorem c_compatible {D' D : DegPre R} {n : ℕ} (pD : IsPowDeg D' D n) (f : D.P.A ⟶ D.P.A) (f' : D'.P.A ⟶ D'.P.A)
    (a : D.X → D.X) (ef : ∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) (ca : ∀ y, D.c (a y) = D.c y ≫ f) (x : D'.X) :
    D'.c (pD.xe.symm fun i => a (pD.xe x i)) = D'.c x ≫ f' :=
  pow_ext pD.pw fun i => by
    rw [pD.c_pr, AddEquiv.apply_symm_apply, ca, Category.assoc, ef, ← Category.assoc, pD.c_pr]

theorem tauBal_id_iff (D : DegPre R) (hr : RosatiAdj D.P.A D.P.L (𝟙 _) (𝟙 _)) (a a' : D.X → D.X) :
    D.TauBal (𝟙 _) (𝟙 _) a a' ↔ ∀ y y' z J, Good D.P.L z J →
      val (D.tau (a y) y') (𝟙 _) z J = val (D.tau y (a' y')) (𝟙 _) z J := by
  have one : ∀ (u : LB.Gen (LB.LinComb D.P.L (rosatiφ D.P.A (𝟙 _) (𝟙 _)) rosatiε)), u.IsGen →
      LB.Gen.Corr D.P.L _ _ _ _ (LB.pullGen D.P.L _ _ u (zero2 D.P.A)) (LB.oneGen D.P.L) →
      ∀ y y' z J, Good D.P.L z J → val (LB.pullGen D.P.L _ _ u (D.pt2 y y')) (𝟙 _) z J = 1 := by
    intro u hu hn y y' z J hJ
    have := val_corr hJ (GlobalTheory.PowBalanceProbe.tauBal_id D u hu hn y y') (𝟙 _)
    rw [val_mul hJ] at this
    exact mul_eq_left.1 this
  constructor
  · intro h y y' z J hJ
    obtain ⟨u, hu, hn⟩ := exists_ros GlobalTheory.globalFns_holds D.P.isAb D.P.isLB _ _ hr
    have := val_corr hJ (h u hu hn y y') (𝟙 _)
    rwa [val_mul hJ, one u hu hn y y' z J hJ, _root_.mul_one] at this
  · intro h u hu hn y y'
    refine corr_of_val D.P.isLB fun z J hJ => ?_
    rw [val_mul hJ, one u hu hn y y' z J hJ, _root_.mul_one]
    exact h y y' z J hJ

end General

theorem pi_zpow_injective {a b : ℤ} (h : pi0 ^ a = pi0 ^ b) : a = b := by
  have inj : Function.Injective (Units.map
      (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).inv.hom.toMonoidHom) :=
    Units.map_injective (Scheme.ΓSpecIso (CommRingCat.of (FractionRing InhTate.R))).symm.commRingCatIsoToRingEquiv.injective
  have h' : piK ^ a = piK ^ b := inj (by rw [map_zpow, map_zpow]; exact h)
  have aux : ∀ k : ℕ, piK ^ k = 1 → k = 0 := fun k hk => by
    have e : algebraMap InhTate.R (FractionRing InhTate.R) (PowerSeries.X ^ k) =
        algebraMap InhTate.R (FractionRing InhTate.R) 1 := by
      rw [map_pow, map_one]
      exact congrArg Units.val hk
    have e' := congrArg PowerSeries.constantCoeff (IsFractionRing.injective _ _ e)
    by_contra h0
    simp [h0] at e'
  have fin : ¬ IsOfFinOrder piK := fun hf => by
    obtain ⟨k, hk, e⟩ := isOfFinOrder_iff_pow_eq_one.1 hf
    exact hk.ne' (aux k e)
  exact (injective_zpow_iff_not_isOfFinOrder.2 fin) h'

theorem rosati_tate : RosatiAdj tatePre.P.A tatePre.P.L (𝟙 _) (𝟙 _) :=
  fun _ => ⟨⊤, trivial, cg _ _ 1, cg_isGen _ _ 1⟩

theorem good_tate (z : (TK InhTate.R).left) (J) : Good tatePre.P.L z J := fun _ => trivial

theorem val_tau_tate (a b : ℤ) (z : (TK InhTate.R).left) (J) :
    val (tatePre.tau a b) (𝟙 _) z J = gm (𝟙 _) z ⊤ (pi0 ^ (2 * a * b)) := by
  unfold val
  erw [tau_isConst a b]
  exact gm_res _ z _ ((good_tate z J).mem _ _) _

theorem gm_pi_zpow_injective (z : (TK InhTate.R).left) {a b : ℤ}
    (h : gm (𝟙 _) z ⊤ (pi0 ^ a) = gm (𝟙 _) z ⊤ (pi0 ^ b)) : a = b := by
  have : Subsingleton (TK InhTate.R).left :=
    inferInstanceAs (Subsingleton (PrimeSpectrum (FractionRing InhTate.R)))
  exact pi_zpow_injective (unit_ext fun x _ => by rw [Subsingleton.elim x z]; exact h)

theorem nonempty_TK : Nonempty (TK InhTate.R).left :=
  inferInstanceAs (Nonempty (PrimeSpectrum (FractionRing InhTate.R)))

theorem tauBal_tate_iff (a a' : ℤ → ℤ) :
    tatePre.TauBal (𝟙 _) (𝟙 _) a a' ↔ ∀ y y', a y * y' = y * a' y' := by
  refine (tauBal_id_iff tatePre rosati_tate a a').trans ⟨fun h y y' => ?_, fun h y y' z J _ => ?_⟩
  · obtain ⟨z⟩ := nonempty_TK
    have := h y y' z (fun _ => PUnit.unit) (good_tate _ _)
    erw [val_tau_tate, val_tau_tate] at this
    have := gm_pi_zpow_injective z this
    linarith
  · erw [val_tau_tate, val_tau_tate]
    have k : ∀ y y' : ℤ, 2 * a y * y' = 2 * y * a' y' := fun y y' => by linarith [h y y']
    exact congrArg (fun t : ℤ => gm (𝟙 _) z ⊤ (pi0 ^ t)) (k y y')

theorem premises_met (m : ℤ) (n : ℕ) :
    ∃ (D' : DegPre InhTate.R) (pD : IsPowDeg D' tatePre n),
      (∀ i, 𝟙 _ ≫ pD.pw.pr i = pD.pw.pr i ≫ 𝟙 _) ∧ RosatiAdj tatePre.P.A tatePre.P.L (𝟙 _) (𝟙 _) ∧
      (∀ y : ℤ, tatePre.c (m * y) = tatePre.c y ≫ 𝟙 _) ∧
      tatePre.TauBal (𝟙 _) (𝟙 _) (fun y : ℤ => m * y) (fun y : ℤ => m * y) := by
  obtain ⟨D', ⟨p⟩⟩ := GlobalTheory.PowActProbe.exists_pow _ _ tateData n
  exact ⟨D'.toPre, p, fun _ => by simp, rosati_tate, fun _ => (Category.comp_id _).symm,
    (tauBal_tate_iff _ _).2 fun y y' => by ring⟩

theorem sum_of_tauBal_pow {D' : DegPre InhTate.R} {n : ℕ} (pD : IsPowDeg D' tatePre n) (a a' : ℤ → ℤ)
    (h : D'.TauBal (𝟙 _) (𝟙 _) (fun y => pD.xe.symm fun i => a (pD.xe y i))
      (fun y => pD.xe.symm fun i => a' (pD.xe y i))) (y y' : Fin n → ℤ) :
    ∑ i, a (y i) * y' i = ∑ i, y i * a' (y' i) := by
  have e1 : ∀ i, 𝟙 _ ≫ pD.pw.pr i = pD.pw.pr i ≫ 𝟙 _ := fun _ => by simp
  have hr := both_hold.1 _ D' tatePre n pD _ _ _ _ inferInstance inferInstance e1 e1 rosati_tate
  obtain ⟨z⟩ := nonempty_TK
  obtain ⟨J', hJ', -⟩ := exists_good D'.P.L D'.P.isLB z (K := PEmpty) PEmpty.elim PEmpty.elim
    (fun a => a.elim) (fun a => a.elim)
  have H := (tauBal_id_iff D' hr _ _).1 h (pD.xe.symm y) (pD.xe.symm y') z J' hJ'
  have hJ := good_tate z (fun _ => PUnit.unit)
  have t₁ := GlobalTheory.TauBalBox.tau_box pD hJ hJ' (pD.xe.symm fun i => a (pD.xe (pD.xe.symm y) i)) (pD.xe.symm y')
  have t₂ := GlobalTheory.TauBalBox.tau_box pD hJ hJ' (pD.xe.symm y) (pD.xe.symm fun i => a' (pD.xe (pD.xe.symm y') i))
  have cc : ∀ p q : D'.X, DVR.cP D' (TK InhTate.R) p = DVR.cP D' (TK InhTate.R) q := fun p q =>
    pow_ext pD.pw fun i => toUnit_unique _ _
  rw [cc (pD.xe.symm fun i => a (pD.xe (pD.xe.symm y) i)) (pD.xe.symm y), H] at t₁
  rw [cc (pD.xe.symm fun i => a' (pD.xe (pD.xe.symm y') i)) (pD.xe.symm y')] at t₂
  have E := t₁.symm.trans t₂
  erw [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply,
    AddEquiv.apply_symm_apply] at E
  have s : ∀ p q : Fin n → ℤ, ∏ i, val (tatePre.tau (p i) (q i)) (𝟙 _) z (fun _ => PUnit.unit) =
      gm (𝟙 _) z ⊤ (pi0 ^ (2 * ∑ i, p i * q i)) := fun p q => by
    refine (Finset.prod_congr rfl fun i _ => val_tau_tate (p i) (q i) z _).trans ?_
    rw [← map_prod, Finset.mul_sum]
    refine congrArg _ ?_
    simp only [_root_.mul_assoc]
    exact (map_prod ((zpowersHom _ pi0).comp (MonoidHom.id (Multiplicative ℤ)))
      (fun i => Multiplicative.ofAdd (2 * (p i * q i))) Finset.univ).symm
  have := gm_pi_zpow_injective z ((s (fun i => a (y i)) y').symm.trans (E.trans (s y (fun i => a' (y' i)))))
  linarith

theorem conclusion_can_fail {D' : DegPre InhTate.R} {n : ℕ} (pD : IsPowDeg D' tatePre (n + 1)) :
    ¬ D'.TauBal (𝟙 _) (𝟙 _) (fun y => pD.xe.symm fun i => (fun _ : ℤ => (0 : ℤ)) (pD.xe y i))
      (fun y => pD.xe.symm fun i => (fun t : ℤ => t) (pD.xe y i)) := fun h => by
  have := sum_of_tauBal_pow pD (fun _ => 0) (fun t => t) h (fun _ => 1) (fun _ => 1)
  simp at this
  omega

theorem rosati_iff {R : Type} [CommRing R] [IsDomain R] {D' D : DegPre R} {n : ℕ} (pD : IsPowDeg D' D (n + 1))
    (f g : D.P.A ⟶ D.P.A) (f' g' : D'.P.A ⟶ D'.P.A) (hf : IsMonHom f) (hg : IsMonHom g)
    (ef : ∀ i, f' ≫ pD.pw.pr i = pD.pw.pr i ≫ f) (eg : ∀ i, g' ≫ pD.pw.pr i = pD.pw.pr i ≫ g) :
    RosatiAdj D'.P.A D'.P.L f' g' ↔ RosatiAdj D.P.A D.P.L f g := by
  refine ⟨fun h => ?_, both_hold.1 R D' D _ pD f g f' g' hf hg ef eg⟩
  have := GlobalTheory.BoxTauLin.isMonHom_of_coord pD.pw f f' ef
  have := GlobalTheory.BoxTauLin.isMonHom_of_coord pD.pw g g' eg
  obtain ⟨u, hu, -⟩ := exists_ros GlobalTheory.globalFns_holds D'.P.isAb D'.P.isLB _ _ h
  exact (GlobalTheory.PowBalanceProbe.hom_and_adjoint pD 0 ef eg u hu).2.2

end GlobalTheory.BoxPowerProbe
