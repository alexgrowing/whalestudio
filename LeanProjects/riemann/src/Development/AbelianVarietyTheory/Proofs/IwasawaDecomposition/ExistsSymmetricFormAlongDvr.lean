import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFiniteCubeInduction
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBimultOfIsPullDeg
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.PolFan GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PreValForm

section Form

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V} (hϖ : Irreducible ϖ) (D : DegPre V)

include hϖ in

theorem qVal_exists (χ : D.X) : ∃ n : ℤ, QForm.QVal D ϖ χ n :=
  exists_genHasVal hϖ D.P.L D.P.isLB _ _ _ _ (D.psi χ) (D.psi_gen χ)

include hϖ in

theorem qVal_unique {χ : D.X} {n m : ℤ} (hn : QForm.QVal D ϖ χ n) (hm : QForm.QVal D ϖ χ m) : n = m :=
  genHasVal_unique hϖ D.P.L D.P.isLB _ _ _ _ _ hn hm

theorem rigK_val0 : GenHasVal ϖ D.P.L (fun _ : PUnit => 𝟙 _ ≫ eSec D.P.A)
    (fun _ => (toUnit (TK V)).left ≫ eSec D.P.A) (fun _ => by rw [Category.id_comp]; rfl) (fun _ => 1)
    D.rigK 0 :=
  genHasVal_pullGen_of (ϖ := ϖ) D.P.L _ _ D.rig D.rig_gen (𝟙 _) (toUnit (TK V)).left
    (by rw [Category.comp_id]; rfl)

variable {Q : D.X → ℤ}

include hϖ in

theorem tau_val' (hQ : QForm.IsQ D ϖ Q) (a b : D.X) :
    ∃ (φ : _) (hφ : _), (∀ k, φ k ≫ D.P.A.hom = 𝟙 _) ∧
      GenHasVal ϖ D.P.L φ _ hφ _ (D.tau a b) (QForm.bOf D Q a b) := by
  have hL := D.P.isLB
  have h1 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (a + b))
    (genHasVal_invGen D.P.L hL _ _ _ _ _ (hQ a))
  have h2 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ h1
    (genHasVal_invGen D.P.L hL _ _ _ _ _ (hQ b))
  have h3 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ h2
    (genHasVal_invGen D.P.L hL _ _ _ _ _ (rigK_val0 D))
  have h4 : Q (a + b) + -Q a + -Q b + -0 = QForm.bOf D Q a b := by simp only [QForm.bOf]; ring
  rw [h4] at h3
  exact ⟨_, _, by secTac, h3⟩

include hϖ in

theorem bOf_add_left' (hB : D.TauBimult) (hQ : QForm.IsQ D ϖ Q) (a a' b : D.X) :
    QForm.bOf D Q (a + a') b = QForm.bOf D Q a b + QForm.bOf D Q a' b := by
  have hL := D.P.isLB
  obtain ⟨_, _, hsA, hA⟩ := tau_val' hϖ D hQ (a + a') b
  obtain ⟨_, _, hsB, hB'⟩ := tau_val' hϖ D hQ a b
  obtain ⟨_, _, hsC, hC⟩ := tau_val' hϖ D hQ a' b
  have hcub := genHasVal_pullGen_of (ϖ := ϖ) D.P.L _ _ D.cub.t D.cub.isGen
    (lift (D.c a) (lift (D.c a') (D.c b))).left (D.pt3 a a' b)
    (by simp [DegPre.pt3, ← CartesianMonoidalCategory.comp_lift])
  have h1 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ hA hcub
  have h2 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ hB' hC
  have := genHasVal_unique hϖ D.P.L hL _ _ _ _ _
    (genHasVal_corr hϖ D.P.L hL D.P.A.hom _ _ _ _ _ _ _ _
      (QForm.sumElim_sec hsA (fun _ => QForm.over_sec _ _)) (QForm.sumElim_sec hsB hsC) _ _
      (genHasVal_isGen D.P.L _ _ _ _ _ h2) (hB a a' b) h1) h2
  linarith

include hϖ in

theorem Q_neg' (hE : D.PsiEven) (hQ : QForm.IsQ D ϖ Q) (χ : D.X) : Q (-χ) = Q χ := by
  have hL := D.P.isLB
  have hsym := genHasVal_pullGen_of (ϖ := ϖ) D.P.L _ _ D.sym D.sym_gen (D.c χ).left (D.xK χ)
    (QForm.ptK_eq D χ)
  have h1 := genHasVal_mulGen hϖ D.P.L hL _ _ _ _ _ _ _ _ _ _ (hQ (-χ)) hsym
  have := qVal_unique hϖ D
    (genHasVal_corr hϖ D.P.L hL D.P.A.hom _ _ _ _ _ _ _ _ (by secTac) (by secTac) _ _ (D.psi_gen χ) (hE χ) h1) (hQ χ)
  linarith

include hϖ in

theorem Q_zero' (hB : D.TauBimult) (hQ : QForm.IsQ D ϖ Q) : Q 0 = 0 := by
  have h := bOf_add_left' hϖ D hB hQ 0 0 0
  simp only [QForm.bOf, add_zero] at h
  linarith

theorem bOf_comm' (χ χ' : D.X) : QForm.bOf D Q χ χ' = QForm.bOf D Q χ' χ := by
  simp only [QForm.bOf, add_comm χ χ']; ring

include hϖ in

theorem two_Q_eq' (hB : D.TauBimult) (hE : D.PsiEven) (hQ : QForm.IsQ D ϖ Q) (χ : D.X) :
    2 * Q χ = QForm.bOf D Q χ χ := by
  have h0 := Q_zero' hϖ D hB hQ
  have hn := Q_neg' hϖ D hE hQ χ
  have hadd := bOf_add_left' hϖ D hB hQ χ (-χ) χ
  have hc := bOf_comm' D (Q := Q) χ (-χ)
  simp only [QForm.bOf, add_neg_cancel, neg_add_cancel, zero_add, h0, hn] at hadd hc ⊢
  linarith

end Form

theorem assoc_of_hasVal {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a : V} {n : ℤ}
    (h : HasVal ϖ (algebraMap V (FractionRing V) a) n) : 0 ≤ n ∧ Associated a (ϖ ^ n.toNat) := by
  obtain ⟨v, hv⟩ := h
  have hinj := IsFractionRing.injective V (FractionRing V)
  rcases le_or_gt 0 n with hn | hn
  · refine ⟨hn, ?_⟩
    lift n to ℕ using hn
    rw [zpow_natCast, ← map_pow, ← map_mul] at hv
    rw [Int.toNat_natCast]
    exact Associated.symm (⟨v, (hinj hv).symm⟩ : Associated (ϖ ^ n) a)
  · exfalso
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = -((k + 1 : ℕ) : ℤ) := ⟨(-n - 1).toNat, by omega⟩
    have hϖ0 : algebraMap V (FractionRing V) ϖ ≠ 0 := (map_ne_zero_iff _ hinj).2 hϖ.ne_zero
    have h2 : algebraMap V (FractionRing V) (a * ϖ ^ (k + 1)) = algebraMap V (FractionRing V) v := by
      rw [map_mul, map_pow, hv, zpow_neg, zpow_natCast]
      field_simp
    have h3 : a * ϖ ^ (k + 1) = v := hinj h2
    exact hϖ.not_isUnit (isUnit_of_dvd_unit
      (h3 ▸ dvd_mul_of_dvd_right (dvd_pow_self ϖ (Nat.succ_ne_zero k)) a) v.isUnit)

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [CharZero R], IsIntegrallyClosed R →
    ∀ (Dg : DegData R (maximalIdeal R)) (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] (f : R →+* W),
    Function.Injective f → ∀ ϖ : W, Irreducible ϖ →
    ∃ be : LinearMap.BilinForm ℤ Dg.toPre.X, (∀ y z, be y z = be z y) ∧ FormAt Dg.toPre f ϖ be := by
  intro R _ _ _ _ hR Dg W _ _ _ f hf ϖ hϖ
  obtain ⟨W₀, hW₀, hψ⟩ := GlobalTheory.PsiSpread.exists_psiOn Dg.toPre Dg.tau_bimult
  have hη : (specOf f).base (genericPoint (Spec (CommRingCat.of W))) ∈ W₀ := by
    have : (specOf f).base (genericPoint (Spec (CommRingCat.of W))) = genericPoint (Spec (CommRingCat.of R)) := by
      rw [genericPoint_eq_bot_of_affine, genericPoint_eq_bot_of_affine]
      exact PrimeSpectrum.ext (Ideal.comap_bot_of_injective f hf)
    rw [this]; exact hW₀
  obtain ⟨D', hD, -, -⟩ := GlobalTheory.StrictPull.exists_isPullDeg_strict GlobalTheory.allSixLaws.1 R W f Dg.toPre W₀ hψ hη
  have hB : D'.TauBimult := GlobalTheory.TauPull.tauBimult_pull GlobalTheory.globalFns_holds hD Dg.tau_bimult
  have hE : D'.PsiEven := GlobalTheory.PsiEvenPull.psiEven_pull GlobalTheory.globalFns_holds R W f Dg.toPre D' hD Dg.psi_even
  choose Q hQ using qVal_exists hϖ D'
  have hQ' : QForm.IsQ D' ϖ Q := hQ
  let B : D'.X →+ D'.X →+ ℤ :=
    AddMonoidHom.mk' (fun a => AddMonoidHom.mk' (fun b => QForm.bOf D' Q a b) (fun b b' => by
        rw [bOf_comm' D' (Q := Q) a (b + b'), bOf_add_left' hϖ D' hB hQ', bOf_comm' D' (Q := Q) b a,
          bOf_comm' D' (Q := Q) b' a]))
      (fun a a' => by ext b; simp [bOf_add_left' hϖ D' hB hQ'])
  have hBa : ∀ a b, B a b = QForm.bOf D' Q a b := fun _ _ => rfl
  let be : LinearMap.BilinForm ℤ Dg.toPre.X :=
    LinearMap.mk₂ ℤ (fun y z => B (hD.xe.symm y) (hD.xe.symm z))
      (fun y y' z => by simp only [map_add, AddMonoidHom.add_apply])
      (fun c y z => by simp only [map_zsmul, AddMonoidHom.smul_apply, smul_eq_mul])
      (fun y z z' => by simp only [map_add])
      (fun c y z => by simp only [map_zsmul, smul_eq_mul])
  have hbe : ∀ y z, be y z = QForm.bOf D' Q (hD.xe.symm y) (hD.xe.symm z) := fun _ _ => rfl
  refine ⟨be, fun y z => by rw [hbe, hbe, bOf_comm'], fun y => ?_⟩
  obtain ⟨r, hr, -⟩ := (GlobalTheory.PsiCoordLocal.main R Dg hR y).1
  have hr' : Formalism.L2.Pj.PsiCoord Dg.toPre (hD.xe (hD.xe.symm y)) r := by rw [AddEquiv.apply_symm_apply]; exact hr
  obtain ⟨u, hu⟩ := GlobalTheory.PelCoordPull.psiCoord_pull hD (hD.xe.symm y) r hr'
  obtain ⟨h0, hassoc⟩ := assoc_of_hasVal hϖ (GlobalTheory.ValForm.hasVal_coord (hQ (hD.xe.symm y)) hu)
  refine ⟨r, (Q (hD.xe.symm y)).toNat, hr, ?_, ?_⟩
  · rw [hbe, ← two_Q_eq' hϖ D' hB hE hQ', Int.toNat_of_nonneg h0]
  · exact (associated_unit_mul_left (f r) (u : W) u.isUnit).symm.trans hassoc

end GlobalTheory.PreValForm
