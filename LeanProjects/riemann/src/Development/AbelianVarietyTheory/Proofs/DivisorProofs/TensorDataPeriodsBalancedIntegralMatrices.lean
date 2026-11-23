import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OfFactorE
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.W8AddTransposeEqE8
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgIdemBinv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTrivialMumfordFormalSumLatticeAdditivityRelati
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.Mum

noncomputable section
open GlobalTheory.Mum.PolTens GlobalTheory.TensBal in

theorem GlobalTheory.Mum.PolTens.tauBal_polTens : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (Q : Data R) (D' : DegData R (maximalIdeal R))
    {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (h : IsUnit (W + W.transpose).det), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef →
    ∀ (pr : Fin r → (D'.toPre.P.A ⟶ Q.B)) (hl : IsLimit (Fan.mk D'.toPre.P.A pr)) (xe : D'.toPre.X ≃+ (Fin r → Q.X))
    (w : LB.Iso D'.toPre.P.L (LB.LinComb Q.M.L (tensφ pr) (tensε W))),
    (∀ i, IsMonHom (pr i)) → (∀ z i, D'.toPre.c z ≫ pr i = Q.c (xe z i)) → w.IsGen →
    (∀ y z J J', Good Q.M.L z J → Good D'.toPre.P.L z J' →
      val (D'.toPre.psi y) (𝟙 _) z J' = gm (D'.toPre.xK y) z _ (w.s (fun k => J (D'.toPre.xK y ≫ tensφ pr k), J' (D'.toPre.xK y))) *
        ∏ i, ∏ j, val (Q.tau (xe y i) (xe y j)) (𝟙 _) z J ^ W i j) →
    letI := PowLim.mod xe (symUnitOf W h)
    ∀ a : TensO (symUnitOf W h), D'.toPre.TauBal (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
      (fun y => a • y) (fun y => star a • y) := by
  intro R _ _ _ _ Q D' r W h _ pr hl xe w hpr hc hw hpsi
  letI := PowLim.mod xe (symUnitOf W h)
  intro a
  have hA := transpose_mul_eq W h a
  intro u' hu' hn' y y'
  have htr := triv_span xe hpr hc (span_sigP W _ _ hA)
  rw [flat_sigP] at htr
  obtain ⟨Ξ, hΞ, hΞ0, hΞv⟩ := htr
  refine corr_of_val D'.toPre.P.isLB fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := GlobalTheory.BoxFamily.exists_good_at Q.M.isLB z
  have key := ros_sig hl hpr w hw _ _ u' hu' hn' Ξ hΞ hΞ0 z J J' hJ hJ' y y'
  rw [hΞv z J hJ y y', tv_sigP Q xe W _ _ (fun y => a • y) (fun y => star a • y) (PowLim.xe_smul xe _ a)
    (PowLim.xe_smul xe _ (star a)) z J y y'] at key
  have prr := prod_ros (PowLim.act pr hl (TensO.mat _ a)) (PowLim.act pr hl (TensO.mat _ (star a)))
    (DVR.cP D'.toPre (TK R) y) (DVR.cP D'.toPre (TK R) y') (isoV w z J J')
  have l₁ : DVR.cP D'.toPre (TK R) y ≫ PowLim.act pr hl (TensO.mat _ a) = DVR.cP D'.toPre (TK R) (a • y) := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  have l₂ : DVR.cP D'.toPre (TK R) y' ≫ PowLim.act pr hl (TensO.mat _ (star a)) =
      DVR.cP D'.toPre (TK R) (star a • y') := by
    rw [DVR.cP, DVR.cP, PowLim.c_smul Q D'.toPre pr hl xe hc, Category.assoc]
  rw [l₁, l₂, ← DVR.cPoint_add, ← DVR.cPoint_add] at prr
  change ∏ k, isoV w z J J' (D'.toPre.pt2 y y' ≫ rosatiφ D'.toPre.P.A (PowLim.act pr hl (TensO.mat _ a))
    (PowLim.act pr hl (TensO.mat _ (star a))) k) ^ rosatiε k = _ at prr
  rw [prr] at key
  rw [val_mul hJ', val_pull hJ', Category.id_comp, tau_pol xe w hpsi hJ hJ', tau_pol xe w hpsi hJ hJ']
  have e0 : rosatiε 0 = 1 := rfl
  have e1 : rosatiε 1 = -1 := rfl
  have e2 : rosatiε 2 = -1 := rfl
  have e3 : rosatiε 3 = -1 := rfl
  have e4 : rosatiε 4 = 1 := rfl
  have e5 : rosatiε 5 = 1 := rfl
  have v0 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 0 = a • y + y' := rfl
  have v1 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 1 = a • y := rfl
  have v2 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 2 = y' := rfl
  have v3 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 3 = y + star a • y' := rfl
  have v4 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 4 = y := rfl
  have v5 : (![a • y + y', a • y, y', y + star a • y', y, star a • y'] : Fin 6 → D'.toPre.X) 5 = star a • y' := rfl
  rw [Fin.prod_univ_six] at key
  erw [v0, v1, v2, v3, v4, v5] at key
  simp only [e0, e1, e2, e3, e4, e5] at key
  apply Additive.ofMul.injective
  have k' := congrArg Additive.ofMul key
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow] at k' ⊢
  linear_combination (norm := abel) k'
