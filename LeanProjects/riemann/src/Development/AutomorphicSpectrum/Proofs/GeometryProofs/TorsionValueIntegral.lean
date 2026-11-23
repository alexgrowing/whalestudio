import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsWeightZeroSectionUnitIntegralTorsionPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsAdaptedBasisAtTraitVsGenericBasis
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLocalExtension
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsUUOver
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsClosed
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCompleteDVRCompletionIntegralIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsTorsFrameOfSymLift
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGtExtOfTorsion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNormalisedMulPullIsoOrigin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UtestGeomNonempty
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ModelTraitExtensionPolarisedFlatBundleIso
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsUniformisedChartAfterValuationRingExt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValExt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open GlobalTheory.TorsFrame

theorem normMul_of_gen {S : Scheme.{0}} (P : PolAV S) (ρ : LB.Gen (P.L.pull (eSec P.A))) (hρ : ρ.IsGen) (N : ℕ)
    (β : LB.Gen (LB.LinComb P.L (K := Fin 2) ![(mulA P.A N).left, 𝟙 P.A.left] ![1, -((N : ℤ) ^ 2)])) (hβ : β.IsGen) :
    ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A N).left] ![(N : ℤ) ^ 2, -1]),
      α.IsGen ∧ IsNormMul P.A P.L ρ N α ∧
      ∀ (Z : Scheme.{0}) (r r' : Z ⟶ P.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), r ≫ P.A.hom = r' ≫ P.A.hom →
        Good P.L z J → val α r z J * val β r z J = val α r' z J * val β r' z J := by
  have hL := P.isLB
  obtain ⟨α₁, h₁, v₁⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A N).left]) (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.invGen P.L _ _ β) (DVR.invGen_isGen _ _ _ _ hβ)
  obtain ⟨t, ht, hv⟩ := exists_gen hL (φ' := ![𝟙 P.A.left, (mulA P.A N).left]) (ε' := ![(N : ℤ) ^ 2, -1])
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, eSec_mulA, Category.comp_id]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen P.L _ _ _ _ α₁ (LB.pullGen P.L _ _ (LB.mulGen P.L _ _ _ _
      (LB.mulGen P.L _ _ _ _ (GeneratorPullback.powGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (N ^ 2))
        (LB.invGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ))
      (LB.invGen P.L _ _ (LB.pullGen P.L _ _ α₁ (eSec P.A)))) P.A.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ h₁ (DVR.pullGen_isGen _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.powGen_isGen _ _ _ _ hρ _) (DVR.invGen_isGen _ _ _ _ hρ))
      (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ h₁ _))) _))
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ P.A.left) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J →
      val t r z J * val β r z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) ρ (r ≫ P.A.hom) z J ^ (N ^ 2) *
          (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) ρ (r ≫ P.A.hom) z J)⁻¹ *
          (val α₁ ((r ≫ P.A.hom) ≫ eSec P.A) z J)⁻¹ := by
    intro Z r z J hJ
    rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
      v₁ _ _ z J hJ, val_inv, mul_comm ((val β r z J)⁻¹)]
    exact inv_mul_cancel_right _ _
  have hn : ∀ (Z : Scheme.{0}) (r : Z ⟶ S) (z : Z) (J : (Z ⟶ P.A.left) → P.L.ι), Good P.L z J → val t (r ≫ eSec P.A) z J =
        val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) ρ r z J ^ (N ^ 2) *
          (val (φ := fun _ : PUnit => eSec P.A) (ε := fun _ => 1) ρ r z J)⁻¹ := by
    intro Z r z J hJ
    have e : (r ≫ eSec P.A) ≫ P.A.hom = r := by rw [Category.assoc, eSec_hom, Category.comp_id]
    rw [hv _ _ z J hJ, val_mul hJ, val_pull hJ, e, val_mul hJ, val_mul hJ, val_inv, val_inv, val_pull hJ, val_powGen,
      mul_comm, inv_mul_cancel_right]
  refine ⟨t, ht, corr_of_val hL fun z J hJ => ?_, fun Z r r' z J e hJ => ?_⟩
  · refine (val_pull hJ _ _ _).trans ((hn _ _ z J hJ).trans (Eq.symm ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _)))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  · rw [key Z r z J hJ, key Z r' z J hJ, e]

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open GlobalTheory.UT.CoefBasic GlobalTheory.ZH GlobalTheory.ZH.SecValue

theorem exists_frame_of_norm {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F]
    [IsAlgClosed F] [Algebra (FractionRing R) F] (ρ : LB.Gen (A.L.pull (eSec A.A))) (hρ : ρ.IsGen) (N : ℕ) (hN : 1 ≤ N)
    (α : LB.Gen (LB.LinComb A.L (K := Fin 2) ![𝟙 A.A.left, (mulA A.A N).left] ![(N : ℤ) ^ 2, -1])) (hα : α.IsGen)
    (x : TFK (R := R) F ⟶ A.A) (hx : x ^ N = 1) :
    ∃ e : GlobalTheory.ZH.FrAt x, e.IsGen ∧ LB.Gen.Corr A.L _ _ _ _ (powFrame A.A A.L x e ((N : ℤ) ^ 2))
      (LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ α x.left) (rigT A.A A.L ρ (TFK (R := R) F) 1)) := by
  have hL := A.isLB
  have hsub : Subsingleton (TFK (R := R) F).left := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  obtain ⟨z₀⟩ := exists_pt (R := R) (F := F)
  obtain ⟨i, hi⟩ := exists_chart hL (x.left z₀)
  have hi' : ∀ p, x.left p ∈ A.L.U i := fun p => by
    rw [Subsingleton.elim p z₀]; exact hi
  have hle : ∀ j : Fin 1 → A.L.ι, LB.wchart A.L (fun _ : Fin 1 => x.left) j ≤ x.left ⁻¹ᵁ (A.L.U (j 0) ⊓ A.L.U i) :=
    fun j p hp => ⟨Set.mem_iInter.1 hp 0, hi' p⟩
  let e₀ : GlobalTheory.ZH.FrAt x := ⟨fun j => res (hle j) (pullU x.left _ (A.L.g (j 0) i))⟩
  have v₀ : ∀ (j : Fin 1 → A.L.ι) (p : (TFK (R := R) F).left), p ∈ LB.wchart A.L (fun _ : Fin 1 => x.left) j →
      gm (𝟙 _) p (LB.wchart A.L (fun _ : Fin 1 => x.left) j) (e₀.s j) = gm x.left p (A.L.U (j 0) ⊓ A.L.U i) (A.L.g (j 0) i) :=
    fun j p hp => (gm_res _ p (hle j) hp _).trans ((gm_pull _ x.left p _ (hle j hp) _).trans (by rw [Category.id_comp]))
  have he₀ : e₀.IsGen := by
    intro j j'
    apply unit_ext
    intro p hp
    have m₁ : x.left p ∈ A.L.U (j 0) := Set.mem_iInter.1 hp.1 0
    have m₂ : x.left p ∈ A.L.U (j' 0) := Set.mem_iInter.1 hp.2 0
    rw [map_mul, gm_res _ p _ hp, gm_res _ p _ hp]
    erw [v₀ j p hp.1, v₀ j' p hp.2, gm_linComb A.L _ _ (𝟙 _) p j j' hp.1 hp.2]
    rw [Fintype.prod_unique, zpow_one, Category.id_comp]
    exact (gm_cocycle hL x.left p m₁ m₂ (hi' p)).symm
  have e₁ : x.left ≫ (mulA A.A N).left = (TFK (R := R) F).hom ≫ eSec A.A := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hx]
    rfl
  let B₀ := LB.mulGen A.L _ _ _ _ (LB.pullGen A.L _ _ α x.left) (rigT A.A A.L ρ (TFK (R := R) F) 1)
  have hB₀ : B₀.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hα _) (GlobalTheory.ThetaReal.NormMul.rigT_isGen hρ 1)
  let d := LB.mulGen A.L _ _ _ _ B₀ (LB.invGen A.L _ _ (GeneratorPullback.powGen A.L _ _ e₀ (N ^ 2)))
  have hd : d.IsGen := DVR.mulGen_isGen _ _ _ _ _ _ _ hB₀ (DVR.invGen_isGen _ _ _ _ (DVR.powGen_isGen _ _ _ _ he₀ _))
  obtain ⟨t, ht, vt⟩ := exists_gen hL (K' := Empty) (φ' := Empty.elim) (ε' := Empty.elim)
    (fun U _ h => by
      simp only [Fintype.prod_sum_type, Fin.prod_univ_two, Fintype.prod_unique, Sum.elim_inl, Sum.elim_inr,
        Matrix.cons_val_zero, Matrix.cons_val_one, e₁, Category.comp_id, Finset.univ_eq_empty, Finset.prod_empty]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow, ofMul_one]
      module) d hd

  have htop : (⊤ : (TFK (R := R) F).left.Opens) ≤ LB.wchart A.L (Y := (TFK (R := R) F).left) (K := Empty) Empty.elim Empty.elim :=
    fun p _ => Set.mem_iInter.2 fun k => k.elim
  let u₀ : (Γ((TFK (R := R) F).left, ⊤))ˣ := res htop (t.s Empty.elim)
  have vu : ∀ (y : (TFK (R := R) F).left) (J : ((TFK (R := R) F).left ⟶ A.A.left) → A.L.ι),
      val t (𝟙 _) y J = gm (𝟙 _) y ⊤ u₀ := fun y J => by
    rw [val_of t _ y J Empty.elim fun k => k.elim]
    exact (gm_res _ y htop trivial _).symm
  obtain ⟨a, ha⟩ := kon_surj (R := R) (F := F) u₀.val
  have hinj : Function.Injective (kon R F) := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).1
  haveI : Nontrivial (Γ((TFK (R := R) F).left, ⊤)) := hinj.nontrivial
  have ha0 : a ≠ 0 := by
    rintro rfl
    rw [map_zero] at ha
    exact u₀.ne_zero ha.symm
  obtain ⟨ν, hν⟩ := IsAlgClosed.exists_pow_nat_eq a (n := N ^ 2) (by positivity)
  have hν0 : ν ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hν
    exact ha0 hν.symm
  let νu : (Γ((TFK (R := R) F).left, ⊤))ˣ := Units.map (kon R F : F →* _) (Units.mk0 ν hν0)
  have hνu : νu ^ (N ^ 2) = u₀ := Units.ext (by
    rw [Units.val_pow_eq_pow_val, ← ha, ← hν, map_pow]
    rfl)
  let e : GlobalTheory.ZH.FrAt x := ⟨fun j => e₀.s j * res le_top νu⟩
  have hres : ∀ j j' : Fin 1 → A.L.ι, res (inf_le_left : (A.L.LinComb (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)).U j ⊓
        (A.L.LinComb (Y := (TFK (R := R) F).left) (K := Fin 1) (fun _ => x.left) (fun _ => 1)).U j' ≤ _)
      (res le_top νu) = res inf_le_right (res le_top νu) := fun j j' => unit_ext fun p hp => by
    rw [gm_res _ p _ hp, gm_res _ p _ hp.1, gm_res _ p _ hp, gm_res _ p _ hp.2]
  have he : e.IsGen := fun j j' => by
    show res _ (e₀.s j * res le_top νu) = _ * res _ (e₀.s j' * res le_top νu)
    rw [map_mul, map_mul, he₀ j j', hres j j', _root_.mul_assoc]
  have ve : ∀ (y : (TFK (R := R) F).left) (J : ((TFK (R := R) F).left ⟶ A.A.left) → A.L.ι), Good A.L y J →
      val e (𝟙 _) y J = val e₀ (𝟙 _) y J * gm (𝟙 _) y ⊤ νu := fun y J hJ => by
    exact (map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (gm_res _ y le_top (hJ.mem _ _) _))
  refine ⟨e, he, corr_of_val hL fun y J hJ => ?_⟩
  have h₁ := vt _ (𝟙 _) y J hJ
  rw [vu, val_mul hJ, val_inv, GlobalTheory.TorsFrame.val_powGen] at h₁
  have h₂ : gm (𝟙 _) y ⊤ u₀ = (gm (𝟙 _) y ⊤ νu) ^ (N ^ 2) := by rw [← hνu, map_pow]
  rw [GlobalTheory.ThetaGeom.val_powFrame, ve y J hJ]
  have ek : ∀ W : ((TFK (R := R) F).left.presheaf.stalk y)ˣ, W ^ ((N : ℤ) ^ 2) = W ^ (N ^ 2) := fun W => by
    rw [← Nat.cast_pow, zpow_natCast]
  rw [ek, mul_pow, ← h₂, h₁]
  exact mul_inv_cancel_comm_assoc _ _

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors

theorem chart_calc {S : Type} [CommRing S] (cT s sj : S) (A Aj R Rj Y Yj g₀ gj : Sˣ) (M : ℕ)
    (hA : A = g₀ * (g₀ ^ M)⁻¹ * Aj) (hR : R = g₀ * Rj) (hY : Y = g₀ * (gj ^ M)⁻¹ * Yj) (hs : s = gj.val * sj)
    (h' : cT * (A.val * R.val ^ M) = s ^ M * Y.val) :
    cT * (Aj.val * Rj.val ^ M) = sj ^ M * Yj.val := by
  subst hA hR hY hs
  have e₁ : (((g₀ ^ M)⁻¹ : Sˣ) : S) * g₀.val ^ M = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  have e₂ : (((gj ^ M)⁻¹ : Sˣ) : S) * gj.val ^ M = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, inv_mul_cancel, Units.val_one]
  simp only [Units.val_mul] at h'
  refine g₀.isUnit.mul_left_cancel ?_
  generalize (((g₀ ^ M)⁻¹ : Sˣ) : S) = u₁ at *
  generalize (((gj ^ M)⁻¹ : Sˣ) : S) = v₁ at *
  linear_combination h' - (cT * g₀.val * Aj.val * Rj.val ^ M) * e₁ + (g₀.val * sj ^ M * Yj.val) * e₂

theorem gs_valF {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (z : Sp F) : gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (valF x U f)) = gs x z U f := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of F)).hom.hom ((x.appLE U ⊤ h).hom f)) =
      (x.appLE U ⊤ h).hom f := by
    exact congrArg (fun q => q.hom ((x.appLE U ⊤ h).hom f)) (Iso.hom_inv_id (Scheme.ΓSpecIso (CommRingCat.of F)))
  rw [valF, dif_pos h, e, GlobalTheory.TranslMove.gs_appLE (𝟙 _) x z U ⊤ h trivial f, Category.id_comp]

theorem torsVal_good {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) (s : H0 P.L 1) {F : Type}
    [Field F] {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (N : ℕ) (T : F) (h : TorsVal P s y N T) :
    ∃ wg : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), wg.IsGen ∧
      ∀ (z : (Over.mk b).left) (J : ((Over.mk b).left ⟶ G.left) → P.L.ι), Good P.L z J →
        gs (X := (Over.mk b).left) (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom T) *
            ((val wg (1 : Over.mk b ⟶ G).left z J).val *
              (val (L := P.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.rig (Over.mk b).hom z J).val ^ (N ^ 2)) =
          sval s y.left z J ^ (N ^ 2) * (val wg y.left z J).val := by
  obtain ⟨-, hyN, wg, i₀, i, hg, h₀, h₁, heq⟩ := h
  refine ⟨wg, hg, fun z J hJ => ?_⟩
  set o := (1 : Over.mk b ⟶ G).left with ho
  have a₀ : o ≫ ((𝟙 G : G ⟶ G) ^ N).left = o := by
    rw [ho, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  have b₀ : y.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = o := by
    rw [ho, ← Over.comp_left, MonObj.comp_pow, Category.comp_id, hyN]
  have mem₂ : ∀ (r : (Over.mk b).left ⟶ G.left) (p : (Over.mk b).left) (c d : P.L.ι), (r ≫ ((𝟙 G : G ⟶ G) ^ N).left) p ∈ P.L.U c → r p ∈ P.L.U d →
      r p ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![c, d] := fun r p c d hc hd => Set.mem_iInter.2 fun k => by
    fin_cases k
    · exact hc
    · exact hd

  have mo : ∀ p, o p ∈ P.L.U i₀ := fun p => h₀ (show p ∈ (⊤ : (Over.mk b).left.Opens) from trivial)
  have my : ∀ p, y.left p ∈ P.L.U i := fun p => h₁ (show p ∈ (⊤ : (Over.mk b).left.Opens) from trivial)
  have wA : ∀ p, o p ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![i₀, i₀] := fun p =>
    mem₂ o p i₀ i₀ (by rw [a₀]; exact mo p) (mo p)
  have wY : ∀ p, y.left p ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![i₀, i] := fun p =>
    mem₂ y.left p i₀ i (by rw [b₀]; exact mo p) (my p)
  have wS : ∀ p, y.left p ∈ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => i) := fun p =>
    Set.mem_iInter.2 fun _ => my p
  have wR : ∀ p, (Over.mk b).hom p ∈ LB.wchart P.L (fun _ : PUnit => eSec G) (fun _ => i₀) := fun p =>
    Set.mem_iInter.2 fun _ => mo p
  let cH : F →+* (Over.mk b).left.presheaf.stalk z :=
    ((((Over.mk b).left.presheaf.germ ((𝟙 (Over.mk b).left) ⁻¹ᵁ ⊤) z trivial).hom).comp ((Scheme.Hom.app (𝟙 (Over.mk b).left) ⊤).hom)).comp
      (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom
  have hcH : ∀ a, cH a = gs (X := (Over.mk b).left) (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom a) :=
    fun a => (gs_eq _ z ⊤ trivial _).symm
  have H := congrArg cH heq
  simp only [map_mul, map_pow, pow_one] at H
  have v₁ := gs_valF o _ (wg.s ![i₀, i₀]).val (fun p _ => wA p) z
  have v₂ := gs_valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val (fun p _ => wR p) z
  have v₃ := gs_valF y.left _ (s.f fun _ => i) (fun p _ => wS p) z
  have v₄ := gs_valF y.left _ (wg.s ![i₀, i]).val (fun p _ => wY p) z
  rw [hcH, hcH, hcH, hcH, hcH] at H
  erw [v₁, v₂, v₃, v₄] at H

  have u₁ := gs_unit o z _ (wA z) (wg.s ![i₀, i₀])
  have u₂ := gs_unit (X := (𝟙_ (Over S)).left) (Over.mk b).hom z _ (wR z) (P.rig.s fun _ => i₀)
  have u₄ := gs_unit y.left z _ (wY z) (wg.s ![i₀, i])
  erw [u₁, u₂, u₄] at H
  have mj₀ : o z ∈ P.L.U (J o) := hJ o
  have mj : y.left z ∈ P.L.U (J y.left) := hJ y.left
  have trf : ∀ (r : (Over.mk b).left ⟶ G.left) (c₀ c₁ d₀ d₁ : P.L.ι), trF (L := P.L) (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) (![1, -((N : ℤ) ^ 2)] : Fin 2 → ℤ) r z ![c₀, c₁] ![d₀, d₁] =
      gm (r ≫ ((𝟙 G : G ⟶ G) ^ N).left) z (P.L.U c₀ ⊓ P.L.U d₀) (P.L.g c₀ d₀) *
        (gm r z (P.L.U c₁ ⊓ P.L.U d₁) (P.L.g c₁ d₁) ^ (N ^ 2))⁻¹ := by
    intro r c₀ c₁ d₀ d₁
    rw [trF, Fin.prod_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Category.comp_id]
    rw [← Nat.cast_pow, zpow_natCast]
    rfl
  have vA : val wg o z J = gm o z (LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![J o, J o]) (wg.s ![J o, J o]) :=
    val_of wg o z J _ fun k => by
      fin_cases k
      · exact congrArg J a₀
      · exact congrArg J (Category.comp_id _)
  have vY : val wg y.left z J = gm y.left z (LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![J o, J y.left]) (wg.s ![J o, J y.left]) :=
    val_of wg y.left z J _ fun k => by
      fin_cases k
      · exact congrArg J b₀
      · exact congrArg J (Category.comp_id _)
  have mA := mem₂ o z (J o) (J o) (by rw [a₀]; exact mj₀) mj₀
  have mY := mem₂ y.left z (J o) (J y.left) (by rw [b₀]; exact mj₀) mj
  have hA := gen_trans hg o z (wA z) mA
  have hY := gen_trans hg y.left z (wY z) mY
  rw [trf, a₀, ← vA] at hA
  rw [trf, b₀, ← vY] at hY

  have vR : val (L := P.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.rig (Over.mk b).hom z J =
      gm (Over.mk b).hom z (LB.wchart P.L (fun _ : PUnit => eSec G) (fun _ => J o)) (P.rig.s fun _ => J o) :=
    val_of (L := P.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) P.rig _ z J _ fun _ => rfl
  have mR : (Over.mk b).hom z ∈ LB.wchart P.L (fun _ : PUnit => eSec G) (fun _ => J o) := Set.mem_iInter.2 fun _ => mj₀
  have hR := gen_trans (L := P.L) (φ := fun _ : PUnit => eSec G) (ε := fun _ => 1) (t := P.rig) P.rigGen (Over.mk b).hom z (wR z) mR
  rw [← vR, trF, Fintype.prod_unique, zpow_one] at hR
  have vS : sval s y.left z J = gs y.left z (LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => J y.left)) (s.f fun _ => J y.left) :=
    sval_of s y.left z J _ fun _ => congrArg J (Category.comp_id _)
  have mS : y.left z ∈ LB.wchart P.L (fun _ : Fin 1 => 𝟙 G.left) (fun _ => J y.left) := Set.mem_iInter.2 fun _ => mj
  have hS := sec_trans s y.left z (wS z) mS
  have et : trF (L := P.L) (fun _ : Fin 1 => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ)) y.left z (fun _ => i) (fun _ => J y.left) =
      gm y.left z (P.L.U i ⊓ P.L.U (J y.left)) (P.L.g i (J y.left)) := by
    rw [trF, Fintype.prod_unique]
    simp only [Nat.cast_one, zpow_one, Category.comp_id]
  rw [← vS, et] at hS
  exact chart_calc _ _ _ _ _ _ _ _ _ (gm o z (P.L.U i₀ ⊓ P.L.U (J o)) (P.L.g i₀ (J o)))
    (gm y.left z (P.L.U i ⊓ P.L.U (J y.left)) (P.L.g i (J y.left))) (N ^ 2) hA hR hY hS H

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open GlobalTheory.TranslMove GlobalTheory.ZH GlobalTheory.UT GlobalTheory.UT.CoefBasic

theorem unit_calc {U : Type} [CommGroup U] (m : ℕ) (W1 Wx u1 ux ax a1 p ex wg1 wgy r0 : U)
    (h1 : wgy = W1 * (Wx ^ m)⁻¹ * ux) (h2 : wg1 = W1 * (W1 ^ m)⁻¹ * u1) (h3 : ax * ux = a1 * u1)
    (h4 : a1 = p ^ m * p⁻¹) (h5 : ex ^ m = ax * p) (h6 : r0 = W1 * p) :
    wg1 * r0 ^ m = Wx ^ m * ex ^ m * wgy := by
  have h7 : ax = a1 * u1 * ux⁻¹ := eq_mul_inv_of_mul_eq h3
  subst h1 h2 h6 h4 h7
  rw [h5]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, mul_pow]
  module

theorem stalk_calc {S : Type} [CommRing S] (cT cC sv : S) (wg1 r0 wgy Wx ex : Sˣ) (m : ℕ)
    (h7 : cT * (wg1.val * r0.val ^ m) = sv ^ m * wgy.val) (h8 : sv = Wx.val * (cC * ex.val))
    (claim : wg1 * r0 ^ m = Wx ^ m * ex ^ m * wgy) : cT = cC ^ m := by
  have e₁ : cT * (wg1 * r0 ^ m).val = cC ^ m * (wg1 * r0 ^ m).val := by
    have e₂ : (wg1 * r0 ^ m).val = wg1.val * r0.val ^ m := by simp
    rw [e₂, h7, ← e₂, claim, h8]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    ring
  exact (Units.mul_left_inj _).1 e₁

theorem frame {Z : Scheme.{0}} {G₀ : Over Z} [GrpObj G₀] [IsCommMonObj G₀] (P₀ : RigLB G₀) (s₀ : H0 P₀.L 1)
    {R : Type} [CommRing R] [IsDomain R] (A : PolAV (Sp (FractionRing R))) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing R) F] (f : Sp (FractionRing R) ⟶ Z) (φ : A.A.left ⟶ G₀.left)
    (w : LB.Iso A.L (P₀.L.pull φ)) (ρ : LB.Gen (A.L.pull (eSec A.A)))
    (hR : GlobalTheory.OneBasis.RigPull A.A G₀ f φ w ρ P₀.rig) (t : GlobalTheory.UT.SecA A F 1) (x : TFK (R := R) F ⟶ A.A)
    (hst : ∀ (z : (TFK (R := R) F).left) (J₀ : ((TFK (R := R) F).left ⟶ G₀.left) → P₀.L.ι)
        (J : ((TFK (R := R) F).left ⟶ A.A.left) → A.L.ι), Good P₀.L z J₀ → Good A.L z J →
      sval s₀ (x.left ≫ φ) z J₀ = (GlobalTheory.TranslMove.wv w z J₀ J x.left).val * GlobalTheory.UT.sA t (ptSecT A.A x).left z J)
    {b : Sp F ⟶ Z} (y : Over.mk b ⟶ G₀) (hy : x.left ≫ φ = y.left) (N : ℕ) (T : F)
    (h : TorsVal P₀ s₀ y N T) :
    ∃ (e : GlobalTheory.ZH.FrAt x) (c : F), IsTorsFrame A ρ N x e ∧ GlobalTheory.ZH.ValAt t x e c ∧ T = c ^ (N ^ 2) := by
  obtain ⟨gp, hw, hρ, pm⟩ := id hR
  have hN : 1 ≤ N := h.1
  have hy1 : (𝟙 (Sp F) : (TFK (R := R) F).left ⟶ (Over.mk b).left) ≫ y.left = x.left ≫ φ := by
    rw [hy]; exact Category.id_comp _
  have ptp := fun n => pt_pow gp (T := TFK (R := R) F) (T₀ := Over.mk b) (τ := 𝟙 (Sp F)) (x := x) (x₀ := y) hy1 n
  have hone : (1 : TFK (R := R) F ⟶ A.A).left ≫ φ = (1 : Over.mk b ⟶ G₀).left := by
    have := ptp 0
    rw [pow_zero, pow_zero] at this
    exact this.symm.trans (Category.id_comp _)
  have hxN : x ^ N = 1 := by
    refine Over.OverMorphism.ext (gp.1.hom_ext ?_ ?_)
    · have := ptp N
      rw [h.2.1] at this
      rw [← this, hone]
      exact Category.id_comp _
    · rw [Over.w, Over.w]

  obtain ⟨wg, hwg, hval⟩ := torsVal_good P₀ s₀ y N T h
  have hcomm : φ ≫ ((𝟙 G₀ : G₀ ⟶ G₀) ^ N).left = (mulA A.A N).left ≫ φ :=
    pt_pow gp (T := A.A) (T₀ := G₀) (x := 𝟙 A.A) (x₀ := 𝟙 G₀) ((Category.comp_id _).trans (Category.id_comp _).symm) N
  obtain ⟨u, hu, hrel⟩ := exists_genRel P₀.isLB A.isLB hw φ (a := (mulA A.A N).left) (b := 𝟙 A.A.left) hcomm
    ((Category.comp_id _).trans (Category.id_comp _).symm) wg hwg
  obtain ⟨α, hα, hnorm, hαu⟩ := normMul_of_gen A ρ hρ N u hu
  obtain ⟨e, he, hcorr⟩ := exists_frame_of_norm A F ρ hρ N hN α hα x hxN
  obtain ⟨c, hc⟩ := GlobalTheory.ZH.SecValue.ValM.exists GlobalTheory.firstFiveLaws.1 (SecM.ofSec A.A t) he
  have hc' : GlobalTheory.ZH.ValAt t x e c := hc
  refine ⟨e, c, ⟨hxN, he, α, hα, hnorm, hcorr⟩, hc', ?_⟩
  obtain ⟨z⟩ := exists_pt (R := R) (F := F)
  obtain ⟨J, hJ⟩ := exists_good' (Z := (TFK (R := R) F).left) A.isLB z
  obtain ⟨J₀, hJ₀⟩ := exists_good' (Z := (TFK (R := R) F).left) P₀.isLB z
  have e₁ : x.left ≫ (mulA A.A N).left = (1 : TFK (R := R) F ⟶ A.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hxN]
  have e₂ : (1 : TFK (R := R) F ⟶ A.A).left ≫ (mulA A.A N).left = (1 : TFK (R := R) F ⟶ A.A).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  have f₁ := hrel _ x.left z J₀ J hJ₀ hJ
  have f₂ := hrel _ (1 : TFK (R := R) F ⟶ A.A).left z J₀ J hJ₀ hJ
  rw [e₁, Category.comp_id, hy] at f₁
  rw [e₂, Category.comp_id, hone] at f₂
  have f₃ := hαu _ x.left (1 : TFK (R := R) F ⟶ A.A).left z J (by rw [Over.w, Over.w]) hJ

  have f₄ : val α (1 : TFK (R := R) F ⟶ A.A).left z J =
      val (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (TFK (R := R) F).hom z J ^ (N ^ 2) *
        (val (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (TFK (R := R) F).hom z J)⁻¹ := by
    refine (val_pull hJ _ _ _).symm.trans ((val_corr hJ hnorm _).trans ((val_mul hJ _ _ _).trans
      (congrArg₂ (· * ·) ((map_zpow _ _ _).trans ?_) (val_inv _ _))))
    rw [← Nat.cast_pow, zpow_natCast]; rfl
  have f₅ : val e (𝟙 _) z J ^ (N ^ 2) = val α x.left z J *
      val (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (TFK (R := R) F).hom z J := by
    have := val_corr hJ hcorr (𝟙 _)
    have e₀ : 𝟙 (TFK (R := R) F).left ≫ (TFK (R := R) F).hom = (TFK (R := R) F).hom := Category.id_comp _
    have ek : val e (𝟙 _) z J ^ ((N : ℤ) ^ 2) = val e (𝟙 _) z J ^ (N ^ 2) := by rw [← Nat.cast_pow, zpow_natCast]
    rw [GlobalTheory.ThetaGeom.val_powFrame, val_mul hJ, val_pull hJ, GlobalTheory.TorsFrame.val_rigT ρ _ z hJ, Category.id_comp, e₀, ek] at this
    exact this
  have hb' : (Over.mk b).hom = (TFK (R := R) F).hom ≫ f := (Category.id_comp _).symm.trans (base_comm gp (T := TFK (R := R) F) (T₀ := Over.mk b) (τ := 𝟙 (Sp F)) (x := x) (x₀ := y) hy1)
  have he' := GlobalTheory.PolBaseChange.eSec_comm gp
  have f₆ := val_move (fun _ => he') pm (TFK (R := R) F).hom hJ₀ hJ
  rw [Fintype.prod_unique, zpow_one] at f₆

  have hzm : ∀ W : ((TFK (R := R) F).left.presheaf.stalk z)ˣ, W ^ (-((N : ℤ) ^ 2)) = (W ^ (N ^ 2))⁻¹ := fun W => by
    rw [zpow_neg, ← Nat.cast_pow, zpow_natCast]
  rw [zpow_one, hzm] at f₁ f₂
  have claim := unit_calc (N ^ 2) (GlobalTheory.TranslMove.wv w z J₀ J (1 : TFK (R := R) F ⟶ A.A).left)
    (GlobalTheory.TranslMove.wv w z J₀ J x.left) (val u (1 : TFK (R := R) F ⟶ A.A).left z J) (val u x.left z J) (val α x.left z J)
    (val α (1 : TFK (R := R) F ⟶ A.A).left z J)
    (val (φ := fun _ : PUnit => eSec A.A) (ε := fun _ => 1) ρ (TFK (R := R) F).hom z J) (val e (𝟙 _) z J) _ _ _
    f₁ f₂ f₃ f₄ f₅ f₆
  have f₇ := hval z J₀ hJ₀
  have f₈ := hst z J₀ J hJ₀ hJ
  have f₉ := hc' z J hJ

  have f₈' := f₈.trans (congrArg _ f₉)
  have ee : val e (𝟙 _) z J ^ ((1 : ℕ) : ℤ) = val e (𝟙 _) z J := by simp
  rw [GlobalTheory.ThetaGeom.val_powFrame, ee] at f₈'
  rw [hb', ← hy] at f₇
  rw [← hy] at claim
  have g := stalk_calc _ _ _ _ _ _ _ _ (N ^ 2) f₇ f₈' claim
  have g₂ : cst (R := R) F z T = (cst (R := R) F z c) ^ (N ^ 2) := g
  rw [cst_eq, cst_eq, ← map_pow] at g₂
  exact cstH_inj z g₂
end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors

theorem exists_pullAll {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (h : Y' ⟶ Y) (φ₁ : K → (Y' ⟶ X)) (hφ : ∀ a, φ₁ a = h ≫ φ a) (s : LB.Sec (LB.LinComb L φ ε)) :
    ∃ s₁ : LB.Sec (LB.LinComb L φ₁ ε), ∀ {Z : Scheme.{0}} (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι), Good L z J →
      sval s₁ r z J = sval s (r ≫ h) z J := by
  obtain rfl : φ₁ = fun a => h ≫ φ a := funext hφ
  exact ⟨_, fun r z J hJ => SectionScalarValuation.sval_pullSec φ ε s h r z hJ⟩

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open IsLocalRing GlobalTheory.UT GlobalTheory.LN GlobalTheory.OneBasis

theorem core {Z : Scheme.{0}} {G₀ : Over Z} [GrpObj G₀] [IsCommMonObj G₀] (P₀ : RigLB G₀) (s₀ : H0 P₀.L 1)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V]
    (hc : IsAdicComplete (maximalIdeal V) V) (ϖ : V) (hϖ : Irreducible ϖ) (D : DegData V (maximalIdeal V))
    (Q : D.toPre.X → ℤ) (hQ : QForm.IsQ D.toPre ϖ Q) (F : Type) [Field F] [IsAlgClosed F]
    [Algebra (FractionRing V) F] (v : AddValuation F (WithTop ℚ)) (hv : ValOver ϖ F v)
    (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G] (hG : IsSemiAbelian G)
    (U : Unif (maximalIdeal V) D A G) (χ : Sp V ⟶ Z) (Φ : G.left ⟶ G₀.left) (ω : LB.Iso U.LG.L (P₀.L.pull Φ))
    (hRP : RigPull G G₀ χ Φ ω U.LG.rig P₀.rig) {b : Sp F ⟶ Z} (hb : b = jFK (R := V) F ≫ jK V ≫ χ)
    (y : Over.mk b ⟶ G₀) (N : ℕ) (T : F) (h : TorsVal P₀ s₀ y N T) : 0 ≤ v T := by
  have hLL : LL := GlobalTheory.firstFiveLaws
  have hTB := GlobalTheory.twistBaseChange
  have hT := twistBCSpan_of hTB
  have hVR : TWM.VRatioGtStatement := GlobalTheory.RatioVal.main
  have hTW := (GlobalTheory.twisting_statements_of_laws hLL.1 hTB).1
  have hUU : UUStatement := GlobalTheory.UnitBallFree.main hLL.1.globalFns hTB
  have hB : AdmBase V (maximalIdeal V) := ⟨inferInstance, inferInstance, inferInstance, hc⟩
  obtain ⟨hbij, hlin⟩ := expBijF_and_expandsF_lin hLL V _ hB D A G hG U
  obtain ⟨φ, w, ρ, w₀, hR, hW, hbr⟩ := GlobalTheory.OneBasis.Bridge.exists_bridge Z G₀ P₀.L P₀.isLB P₀.rig V _ D A G U.toUnifPre χ Φ ω hRP
  have cal := GlobalTheory.OneBasis.Calc.main Z G₀ P₀.L P₀.isLB V (jK V ≫ χ) A φ w hR.1 hR.2.1 F
  obtain ⟨r, cls, mu, f, hf, hs⟩ := GlobalTheory.OneBasis.AdaptedFamily.main hLL V ϖ hϖ D Q hQ 1 le_rfl
  choose s hs using hs F
  obtain ⟨σ, hσ, hσb⟩ := GlobalTheory.OneBasis.ModelBasis.main hLL V D Q A G U 1 le_rfl r cls mu f hf
  obtain ⟨bb, hb₁, hb'⟩ := hbr 1 r σ hσb
  choose bF hbF using fun i => ((cal 1).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) (bb i)).exists
  have hN := GlobalTheory.OneBasis.NormsPf.norms_of_adapted hLL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv 1 le_rfl r cls mu f s hf hs
  have hE := fun i => hb' i F (f i) (s i) (bF i) (hσ i) (hs i) (hbF i)
  obtain ⟨s₁, hs₁⟩ := exists_pullAll (L := P₀.L) (φ := fun _ : Fin 1 => 𝟙 G₀.left) (ε := fun _ => ((1 : ℕ) : ℤ))
    (snd (Over.mk χ) G₀).left (fun _ => (snd (Over.mk χ) G₀).left) (fun _ => (Category.comp_id _).symm) s₀
  obtain ⟨t, ht⟩ := ((cal 1).1 (Over.mk χ) (jFK (R := V) F ≫ jK V) (Category.assoc _ _ _) s₁).exists
  obtain ⟨c, hc'⟩ := (hb₁ s₁).exists
  obtain ⟨c, rfl⟩ := GlobalTheory.GBasis.fnR_surj c
  let ga : V →+* F := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V))
  have hga : spMap ga = jFK (R := V) F ≫ jK V := Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _)
  have hcm : Cmb bF (fun i => ga (c i)) t := by
    refine (cal 1).2.1 V χ (Over.mk χ) (𝟙 _) ga (by rw [hga, Category.assoc]) r bb c s₁ bF t hc' (fun i => ?_) ?_
    · have e : spMap ga ≫ (𝟙 (Over.mk χ) : _ ⟶ _).left = spMap ga := Category.comp_id _
      rw [e, hga]
      exact hbF i
    · rw [hga]
      exact ht
  have hEt : U.ExpandsF F 1 w₀ t (∑ i, ga (c i) • s i) :=
    GlobalTheory.GBasis.cmb_rel (fun t => ((hbij F 1 le_rfl w₀ hW.1).1 t).exists) (hlin F 1 w₀) bF s _ t hE hcm

  have hν : NuGe D Q F v 1 (∑ i, ga (c i) • s i) 0 := by
    refine ((hN.2 _ 0).1).2 fun i => ?_
    have hq : Q (cls i) ≤ 0 := by
      have h₁ := hf.1.1 i (-(cls i))
      rw [one_smul, add_neg_cancel, QForm.Q_zero hϖ D hQ] at h₁
      exact h₁
    have hq' : (0 + (Q (cls i) : ℚ) / ((1 : ℕ) : ℚ)) ≤ 0 := by
      have : (Q (cls i) : ℚ) ≤ 0 := by exact_mod_cast hq
      simpa using this
    exact le_trans (WithTop.coe_le_coe.2 hq') (GlobalTheory.GBasis.val_nonneg hϖ hv (c i))
  have hw₀ : y.left ≫ G₀.hom = jFK (R := V) F ≫ jK V ≫ χ := by
    have := Over.w y
    simpa [hb] using this
  let xl : (TFK (R := V) F).left ⟶ A.A.left := hR.1.1.lift y.left (jFK (R := V) F) (by rw [hw₀])
  have hxl₁ : xl ≫ φ = y.left := hR.1.1.lift_fst _ _ _
  have hxl₂ : xl ≫ A.A.hom = jFK (R := V) F := hR.1.1.lift_snd _ _ _
  let x : TFK (R := V) F ⟶ A.A := Over.homMk xl hxl₂
  have hxy : x.left ≫ φ = y.left := hxl₁
  have hpt : (ptSecT A.A x).left ≫ (snd (TFK (R := V) F) A.A).left = x.left := by
    rw [← Over.comp_left, ptSecT, lift_snd]
  have hpf : (ptSecT A.A x).left ≫ (fst (TFK (R := V) F) A.A).left = 𝟙 _ := by
    rw [← Over.comp_left, ptSecT, lift_fst]
    rfl
  obtain ⟨H, hH₁, hH₂⟩ := GlobalTheory.OneBasis.Calc.exists_lift (T := Over.mk χ) (G := G₀) (jFK (R := V) F ≫ jK V) (x.left ≫ φ)
    (by rw [hxy, hw₀]; simp)
  have hst : ∀ (z : (TFK (R := V) F).left) (J₀ : ((TFK (R := V) F).left ⟶ G₀.left) → P₀.L.ι)
      (J : ((TFK (R := V) F).left ⟶ A.A.left) → A.L.ι), Good P₀.L z J₀ → Good A.L z J →
      sval s₀ (x.left ≫ φ) z J₀ = (GlobalTheory.TranslMove.wv w z J₀ J x.left).val * sA t (ptSecT A.A x).left z J := by
    intro z J₀ J g₀ g₁
    have e := ht _ (ptSecT A.A x).left H (by rw [hH₁, ← Category.assoc, hpf, Category.id_comp])
      (by rw [hH₂, ← Category.assoc, hpt]) z J₀ J g₀ g₁
    rw [hs₁ H z J₀ g₀, hH₂, pow_one] at e
    rw [e]
    simp only [hpt]
    rfl
  obtain ⟨e, c₁, he, hval, rfl⟩ := frame P₀ s₀ A F (jK V ≫ χ) φ w ρ hR t x hst y hxy N T h
  obtain ⟨ft, hft⟩ := GlobalTheory.TorsionIso.exists_tors_closed V _ hB D A G hG U F N h.1
  obtain ⟨p, hp⟩ := hft.2.1 x he.1
  have hqx : QkToAkU U.toUnifPre F N p x := (hft.1 p x).2 hp.symm
  have h0 := GlobalTheory.ZH.WeightZeroUnit.value_nonneg_all hLL hT hVR hTW hUU V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hW N h.1 p x
    hqx e he t _ c₁ hEt hν hval
  rw [AddValuation.map_pow]
  exact nsmul_nonneg h0 _
end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open IsLocalRing GlobalTheory.UT GlobalTheory.LN GlobalTheory.OneBasis IsDedekindDomain Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem integral_of_places {K : Type} [Field K] [NumberField K] (x : K)
    (h : ∀ w : HeightOneSpectrum (𝓞 K), w.valuation K x ≤ 1) : IsIntegral ℤ x := by
  obtain ⟨a, rfl⟩ := HeightOneSpectrum.mem_integers_of_valuation_le_one K x h
  exact RingOfIntegers.isIntegral_coe a

theorem valuation_le_one_of_isIntegral {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K)) {x : K}
    (h : IsIntegral ℤ x) : w.valuation K x ≤ 1 := by
  have := w.valuation_le_one (K := K) (⟨x, h⟩ : 𝓞 K)
  exact this

theorem polAt_generic {L : Type} [Field L] [NumberField L] (D : PPData H L) :
    PolAt D.t (spMap (algebraMap (𝓞 L) L)) := by
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull (𝟙 _ ≫ spMap (algebraMap (𝓞 L) L)) D.t
  obtain ⟨m₃, -⟩ := sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ D.m m₂
  have h₂ : LBIso PP'.L (D.t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
  rw [hm₂] at h₂
  have h₃ : LBIso PP'.L (D.tK.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
  have hL := LB.isLB_pull D.t.PP.isLB (pullback.fst D.t.G.hom (𝟙 _ ≫ spMap (algebraMap (𝓞 L) L)))
  have : PolAt D.t (𝟙 _ ≫ spMap (algebraMap (𝓞 L) L)) :=
    ⟨MorphismProperty.of_isPullback (P := @IsProper) m₃.cart.1 D.princ.1,
    amplePt _ _ (𝟙 _) _ _ m₃.φ m₃.cart _ _ D.tK.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull D.tK.PP.isLB _) h₂.symm h₃) D.princ.2.1 D.princ.2.2⟩
  simpa using this

theorem injective_of_charZero {L : Type} [Field L] [NumberField L] {B : Type} [Field B] [CharZero B] (ψ : 𝓞 L →+* B) :
    Function.Injective ψ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [eq_bot_iff]
  intro n hn
  have h0 : ψ (algebraMap ℤ (𝓞 L) n) = 0 := hn
  have h1 : ((n : ℤ) : B) = 0 := by simpa using h0
  exact (Ideal.mem_bot).2 (Int.cast_eq_zero.1 h1)

theorem exists_ext {L : Type} [Field L] [NumberField L] (D : PPData H L) (T₀ : CDVR) (κ : 𝓞 L →+* T₀.V) :
    ∃ (T' : CDVR) (φ : T₀.V →+* T'.V) (t' : SAB H (Sp T'.V)), Function.Injective φ ∧ IsLocalHom φ ∧
      Nonempty (SABMap t' D.t (spMap (φ.comp κ))) ∧ Nonempty (PELUnif (maximalIdeal T'.V) t') := by
  obtain ⟨t, ⟨m₁⟩⟩ : ∃ t : SAB H (Sp T₀.V), Nonempty (SABMap t D.t (spMap κ)) := by
    obtain ⟨PP₁, cub₁, sym₁, adj₁, prim₁, m₁, -⟩ := sabPull Out.CubePf.cubePull (spMap κ) D.t
    exact ⟨_, ⟨m₁⟩⟩
  have : CharZero T₀.Fr := charZero_of_injective_algebraMap (IsFractionRing.injective T₀.V T₀.Fr)
  let ψ : 𝓞 L →+* T₀.Fr := (algebraMap T₀.V T₀.Fr).comp κ
  have hψ : Function.Injective ψ := injective_of_charZero ψ
  let ιL : L →+* T₀.Fr := IsFractionRing.lift hψ
  have hιL : ∀ a : 𝓞 L, ιL (algebraMap (𝓞 L) L a) = ψ a := fun a => IsFractionRing.lift_algebraMap hψ a
  have hp : PolAt t (jK T₀.V) := GlobalTheory.DatUniq.polAt_pull m₁ (polAt_generic D) (jK T₀.V) (spMap ιL)
    ((GlobalTheory.Ex.UnifModel.spMap_comp hιL).trans (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  let F := AlgebraicClosure (FractionRing T₀.V)
  have hF : Function.Injective (algebraMap T₀.V F) := by
    rw [IsScalarTower.algebraMap_eq T₀.V (FractionRing T₀.V) F]
    exact (algebraMap (FractionRing T₀.V) F).injective.comp (IsFractionRing.injective T₀.V _)
  have : FaithfulSMul T₀.V F := (faithfulSMul_iff_algebraMap_injective _ _).2 hF
  have : Algebra.IsAlgebraic T₀.V F := (IsFractionRing.comap_isAlgebraic_iff (K := FractionRing T₀.V)).2 inferInstance
  obtain ⟨W, hd, hc, hf, hs⟩ := GlobalTheory.Ex.UnifModel.exists_split T₀.V F t.G t.semi
  have hi : Function.Injective (algebraMap T₀.V W) := fun _ _ h => hF (congrArg (fun z : W => (z : F)) h)
  have hz : CharZero W := charZero_of_injective_ringHom hi
  have : FaithfulSMul T₀.V W := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have hl : IsLocalHom (algebraMap T₀.V W) := inferInstance
  obtain ⟨PP', cub, sym, adj, prim, m, -⟩ := sabPull Out.CubePf.cubePull (spMap (algebraMap T₀.V W)) t
  have j : Function.Injective ((algebraMap W (FractionRing W)).comp (algebraMap T₀.V W)) :=
    (IsFractionRing.injective W _).comp hi
  let g : FractionRing T₀.V →+* FractionRing W := IsFractionRing.lift j
  have hp' := GlobalTheory.DatUniq.polAt_pull m hp (jK W) (spMap g)
    ((GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).symm)
  obtain ⟨P, -⟩ := GlobalTheory.LN.uDvrSt_holds E H W ⟨hd, hc, hz⟩ _ hp' hs
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ m₁ m
  have e : spMap (algebraMap T₀.V W) ≫ spMap κ = spMap ((algebraMap T₀.V W).comp κ) :=
    GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
  exact ⟨{ V := W }, algebraMap T₀.V W, _, hi, hl, ⟨e ▸ n⟩, ⟨P⟩⟩

theorem mem_range_of_val {T₀ T' : CDVR} (φ : T₀.V →+* T'.V) [IsLocalHom φ] (g : T₀.Fr →+* T'.Fr)
    (hg : ∀ a, g (algebraMap T₀.V T₀.Fr a) = algebraMap T'.V T'.Fr (φ a)) {ϖ : T'.V} (hϖ : Irreducible ϖ)
    {F : Type} [Field F] [Algebra T'.Fr F] {v : AddValuation F (WithTop ℚ)} (hv : ValOver ϖ F v) (x : T₀.Fr)
    (h : 0 ≤ v (algebraMap T'.Fr F (g x))) : x ∈ (algebraMap T₀.V T₀.Fr).range := by
  by_cases hx : x = 0
  · rw [hx]; exact zero_mem _
  obtain ha | ⟨a, ha⟩ := ValuationRing.isInteger_or_isInteger T₀.V x
  · exact ha
  by_cases hu : IsUnit a
  · obtain ⟨u, rfl⟩ := hu
    refine ⟨(u⁻¹ : T₀.V ˣ), ?_⟩
    have e : algebraMap T₀.V T₀.Fr (u⁻¹ : T₀.V ˣ) * algebraMap T₀.V T₀.Fr u = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    rw [ha] at e
    exact (eq_inv_of_mul_eq_one_left e).trans (inv_inv x)
  exfalso
  have hnu : ¬ IsUnit (φ a) := fun h' => hu ((isUnit_map_iff φ a).1 h')
  have hmem : φ a ∈ maximalIdeal T'.V := hnu
  rw [hϖ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
  obtain ⟨b, hb⟩ := hmem
  let i : T'.V →+* F := (algebraMap T'.Fr F).comp (algebraMap T'.V T'.Fr)
  have h1 : v (i ϖ) = ((1 : ℚ) : WithTop ℚ) := by
    have := hv (algebraMap T'.V T'.Fr ϖ) 1 ⟨1, by simp⟩
    simpa [i] using this
  have h2 : 0 ≤ v (i b) := GlobalTheory.GBasis.val_nonneg hϖ hv b
  have e : (algebraMap T'.Fr F (g x))⁻¹ = i ϖ * i b := by
    rw [← map_mul, ← hb, ← map_inv₀, ← map_inv₀, ← ha, hg]
    rfl
  have h3 : v (algebraMap T'.Fr F (g x)) + v ((algebraMap T'.Fr F (g x))⁻¹) = 0 := by
    rw [← AddValuation.map_mul, mul_inv_cancel₀, AddValuation.map_one]
    exact (map_ne_zero _).2 ((map_ne_zero g).2 hx)
  rw [e, AddValuation.map_mul, h1] at h3
  have h4 : ((1 : ℚ) : WithTop ℚ) ≤ 0 := by
    calc ((1 : ℚ) : WithTop ℚ) = 0 + (((1 : ℚ) : WithTop ℚ) + 0) := by simp
      _ ≤ v (algebraMap T'.Fr F (g x)) + (((1 : ℚ) : WithTop ℚ) + v (i b)) := add_le_add h (add_le_add le_rfl h2)
      _ = 0 := h3
  have : (1 : ℚ) ≤ 0 := by exact_mod_cast h4
  linarith

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors

theorem torsVal_map {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (P : RigLB G) (s : H0 P.L 1) {F F' : Type}
    [Field F] [Field F'] (f : F →+* F') {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) (y' : Over.mk (spMap f ≫ b) ⟶ G)
    (hy : y'.left = spMap f ≫ y.left) (N : ℕ) (T : F) (h : TorsVal P s y N T) : TorsVal P s y' N (f T) := by
  obtain ⟨hN, hyN, wg, i₀, i, hg, h₀, h₁, heq⟩ := h
  let hh : Over.mk (spMap f ≫ b) ⟶ Over.mk b := Over.homMk (spMap f) rfl
  have eY : y' = hh ≫ y := Over.OverMorphism.ext hy
  have hone : (1 : Over.mk (spMap f ≫ b) ⟶ G).left = spMap f ≫ (1 : Over.mk b ⟶ G).left := by
    rw [GlobalTheory.TorsFrame.one_left, GlobalTheory.TorsFrame.one_left]
    exact Category.assoc _ _ _
  have a₀ : (1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, one_pow]
  have b₀ : y.left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id, hyN]
  have mem₂ : ∀ (r : (Over.mk b).left ⟶ G.left) (p : (Over.mk b).left) (c d : P.L.ι),
      (r ≫ ((𝟙 G : G ⟶ G) ^ N).left) p ∈ P.L.U c → r p ∈ P.L.U d →
      r p ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![c, d] := fun r p c d hc hd => Set.mem_iInter.2 fun k => by
    fin_cases k
    · exact hc
    · exact hd
  have mo : ∀ p, (1 : Over.mk b ⟶ G).left p ∈ P.L.U i₀ := fun p => h₀ (show p ∈ (⊤ : (Over.mk b).left.Opens) from trivial)
  have my : ∀ p, y.left p ∈ P.L.U i := fun p => h₁ (show p ∈ (⊤ : (Over.mk b).left.Opens) from trivial)
  have wA : ⊤ ≤ (1 : Over.mk b ⟶ G).left ⁻¹ᵁ (LB.LinComb P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![1, -((N : ℤ) ^ 2)]).U ![i₀, i₀] := fun p _ =>
    mem₂ _ p i₀ i₀ (by rw [a₀]; exact mo p) (mo p)
  have wY : ⊤ ≤ y.left ⁻¹ᵁ (LB.LinComb P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![1, -((N : ℤ) ^ 2)]).U ![i₀, i] := fun p _ =>
    mem₂ _ p i₀ i (by rw [b₀]; exact mo p) (my p)
  have wS : ⊤ ≤ y.left ⁻¹ᵁ (LB.LinComb P.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => ((1 : ℕ) : ℤ))).U (fun _ => i) := fun p _ =>
    Set.mem_iInter.2 fun _ => my p
  have wR : ⊤ ≤ b ⁻¹ᵁ (P.L.pull (eSec G)).U (fun _ => i₀) := fun p _ => Set.mem_iInter.2 fun _ => mo p
  refine ⟨hN, ?_, wg, i₀, i, hg, ?_, ?_, ?_⟩
  · rw [eY, ← MonObj.comp_pow, hyN]
    exact Over.OverMorphism.ext hone.symm
  · rw [hone]
    exact fun p _ => mo (spMap f p)
  · rw [hy]
    exact fun p _ => my (spMap f p)
  · rw [hone, hy, GlobalTheory.ArcExt.valF_ext f _ _ wA, GlobalTheory.ArcExt.valF_ext f _ _ wR, GlobalTheory.ArcExt.valF_ext f _ _ wS,
      GlobalTheory.ArcExt.valF_ext f _ _ wY]
    have := congrArg f heq
    simpa only [map_mul, map_pow] using this

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors

namespace GlobalTheory.CompanionTheory.Ar.Sl.IntTors
open IsLocalRing GlobalTheory.UT GlobalTheory.LN GlobalTheory.OneBasis IsDedekindDomain Formalism.L2.Pj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem local_step {L : Type} [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) {K : Type} [Field K]
    (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K) (hT : TorsVal D.t.PP th y N T)
    (T₀ : CDVR) (io : K →+* T₀.Fr) (hio : ∀ a, io (c a) ∈ Set.range (algebraMap T₀.V T₀.Fr)) :
    io T ∈ Set.range (algebraMap T₀.V T₀.Fr) := by
  have hinj : Function.Injective (algebraMap T₀.V T₀.Fr) := IsFractionRing.injective _ _
  choose κf hκf using hio
  let κ : 𝓞 L →+* T₀.V :=
    { toFun := κf
      map_one' := hinj (by rw [hκf, map_one, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hκf, map_mul, map_mul, map_mul, hκf, hκf])
      map_zero' := hinj (by rw [hκf, map_zero, map_zero, map_zero])
      map_add' := fun a b => hinj (by rw [hκf, map_add, map_add, map_add, hκf, hκf]) }
  have hκ : ∀ a, algebraMap T₀.V T₀.Fr (κ a) = io (c a) := hκf
  obtain ⟨T', φ, t', hφ, hloc, ⟨m⟩, ⟨P⟩⟩ := exists_ext D T₀ κ
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  let F := AlgebraicClosure T'.Fr
  obtain ⟨v, hv⟩ := exists_valOver hϖ F
  choose Q hQ using QForm.exists_QVal hϖ P.D
  have hj : Function.Injective ((algebraMap T'.V T'.Fr).comp φ) := (IsFractionRing.injective _ _).comp hφ
  let g : T₀.Fr →+* T'.Fr := IsFractionRing.lift hj
  have hg : ∀ a, g (algebraMap T₀.V T₀.Fr a) = algebraMap T'.V T'.Fr (φ a) := fun a => IsFractionRing.lift_algebraMap hj a
  let f : K →+* F := (algebraMap T'.Fr F).comp (g.comp io)
  let y₁ : Over.mk (spMap f ≫ spMap c) ⟶ D.t.G := Over.homMk (spMap f ≫ y.left) (by
    have := Over.w y
    simp only [Over.mk_left, Over.mk_hom, Category.assoc] at this ⊢
    rw [this])
  have hT₁ := torsVal_map D.t.PP th f y y₁ rfl N T hT
  obtain ⟨ω, hω⟩ := GlobalTheory.ModelFacts.exists_rigPull m
  obtain ⟨ω', hω'⟩ : ∃ ω' : LB.Iso P.U.LG.L (D.t.PP.L.pull m.φ),
      RigPull t'.G D.t.G (spMap (φ.comp κ)) m.φ ω' P.U.LG.rig D.t.PP.rig := by
    rw [P.bundle]
    exact ⟨ω, hω⟩
  have hb : spMap f ≫ spMap c = jFK (R := T'.V) F ≫ jK T'.V ≫ spMap (φ.comp κ) := by
    have e₁ : spMap f ≫ spMap c = spMap (f.comp c) := GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
    have e₂ : jK T'.V ≫ spMap (φ.comp κ) = spMap ((algebraMap T'.V T'.Fr).comp (φ.comp κ)) :=
      GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
    have e₃ : jFK (R := T'.V) F ≫ spMap ((algebraMap T'.V T'.Fr).comp (φ.comp κ)) =
        spMap ((algebraMap T'.Fr F).comp ((algebraMap T'.V T'.Fr).comp (φ.comp κ))) :=
      GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl
    rw [e₂, e₃, e₁]
    congr 1
    ext a
    show algebraMap T'.Fr F (g (io (c a))) = algebraMap T'.Fr F (algebraMap T'.V T'.Fr (φ (κ a)))
    rw [← hκ, hg]
  have h0 := core D.t.PP th T'.V inferInstance ϖ hϖ P.D Q hQ F v hv P.A t'.G t'.semi P.U (spMap (φ.comp κ)) m.φ ω' hω'
    hb y₁ N (f T) hT₁
  exact RingHom.mem_range.1 (mem_range_of_val φ g hg hϖ hv (io T) h0)

theorem integral_torsVal : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (th : Out.H0 D.t.PP.L 1) (K : Type) [Field K] [NumberField K] (c : 𝓞 L →+* K) (y : Over.mk (spMap c) ⟶ D.t.G) (N : ℕ) (T : K), TorsVal D.t.PP th y N T → IsIntegral ℤ T := by
  intro E _ _ _ H L _ _ D th K _ _ c y N T hT
  refine integral_of_places T fun w => ?_
  obtain ⟨T₀, iK, -, hiK⟩ := GlobalTheory.exists_cdvr_completion_integral_iff K w
  refine (hiK T).1 (local_step D th c y N T hT T₀ iK fun a => (hiK _).2 (valuation_le_one_of_isIntegral w ?_))
  exact (Algebra.IsIntegral.isIntegral (R := ℤ) a).map c.toIntAlgHom

end GlobalTheory.CompanionTheory.Ar.Sl.IntTors
