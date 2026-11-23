import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AdmissibleBaseOfCompleteNormalLocalCharZero
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLaws
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExpandsAtTransport
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.SqCube

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.LamBiext

section Transport

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']

theorem transport (hG : GlobalFnsSt) (hA' : IsAbelianScheme A') (Φ : A' ⟶ A) [IsMonHom Φ]
    {M : LB A.left} {M' : LB A'.left} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (M.pull Φ.left)) (hw : w.IsGen)
    (c : LB.Gen (LB.LinComb M (thφ A (x3 A)) thε)) (c' : LB.Gen (LB.LinComb M' (thφ A' (x3 A')) thε))
    (hc : c.IsGen) (hc' : c'.IsGen)
    (n : ∀ (y : (𝟙_ (Over S)).left) J, Good M y J →
      val c (lift (1 : 𝟙_ (Over S) ⟶ A) (lift 1 1)).left y J = 1)
    (n' : ∀ (y : (𝟙_ (Over S)).left) J, Good M' y J →
      val c' (lift (1 : 𝟙_ (Over S) ⟶ A') (lift 1 1)).left y J = 1)
    {T : Over S} {z : T.left} {J J'} (hJ : Good M z J) (hJ' : Good M' z J') (x x' y : T ⟶ A') :
    val c (lift (x ≫ Φ) (lift (x' ≫ Φ) (y ≫ Φ))).left z J =
      (∏ I : thK.{0}, gw w ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) z
        (J (((lift x (lift x' y)).left ≫ thφ A' (x3 A') I) ≫ Φ.left))
        (J' ((lift x (lift x' y)).left ≫ thφ A' (x3 A') I)) ^ thε I) * val c' (lift x (lift x' y)).left z J' := by
  let m3 : G3 A' ⟶ G3 A := lift (x3 A' 0 ≫ Φ) (lift (x3 A' 1 ≫ Φ) (x3 A' 2 ≫ Φ))
  let β : (G3 A' ⟶ A') →* (G3 A' ⟶ A) := MonoidHom.mk' (· ≫ Φ) fun a b => MonObj.mul_comp a b Φ
  have hx : ∀ i, m3 ≫ x3 A i = x3 A' i ≫ Φ := fun i => by fin_cases i <;> simp [m3, x3]
  have comm : ∀ I : thK.{0}, m3.left ≫ thφ A (x3 A) I = thφ A' (x3 A') I ≫ Φ.left := fun I => by
    have e : m3 ≫ psum A (x3 A) I.down = psum A' (x3 A') I.down ≫ Φ :=
      (psum_hom (Geo.Tor.preHom m3) (x3 A) I.down).trans ((congrArg (fun q => psum A q I.down) (funext hx)).trans
        (psum_hom β (x3 A') I.down).symm)
    exact congrArg (fun q => q.left) e
  have q : ∀ {T : Over S} (a b d : T ⟶ A'),
      (lift a (lift b d)).left ≫ m3.left = (lift (a ≫ Φ) (lift (b ≫ Φ) (d ≫ Φ))).left := fun a b d => by
    rw [← Over.comp_left]; congr 1; simp [m3, x3]
  obtain ⟨t, ht, hv⟩ := exists_up ((isGen_iff w).1 hw) hM hM' c' hc'
  have hv' : ∀ (Z : Scheme.{0}) (r : Z ⟶ (G3 A').left) (z : Z) J J', Good M z J → Good M' z J' →
      val t r z J = (∏ I : thK.{0}, gw w (r ≫ thφ A' (x3 A') I) z
        (J ((r ≫ thφ A' (x3 A') I) ≫ Φ.left)) (J' (r ≫ thφ A' (x3 A') I)) ^ thε I) * val c' r z J' :=
    fun Z r z J J' hJ hJ' => by
      refine (hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans
        (congrArg₂ (· * ·) (Finset.prod_congr rfl fun I _ => ?_) rfl)
      rw [Category.assoc]
  let e : 𝟙_ (Over S) ⟶ G3 A' := lift 1 (lift 1 1)
  have sj : Function.Surjective ((snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom).appTop.hom :=
    surj_comp (surj_snd hG hA' _) (surj_comp (surj_snd hG hA' _) (hG _ _ hA').2)
  have he : e.left ≫ (snd A' (A' ⊗ A')).left ≫ (snd A' A').left ≫ A'.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := gen_unique' hM (φ := fun I => m3.left ≫ thφ A (x3 A) I) (ε := thε)
    (fun V _ k => Finset.prod_congr rfl fun I _ => congrArg (fun q => k q ^ thε I) (comm I).symm)
    _ e.left he sj (pullGen_isGen _ _ _ _ hc m3.left) ht (fun y I hI => by
      choose I' hI' using fun χ : (𝟙_ (Over S)).left ⟶ A'.left => exists_chart hM' (χ y)
      have p := prod_cub (1 : 𝟙_ (Over S) ⟶ A') 1 1 (fun q => gw w q y (I (q ≫ Φ.left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine Eq.trans ?_ ((hv' _ e.left y I I' hI hI').trans (congrArg₂ (· * ·) p (n' y I' hI'))).symm
      rw [val_pull hI, q, MonObj.one_comp, n y I hI]
      simp) _ (lift x (lift x' y)).left z J hJ
  rw [val_pull hJ, q] at key
  exact key.trans (hv' _ _ z J J' hJ hJ')

end Transport

section Chart

variable {X Y : Scheme.{0}} {L : LB X}

theorem good_sq {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) :
    Good (LB.LinComb L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => 2)) y (fun q _ => J q) :=
  fun ψ => Set.mem_iInter.2 fun _ => by simpa using hJ ψ

theorem adj_sq (hL : L.IsLB) {y : Y} {J : (Y ⟶ X) → L.ι} (hJ : Good L y J) (χ : Y ⟶ X) :
    adj (fun _ : Fin 1 => 𝟙 X) (fun _ => (2 : ℤ)) y (fun q _ => J q) J χ = 1 := by
  have m := hJ.mem (fun _ : Fin 1 => 𝟙 X) χ
  simp only [Category.comp_id] at m
  unfold adj
  simp only [Category.comp_id]
  exact trF_self hL _ _ χ y m

end Chart

section Square

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem sq_formEq : FormEq (Sum.elim (thφ G (x3 G)) (thφ G (x3 G))) (Sum.elim thε thε)
    (flatφ (fun _ : Fin 1 => 𝟙 G.left) (thφ G (x3 G))) (flatε (fun _ : Fin 1 => (2 : ℤ)) thε) := fun U _ h => by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun I _ => ?_
  simp only [Sum.elim_inl, Sum.elim_inr, Fin.prod_univ_one, flatφ, flatε, Category.comp_id]
  rw [zpow_mul, zpow_two]

theorem exists_sqCube {L : RigLB G} (c : CubicalStr G L) :
    ∃ u : LB.Gen (LB.LinComb (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) (thφ G (x3 G)) thε),
      u.IsGen ∧ (∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val u (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2) ∧
      ∀ (y : (𝟙_ (Over S)).left) JP, Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        val u (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y JP = 1 := by
  obtain ⟨s, hs, hv⟩ := exists_gen L.isLB sq_formEq (LB.mulGen L.L (thφ G (x3 G)) thε (thφ G (x3 G)) thε c.t c.t)
    (DVR.mulGen_isGen _ _ _ _ _ _ _ c.isGen c.isGen)
  have F : ∀ {T : Over S} (y : T.left) (J : (T.left ⟶ G.left) → L.L.ι), Good L.L y J →
        ∀ (JP : (T.left ⟶ G.left) → Fin 1 → L.L.ι), Good (LB.LinComb L.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => 2)) y JP →
        ∀ a b d : T ⟶ G, val (nest L.L _ _ _ _ s) (lift a (lift b d)).left y JP =
          (∏ I : thK.{0}, adj (fun _ : Fin 1 => 𝟙 G.left) (fun _ => 2) y JP J ((lift a (lift b d)).left ≫ thφ G (x3 G) I) ^ thε I) *
            cubV c y J a b d ^ 2 := fun y J hJ JP hJP a b d => by
    rw [val_nest hs _ hJP hJ, hv _ _ y J hJ]
    exact congrArg _ ((val_mul hJ _ _ _).trans (sq _).symm)
  refine ⟨nest L.L _ _ _ _ s, nest_isGen hs, F, fun y JP hJP => ?_⟩
  choose J hJ using fun χ : (𝟙_ (Over S)).left ⟶ G.left => exists_chart L.isLB (χ y)
  rw [F y J hJ JP hJP, prod_cub, (isCub_cubV c hJ).face]
  simp

end Square

end GlobalTheory.SqCube

theorem GlobalTheory.cube_sq_transport : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2 := by
  intro R _ _ _ _ D D' Φ w hw hΦ T z J J' hJ hJ' Ω hΩ a b c
  subst hΩ
  obtain ⟨u, hu, hvu, nu⟩ := GlobalTheory.SqCube.exists_sqCube D.toPre.cub
  obtain ⟨u', hu', hvu', nu'⟩ := GlobalTheory.SqCube.exists_sqCube D'.toPre.cub
  have key := GlobalTheory.SqCube.transport GlobalTheory.globalFns_holds D'.toPre.P.isAb Φ.hom
    (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (DVR.linComb_isLB _ D'.toPre.P.isLB _ _) w hw u u' hu hu' nu nu'
    (GlobalTheory.SqCube.good_sq hJ) (GlobalTheory.SqCube.good_sq hJ') a b c
  rw [hvu z J hJ _ (GlobalTheory.SqCube.good_sq hJ), hvu' z J' hJ' _ (GlobalTheory.SqCube.good_sq hJ')] at key
  simp only [GlobalTheory.SqCube.adj_sq D.toPre.P.isLB hJ, GlobalTheory.SqCube.adj_sq D'.toPre.P.isLB hJ', one_zpow,
    Finset.prod_const_one, _root_.one_mul] at key
  refine key.trans ?_
  rw [prod_cub a b c (fun q => gw w q z (fun _ => J (q ≫ Φ.hom.left)) (fun _ => J' q))]
  rfl
