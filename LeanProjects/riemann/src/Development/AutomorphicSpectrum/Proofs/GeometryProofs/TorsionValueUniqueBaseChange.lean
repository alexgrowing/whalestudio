import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsThetaMeanSquareNorm
import Development.AutomorphicSpectrum.Statements.GeometryStatements.ZhangDimensionPushDownGrassmannianHeightBounds
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.StatementsBundles
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.TorsionValueLineBundleSection
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsPullSnd
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbelianSchemeGerms
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVDesc
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoAppTopOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights TensorProduct
open GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Sl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Sl.TorsExist

open GlobalTheory.CompanionTheory.Ar.Sl.Transl

section General

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem exists_mulGen {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) (N : ℕ) :
    ∃ w : LB.Gen (LB.LinComb P.L (K := Fin 2) ![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] ![1, -((N : ℤ) ^ 2)]), w.IsGen := by
  refine (genOf_pow c hs (𝟙 G) N).inv.gen P.isLB fun U _ h => ?_
  rw [Fin.prod_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, zpow_one, zpow_neg, Over.id_left, mul_inv, inv_inv]
  norm_cast
  exact mul_comm _ _

theorem valF_spMap {F F' : Type} [Field F] [Field F'] (f : F →+* F') {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens)
    (a : Γ(X, U)) : valF (spMap f ≫ x) U a = f (valF x U a) := by
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · have h' : ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U :=
      (top_le_iff_mem _ U z').2 ((top_le_iff_mem x U (spMap f z')).1 h)
    have e₀ : (spMap f).appLE ⊤ ⊤ (by first | exact le_rfl | simp) = (spMap f).appTop := by
      rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
      rfl
    have e : (spMap f ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap f).appTop := by
      rw [← e₀]
      exact (Scheme.Hom.appLE_comp_appLE (spMap f) x U ⊤ ⊤ h _).symm
    have n := congrArg (fun φ => φ.hom ((x.appLE U ⊤ h).hom a)) (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f))
    rw [valF, valF, dif_pos h, dif_pos h', e]
    exact n
  · have h' : ¬ ⊤ ≤ (spMap f ≫ x) ⁻¹ᵁ U := fun k =>
      h ((top_le_iff_mem x U (spMap f z')).2 ((top_le_iff_mem _ U z').1 k))
    rw [valF, valF, dif_neg h, dif_neg h', map_zero]

theorem val_ne_zero {F : Type} [Field F] {X : Scheme.{0}} (x : Sp F ⟶ X) (U : X.Opens) (f : Γ(X, U)ˣ)
    (h : ⊤ ≤ x ⁻¹ᵁ U) : valF x U f.val ≠ 0 := by
  unfold valF
  rw [dif_pos h]
  exact ((f.isUnit.map _).map _).ne_zero

theorem exists_torsVal {P : RigLB G} (c : CubicalStr G P) (hs : P.IsSymmetric) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} (hN : 1 ≤ N) (hy : y ^ N = 1) : ∃ T : F, TorsVal P s y N T := by
  obtain ⟨w, hw⟩ := exists_mulGen c hs N
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  obtain ⟨i₀, h₀⟩ := exists_chart P.isLB ((1 : Over.mk b ⟶ G).left z)
  obtain ⟨i, hi⟩ := exists_chart P.isLB (y.left z)
  have e₁ : (1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left = (1 : Over.mk b ⟶ G).left := by
    rw [left_pow, one_pow]
  have e₂ : b ≫ eSec G = (1 : Over.mk b ⟶ G).left := (one_left (Over.mk b)).symm
  have m₁ : (1 : Over.mk b ⟶ G).left z ∈ LB.wchart P.L (![((𝟙 G : G ⟶ G) ^ N).left, 𝟙 G.left] : Fin 2 → _) ![i₀, i₀] := by
    refine Set.mem_iInter.2 fun k => ?_
    fin_cases k
    · show (((1 : Over.mk b ⟶ G).left ≫ ((𝟙 G : G ⟶ G) ^ N).left) z) ∈ P.L.U i₀
      rw [e₁]; exact h₀
    · exact h₀
  have m₂ : b z ∈ LB.wchart P.L (K := PUnit) (fun _ => eSec G) (fun _ => i₀) := by
    refine Set.mem_iInter.2 fun _ => ?_
    show (b ≫ eSec G) z ∈ P.L.U i₀
    rw [e₂]; exact h₀
  have n₁ := val_ne_zero _ _ (w.s ![i₀, i₀]) ((top_le_iff_mem _ _ z).2 m₁)
  have n₂ := val_ne_zero (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀) ((top_le_iff_mem _ _ z).2 m₂)
  refine ⟨valF y.left _ (s.f fun _ => i) ^ (N ^ 2) * valF y.left _ (w.s ![i₀, i]).val ^ n /
    (valF (1 : Over.mk b ⟶ G).left _ (w.s ![i₀, i₀]).val *
        valF (X := (𝟙_ (Over S)).left) b _ (P.rig.s fun _ => i₀).val ^ (N ^ 2)) ^ n, hN, hy, w, i₀, i, hw,
    (top_le_iff_mem _ _ z).2 h₀, (top_le_iff_mem _ _ z).2 hi, ?_⟩
  exact div_mul_cancel₀ _ (pow_ne_zero _ (mul_ne_zero n₁ (pow_ne_zero _ n₂)))

theorem alg {R : Type*} [CommRing R] (t t' s : R) (A Y A' Y' r : Rˣ) (M n : ℕ) (hc : A' * A⁻¹ = Y' * Y⁻¹)
    (e : t * (A.val * r.val ^ M) ^ n = s ^ M * Y.val ^ n) (e' : t' * (A'.val * r.val ^ M) ^ n = s ^ M * Y'.val ^ n) :
    t = t' := by
  obtain ⟨c, rfl⟩ : ∃ c : Rˣ, A' = c * A := ⟨A' * A⁻¹, by simp⟩
  obtain rfl : Y' = c * Y := by
    have : c = Y' * Y⁻¹ := by simpa using hc
    rw [this]; simp
  simp only [Units.val_mul] at e'
  have u : IsUnit ((c.val * (A.val * r.val ^ M)) ^ n) := ((c.isUnit.mul A.isUnit).mul (r.isUnit.pow M)).pow n |>.map (RingHom.id R) |> fun h => by
    simpa [_root_.mul_assoc] using h
  apply u.mul_left_injective
  calc t * (c.val * (A.val * r.val ^ M)) ^ n = c.val ^ n * (t * (A.val * r.val ^ M) ^ n) := by rw [mul_pow]; ring
    _ = c.val ^ n * (s ^ M * Y.val ^ n) := by rw [e]
    _ = s ^ M * (c.val * Y.val) ^ n := by rw [mul_pow]; ring
    _ = t' * (c.val * A.val * r.val ^ M) ^ n := e'.symm
    _ = _ := by rw [_root_.mul_assoc]

theorem torsVal_unique (hp : Function.Surjective G.hom.appTop.hom) (P : RigLB G) {n : ℕ} (s : Out.H0 P.L n) {F : Type} [Field F]
    {b : Sp F ⟶ S} (y : Over.mk b ⟶ G) {N : ℕ} {T T' : F} (hT : TorsVal P s y N T) (hT' : TorsVal P s y N T') : T = T' := by
  have z : Sp F := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F)
  choose J hJ using fun χ : Sp F ⟶ G.left => exists_chart P.isLB (χ z)
  obtain ⟨w, hw, e⟩ := torsVal_charts P s y N T hT z J hJ
  obtain ⟨w', hw', e'⟩ := torsVal_charts P s y N T' hT' z J hJ
  have hb : (1 : Over.mk b ⟶ G).left ≫ G.hom = y.left ≫ G.hom := (Over.w (1 : Over.mk b ⟶ G)).trans (Over.w y).symm
  have hc := FG.v_const (z := z) (J := J) P.isLB ((mulFG w' hw').mul (mulFG w hw).inv) (fun U _ h => by
    simp only [FG.sum_mul, FG.sum_inv, sum_mulFG, mul_inv_cancel]) G.hom hp hb hJ
  rw [FG.v_mul hJ, FG.v_mul hJ, FG.v_inv, FG.v_inv] at hc
  exact (toStk z).injective (alg _ _ _ _ _ _ _ _ _ _ hc e e')

theorem torsVal_map {P : RigLB G} {n : ℕ} (s : Out.H0 P.L n) {F F' : Type} [Field F] [Field F'] (f : F →+* F') {b : Sp F ⟶ S}
    (y : Over.mk b ⟶ G) (y' : Over.mk (spMap f ≫ b) ⟶ G) (hy' : y'.left = spMap f ≫ y.left) {N : ℕ} {T : F}
    (hT : TorsVal P s y N T) : TorsVal P s y' N (f T) := by
  obtain ⟨hN, hy, w, i₀, i, hw, h₀, hi, hE⟩ := hT
  let g : Over.mk (spMap f ≫ b) ⟶ Over.mk b := Over.homMk (spMap f) rfl
  have ey : y' = g ≫ y := by ext1; exact hy'
  have e₁ : (1 : Over.mk (spMap f ≫ b) ⟶ G).left = spMap f ≫ (1 : Over.mk b ⟶ G).left := by
    rw [one_left, one_left]
    simp
  have z' : Sp F' := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum F')
  refine ⟨hN, by rw [ey, ← MonObj.comp_pow, hy, MonObj.comp_one], w, i₀, i, hw, ?_, ?_, ?_⟩
  · rw [e₁]
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 h₀)
  · rw [hy']
    exact (top_le_iff_mem _ _ z').2 ((top_le_iff_mem _ _ (spMap f z')).1 hi)
  · have := congrArg f hE
    simp only [map_mul, map_pow] at this
    simp only [e₁, hy', valF_spMap]
    exact this

end General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {L : Type} [Field L] [NumberField L]

theorem appTop_surjective (D : PPData H L) : Function.Surjective D.t.G.hom.appTop.hom := by
  have cart := D.m.cart.1
  have := D.t.semi.smooth
  have := D.tK.semi.smooth
  have hprop : IsProper D.tK.G.hom := D.princ.1
  have hab := GlobalTheory.globalFns_holds _ D.tK.G (AbelianSchemeGerms.isAbelianScheme_of_proper D.tK.G D.tK.semi)
  have hj : Function.Injective (spMap (algebraMap (𝓞 L) L)).appTop :=
    specMap_appTop_injective _ (FaithfulSMul.algebraMap_injective _ _)
  have hinj := GlobalTheory.ProperFunctions.injective_appTop_of_isPullback cart hj
  have comp : ∀ {X Y Z : Scheme.{0}} (a : X ⟶ Y) (b : Y ⟶ Z) (x : Γ(Z, ⊤)),
      (a ≫ b).appTop.hom x = a.appTop.hom (b.appTop.hom x) := fun a b x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  let e' : Sp (𝓞 L) ⟶ D.t.G.left := eSec D.t.G
  have he : e' ≫ D.t.G.hom = 𝟙 _ := Over.w (η[D.t.G])
  let sK : Sp L ⟶ D.tK.G.left := cart.lift (spMap (algebraMap (𝓞 L) L) ≫ e') (𝟙 _) (by
    rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : sK ≫ D.m.cm.F = spMap (algebraMap (𝓞 L) L) ≫ e' := cart.lift_fst _ _ _
  have h₂ : sK ≫ D.tK.G.hom = 𝟙 _ := cart.lift_snd _ _ _
  intro f
  obtain ⟨c, hc⟩ := hab.2 (D.m.cm.F.appTop.hom f)
  refine ⟨e'.appTop.hom f, hinj ?_⟩
  show D.m.cm.F.appTop.hom (D.t.G.hom.appTop.hom (e'.appTop.hom f)) = D.m.cm.F.appTop.hom f
  rw [← comp, ← comp, cart.w, Category.assoc, ← h₁, comp, comp, ← hc, ← comp sK, h₂]
  simp

theorem torsVal_existsUnique : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (L : Type) [Field L] [NumberField L] (D : PPData H L) (n : ℕ) (s : Out.H0 D.t.PP.L n) (F : Type) [Field F] (b : Sp F ⟶ Sp (𝓞 L)) (y : Over.mk b ⟶ D.t.G) (N : ℕ), 1 ≤ N → y ^ N = 1 → (∃! T : F, TorsVal D.t.PP s y N T) ∧ ∀ (F' : Type) [Field F'] (f : F →+* F') (y' : Over.mk (spMap f ≫ b) ⟶ D.t.G) (T : F), y'.left = spMap f ≫ y.left → TorsVal D.t.PP s y N T → TorsVal D.t.PP s y' N (f T) := by
  intro E _ _ _ H L _ _ D n s F _ b y N hN hy
  obtain ⟨T, hT⟩ := exists_torsVal D.t.cub D.t.sym s y hN hy
  exact ⟨⟨T, hT, fun T' hT' => torsVal_unique (appTop_surjective D) _ s y hT' hT⟩,
    fun F' _ f y' T e h => torsVal_map s f y y' e h⟩

end GlobalTheory.CompanionTheory.Ar.Sl.TorsExist
