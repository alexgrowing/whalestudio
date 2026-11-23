import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.GeomIntSelf
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.AtOfNumberField
import Development.AbelianVarietyTheory.Statements.ThetaLevelCharacters.MemThetaLevelCharDimZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.GenMove
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyNormalFormDetRatioTwoTorsionTranslateStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ThetaFrameValueKnownOfPolarizedPullbackStatement
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.DualNumberRingHomExt
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsKeyPBRing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisedIsoPullbackMulByM
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsNormalisingUnitSimilitudeOrigin

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.KeyPow GlobalTheory.KeyFam GlobalTheory.ZM GlobalTheory.AbLaw

noncomputable section
namespace GlobalTheory.KnownTwist
open GlobalTheory.KeyEq (trl IsTrl)

section Calc

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {K : Type} [Fintype K]

theorem gm_map (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hz : h (r z) ∈ U) (a : Γ(X, U)ˣ) :
    gm (r ≫ h) z U a = Units.map (r.stalkMap z).hom.toMonoidHom (gm h (r z) U a) := by
  apply Units.ext
  refine (gs_unit (r ≫ h) z U hz a).symm.trans ((gs_pull r h z U hz _).symm.trans
    ((gs_stalkMap r z _ hz _).trans (congrArg (r.stalkMap z).hom ?_)))
  refine (gs_pull (𝟙 Y) h (r z) U hz _).trans ?_
  rw [Category.id_comp]
  exact gs_unit h (r z) U hz a

theorem val_map {φ : K → (Y' ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) (h : Y ⟶ Y') (z : Z)
    {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    val t (r ≫ h) z J = Units.map (r.stalkMap z).hom.toMonoidHom (val t h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [val_of t (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gm_map r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem pmaps_val {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} {h : Y' ⟶ Y} (H : PMaps w φ' φ ε a t h)
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) (r : Z ⟶ Y') (z : Z) {I : (Z ⟶ X) → L.ι} {J : (Z ⟶ X') → L'.ι}
    (hI : Good L z I) (hJ : Good L' z J) :
    val t (r ≫ h) z I = (∏ k, gw w (r ≫ φ' k) z (I ((r ≫ φ' k) ≫ F)) (J (r ≫ φ' k)) ^ ε k) * val a r z J := by
  rw [val_of t (r ≫ h) z I (fun k => I ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hI ((r ≫ φ' k) ≫ F)) (fun k => hJ (r ≫ φ' k))

theorem exists_square {A A' B B' : Scheme.{0}} {M : LB A} {M' : LB A'} {N : LB B} {N' : LB B'} (hM : M.IsLB)
    (hM' : M'.IsLB) (hN : N.IsLB) (hN' : N'.IsLB) {F : A' ⟶ A} {G : B' ⟶ B} {φ : B ⟶ A} {φ' : B' ⟶ A'}
    (hsq : φ' ≫ F = G ≫ φ) {u : LB.Iso M' (M.pull F)} {v : LB.Iso N (M.pull φ)} {v' : LB.Iso N' (M'.pull φ')}
    (hu : PGen u) (hv : PGen v) (hv' : PGen v') :
    ∃ w : LB.Iso N' (N.pull G), PGen w ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) j i i' k, φ (G (f z)) ∈ M.U j →
      G (f z) ∈ N.U i → φ' (f z) ∈ M'.U i' → f z ∈ N'.U k →
      gw v (f ≫ G) z j i * gw w f z i k = gw u (f ≫ φ') z j i' * gw v' f z i' k := by
  obtain ⟨c, T⟩ := exists_comp hM' u v' hu hv' hM hN'
  have key : ∀ H : B' ⟶ A, φ' ≫ F = H → ∃ c : LB.Iso N' (M.pull H), PGen c ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) j i' k, H (f z) ∈ M.U j → φ' (f z) ∈ M'.U i' → f z ∈ N'.U k →
        gw c f z j k = gw u (f ≫ φ') z j i' * gw v' f z i' k := by
    rintro _ rfl
    exact ⟨c, T.pgen_comp hM' hu hv', T⟩
  obtain ⟨c', hc', T'⟩ := key _ hsq
  obtain ⟨w, S⟩ := exists_cancel hM v c' hv hc' hN hN'
  exact ⟨w, S.pgen_cancel hM hv hc', fun Z f z j i i' k a b c d =>
    (S Z f z j i k a b d).symm.trans (T' Z f z j i' k a c d)⟩

end Calc

def IsTranslate {K : Type} [CommRing K] (y' y : KeyIn K) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A) (ν : Kˣ) : Prop :=
  ∃ (e : y'.P.A ≅ y.P.A) (hg : y'.P.g = y.P.g) (w : LB.Iso y'.P.L (y.P.L.pull (e.hom ≫ trl y.P.A t).left))
    (mu : LB.Gen (LB.LinComb y.P.L (K := Fin 2) ![((𝟙 y.P.A) ^ 2).left, 𝟙 y.P.A.left] ![1, -4]))
    (rp : LB.Gen (y.P.L.pull t.left)),
    t ^ 2 = 1 ∧ IsMonHom e.hom ∧ PGen w ∧ mu.IsGen ∧ rp.IsGen ∧
    (∀ i, y'.v i ≫ e.hom = y.v (i.cast hg)) ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ y'.P.A.left) (z : Z) j k, (e.hom ≫ trl y.P.A t).left (r z) ∈ y.P.L.U j →
      r z ∈ y'.P.L.U k → gs (r ≫ (e.hom ≫ trl y.P.A t).left) z _ (y.th.f j) =
        (gw w r z j k).val * gs r z _ (y'.th.f k)) ∧
    PMaps w (K := PUnit) (fun _ => eSec y'.P.A) (fun _ => t.left) (fun _ => 1) y'.rig rp (𝟙 _) ∧
    (∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp K))).left) (z : Z) J, Good y.P.L z J →
      val mu (r ≫ eSec y.P.A) z J = val y.rig r z J ^ (-3 : ℤ)) ∧
    ∀ (Z : Scheme.{0}) (r : Z ⟶ (𝟙_ (Over (Sp K))).left) (z : Z) J, Good y.P.L z J →
      val mu (r ≫ t.left) z J =
        gm r z ⊤ (show Γ((𝟙_ (Over (Sp K))).left, ⊤)ˣ from unitOn ν) * val y.rig r z J * val rp r z J ^ (-4 : ℤ)

section Grp

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B]

theorem comp_trl {T : Over S} (p : 𝟙_ (Over S) ⟶ A) (q : T ⟶ A) : q ≫ trl A p = (toUnit T ≫ p) * q := by
  rw [trl, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]

theorem eSec_trl (e : B ⟶ A) [IsMonHom e] (p : 𝟙_ (Over S) ⟶ A) : eSec B ≫ (e ≫ trl A p).left = p.left := by
  have : η[B] ≫ e ≫ trl A p = p := by
    have h1 : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
    rw [← Category.assoc, IsMonHom.one_hom, comp_trl, toUnit_unit, Category.id_comp, h1, _root_.mul_one]
  exact congrArg CommaMorphism.left this

theorem comp_sq (p : 𝟙_ (Over S) ⟶ A) (hp : p ^ 2 = 1) : p.left ≫ ((𝟙 A) ^ 2).left = eSec A := by
  have : p ≫ (𝟙 A) ^ 2 = η[A] := by
    rw [MonObj.comp_pow, Category.comp_id, hp, Hom.one_def, toUnit_unit, Category.id_comp]
  exact congrArg CommaMorphism.left this

theorem eSec_sq : eSec A ≫ ((𝟙 A) ^ 2).left = eSec A := by
  have h1 : η[A] = (1 : 𝟙_ (Over S) ⟶ A) := by rw [Hom.one_def, toUnit_unit, Category.id_comp]
  exact comp_sq η[A] (by rw [h1, one_pow])

theorem trl_trl_inv (p : 𝟙_ (Over S) ⟶ A) : trl A p⁻¹ ≫ trl A p = 𝟙 A := by
  rw [comp_trl, trl, ← _root_.mul_assoc, ← MonObj.comp_mul, mul_inv_cancel, MonObj.comp_one, _root_.one_mul]

end Grp

theorem exists_isTranslate (laws : Out.Laws) {K : Type} [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A)
    (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A) [he : IsMonHom e.hom] (ht : t ^ 2 = 1)
    (hL : LBIso y'.P.L (y.P.L.pull (e.hom ≫ trl y.P.A t).left)) :
    ∃ (y₁ : KeyIn K) (ν : Kˣ), y₁.P = y'.P ∧ IsTranslate y₁ y t ν := by
  obtain ⟨w, hw⟩ := hL
  replace hw := (isGen_iff w).1 hw
  have hg : y'.P.g = y.P.g := by
    obtain ⟨z, -⟩ := y'.th_ne (default : PrimeSpectrum K)
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have := y.P.smoothDim
    have h : SmoothOfRelativeDimension (0 + y.P.g) (e.hom.left ≫ y.P.A.hom) := inferInstance
    rw [Over.w, zero_add] at h
    exact H1.dim_unique _ y'.P.smoothDim h z
  obtain ⟨mu, hmu, hv⟩ := KeyKa.exists_normalised_mulPull laws K y 2
  obtain ⟨rp, hrp⟩ := DVR.exists_gen_of_local (V := K) y.P.L y.P.isLB (K := PUnit) (fun _ => t.left) (fun _ => 1)
  obtain ⟨rig, hrig, hm⟩ := H1.exists_gen_move y.P.isLB y'.P.isLB w hw (K := PUnit) (fun _ => t.left)
    (fun _ => eSec y'.P.A) (fun _ => 1) (𝟙 _) (fun _ => (eSec_trl e.hom t).trans (Category.id_comp _).symm) rp hrp
  obtain ⟨th, hth⟩ := sec_pull_down hw y.P.isLB y'.P.isLB y.th
  have hne : ∀ s : Sp K, ∃ x : y'.P.A.left, y'.P.A.hom x = s ∧ x ∈ Out.nonzeroLocus th := by
    intro s
    obtain ⟨z, -, hz⟩ := y.th_ne s
    have hs : (trl y.P.A t⁻¹ ≫ e.inv).left ≫ (e.hom ≫ trl y.P.A t).left = 𝟙 _ := by
      rw [← Over.comp_left, Category.assoc, e.inv_hom_id_assoc, trl_trl_inv, Over.id_left]
    obtain ⟨x, rfl⟩ : ∃ x, (e.hom ≫ trl y.P.A t).left x = z := ⟨_, congrArg (fun q => q z) hs⟩
    obtain ⟨j, hj, u⟩ := (mem_nonzeroLocus _ _).1 hz
    obtain ⟨k, hk⟩ := exists_chart y'.P.isLB x
    refine ⟨x, Subsingleton.elim (α := PrimeSpectrum K) _ _, (mem_nonzeroLocus _ _).2 ⟨k, hk, ?_⟩⟩
    have u₁ : IsUnit (gs (e.hom ≫ trl y.P.A t).left x _ (y.th.f j)) := by
      rw [gs_stalkMap _ x _ hj]; exact u.map _
    have e := hth _ (𝟙 _) x j k hj hk
    rw [Category.id_comp] at e
    exact isUnit_of_mul_isUnit_right (e ▸ u₁)
  have hb : IsLieBasis (fun i : Fin y'.P.g => y.v (i.cast hg) ≫ e.inv) := by
    refine Chart.isLieBasis_iso e ?_
    simp only [Category.assoc, e.inv_hom_id, Category.comp_id]
    have : ∀ (n : ℕ) (h : n = y.P.g), IsLieBasis (fun i : Fin n => y.v (i.cast h)) := by
      rintro _ rfl; exact y.basis
    exact this _ hg
  obtain ⟨u, hu⟩ := (((SimilUnit.IsVal.pull hmu t.left).mul (SimilUnit.IsVal.pull y.rig_gen (𝟙 _)).inv).mul
    ((SimilUnit.IsVal.pull hrp (𝟙 _)).zpow (-4)).inv).exists_unit y.P.isLB (fun U _ h => by
      simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, comp_sq t ht, Category.comp_id,
        Category.id_comp, Fintype.prod_unique, zpow_one]
      generalize h (eSec y.P.A) = a
      generalize h t.left = b
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_one]
      module)
  let ν : Kˣ := Units.map (Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom.toMonoidHom u
  have hν : unitOn ν = u := Units.ext (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of K)) u.val)
  refine ⟨⟨y'.P, y'.g_pos, rig, hrig, th, hne, _, hb⟩, ν, rfl, e, hg, w, mu, rp, ht, he, hw, hmu, hrp,
    fun i => by simp, hth, hm, fun Z r z J hJ => ?_, fun Z r z J hJ => ?_⟩
  · have a := val_map y.rig r (𝟙 _) z hJ
    rw [Category.comp_id] at a
    refine (val_map mu r _ z hJ).trans ?_
    rw [a, ← map_zpow]
    exact congrArg _ (hv (r z) _ fun ψ => hJ (r ≫ ψ))
  · have a := val_map y.rig r (𝟙 _) z hJ
    have b := val_map rp r (𝟙 _) z hJ
    have c := gm_map r (𝟙 _) z ⊤ trivial u
    rw [Category.comp_id] at a b c
    refine (val_map mu r _ z hJ).trans ?_
    rw [a, hν]
    erw [b, c]
    rw [← map_zpow, ← map_mul, ← map_mul]
    have d := Units.ext ((hu (r z) _ fun ψ => hJ (r ≫ ψ)).trans (gs_unit _ _ ⊤ trivial _))
    rw [mul_inv_eq_iff_eq_mul, mul_inv_eq_iff_eq_mul] at d
    refine congrArg _ (d.trans ?_)
    exact mul_right_comm _ _ _

section Pull

variable {S S' : Scheme.{0}} {A : Over S} {B : Over S'} [GrpObj A] [GrpObj B] {f : S' ⟶ S} {φ : B.left ⟶ A.left}

theorem sq_comm (h : IsGrpPullback B A f φ) : ((𝟙 B) ^ 2).left ≫ φ = φ ≫ ((𝟙 A) ^ 2).left := by
  have e : pushPt h.1.w ((𝟙 B) ^ 2) = pushPt h.1.w (𝟙 B) ≫ (𝟙 A) ^ 2 := by
    rw [MonObj.comp_pow, Category.comp_id]
    exact map_pow (pushHom h B) _ 2
  have e' : ((𝟙 B) ^ 2).left ≫ φ = (𝟙 B.left ≫ φ) ≫ ((𝟙 A) ^ 2).left := congrArg CommaMorphism.left e
  rwa [Category.id_comp] at e'

theorem trl_comm (h : IsGrpPullback B A f φ) {p : 𝟙_ (Over S') ⟶ B} {t : 𝟙_ (Over S) ⟶ A}
    (hp : p.left ≫ φ = f ≫ t.left) : (trl B p).left ≫ φ = φ ≫ (trl A t).left := by
  have e : pushPt h.1.w (trl B p) = pushPt h.1.w (𝟙 B) ≫ trl A t := by
    rw [comp_trl]
    refine (map_mul (pushHom h B) _ _).trans (congrArg (· * _) (Over.OverMorphism.ext ?_))
    show ((toUnit B).left ≫ p.left) ≫ φ = (toUnit (Over.mk (B.hom ≫ f))).left ≫ t.left
    rw [Category.assoc, hp]
    simp
  have e' : (trl B p).left ≫ φ = (𝟙 B.left ≫ φ) ≫ (trl A t).left := congrArg CommaMorphism.left e
  rwa [Category.id_comp] at e'

theorem exists_pt (h : IsGrpPullback B A f φ) (t : 𝟙_ (Over S) ⟶ A) (ht : t ^ 2 = 1) :
    ∃ p : 𝟙_ (Over S') ⟶ B, p.left ≫ φ = f ≫ t.left ∧ p ^ 2 = 1 := by
  have w : (f ≫ t.left) ≫ A.hom = 𝟙 S' ≫ f := by
    rw [Category.assoc, Over.w t]; simp
  let p : 𝟙_ (Over S') ⟶ B := Over.homMk (h.1.lift _ _ w) (h.1.lift_snd _ _ _)
  have hp : p.left ≫ φ = f ≫ t.left := h.1.lift_fst _ _ _
  refine ⟨p, hp, ?_⟩
  have inj : Function.Injective (pushHom h (𝟙_ (Over S'))) := fun a b e =>
    Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left e) ((Over.w a).trans (Over.w b).symm))
  apply inj
  have e : pushHom h (𝟙_ (Over S')) p = toUnit _ ≫ t := Over.OverMorphism.ext (hp.trans (by simp))
  rw [map_pow, map_one, e, ← MonObj.comp_pow, ht, MonObj.comp_one]

end Pull

def baseMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') :
    (𝟙_ (Over (Sp R'))).left ⟶ (𝟙_ (Over (Sp R))).left := spMap f

theorem gm_spMap_unitOn {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') (q : (𝟙_ (Over (Sp R'))).left)
    (u : Rˣ) : gm (𝟙 _ ≫ baseMap f) q ⊤ (show Γ((𝟙_ (Over (Sp R))).left, ⊤)ˣ from unitOn u) =
      gm (𝟙 _) q ⊤ (show Γ((𝟙_ (Over (Sp R'))).left, ⊤)ˣ from unitOn (Units.map f.toMonoidHom u)) := by
  refine (gm_pull (𝟙 _) (baseMap f) q ⊤ trivial _).symm.trans (congrArg (gm (𝟙 _) q ⊤) (Units.ext ?_))
  have := congrArg (fun q => q.hom u.val) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom f))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at this
  exact this.symm

theorem IsTranslate.baseChange {K : Type} [CommRing K] {y' y : KeyIn K} {t : 𝟙_ (Over (Sp K)) ⟶ y.P.A} {ν : Kˣ}
    (H : IsTranslate y' y t ν) {f : K →+* ℂ} {x' x : KeyIn ℂ} (h' : KeyPB x' y' f) (h : KeyPB x y f) :
    ∃ p, IsTrl x' x p (Units.map f.toMonoidHom ν) := by
  obtain ⟨e, hg₀, w₀, mu₀, rp₀, ht, he, hw₀, hmu₀, hrp₀, hv₀, hs₀, hr₀, m₀, m₁⟩ := H
  obtain ⟨φ, hφe, v, hg, F, hc, hv, hr, hs, hF, hFe, hb⟩ := h
  obtain ⟨φ', hφe', v', hg', F', hc', hv', hr', hs', hF', hFe', hb'⟩ := h'
  obtain rfl : F = F' := KeyCancel.dualNumber_ringHom_ext (fun a => (hF a).trans (hF' a).symm) (hFe.trans hFe'.symm)
  change eSec x.P.A ≫ φ = baseMap f ≫ eSec y.P.A at hφe
  change eSec x'.P.A ≫ φ' = baseMap f ≫ eSec y'.P.A at hφe'
  replace hv := (isGen_iff v).1 hv
  replace hv' := (isGen_iff v').1 hv'
  replace hr := (maps_iff v _ (fun _ => eSec y.P.A) _ x.rig y.rig (baseMap f) _ (rigPull_le φ (baseMap f) hφe y.P.L)
    (fun _ => rfl)).1 hr
  replace hr' := (maps_iff v' _ (fun _ => eSec y'.P.A) _ x'.rig y'.rig (baseMap f) _
    (rigPull_le φ' (baseMap f) hφe' y'.P.L) (fun _ => rfl)).1 hr'
  replace hs := (KeyCancel.appLE_eq_iff_stalk v y.th x.th).1 hs
  replace hs' := (KeyCancel.appLE_eq_iff_stalk v' y'.th x'.th).1 hs'
  obtain ⟨ε, hε, hεφ⟩ := grpPullback_iso ((hc'.comp (isGrpPullback_of_iso e)).congr (Category.comp_id _) rfl) hc
  obtain ⟨p, hp, hp2⟩ := exists_pt hc t ht
  change p.left ≫ φ = baseMap f ≫ t.left at hp
  have hsq : φ' ≫ (e.hom ≫ trl y.P.A t).left = (ε.hom ≫ trl x.P.A p).left ≫ φ := by
    rw [Over.comp_left, Over.comp_left, Category.assoc, trl_comm hc hp, ← Category.assoc, ← hεφ, Category.assoc]
  obtain ⟨w, hw, Q⟩ := exists_square y.P.isLB y'.P.isLB x.P.isLB x'.P.isLB hsq hw₀ hv hv'
  have c₁ : ∀ k : Fin 2, ![((𝟙 x.P.A) ^ 2).left, 𝟙 x.P.A.left] k ≫ φ =
      φ ≫ ![((𝟙 y.P.A) ^ 2).left, 𝟙 y.P.A.left] k := fun k => by
    fin_cases k
    · exact sq_comm hc
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨mu, hmu, pm⟩ := H1.exists_gen_move y.P.isLB x.P.isLB v hv _ _ _ φ c₁ mu₀ hmu₀
  obtain ⟨rp, hrp, pr⟩ := H1.exists_gen_move y.P.isLB x.P.isLB v hv (K := PUnit) (fun _ => t.left) (fun _ => p.left)
    (fun _ => 1) (baseMap f) (fun _ => hp) rp₀ hrp₀
  have good : ∀ q : (𝟙_ (Over (Sp ℂ))).left, ∃ I, Good y.P.L q I := fun q => by
    choose I hI using fun ψ : (𝟙_ (Over (Sp ℂ))).left ⟶ y.P.A.left => exists_chart y.P.isLB (ψ q)
    exact ⟨I, hI⟩
  refine ⟨p, ε, hg'.trans (hg₀.trans hg.symm), w, mu, rp, hp2, hε, (isGen_iff w).2 hw, hmu, hrp, fun i => ?_,
    fun z j k hj hk => ?_, fun q J J' hJ hJ' => ?_, fun q J hJ => ?_, fun q J hJ => ?_⟩
  · refine Over.OverMorphism.ext (hc.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    rw [Over.comp_left, Category.assoc, hεφ, ← Category.assoc, hb', hb, Category.assoc, ← Over.comp_left, hv₀]
    rfl
  · obtain ⟨a, ha⟩ := exists_chart y.P.isLB (φ ((ε.hom ≫ trl x.P.A p).left z))
    obtain ⟨b, hb⟩ := exists_chart y'.P.isLB (φ' z)
    have ha' : (e.hom ≫ trl y.P.A t).left (φ' z) ∈ y.P.L.U a := (congrArg (fun g => g z ∈ y.P.L.U a) hsq).mpr ha
    have e₁ := hs _ (𝟙 _ ≫ (ε.hom ≫ trl x.P.A p).left) z a j ha hj
    have e₂ := hs₀ _ (𝟙 _ ≫ φ') z a b ha' hb
    have e₃ := hs' _ (𝟙 _) z b k hb hk
    have e₄ := Q _ (𝟙 _) z a j b k ha hj hb hk
    rw [Category.assoc, hsq, ← Category.assoc, e₁, e₃, ← _root_.mul_assoc, ← Units.val_mul, ← e₄, Units.val_mul,
      _root_.mul_assoc, Units.mul_right_inj, Category.id_comp] at e₂
    exact e₂
  · obtain ⟨I, hI⟩ := good q
    obtain ⟨b, hb⟩ := exists_chart y'.P.isLB (φ' (eSec x'.P.A q))
    have E := eSec_trl ε.hom p
    have E₀ := eSec_trl e.hom t
    have a₁ : φ (p.left q) ∈ y.P.L.U (I (p.left ≫ φ)) := hI _
    have a₂ : p.left q ∈ x.P.L.U (J (𝟙 _ ≫ p.left)) := hJ (𝟙 _ ≫ p.left)
    have a₃ : eSec x'.P.A q ∈ x'.P.L.U (J' (𝟙 _ ≫ eSec x'.P.A)) := hJ' (𝟙 _ ≫ eSec x'.P.A)
    have b₁ : eSec y'.P.A (baseMap f q) ∈ y'.P.L.U b := (congrArg (fun g => g q ∈ y'.P.L.U b) hφe').mp hb
    have b₂ : (e.hom ≫ trl y.P.A t).left (eSec y'.P.A (baseMap f q)) ∈ y.P.L.U (I (p.left ≫ φ)) :=
      (congrArg (fun g => g q ∈ y.P.L.U (I (p.left ≫ φ))) (hp.trans (congrArg (baseMap f ≫ ·) E₀.symm))).mp a₁
    have e₁ := pr _ (𝟙 _) q (fun _ => I (p.left ≫ φ)) (fun _ => J (𝟙 _ ≫ p.left)) (fun _ => a₁) (fun _ => a₂)
    have e₂ := hr₀ _ (𝟙 _ ≫ baseMap f) q (fun _ => I (p.left ≫ φ)) (fun _ => b) (fun _ => b₂) (fun _ => b₁)
    have e₃ := hr' _ (𝟙 _) q (fun _ => b) (fun _ => J' (𝟙 _ ≫ eSec x'.P.A)) (fun _ => hb) (fun _ => a₃)
    have e₄ := Q _ (eSec x'.P.A) q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) b (J' (𝟙 _ ≫ eSec x'.P.A))
      ((congrArg (fun g => φ (g q) ∈ y.P.L.U (I (p.left ≫ φ))) E).mpr a₁)
      ((congrArg (fun g => g q ∈ x.P.L.U (J (𝟙 _ ≫ p.left))) E).mpr a₂) hb a₃
    rw [E, hφe'] at e₄
    simp only [Fintype.prod_unique, zpow_one] at e₁ e₂ e₃
    have e₅ : gm (𝟙 _ ≫ baseMap f) q _ (rp₀.s (fun _ => I (p.left ≫ φ))) =
      gm ((𝟙 _ ≫ baseMap f) ≫ 𝟙 _) q _ (rp₀.s (fun _ => I (p.left ≫ φ))) := by erw [Category.comp_id]
    have e₆ := e₁.symm.trans (e₅.trans (e₂.trans (congrArg _ e₃)))
    have i₁ : gw v (𝟙 _ ≫ p.left) q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) =
      gw v p.left q (I (p.left ≫ φ)) (J (𝟙 _ ≫ p.left)) := congrArg (gw v · q _ _) (Category.id_comp _)
    have i₂ : gw w₀ ((𝟙 _ ≫ baseMap f) ≫ eSec y'.P.A) q (I (p.left ≫ φ)) b =
      gw w₀ (baseMap f ≫ eSec y'.P.A) q (I (p.left ≫ φ)) b :=
        congrArg (fun g => gw w₀ (g ≫ eSec y'.P.A) q _ _) (Category.id_comp _)
    have i₃ : gw v' (𝟙 _ ≫ eSec x'.P.A) q b (J' (𝟙 _ ≫ eSec x'.P.A)) =
      gw v' (eSec x'.P.A) q b (J' (𝟙 _ ≫ eSec x'.P.A)) := congrArg (gw v' · q _ _) (Category.id_comp _)
    have e₇ := (congrArg (· * _) i₁.symm).trans (e₆.trans ((congrArg₂ (fun a b => a * (b * _)) i₂ i₃).trans
      ((_root_.mul_assoc _ _ _).symm.trans ((congrArg (· * _) e₄.symm).trans (_root_.mul_assoc _ _ _)))))
    exact mul_left_cancel e₇
  · obtain ⟨I, hI⟩ := good q
    have e₁ := pmaps_val pm c₁ (eSec x.P.A) q hI hJ
    have e₂ := pmaps_val hr (fun _ => hφe) (𝟙 _) q hI hJ
    have e₃ := m₀ _ (𝟙 _ ≫ baseMap f) q I hI
    have e₄ : (𝟙 _ ≫ baseMap f : (𝟙_ (Over (Sp ℂ))).left ⟶ (𝟙_ (Over (Sp K))).left) ≫ eSec y.P.A = eSec x.P.A ≫ φ :=
      (congrArg (· ≫ eSec y.P.A) (Category.id_comp _)).trans hφe.symm
    have e₅ := e₁.symm.trans ((congrArg (val mu₀ · q I) e₄.symm).trans (e₃.trans (congrArg (· ^ (-3 : ℤ)) e₂)))
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, eSec_sq, Category.comp_id,
      Fintype.prod_unique, zpow_one] at e₅
    rw [Category.id_comp] at e₅
    generalize gw v (eSec x.P.A) q _ _ = a at e₅
    rw [eq_inv_mul_of_mul_eq e₅]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module
  · obtain ⟨I, hI⟩ := good q
    have e₁ := pmaps_val pm c₁ p.left q hI hJ
    have e₂ := pmaps_val hr (fun _ => hφe) (𝟙 _) q hI hJ
    have e₂' := pmaps_val pr (fun _ => hp) (𝟙 _) q hI hJ
    have e₃ := m₁ _ (𝟙 _ ≫ baseMap f) q I hI
    have e₄ : (𝟙 _ ≫ baseMap f : (𝟙_ (Over (Sp ℂ))).left ⟶ (𝟙_ (Over (Sp K))).left) ≫ t.left = p.left ≫ φ :=
      (congrArg (· ≫ t.left) (Category.id_comp _)).trans hp.symm
    have e₅ := e₁.symm.trans ((congrArg (val mu₀ · q I) e₄.symm).trans (e₃.trans (congrArg₂ (· * ·)
      (congrArg₂ (· * ·) (gm_spMap_unitOn f q ν) e₂) (congrArg (· ^ (-4 : ℤ)) e₂'))))
    simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, comp_sq p hp2, Category.comp_id,
      Fintype.prod_unique, zpow_one] at e₅
    rw [Category.id_comp, Category.id_comp] at e₅
    generalize gw v (eSec x.P.A) q _ _ = a at e₅
    generalize gw v p.left q _ _ = b at e₅
    rw [eq_inv_mul_of_mul_eq e₅]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
    module

theorem polPB_of_eq {S : Scheme.{0}} {P P' : Out.PolAV S} (h : P = P') : ∃ φ, PolPB P' P (𝟙 _) φ := by
  subst h
  have : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  exact ⟨𝟙 _, isGrpPullback_of_iso (Iso.refl P.A), rfl, isoPullId (idIso P.L) rfl,
    (isGen_iff _).2 (isoPullId_pgen (idIso_isGen P.isLB) rfl)⟩

theorem known_of_translate : Out.Laws → ThetaUnifAV → ∀ (K : Type) [Field K] (y y' : KeyIn K) (e : y'.P.A ≅ y.P.A) (t : 𝟙_ (Over (Sp K)) ⟶ y.P.A), IsMonHom e.hom → t ^ 2 = 1 → LBIso y'.P.L (y.P.L.pull (e.hom ≫ ((toUnit y.P.A ≫ t) * 𝟙 y.P.A)).left) → Known K y → Known K y' := by
  intro laws hU K _ y y' e t he ht hL hk
  obtain ⟨t₀, h₀⟩ := hk
  obtain ⟨y₁, ν, hP, H⟩ := exists_isTranslate laws y y' e t ht hL
  have k₁ : Known K y₁ := by
    refine ⟨t₀ * (ν : K) ^ 2, fun f x' h' => ?_⟩
    obtain ⟨x, h⟩ := exists_keyPB_ring y f
    obtain ⟨p, hp⟩ := H.baseChange h' h
    have a : KeyEq.Val x (f t₀) := h₀ f x h
    have b : f (t₀ * (ν : K) ^ 2) = f t₀ * ((Units.map f.toMonoidHom ν : ℂˣ) : ℂ) ^ 2 := by
      rw [map_mul, map_pow]; rfl
    rw [b]
    exact GlobalTheory.T.keyNormalFormDetRatio_twoTorsion_translate laws hU x x' p _ _ hp a
  obtain ⟨φ, hφ⟩ := polPB_of_eq hP
  exact GlobalTheory.T.thetaFrameValueKnown_of_polarizedPullback laws K y₁ y' φ hφ k₁

end GlobalTheory.KnownTwist
end
