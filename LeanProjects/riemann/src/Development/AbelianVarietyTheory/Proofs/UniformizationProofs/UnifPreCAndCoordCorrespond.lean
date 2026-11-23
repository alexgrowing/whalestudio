import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsIsGenOfInvariant

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordCompare

theorem exists_gen_of_val_eq {X Y Y' : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (m : Y' ⟶ Y) [Flat m] [Surjective m] [QuasiCompact m]
    (u : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hu : u.IsGen)
    (hinv : ∀ (Z : Scheme.{0}) (r r' : Z ⟶ Y') (z : Z) (J), Good L z J → r ≫ m = r' ≫ m →
      val u r z J = val u r' z J) :
    ∃ v : LB.Gen (LB.LinComb L φ ε), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J), Good L z J → val v (r ≫ m) z J = val u r z J := by
  have hinj := FunDescent.app_injective m
  have le : ∀ j : K → L.ι, m ⁻¹ᵁ LB.wchart L φ j ≤ LB.wchart L (fun k => m ≫ φ k) j :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  have hex : ∀ j : K → L.ι, ∃ b : Γ(Y, LB.wchart L φ j)ˣ, pullU m _ b = res (le j) (u.s j) := by
    intro j
    obtain ⟨a, ha⟩ := FunDescent.exists_app_eq m (LB.wchart L φ j) (res (le j) (u.s j)).val (by
      intro Z g₁ g₂ h₁ h₂ e
      refine congrArg Units.val (show res h₁ (pullU g₁ _ (res (le j) (u.s j))) =
        res h₂ (pullU g₂ _ (res (le j) (u.s j))) from unit_ext fun y hy => ?_)
      choose J hJ using fun χ : Z ⟶ X => exists_chart hL (χ y)
      have hJ' : Good L y J := hJ
      have key : ∀ (g : Z ⟶ Y') (h : ⊤ ≤ g ⁻¹ᵁ (m ⁻¹ᵁ LB.wchart L φ j)),
          gm (𝟙 Z) y ⊤ (res h (pullU g _ (res (le j) (u.s j)))) =
            (∏ k, gm ((g ≫ m) ≫ φ k) y (L.U (j k) ⊓ L.U (J ((g ≫ m) ≫ φ k)))
              (L.g (j k) (J ((g ≫ m) ≫ φ k))) ^ ε k) * val u g y J := fun g h => by
        refine (gm_res (𝟙 Z) y h hy _).trans ((gm_pull (𝟙 Z) g y _ (h hy) _).trans ?_)
        rw [Category.id_comp]
        refine (gm_res g y (le j) (h hy) _).trans
          ((gen_trans hu g y (le j (h hy)) (hJ'.mem _ _)).trans ?_)
        simp only [trF, Category.assoc]
        rfl
      rw [key, key, e, hinv Z g₁ g₂ y J hJ' e])
    have hua : IsUnit a := FunDescent.isUnit_of_isUnit_app m _ a (ha ▸ Units.isUnit _)
    exact ⟨hua.unit, Units.ext ha⟩
  choose b hb using hex
  have vb : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (j : K → L.ι), r z ∈ m ⁻¹ᵁ LB.wchart L φ j →
      gm (r ≫ m) z _ (b j) = gm r z _ (u.s j) := fun Z r z j hj =>
    (gm_pull r m z _ hj _).symm.trans ((congrArg _ (hb j)).trans (gm_res r z (le j) hj _))
  refine ⟨⟨b⟩, fun i j => Units.ext (hinj _ (congrArg Units.val
    (show pullU m _ _ = pullU m _ _ from unit_ext fun y hy => ?_))), fun Z r z J hJ => ?_⟩
  · refine (gm_pull (𝟙 Y') m y _ hy _).trans (Eq.trans ?_ (gm_pull (𝟙 Y') m y _ hy _).symm)
    refine ((gm_res _ y _ hy _).trans (vb _ (𝟙 Y') y i hy.1)).trans
      ((gen_trans hu (𝟙 Y') y (le i hy.1) (le j hy.2)).trans (Eq.symm ?_))
    refine (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_linComb L φ ε (𝟙 Y' ≫ m) y i j hy.1 hy.2).trans ?_)
      ((gm_res _ y _ hy _).trans (vb _ (𝟙 Y') y j hy.2)))
    simp only [trF, Category.assoc]
  · rw [val_of u r z J (fun k => J ((r ≫ m) ≫ φ k)) (fun k => by rw [Category.assoc])]
    exact vb Z r z _ (hJ.mem φ (r ≫ m))

def diffφ {S : Scheme.{0}} {A Y : Over S} [GrpObj A] (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A) :
    Fin 4 → (Y.left ⟶ A.left) :=
  ![(y * (toUnit Y ≫ b)).left, (y * (toUnit Y ≫ a)).left, (toUnit Y ≫ a).left, (toUnit Y ≫ b).left]

theorem prod_diff {S : Scheme.{0}} {A Y Z : Over S} [GrpObj A] (y : Y ⟶ A) (a b : 𝟙_ (Over S) ⟶ A)
    (r : Z ⟶ Y) {U : Type} [CommGroup U] (h : (Z.left ⟶ A.left) → U) :
    ∏ k, h (r.left ≫ diffφ y a b k) ^ (![1, -1, 1, -1] : Fin 4 → ℤ) k =
      h ((r ≫ y) * (toUnit Z ≫ b)).left * (h ((r ≫ y) * (toUnit Z ≫ a)).left)⁻¹ *
        h (toUnit Z ≫ a).left * (h (toUnit Z ≫ b).left)⁻¹ := by
  rw [Fin.prod_univ_four]
  show h (r ≫ (y * (toUnit Y ≫ b))).left ^ (1 : ℤ) * h (r ≫ (y * (toUnit Y ≫ a))).left ^ (-1 : ℤ) *
    h (r ≫ toUnit Y ≫ a).left ^ (1 : ℤ) * h (r ≫ toUnit Y ≫ b).left ^ (-1 : ℤ) = _
  simp only [MonObj.comp_mul, comp_toUnit_assoc, zpow_neg, zpow_one]

theorem eq_of_diff_gen {R R' : Type} [CommRing R] [IsLocalRing R] [CommRing R']
    {A : Over (Spec (CommRingCat.of R))} [GrpObj A] [IsCommMonObj A] {L : LB A.left} (hL : L.IsLB)
    (hK : KTriv A L) (t : Spec (CommRingCat.of R') ⟶ Spec (CommRingCat.of R))
    (a b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ A) {Y : Over (Spec (CommRingCat.of R))} (y : Y ⟶ A)
    (n : Over.mk t ⊗ A ⟶ Y) (hn : n ≫ y = snd _ _ * (toUnit _ ≫ a)⁻¹)
    (v : LB.Gen (LB.LinComb L (diffφ y a b) ![1, -1, 1, -1])) (hv : v.IsGen) :
    t ≫ a.left = t ≫ b.left := by
  obtain ⟨s, hs⟩ := DVR.exists_gen_of_local L hL (K := Fin 2) ![a.left, b.left] ![-1, 1]
  let x : Over.mk t ⟶ A := (toUnit _ ≫ b) * (toUnit _ ≫ a)⁻¹
  have hx : lift (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A) ≫ μ[A] = (n ≫ y) * (toUnit _ ≫ b) := by
    rw [← Hom.mul_def, hn]
    simp only [x, MonObj.comp_mul, GrpObj.comp_inv, comp_toUnit_assoc]
    rw [mul_comm, _root_.mul_assoc, mul_comm (toUnit _ ≫ b)]
  have hy : (n ≫ y) * (toUnit _ ≫ a) = snd (Over.mk t) A := by rw [hn, inv_mul_cancel_right]
  obtain ⟨c, hc, -⟩ := exists_gen hL (K' := Fin 2)
    (φ' := ![(lift (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A) ≫ μ[A]).left, (snd (Over.mk t) A).left])
    (ε' := ![1, -1]) (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      refine (congrArg₂ (· * ·) (prod_diff y a b n h) (Fin.prod_univ_two _)).trans ?_
      rw [Fin.prod_univ_two, hy, ← hx]
      show _ * (h (toUnit (Over.mk t ⊗ A) ≫ a).left ^ (-1 : ℤ) * h (toUnit (Over.mk t ⊗ A) ≫ b).left ^ (1 : ℤ)) =
        h (lift (fst (Over.mk t) A ≫ x) (snd (Over.mk t) A) ≫ μ[A]).left ^ (1 : ℤ) *
          h (snd (Over.mk t) A).left ^ (-1 : ℤ)
      simp only [zpow_neg, zpow_one]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ v n.left) (LB.pullGen L _ _ s (toUnit (Over.mk t ⊗ A)).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hv _) (DVR.pullGen_isGen _ _ _ _ hs _))
  have h1 : x = 1 := hK R' t x fun p => ⟨⊤, trivial, exists_isGen_pull (translDiff A L x) c hc _⟩
  exact (congrArg (fun q => q.left) (mul_inv_eq_one.1 h1)).symm

section Level

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D D' : DegPre R} {e : ℕ}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

open TorusCoord

theorem torus_pG (g : GtCoord I D e G) {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (τ : Z ⟶ WeightPf.Te D I e) : (τ ≫ g.i).left ≫ g.pG.left =
      (τ ≫ g.i).left ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A := by
  have := g.q_hom
  have h : im g (τ ≫ g.i) = 1 := (im_congr g (x' := 1) (by
    rw [Category.assoc, g.isKernel.w, MonObj.one_comp, comp_toUnit_assoc, Hom.one_def])).trans (im_one g)
  refine (congrArg (fun q => q.left) h).trans ?_
  have h2 := Over.w ((Over.map (thick R I e)).map (τ ≫ g.i) ≫ fstG I e G)
  exact (congrArg (· ≫ eSec D.P.A) h2.symm).trans (by simp only [Over.comp_left, Category.assoc]; rfl)

theorem val_torus_mul (g : GtCoord I D e G) {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (χ : D.X) {z : Z.left} {J : (Z.left ⟶ D.P.A.left) → D.P.L.ι} (hJ : Good D.P.L z J)
    (τ : Z ⟶ WeightPf.Te D I e) (k a b : Z ⟶ thickObj R I e G) (hk : k = τ ≫ g.i) (ha : a = k * b) :
    val (g.t χ) a.left z J = val (g.t χ) k.left z J * val (g.t χ) b.left z J := by
  subst hk ha
  have h := val_torus g χ hJ τ 1
  rw [_root_.mul_one, val_unit g χ hJ, _root_.mul_one] at h
  exact (val_torus g χ hJ τ b).trans (congrArg (· * _) h.symm)

variable (g : GtCoord I D e G) (g' : GtCoord I D' e G) (Φ : D'.P.A ⟶ D.P.A) (hp : g'.pG ≫ Φ = g.pG)
  (χ : D.X) (χ' : D'.X)

include hp in

theorem ratio_invariant [Mono Φ.left]
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J')
    {Z : Scheme.{0}} (r r' : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J') (hJ : Good D.P.L z J)
    (hJ' : Good D'.P.L z J') (h : r ≫ g.q.left = r' ≫ g.q.left) :
    r ≫ g'.pG.left = r' ≫ g'.pG.left ∧
      val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹ = val (g'.t χ') r' z J' * (val (g.t χ) r' z J)⁻¹ := by
  have h₀ : r ≫ g.pG.left = r' ≫ g.pG.left :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (D.prBe I e).left) h).trans (Category.assoc _ _ _))
  have hp' : g'.pG.left ≫ Φ.left = g.pG.left := congrArg (fun q => q.left) hp
  have h₁ : r ≫ g'.pG.left = r' ≫ g'.pG.left := by
    rw [← cancel_mono Φ.left]
    exact (Category.assoc _ _ _).trans ((congrArg (r ≫ ·) hp').trans (h₀.trans
      ((congrArg (r' ≫ ·) hp').symm.trans (Category.assoc _ _ _).symm)))
  refine ⟨h₁, ?_⟩
  have hw : r ≫ (thickObj R I e G).hom = r' ≫ (thickObj R I e G).hom := by
    rw [← Over.w g.q, reassoc_of% h]
  let Z' : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) := Over.mk (r' ≫ (thickObj R I e G).hom)
  let a : Z' ⟶ thickObj R I e G := Over.homMk r hw
  let a' : Z' ⟶ thickObj R I e G := Over.homMk r' rfl
  obtain ⟨τ, hτ⟩ := exists_torus g a a' (Over.OverMorphism.ext h)
  obtain ⟨τ', hτ'⟩ := exists_torus g' a a' (Over.OverMorphism.ext (pullback.hom_ext
    ((Category.assoc _ _ _).trans (h₁.trans (Category.assoc _ _ _).symm))
    ((Over.w (a ≫ g'.q)).trans (Over.w (a' ≫ g'.q)).symm)))
  have hk : τ ≫ g.i = τ' ≫ g'.i := mul_right_cancel (hτ.symm.trans hτ')
  have v := val_torus_mul g χ (Z := Z') hJ τ _ a a' rfl hτ
  have v' := val_torus_mul g' χ' (Z := Z') hJ' τ' _ a a' hk hτ
  have v₀ := hker _ (τ ≫ g.i).left z J J' hJ hJ' (torus_pG g τ) (hk ▸ torus_pG g' τ')
  refine (congrArg₂ (fun s t => s * t⁻¹) v' v).trans ?_
  rw [v₀, mul_inv, _root_.mul_mul_mul_comm, mul_inv_cancel, _root_.one_mul]
  rfl

theorem Oφ_comp_hom [IsMonHom Φ] {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D'.P.A) (k : Fin 4) :
    D'.Oφ p χ' k ≫ Φ.left = (![((p ≫ Φ) * (toUnit T ≫ D'.c χ' ≫ Φ)).left, (toUnit T ≫ D'.c χ' ≫ Φ).left,
      (p ≫ Φ).left, (1 : T ⟶ D.P.A).left] : Fin 4 → _) k := by
  fin_cases k
  · exact congrArg (fun q => q.left) ((MonObj.mul_comp p (toUnit T ≫ D'.c χ') Φ).trans (by rw [Category.assoc]))
  · exact Category.assoc _ _ _
  · rfl
  · exact congrArg (fun q => q.left) (MonObj.one_comp (X := T) Φ)

variable (w : LB.Iso D'.P.L (D.P.L.pull Φ.left))

def wVal {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.P.A.left) → D.P.L.ι)
    (J' : (Z ⟶ D'.P.A.left) → D'.P.L.ι) : (Z.presheaf.stalk z)ˣ :=
  ∏ k, gw w (r ≫ D'.Oφ g'.pG χ' k) z (J ((r ≫ D'.Oφ g'.pG χ' k) ≫ Φ.left)) (J' (r ≫ D'.Oφ g'.pG χ' k)) ^ Oinvε k

include hp in

theorem exists_ratio_gen [IsMonHom Φ] (hw : PGen w) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k)
      ![1, -1, 1, -1]), u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
        Good D.P.L z J → Good D'.P.L z J' →
        val u r z J = wVal g' Φ χ' w r z J J' * (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) := by
  obtain ⟨t, ht, hv⟩ := exists_up hw D.P.isLB D'.P.isLB (g'.t χ') (g'.t_gen χ')
  obtain ⟨u, hu, hu'⟩ := exists_gen D.P.isLB
    (φ' := fun k => g.q.left ≫ diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) k) (ε' := ![1, -1, 1, -1])
    (fun U _ h => by
      refine (Fintype.prod_sum_type _).trans (Eq.trans ?_
        (prod_diff (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ) ((Over.map (thick R I e)).map g.q) h).symm)
      simp only [Sum.elim_inl, Sum.elim_inr, Oφ_comp_hom, hp]
      rw [Fin.prod_univ_four, Fin.prod_univ_four]
      let T := (Over.map (thick R I e)).obj (thickObj R I e G)
      show h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left ^ (-1 : ℤ) * h (toUnit T ≫ D'.c χ' ≫ Φ).left ^ (1 : ℤ) *
          h g.pG.left ^ (1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (-1 : ℤ) *
        (h (g.pG * (toUnit T ≫ D.c χ)).left ^ (- -1 : ℤ) * h (toUnit T ≫ D.c χ).left ^ (-1 : ℤ) *
          h g.pG.left ^ (-1 : ℤ) * h (1 : T ⟶ D.P.A).left ^ (- -1 : ℤ)) =
        h (g.pG * (toUnit T ≫ D.c χ)).left * (h (g.pG * (toUnit T ≫ D'.c χ' ≫ Φ)).left)⁻¹ *
          h (toUnit T ≫ D'.c χ' ≫ Φ).left * (h (toUnit T ≫ D.c χ).left)⁻¹
      simp only [zpow_neg, zpow_one, inv_inv]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen D.P.L _ _ _ _ t (LB.invGen D.P.L _ _ (g.t χ)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (g.t_gen χ)))
  refine ⟨u, hu, fun Z r z J J' hJ hJ' => (hu' Z r z J hJ).trans ((val_mul hJ _ _ _).trans ?_)⟩
  rw [val_inv, ← _root_.mul_assoc]
  refine congrArg (· * _) ((hv Z r z _ _ (hJ.mem _ r) (hJ'.mem _ r)).trans
    (congrArg₂ (· * ·) (Finset.prod_congr rfl fun k _ => ?_) rfl))
  rw [Category.assoc]

theorem Oφ_congr {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) {Z : Scheme.{0}} (r r' : Z ⟶ T.left)
    (h : r ≫ p.left = r' ≫ p.left) (k : Fin 4) : r ≫ D.Oφ p χ k = r' ≫ D.Oφ p χ k := by
  have hw : r ≫ T.hom = r' ≫ T.hom := by rw [← Over.w p, reassoc_of% h]
  let a : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r hw
  let a' : Over.mk (r' ≫ T.hom) ⟶ T := Over.homMk r' rfl
  have ha : a ≫ p = a' ≫ p := Over.OverMorphism.ext h
  exact (WeightPf.Oφ_comp a p χ k).trans ((congrArg (D.Oφ · χ k) ha).trans (WeightPf.Oφ_comp a' p χ k).symm)

include hp in

theorem exists_desc_gen [IsMonHom Φ] [Mono Φ.left] (hw : PGen w)
    (hker : ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'), Good D.P.L z J →
      Good D'.P.L z J' → r ≫ g.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.P.A →
      r ≫ g'.pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.P.A →
      val (g.t χ) r z J = val (g'.t χ') r z J') :
    ∃ v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) (D'.c χ' ≫ Φ) (D.c χ)) ![1, -1, 1, -1]),
      v.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J) (J'),
        Good D.P.L z J → Good D'.P.L z J' → val v (r ≫ g.q.left) z J =
          wVal g' Φ χ' w r z J J' * (val (g'.t χ') r z J' * (val (g.t χ) r z J)⁻¹) := by
  obtain ⟨u, hu, hu'⟩ := exists_ratio_gen g g' Φ hp χ χ' w hw
  have := g.q_flat
  have := g.q_surj
  have := g.q_affine
  obtain ⟨v, hv, hv'⟩ := exists_gen_of_val_eq D.P.isLB _ _ g.q.left u hu (fun Z r r' z J hJ h => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.P.L D'.P.isLB z
    obtain ⟨h₁, h₂⟩ := ratio_invariant g g' Φ hp χ χ' hker r r' z J J' hJ hJ' h
    refine (hu' Z r z J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ h₂) (hu' Z r' z J J' hJ hJ').symm)
    exact Finset.prod_congr rfl fun k _ => congrArg
      (fun ψ : Z ⟶ D'.P.A.left => gw w ψ z (J (ψ ≫ Φ.left)) (J' ψ) ^ Oinvε k)
      (Oφ_congr χ' g'.pG r r' h₁ k))
  exact ⟨v, hv, fun Z r z J J' hJ hJ' => (hv' Z r z J hJ).trans (hu' Z r z J J' hJ hJ')⟩

theorem thick_eq [IsLocalRing R] (a b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A)
    (v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) a b) ![1, -1, 1, -1])) (hv : v.IsGen) :
    thick R I e ≫ a.left = thick R I e ≫ b.left := by
  let y : Over.mk (thick R I e) ⊗ D.P.A ⟶ D.P.A := snd _ _ * (toUnit _ ≫ a)⁻¹
  have hy : y.left ≫ D.P.A.hom = (fst (Over.mk (thick R I e)) D.P.A).left ≫ thick R I e :=
    (Over.w y).trans (Over.w (fst (Over.mk (thick R I e)) D.P.A)).symm
  exact eq_of_diff_gen D.P.isLB D.P.ktriv (thick R I e) a b (D.prBe I e)
    (Over.homMk (pullback.lift y.left _ hy) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ thick R I e) (pullback.lift_snd _ _ _)).trans
        (Over.w (fst (Over.mk (thick R I e)) D.P.A)))))
    (Over.OverMorphism.ext (pullback.lift_fst _ _ _)) v hv

theorem wVal_one {Z : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))} (z : Z.left) (J) (J') :
    wVal g' Φ χ' w (1 : Z ⟶ thickObj R I e G).left z J J' = 1 := by
  let T := (Over.map (thick R I e)).obj Z
  let f : (Z.left ⟶ D'.P.A.left) → (Z.left.presheaf.stalk z)ˣ :=
    fun ψ => gw w ψ z (J (ψ ≫ Φ.left)) (J' ψ)
  have e0 : ∀ k, (1 : Z ⟶ thickObj R I e G).left ≫ D'.Oφ g'.pG χ' k = D'.Oφ (1 : T ⟶ D'.P.A) χ' k :=
    fun k => (WeightPf.Oφ_comp ((Over.map (thick R I e)).map 1) g'.pG χ' k).trans
      (congrArg (D'.Oφ · χ' k) (im_one g'))
  refine (Finset.prod_congr rfl fun k _ => congrArg (fun ψ => f ψ ^ Oinvε k) (e0 k)).trans ?_
  rw [Fin.prod_univ_four]
  show f ((1 : T ⟶ D'.P.A) * (toUnit T ≫ D'.c χ')).left ^ (-1 : ℤ) * f (toUnit T ≫ D'.c χ').left ^ (1 : ℤ) *
    f (1 : T ⟶ D'.P.A).left ^ (1 : ℤ) * f (1 : T ⟶ D'.P.A).left ^ (-1 : ℤ) = 1
  rw [_root_.one_mul]
  simp

theorem val_eq_one (hG : GlobalFnsSt) (a b : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D.P.A) (hab : a = b)
    (v : LB.Gen (LB.LinComb D.P.L (diffφ (D.prBe I e) a b) ![1, -1, 1, -1])) (hv : v.IsGen)
    (h₁ : ∀ y J, Good D.P.L y J →
      val v (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.P.A).left y J = 1)
    (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e D.P.A).left) (z : Z) (J) (hJ : Good D.P.L z J) :
    val v r z J = 1 := by
  subst hab
  refine (gen_unique' D.P.isLB (u' := LB.oneGen D.P.L) (fun U _ h => ?_) (thickObj R I e D.P.A).hom
    (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e D.P.A).left (Over.w _)
    (hG _ _ (TLinPf.isAb_pullback _ _ D.P.isAb)).2 hv
    (isGen_of_gm _ fun y j j' _ _ => ?_) (fun y J hJ => (h₁ y J hJ).trans (val_one _).symm) Z r z J hJ).trans
    (val_one _)
  · refine (Fintype.prod_empty _).trans (Eq.symm ?_)
    rw [Fin.prod_univ_four]
    simp [diffφ]
  · exact (map_one _).trans (Eq.symm ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans
      (_root_.mul_one _)))

end Level

end GlobalTheory.CoordCompare

namespace GlobalTheory

open CoordCompare in

theorem unifPre_c_and_coord_correspond : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → (∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left) → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → r ≫ (U.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D.toPre.P.A → r ≫ (U'.gt e).pG.left = r ≫ (fstG I e G).left ≫ G.hom ≫ eSec D'.toPre.P.A → ∀ x, Geo.Tor.val ((U.gt e).t (xe x)) r z J = Geo.Tor.val ((U'.gt e).t x) r z J') → ((∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x)) ∧ ∀ e : ℕ, ((U'.gt e).pG.left ≫ Φ.hom.left = (𝟙 _) ≫ (U.gt e).pG.left ∧ ∀ x : D'.toPre.X, (∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ Φ.hom.left = (𝟙 _) ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ) ∧ Geo.Tor.PMaps w (D'.toPre.Oφ (U'.gt e).pG x) (D.toPre.Oφ (U.gt e).pG (xe x)) Oinvε ((U'.gt e).t x) ((U.gt e).t (xe x)) (𝟙 _))) := by
  intro hG R _ _ _ I hA D D' A A' G _ _ _ U U' Φ w hw hΦ hp xe hker
  obtain ⟨_, -, -, _⟩ := hA
  have hw' := (isGen_iff w).1 hw
  have hp' : ∀ e, (U'.gt e).pG ≫ Φ.hom = (U.gt e).pG := fun e => Over.OverMorphism.ext (hp e)
  have desc := fun e x => exists_desc_gen (U.gt e) (U'.gt e) Φ.hom (hp' e) (xe x) x w hw'
    (fun Z r z J J' hJ hJ' h h' => hker e Z r z J J' hJ hJ' h h' x)
  have hc : ∀ x, D'.toPre.c x ≫ Φ.hom = D.toPre.c (xe x) := fun x => by
    have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    have := D.toPre.P.isAb.proper
    have h := (sec_eq_zero_and_hom_eq_of_thickenings R I (IsAdicComplete.le_jacobson_bot I)
      D.toPre.P.A).2 D.toPre.P.A (toUnit _ ≫ D'.toPre.c x ≫ Φ.hom) (toUnit _ ≫ D.toPre.c (xe x)) fun n => by
        obtain ⟨v, hv, -⟩ := desc n x
        have h₁ := thick_eq _ _ v hv
        have h₂ : (fstG I n D.toPre.P.A).left ≫ (toUnit D.toPre.P.A).left =
            pullback.snd D.toPre.P.A.hom (thick R I n) ≫ thick R I n := pullback.condition
        exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).trans
          ((congrArg (_ ≫ ·) h₁).trans ((Category.assoc _ _ _).symm.trans
            ((congrArg (· ≫ _) h₂.symm).trans (Category.assoc _ _ _))))))
    simpa using congrArg (η[D.toPre.P.A] ≫ ·) h
  refine ⟨hc, fun e => ⟨(hp e).trans (Category.id_comp _).symm, fun x => ?_⟩⟩
  have hψ : ∀ κ : Fin 4, D'.toPre.Oφ (U'.gt e).pG x κ ≫ Φ.hom.left =
      𝟙 _ ≫ D.toPre.Oφ (U.gt e).pG (xe x) κ := fun κ => by
    rw [Oφ_comp_hom, hp', hc, Category.id_comp]
    rfl
  refine ⟨hψ, (maps_iff w _ _ _ _ _ (𝟙 _) _ (GeneratorPullback.pullAlong_le _ _ _ _ _ hψ) (fun _ => rfl)).1
    (maps_of_good hw' D.toPre.P.isLB D'.toPre.P.isLB _ ((U'.gt e).t_gen x) _ ((U.gt e).t_gen _) hψ
      fun y J J' hJ hJ' => ?_)⟩
  obtain ⟨v, hv, hv'⟩ := desc e x
  have h₁ := val_eq_one hG _ _ (hc x) v hv (fun y J hJ => by
    obtain ⟨J', hJ'⟩ := TLinPf.idx_exists D'.toPre.P.L D'.toPre.P.isLB y
    have := (U.gt e).q_hom
    have h := hv' _ (1 : 𝟙_ (Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) ⟶ thickObj R I e G).left
      y J J' hJ hJ'
    rwa [← Over.comp_left, MonObj.one_comp, wVal_one, TorusCoord.val_unit _ _ hJ,
      TorusCoord.val_unit _ _ hJ', inv_one, _root_.mul_one, _root_.mul_one] at h) _ (𝟙 _ ≫ (U.gt e).q.left) y J hJ
  have h₂ := (hv' _ (𝟙 _) y J J' hJ hJ').symm.trans h₁
  rw [← _root_.mul_assoc, mul_inv_eq_one] at h₂
  refine h₂.symm.trans (congrArg (· * _) ?_)
  simp only [wVal, Category.id_comp]

end GlobalTheory
