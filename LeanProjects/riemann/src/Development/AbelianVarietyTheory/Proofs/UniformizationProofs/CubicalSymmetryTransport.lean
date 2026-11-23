import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul

noncomputable section

namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace CubTransport

open TopologicalSpace ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

section Down

variable {X X' Y Y' Z : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]

theorem exists_down_units {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y ⟶ X')} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L (fun k => φ' k ≫ F) ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) =
          pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
  choose u hu using fun p q => exists_pw w φ' ε p q
  have glue : ∀ q : K → L'.ι, ∃ s : Γ(Y, LB.wchart L' φ' q)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
      r z ∈ LB.wchart L (fun k => φ' k ≫ F) p → r z ∈ LB.wchart L' φ' q →
      gm r z _ s = (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) := by
    intro q
    have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) p,
        r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q →
        gm r z _ ((u p q)⁻¹ * res inf_le_left (t.s p)) =
          (pw w φ' ε r z p q)⁻¹ * gm r z (LB.wchart L (fun k => φ' k ≫ F) p) (t.s p) :=
      fun Z r z p hz => (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_inv _ _).trans
        (congrArg (·⁻¹) (hu p q _ _ z hz))) (gm_res _ z _ hz _))
    obtain ⟨s, hs⟩ := glue_unit _ (fun p => LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q)
      (fun _ => inf_le_right)
      (fun y hy => by
        choose p hp using fun k => exists_chart hL (F (φ' k y))
        exact Opens.mem_iSup.2 ⟨p, Set.mem_iInter.2 hp, hy⟩) (fun p => (u p q)⁻¹ * res inf_le_left (t.s p))
      (fun p p' y hy => by
        rw [hv _ _ y p hy.1, hv _ _ y p' hy.2, pw_trans hw φ' ε (𝟙 Y) y hy.1.1 hy.2.1 hy.1.2 hy.1.2,
          trF_self hL' _ ε (𝟙 Y) y hy.1.2, gen_trans ht (𝟙 Y) y hy.1.1 hy.2.1, inv_one, _root_.mul_one, mul_inv,
          _root_.mul_mul_mul_comm, inv_mul_cancel, _root_.one_mul])
    refine ⟨s, fun Z r z p h₁ h₂ => ?_⟩
    have hz : r z ∈ LB.wchart L (fun k => φ' k ≫ F) p ⊓ LB.wchart L' φ' q := ⟨h₁, h₂⟩
    exact (gm_res _ z inf_le_right hz s).symm.trans ((congrArg (gm _ z _) (hs p)).trans (hv Z r z p hz))
  choose s hs using glue
  refine ⟨⟨s⟩, isGen_of_gm _ fun y j j' hj hj' => ?_, fun Z r z p q h₁ h₂ => ?_⟩
  · choose p hp using fun k => exists_chart hL (F (φ' k y))
    have m : y ∈ LB.wchart L (fun k => φ' k ≫ F) p := Set.mem_iInter.2 hp
    refine (hs j _ (𝟙 Y) y p m hj).trans (Eq.trans ?_ (congrArg _ (hs j' _ (𝟙 Y) y p m hj')).symm)
    rw [pw_trans hw φ' ε (𝟙 Y) y m m hj hj', trF_self hL _ ε (𝟙 Y) y m, _root_.one_mul, mul_inv, inv_inv,
      _root_.mul_assoc]
  · exact (mul_inv_cancel_left _ _).symm.trans (congrArg (pw w φ' ε r z p q * ·) (hs q Z r z p h₁ h₂).symm)

theorem exists_pmaps {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB)
    {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} (h : Y' ⟶ Y) (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) :
    ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧ PMaps w φ' φ ε a t h := by
  have key : ∀ (ψ : K → (Y' ⟶ X)) (_ : ∀ k, φ' k ≫ F = ψ k) (t₀ : LB.Gen (LB.LinComb L ψ ε)), t₀.IsGen →
      ∃ a : LB.Gen (LB.LinComb L' φ' ε), a.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (p : K → L.ι) (q : K → L'.ι),
        r z ∈ LB.wchart L ψ p → r z ∈ LB.wchart L' φ' q →
        gm r z (LB.wchart L ψ p) (t₀.s p) = pw w φ' ε r z p q * gm r z (LB.wchart L' φ' q) (a.s q) := by
    intro ψ hψ t₀ h₀
    obtain rfl : (fun k => φ' k ≫ F) = ψ := funext hψ
    exact exists_down_units hw hL hL' t₀ h₀
  obtain ⟨a, ha, hv⟩ := key _ hc (LB.pullGen L φ ε t h) (pullGen_isGen _ _ _ _ ht h)
  refine ⟨a, ha, fun Z r z p q hp hq => ?_⟩
  have hm : r z ∈ LB.wchart L (fun k => h ≫ φ k) p := Set.mem_iInter.2 fun k => by
    show φ k (h (r z)) ∈ L.U (p k)
    rw [pt_eq hc]; exact hp k
  refine Eq.trans ?_ (hv Z r z p q hm (Set.mem_iInter.2 hq))
  exact ((gm_res r z _ hm _).trans (gm_pull r h z (LB.wchart L φ p)
    (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hm k) _)).symm

theorem val_pmaps {w : LB.Iso L' (L.pull F)} {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y}
    (hc : ∀ k, φ' k ≫ F = h ≫ φ k) {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)}
    (H : PMaps w φ' φ ε a t h) (r : Z ⟶ Y') {z : Z} {J J'} (hJ : Good L z J) (hJ' : Good L' z J') :
    val t (r ≫ h) z J = (∏ k, gw w (r ≫ φ' k) z (J ((r ≫ φ' k) ≫ F)) (J' (r ≫ φ' k)) ^ ε k) * val a r z J' := by
  rw [val_of t (r ≫ h) z J (fun k => J ((r ≫ φ' k) ≫ F)) (fun k => by rw [Category.assoc, Category.assoc, hc])]
  exact H Z r z _ _ (fun k => hJ ((r ≫ φ' k) ≫ F)) (fun k => hJ' (r ≫ φ' k))

end Down

theorem isCub_of_twist {A A' U : Type} [CommGroup A] [CommGroup A'] [CommGroup U] {θ : A → A → A → U}
    (hθ : IsCub θ) (β : A' →* A) (Ω : A' → U) {θ' : A' → A' → A' → U}
    (h : ∀ a b c, θ (β a) (β b) (β c) = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b *
      Ω c * (Ω 1)⁻¹ * θ' a b c) : IsCub θ' := by
  refine ⟨fun x y => ?_, fun x y z => ?_, fun x y z => ?_, fun x x' x'' y => ?_⟩
  · have e := h 1 x y
    rw [map_one, hθ.face] at e
    simp only [_root_.one_mul] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢
    linear_combination (norm := abel) -e'
  · have e := hθ.s01 (β x) (β y) (β z)
    rw [h, h, mul_comm y x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.s12 (β x) (β y) (β z)
    rw [h, h, mul_comm z y, mul_right_comm x z y] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'
  · have e := hθ.coc (β x) (β x') (β x'') (β y)
    rw [← map_mul, ← map_mul, h, h, h, h] at e
    simp only [← _root_.mul_assoc x] at e
    apply Additive.ofMul.injective
    have e' := congrArg Additive.ofMul e
    simp only [ofMul_mul, ofMul_inv] at e' ⊢
    linear_combination (norm := abel) e'

section Cub

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}

def thV (t : LB.Gen (Theta G L.L)) {T : Over S} (z : T.left) (J : (T.left ⟶ G.left) → L.L.ι) (x x' y : T ⟶ G) :
    (T.left.presheaf.stalk z)ˣ :=
  val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (lift x (lift x' y)).left z J

theorem val_thV (t : LB.Gen (Theta G L.L)) {T : Over S} {z : T.left} {J : (T.left ⟶ G.left) → L.L.ι}
    (hJ : Good L.L z J) (x x' y : T ⟶ G) :
    val (LB.pullGen L.L (thφ G (x3 G)) thε t (lift x (lift x' y)).left) (𝟙 T.left) z J = thV t z J x x' y := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [Category.id_comp]; rfl

theorem val_id_thV (t : LB.Gen (Theta G L.L)) {z : (G3 G).left} {J : ((G3 G).left ⟶ G.left) → L.L.ι} :
    val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) t (𝟙 (G3 G).left) z J = thV t z J (x3 G 0) (x3 G 1) (x3 G 2) := by
  have e : lift (x3 G 0) (lift (x3 G 1) (x3 G 2)) = 𝟙 (G3 G) := by
    ext <;> simp [x3]
  rw [thV, e]; rfl

def cubicalOfVal (t : LB.Gen (Theta G L.L)) (ht : t.IsGen)
    (h : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → IsCub (thV t z J)) : CubicalStr G L where
  t := t
  isGen := ht
  face i := corr_of_val L.isLB fun y J hJ => by
    refine Eq.trans ?_ (val_one _).symm
    have C := h (G2 G) y J hJ
    fin_cases i
    · exact (val_thV t hJ _ _ _).trans (C.face _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₂ _ _)
    · exact (val_thV t hJ _ _ _).trans (C.face₃ _ _)
  cubeSymmetric_swap_first := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s01 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cubeSymmetric_swap_last := corr_of_val L.isLB fun y J hJ =>
    (val_id_thV t).trans (((h (G3 G) y J hJ).s12 _ _ _).trans (val_thV t hJ _ _ _).symm)
  cocycle := corr_of_val L.isLB fun y J hJ =>
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).trans
      (((h (G4 G) y J hJ).coc _ _ _ _).trans
        ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_thV t hJ _ _ _) (val_thV t hJ _ _ _))).symm)

end Cub

end CubTransport

open CubTransport ReciprocityTheory.ChartRestriction.G.Geo.Tor in

theorem cubical_symmetry_transport : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (Ψ : G'.left ⟶ G.left) (hgp : Geo.Tor.IsGrpPullback G' G f Ψ) (L : RigLB G) (L' : RigLB G') (wL : LB.Iso L'.L (L.L.pull Ψ)) (he : eSec G' ≫ Ψ = f ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig (rigPullOf Ψ f he L.L L.rig) → ∀ (c : CubicalStr G L) (s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])), s.IsGen → LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) → ∃ (c' : CubicalStr G' L') (s' : LB.Gen (LB.LinComb L'.L (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![1, -1])), s'.IsGen ∧ LB.Gen.Corr L'.L _ _ _ _ (LB.pullGen L'.L _ _ s' (eSec G')) (LB.oneGen L'.L) ∧ Geo.Tor.PMaps wL (thφ G' (x3 G')) (thφ G (x3 G)) thε c'.t c.t (Geo.Tor.cubeMapOf hgp).F3 ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G']).left, 𝟙 G'.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] s' s Ψ := by
  intro S S' f G _ _ G' _ _ Ψ hgp L L' wL he hw _ c s hs hs1
  have hw' := (isGen_iff wL).1 hw
  have good : ∀ {Z : Scheme.{0}} (z : Z), ∃ J, Good L.L z J := fun {Z} z => by
    choose I hI using fun χ : Z ⟶ G.left => exists_chart L.isLB (χ z)
    exact ⟨I, hI⟩
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ Ψ = (cubeMapOf hgp).F3 ≫ thφ G (x3 G) I :=
    fun I => (cubeMapOf hgp).psum_comm I.down
  obtain ⟨t', ht', Ht⟩ := exists_pmaps hw' L.isLB L'.isLB (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε)
    (cubeMapOf hgp).F3 hc c.t c.isGen
  have hι : (ι[G']).left ≫ Ψ = Ψ ≫ (ι[G]).left := by
    have e := congrArg (fun q => q.left) (map_inv (pushHom hgp G') (𝟙 G'))
    simp only [Hom.inv_def, Category.id_comp] at e
    refine e.trans ?_
    show (𝟙 _ ≫ Ψ) ≫ _ = _
    rw [Category.id_comp]
  have hc₂ : ∀ k : Fin 2, ![(ι[G']).left, 𝟙 G'.left] k ≫ Ψ = Ψ ≫ ![(ι[G]).left, 𝟙 G.left] k := fun k => by
    fin_cases k
    · exact hι
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
  obtain ⟨s', hs', Hs⟩ := exists_pmaps hw' L.isLB L'.isLB Ψ hc₂ s hs
  refine ⟨cubicalOfVal t' ht' fun T z J' hJ' => ?_, s', hs', corr_of_val L'.isLB fun y J' hJ' => ?_, Ht, Hs⟩
  · obtain ⟨J, hJ⟩ := good z
    refine isCub_of_twist (isCub_cubV c (T := Over.mk (T.hom ≫ f)) hJ) (pushHom hgp T)
      (fun x => gw wL x.left z (J (x.left ≫ Ψ)) (J' x.left)) fun a b d => ?_
    have q : (lift a (lift b d)).left ≫ (cubeMapOf hgp).F3 =
        (lift (pushHom hgp T a) (lift (pushHom hgp T b) (pushHom hgp T d))).left := hom_ext_triple _ fun i => by
      rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
      fin_cases i <;> simp [x3] <;> rfl
    have e := val_pmaps hc Ht (lift a (lift b d)).left hJ hJ'
    rw [q] at e
    exact e.trans (congrArg₂ (· * ·) (prod_cub a b d (fun q => gw wL q z (J (q ≫ Ψ)) (J' q))) rfl)
  · obtain ⟨J, hJ⟩ := good y
    have e := val_pmaps hc₂ Hs (eSec G') hJ hJ'
    have e₁ : val s (eSec G' ≫ Ψ) y J = 1 := by
      rw [he]
      exact (val_pull hJ s (eSec G) f).symm.trans ((val_corr hJ hs1 f).trans (val_one _))
    have e₂ : eSec G' ≫ (ι[G']).left = eSec G' := by
      rw [eSec, ← Over.comp_left, GrpObj.one_inv]
    rw [e₁, Fin.prod_univ_two] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, e₂, Category.comp_id, zpow_one, zpow_neg,
      mul_inv_cancel, _root_.one_mul] at e
    refine (val_pull hJ' _ _ _).trans (Eq.trans ?_ (val_one _).symm)
    rw [Category.id_comp]
    exact e.symm

end GlobalTheory
