import Mathlib
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.CubicalSymmetricTriv
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsAffineWeightUnits

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.UU GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.CubCompare
variable {S S' : Scheme.{0}}

section Gen
variable {X X' Y Y' : Scheme.{0}} {K : Type} [Fintype K]

theorem gen_eq_of_val {L : LB X} (hL : L.IsLB) {φ : K → (Y ⟶ X)} {ε : K → ℤ} {t t' : LB.Gen (LB.LinComb L φ ε)}
    (ht : t.IsGen) (ht' : t'.IsGen) (h : ∀ y J, Good L y J → val t (𝟙 Y) y J = val t' (𝟙 Y) y J) : t = t' := by
  have e : t.s = t'.s := funext fun j => Units.ext (sec_ext_val hL (s := genSec t ht) (s' := genSec t' ht')
    (fun y J hJ => by rw [sval_genSec t ht _ y hJ, sval_genSec t' ht' _ y hJ, h y J hJ]) j)
  cases t; cases t'; cases e; rfl

theorem pmaps_of_val {L : LB X} {L' : LB X'} {F : X' ⟶ X} {w : LB.Iso L' (L.pull F)} (hw : w.IsGen) (hL : L.IsLB)
    (hL' : L'.IsLB) {φ' : K → (Y' ⟶ X')} {φ : K → (Y ⟶ X)} {ε : K → ℤ} {h : Y' ⟶ Y} (hc : ∀ k, φ' k ≫ F = h ≫ φ k)
    {a : LB.Gen (LB.LinComb L' φ' ε)} {t : LB.Gen (LB.LinComb L φ ε)} (ha : a.IsGen) (ht : t.IsGen)
    (H : ∀ (y : Y') J' J, Good L' y J' → Good L y J → val t (𝟙 Y' ≫ h) y J =
      (∏ k, gw w (𝟙 Y' ≫ φ' k) y (J ((𝟙 Y' ≫ φ' k) ≫ F)) (J' (𝟙 Y' ≫ φ' k)) ^ ε k) * val a (𝟙 Y') y J') :
    PMaps w φ' φ ε a t h := by
  obtain ⟨a', ha', H'⟩ := CubTransport.exists_pmaps ((isGen_iff w).1 hw) hL hL' h hc t ht
  obtain rfl : a = a' := gen_eq_of_val hL' ha ha' fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good_pt hL y
    exact mul_left_cancel ((H y J' J hJ' hJ).symm.trans (CubTransport.val_pmaps hc H' (𝟙 Y') hJ hJ'))
  exact H'

end Gen

section Pack
variable {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem symCub_iff {A U : Type} [CommGroup A] [CommGroup U] {σ : A → U} (h : σ 1 = 1) {C C' : U} {x y u : A} :
    C' * σ (x * y) * σ (x * u) * σ (y * u) = C * σ (x * y * u) * σ x * σ y * σ u ↔ C' = thirdDiff σ x y u * C := by
  rw [thirdDiff, h]
  constructor <;> intro e <;> apply Additive.ofMul.injective <;> have e' := congrArg Additive.ofMul e <;>
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢ <;> linear_combination (norm := abel) e'

theorem symV_one {L : RigLB G} {σ : LB.Gen (symLB G L.L)}
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ σ (eSec G)) (LB.oneGen L.L)) {T : Over S} {z : T.left} {J}
    (hJ : Good L.L z J) : symV σ z J (1 : T ⟶ G) = 1 := by
  rw [symV, one_left]
  exact (val_pull hJ σ (eSec G) T.hom).symm.trans ((val_corr hJ hr T.hom).trans (val_one _))

def toCubSym (P : CP G) : CubSym G :=
  ⟨P.L, P.c, P.sym, P.sym_gen, P.sym_rig, fun T z J hJ x y u =>
    (symCub_iff (σ := symV P.sym z J) (symV_one P.sym_rig hJ)).1 (P.sym_cub T x y u z J hJ)⟩

def toCP (L : CubSym G) : CP G :=
  ⟨L.L, L.cub, L.sym, L.sym_gen, L.sym_rig, fun T x y u z J hJ =>
    (symCub_iff (σ := symV L.sym z J) (symV_one L.sym_rig hJ)).2 (L.sym_cub T z J hJ x y u)⟩

def cpEquiv (G : Over S) [GrpObj G] [IsCommMonObj G] : CP G ≃ CubSym G :=
  ⟨toCubSym, toCP, fun _ => rfl, fun _ => rfl⟩

end Pack

section Maps
variable {G : Over S} {G' : Over S'} [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G']

theorem eSec_hom (G : Over S) [GrpObj G] : eSec G ≫ G.hom = 𝟙 S := Over.w η[G]

theorem cubeMap_triple_over (m : CubeMap G' G) : m.F3 ≫ (G3 G).hom = (G3 G').hom ≫ m.e := by
  have e : (1 : G3 G' ⟶ G').left ≫ m.F = m.F3 ≫ (1 : G3 G ⟶ G).left := m.psum_comm ∅
  rw [one_left, one_left, Category.assoc, m.e_comm] at e
  have e' := congrArg (· ≫ G.hom) e
  simp only [Category.assoc] at e'
  erw [eSec_hom, Category.comp_id, Category.comp_id] at e'
  exact e'.symm

theorem cubeMap_over (m : CubeMap G' G) : m.F ≫ G.hom = G'.hom ≫ m.e := by
  let d : G' ⟶ G3 G' := lift (𝟙 _) (lift (𝟙 _) (𝟙 _))
  have hd : d.left ≫ (x3 G' 0).left = 𝟙 _ := by rw [← Over.comp_left]; simp [d, x3]
  have e := congrArg (fun q => d.left ≫ q ≫ G.hom) (cubeMap_comp_proj_three m 0)
  simp only [Category.assoc, Over.w] at e
  rw [cubeMap_triple_over, ← Category.assoc, Over.w, ← Category.assoc, hd, Category.id_comp] at e
  exact e.symm

theorem cubeMap_lift (m : CubeMap G' G) {T : Over S'} (x y u : T ⟶ G') :
    (lift x (lift y u)).left ≫ m.F3 = (lift (toBase (cubeMap_over m) x)
      (lift (toBase (cubeMap_over m) y) (toBase (cubeMap_over m) u))).left := hom_ext_triple _ fun i => by
  rw [Category.assoc, cubeMap_comp_proj_three, ← Category.assoc, ← Over.comp_left, ← Over.comp_left]
  fin_cases i <;> simp [x3] <;> rfl

theorem cubeMap_mul (m : CubeMap G' G) (T : Over S') (x y : T ⟶ G') :
    toBase (cubeMap_over m) (x * y) = toBase (cubeMap_over m) x * toBase (cubeMap_over m) y := by
  have p : ∀ {S : Scheme.{0}} (G : Over S) [GrpObj G] [IsCommMonObj G] {T : Over S} (x y : T ⟶ G),
      lift x (lift y y) ≫ psum G (x3 G) {0, 1} = x * y := fun G _ _ T x y => by
    have : psum G (x3 G) {0, 1} = x3 G 0 * x3 G 1 := congrArg (x3 G 0 * ·) (_root_.mul_one _)
    rw [this, MonObj.comp_mul]; simp [x3]
  have e := congrArg ((lift x (lift y y)).left ≫ ·) (m.psum_comm {0, 1})
  simp only [← Category.assoc] at e
  rw [← Over.comp_left, p, cubeMap_lift, ← Over.comp_left, p] at e
  exact Over.OverMorphism.ext e

def cubeMapOf {f : S' ⟶ S} {F : G'.left ⟶ G.left} {hw : F ≫ G.hom = G'.hom ≫ f}
    (mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y) : CubeMap G' G where
  F := F
  F3 := (lift (toBaseHom mul _ (x3 G' 0)) (lift (toBaseHom mul _ (x3 G' 1)) (toBaseHom mul _ (x3 G' 2)))).left
  e := f
  e_comm := by
    have := one_left_comp mul (𝟙_ (Over S'))
    rw [one_left] at this
    exact ((congrArg (· ≫ F) (Category.id_comp _)).symm.trans this).trans (congrArg (· ≫ eSec G) (Category.id_comp f))
  psum_comm I := by
    let β := toBaseHom mul
    have e : β (G3 G') (psum G' (x3 G') I) =
        lift (β (G3 G') (x3 G' 0)) (lift (β (G3 G') (x3 G' 1)) (β (G3 G') (x3 G' 2))) ≫ psum G (x3 G) I :=
      (psum_hom (β (G3 G')) (x3 G') I).trans ((congrArg (fun q => psum G q I) (funext fun i => by
        fin_cases i <;> simp [x3, preHom])).trans (psum_hom (preHom (lift (β (G3 G') (x3 G' 0))
          (lift (β (G3 G') (x3 G' 1)) (β (G3 G') (x3 G' 2))))) (x3 G) I).symm)
    exact congrArg (fun q => q.left) e

theorem cub_alg_iff {U : Type} [CommGroup U] {C C' a b c d e g h k : U} :
    C * b * c * d * k = a * e * g * h * C' ↔ C = a * b⁻¹ * c⁻¹ * d⁻¹ * e * g * h * k⁻¹ * C' := by
  refine ⟨fun H => ?_, cub_alg⟩
  apply Additive.ofMul.injective
  have e' := congrArg Additive.ofMul H
  simp only [ofMul_mul, ofMul_inv] at e' ⊢
  linear_combination (norm := abel) e'

theorem isCPMap_iff (m : CubeMap G' G) (P' : CP G') (P : CP G) (w : LB.Iso P'.L.L (P.L.L.pull m.F)) :
    IsCPMap P' P m.e m.F (cubeMap_over m) w ↔ IsCubSymIso m (toCubSym P') (toCubSym P) w := by
  have r := maps_iff w (K := PUnit) (fun _ => eSec G') (fun _ => eSec G) (fun _ => 1) P'.L.rig P.L.rig m.e
    (m.rigPull P.L.L P.L.rig) (rigPull_le m.F m.e m.e_comm P.L.L) (fun _ => rfl)
  have c := maps_iff w (thφ G' (x3 G')) (thφ G (x3 G)) thε P'.c.t P.c.t m.F3 (m.thetaPull P.L.L P.c.t)
    (m.theta_le P.L.L) (fun _ => rfl)
  have hc : ∀ I : thK.{0}, thφ G' (x3 G') I ≫ m.F = m.F3 ≫ thφ G (x3 G) I := fun I => m.psum_comm I.down
  constructor
  · intro h
    refine ⟨⟨h.gen, r.2 (pmaps_of_val h.gen P.L.isLB P'.L.isLB (fun _ => m.e_comm) P'.L.rigGen P.L.rigGen
      fun y J' J hJ' hJ => ?_)⟩, c.2 (pmaps_of_val h.gen P.L.isLB P'.L.isLB hc P'.c.isGen P.c.isGen
      fun y J' J hJ' hJ => ?_), fun Z z J' J hJ' hJ ψ => ?_⟩
    · have e := (h.vals (𝟙_ _) y J' J hJ' hJ _ (fun _ => rfl)).1
      rw [one_left] at e
      rw [Fintype.prod_unique, zpow_one]
      exact e
    · have e := cub_alg_iff.1 ((h.vals (G3 G') y J' J hJ' hJ _ (fun _ => rfl)).2.2 (x3 G' 0) (x3 G' 1) (x3 G' 2))
      have l : lift (x3 G' 0) (lift (x3 G' 1) (x3 G' 2)) = 𝟙 _ := by simp [x3]
      have l' : 𝟙 (G3 G').left = (lift (x3 G' 0) (lift (x3 G' 1) (x3 G' 2))).left := by rw [l]; rfl
      rw [l', cubeMap_lift]
      exact e.trans (congrArg₂ (· * ·) (prod_cub _ _ _ (fun q => gw w q y (J (q ≫ m.F)) (J' q))).symm rfl)
    · exact (h.vals (Over.mk (ψ ≫ G'.hom)) z J' J hJ' hJ _ (fun _ => rfl)).2.1 (Over.homMk ψ rfl)
  · intro h
    refine ⟨cubeMap_mul m, h.gen, fun T z J' J hJ' hJ W hW => ⟨?_, fun x => ?_, fun x y u => cub_alg ?_⟩⟩
    · have e := CubTransport.val_pmaps (fun _ => m.e_comm) (r.1 h.rig) T.hom hJ hJ'
      rw [Fintype.prod_unique, zpow_one, ← one_left] at e
      rw [hW]; exact e
    · rw [hW, hW]; exact h.even _ z J' J hJ' hJ x.left
    · have e := CubTransport.val_pmaps hc (c.1 h.cub) (lift x (lift y u)).left hJ hJ'
      rw [cubeMap_lift] at e
      simp only [hW]
      exact e.trans (congrArg₂ (· * ·) (prod_cub x y u (fun q => gw w q z (J (q ≫ m.F)) (J' q))) rfl)

theorem isCPMap_iff_exists {f : S' ⟶ S} {F : G'.left ⟶ G.left} (hw : F ≫ G.hom = G'.hom ≫ f) (P' : CP G') (P : CP G)
    (w : LB.Iso P'.L.L (P.L.L.pull F)) : IsCPMap P' P f F hw w ↔
      ∃ mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y,
        IsCubSymIso (cubeMapOf mul) (toCubSym P') (toCubSym P) w :=
  ⟨fun h => ⟨h.mul, (isCPMap_iff (cubeMapOf h.mul) P' P w).1 h⟩,
    fun ⟨mul, h⟩ => (isCPMap_iff (cubeMapOf mul) P' P w).2 h⟩

theorem cubeMapOf_cubeMap_mul (m : CubeMap G' G) : cubeMapOf (cubeMap_mul m) = m := by
  have e : (cubeMapOf (cubeMap_mul m)).F3 = m.F3 := hom_ext_triple _ fun i =>
    (cubeMap_comp_proj_three _ i).trans (cubeMap_comp_proj_three m i).symm
  obtain ⟨F, F3, e₀, h₁, h₂⟩ := m
  simp only [cubeMapOf] at e ⊢
  congr

end Maps

section Triv
variable {G H : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H]

omit [IsCommMonObj H] in

def biTrivEquiv {L : RigLB G} (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i] :
    BiTriv c i ≃ {s : LB.Gen (lamOn i L.L) // IsBiextTriv c i s} where
  toFun σ := ⟨σ.s, σ.gen, fun T z J hJ t t' x => σ.law1 T t t' x z J hJ, fun T z J hJ t x x' => σ.law2 T t x x' z J hJ⟩
  invFun s := ⟨s.1, s.2.gen, fun T t t' x z J hJ => s.2.law₁ T z J hJ t t' x,
    fun T t x x' z J hJ => s.2.law₂ T z J hJ t x x'⟩
  left_inv _ := rfl
  right_inv _ := rfl

def RigMul (L : RigLB G) (i : H ⟶ G)
    (τ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (σ : LB.Gen (L.L.pull i.left)) : Prop :=
  ∀ (T : Over S) (z : T.left) (J), Good L.L z J → ∀ t : T ⟶ H, trivV σ z J t = val τ t.left z J * rigV L z J

variable {L : RigLB G} {i : H ⟶ G}

omit [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] in
theorem val_rigPull {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) (t : T ⟶ H) :
    val (LB.pullGen L.L (fun _ : PUnit => eSec G) (fun _ => 1) L.rig H.hom) t.left z J = rigV L z J := by
  refine (val_pull hJ _ _ _).trans ?_
  rw [rigV, Rosenlicht.toUnit_left, Over.w]

omit [IsCommMonObj H] in

theorem existsUnique_rigMul_right
    (τ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])) (hτ : τ.IsGen) :
    ∃! σ : LB.Gen (L.L.pull i.left), σ.IsGen ∧ RigMul L i τ σ := by
  obtain ⟨σ, hσ, hv⟩ := exists_gen L.isLB (K' := PUnit) (φ' := fun _ => i.left) (ε' := fun _ => 1) (fun U _ h => by
      rw [Fintype.prod_sum_type, one_left]
      simp [Fin.prod_univ_two])
    (LB.mulGen L.L _ _ _ _ τ (LB.pullGen L.L (fun _ : PUnit => eSec G) (fun _ => 1) L.rig H.hom))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hτ (DVR.pullGen_isGen _ _ _ _ L.rigGen _))
  have R : RigMul L i τ σ := fun T z J hJ t =>
    (hv _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg _ (val_rigPull hJ t)))
  exact ⟨σ, ⟨hσ, R⟩, fun σ' h => gen_eq_of_val L.isLB h.1 hσ fun y J hJ =>
    (h.2 H y J hJ (𝟙 H)).trans (R H y J hJ (𝟙 H)).symm⟩

omit [IsCommMonObj H] in

theorem existsUnique_rigMul_left (σ : LB.Gen (L.L.pull i.left)) (hσ : σ.IsGen) :
    ∃! τ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1]), τ.IsGen ∧ RigMul L i τ σ := by
  obtain ⟨τ, hτ, hv⟩ := exists_gen L.isLB (K' := Fin 2) (φ' := ![i.left, (1 : H ⟶ G).left]) (ε' := ![1, -1])
    (fun U _ h => by
      rw [Fintype.prod_sum_type, one_left]
      simp [Fin.prod_univ_two])
    (LB.mulGen L.L _ _ _ _ σ (LB.invGen L.L _ _ (LB.pullGen L.L (fun _ : PUnit => eSec G) (fun _ => 1) L.rig H.hom)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hσ (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ L.rigGen _)))
  have R : RigMul L i τ σ := fun T z J hJ t => by
    rw [hv _ _ z J hJ, val_mul hJ, val_inv, val_rigPull hJ t, inv_mul_cancel_right]; rfl
  exact ⟨τ, ⟨hτ, R⟩, fun τ' h => gen_eq_of_val L.isLB h.1 hτ fun y J hJ =>
    mul_right_cancel ((h.2 H y J hJ (𝟙 H)).symm.trans (R H y J hJ (𝟙 H)))⟩

theorem thirdDiff_iff {A U : Type} [CommGroup A] [CommGroup U] {σ τ : A → U} {ρ C : U} (h : ∀ a, σ a = τ a * ρ)
    (h₁ : τ 1 = 1) {x y u : A} :
    τ (x * y * u) * τ x * τ y * τ u = C * τ (x * y) * τ (x * u) * τ (y * u) ↔ thirdDiff σ x y u = C := by
  simp only [thirdDiff, h, h₁]
  constructor <;> intro e <;> apply Additive.ofMul.injective <;> have e' := congrArg Additive.ofMul e <;>
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at e' ⊢ <;> linear_combination (norm := abel) e'

variable {c : CubicalStr G L} [IsMonHom i]

theorem isCubTriv_iff {τ : LB.Gen (LB.LinComb L.L (K := Fin 2) ![i.left, (1 : H ⟶ G).left] ![1, -1])}
    {σ : LB.Gen (L.L.pull i.left)} (hσ : σ.IsGen) (hτ : τ.IsGen) (R : RigMul L i τ σ) :
    (∃ a : CubTriv c i, a.s = τ) ↔ IsCubTriv c i σ := by
  constructor
  · rintro ⟨a, rfl⟩
    exact ⟨hσ, fun T z J hJ => by rw [R T z J hJ, a.val_one hJ, _root_.one_mul], fun T z J hJ t t' t'' =>
      (thirdDiff_iff (τ := fun t : T ⟶ H => val a.s t.left z J) (R T z J hJ) (a.val_one hJ)).1 (a.cub T t t' t'' z J hJ)⟩
  · intro h
    refine ⟨⟨τ, hτ, fun T x y u z J hJ => ?_⟩, rfl⟩
    have e : val τ (1 : T ⟶ H).left z J = 1 := mul_eq_right.1 ((R T z J hJ 1).symm.trans (h.rig T z J hJ))
    exact (thirdDiff_iff (τ := fun t : T ⟶ H => val τ t.left z J) (R T z J hJ) e).2 (h.cub T z J hJ x y u)

omit [IsCommMonObj H] [IsMonHom i] in
theorem cubTriv_ext {a b : CubTriv c i} (h : a.s = b.s) : a = b := by
  cases a; cases b; cases h; rfl

def cubTrivEquiv (c : CubicalStr G L) (i : H ⟶ G) [IsMonHom i] :
    CubTriv c i ≃ {σ : LB.Gen (L.L.pull i.left) // IsCubTriv c i σ} :=
  Equiv.ofBijective (fun a => ⟨(existsUnique_rigMul_right a.s a.gen).exists.choose,
      (isCubTriv_iff (existsUnique_rigMul_right a.s a.gen).exists.choose_spec.1 a.gen
        (existsUnique_rigMul_right a.s a.gen).exists.choose_spec.2).1 ⟨a, rfl⟩⟩)
    ⟨fun a b e => by
      have ha := (existsUnique_rigMul_right a.s a.gen).exists.choose_spec
      have hb := (existsUnique_rigMul_right b.s b.gen).exists.choose_spec
      have e' : (existsUnique_rigMul_right a.s a.gen).exists.choose =
        (existsUnique_rigMul_right b.s b.gen).exists.choose := Subtype.ext_iff.1 e
      rw [e'] at ha
      exact cubTriv_ext ((existsUnique_rigMul_left _ hb.1).unique ⟨a.gen, ha.2⟩ ⟨b.gen, hb.2⟩),
    fun σ => by
      obtain ⟨τ, hτ, R⟩ := (existsUnique_rigMul_left σ.1 σ.2.gen).exists
      obtain ⟨a, rfl⟩ := (isCubTriv_iff (c := c) σ.2.gen hτ R).2 σ.2
      exact ⟨a, Subtype.ext ((existsUnique_rigMul_right a.s a.gen).unique
        (existsUnique_rigMul_right a.s a.gen).exists.choose_spec ⟨σ.2.gen, R⟩)⟩⟩

theorem rigMul_cubTrivEquiv (a : CubTriv c i) : RigMul L i a.s (cubTrivEquiv c i a).1 :=
  (existsUnique_rigMul_right a.s a.gen).exists.choose_spec.2

theorem even_iff {P : CP G} (a : CubTriv P.c i) {σ} (R : RigMul P.L i a.s σ) : a.Even ↔ IsEven (toCubSym P) i σ := by
  refine forall_congr' fun T => ⟨fun h z J hJ t => ?_, fun h t z J hJ => ?_⟩
  · refine (R T z J hJ _).trans (Eq.trans ?_ (congrArg _ (R T z J hJ _).symm))
    rw [h t z J hJ, _root_.mul_assoc]; rfl
  · have e := ((R T z J hJ _).symm.trans (h z J hJ t)).trans (congrArg _ (R T z J hJ _))
    exact mul_right_cancel (e.trans (_root_.mul_assoc _ _ _).symm)

theorem cubWeil_iff (c : CubicalStr G L) (N : ℕ) {T : Over S} (x y : T ⟶ G) (ζ : Γ(T.left, ⊤)ˣ) :
    CubWeil c N x y ζ ↔ IsPairing c N x y ζ := cubWeil_iff_isRatio

end Triv

section Wt
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem gs_appLE {Y Z : Scheme.{0}} (r : Z ⟶ Y) (V : Y.Opens) (h : ⊤ ≤ r ⁻¹ᵁ V) (u : Γ(Y, V)) (z : Z) :
    gs (𝟙 Z) z ⊤ ((r.appLE V ⊤ h).hom u) = gs r z V u :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) r z V (h trivial) u).trans (by rw [Category.id_comp]))

theorem gs_comp {Y Z Z' : Scheme.{0}} (ρ : Z' ⟶ Z) (r : Z ⟶ Y) (V : Y.Opens) (z : Z') (h : r (ρ z) ∈ V) (u : Γ(Y, V)) :
    gs (ρ ≫ r) z V u = (ρ.stalkMap z).hom (gs r (ρ z) V u) := by
  rw [gs_eq (ρ ≫ r) z V h, gs_eq r _ V h]
  exact (Scheme.Hom.germ_stalkMap_apply ρ (r ⁻¹ᵁ V) z h _).symm

theorem isWt_iff_germ (i : splitTorus S X ⟶ G) (V : G.left.Opens) (u : Γ(G.left, V)) (χ : X) :
    IsWt i V u χ ↔ ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G), x.left z ∈ V →
      ((t ≫ i) * x).left z ∈ V → gs ((t ≫ i) * x).left z V u = (charV χ z t).val * gs x.left z V u := by
  have key : ∀ (Z : Over S) (t : Z ⟶ splitTorus S X) (g : Z ⟶ G) (h₂ : ⊤ ≤ g.left ⁻¹ᵁ V) (z : Z.left),
      gs (𝟙 Z.left) z ⊤ (t.left.appTop.hom (charUnit S X χ).val * (g.left.appLE _ ⊤ h₂).hom u) =
        (charV χ z t).val * gs g.left z V u := fun Z t g h₂ z => by
    rw [gs_mul _ z ⊤ trivial, gs_appLE, ← chV_val, gs_unit _ z ⊤ trivial, charV, gm_charUnit]
  constructor
  · intro h T z t x hx hx'
    let O : T.left.Opens := x.left ⁻¹ᵁ V ⊓ ((t ≫ i) * x).left ⁻¹ᵁ V
    let ρ : Over.mk (O.ι ≫ T.hom) ⟶ T := Over.homMk O.ι rfl
    have e : ((ρ ≫ t) ≫ i) * (ρ ≫ x) = ρ ≫ ((t ≫ i) * x) := by rw [MonObj.comp_mul, Category.assoc]
    have h₁ : ⊤ ≤ (((ρ ≫ t) ≫ i) * (ρ ≫ x)).left ⁻¹ᵁ V := by rw [e]; exact fun y _ => y.2.2
    have h₂ : ⊤ ≤ (ρ ≫ x).left ⁻¹ᵁ V := fun y _ => y.2.1
    have a := congrArg (gs (𝟙 _) (⟨z, hx, hx'⟩ : O) ⊤) (h _ (ρ ≫ t) (ρ ≫ x) h₁ h₂)
    erw [key, gs_appLE] at a
    rw [e] at a
    unfold charV at a
    erw [← gs_unit _ _ ⊤ trivial] at a
    have inj : ∀ y : O.toScheme, Function.Injective (O.ι.stalkMap y).hom := fun y =>
      (ConcreteCategory.bijective_of_isIso _).1
    apply inj ⟨z, hx, hx'⟩
    rw [charV, ← gs_unit _ _ ⊤ trivial]
    exact ((gs_comp O.ι _ V ⟨z, hx, hx'⟩ hx' u).symm.trans a).trans ((congrArg₂ (· * ·)
      (gs_comp O.ι t.left ⊤ ⟨z, hx, hx'⟩ trivial _) (gs_comp O.ι x.left V ⟨z, hx, hx'⟩ hx u)).trans (map_mul _ _ _).symm)
  · intro h Z t g h₁ h₂
    refine fn_ext fun z _ => ?_
    rw [key, gs_appLE]
    exact h Z z t g (h₂ trivial) (h₁ trivial)

theorem isWeight_iff (i : splitTorus S X ⟶ G) (χ : X) (V : G.left.Opens) (u : Γ(G.left, V)) :
    IsWeight i χ V u ↔ IsStable i V ∧ IsWt i V u χ :=
  and_congr_right fun hV => ((isWt_iff_germ i V u χ).trans ⟨fun h T z t x hx => h T z t x hx (hV T z t x hx),
    fun h T z t x hx _ => h T z t x hx⟩).symm

end Wt

section Ext
variable {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

theorem act_comp {H B Z : Over S} [GrpObj B] {i : H ⟶ G} {q : G ⟶ B} [IsMonHom q] (w : i ≫ q = toUnit _ ≫ η[B])
    (t : Z ⟶ H) (g : Z ⟶ G) : ((t ≫ i) * g) ≫ q = g ≫ q := by
  rw [MonObj.mul_comp, Category.assoc, w, ← Category.assoc, comp_toUnit, ← Hom.one_def, _root_.one_mul]

theorem genWt_iff (Q : TQ G X) {N : LB Q.B.left} (hN : N.IsLB) (u : LB.Gen (N.pull Q.q.left)) (χ : X) :
    Q.GenWt N u χ ↔ IsWeightGen Q.i χ N (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) u := by
  have := Q.q_hom
  have e : ∀ (T : Over S) (t : T ⟶ splitTorus S X) (x : T ⟶ G),
      ((t ≫ Q.i) * x).left ≫ Q.q.left = x.left ≫ Q.q.left := fun T t x =>
    congrArg (fun q => q.left) (act_comp Q.isKernel.w t x)
  have key : ∀ (T : Over S) (z : T.left) (t : T ⟶ splitTorus S X) (x : T ⟶ G) (J) (j : PUnit → N.ι),
      J (x.left ≫ Q.q.left) = j PUnit.unit → x.left z ∈ (N.pull Q.q.left).U j →
      ((t ≫ Q.i) * x).left z ∈ (N.pull Q.q.left).U j →
      (val u ((t ≫ Q.i) * x).left z J = charV χ z t * val u x.left z J ↔
        gs ((t ≫ Q.i) * x).left z _ (u.s j).val = (charV χ z t).val * gs x.left z _ (u.s j).val) := by
    intro T z t x J j hj h h'
    rw [val_of u _ z J j (fun _ => by rw [e]; exact hj), val_of u x.left z J j (fun _ => hj), gs_unit _ z _ h',
      gs_unit _ z _ h, ← Units.val_mul, Units.val_inj]
    rfl
  constructor
  · rintro ⟨hu, h⟩
    refine ⟨hu, fun _ => e, fun T z J hJ t x => ?_⟩
    have m : x.left z ∈ (N.pull Q.q.left).U (fun _ => J (x.left ≫ Q.q.left)) := mem_pull.2 (hJ _)
    have m' : ((t ≫ Q.i) * x).left z ∈ (N.pull Q.q.left).U (fun _ => J (x.left ≫ Q.q.left)) := by
      rw [← e T t x]; exact mem_pull.2 (hJ _)
    exact (key T z t x J _ rfl m m').2 ((isWt_iff_germ _ _ _ _).1 (h _) T z t x m m')
  · intro h
    refine ⟨h.gen, fun j => (isWt_iff_germ _ _ _ _).2 fun T z t x m m' => ?_⟩
    obtain ⟨J, hJ, hj⟩ := exists_good N hN z (K := PUnit) (fun _ => x.left ≫ Q.q.left) j (fun _ _ _ => rfl)
      (fun _ => (mem_pull (F := Q.q.left)).1 m)
    exact (key T z t x J j (hj _) m m').1 (h.weight T z J hJ t x)

theorem charV_neg (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : charV (-χ) z t = (charV χ z t)⁻¹ := by
  have n : chV t (-χ) = (chV t χ)⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← chV_add, neg_add_cancel, chV_zero])
  rw [charV, charV, gm_charUnit, gm_charUnit, n, map_inv]

theorem isWeightGen_inv {i : splitTorus S X ⟶ G} {χ : X} {Y : Scheme.{0}} {M : LB Y} {K : Type} [Fintype K]
    {φ : K → (G.left ⟶ Y)} {ε : K → ℤ} {u : LB.Gen (LB.LinComb M φ ε)} (h : IsWeightGen i χ M φ ε u) :
    IsWeightGen i (-χ) M φ (fun k => -ε k) (LB.invGen M φ ε u) :=
  ⟨DVR.invGen_isGen _ _ _ _ h.gen, h.invariant, fun T z J hJ t x => by
    rw [val_inv, val_inv, h.weight T z J hJ, charV_neg, mul_inv]⟩

theorem isWeightBundle_iff (Q : TQ G X) (χ : X) (N : LB Q.B.left) :
    IsWeightBundle Q.i Q.q χ N ↔ N.IsLB ∧ ∃ u, Q.GenWt N u (-χ) :=
  and_congr_right fun hN => ⟨fun ⟨_, h⟩ => ⟨_, (genWt_iff Q hN _ _).2 (isWeightGen_inv h)⟩,
    fun ⟨_, h⟩ => ⟨_, neg_neg χ ▸ isWeightGen_inv ((genWt_iff Q hN _ _).1 h)⟩⟩

theorem isTorusExt_of_tq [Module.Free ℤ X] [Module.Finite ℤ X] [IsCommMonObj G] (Q : TQ G X) : IsTorusExt Q.i Q.q where
  free := inferInstance
  finite := inferInstance
  comm := inferInstance
  abelian := Q.isAb
  i_hom := Q.i_hom
  q_hom := Q.q_hom
  isKernel := Q.isKernel
  locTriv b := by
    obtain ⟨V, hV, hb, s, hs⟩ := Q.exists_local_section b
    exact ⟨V, hb, hV.isoSpec.hom ≫ s, by rw [Category.assoc, hs, IsAffineOpen.isoSpec_hom_fromSpec]⟩

variable {B : Over S} [GrpObj B]

theorem isPullback_of_section {H V : Over S} {i : H ⟶ G} {q : G ⟶ B} [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η[B])) {j : V ⟶ B} {r : V ⟶ G} (hr : r ≫ q = j) :
    IsPullback ((fst H V ≫ i) * (snd H V ≫ r)) (snd H V) q j := by
  have w : ∀ s : PullbackCone q j, (s.fst * (s.snd ≫ r)⁻¹) ≫ q = toUnit _ ≫ η[B] := fun s => by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hr, s.condition, mul_inv_cancel]; rfl
  refine ⟨⟨by rw [act_comp hk.w, Category.assoc, hr]⟩, ⟨PullbackCone.IsLimit.mk _
    (fun s => lift (hk.lift _ _ (w s)) s.snd) (fun s => ?_) (fun s => lift_snd _ _) fun s m h₁ h₂ => ?_⟩⟩
  · rw [MonObj.comp_mul, lift_fst_assoc, lift_snd_assoc, hk.lift_fst, inv_mul_cancel_right]
  · ext1
    · refine hk.hom_ext ?_ (toUnit_unique _ _)
      rw [lift_fst, hk.lift_fst, ← h₁, ← h₂, MonObj.comp_mul]
      simp only [Category.assoc, mul_inv_cancel_right]
    · rw [lift_snd, h₂]

theorem prop_of_isTorusExt {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsTorusExt i q) (P : MorphismProperty Scheme.{0})
    [IsZariskiLocalAtTarget P] [P.IsStableUnderBaseChange] (hP : P (splitTorus S X).hom) : P q.left := by
  have := h.q_hom
  choose V hV r hr using h.locTriv
  refine IsZariskiLocalAtTarget.of_iSup_eq_top V (top_le_iff.1 fun b _ =>
    TopologicalSpace.Opens.mem_iSup.2 ⟨b, hV b⟩) fun b => ?_
  let W : Over S := Over.mk ((V b).ι ≫ B.hom)
  let j : W ⟶ B := Over.homMk (V b).ι rfl
  let r' : W ⟶ G := Over.homMk (r b) (by rw [← Over.w q, ← Category.assoc, hr]; rfl)
  have p := (isPullback_of_section h.isKernel (j := j) (r := r') (Over.OverMorphism.ext (hr b))).map (Over.forget S)
  have p' := (isPullback_morphismRestrict q.left (V b)).flip
  have e := IsPullback.isoIsPullback_hom_snd _ _ p' p
  rw [← e]
  exact (P.cancel_left_of_respectsIso _ _).2 (P.of_isPullback (IsPullback.of_hasPullback (splitTorus S X).hom W.hom) hP)

theorem appLE_topIso {Y Z : Scheme.{0}} (U : Y.Opens) (g : Z ⟶ U) (h : ⊤ ≤ (g ≫ U.ι) ⁻¹ᵁ U) (a : Γ(U, ⊤)) :
    ((g ≫ U.ι).appLE U ⊤ h).hom (U.topIso.hom.hom a) = g.appTop.hom a := by
  have e : U.topIso.hom ≫ (g ≫ U.ι).appLE U ⊤ h = g.appTop := by
    rw [← Scheme.Hom.appLE_comp_appLE g U.ι U ⊤ ⊤ (by simp) le_top, ← Category.assoc]
    have : U.topIso.hom ≫ U.ι.appLE U ⊤ (by simp) = 𝟙 _ := by
      simp only [Scheme.Opens.topIso_hom, Scheme.Opens.ι_appLE]
      exact (Y.presheaf.map_comp _ _).symm.trans (Y.presheaf.map_id _)
    rw [this, Category.id_comp, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl
  exact congrArg (fun q => q.hom a) e

theorem loc_of_isTorusExt {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsTorusExt i q) (b : B.left) (χ : X) :
    ∃ V : B.left.Opens, b ∈ V ∧ ∃ u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ, IsWt i _ u.val χ := by
  have := h.q_hom
  have := h.i_hom
  obtain ⟨V, hb, r, hr⟩ := h.locTriv b
  let W : Over S := Over.mk (V.ι ≫ B.hom)
  let j : W ⟶ B := Over.homMk V.ι rfl
  let r' : W ⟶ G := Over.homMk r (by rw [← Over.w q, ← Category.assoc, hr]; rfl)
  have hr' : r' ≫ q = j := Over.OverMorphism.ext hr
  let U : Over S := Over.mk ((q.left ⁻¹ᵁ V).ι ≫ G.hom)
  let k : U ⟶ G := Over.homMk (q.left ⁻¹ᵁ V).ι rfl
  let q' : U ⟶ W := Over.homMk (q.left ∣_ V) (by
    show _ ≫ V.ι ≫ B.hom = _ ≫ G.hom
    rw [← Over.w q, morphismRestrict_ι_assoc])
  have hq' : q' ≫ j = k ≫ q := Over.OverMorphism.ext (morphismRestrict_ι _ _)
  have w : (k * (q' ≫ r')⁻¹) ≫ q = toUnit _ ≫ η[B] := by
    rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, hr', hq', mul_inv_cancel]; rfl
  let p : U ⟶ splitTorus S X := h.isKernel.lift _ _ w
  have hp : p ≫ i = k * (q' ≫ r')⁻¹ := h.isKernel.lift_fst _ _ _
  have lf : ∀ {Z : Over S} (g : Z ⟶ G), ⊤ ≤ g.left ⁻¹ᵁ (q.left ⁻¹ᵁ V) → ∃ g' : Z ⟶ U, g' ≫ k = g := fun g hg => by
    have hs : Set.range g.left ⊆ Set.range (q.left ⁻¹ᵁ V).ι := by
      rw [Scheme.Opens.range_ι]; rintro _ ⟨y, rfl⟩; exact hg trivial
    have e := IsOpenImmersion.lift_fac (q.left ⁻¹ᵁ V).ι g.left hs
    exact ⟨Over.homMk (IsOpenImmersion.lift _ _ hs) ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ G.hom) e).trans (Over.w g))), Over.OverMorphism.ext e⟩
  refine ⟨V, hb, Units.map (q.left ⁻¹ᵁ V).topIso.hom.hom.toMonoidHom (chV p χ), fun Z t g h₁ h₂ => ?_⟩
  have ev : ∀ (a : Z ⟶ G) (a' : Z ⟶ U) (_ : a' ≫ k = a) (ha : ⊤ ≤ a.left ⁻¹ᵁ (q.left ⁻¹ᵁ V)),
      (a.left.appLE _ ⊤ ha).hom (Units.map (q.left ⁻¹ᵁ V).topIso.hom.hom.toMonoidHom (chV p χ)).val =
        (chV (a' ≫ p) χ).val := by
    rintro _ a' rfl ha
    refine (appLE_topIso (q.left ⁻¹ᵁ V) a'.left ha _).trans ?_
    rw [chV_val, chV_val, Rosenlicht.over_appTop_comp]
  obtain ⟨g', hg⟩ := lf g h₂
  obtain ⟨g₁, hg₁⟩ := lf _ h₁
  have e : g₁ ≫ q' = g' ≫ q' := Over.OverMorphism.ext ((cancel_mono V.ι).1 (congrArg (fun q => q.left)
    (show (g₁ ≫ q') ≫ j = (g' ≫ q') ≫ j by
      rw [Category.assoc, Category.assoc, hq', ← Category.assoc, ← Category.assoc, hg, hg₁, act_comp h.isKernel.w])))
  have e' : g₁ ≫ p = t * (g' ≫ p) := h.isKernel.hom_ext (by
    rw [MonObj.mul_comp, Category.assoc, Category.assoc, hp, MonObj.comp_mul, MonObj.comp_mul, GrpObj.comp_inv,
      GrpObj.comp_inv, ← Category.assoc, ← Category.assoc, e, hg, hg₁, _root_.mul_assoc]) (toUnit_unique _ _)
  rw [ev _ g₁ hg₁, ev _ g' hg, e', chV_mul, Units.val_mul, chV_val]

set_option backward.isDefEq.respectTransparency.types false in

theorem isAffineHom_localAtTarget : IsZariskiLocalAtTarget @IsAffineHom.{0} :=
  HasAffineProperty.instIsZariskiLocalAtTarget (P := @IsAffineHom.{0})

def toTQ {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsTorusExt i q) : TQ G X where
  B := B
  comm := h.abelian.comm
  isAb := h.abelian
  q := q
  i := i
  q_hom := h.q_hom
  i_hom := h.i_hom
  q_flat := have := HasRingHomProperty.instIsZariskiLocalAtTarget (P := @Flat)
    prop_of_isTorusExt h @Flat (Diag.flat_hom S X)
  q_surj := prop_of_isTorusExt h @Surjective (Diag.surjective_hom S X)
  q_affine := by
    have := isAffineHom_localAtTarget
    have := isAffineHom_isStableUnderBaseChange
    exact prop_of_isTorusExt h @IsAffineHom (Diag.isAffineHom_hom S X)
  isKernel := h.isKernel
  loc := loc_of_isTorusExt h

def tqEquiv (G : Over S) [GrpObj G] [IsCommMonObj G] (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    TQ G X ≃ {d : Σ (B : Over S) (_ : GrpObj B), (splitTorus S X ⟶ G) × (G ⟶ B) //
      letI := d.2.1; IsTorusExt d.2.2.1 d.2.2.2} where
  toFun Q := ⟨⟨Q.B, Q.grp, Q.i, Q.q⟩, isTorusExt_of_tq Q⟩
  invFun d := letI := d.1.2.1; toTQ d.2
  left_inv _ := rfl
  right_inv _ := rfl

theorem isLocalWeightGen_iff {i : splitTorus S X ⟶ G} {q : G ⟶ B} (h : IsTorusExt i q) (χ : X) (V : B.left.Opens)
    (u : Γ(G.left, q.left ⁻¹ᵁ V)ˣ) : IsLocalWeightGen i q χ V u ↔ IsWt i _ u.val χ :=
  (isWeight_iff i χ _ u.val).trans (and_iff_right (h.isStable V))

end Ext

section Desc
variable {G H B : Over S} [GrpObj G] [IsCommMonObj G] [GrpObj H] [IsCommMonObj H] [GrpObj B] [IsCommMonObj B]
  {i : H ⟶ G} [IsMonHom i] {q : G ⟶ B} [IsMonHom q] {P : CP G} {M : CP B} {w : LB.Iso P.L.L (M.L.L.pull q.left)}

theorem isCPMap_iff_ofHom (hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S) :
    IsCPMap P M (𝟙 S) q.left hq w ↔ IsCubSymIso (CubeMap.ofHom q) (toCubSym P) (toCubSym M) w :=
  isCPMap_iff (CubeMap.ofHom q) P M w

omit [IsMonHom i] [IsMonHom q] [IsCommMonObj H] in

theorem vals_ker {hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S} (h : IsCPMap P M (𝟙 S) q.left hq w) (hk : i ≫ q = 1)
    {T : Over S} {z : T.left} {J I} (hJ : Good P.L.L z J) (hI : Good M.L.L z I)
    (W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ) (hW : ∀ x, W x = gw w x.left z (I (x.left ≫ q.left)) (J x.left)) :
    val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig T.hom z I = W 1 * rigV P.L z J ∧
      (∀ t : T ⟶ H, W (t ≫ i) = W (t ≫ i)⁻¹ * symV P.sym z J (t ≫ i)) ∧
      ∀ (t : T ⟶ H) (x y : T ⟶ G), W ((t ≫ i) * x) * W ((t ≫ i) * y) * W (x * y) * W 1 =
        W ((t ≫ i) * x * y) * W (t ≫ i) * W x * W y * cubV P.c z J (t ≫ i) x y := by
  obtain ⟨a, b, c⟩ := h.vals T z J I hJ hI W hW
  have e : ∀ t : T ⟶ H, (t ≫ i).left ≫ q.left = (1 : T ⟶ B).left := fun t => by
    rw [← Over.comp_left, Category.assoc, hk, MonObj.comp_one]
  refine ⟨?_, fun t => ?_, fun t x y => ?_⟩
  · rw [Category.comp_id] at a
    rw [a, rigV, Rosenlicht.toUnit_left]
  · have := b (t ≫ i)
    rw [e, M.val_sym_one hI, _root_.one_mul] at this
    exact this
  · have := c (t ≫ i) x y
    have o : toBase hq (t ≫ i) = 1 := Over.OverMorphism.ext ((e t).trans ((one_left B T).trans
      ((congrArg (· ≫ eSec B) (Category.comp_id T.hom).symm).trans (one_left B (Over.mk (T.hom ≫ 𝟙 S))).symm)))
    rw [o, _root_.id, (isCub_cubV M.c (T := Over.mk (T.hom ≫ 𝟙 S)) hI).face, _root_.one_mul] at this
    exact this

omit [IsMonHom i] [IsCommMonObj H] in

theorem exists_gens (hw : w.IsGen) (hk : i ≫ q = 1) : ∃ (s : LB.Gen (lamOn i P.L.L)) (σ : LB.Gen (P.L.L.pull i.left)),
    s.IsGen ∧ σ.IsGen ∧ ∀ (T : Over S) (z : T.left) (J I), Good P.L.L z J → Good M.L.L z I →
      ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (I (x.left ≫ q.left)) (J x.left)) →
      (∀ t : T ⟶ H, val (L := M.L.L) (φ := fun _ : PUnit => eSec B) (ε := fun _ => 1) M.L.rig T.hom z I =
        W (t ≫ i) * trivV σ z J t) ∧
      ∀ (t : T ⟶ H) (x : T ⟶ G), 1 = W ((t ≫ i) * x) * (W (t ≫ i))⁻¹ * (W x)⁻¹ * W 1 * lamV s z J t x := by
  have hp := (isGen_iff w).1 hw
  have c₁ : i.left ≫ q.left = H.hom ≫ eSec B := by rw [← Over.comp_left, hk, one_left]
  obtain ⟨σ, hσ, Hσ⟩ := CubTransport.exists_pmaps hp M.L.isLB P.L.isLB (φ' := fun _ : PUnit => i.left)
    (φ := fun _ => eSec B) (ε := fun _ => 1) H.hom (fun _ => c₁) M.L.rig M.L.rigGen
  let ψ : Fin 4 → (B ⟶ B) := ![𝟙 B, 1, 𝟙 B, 1]
  have c₂ : ∀ k, lamφ i k ≫ q.left = (snd H G ≫ q).left ≫ (ψ k).left := fun k => by
    have o : (fst H G ≫ i) ≫ q = 1 := by rw [Category.assoc, hk, MonObj.comp_one]
    fin_cases k
    · exact congrArg (fun a => a.left) (show ((fst H G ≫ i) * snd H G) ≫ q = (snd H G ≫ q) ≫ 𝟙 B by
        rw [MonObj.mul_comp, o, _root_.one_mul, Category.comp_id])
    · exact congrArg (fun a => a.left) (show (fst H G ≫ i) ≫ q = (snd H G ≫ q) ≫ 1 by rw [o, MonObj.comp_one])
    · exact congrArg (fun a => a.left) (Category.comp_id (snd H G ≫ q)).symm
    · exact congrArg (fun a => a.left) (show (1 : H ⊗ G ⟶ G) ≫ q = (snd H G ≫ q) ≫ 1 by
        rw [MonObj.one_comp, MonObj.comp_one])
  obtain ⟨u, hu, vu⟩ := exists_gen M.L.isLB (φ' := fun k => (ψ k).left) (ε' := Oε)
    (fun U _ h => by simp [Fin.prod_univ_succ, ψ, Oε]) (LB.oneGen M.L.L (Y := B.left))
    (fun _ _ => (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm)
  obtain ⟨s, hs, Hs⟩ := CubTransport.exists_pmaps hp M.L.isLB P.L.isLB (φ' := lamφ i) (ε := Oε) _ c₂ u hu
  refine ⟨s, σ, hs, hσ, fun T z J I hJ hI W hW => ⟨fun t => ?_, fun t x => ?_⟩⟩
  · have e := CubTransport.val_pmaps (fun _ => c₁) Hσ t.left hI hJ
    rw [Fintype.prod_unique, zpow_one, Over.w] at e
    rw [hW]; exact e
  · have e := CubTransport.val_pmaps c₂ Hs (lift t x).left hI hJ
    rw [vu _ _ z I hI, val_one, Fin.prod_univ_four] at e
    have a₀ : (lift t x).left ≫ lamφ i 0 = ((t ≫ i) * x).left := congrArg (fun a => a.left)
      (show lift t x ≫ ((fst H G ≫ i) * snd H G) = _ by rw [MonObj.comp_mul, lift_fst_assoc, lift_snd])
    have a₁ : (lift t x).left ≫ lamφ i 1 = (t ≫ i).left := congrArg (fun a => a.left) (lift_fst_assoc t x i)
    have a₂ : (lift t x).left ≫ lamφ i 2 = x.left := congrArg (fun a => a.left) (lift_snd t x)
    have a₃ : (lift t x).left ≫ lamφ i 3 = (1 : T ⟶ G).left := congrArg (fun a : T ⟶ G => a.left) (MonObj.comp_one (lift t x))
    rw [a₀, a₁, a₂, a₃, ← hW, ← hW, ← hW, ← hW] at e
    have n : ∀ a : (T.left.presheaf.stalk z)ˣ, a ^ Oε 0 = a ∧ a ^ Oε 1 = a⁻¹ ∧ a ^ Oε 2 = a⁻¹ ∧ a ^ Oε 3 = a :=
      fun a => ⟨zpow_one a, zpow_neg_one a, zpow_neg_one a, zpow_one a⟩
    rw [(n _).1, (n _).2.1, (n _).2.2.1, (n _).2.2.2] at e
    exact e

local macro "grp_comb " e:term : tactic => `(tactic| (
  have hcomb := congrArg Additive.ofMul $e
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at hcomb ⊢
  linear_combination (norm := abel) hcomb))

theorem exists_descent {hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S} (h : IsCPMap P M (𝟙 S) q.left hq w) (hk : i ≫ q = 1) :
    ∃ s σ, IsBiextTriv P.c i s ∧ IsCubTriv P.c i σ ∧ IsEven (toCubSym P) i σ ∧ Induces i σ s ∧
      IsCubSymDescent (toCubSym P) i s σ q (toCubSym M) w := by
  obtain ⟨s, σ, hs, hσ, H⟩ := exists_gens (i := i) h.gen hk
  have key : ∀ (T : Over S) (z : T.left) (J I), Good P.L.L z J → Good M.L.L z I →
      ∀ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ, (∀ x, W x = gw w x.left z (I (x.left ≫ q.left)) (J x.left)) →
      (∀ t, trivV σ z J t = (W (t ≫ i))⁻¹ * W 1 * rigV P.L z J) ∧
      (∀ t x, lamV s z J t x = (W ((t ≫ i) * x))⁻¹ * W (t ≫ i) * W x * (W 1)⁻¹) ∧
      (∀ t, symV P.sym z J (t ≫ i) = (W (t ≫ i)⁻¹)⁻¹ * W (t ≫ i)) ∧
      ∀ t x y, cubV P.c z J (t ≫ i) x y = W ((t ≫ i) * x) * W ((t ≫ i) * y) * W (x * y) * W 1 *
        (W ((t ≫ i) * x * y) * W (t ≫ i) * W x * W y)⁻¹ := fun T z J I hJ hI W hW => by
    obtain ⟨a, b⟩ := H T z J I hJ hI W hW
    obtain ⟨c, d, e⟩ := vals_ker h hk hJ hI W hW
    exact ⟨fun t => by grp_comb ((a t).symm.trans c), fun t x => by grp_comb (b t x).symm,
      fun t => by grp_comb (d t).symm, fun t x y => by grp_comb (e t x y).symm⟩
  have key' : ∀ (T : Over S) (z : T.left) (J), Good P.L.L z J → ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      (∀ t, trivV σ z J t = (W (t ≫ i))⁻¹ * W 1 * rigV P.L z J) ∧
      (∀ t x, lamV s z J t x = (W ((t ≫ i) * x))⁻¹ * W (t ≫ i) * W x * (W 1)⁻¹) ∧
      (∀ t, symV P.sym z J (t ≫ i) = (W (t ≫ i)⁻¹)⁻¹ * W (t ≫ i)) ∧
      ∀ t x y, cubV P.c z J (t ≫ i) x y = W ((t ≫ i) * x) * W ((t ≫ i) * y) * W (x * y) * W 1 *
        (W ((t ≫ i) * x * y) * W (t ≫ i) * W x * W y)⁻¹ := fun T z J hJ => by
    obtain ⟨I, hI⟩ := exists_good_pt M.L.isLB z
    exact ⟨_, key T z J I hJ hI _ fun _ => rfl⟩
  have iso := (isCPMap_iff_ofHom hq).1 h
  refine ⟨s, σ, ⟨hs, fun T z J hJ t t' x => ?_, fun T z J hJ t x x' => ?_⟩,
    ⟨hσ, fun T z J hJ => ?_, fun T z J hJ t t' t'' => ?_⟩, fun T z J hJ t => ?_, fun T z J hJ t t' => ?_,
    ⟨iso.toIsRigIso, hk, fun T z J I hJ hI t x => ?_⟩, iso⟩
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    simp only [b, d, MonObj.mul_comp]
    grp_comb (rfl : W 1 = W 1)
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    simp only [b, d, ← _root_.mul_assoc]
    grp_comb (rfl : W 1 = W 1)
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    rw [a, MonObj.one_comp, inv_mul_cancel, _root_.one_mul]
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    simp only [thirdDiff, a, d, MonObj.mul_comp, MonObj.one_comp]
    grp_comb (rfl : W 1 = W 1)
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    refine (a _).trans (Eq.trans ?_ (congrArg₂ (· * ·) (c t) (a t)).symm)
    rw [GrpObj.inv_comp]
    grp_comb (rfl : W 1 = W 1)
  · obtain ⟨W, a, b, c, d⟩ := key' T z J hJ
    simp only [a, b, MonObj.mul_comp, MonObj.one_comp]
    grp_comb (rfl : W 1 = W 1)
  · obtain ⟨W, hW⟩ : ∃ W : (T ⟶ G) → (T.left.presheaf.stalk z)ˣ,
      ∀ x, W x = gw w x.left z (I (x.left ≫ q.left)) (J x.left) := ⟨_, fun _ => rfl⟩
    obtain ⟨a, b, -⟩ := key T z J I hJ hI W hW
    refine (congrArg₂ (· * ·) (hW _).symm (congrArg₂ (· * ·) (congrArg₂ (· * ·) (b t x) (a t)) rfl)).trans
      (Eq.trans ?_ (hW x))
    show _ * (_ * (rigV P.L z J)⁻¹) = _
    grp_comb (rfl : W 1 = W 1)

theorem descent_unique {L : RigLB G} {c : CubicalStr G L} {N : RigLB B}
    {v : LB.Iso L.L (N.L.pull (CubeMap.ofHom q).F)} {s s' : LB.Gen (lamOn i L.L)} {σ σ' : LB.Gen (L.L.pull i.left)}
    (hs : IsBiextTriv c i s) (hs' : IsBiextTriv c i s') (hσ : σ.IsGen) (hσ' : σ'.IsGen)
    (h : IsDescent L i s σ q N v) (h' : IsDescent L i s' σ' q N v) : s = s' ∧ σ = σ' := by
  have e : ∀ (T : Over S) (z : T.left) (J), Good L.L z J → ∀ t x,
      lamV s z J t x * trivV σ z J t = lamV s' z J t x * trivV σ' z J t := fun T z J hJ t x => by
    obtain ⟨I, hI⟩ := exists_good_pt N.isLB z
    exact mul_right_cancel (mul_left_cancel
      ((h.equivariant T z J I hJ hI t x).trans (h'.equivariant T z J I hJ hI t x).symm))
  obtain rfl : σ = σ' := gen_eq_of_val L.isLB hσ hσ' fun y J hJ => by
    have := e H y J hJ (𝟙 H) 1
    rw [(hs.axes (T := H) hJ (𝟙 H) 1).2, (hs'.axes (T := H) hJ (𝟙 H) 1).2] at this
    exact mul_left_cancel this
  refine ⟨gen_eq_of_val L.isLB hs.gen hs'.gen fun y J hJ => ?_, rfl⟩
  have := mul_right_cancel (e (H ⊗ G) y J hJ (fst H G) (snd H G))
  rwa [lamV, lamV, lift_fst_snd] at this

theorem isCPMap_iff_descent (hq : q.left ≫ B.hom = G.hom ≫ 𝟙 S) (hk : i ≫ q = 1) :
    IsCPMap P M (𝟙 S) q.left hq w ↔ ∃! p : LB.Gen (lamOn i P.L.L) × LB.Gen (P.L.L.pull i.left),
      IsBiextTriv P.c i p.1 ∧ IsCubTriv P.c i p.2 ∧ IsEven (toCubSym P) i p.2 ∧ Induces i p.2 p.1 ∧
        IsCubSymDescent (toCubSym P) i p.1 p.2 q (toCubSym M) w := by
  refine ⟨fun h => ?_, fun ⟨_, h, _⟩ => (isCPMap_iff_ofHom hq).2 h.2.2.2.2.2⟩
  obtain ⟨s, σ, a⟩ := exists_descent h hk
  refine ⟨(s, σ), a, fun p b => ?_⟩
  have := descent_unique b.1 a.1 b.2.1.gen a.2.1.gen b.2.2.2.2.1 a.2.2.2.2.1
  exact Prod.ext this.1 this.2

def descEquiv {X : Type} [AddCommGroup X] (Q : TQ G X) (P : CP G) :
    haveI := Q.i_hom; haveI := Q.q_hom
    Q.Desc P ≃ {d : Σ M : CubSym Q.B, LB.Iso P.L.L (M.L.L.pull Q.q.left) //
      ∃ s σ, IsBiextTriv P.c Q.i s ∧ IsCubTriv P.c Q.i σ ∧ IsCubSymDescent (toCubSym P) Q.i s σ Q.q d.1 d.2} :=
  haveI := Q.i_hom; haveI := Q.q_hom
  { toFun := fun D => ⟨⟨toCubSym D.M, D.w⟩, by
      obtain ⟨s, σ, a, b, -, -, c⟩ := exists_descent D.map Q.isKernel.w
      exact ⟨s, σ, a, b, c⟩⟩
    invFun := fun d => ⟨toCP d.1.1, d.1.2, (isCPMap_iff_ofHom _).2 (d.2.elim fun _ h => h.elim fun _ h => h.2.2.2)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

end Desc

theorem typings_agree (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] :
    (∃ E : CP G ≃ CubSym G, ∀ P, (E P).L = P.L ∧ (E P).cub ≍ P.c ∧ (E P).sym ≍ P.sym ∧ E P = toCubSym P) ∧
    (∀ (S' : Scheme.{0}) (G' : Over S') [GrpObj G'] [IsCommMonObj G'] (P' : CP G') (P : CP G),
      (∀ (m : CubeMap G' G) (w), IsCPMap P' P m.e m.F (cubeMap_over m) w ↔ IsCubSymIso m (toCubSym P') (toCubSym P) w) ∧
      ∀ (f : S' ⟶ S) (F : G'.left ⟶ G.left) (hw) (w), IsCPMap P' P f F hw w ↔
        ∃ mul : ∀ (T : Over S') (x y : T ⟶ G'), toBase hw (x * y) = toBase hw x * toBase hw y,
          IsCubSymIso (cubeMapOf mul) (toCubSym P') (toCubSym P) w) ∧
    (∀ (H : Over S) [GrpObj H] [IsCommMonObj H] (i : H ⟶ G) [IsMonHom i],
      (∀ (L : RigLB G) (c : CubicalStr G L),
        (∃ E : BiTriv c i ≃ {s // IsBiextTriv c i s}, ∀ a, (E a).1 = a.s) ∧
        ∃ E : CubTriv c i ≃ {σ // IsCubTriv c i σ}, ∀ a, RigMul L i a.s (E a).1) ∧
      ∀ (P : CP G) (a : CubTriv P.c i) (σ), RigMul P.L i a.s σ → (a.Even ↔ IsEven (toCubSym P) i σ)) ∧
    (∀ (L : RigLB G) (c : CubicalStr G L) (N : ℕ) (T : Over S) (x y : T ⟶ G) (ζ),
      CubWeil c N x y ζ ↔ IsPairing c N x y ζ) ∧
    ∀ (X : Type) [AddCommGroup X],
      (∀ (i : splitTorus S X ⟶ G) (χ : X) (V) (u), IsWeight i χ V u ↔ IsStable i V ∧ IsWt i V u χ) ∧
      (∀ (B : Over S) [GrpObj B] (i : splitTorus S X ⟶ G) (q : G ⟶ B), IsTorusExt i q ↔
        Module.Free ℤ X ∧ Module.Finite ℤ X ∧
          ∃ Q : TQ G X, (⟨Q.B, Q.grp, Q.i, Q.q⟩ : Σ (B : Over S) (_ : GrpObj B), (splitTorus S X ⟶ G) × (G ⟶ B)) =
            ⟨B, inferInstance, i, q⟩) ∧
      ∀ Q : TQ G X, haveI := Q.i_hom; haveI := Q.q_hom
        (∀ (P : CP G) (M : CP Q.B) (w), (∃ D : Q.Desc P, (⟨D.M, D.w⟩ : Σ M : CP Q.B, LB.Iso P.L.L (M.L.L.pull Q.q.left)) =
            ⟨M, w⟩) ↔ ∃! p : LB.Gen (lamOn Q.i P.L.L) × LB.Gen (P.L.L.pull Q.i.left),
          IsBiextTriv P.c Q.i p.1 ∧ IsCubTriv P.c Q.i p.2 ∧ IsEven (toCubSym P) Q.i p.2 ∧ Induces Q.i p.2 p.1 ∧
            IsCubSymDescent (toCubSym P) Q.i p.1 p.2 Q.q (toCubSym M) w) ∧
        ∀ (N : LB Q.B.left) (χ : X), N.IsLB →
          (∀ u, Q.GenWt N u χ ↔ IsWeightGen Q.i χ N (K := PUnit) (fun _ => Q.q.left) (fun _ => 1) u) ∧
          (IsWeightBundle Q.i Q.q χ N ↔ ∃ u, Q.GenWt N u (-χ)) := by
  refine ⟨⟨cpEquiv G, fun _ => ⟨rfl, HEq.rfl, HEq.rfl, rfl⟩⟩,
    fun S' G' _ _ P' P => ⟨fun m w => isCPMap_iff m P' P w, fun f F hw w => isCPMap_iff_exists hw P' P w⟩,
    fun H _ _ i _ => ⟨fun L c => ⟨⟨biTrivEquiv c i, fun _ => rfl⟩, cubTrivEquiv c i, rigMul_cubTrivEquiv⟩,
      fun P a σ R => even_iff a R⟩, fun L c N T x y ζ => cubWeil_iff c N x y ζ,
    fun X _ => ⟨isWeight_iff, fun B _ i q => ⟨fun h => ⟨h.free, h.finite, toTQ h, rfl⟩, ?_⟩, fun Q => ⟨fun P M w => ?_,
      fun N χ hN => ⟨fun u => genWt_iff Q hN u χ, (isWeightBundle_iff Q χ N).trans (and_iff_right hN)⟩⟩⟩⟩
  · rintro ⟨_, _, Q, e⟩
    have h := isTorusExt_of_tq Q
    cases Q; cases e; exact h
  · have := Q.i_hom
    have := Q.q_hom
    refine Iff.trans ⟨?_, fun h => ⟨⟨M, w, h⟩, rfl⟩⟩ (isCPMap_iff_descent (by simp) Q.isKernel.w)
    rintro ⟨⟨_, _, h⟩, e⟩
    cases e; exact h

end GlobalTheory.CubCompare
end
