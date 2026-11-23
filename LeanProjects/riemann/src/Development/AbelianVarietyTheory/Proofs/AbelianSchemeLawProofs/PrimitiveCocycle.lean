import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod

noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PrimCocycle

variable {S : Scheme.{0}} {B : Over S} [GrpObj B] [IsCommMonObj B]

abbrev lamφ (B : Over S) [GrpObj B] : ULift.{0} (Finset (Fin 2)) → ((B ⊗ B).left ⟶ B.left) :=
  fun I => (psum B (x2 B) I.down).left

abbrev lamε : ULift.{0} (Finset (Fin 2)) → ℤ := fun I => (-1) ^ (2 - I.down.card)

theorem prod_lam {T : Over S} (x y : T ⟶ B) {U : Type} [CommGroup U] (h : (T.left ⟶ B.left) → U) :
    ∏ I, h ((lift x y).left ≫ lamφ B I) ^ lamε I =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ B).left := by
  have e : ∀ I, (lift x y).left ≫ lamφ B I = (psum B ![x, y] I.down).left := fun I =>
    congrArg (fun q => q.left) ((psum_hom (preHom (lift x y)) (x2 B) I.down).trans
      (congrArg (fun q => psum B q I.down) (funext fun i => by fin_cases i <;> simp [preHom, x2])))
  refine (Fintype.prod_equiv (Equiv.ulift : ULift.{0} (Finset (Fin 2)) ≃ Finset (Fin 2)) _
    (fun I => h (psum B ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    (fun I => congrArg (fun q => h q ^ lamε I) (e I))).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton]
  have p₀ : psum B ![x, y] ∅ = 1 := rfl
  have p₁ : psum B ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum B ![x, y] {1} = y := _root_.mul_one y
  have p₄ : psum B ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  rw [p₀, p₁, p₂, p₄]
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₄ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [q₀, q₁, q₁, q₄]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem exists_normalised {L : LB B.left} (hL : L.IsLB) (t : LB.Gen (LB.LinComb L (lamφ B) lamε)) (ht : t.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L (lamφ B) lamε), u.IsGen ∧
      ∀ (T : Over S) (z : T.left) (J), Good L z J → val₂ u z J (1 : T ⟶ B) 1 = 1 := by
  obtain ⟨u, hu, hv⟩ := exists_gen hL (φ' := lamφ B) (ε' := lamε)
    (fun V _ k => by
      refine Eq.trans (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (c := ∏ i, k (lamφ B i) ^ lamε i) rfl
        (DVR.prod_neg _ _ (prod_lam (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B) k))) ?_
      simp)
    (LB.mulGen L _ _ _ _ t (LB.invGen L _ _ (LB.pullGen L _ _ t (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left)))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ ht (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _)))
  refine ⟨u, hu, fun T z J hJ => ?_⟩
  have : (lift (1 : T ⟶ B) (1 : T ⟶ B)).left ≫ (lift (1 : B ⊗ B ⟶ B) (1 : B ⊗ B ⟶ B)).left =
      (lift (1 : T ⟶ B) (1 : T ⟶ B)).left := by
    rw [← Over.comp_left, comp_lift, MonObj.comp_one]
  rw [val₂, hv _ _ z J hJ, val_mul hJ, val_inv, val_pull hJ, this, mul_inv_cancel]

theorem val_mul_eq (hG : GlobalFnsSt) (hB : IsAbelianScheme B) {L : LB B.left} (hL : L.IsLB)
    (u : LB.Gen (LB.LinComb L (lamφ B) lamε)) (hu : u.IsGen)
    (e : 𝟙_ (Over S) ⟶ G3 B) (a b c d a' b' c' d' : G3 B ⟶ B)
    (hF : ∀ (V : Type) [CommGroup V] (k : (G3 B ⟶ B) → V),
      (k (a' * b') * (k a')⁻¹ * (k b')⁻¹ * k 1) * (k (c' * d') * (k c')⁻¹ * (k d')⁻¹ * k 1) =
      (k (a * b) * (k a)⁻¹ * (k b)⁻¹ * k 1) * (k (c * d) * (k c)⁻¹ * (k d)⁻¹ * k 1))
    (ha : e ≫ a = 1) (hb : e ≫ b = 1) (hc : e ≫ c = 1) (hd : e ≫ d = 1)
    (ha' : e ≫ a' = 1) (hb' : e ≫ b' = 1) (hc' : e ≫ c' = 1) (hd' : e ≫ d' = 1)
    {T : Over S} (ρ : T ⟶ G3 B) {z : T.left} {J} (hJ : Good L z J) :
    val₂ u z J (ρ ≫ a) (ρ ≫ b) * val₂ u z J (ρ ≫ c) (ρ ≫ d) =
      val₂ u z J (ρ ≫ a') (ρ ≫ b') * val₂ u z J (ρ ≫ c') (ρ ≫ d') := by
  have vp : ∀ {T T' : Over S} (ρ : T' ⟶ T) {z : T'.left} {J}, Good L z J → ∀ a b : T ⟶ B,
      val (LB.pullGen L _ _ u (lift a b).left) ρ.left z J = val₂ u z J (ρ ≫ a) (ρ ≫ b) := fun ρ z J hJ a b => by
    rw [val_pull hJ, ← Over.comp_left, comp_lift]; rfl
  have sj : Function.Surjective ((snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom).appTop.hom :=
    surj_comp (surj_snd hG hB _) (surj_comp (surj_snd hG hB _) (hG _ _ hB).2)
  have he : e.left ≫ (snd B (B ⊗ B)).left ≫ (snd B B).left ≫ B.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have ev : ∀ {T' : Over S} (σ : T' ⟶ G3 B) {z : T'.left} {J}, Good L z J → ∀ a b c d : G3 B ⟶ B,
      val (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ u (lift a b).left) (LB.pullGen L _ _ u (lift c d).left))
        σ.left z J = val₂ u z J (σ ≫ a) (σ ≫ b) * val₂ u z J (σ ≫ c) (σ ≫ d) := fun σ z J hJ a b c d =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vp σ hJ _ _) (vp σ hJ _ _))
  refine (ev ρ hJ a b c d).symm.trans (Eq.trans (gen_unique' hL (fun V _ k => ?_) _ e.left he sj
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hu _) (DVR.pullGen_isGen _ _ _ _ hu _))
    (fun y I hI => ?_) _ ρ.left z J hJ) (ev ρ hJ a' b' c' d'))
  · exact (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
      (prod_lam a' b' k) (prod_lam c' d' k)).trans ((hF V fun q => k q.left).trans
      (DVR.prod_sum₂ (K := ULift.{0} (Finset (Fin 2))) (K' := ULift.{0} (Finset (Fin 2))) (U := V) _
        (prod_lam a b k) (prod_lam c d k)).symm)
  · refine (ev e hI a b c d).trans (Eq.trans ?_ (ev e hI a' b' c' d').symm)
    rw [ha, hb, hc, hd, ha', hb', hc', hd']

theorem primitive_cocycle : GlobalFnsSt → ∀ (S : Scheme.{0}) (B : Over S) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → ∀ (O : RigLB B), (∃ t : LB.Gen (abelian₂ B O.L), t.IsGen) → ∃ t : LB.Gen (abelian₂ B O.L), t.IsGen ∧ ∀ (Z : Over S) (z : Z.left) (J : (Z.left ⟶ B.left) → O.L.ι), Geo.Tor.Good O.L z J → let v : (Z ⟶ B) → (Z ⟶ B) → (Z.left.presheaf.stalk z)ˣ := fun x y => Geo.Tor.val (L := O.L) (φ := fun I : ULift.{0} (Finset (Fin 2)) => (psum B (x2 B) I.down).left) (ε := fun I => (-1) ^ (2 - I.down.card)) t (lift x y).left z J; (∀ x, v x 1 = 1) ∧ (∀ x y, v x y = v y x) ∧ ∀ x y w, v (x * y) w * v x y = v x (y * w) * v y w := by
  rintro hG S B _ _ hB O ⟨t, ht⟩
  obtain ⟨u, hu, h₀⟩ := exists_normalised O.isLB t ht
  refine ⟨u, hu, fun Z z J hJ => ?_⟩
  show (∀ x, val₂ u z J x 1 = 1) ∧ (∀ x y, val₂ u z J x y = val₂ u z J y x) ∧
    ∀ x y w, val₂ u z J (x * y) w * val₂ u z J x y = val₂ u z J x (y * w) * val₂ u z J y w
  let p₀ := x3 B 0
  let p₁ := x3 B 1
  let p₂ := x3 B 2
  let e : 𝟙_ (Over S) ⟶ G3 B := lift 1 (lift 1 1)
  have e₀ : e ≫ p₀ = 1 := by simp [e, p₀, x3]
  have e₁ : e ≫ p₁ = 1 := by simp [e, p₁, x3]
  have e₂ : e ≫ p₂ = 1 := by simp [e, p₂, x3]
  have o : e ≫ (1 : G3 B ⟶ B) = 1 := MonObj.comp_one _
  have r₀ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₀ = x := fun x y w => by simp [p₀, x3]
  have r₁ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₁ = y := fun x y w => by simp [p₁, x3]
  have r₂ : ∀ x y w : Z ⟶ B, lift x (lift y w) ≫ p₂ = w := fun x y w => by simp [p₂, x3]
  refine ⟨fun x => ?_, fun x y => ?_, fun x y w => ?_⟩
  · have := val_mul_eq hG hB O.isLB u hu e p₀ 1 1 1 1 1 1 1 (fun V _ k => by simp) e₀ o o o o o o o
      (lift x (lift x x)) hJ
    rw [r₀, MonObj.comp_one, h₀ Z z J hJ] at this
    simpa using this
  · have := val_mul_eq hG hB O.isLB u hu e p₀ p₁ 1 1 p₁ p₀ 1 1 (fun V _ k => by
      rw [mul_comm p₁ p₀, mul_right_comm (k (p₀ * p₁))]) e₀ e₁ o o e₁ e₀ o o (lift x (lift y x)) hJ
    rw [r₀, r₁] at this
    exact mul_right_cancel this
  · have := val_mul_eq hG hB O.isLB u hu e (p₀ * p₁) p₂ p₀ p₁ p₀ (p₁ * p₂) p₁ p₂ (fun V _ k => by
      rw [_root_.mul_assoc p₀ p₁ p₂]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel) ((MonObj.comp_mul _ _ _).trans (by rw [e₀, e₁, _root_.mul_one])) e₂ e₀ e₁ e₀
      ((MonObj.comp_mul _ _ _).trans (by rw [e₁, e₂, _root_.mul_one])) e₁ e₂ (lift x (lift y w)) hJ
    rwa [MonObj.comp_mul, MonObj.comp_mul, r₀, r₁, r₂] at this

end GlobalTheory.PrimCocycle
