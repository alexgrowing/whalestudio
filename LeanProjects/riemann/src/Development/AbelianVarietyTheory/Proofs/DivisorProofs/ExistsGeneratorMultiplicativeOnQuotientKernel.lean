import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TorusHomOfIff
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TwistBaseChangeAndValuationStatements
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MK
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointAbelianPartAndClassifyingMapLinear
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordGeneratorAbelianPartAtLevelImports
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT GlobalTheory.Mum GlobalTheory.Mum.Two
open GlobalTheory.HomMum

noncomputable section

namespace GlobalTheory.HomMum

theorem prod_psum_two {S : Scheme.{0}} {A T : Over S} [GrpObj A] [IsCommMonObj A] (x y : T ⟶ A) {V : Type}
    [CommGroup V] (h : (T.left ⟶ A.left) → V) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h (psum A ![x, y] I.down).left ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ A).left := by
  refine (Fintype.prod_equiv Equiv.ulift _ (fun I => h (psum A ![x, y] I).left ^ ((-1 : ℤ) ^ (2 - I.card)))
    fun _ => rfl).trans ?_
  rw [show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_insert (by decide), Finset.prod_singleton]
  have p₀ : psum A ![x, y] ∅ = 1 := rfl
  have p₁ : psum A ![x, y] {0} = x := _root_.mul_one x
  have p₂ : psum A ![x, y] {1} = y := _root_.mul_one y
  have p₃ : psum A ![x, y] {0, 1} = x * y := congrArg (x * ·) (_root_.mul_one y)
  have q₀ : (-1 : ℤ) ^ (2 - (∅ : Finset (Fin 2)).card) = 1 := by decide
  have q₁ : ∀ i : Fin 2, (-1 : ℤ) ^ (2 - ({i} : Finset (Fin 2)).card) = -1 := by decide
  have q₃ : (-1 : ℤ) ^ (2 - ({0, 1} : Finset (Fin 2)).card) = 1 := by decide
  rw [p₀, p₁, p₂, p₃, q₀, q₁, q₁, q₃]
  simp only [zpow_neg, zpow_one]
  ac_rfl

theorem prod_mφ {S : Scheme.{0}} {H₁ H₂ : Over S} [GrpObj H₁] [IsCommMonObj H₁] [GrpObj H₂] [IsCommMonObj H₂]
    (a b : H₁ ⟶ H₂) {T : Over S} (x y : T ⟶ H₁) {V : Type} [CommGroup V] (h : (T.left ⟶ H₁.left ⨿ H₂.left) → V) :
    ∏ k, h ((lift x y).left ≫ mφ H₁ H₂ a b k) ^ mε k =
      (h (((x ≫ a) * (y ≫ b)).left ≫ coprod.inr) * (h ((x ≫ a).left ≫ coprod.inr))⁻¹ *
        (h ((y ≫ b).left ≫ coprod.inr))⁻¹ * h ((1 : T ⟶ H₂).left ≫ coprod.inr)) *
      (h ((x * y).left ≫ coprod.inl) * (h (x.left ≫ coprod.inl))⁻¹ * (h (y.left ≫ coprod.inl))⁻¹ *
        h ((1 : T ⟶ H₁).left ≫ coprod.inl))⁻¹ := by
  rw [Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) ((Finset.prod_congr rfl fun I _ => ?_).trans
    (prod_psum_two (x ≫ a) (y ≫ b) (fun q => h (q ≫ coprod.inr))))
    ((Finset.prod_congr rfl fun I _ => ?_).trans ((Finset.prod_inv_distrib _).trans
      (congrArg (·⁻¹) (prod_psum_two x y (fun q => h (q ≫ coprod.inl))))))
  · rw [mφ_comp]; rfl
  · rw [mφ_comp]; exact zpow_neg _ _

theorem push_comp_two {S S' : Scheme.{0}} {j : S' ⟶ S} {E₁ E₂ : Over S'} {A₁ A₂ : Over S}
    (p₁ : (Over.map j).obj E₁ ⟶ A₁) (p₂ : (Over.map j).obj E₂ ⟶ A₂) {c' : E₁ ⟶ E₂} {c : A₁ ⟶ A₂}
    (h : GlobalTheory.EndRosati.push p₂ c' = p₁ ≫ c) {T : Over S'} (x : T ⟶ E₁) :
    GlobalTheory.EndRosati.push p₂ (x ≫ c') = GlobalTheory.EndRosati.push p₁ x ≫ c := by
  simp only [GlobalTheory.EndRosati.push, Functor.map_comp, Category.assoc] at h ⊢
  rw [h]

theorem push_pG_pair {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I}
    {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂]
    [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f : G₁ ⟶ G₂}
    {fB : D₁.toPre.P.A ⟶ D₂.toPre.P.A}
    (hf : (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB) :
    GlobalTheory.EndRosati.push (U₂.gt e).pG ((Over.pullback (thick R I e)).map f) = (U₁.gt e).pG ≫ fB := by
  rw [GlobalTheory.EndRosati.push]
  simp only [GtCoord.pG]
  rw [← Functor.map_comp_assoc, hf, Functor.map_comp_assoc, Category.assoc]
  exact congrArg _ (GlobalTheory.EndRosati.push_fstG e fB)

theorem add_left_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a a' b : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ (x * y))⁻¹ * (W₁ (x' * y))⁻¹ * W₁ x * W₁ x' * W₁ y *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ (a * b))⁻¹ * (W₂ (a' * b))⁻¹ * W₂ a * W₂ a' * W₂ b *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * a' * b) * (W₂ (a * a'))⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * x' * y) * (W₁ (x * x'))⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ *
        v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x * y) * (W₁ x)⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a' * b) * (W₂ a')⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (x' * y) * (W₁ x')⁻¹ * (W₁ y)⁻¹ * W₁ 1)⁻¹ * v₂) := by
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

theorem add_right_two {P₁ P₂ V : Type} [CommGroup P₁] [CommGroup P₂] [CommGroup V] (W₁ : P₁ → V) (W₂ : P₂ → V)
    {x x' y : P₁} {a b b' : P₂} {c₁ c₂ v v₁ v₂ : V}
    (h₁ : 1 = W₁ (y * x * x') * (W₁ (y * x))⁻¹ * (W₁ (y * x'))⁻¹ * (W₁ (x * x'))⁻¹ * W₁ y * W₁ x * W₁ x' *
      (W₁ 1)⁻¹ * c₁)
    (h₂ : 1 = W₂ (a * b * b') * (W₂ (a * b))⁻¹ * (W₂ (a * b'))⁻¹ * (W₂ (b * b'))⁻¹ * W₂ a * W₂ b * W₂ b' *
      (W₂ 1)⁻¹ * c₂)
    (h : v * c₁ = c₂ * (v₁ * v₂)) :
    (W₂ (a * (b * b')) * (W₂ a)⁻¹ * (W₂ (b * b'))⁻¹ * W₂ 1) *
        (W₁ (y * (x * x')) * (W₁ y)⁻¹ * (W₁ (x * x'))⁻¹ * W₁ 1)⁻¹ * v =
      ((W₂ (a * b) * (W₂ a)⁻¹ * (W₂ b)⁻¹ * W₂ 1) * (W₁ (y * x) * (W₁ y)⁻¹ * (W₁ x)⁻¹ * W₁ 1)⁻¹ * v₁) *
        ((W₂ (a * b') * (W₂ a)⁻¹ * (W₂ b')⁻¹ * W₂ 1) * (W₁ (y * x') * (W₁ y)⁻¹ * (W₁ x')⁻¹ * W₁ 1)⁻¹ * v₂) := by
  rw [← _root_.mul_assoc a b b', ← _root_.mul_assoc y x x']
  have e₁ := congrArg Additive.ofMul h₁
  have e₂ := congrArg Additive.ofMul h₂
  have e := congrArg Additive.ofMul h
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_one] at e₁ e₂ e ⊢
  linear_combination (norm := abel) e₁ - e₂ + e

end GlobalTheory.HomMum

end

namespace GlobalTheory.HomMum

set_option maxHeartbeats 1600000 in

theorem exists_gen_mul_level : ∀ {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D₁ D₂ : DegData R I} {A₁ A₂ : PolAV (Sp (FractionRing R))} {G₁ G₂ : Over (Sp R)} [GrpObj G₁] [IsCommMonObj G₁] [GrpObj G₂] [IsCommMonObj G₂] (U₁ : UnifPre I D₁ A₁ G₁) (U₂ : UnifPre I D₂ A₂ G₂) (e : ℕ) {f g : G₁ ⟶ G₂} [IsMonHom f] [IsMonHom g] {fB gB : D₁.toPre.P.A ⟶ D₂.toPre.P.A} [IsMonHom fB] [IsMonHom gB], (Over.pullback (thick R I e)).map f ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map fB → (Over.pullback (thick R I e)).map g ≫ (U₂.gt e).q = (U₁.gt e).q ≫ (Over.pullback (thick R I e)).map gB → ∀ (W : LB.Iso ((join U₁.LG.L U₂.LG.L).pull (coprod.map (fstG I e G₁).left (fstG I e G₂).left)) ((JN D₁.toPre D₂.toPre).pull (coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))), W.IsGen → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₁).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₁.gt e).pG.left (r z) ∈ D₁.toPre.P.L.U j.1 → (fstG I e G₁).left (r z) ∈ U₁.LG.L.U k.1 → gw W (r ≫ coprod.inl) z j (fun _ => k) = gw (U₁.w e) r z j.1 (fun _ => k.1)) → (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G₂).left) (z : Z) (j : (JN D₁.toPre D₂.toPre).ι) (k : (join U₁.LG.L U₂.LG.L).ι), (U₂.gt e).pG.left (r z) ∈ D₂.toPre.P.L.U j.2 → (fstG I e G₂).left (r z) ∈ U₂.LG.L.U k.2 → gw W (r ≫ coprod.inr) z j (fun _ => k) = gw (U₂.w e) r z j.2 (fun _ => k.2)) → ∀ (u : LB.Gen (LB.LinComb (join U₁.LG.L U₂.LG.L) (mφ G₁ G₂ f g) mε)), u.IsGen → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ G₁.left ⨿ G₂.left) → (join U₁.LG.L U₂.LG.L).ι), Good (join U₁.LG.L U₂.LG.L) z J → ∀ x x' y : T ⟶ G₁, val u (lift (x * x') y).left z J * cubV U₁.cubG z (rl J) x x' y = cubV U₂.cubG z (rr J) (x ≫ f) (x' ≫ f) (y ≫ g) * (val u (lift x y).left z J * val u (lift x' y).left z J) ∧ val u (lift y (x * x')).left z J * cubV U₁.cubG z (rl J) y x x' = cubV U₂.cubG z (rr J) (y ≫ f) (x ≫ g) (x' ≫ g) * (val u (lift y x).left z J * val u (lift y x').left z J)) → ∃ v : LB.Gen (LB.LinComb (JN D₁.toPre D₂.toPre) (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) ((Over.pullback (thick R I e)).map f) ((Over.pullback (thick R I e)).map g) k ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left) mε), v.IsGen ∧ (∀ (T : Over (Sp (R ⧸ I ^ (e + 1)))) (z : T.left) (J : (T.left ⟶ D₁.toPre.P.A.left ⨿ D₂.toPre.P.A.left) → (JN D₁.toPre D₂.toPre).ι), Good (JN D₁.toPre D₂.toPre) z J → ∀ x x' y : T ⟶ thickObj R I e G₁, (Over.map (thick R I e)).map x ≫ (U₁.gt e).pG = 1 → val v (lift (x * x') y).left z J = val v (lift x y).left z J * val v (lift x' y).left z J ∧ val v (lift y (x * x')).left z J = val v (lift y x).left z J * val v (lift y x').left z J) := by
  intro R _ _ I D₁ D₂ A₁ A₂ G₁ G₂ _ _ _ _ U₁ U₂ e f g _ _ fB gB _ _ hf hg W hW hW₁ hW₂ u hu hadd
  let f' := (Over.pullback (thick R I e)).map f
  let g' := (Over.pullback (thick R I e)).map g
  haveI : Nonempty G₁.left := ⟨eSec G₁ (⊥ : PrimeSpectrum R)⟩
  haveI : Nonempty G₂.left := ⟨eSec G₂ (⊥ : PrimeSpectrum R)⟩
  have hL : (join U₁.LG.L U₂.LG.L).IsLB := join_isLB U₁.LG.isLB U₂.LG.isLB
  obtain ⟨u', hu', vu⟩ := exists_gen hL
    (φ' := fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k ≫
      coprod.map (fstG I e G₁).left (fstG I e G₂).left) (ε' := mε)
    (fun V _ h => Finset.prod_congr rfl fun k _ => congrArg (h · ^ mε k) (by
      rw [mφ_push (fstG I e G₁) (fstG I e G₂) (GlobalTheory.EndRosati.fstG_mul e) (GlobalTheory.EndRosati.fstG_mul e)
        (GlobalTheory.EndRosati.push_fstG e f) (GlobalTheory.EndRosati.push_fstG e g) (fst _ _) (snd _ _) k, lift_fst_snd,
        Over.id_left, Category.id_comp]))
    (LB.pullGen (join U₁.LG.L U₂.LG.L) _ _ u
      (lift (GlobalTheory.EndRosati.push (fstG I e G₁) (fst (thickObj R I e G₁) (thickObj R I e G₁)))
        (GlobalTheory.EndRosati.push (fstG I e G₁) (snd (thickObj R I e G₁) (thickObj R I e G₁)))).left)
    (DVR.pullGen_isGen _ _ _ _ hu _)
  obtain ⟨v, hv, vv⟩ := GlobalTheory.EndRosati.exists_gen_through hL (jn_isLB D₁.toPre D₂.toPre) W hW
    (fun k => mφ (thickObj R I e G₁) (thickObj R I e G₂) f' g' k) mε u' hu'
  refine ⟨v, hv, fun T z J hJ x x' y hx => ?_⟩
  choose N hN using fun χ : T.left ⟶ G₁.left ⨿ G₂.left => exists_chart hL (χ z)
  have hN' : Good (join U₁.LG.L U₂.LG.L) z N := hN
  have gJ₁ : Good D₁.toPre.P.L z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inl _ _).good hJ
  have gJ₂ : Good D₂.toPre.P.L z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) := (isPart_inr _ _).good hJ
  have gN₁ : Good U₁.LG.L z (rl N) := (isPart_inl _ _).good hN'
  have gN₂ : Good U₂.LG.L z (rr N) := (isPart_inr _ _).good hN'
  let W₁ : (T ⟶ thickObj R I e G₁) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N) q.left
  let W₂ : (T ⟶ thickObj R I e G₂) → (T.left.presheaf.stalk z)ˣ := fun q =>
    GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N) q.left
  have hinl : ∀ q : T ⟶ thickObj R I e G₁, gw W (q.left ≫ coprod.inl) z
      (J ((q.left ≫ coprod.inl) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inl) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₁ q := fun q => by
    have := hW₁ T.left q.left z (J ((q.left ≫ (U₁.gt e).pG.left) ≫ coprod.inl))
      (N ((q.left ≫ (fstG I e G₁).left) ≫ coprod.inl)) (gJ₁ _) (gN₁ _)
    simp only [Category.assoc, coprod.inl_map] at this ⊢
    exact this
  have hinr : ∀ q : T ⟶ thickObj R I e G₂, gw W (q.left ≫ coprod.inr) z
      (J ((q.left ≫ coprod.inr) ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
      (fun _ => N ((q.left ≫ coprod.inr) ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)) = W₂ q := fun q => by
    have := hW₂ T.left q.left z (J ((q.left ≫ (U₂.gt e).pG.left) ≫ coprod.inr))
      (N ((q.left ≫ (fstG I e G₂).left) ≫ coprod.inr)) (gJ₂ _) (gN₂ _)
    simp only [Category.assoc, coprod.inr_map] at this ⊢
    exact this
  let p₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ G₁) := GlobalTheory.EndRosati.push (fstG I e G₁)
  let p₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ G₂) := GlobalTheory.EndRosati.push (fstG I e G₂)
  let q₁ : (T ⟶ thickObj R I e G₁) → ((Over.map (thick R I e)).obj T ⟶ D₁.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₁.gt e).pG
  let q₂ : (T ⟶ thickObj R I e G₂) → ((Over.map (thick R I e)).obj T ⟶ D₂.toPre.P.A) :=
    GlobalTheory.EndRosati.push (U₂.gt e).pG
  have hV : ∀ a b : T ⟶ thickObj R I e G₁, val v (lift a b).left z J =
      (W₂ ((a ≫ f') * (b ≫ g')) * (W₂ (a ≫ f'))⁻¹ * (W₂ (b ≫ g'))⁻¹ * W₂ 1) *
        (W₁ (a * b) * (W₁ a)⁻¹ * (W₁ b)⁻¹ * W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (val u (lift (p₁ a) (p₁ b)).left z N) :=
    fun a b => by
      refine (vv _ _ z J N hJ hN').trans (congrArg₂ (· * ·) ?_
        ((vu _ _ z N hN').trans ((val_pull hN' _ _ _).trans (congrArg (val u · z N) (GlobalTheory.EndRosati.lift_push _ a b)))))
      refine (prod_mφ f' g' a b (fun ψ => gw W ψ z (J (ψ ≫ coprod.map (U₁.gt e).pG.left (U₂.gt e).pG.left))
        (fun _ => N (ψ ≫ coprod.map (fstG I e G₁).left (fstG I e G₂).left)))).trans ?_
      beta_reduce
      erw [hinr ((a ≫ f') * (b ≫ g')), hinr (a ≫ f'), hinr (b ≫ g'), hinr 1, hinl (a * b), hinl a, hinl b, hinl 1]
  have hc₁ : ∀ a b c : T ⟶ thickObj R I e G₁,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) (q₁ b) (q₁ c)) =
      W₁ (a * b * c) * (W₁ (a * b))⁻¹ * (W₁ (a * c))⁻¹ * (W₁ (b * c))⁻¹ * W₁ a * W₁ b * W₁ c * (W₁ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₁.cubG (T := (Over.map (thick R I e)).obj T) z (rl N) (p₁ a) (p₁ b) (p₁ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₁ ![a, b, c] gJ₁ gN₁).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₁ e z (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rl N))))
  have hc₂ : ∀ a b c : T ⟶ thickObj R I e G₂,
      @id (T.left.presheaf.stalk z)ˣ (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
        (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) (q₂ b) (q₂ c)) =
      W₂ (a * b * c) * (W₂ (a * b))⁻¹ * (W₂ (a * c))⁻¹ * (W₂ (b * c))⁻¹ * W₂ a * W₂ b * W₂ c * (W₂ 1)⁻¹ *
        @id (T.left.presheaf.stalk z)ˣ (cubV U₂.cubG (T := (Over.map (thick R I e)).obj T) z (rr N) (p₂ a) (p₂ b) (p₂ c)) :=
    fun a b c => (GlobalTheory.TorusInvariance.cube_val U₂ ![a, b, c] gJ₂ gN₂).trans
      (congrArg (· * _) (GlobalTheory.TorusInvariance.prod_psum a b c
        (GlobalTheory.TorusInvariance.wVal U₂ e z (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (rr N))))
  have C₁ := isCub_cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₁
  have C₂ := isCub_cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) gJ₂
  have c₁ : ∀ a b c, q₁ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₁ b) (q₁ c)) h).trans (C₁.face _ _)).symm.trans (hc₁ a b c)
  have c₂ : ∀ a b c, q₁ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₁.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rl (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₁ a) · (q₁ c)) h).trans (C₁.face₂ _ _)).symm.trans (hc₁ a b c)
  have d₁ : ∀ a b c, q₂ a = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) · (q₂ b) (q₂ c)) h).trans (C₂.face _ _)).symm.trans (hc₂ a b c)
  have d₂ : ∀ a b c, q₂ b = 1 → _ := fun a b c h =>
    ((congrArg (cubV D₂.toPre.cub (T := (Over.map (thick R I e)).obj T) z
      (rr (M₁ := D₁.toPre.P.L) (M₂ := D₂.toPre.P.L) J) (q₂ a) · (q₂ c)) h).trans (C₂.face₂ _ _)).symm.trans (hc₂ a b c)
  have hx' : q₁ x = 1 := hx
  have xf : q₂ (x ≫ f') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hf) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have xg : q₂ (x ≫ g') = 1 :=
    (push_comp_two _ _ (push_pG_pair U₁ U₂ e hg) x).trans (by rw [show GlobalTheory.EndRosati.push (U₁.gt e).pG x = 1 from hx, MonObj.one_comp])
  have pf : ∀ a, p₁ a ≫ f = p₂ (a ≫ f') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e f) a).symm
  have pg : ∀ a, p₁ a ≫ g = p₂ (a ≫ g') := fun a => (push_comp_two _ _ (GlobalTheory.EndRosati.push_fstG e g) a).symm
  have pm : p₁ x * p₁ x' = p₁ (x * x') := (GlobalTheory.EndRosati.fstG_mul e x x').symm
  obtain ⟨r₁, r₂⟩ := hadd ((Over.map (thick R I e)).obj T) z N hN' (p₁ x) (p₁ x') (p₁ y)
  rw [pm, pf, pf, pg] at r₁
  rw [pm, pf, pg, pg] at r₂
  rw [hV, hV, hV, hV, hV, hV, MonObj.mul_comp x x' f', MonObj.mul_comp x x' g']
  exact ⟨add_left_two W₁ W₂ (c₁ _ _ _ hx') (d₁ _ _ _ xf) r₁, add_right_two W₁ W₂ (c₂ _ _ _ hx') (d₂ _ _ _ xg) r₂⟩

end GlobalTheory.HomMum
