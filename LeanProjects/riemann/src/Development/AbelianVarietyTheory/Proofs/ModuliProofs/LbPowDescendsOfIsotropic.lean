import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsIffCommIsOfAndLiftSubsingleton

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.ThetaSplit

@[ext] structure CocycleExt {C U : Type} (a : C → C → U) where

  u : U

  c : C

theorem exists_coboundary {C U : Type} [CommGroup C] [CommGroup U]
    (hU : ∀ n : ℕ, 0 < n → ∀ y : U, ∃ x : U, x ^ n = y) (a : C → C → U) (hs : ∀ x y, a x y = a y x)
    (hc : ∀ x y z, a x y * a (x * y) z = a y z * a x (y * z)) :
    ∃ b : C → U, ∀ x y, b (x * y) * a x y = b x * b y := by
  have h1 : ∀ x, a 1 x = a 1 1 := fun x => by
    have := hc 1 1 x
    simp only [_root_.one_mul] at this
    exact (mul_right_cancel this).symm
  letI : CommGroup (CocycleExt a) :=
    { mul := fun p q => ⟨p.u * q.u * a p.c q.c, p.c * q.c⟩
      one := ⟨(a 1 1)⁻¹, 1⟩
      inv := fun p => ⟨p.u⁻¹ * (a p.c⁻¹ p.c)⁻¹ * (a 1 1)⁻¹, p.c⁻¹⟩
      mul_assoc := fun p q r => CocycleExt.ext (by
        show p.u * q.u * a p.c q.c * r.u * a (p.c * q.c) r.c = p.u * (q.u * r.u * a q.c r.c) * a p.c (q.c * r.c)
        have e := congrArg Additive.ofMul (hc p.c q.c r.c)
        apply Additive.ofMul.injective
        simp only [ofMul_mul] at e ⊢
        linear_combination (norm := abel) e) (_root_.mul_assoc _ _ _)
      one_mul := fun p => CocycleExt.ext (by
        show (a 1 1)⁻¹ * p.u * a 1 p.c = p.u
        rw [h1 p.c, mul_comm (a 1 1)⁻¹, inv_mul_cancel_right]) (_root_.one_mul _)
      mul_one := fun p => CocycleExt.ext (by
        show p.u * (a 1 1)⁻¹ * a p.c 1 = p.u
        rw [hs p.c, h1 p.c, inv_mul_cancel_right]) (_root_.mul_one _)
      inv_mul_cancel := fun p => CocycleExt.ext (by
        show p.u⁻¹ * (a p.c⁻¹ p.c)⁻¹ * (a 1 1)⁻¹ * p.u * a p.c⁻¹ p.c = (a 1 1)⁻¹
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_inv]
        abel) (inv_mul_cancel _)
      mul_comm := fun p q => CocycleExt.ext (by
        show p.u * q.u * a p.c q.c = q.u * p.u * a q.c p.c
        rw [hs, mul_comm p.u]) (mul_comm _ _) }
  let j : U →* CocycleExt a := MonoidHom.mk' (fun u => ⟨u * (a 1 1)⁻¹, 1⟩) fun u v => CocycleExt.ext (by
    show u * v * (a 1 1)⁻¹ = u * (a 1 1)⁻¹ * (v * (a 1 1)⁻¹) * a 1 1
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel) (_root_.mul_one _).symm
  have hj : Function.Injective j := fun u v h => mul_right_cancel (congrArg CocycleExt.u h)
  letI : DivisibleBy (Additive U) ℕ := divisibleByOfSMulRightSurj _ _ fun {n} hn y => by
    obtain ⟨x, hx⟩ := hU n (Nat.pos_of_ne_zero hn) y.toMul
    exact ⟨Additive.ofMul x, congrArg Additive.ofMul hx⟩
  letI : DivisibleBy (Additive U) ℤ := AddGroup.divisibleByIntOfDivisibleByNat _
  obtain ⟨ρ, hρ⟩ := (Module.Baer.of_divisible (Additive U)).extension_property_addMonoidHom
    (MonoidHom.toAdditive j) hj (AddMonoidHom.id _)
  let σ : CocycleExt a →* U := AddMonoidHom.toMultiplicative ρ
  have hσ : ∀ u, σ (j u) = u := fun u => DFunLike.congr_fun hρ (Additive.ofMul u)
  refine ⟨fun x => σ ⟨1, x⟩, fun x y => ?_⟩
  rw [← map_mul σ, ← hσ (a x y), ← map_mul σ]
  refine congrArg σ (CocycleExt.ext ?_ (_root_.mul_one _))
  show 1 * (a x y * (a 1 1)⁻¹) * a (x * y) 1 = 1 * 1 * a x y
  rw [hs (x * y), h1 (x * y)]
  simp

theorem exists_rational {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {X : Scheme.{0}} (f : X ⟶ Sp k)
    [IsFinite f] (y : Sp k' ⟶ X) : ∃ c : Sp k ⟶ X, c ≫ f = 𝟙 _ ∧ (y ≫ f) ≫ c = y := by
  have hd : DiscreteTopology X := by
    have h := f.isDiscrete_preimage_singleton (IsLocalRing.closedPoint k)
    have e : f ⁻¹' {IsLocalRing.closedPoint k} = Set.univ := Set.eq_univ_of_forall fun x => Subsingleton.elim _ _
    exact isDiscrete_univ_iff.1 ((congrArg _root_.IsDiscrete e).mp h)
  have hx : IsClosed {y (IsLocalRing.closedPoint k')} := isClosed_discrete _
  refine ⟨pointOfClosedPoint f _ hx, pointOfClosedPoint_comp _ _ _, ?_⟩
  have e := Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k' X y
  calc (y ≫ f) ≫ pointOfClosedPoint f _ hx
      = ((Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo y)) ≫
          X.fromSpecResidueField (y (IsLocalRing.closedPoint k'))) ≫ f) ≫ pointOfClosedPoint f _ hx := by rw [e]
    _ = Spec.map (Scheme.descResidueField (Scheme.stalkClosedPointTo y)) ≫
          X.fromSpecResidueField (y (IsLocalRing.closedPoint k')) := by
        rw [Category.assoc, Category.assoc, ← Category.assoc (X.fromSpecResidueField _),
          ← SpecMap_residueFieldIsoBase_inv f _ hx, pointOfClosedPoint]
        refine congrArg (_ ≫ ·) ?_
        rw [← Spec.map_comp_assoc, Iso.hom_inv_id, Spec.map_id, Category.id_comp]
    _ = y := e

theorem epi_of_fields {k k' : Type} [Field k] [Field k'] (t : Sp k' ⟶ Sp k) : Epi t := by
  have : Surjective t := ⟨fun x => ⟨IsLocalRing.closedPoint k', Subsingleton.elim _ _⟩⟩
  have : Flat t := inferInstance
  exact Flat.epi_of_flat_of_surjective t

section Bundles

variable {X Y : Scheme.{0}} {L : LB X}

theorem exists_gen_lbPow (n : ℕ) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε ε' : K → ℤ}
    (hε : ∀ k, ε' k = n * ε k) (t : LB.Gen (LB.LinComb L φ ε')) (ht : t.IsGen) (b : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb (lbPow L n) φ ε), t'.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good (lbPow L n) z J →
        val t' r z J = val t r z (fun χ => J χ PUnit.unit) * gm r z ⊤ b := by
  have le : ∀ j : K → (lbPow L n).ι, LB.wchart (lbPow L n) φ j ≤ LB.wchart L φ (fun k => j k PUnit.unit) :=
    fun j y hy => Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Set.mem_iInter.1 hy k) PUnit.unit
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : K → (lbPow L n).ι), r z ∈ LB.wchart (lbPow L n) φ j →
      gm r z (LB.wchart (lbPow L n) φ j) (res (le j) (t.s _) * res le_top b) =
        gm r z (LB.wchart L φ (fun k => j k PUnit.unit)) (t.s _) * gm r z ⊤ b := fun Z r z j hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  refine ⟨⟨fun j => res (le j) (t.s _) * res le_top b⟩, fun i j => unit_ext fun y hy => ?_,
    fun Z r z J hJ => key Z r z _ (hJ.mem φ r)⟩
  refine ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y i hy.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gm_linComb (lbPow L n) φ ε (𝟙 Y) y i j hy.1 hy.2)
      ((gm_res (𝟙 Y) y _ hy _).trans (key _ _ y j hy.2)))).symm)
  rw [gen_trans ht (𝟙 Y) y (le i hy.1) (le j hy.2), _root_.mul_assoc]
  refine congrArg (· * _) (Finset.prod_congr rfl fun k _ => ?_)
  have e := gm_linComb L (K := PUnit) (fun _ => 𝟙 X) (fun _ => (n : ℤ)) (𝟙 Y ≫ φ k) y (i k) (j k)
    (Set.mem_iInter.1 hy.1 k) (Set.mem_iInter.1 hy.2 k)
  rw [Fintype.prod_unique, Category.comp_id] at e
  rw [hε, zpow_mul]
  exact congrArg (· ^ ε k) e.symm

theorem exists_rescale (hL : L.IsLB) {S₀ : Scheme.{0}} (p : X ⟶ S₀) (e : S₀ ⟶ X) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom) (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S₀, ⊤)ˣ, ∃ x : Γ(S₀, ⊤)ˣ, x ^ n = y)
    {C : Type} [CommGroup C] (τ : C → (X ⟶ X)) (hτ : ∀ c c', τ (c * c') = τ c ≫ τ c') (hτp : ∀ c, τ c ≫ p = p)
    (m : ℤ) (v : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, τ c] ![m, -m])) (hv : ∀ c, (v c).IsGen)
    (hc : ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v c) r z J * val (v c') (r ≫ τ c) z J = val (v c') r z J * val (v c) (r ≫ τ c') z J) :
    ∃ b : C → Γ(S₀, ⊤)ˣ, ∀ c c' (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v (c * c')) r z J * gm (r ≫ p) z ⊤ (b (c * c')) =
        (val (v c) r z J * gm (r ≫ p) z ⊤ (b c)) * (val (v c') (r ≫ τ c) z J * gm (r ≫ p) z ⊤ (b c')) := by
  have ex : ∀ c c', ∃ a : Γ(S₀, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ X) (z : Z) (J), Good L z J →
      val (v (c * c')) r z J = val (v c) r z J * val (v c') (r ≫ τ c) z J * gm (r ≫ p) z ⊤ a := fun c c' => by
    obtain ⟨a, ha⟩ := CommutatorPairing.exists_ratio hL (fun U _ g => by
        refine Eq.trans ?_ (Fintype.prod_sum_type _).symm
        simp only [Fin.prod_univ_two, Sum.elim_inl, Sum.elim_inr]
        show g (𝟙 X) ^ m * g (τ (c * c')) ^ (-m) =
          g (𝟙 X) ^ m * g (τ c) ^ (-m) * (g (τ c ≫ 𝟙 X) ^ m * g (τ c ≫ τ c') ^ (-m))
        rw [Category.comp_id, hτ]
        simp only [zpow_neg, _root_.mul_assoc, inv_mul_cancel_left]) p e he hp (hv (c * c'))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (hv c) (DVR.pullGen_isGen _ _ _ _ (hv c') (τ c)))
    exact ⟨a, fun Z r z J hJ => (ha Z r z J hJ).trans (congrArg (· * _) ((val_mul hJ _ _ _).trans
      (congrArg (val (v c) r z J * ·) (val_pull hJ _ _ _))))⟩
  choose a ha using ex
  have inj : ∀ u u' : Γ(S₀, ⊤)ˣ, (∀ (y : S₀) (J), Good L y J → gm (e ≫ p) y ⊤ u = gm (e ≫ p) y ⊤ u') → u = u' :=
    fun u u' h => unit_ext fun y _ => by
      choose J hJ using fun χ : S₀ ⟶ X => exists_chart hL (χ y)
      rw [← he]; exact h y J hJ
  obtain ⟨b, hb⟩ := exists_coboundary hU a (fun c c' => inj _ _ fun y J hJ => by
      have e₁ := ha c c' _ e y J hJ
      have e₂ := ha c' c _ e y J hJ
      rw [hc c c' _ e y J hJ] at e₁
      rw [mul_comm c' c, e₁] at e₂
      exact mul_left_cancel e₂) (fun c c' c'' => inj _ _ fun y J hJ => by
      have e₁ := ha c c' _ e y J hJ
      have e₂ := ha (c * c') c'' _ e y J hJ
      have e₃ := ha c' c'' _ (e ≫ τ c) y J hJ
      have e₄ := ha c (c' * c'') _ e y J hJ
      rw [_root_.mul_assoc c] at e₂
      rw [Category.assoc, Category.assoc, hτp, ← hτ] at e₃
      rw [map_mul, map_mul]
      apply Additive.ofMul.injective
      have a₁ := congrArg Additive.ofMul e₁
      have a₂ := congrArg Additive.ofMul e₂
      have a₃ := congrArg Additive.ofMul e₃
      have a₄ := congrArg Additive.ofMul e₄
      simp only [ofMul_mul] at a₁ a₂ a₃ a₄ ⊢
      linear_combination (norm := abel) a₃ + a₄ - a₁ - a₂)
  refine ⟨b, fun c c' Z r z J hJ => ?_⟩
  rw [ha c c' Z r z J hJ, _root_.mul_assoc, ← map_mul, mul_comm (a c c'), hb, map_mul, _root_.mul_mul_mul_comm]

end Bundles

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A]

abbrev transl (c : 𝟙_ (Over S) ⟶ A) : A.left ⟶ A.left := ((toUnit A ≫ c) * 𝟙 A).left

theorem transl_mul [IsCommMonObj A] (c c' : 𝟙_ (Over S) ⟶ A) : transl (c * c') = transl c ≫ transl c' := by
  rw [transl, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit,
    _root_.mul_assoc, mul_left_comm]

theorem transl_hom (c : 𝟙_ (Over S) ⟶ A) : transl c ≫ A.hom = A.hom := Over.w _

theorem transl_lift (c : 𝟙_ (Over S) ⟶ A) : transl c ≫ (lift (toUnit A) (𝟙 A)).left =
    (lift (toUnit A) (𝟙 A)).left ≫ (Out.translT A c).left := by
  rw [← Over.comp_left, ← Over.comp_left, CommutatorPairing.lift_translT, comp_lift, comp_toUnit, Category.comp_id]

theorem exists_gen_theta {L : LB A.left} (hL : L.IsLB) {m : ℤ} (θ : Out.ThetaGrp A L m (𝟙_ (Over S)))
    {c : 𝟙_ (Over S) ⟶ A} (hθ : θ.pt = c) :
    ∃ v : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, transl c] ![m, -m]), v.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ A.left) (z : Z) (J), Good L z J →
        val v r z J = CommPairing.tval θ (r ≫ (lift (toUnit A) (𝟙 A)).left) z J := by
  subst hθ
  obtain ⟨v, hv, e⟩ := exists_gen hL (K' := Fin 2) (φ' := ![𝟙 A.left, transl θ.pt]) (ε' := ![m, -m])
    (fun U _ h => (CommutatorPairing.prod_theta θ.pt (toUnit A) (𝟙 A) h).trans (by rw [Fin.prod_univ_two]; rfl))
    (LB.pullGen L (K := Fin 2) ![(snd _ A).left, (Out.translPt A θ.pt).left] ![m, -m] θ.φ
      (lift (toUnit A) (𝟙 A)).left) (DVR.pullGen_isGen _ _ _ _ θ.isGen _)
  exact ⟨v, hv, fun Z r z J hJ => (e Z r z J hJ).trans (val_pull hJ _ _ _)⟩

theorem exists_cocycle (hG : Out.GlobalFnsSt) (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB)
    [Subsingleton S] [Nonempty S] (hU : ∀ n : ℕ, 0 < n → ∀ y : Γ(S, ⊤)ˣ, ∃ x : Γ(S, ⊤)ˣ, x ^ n = y) (n : ℕ)
    {C : Type} [CommGroup C] (i : C →* (𝟙_ (Over S) ⟶ A))
    (hW : ∀ c c', Out.WeilIs A L n (i c) (i c') 1) :
    ∃ u : ∀ c, LB.Gen (LB.LinComb (lbPow L n) (K := Fin 2) ![𝟙 A.left, transl (i c)] ![1, -1]),
      (∀ c, (u c).IsGen) ∧ ∀ c c', LB.Gen.Corr (lbPow L n) _ _ _ _ (u (c * c'))
        (LB.mulGen (lbPow L n) _ _ _ _ (u c) (LB.pullGen (lbPow L n) _ _ (u c') (transl (i c)))) := by
  have := hA.comm
  have : Subsingleton (𝟙_ (Over S)).left := inferInstanceAs (Subsingleton S)
  have lifts : ∀ c, ∃ θ : Out.ThetaGrp A L n (𝟙_ (Over S)), θ.pt = i c := fun c => by
    obtain ⟨V, hp, ⟨θ, -, H, -⟩, -⟩ := hW c c (Classical.arbitrary S)
    obtain ⟨h, e⟩ := GlobalLift.exists_section hp
    obtain ⟨θ', e', -⟩ := CommPairing.exists_pull hL h θ
    rw [H, ← Category.assoc, e, Category.id_comp] at e'
    exact ⟨θ', e'⟩
  choose θ hθ using lifts
  choose v hv ev using fun c => exists_gen_theta hL (θ c) (hθ c)
  obtain ⟨b, hb⟩ := exists_rescale hL A.hom η[A].left (Over.w _) (hG S A hA).2 hU (fun c => transl (i c))
    (fun c c' => by rw [map_mul, transl_mul]) (fun c => transl_hom _) n v hv (fun c c' Z r z J hJ => by
      have H := (GlobalLift.weilIs_iff_commIsOf hG hA hL (θ c) (θ c') 1).1 (by rw [hθ, hθ]; exact hW c c')
      have e := (CommPairing.commIsOf_iff hL _ _ _).1 H Z (r ≫ (lift (toUnit A) (𝟙 A)).left) z J hJ
      rw [map_one, _root_.mul_one, hθ, hθ, Category.assoc, Category.assoc, ← transl_lift, ← transl_lift,
        ← Category.assoc, ← Category.assoc] at e
      rw [ev _ _ _ z J hJ, ev _ _ _ z J hJ, ev _ _ _ z J hJ, ev _ _ _ z J hJ]
      exact e)
  choose u hu eu using fun c => exists_gen_lbPow n (ε := ![1, -1]) (fun k => by fin_cases k <;> simp) (v c) (hv c)
    (pullU A.hom ⊤ (b c))
  refine ⟨u, hu, fun c c' => corr_of_val (DVR.linComb_isLB L hL _ _) fun y J hJ => ?_⟩
  have hJ' : Good L y (fun χ => J χ PUnit.unit) := fun χ => Set.mem_iInter.1 (hJ χ) PUnit.unit
  have g : ∀ (r : A.left ⟶ A.left) (a : Γ(S, ⊤)ˣ), gm r y ⊤ (pullU A.hom ⊤ a) = gm (r ≫ A.hom) y ⊤ a :=
    fun r a => gm_pull r A.hom y ⊤ trivial a
  refine Eq.trans ?_ ((val_mul hJ _ _ _).trans (congrArg (val (u c) (𝟙 _) y J * ·) (val_pull hJ _ _ _))).symm
  rw [eu _ _ _ y J hJ, eu _ _ _ y J hJ, eu _ _ _ y J hJ, g, g, g, Category.assoc, transl_hom]
  exact hb c c' _ (𝟙 _) y _ hJ'

end Group

theorem units_divisible (k : Type) [Field k] [IsAlgClosed k] (n : ℕ) (hn : 0 < n) (y : Γ(Sp k, ⊤)ˣ) :
    ∃ x : Γ(Sp k, ⊤)ˣ, x ^ n = y := by
  let e : Γ(Sp k, ⊤) ≃+* k := (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq (e y) hn
  have h : e.symm x ^ n = y := by rw [← map_pow, hx, RingEquiv.symm_apply_apply]
  have hu : IsUnit (e.symm x) := (isUnit_pow_iff hn.ne').1 (h ▸ y.isUnit)
  exact ⟨hu.unit, Units.ext h⟩

theorem exists_rational_ker {k k' : Type} [Field k] [IsAlgClosed k] [Field k'] {A B : Over (Sp k)} [GrpObj B]
    (ψ : A ⟶ B) [IsFinite ψ.left] (t : Sp k' ⟶ Sp k) (x : Over.mk t ⟶ A) (hx : x ≫ ψ = 1) :
    ∃ c : 𝟙_ (Over (Sp k)) ⟶ A, c ≫ ψ = 1 ∧ x = toUnit _ ≫ c := by
  let o : Sp k ⟶ B.left := η[B].left
  have w : x.left ≫ ψ.left = t ≫ o := congrArg (fun q => q.left) hx
  obtain ⟨c, hc, hy⟩ := exists_rational (pullback.snd ψ.left o) (pullback.lift x.left t w)
  rw [pullback.lift_snd] at hy
  have ho : o ≫ B.hom = 𝟙 _ := Over.w η[B]
  have h₁ : (c ≫ pullback.fst ψ.left o) ≫ ψ.left = o := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hc, Category.id_comp]
  refine ⟨Over.homMk (c ≫ pullback.fst ψ.left o) (by
    show (c ≫ pullback.fst ψ.left o) ≫ A.hom = 𝟙 _
    rw [← Over.w ψ, ← Category.assoc, h₁, ho]), Over.OverMorphism.ext ?_, Over.OverMorphism.ext ?_⟩
  · exact h₁.trans (Category.id_comp _).symm
  · show x.left = t ≫ c ≫ pullback.fst ψ.left o
    rw [← Category.assoc, hy, pullback.lift_fst]

end GlobalTheory.ThetaSplit

namespace GlobalTheory

open ThetaSplit in

theorem lbPow_descends_of_isotropic : Out.Laws → (∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [GrpObj B] (ψ : A ⟶ B) (C : Type) [CommGroup C] [Finite C] (i : C →* (𝟙_ (Over S) ⟶ A)) (L : LB A.left), L.IsLB → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), (∀ x : Over.mk t ⟶ A, x ≫ ψ = 1 ↔ ∃ c, x = toUnit _ ≫ i c) ∧ ∀ c, toUnit (Over.mk t) ≫ i c = 1 → c = 1) → ∀ (u : ∀ c, LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 A.left, ((toUnit A ≫ i c) * 𝟙 A).left] ![1, -1])), (∀ c, (u c).IsGen) → (∀ c c', LB.Gen.Corr L _ _ _ _ (u (c * c')) (LB.mulGen L _ _ _ _ (u c) (LB.pullGen L _ _ (u c') ((toUnit A ≫ i c) * 𝟙 A).left))) → ∃ M : LB B.left, M.IsLB ∧ LBIso L (M.pull ψ.left)) → ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Out.PolAV (Sp k)) (n : ℕ) (C : Subgroup (𝟙_ (Over (Sp k)) ⟶ P.A)) (B : Over (Sp k)) [GrpObj B] (ψ : P.A ⟶ B), 0 < n → (n : k) ≠ 0 → (∀ x ∈ C, x ^ n = 1) → (∀ x ∈ C, ∀ y ∈ C, Out.WeilIs P.A P.L n x y 1) → IsMonHom ψ → IsFinite ψ.left → Etale ψ.left → Surjective ψ.left → (∀ x : 𝟙_ (Over (Sp k)) ⟶ P.A, x ≫ ψ = 1 ↔ x ∈ C) → ∃ M : LB B.left, M.IsLB ∧ LBIso (lbPow P.L n) (M.pull ψ.left) := by
  intro hlaw hdesc k _ _ P n C B _ ψ hn hnk htor hW hψ hfin het hsurj hker
  have := P.isAb.comm
  letI : CommGroup C := { (inferInstance : Group C) with mul_comm := fun a b => Subtype.ext (mul_comm a.1 b.1) }
  have hfinT : Finite {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} := by
    have h := (hlaw.mulN (Sp k) P n hn).2.2.2.2 k (𝟙 _) hnk
    exact Nat.finite_of_card_ne_zero (h.trans_ne (pow_ne_zero _ hn.ne'))
  have : Finite C := Finite.of_injective
    (fun c : C => (⟨c.1, htor c.1 c.2⟩ : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1}))
    fun a b h => Subtype.ext (congrArg (fun q => q.1) h)
  obtain ⟨u, hu, hc⟩ := exists_cocycle hlaw.globalFns P.isAb P.isLB (units_divisible k) n C.subtype
    (fun c c' => hW c.1 c.2 c'.1 c'.2)
  refine hdesc (Sp k) P.A B ψ C C.subtype (lbPow P.L n) (DVR.linComb_isLB P.L P.isLB _ _) hψ hfin het hsurj
    (fun k' _ _ t => ⟨fun x => ⟨fun hx => ?_, ?_⟩, fun c h => ?_⟩) u hu hc
  · obtain ⟨c, h₁, h₂⟩ := exists_rational_ker ψ t x hx
    exact ⟨⟨c, (hker c).1 h₁⟩, h₂⟩
  · rintro ⟨c, rfl⟩
    rw [Category.assoc, (hker (C.subtype c)).2 c.2, MonObj.comp_one]
  · have : Epi t := epi_of_fields t
    refine Subtype.ext (Over.OverMorphism.ext ((cancel_epi t).1 ?_))
    have e : toUnit (Over.mk t) ≫ c.1 = toUnit (Over.mk t) ≫ (1 : 𝟙_ (Over (Sp k)) ⟶ P.A) :=
      h.trans (MonObj.comp_one _).symm
    exact congrArg (fun q => q.left) e

end GlobalTheory
