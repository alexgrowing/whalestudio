import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsRatioPoints
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ComparisonTorusInvariant

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory

namespace TorsionTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem exists_lift {R : Type} [CommRing R] (I : Ideal R) [IsAdicComplete I R] (a : ∀ e : ℕ, R ⧸ I ^ (e + 1))
    (h : ∀ e, Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1))) (a (e + 1)) = a e) :
    ∃ u : R, ∀ e, Ideal.Quotient.mk (I ^ (e + 1)) u = a e := by
  choose b hb using fun e => Ideal.Quotient.mk_surjective (a e)
  have h1 : ∀ e, b (e + 1) - b e ∈ I ^ (e + 1) := fun e => by
    rw [← Ideal.Quotient.eq, hb, ← h e, ← hb, Ideal.Quotient.factor_mk]
  have h2 : ∀ m n, m ≤ n → b n - b m ∈ I ^ (m + 1) := fun m n hmn => by
    induction n, hmn using Nat.le_induction with
    | base => simp
    | succ n hmn ih =>
      have := (I ^ (m + 1)).add_mem (Ideal.pow_le_pow_right (by omega) (h1 n)) ih
      rwa [sub_add_sub_cancel] at this
  obtain ⟨u, hu⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete (I := I) (M := R)) (f := b) (fun {m n} hmn => by
    rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem, ← neg_sub, neg_mem_iff]
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (h2 m n hmn))
  refine ⟨u, fun e => ?_⟩
  have := hu (e + 1)
  rw [smul_eq_mul, Ideal.mul_top, SModEq.sub_mem] at this
  rw [← hb, Ideal.Quotient.eq]
  have := (I ^ (e + 1)).sub_mem (h1 e) this
  rwa [sub_sub_sub_cancel_left] at this

theorem exists_unit_lift {R : Type} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsAdicComplete I R] (hI : I ≠ ⊤)
    (ρ : ∀ e : ℕ, Γ(Spec (CommRingCat.of (R ⧸ I ^ (e + 1))), ⊤)ˣ)
    (h : ∀ e z, gm (thickTrans R I e) z ⊤ (ρ (e + 1)) = gm (𝟙 _) z ⊤ (ρ e)) :
    ∃ u : Γ(Spec (CommRingCat.of R), ⊤)ˣ, ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))
      (z : Z), gm (r ≫ thick R I e) z ⊤ u = gm r z ⊤ (ρ e) := by
  have nat : ∀ {A B : CommRingCat.{0}} (f : A ⟶ B) (c : Γ(Spec A, ⊤)),
      (Scheme.ΓSpecIso B).hom.hom ((Spec.map f).appTop.hom c) = f.hom ((Scheme.ΓSpecIso A).hom.hom c) :=
    fun f c => congrArg (fun q => q.hom c) (Scheme.ΓSpecIso_naturality f)
  obtain ⟨u, hu⟩ := exists_lift I (fun e => (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (ρ e).val)
    (fun e => by
      refine (nat (CommRingCat.ofHom (Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (e + 1)))))
        (ρ (e + 1)).val).symm.trans (congrArg _ ?_)
      apply TopCat.Presheaf.section_ext (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))).sheaf ⊤
      intro z hz
      have := congrArg Units.val (h e z)
      rw [gm_val _ z ⊤ trivial, gm_val _ z ⊤ trivial] at this
      exact this)
  have hunit : IsUnit u := by
    by_contra hn
    have h0 : IsUnit (Ideal.Quotient.mk (I ^ (0 + 1)) u) := (hu 0).symm ▸ (ρ 0).isUnit.map _
    obtain ⟨v, hv⟩ := h0.exists_right_inv
    obtain ⟨v, rfl⟩ := Ideal.Quotient.mk_surjective v
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (I ^ (0 + 1))), Ideal.Quotient.eq, zero_add, pow_one] at hv
    have m₁ : u * v ∈ IsLocalRing.maximalIdeal R := Ideal.mul_mem_right _ _ hn
    have m₂ := (IsLocalRing.maximalIdeal R).sub_mem m₁ (IsLocalRing.le_maximalIdeal hI hv)
    rw [sub_sub_cancel] at m₂
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).2 m₂)
  refine ⟨(hunit.map (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom).unit, fun e Z r z => ?_⟩
  refine (gm_pull r (thick R I e) z ⊤ trivial _).symm.trans (congrArg (gm r z ⊤) (Units.ext ?_))
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom).1
  refine (nat (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))) _).trans (Eq.trans ?_ (hu e))
  exact congrArg (Ideal.Quotient.mk (I ^ (e + 1)))
    (congrArg (fun q => q.hom u) (Scheme.ΓSpecIso (CommRingCat.of R)).inv_hom_id)

theorem exists_ratio_gen {S T E B G : Scheme.{0}} {M : LB B} {L : LB G} {F : E ⟶ B} {F' : E ⟶ G}
    (w : LB.Iso (L.pull F') (M.pull F)) (hw : w.IsGen) {K : Type} [Fintype K] {ε : K → ℤ} (φ : K → (S ⟶ B))
    (φ' : K → (S ⟶ G)) (θ : T ⟶ S) (p : K → (T ⟶ E)) (hp : ∀ k, p k ≫ F = θ ≫ φ k) (hp' : ∀ k, p k ≫ F' = θ ≫ φ' k)
    (t : LB.Gen (LB.LinComb M φ ε)) (ht : t.IsGen) (t' : LB.Gen (LB.LinComb L φ' ε)) (ht' : t'.IsGen)
    (j₀ : K → M.ι) (h₀ : LB.wchart M φ j₀ = ⊤) (j₀' : K → L.ι) (h₀' : LB.wchart L φ' j₀' = ⊤) :
    ∃ ρ : Γ(T, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z) (j : K → M.ι) (j' : K → L.ι),
      (r ≫ θ) z ∈ LB.wchart M φ j → (r ≫ θ) z ∈ LB.wchart L φ' j' →
      gm r z ⊤ ρ * gm (r ≫ θ) z (LB.wchart M φ j) (t.s j) =
        gm (r ≫ θ) z (LB.wchart L φ' j') (t'.s j') * ∏ k, gw w (r ≫ p k) z (j k) (fun _ => j' k) ^ ε k := by
  have pg := (isGen_iff w).1 hw
  have m : ∀ (j : K → M.ι) (y : T), θ y ∈ LB.wchart M φ j → ∀ k, F (p k y) ∈ M.U (j k) := fun j y hy k =>
    (congrArg (fun g => g y ∈ M.U (j k)) (hp k)).mpr (Set.mem_iInter.1 hy k)
  have m' : ∀ (j : K → L.ι) (y : T), θ y ∈ LB.wchart L φ' j → ∀ k, F' (p k y) ∈ L.U (j k) := fun j y hy k =>
    (congrArg (fun g => g y ∈ L.U (j k)) (hp' k)).mpr (Set.mem_iInter.1 hy k)
  have a₀ : ∀ s, s ∈ LB.wchart M φ j₀ := fun s => by rw [h₀]; trivial
  have a₀' : ∀ s, s ∈ LB.wchart L φ' j₀' := fun s => by rw [h₀']; trivial
  have l₁ : (⊤ : T.Opens) ≤ θ ⁻¹ᵁ LB.wchart M φ j₀ := fun y _ => a₀ _
  have l₂ : (⊤ : T.Opens) ≤ θ ⁻¹ᵁ LB.wchart L φ' j₀' := fun y _ => a₀' _
  have l₃ : ∀ k, (⊤ : T.Opens) ≤ p k ⁻¹ᵁ ((M.pull F).U (fun _ => j₀ k) ⊓ (L.pull F').U (fun _ => j₀' k)) :=
    fun k y _ => ⟨mem_pull.2 (m j₀ y (a₀ _) k), mem_pull.2 (m' j₀' y (a₀' _) k)⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Γ(T, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ T) (z : Z), gm r z ⊤ ρ =
      gm (r ≫ θ) z (LB.wchart L φ' j₀') (t'.s j₀') * (∏ k, gw w (r ≫ p k) z (j₀ k) (fun _ => j₀' k) ^ ε k) *
        (gm (r ≫ θ) z (LB.wchart M φ j₀) (t.s j₀))⁻¹ :=
    ⟨res l₂ (pullU θ _ (t'.s j₀')) * (∏ k, res (l₃ k) (pullU (p k) _ (w.s (fun _ => j₀ k, fun _ => j₀' k))) ^ ε k) *
      (res l₁ (pullU θ _ (t.s j₀)))⁻¹, fun Z r z => (map_mul _ _ _).trans (congrArg₂ (· * ·)
        ((map_mul _ _ _).trans (congrArg₂ (· * ·)
          ((gm_res r z l₂ trivial _).trans (gm_pull r θ z _ (a₀' _) _))
          ((map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k)
            ((gm_res r z (l₃ k) trivial _).trans (gm_pull r (p k) z _ (l₃ k trivial) _)))))))
        ((map_inv _ _).trans (congrArg (·⁻¹) ((gm_res r z l₁ trivial _).trans (gm_pull r θ z _ (a₀ _) _)))))⟩
  refine ⟨ρ, fun Z r z j j' hj hj' => ?_⟩
  have e₁ := gen_trans ht (r ≫ θ) z hj (a₀ _)
  have e₂ := gen_trans ht' (r ≫ θ) z hj' (a₀' _)
  have e₃ : ∏ k, gw w (r ≫ p k) z (j k) (fun _ => j' k) ^ ε k = trF φ ε (r ≫ θ) z j j₀ * (trF φ' ε (r ≫ θ) z j' j₀')⁻¹ *
      ∏ k, gw w (r ≫ p k) z (j₀ k) (fun _ => j₀' k) ^ ε k := by
    rw [trF, trF, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun k _ => ?_
    rw [pg Z (r ≫ p k) z (j k) (j₀ k) (fun _ => j' k) (fun _ => j₀' k) (m j _ hj k) (m j₀ _ (a₀ _) k)
      (mem_pull.2 (m' j' _ hj' k)) (mem_pull.2 (m' j₀' _ (a₀' _) k)),
      gm_pull_g L F' (r ≫ p k) z (fun _ => j' k) (fun _ => j₀' k) (mem_pull.2 (m' j' _ hj' k))
        (mem_pull.2 (m' j₀' _ (a₀' _) k)), mul_zpow, mul_zpow, inv_zpow, Category.assoc, Category.assoc, hp, hp',
      Category.assoc, Category.assoc]
  rw [hρ, e₁, e₂, e₃]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_scale {X Y : Scheme.{0}} {M : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (t : LB.Gen (LB.LinComb M φ ε)) (ht : t.IsGen) (u : Γ(Y, ⊤)ˣ) :
    ∃ t' : LB.Gen (LB.LinComb M φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good M z J →
      val t' r z J = gm r z ⊤ u * val t r z J := by
  refine ⟨⟨fun j => res (le_top : (LB.LinComb M φ ε).U j ≤ ⊤) u * t.s j⟩, fun j j' => ?_, fun Z r z J hJ =>
    (map_mul _ _ _).trans (congrArg (· * _) (gm_res r z le_top (hJ.mem φ r) u))⟩
  refine (map_mul _ _ _).trans (Eq.trans ?_ (congrArg (_ * ·) (map_mul _ _ _).symm))
  rw [ht j j', mul_left_comm]
  exact congrArg (fun q => _ * (q * _)) ((DVR.res_res' _ _ u).trans (DVR.res_res' _ _ u).symm)

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}

omit [IsDomain R] in
theorem trans_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) :
    thickMap R I e G ≫ (fstG I (e + 1) G).left = (fstG I e G).left :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

omit [IsDomain R] in
theorem mono_fst (e : ℕ) (G : Over (Spec (CommRingCat.of R))) : Mono (fstG I e G).left := by
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  exact inferInstanceAs (Mono (pullback.fst G.hom (thick R I e)))

variable {D : DegData R I} {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G)

theorem gw_trans (e : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jL : U.LG.L.ι)
    (hM : (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM) (hL : (fstG I e G).left (r z) ∈ U.LG.L.U jL) :
    gw (U.w (e + 1)) (r ≫ thickMap R I e G) z jM (fun _ => jL) = gw (U.w e) r z jM (fun _ => jL) := by
  have hM' : (U.gt (e + 1)).pG.left (thickMap R I e G (r z)) ∈ D.toPre.P.L.U jM :=
    (congrArg (fun g => g (r z) ∈ D.toPre.P.L.U jM) (U.gt_q e)).mpr hM
  have hL' : (fstG I (e + 1) G).left (thickMap R I e G (r z)) ∈ U.LG.L.U jL :=
    (congrArg (fun g => g (r z) ∈ U.LG.L.U jL) (trans_fst e G)).mpr hL
  have hm : r z ∈ thickMap R I e G ⁻¹ᵁ ((D.toPre.P.L.pull (U.gt (e + 1)).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I (e + 1) G).left).U (fun _ => jL)) ⊓
      ((D.toPre.P.L.pull (U.gt e).pG.left).U (fun _ => jM) ⊓
        (U.LG.L.pull (fstG I e G).left).U (fun _ => jL)) :=
    ⟨⟨mem_pull.2 hM', mem_pull.2 hL'⟩, mem_pull.2 hM, mem_pull.2 hL⟩
  have H := congrArg (gm r z _) (U.w_compat e (fun _ => jM, fun _ => jL) _ inf_le_left inf_le_right)
  exact (gm_pull r (thickMap R I e G) z _ hm.1 ((U.w (e + 1)).s (fun _ => jM, fun _ => jL))).symm.trans
    ((gm_res r z inf_le_left hm _).symm.trans (H.trans (gm_res r z inf_le_right hm _)))

open TorusInvariance in

theorem exists_matching [IsLocalRing R] [IsAdicComplete I R] (hI : I ≠ ⊤) {K : Type} [Fintype K] (ε : K → ℤ)
    (φ : K → (Spec (CommRingCat.of R) ⟶ D.toPre.P.A.left)) (φ' : K → (Spec (CommRingCat.of R) ⟶ G.left))
    (p : ∀ e : ℕ, K → (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))) ⟶ (thickObj R I e G).left))
    (hp : ∀ e k, p e k ≫ (U.gt e).pG.left = thick R I e ≫ φ k)
    (hp' : ∀ e k, p e k ≫ (fstG I e G).left = thick R I e ≫ φ' k) :
    ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L φ ε)) (ν' : LB.Gen (LB.LinComb U.LG.L φ' ε)), ν.IsGen ∧ ν'.IsGen ∧
      ∀ (e : ℕ) (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (z : Z) (J) (N),
        Good D.toPre.P.L z J → Good U.LG.L z N →
        val ν (r ≫ thick R I e) z J = val ν' (r ≫ thick R I e) z N * ∏ k, wVal U e z J N (r ≫ p e k) ^ ε k := by
  obtain ⟨t, ht⟩ := DVR.exists_gen_of_local D.toPre.P.L D.toPre.P.isLB φ ε
  obtain ⟨t', ht'⟩ := DVR.exists_gen_of_local U.LG.L U.LG.isLB φ' ε
  obtain ⟨j₀, h₀⟩ := DVR.exists_chart_top D.toPre.P.L D.toPre.P.isLB φ ε
  obtain ⟨j₀', h₀'⟩ := DVR.exists_chart_top U.LG.L U.LG.isLB φ' ε
  choose ρ hρ using fun e => exists_ratio_gen (U.w e) (U.w_gen e) φ φ' (thick R I e) (p e) (hp e) (hp' e)
    t ht t' ht' j₀ h₀ j₀' h₀'
  have a₀ : ∀ s, s ∈ LB.wchart D.toPre.P.L φ j₀ := fun s => by rw [h₀]; trivial
  have a₀' : ∀ s, s ∈ LB.wchart U.LG.L φ' j₀' := fun s => by rw [h₀']; trivial
  obtain ⟨u, hu⟩ := exists_unit_lift I hI ρ (fun e z => by
    have c : ∀ k, thickTrans R I e ≫ p (e + 1) k = p e k ≫ thickMap R I e G := fun k => by
      have := mono_fst (I := I) (e + 1) G
      rw [← cancel_mono (fstG I (e + 1) G).left, Category.assoc, Category.assoc, hp', trans_fst, hp',
        ← Category.assoc, thickTrans_comp]
    have e₁ := hρ (e + 1) _ (thickTrans R I e) z j₀ j₀' (a₀ _) (a₀' _)
    have e₂ := hρ e _ (𝟙 _) z j₀ j₀' (a₀ _) (a₀' _)
    rw [thickTrans_comp] at e₁
    rw [Category.id_comp] at e₂
    refine mul_right_cancel (e₁.trans (Eq.trans (congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_)) e₂.symm))
    rw [c, Category.id_comp, gw_trans U e (p e k) z _ _
      ((congrArg (fun g => g z ∈ D.toPre.P.L.U (j₀ k)) (hp e k)).mpr (Set.mem_iInter.1 (a₀ _) k))
      ((congrArg (fun g => g z ∈ U.LG.L.U (j₀' k)) (hp' e k)).mpr (Set.mem_iInter.1 (a₀' _) k))])
  obtain ⟨ν, hν, vν⟩ := exists_scale t ht u
  refine ⟨ν, t', hν, ht', fun e Z r z J N hJ hN => ?_⟩
  rw [vν _ _ z J hJ, hu]
  refine (hρ e Z r z _ _ (hJ.mem φ _) (hN.mem φ' _)).trans (congrArg (_ * ·) (Finset.prod_congr rfl fun k _ => ?_))
  rw [wVal, Category.assoc, Category.assoc, Category.assoc, Category.assoc, hp, hp']

section Square

variable {S : Scheme.{0}} {H : Over S} [GrpObj H] [IsCommMonObj H] {L : RigLB H} (c : CubicalStr H L)

omit [IsCommMonObj H] in
theorem comp_pt {T T' : Over S} (ρ : T' ⟶ T) (x : 𝟙_ (Over S) ⟶ H) : ρ ≫ toUnit T ≫ x = toUnit T' ≫ x := by
  rw [← Category.assoc, comp_toUnit]

theorem exists_square (k : ℕ) (x : 𝟙_ (Over S) ⟶ H) (hx : x ^ k = 1)
    (ν : LB.Gen (LB.LinComb L.L (K := Fin 2) ![eSec H, x.left] (DegPre.lineε k))) (hν : ν.IsGen) :
    ∃ u : LB.Gen (LB.LinComb L.L (K := Fin 2) ![𝟙 H.left, (𝟙 H * (toUnit H ≫ x)).left] ![(k : ℤ), -(k : ℤ)]),
      u.IsGen ∧ ∀ (T : Over S) (ρ : T ⟶ H) (z : T.left) (J), Good L.L z J →
        val u ρ.left z J = cubN (cubV c z J) k 1 (toUnit T ≫ x) ρ * val ν (toUnit T).left z J := by
  have hm : (toUnit H ≫ x) ^ k = 1 :=
    (map_pow (preHom (toUnit H)) x k).symm.trans ((congrArg _ hx).trans (map_one (preHom (toUnit H))))
  obtain ⟨N, hN, vN⟩ := exists_cubN c 1 (toUnit H ≫ x) (𝟙 H) k
  obtain ⟨u, hu, vu⟩ := exists_gen L.isLB (φ' := ![𝟙 H.left, (𝟙 H * (toUnit H ≫ x)).left])
    (ε' := ![(k : ℤ), -(k : ℤ)]) (fun V _ h => by
      refine (Fintype.prod_sum_type _).trans ?_
      have e₁ : (toUnit H).left ≫ eSec H = (1 : H ⟶ H).left := rfl
      have e₂ : (toUnit H).left ≫ x.left = (toUnit H ≫ x).left := rfl
      rw [Fin.prod_univ_two, Fin.prod_univ_two, Fin.prod_univ_eight, mul_comm (𝟙 H)]
      simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val, hm, _root_.mul_one, _root_.one_mul, e₁, e₂, Over.id_left,
        DegPre.lineε]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_zpow]
      module)
    (LB.mulGen L.L _ _ _ _ N (LB.pullGen L.L _ _ ν (toUnit H).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.pullGen_isGen _ _ _ _ hν _))
  refine ⟨u, hu, fun T ρ z J hJ => (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((vN T ρ z J hJ).trans ?_) ((val_pull hJ _ _ _).trans ?_)))⟩
  · rw [MonObj.comp_one, comp_pt, Category.comp_id]
  · rw [← Over.comp_left, comp_toUnit]

end Square

theorem prod_famB (D : DegPre R) {T : Over (Spec (CommRingCat.of R))} (ρ : T ⟶ D.P.A) (α : D.X) (k : ℕ) {V : Type}
    [CommGroup V] (h : (T.left ⟶ D.P.A.left) → V) : ∏ i, h (ρ.left ≫ D.famφB α i) ^ DegPre.famε k i =
      h ρ.left ^ ((k : ℤ) - 1) * h (DVR.cP D T α * ρ).left * (h (DVR.cP D T α).left)⁻¹ * h (1 : T ⟶ D.P.A).left := by
  have e₀ : ρ.left ≫ D.famφB α 0 = ρ.left := Category.comp_id _
  have e₁ : ρ.left ≫ D.famφB α 1 = (DVR.cP D T α * ρ).left :=
    congrArg (fun q => q.left) ((MonObj.comp_mul ρ (𝟙 _) (DVR.cP D _ α)).trans
      (by rw [DVR.comp_cP, mul_comm, Category.comp_id]))
  have e₂ : ρ.left ≫ D.famφB α 2 = (DVR.cP D T α).left := congrArg (fun q => q.left) (DVR.comp_cP D ρ α)
  have e₃ : ρ.left ≫ D.famφB α 3 = (1 : T ⟶ D.P.A).left :=
    congrArg (fun q : T ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) ρ)
  rw [Fin.prod_univ_four, e₀, e₁, e₂, e₃]
  show _ ^ ((k : ℤ) - 1) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) = _
  rw [zpow_one, zpow_one, zpow_neg_one]

theorem exists_coeff_gen (D : DegPre R) (k : ℕ) (gp : GtPt D (𝟙_ (Over (Spec (CommRingCat.of R)))))
    (hb : gp.b ^ k = 1) (ν : LB.Gen (LB.LinComb D.P.L (K := Fin 2) ![eSec D.P.A, gp.b.left] (DegPre.lineε k)))
    (hν : ν.IsGen) (α : D.X) :
    ∃ u : LB.Gen (LB.LinComb D.P.L (Sum.elim (D.famφB α)
        (fun i => (𝟙 D.P.A * (toUnit D.P.A ≫ gp.b)).left ≫ D.famφB α i)) (DegPre.deltaε k)),
      u.IsGen ∧ ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.P.A) (z : T.left) (J), Good D.P.L z J →
        val u ρ.left z J = cubN (cubV D.cub z J) k 1 (toUnit T ≫ gp.b) ρ * val ν (toUnit T).left z J *
          (cubV D.cub z J (DVR.cP D T α) ρ (toUnit T ≫ gp.b))⁻¹ * val (gp.s α) (toUnit T).left z J := by
  obtain ⟨N, hN, vN⟩ := exists_square D.cub k gp.b hb ν hν
  obtain ⟨u, hu, vu⟩ := exists_gen D.P.isLB (φ' := Sum.elim (D.famφB α)
        (fun i => (𝟙 D.P.A * (toUnit D.P.A ≫ gp.b)).left ≫ D.famφB α i)) (ε' := DegPre.deltaε k) (fun V _ h => by
      have p₁ := prod_cub (DVR.cP D _ α) (𝟙 D.P.A) (toUnit D.P.A ≫ gp.b) h
      have p₂ : ∏ i, h ((toUnit D.P.A).left ≫ DegPre.gtφT D _ gp.b α i) ^ DegPre.gtε i =
          (h (DVR.cP D _ α * (toUnit D.P.A ≫ gp.b)).left)⁻¹ * h (DVR.cP D _ α).left * h (toUnit D.P.A ≫ gp.b).left *
            (h (1 : D.P.A ⟶ D.P.A).left)⁻¹ := by
        have e₀ : (toUnit D.P.A).left ≫ DegPre.gtφT D _ gp.b α 0 = (DVR.cP D _ α * (toUnit D.P.A ≫ gp.b)).left :=
          congrArg (fun q => q.left) ((MonObj.comp_mul (toUnit D.P.A) (DVR.cP D _ α) gp.b).trans
            (by rw [DVR.comp_cP]))
        have e₁ : (toUnit D.P.A).left ≫ DegPre.gtφT D _ gp.b α 1 = (DVR.cP D _ α).left :=
          congrArg (fun q => q.left) (DVR.comp_cP D (toUnit D.P.A) α)
        have e₃ : (toUnit D.P.A).left ≫ DegPre.gtφT D _ gp.b α 3 = (1 : D.P.A ⟶ D.P.A).left :=
          congrArg (fun q : _ ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (toUnit D.P.A))
        rw [Fin.prod_univ_four, e₀, e₁, e₃]
        show _ ^ (-1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (1 : ℤ) * _ ^ (-1 : ℤ) = _
        rw [zpow_one, zpow_one, zpow_neg_one, zpow_neg_one]; rfl
      have p₃ := prod_famB D (𝟙 _) α k h
      have p₄ := prod_famB D (𝟙 D.P.A * (toUnit D.P.A ≫ gp.b)) α k h
      simp only [Over.id_left, Category.id_comp] at p₃ p₁
      refine Eq.trans (DVR.prod_sum₂ (K := Fin 2 ⊕ thK) (K' := Fin 4) (U := V) _
        (DVR.prod_sum₂ (K := Fin 2) (K' := thK) (U := V) _ (Fin.prod_univ_two _) (DVR.prod_neg _ _ p₁)) p₂)
        (Eq.trans ?_ (DVR.prod_sum₂ (K := Fin 4) (K' := Fin 4) (U := V) _ p₃ (DVR.prod_neg _ _ p₄)).symm)
      rw [← _root_.mul_assoc (DVR.cP D _ α)]
      apply Additive.ofMul.injective
      simp only [Sum.elim_inl, Matrix.cons_val, ofMul_mul, ofMul_inv, ofMul_zpow]
      module)
    (LB.mulGen D.P.L _ _ _ _ (LB.mulGen D.P.L _ _ _ _ N (LB.invGen D.P.L _ _
      (LB.pullGen D.P.L (thφ D.P.A (x3 D.P.A)) thε D.cub.t
        (lift (DVR.cP D _ α) (lift (𝟙 D.P.A) (toUnit D.P.A ≫ gp.b))).left)))
      (LB.pullGen D.P.L _ _ (gp.s α) (toUnit D.P.A).left))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ hN (DVR.invGen_isGen _ _ _ _
      (DVR.pullGen_isGen _ _ _ _ D.cub.isGen _))) (DVR.pullGen_isGen _ _ _ _ (gp.isGen α) _))
  refine ⟨u, hu, fun T ρ z J hJ => (vu _ _ z J hJ).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vN T ρ z J hJ) ((val_inv _ _).trans (congrArg (·⁻¹)
      ((val_cub D.cub ρ hJ _ _ _).trans ?_))))) ((val_pull hJ _ _ _).trans ?_)))⟩
  · rw [DVR.comp_cP, comp_pt, Category.comp_id]
  · rw [← Over.comp_left, comp_toUnit]

theorem cubN_transfer {P Q Q' V : Type} [CommGroup P] [CommGroup Q] [CommGroup Q'] [CommGroup V] (p : P →* Q)
    (p' : P →* Q') (θ : Q → Q → Q → V) (θ' : Q' → Q' → Q' → V) (W : P → V)
    (h : ∀ a b c, θ (p a) (p b) (p c) = W (a * b * c) * (W (a * b))⁻¹ * (W (a * c))⁻¹ * (W (b * c))⁻¹ * W a * W b *
      W c * (W 1)⁻¹ * θ' (p' a) (p' b) (p' c)) (ξ y : P) (k : ℕ) :
    cubN θ k 1 (p ξ) (p y) = W (ξ ^ k * y) * (W y)⁻¹ * W 1 * (W (ξ ^ k))⁻¹ * (W (ξ * y) ^ k)⁻¹ * W ξ ^ k * W y ^ k *
      (W 1 ^ k)⁻¹ * cubN θ' k 1 (p' ξ) (p' y) := by
  induction k with
  | zero => simp [cubN]
  | succ k ih =>
    simp only [cubN, Finset.prod_range_succ, _root_.one_mul] at ih ⊢
    rw [ih, ← map_pow, ← map_pow, h, pow_succ ξ]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_pow]
    module

section Level

open TorusInvariance TorusCoord

variable (I G) in

def toG (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ G) :=
  MonoidHom.mk' (fun y => (Over.map (thick R I e)).map y ≫ fstG I e G) fun a b =>
    map_mul (pushHom (isGrpPullback_pullback G (thick R I e)) T) a b

def toB (e : ℕ) (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) :
    (T ⟶ thickObj R I e G) →* ((Over.map (thick R I e)).obj T ⟶ D.toPre.P.A) :=
  MonoidHom.mk' (fun y => im (U.gt e) y) fun a b => im_mul (U.gt e) a b

omit [IsDomain R] in

def cubT {H : Over (Spec (CommRingCat.of R))} [GrpObj H] [IsCommMonObj H] {L : RigLB H} (c : CubicalStr H L) {e : ℕ}
    (T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))) (z : T.left) (J : (T.left ⟶ H.left) → L.L.ι)
    (a b d : (Over.map (thick R I e)).obj T ⟶ H) : (T.left.presheaf.stalk z)ˣ :=
  cubV c (T := (Over.map (thick R I e)).obj T) z J a b d

theorem translate_val (hGF : GlobalFnsSt) {e : ℕ} (k : ℕ) {T : Over (Spec (CommRingCat.of (R ⧸ I ^ (e + 1))))}
    (y ξ : T ⟶ thickObj R I e G) (hξ : ξ ^ k = 1) {z : T.left} {J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    {N : (T.left ⟶ G.left) → U.LG.L.ι} (hJ : Good D.toPre.P.L z J) (hN : Good U.LG.L z N)
    {n n' : (T.left.presheaf.stalk z)ˣ}
    (hn : n = n' * (wVal U e z J N (1 : T ⟶ thickObj R I e G).left ^ (k : ℤ) * wVal U e z J N ξ.left ^ (-(k : ℤ))))
    (α : D.toPre.X) :
    wVal U e z J N y.left ^ k * (cubN (cubT U.cubG T z N) k 1 (toG I G e T ξ)
        (toG I G e T y) * n') * val ((U.gt e).t α) (y * ξ).left z J =
      wVal U e z J N (y * ξ).left ^ k * (cubN (cubT D.toPre.cub T z J) k 1
        (toB U e T ξ) (toB U e T y) * n * (cubT D.toPre.cub T z J
          (DVR.cP D.toPre _ α) (toB U e T y) (toB U e T ξ))⁻¹ * val ((U.gt e).t α) ξ.left z J) *
        val ((U.gt e).t α) y.left z J := by
  have h₁ := cubN_transfer (toB U e T) (toG I G e T) (cubT D.toPre.cub T z J)
    (cubT U.cubG T z N) (fun a => wVal U e z J N a.left)
    (fun a b c => (cube_val U ![a, b, c] hJ hN).trans (congrArg₂ (· * ·) (prod_psum a b c (wVal U e z J N)) rfl)) ξ y k
  have h₂ : val ((U.gt e).t α) (y * ξ).left z J * cubT D.toPre.cub T z J
      (DVR.cP D.toPre _ α) (toB U e T y) (toB U e T ξ) =
      val ((U.gt e).t α) y.left z J * val ((U.gt e).t α) ξ.left z J := val_t_mul_points (U.gt e) hGF α y ξ z J hJ
  rw [hξ, _root_.one_mul, mul_comm ξ y] at h₁
  rw [h₁, hn, eq_mul_inv_of_mul_eq h₂]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_pow, ofMul_zpow]
  module

end Level

section Main

open TorusInvariance TorusCoord

theorem expandsAt_translate (hGF : GlobalFnsSt) (k e : ℕ) (x : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G)
    (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))) (hx : x ^ k = 1)
    (xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G))
    (h₁ : xe ≫ fstG I e G = toUnit _ ≫ x) (h₂ : xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b)
    (h₃ : ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left)
      (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left))
    (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k)))
    (ν' : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![eSec G, x.left] (DegPre.lineε k)))
    (hν : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (z : Z) (J) (N),
        Good D.toPre.P.L z J → Good U.LG.L z N →
        val ν (r ≫ thick R I e) z J = val ν' (r ≫ thick R I e) z N *
          (wVal U e z J N (r ≫ eSec (thickObj R I e G)) ^ (k : ℤ) * wVal U e z J N (r ≫ xe.left) ^ (-(k : ℤ))))
    (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)]))
    (vL : ∀ (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ G) (z : T.left) (J), Good U.LG.L z J →
        val uL ρ.left z J = cubN (cubV U.cubG z J) k 1 (toUnit T ≫ x) ρ * val ν' (toUnit T).left z J)
    (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α)
      (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k)))
    (vM : ∀ α (T : Over (Spec (CommRingCat.of R))) (ρ : T ⟶ D.toPre.P.A) (z : T.left) (J), Good D.toPre.P.L z J →
        val (uM α) ρ.left z J = cubN (cubV D.toPre.cub z J) k 1 (toUnit T ≫ gp.b) ρ * val ν (toUnit T).left z J *
          (cubV D.toPre.cub z J (DVR.cP D.toPre T α) ρ (toUnit T ≫ gp.b))⁻¹ * val (gp.s α) (toUnit T).left z J)
    (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α)
    (hσ : GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL)
    (hf : ∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α))
    (hE : U.ExpandsAt e k σ f) : U.ExpandsAt e k σ' f' := by
  have : IsClosedImmersion (thick R I e) := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have := mono_fst (I := I) e G
  have hxe : xe.left ≫ (thickObj R I e G).hom = 𝟙 _ := by
    rw [← cancel_mono (thick R I e), Category.assoc, Category.id_comp]
    exact Over.w xe
  obtain ⟨ξ, hξ⟩ : ∃ ξ : thickObj R I e G ⟶ thickObj R I e G, ξ.left = (thickObj R I e G).hom ≫ xe.left :=
    ⟨Over.homMk ((thickObj R I e G).hom ≫ xe.left) ((Category.assoc _ _ _).trans
      ((congrArg ((thickObj R I e G).hom ≫ ·) hxe).trans (Category.comp_id _))), rfl⟩
  have u₀ : (toUnit ((Over.map (thick R I e)).obj (thickObj R I e G))).left =
      (thickObj R I e G).hom ≫ thick R I e := rfl
  have gξ : toG I G e _ ξ = toUnit _ ≫ x := Over.OverMorphism.ext (by
    show ξ.left ≫ (fstG I e G).left = ((thickObj R I e G).hom ≫ thick R I e) ≫ x.left
    rw [hξ, Category.assoc, Category.assoc]
    exact congrArg (fun q => (thickObj R I e G).hom ≫ q.left) h₁)
  have bξ : toB U e _ ξ = toUnit _ ≫ gp.b := Over.OverMorphism.ext (by
    show ξ.left ≫ (U.gt e).pG.left = ((thickObj R I e G).hom ≫ thick R I e) ≫ gp.b.left
    rw [hξ, Category.assoc, Category.assoc]
    exact congrArg (fun q => (thickObj R I e G).hom ≫ q.left) h₂)
  have g₁ : toG I G e _ (𝟙 (thickObj R I e G)) = fstG I e G := Over.OverMorphism.ext (Category.id_comp _)
  have b₁ : toB U e _ (𝟙 (thickObj R I e G)) = (U.gt e).pG := Over.OverMorphism.ext (Category.id_comp _)
  have hk : ξ ^ k = 1 := by
    have : toG I G e _ (ξ ^ k) = toG I G e _ 1 := by
      rw [map_pow, map_one, gξ]
      exact (map_pow (preHom (toUnit _)) x k).symm.trans ((congrArg _ hx).trans (map_one (preHom (toUnit _))))
    exact Over.OverMorphism.ext ((cancel_mono (fstG I e G).left).1 (congrArg (fun q => q.left) this))
  have tg : (𝟙 (thickObj R I e G) * ξ).left ≫ DVR.fGl I G e = DVR.fGl I G e ≫ (𝟙 G * (toUnit G ≫ x)).left := by
    have : toG I G e _ (𝟙 (thickObj R I e G) * ξ) = fstG I e G ≫ (𝟙 G * (toUnit G ≫ x)) := by
      rw [map_mul, g₁, gξ, MonObj.comp_mul, comp_pt, Category.comp_id]
    exact congrArg (fun q => q.left) this
  have tb : (𝟙 (thickObj R I e G) * ξ).left ≫ DVR.pGl U e =
      DVR.pGl U e ≫ (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left := by
    have : toB U e _ (𝟙 (thickObj R I e G) * ξ) = (U.gt e).pG ≫ (𝟙 _ * (toUnit D.toPre.P.A ≫ gp.b)) := by
      rw [map_mul, b₁, bξ, MonObj.comp_mul, comp_pt, Category.comp_id]
    exact congrArg (fun q => q.left) this
  obtain ⟨S, hS⟩ := DVR.expandsAt_val U e k σ f hE
  refine DVR.expandsAt_of_val U e k σ' f' S fun z J hJ => ?_
  obtain ⟨S₀, S₁⟩ := hS _ (𝟙 (thickObj R I e G) * ξ).left z J hJ
  have F : ∀ α, sval (f' α) (DVR.pGl U e) z J = sval (f α) ((𝟙 (thickObj R I e G) * ξ).left ≫ DVR.pGl U e) z J *
      (val (uM α) (DVR.pGl U e) z J).val := fun α => by
    rw [tb]
    exact (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ _).1 (hf α) _ _ z J hJ
  refine ⟨fun α hα => by rw [F, S₀ α hα, zero_mul], fun jL hL => ?_⟩
  obtain ⟨N, hN, eN⟩ := exists_good U.LG.L U.LG.isLB z (K := PUnit) (fun _ => DVR.fGl I G e) (fun _ => jL)
    (fun _ _ _ => rfl) (fun _ => hL)
  obtain rfl : N (DVR.fGl I G e) = jL := eN PUnit.unit
  have sv : ∀ (s : H0 U.LG.L k) (q : (thickObj R I e G).left ⟶ G.left), DVR.sv U k s q z (N q) = sval s q z N :=
    fun s q => (sval_of s q z N (fun _ => N q) (fun _ => congrArg N (Category.comp_id _))).symm
  have sL : sval σ' (DVR.fGl I G e) z N = sval σ ((𝟙 (thickObj R I e G) * ξ).left ≫ DVR.fGl I G e) z N *
      (val uL (DVR.fGl I G e) z N).val := by
    rw [tg]
    exact (secRel_iff U.LG.isLB _ _ _ _ _ _ _ _ _ _).1 hσ _ _ z N hN
  have E := S₁ (N ((𝟙 (thickObj R I e G) * ξ).left ≫ DVR.fGl I G e)) (hN _)
  rw [sv] at E
  have w₁ : DVR.wv U e (𝟙 _) z (J (DVR.pGl U e)) (N (DVR.fGl I G e)) = wVal U e z J N (𝟙 (thickObj R I e G) :).left := by
    rw [wVal, Over.id_left, Category.id_comp, Category.id_comp]; rfl
  have key : ∀ α, DVR.wv U e (𝟙 _) z (J (DVR.pGl U e)) (N (DVR.fGl I G e)) ^ k * val uL (DVR.fGl I G e) z N *
      val (DVR.tG U e α) (𝟙 (thickObj R I e G) * ξ).left z J =
      wVal U e z J N (𝟙 (thickObj R I e G) * ξ).left ^ k * val (uM α) (DVR.pGl U e) z J *
        val (DVR.tG U e α) (𝟙 _) z J := fun α => by
    have a := translate_val U hGF k (𝟙 (thickObj R I e G)) ξ hk hJ hN
      ((hν _ (thickObj R I e G).hom z J N hJ hN).trans (by rw [hξ]; rfl)) α
    have t : val ((U.gt e).t α) ξ.left z J = val (gp.s α) ((thickObj R I e G).hom ≫ thick R I e) z J := by
      rw [hξ]
      exact (val_pull hJ _ _ _).symm.trans ((val_corr hJ (h₃ α) _).trans (val_pull hJ _ _ _))
    rw [g₁, b₁, gξ, bξ, t] at a
    rw [w₁, vL _ (fstG I e G) z N hN, vM α _ (U.gt e).pG z J hJ]
    exact a
  refine (wVal U e z J N (𝟙 (thickObj R I e G) * ξ).left ^ k).mul_right_inj.1 ?_
  rw [sv, sL, mul_left_comm, ← _root_.mul_assoc (wVal U e z J N (𝟙 (thickObj R I e G) * ξ).left ^ k).val]
  refine (congrArg (fun q => _ * (q * _)) E).trans ?_
  rw [Finset.sum_mul, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  have := congrArg Units.val (key α)
  simp only [Units.val_mul] at this
  rw [F]
  linear_combination sval (f α) ((𝟙 (thickObj R I e G) * ξ).left ≫ DVR.pGl U e) z J * this

theorem eSec_pG (e : ℕ) :
    eSec (thickObj R I e G) ≫ (U.gt e).pG.left = thick R I e ≫ eSec D.toPre.P.A := by
  have := (U.gt e).q_hom
  have h : eSec (thickObj R I e G) ≫ (U.gt e).q.left = eSec (thickObj R I e D.toPre.P.A) :=
    congrArg (fun q => q.left) (IsMonHom.one_hom (U.gt e).q)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.fst D.toPre.P.A.hom (thick R I e)) h).trans
    (cubeMapOf (isGrpPullback_pullback D.toPre.P.A (thick R I e))).e_comm)

end Main

end TorsionTranslate

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TorsionTranslate in

theorem expandsAt_translate_torsion : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → I ≠ ⊤ → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (x : (𝟙_ (Over (Spec (CommRingCat.of R)))) ⟶ G) (gp : GtPt D.toPre (𝟙_ (Over (Spec (CommRingCat.of R))))), x ^ k = 1 → gp.b ^ k = 1 → (∀ e : ℕ, ∃ xe : Over.mk (thick R I e) ⟶ (Over.map (thick R I e)).obj (thickObj R I e G), xe ≫ fstG I e G = toUnit _ ≫ x ∧ xe ≫ (U.gt e).pG = toUnit _ ≫ gp.b ∧ ∀ χ, LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ ((U.gt e).t χ) xe.left) (LB.pullGen D.toPre.P.L _ _ (gp.s χ) (toUnit (Over.mk (thick R I e))).left)) → ∃ (ν : LB.Gen (LB.LinComb D.toPre.P.L (K := Fin 2) ![eSec D.toPre.P.A, gp.b.left] (DegPre.lineε k))) (uL : LB.Gen (LB.LinComb U.LG.L (K := Fin 2) ![𝟙 G.left, (𝟙 G * (toUnit G ≫ x)).left] ![(k : ℤ), -(k : ℤ)])) (uM : ∀ α, LB.Gen (LB.LinComb D.toPre.P.L (Sum.elim (D.toPre.famφB α) (fun i => (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left ≫ D.toPre.famφB α i)) (DegPre.deltaε k))), ν.IsGen ∧ uL.IsGen ∧ (∀ α, (uM α).IsGen ∧ LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ (uM α) (eSec D.toPre.P.A)) (LB.mulGen D.toPre.P.L _ _ _ _ (gp.s α) ν)) ∧ ∀ (σ σ' : H0 U.LG.L k) (f f' : ∀ α, D.toPre.SecB k α), GeneratorPullback.SecRel U.LG.L _ _ σ' _ _ σ (𝟙 G * (toUnit G ≫ x)).left _ _ uL → (∀ α, GeneratorPullback.SecRel D.toPre.P.L _ _ (f' α) _ _ (f α) (𝟙 D.toPre.P.A * (toUnit D.toPre.P.A ≫ gp.b)).left _ _ (uM α)) → ∀ e, U.ExpandsAt e k σ f → U.ExpandsAt e k σ' f' := by
  intro hGF R _ _ _ I hR hI D A G _ _ U k x gp hx hb H
  have := hR.2.2.2
  choose xe h₁ h₂ h₃ using H
  obtain ⟨ν, ν', hν, hν', vν⟩ := exists_matching U hI (DegPre.lineε k) ![eSec D.toPre.P.A, gp.b.left] ![eSec G, x.left]
    (fun e => ![eSec (thickObj R I e G), (xe e).left])
    (fun e => Fin.forall_fin_two.2 ⟨eSec_pG U e, congrArg (fun q => q.left) (h₂ e)⟩)
    (fun e => Fin.forall_fin_two.2 ⟨(cubeMapOf (isGrpPullback_pullback G (thick R I e))).e_comm,
      congrArg (fun q => q.left) (h₁ e)⟩)
  obtain ⟨uL, huL, vL⟩ := exists_square U.cubG k x hx ν' hν'
  choose uM huM vM using exists_coeff_gen D.toPre k gp hb ν hν
  refine ⟨ν, uL, uM, hν, huL, fun α => ⟨huM α, corr_of_val D.toPre.P.isLB fun z J hJ => ?_⟩,
    fun σ σ' f f' hσ hf e => expandsAt_translate U hGF k e x gp hx (xe e) (h₁ e) (h₂ e) (h₃ e) ν ν'
      (fun Z r z J N hJ hN => (vν e Z r z J N hJ hN).trans (congrArg (_ * ·) (Fin.prod_univ_two _)))
      uL vL uM vM σ σ' f f' hσ hf⟩
  have a := vM α _ (1 : 𝟙_ _ ⟶ D.toPre.P.A) z J hJ
  rw [(isCub_cubV D.toPre.cub hJ).N_one, (isCub_cubV D.toPre.cub hJ).face₂, inv_one, _root_.one_mul, _root_.mul_one] at a
  exact (val_pull hJ _ _ _).trans (a.trans ((mul_comm _ _).trans (val_mul hJ _ _ _).symm))

end GlobalTheory
