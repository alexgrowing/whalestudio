import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.TorsionFixedAut

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

section Twist

variable {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem isGen_of_germs {φ : K → (Y ⟶ X)} {ε : K → ℤ} (t : LB.Gen (LB.LinComb L φ ε))
    (h : ∀ (y : Y) (j j' : K → L.ι), y ∈ LB.wchart L φ j → y ∈ LB.wchart L φ j' →
      gm (𝟙 Y) y (LB.wchart L φ j) (t.s j) = trF φ ε (𝟙 Y) y j j' * gm (𝟙 Y) y (LB.wchart L φ j') (t.s j')) :
    t.IsGen := fun j j' => unit_ext fun y hy =>
  ((gm_res (𝟙 Y) y _ hy _).trans (h y j j' hy.1 hy.2)).trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linComb L φ ε (𝟙 Y) y j j' hy.1 hy.2) (gm_res (𝟙 Y) y _ hy _))).symm

variable {σ : X ⟶ X} (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ, 𝟙 X] ![1, -1]))

def twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) :
    LB.Gen (LB.LinComb L (K := K × Fin 2) (fun p => φ p.1 ≫ ![σ, 𝟙 X] p.2) (fun p => -ε p.1 * ![1, -1] p.2)) where
  s := fun j => ∏ k : K,
    res ((fun _ hy => Set.mem_iInter.2 fun b => Set.mem_iInter.1 hy (k, b)) :
        LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j ≤
          LB.wchart L (fun b => φ k ≫ ![σ, 𝟙 X] b) (fun b => j (k, b)))
      ((LB.pullGen L _ _ c (φ k)).s (fun b => j (k, b))) ^ (-ε k)

theorem gm_twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (j : K × Fin 2 → L.ι)
    (hj : r z ∈ LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) :
    gm r z (LB.wchart L (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2) j) ((twistGen c φ ε).s j) =
      ∏ k, gm r z (LB.wchart L (fun b => φ k ≫ ![σ, 𝟙 X] b) (fun b => j (k, b)))
        ((LB.pullGen L _ _ c (φ k)).s (fun b => j (k, b))) ^ (-ε k) :=
  (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans
    (congrArg (· ^ (-ε k)) (gm_res r z _ hj _)))

theorem twistGen_isGen (hc : c.IsGen) (φ : K → (Y ⟶ X)) (ε : K → ℤ) : (twistGen c φ ε).IsGen := by
  refine isGen_of_germs _ fun y j j' hj hj' => ?_
  rw [gm_twistGen c φ ε (𝟙 Y) y j hj, gm_twistGen c φ ε (𝟙 Y) y j' hj', trF, Fintype.prod_prod_type,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [gen_trans (DVR.pullGen_isGen _ _ _ _ hc (φ k)) (𝟙 Y) y (j := fun b => j (k, b)) (j' := fun b => j' (k, b))
    (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj (k, b)) (Set.mem_iInter.2 fun b => Set.mem_iInter.1 hj' (k, b)),
    mul_zpow, trF, ← Finset.prod_zpow]
  congr 1
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← zpow_mul, mul_comm]

theorem val_twistGen (φ : K → (Y ⟶ X)) (ε : K → ℤ) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J} (hJ : Good L z J) :
    val (twistGen c φ ε) r z J = (∏ k, val c (r ≫ φ k) z J ^ ε k)⁻¹ := by
  refine (gm_twistGen c φ ε r z _ (hJ.mem _ r)).trans ?_
  rw [← Finset.prod_inv_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  rw [← zpow_neg, ← val_pull hJ c (φ k) r]
  rfl

theorem formEq_twist (φ' : K → (Y' ⟶ X)) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (h : Y ⟶ Y')
    (hh : ∀ k, h ≫ φ' k = φ k ≫ σ) :
    FormEq (Sum.elim (fun k => h ≫ φ' k) (fun p : K × Fin 2 => φ p.1 ≫ ![σ, 𝟙 X] p.2))
      (Sum.elim ε (fun p : K × Fin 2 => -ε p.1 * ![1, -1] p.2)) φ ε := fun U _ f => by
  rw [Fintype.prod_sum_type, Fintype.prod_prod_type, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun k _ => ?_
  simp [hh k]

theorem exists_twist_sec (hL : L.IsLB) (hc : c.IsGen) {φ' : K → (Y' ⟶ X)} (φ : K → (Y ⟶ X)) {ε : K → ℤ}
    (h : Y ⟶ Y') (hh : ∀ k, h ≫ φ' k = φ k ≫ σ) (s : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ s' : LB.Sec (LB.LinComb L φ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      sval s' r z J = sval s (r ≫ h) z J * ((∏ k, val c (r ≫ φ k) z J ^ ε k)⁻¹).val := by
  obtain ⟨s', hs'⟩ := exists_sec hL (formEq_twist φ' φ ε h hh) (pullMulSec s h _ (twistGen_isGen c hc φ ε))
  refine ⟨s', fun Z r z J hJ => ?_⟩
  rw [hs' Z r z J hJ, sval_pullMulSec s h _ _ r z hJ, val_twistGen c φ ε r z hJ]

theorem exists_twist_gen (hL : L.IsLB) (hc : c.IsGen) {φ' : K → (Y' ⟶ X)} (φ : K → (Y ⟶ X)) {ε : K → ℤ}
    (h : Y ⟶ Y') (hh : ∀ k, h ≫ φ' k = φ k ≫ σ) (t : LB.Gen (LB.LinComb L φ' ε)) (ht : t.IsGen) :
    ∃ t' : LB.Gen (LB.LinComb L φ ε), t'.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J), Good L z J →
      val t' r z J = val t (r ≫ h) z J * (∏ k, val c (r ≫ φ k) z J ^ ε k)⁻¹ := by
  obtain ⟨t', ht', hv⟩ := exists_gen hL (formEq_twist φ' φ ε h hh)
    (LB.mulGen L _ _ _ _ (LB.pullGen L _ _ t h) (twistGen c φ ε))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht h) (twistGen_isGen c hc φ ε))
  refine ⟨t', ht', fun Z r z J hJ => ?_⟩
  rw [hv Z r z J hJ, val_mul hJ, val_pull hJ, val_twistGen c φ ε r z hJ]

theorem exists_gen_pull (M : LB X) (t : LB.Gen M) (ht : t.IsGen) (f : Y ⟶ X) :
    ∃ u : LB.Gen (M.pull f), u.IsGen := by
  refine ⟨⟨fun j => res (LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit) (pullU f _ (t.s (j PUnit.unit)))⟩,
    isGen_of_germs _ fun y j j' hj hj' => ?_⟩
  have v : ∀ j : PUnit → M.ι, y ∈ LB.wchart M (fun _ : PUnit => f) j →
      gm (𝟙 Y) y (LB.wchart M (fun _ : PUnit => f) j)
        (res (LB.wchart_le M (fun _ : PUnit => f) j PUnit.unit) (pullU f _ (t.s (j PUnit.unit)))) =
      gm (𝟙 Y ≫ f) y _ (t.s (j PUnit.unit)) := fun j hj =>
    (gm_res _ y _ hj _).trans (gm_pull _ f y _ (Set.mem_iInter.1 hj PUnit.unit) _)
  refine (v j hj).trans (Eq.trans ?_ (congrArg _ (v j' hj')).symm)
  have hm : (𝟙 Y ≫ f) y ∈ M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit) :=
    ⟨Set.mem_iInter.1 hj PUnit.unit, Set.mem_iInter.1 hj' PUnit.unit⟩
  rw [trF, Fintype.prod_unique, zpow_one]
  exact (gm_res _ y _ hm _).symm.trans ((congrArg (gm _ y _) (ht _ _)).trans ((map_mul _ _ _).trans
    (congrArg _ (gm_res _ y _ hm _))))

theorem isUnit_gs_iff {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    IsUnit (gs r z U a) ↔ r z ∈ Y.basicOpen a := by
  rw [gs_eq r z _ h, ← Scheme.Hom.germ_stalkMap_apply, isUnit_map_iff]
  exact (Y.mem_basicOpen a (r z) h).symm

theorem isUnit_sval_iff {φ : K → (Y ⟶ X)} {ε : K → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) {Z : Scheme.{0}} (r : Z ⟶ Y)
    (z : Z) {J} (hJ : Good L z J) : IsUnit (sval s r z J) ↔ r z ∈ nonzeroLocus s := by
  have key : ∀ (j : K → L.ι) (hj : r z ∈ LB.wchart L φ j),
      IsUnit (gs r z (LB.wchart L φ j) (s.f j)) ↔ r z ∈ Y.basicOpen (s.f j) := fun j hj =>
    isUnit_gs_iff r z _ hj _
  constructor
  · intro h
    exact Opens.mem_iSup.2 ⟨_, (key _ (hJ.mem φ r)).1 h⟩
  · intro h
    obtain ⟨j, hj⟩ := Opens.mem_iSup.1 h
    have hj' : r z ∈ LB.wchart L φ j := Y.basicOpen_le _ hj
    have := (key j hj').2 hj
    rw [sec_trans s r z hj' (hJ.mem φ r)] at this
    exact isUnit_of_mul_isUnit_right this

end Twist

section Embed

variable {X Y B : Scheme.{0}} {L : LB X} {K : Type} [Fintype K]

theorem eq_id_of_sval {φ : K → (Y ⟶ X)} {ε : K → ℤ} {ι' : Type} (s : ι' → LB.Sec (LB.LinComb L φ ε))
    (b : Y ⟶ B) (f : Y ⟶ Y) (hf : f ≫ b = b) (hcov : ⨆ i, nonzeroLocus (s i) = ⊤)
    (haff : ∀ i, IsAffineOpen (nonzeroLocus (s i)) ∧ ∃ r : ι' → Γ(Y, nonzeroLocus (s i)),
      (∀ j k, (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s j).f k) =
        (Y.presheaf.map (homOfLE (inf_le_left :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ nonzeroLocus (s i))).op).hom (r j) *
        (Y.presheaf.map (homOfLE (inf_le_right :
          nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U k ≤ (LB.LinComb L φ ε).U k)).op).hom ((s i).f k)) ∧
      Function.Surjective (MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r))
    (h : ∀ y : Y, ∃ J, Good L y J ∧ ∃ u, ∀ i, sval (s i) f y J = u * sval (s i) (𝟙 Y) y J) : f = 𝟙 Y := by
  have cov : ∀ y : Y, ∃ i, y ∈ nonzeroLocus (s i) := fun y =>
    Opens.mem_iSup.1 (show y ∈ ⨆ i, nonzeroLocus (s i) by rw [hcov]; trivial)
  choose J hJ u hu using h
  have uu : ∀ y, IsUnit (u y) := fun y => by
    obtain ⟨i, hi⟩ := cov (f y)
    have := (isUnit_sval_iff (s i) f y (hJ y)).2 hi
    rw [hu] at this
    exact isUnit_of_mul_isUnit_left this
  have le : ∀ i, nonzeroLocus (s i) ≤ f ⁻¹ᵁ nonzeroLocus (s i) := fun i y hy => by
    refine (isUnit_sval_iff (s i) f y (hJ y)).1 ?_
    rw [hu]
    exact (uu y).mul ((isUnit_sval_iff (s i) (𝟙 Y) y (hJ y)).2 hy)
  refine Scheme.hom_ext_of_forall _ _ fun y => ?_
  obtain ⟨i, hi⟩ := cov y
  refine ⟨nonzeroLocus (s i), hi, ?_⟩
  obtain ⟨hA, r, hr, hs⟩ := haff i
  have ratio : ∀ (g : Y ⟶ Y) (z : Y) (j), g z ∈ nonzeroLocus (s i) →
      sval (s j) g z (J z) = gs g z _ (r j) * sval (s i) g z (J z) := fun g z j hz => by
    have hm : g z ∈ nonzeroLocus (s i) ⊓ (LB.LinComb L φ ε).U (fun k => J z (g ≫ φ k)) := ⟨hz, (hJ z).mem φ g⟩
    exact (gs_res g z _ hm _).symm.trans ((congrArg (gs g z _) (hr j _)).trans ((gs_mul g z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_res g z _ hm _) (gs_res g z _ hm _))))
  have fixr : ∀ j, (f.appLE _ _ (le i)).hom (r j) = r j := fun j => fn_ext fun z hz => by
    have e₁ : gs (𝟙 Y) z _ ((f.appLE _ _ (le i)).hom (r j)) = gs f z _ (r j) :=
      (gs_res (𝟙 Y) z (le i) hz _).trans ((gs_pull (𝟙 Y) f z _ (le i (x := z) hz) _).trans (by rw [Category.id_comp]))
    have e₂ := ratio f z j (le i hz)
    rw [hu, hu, ratio (𝟙 Y) z j hz, ← _root_.mul_assoc, ← _root_.mul_assoc, mul_comm (u z)] at e₂
    rw [e₁]
    exact ((uu z).mul_right_cancel (((isUnit_sval_iff (s i) (𝟙 Y) z (hJ z)).2 hz).mul_right_cancel e₂)).symm
  have fixc : b.appLE ⊤ (nonzeroLocus (s i)) le_top ≫ f.appLE _ _ (le i) = b.appLE ⊤ (nonzeroLocus (s i)) le_top := by
    refine (Scheme.Hom.appLE_comp_appLE f b ⊤ _ _ le_top (le i)).trans ?_
    simp only [hf]
  have fix : f.appLE _ _ (le i) = 𝟙 _ := by
    ext a
    obtain ⟨p, rfl⟩ := hs a
    have : (f.appLE _ _ (le i)).hom.comp (MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r) =
        MvPolynomial.eval₂Hom (b.appLE ⊤ (nonzeroLocus (s i)) le_top).hom r := by
      refine MvPolynomial.ringHom_ext (fun a => ?_) (fun j => ?_)
      · simpa using congrArg (fun q => q.hom a) fixc
      · simpa using fixr j
    exact congrArg (fun q => q p) this
  have e := IsAffineOpen.SpecMap_appLE_fromSpec f hA hA (le i)
  rw [fix, Spec.map_id, Category.id_comp, ← hA.isoSpec_inv_ι, Category.assoc, cancel_epi] at e
  rw [Category.comp_id, ← e]

end Embed

theorem exists_eigenvector {K R M : Type} [Field K] [IsAlgClosed K] [CommRing R] (e : K ≃+* R) [AddCommGroup M]
    [Module R M] (hM : Module.finrank R M ≠ 0) (f : M →ₗ[R] M) : ∃ (a : R) (v : M), v ≠ 0 ∧ f v = a • v := by
  letI : Field R := (e.symm.isField (Field.toIsField K)).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv K R e
  haveI : Module.Finite R M := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero hM)
  haveI : Nontrivial M := Module.nontrivial_of_finrank_pos (R := R) (Nat.pos_of_ne_zero hM)
  obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue (K := R) f
  obtain ⟨v, hv⟩ := ha.exists_hasEigenvector
  exact ⟨a, v, hv.2, hv.apply_eq_smul⟩

section Theta

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} {T : Over S}

def secVal {k : ℤ} (s : LB.Sec (LPow A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : Z.presheaf.stalk z :=
  sval (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s r z J

def thetaVal {k : ℤ} {x : T ⟶ A} (t : LB.Gen (thetaLB A L k x)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (translPt A x).left]) (ε := ![k, -k]) t r z J

def negVal {k : ℤ} (t : LB.Gen (negLB A L k T)) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z)
    (J : (Z ⟶ A.left) → L.ι) : (Z.presheaf.stalk z)ˣ :=
  val (L := L) (φ := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left]) (ε := ![k, -k]) t r z J

theorem sval_isActOf {k : ℤ} {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)} (h : IsActOf A L k θ s s')
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) :
    secVal s' r z J =
      (thetaVal θ.φ r z J).val *
        secVal s (r ≫ (translT A θ.pt).left) z J := by
  have e : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left, translT, lift_snd]
  refine Eq.trans ?_ (congrArg (_ * ·) (sval_of (L := L) (φ := fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) s
    (r ≫ (translT A θ.pt).left) z J (fun _ => J (r ≫ (translPt A θ.pt).left))
    (fun _ => by rw [Category.assoc, e])).symm)
  have hm := hJ.mem ![(snd T A).left, (translPt A θ.pt).left] r
  refine (gs_res r z (chart_le_zero A L _ _) hm _).symm.trans ((congrArg (gs r z _)
    (h fun b => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] b))).trans ((gs_mul r z _ hm _ _).trans
      (congrArg₂ (· * ·) (gs_unit r z _ hm _) ((gs_res r z _ hm _).trans (gs_pull r _ z _ ?_ _)))))
  exact chart_le_pull A L (translT A θ.pt) (translPt A θ.pt) (lift_snd _ _) _ hm

theorem val_thetaPow {k : ℤ} (θ : ThetaGrp A L k T) (n : ℕ) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) : val (powGen A L k θ n) r z J = ∏ j : Fin n,
      thetaVal θ.φ
        (r ≫ (translT A (θ.pt ^ (j : ℕ))).left) z J := by
  unfold val powGen
  dsimp only
  refine (map_prod (gm r z _) _ Finset.univ).trans (Finset.prod_congr rfl fun j _ => ?_)
  exact (gm_res r z _ (hJ.mem (powφ A θ.pt n) r) _).trans
    (val_pull hJ (φ := ![(snd T A).left, (translPt A θ.pt).left]) (ε := ![k, -k]) θ.φ
      (translT A (θ.pt ^ (j : ℕ))).left r)

theorem val_symGen {k : ℤ} (θ : ThetaGrp A L k T) (nu : LB.Gen (negLB A L k T)) {Z : Scheme.{0}}
    (r : Z ⟶ (T ⊗ A).left) (z : Z) {J} (hJ : Good L z J) : val (symGen A L k θ nu) r z J =
      thetaVal θ.φ
        (r ≫ (translT A θ.pt⁻¹).left) z J *
      negVal nu r z J *
      (thetaVal θ.φ
        (r ≫ (negT A T).left) z J *
      (negVal nu
        (r ≫ (translT A θ.pt⁻¹).left) z J)⁻¹) :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
    ((val_mul hJ _ _ _).trans (congrArg (· * _) (val_pull hJ _ _ _)))
    ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (val_pull hJ _ _ _)
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))))

theorem sval_add {k : ℤ} (v w : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    secVal (SecM.toSec A (v + w)) r z J =
      secVal (SecM.toSec A v) r z J +
      secVal (SecM.toSec A w) r z J :=
  gs_add r z _ (hJ.mem _ r) _ _

theorem sval_smul {k : ℤ} (a : Γ(T.left, ⊤)) (v : SecM A L k T) {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J}
    (hJ : Good L z J) :
    secVal (SecM.toSec A (a • v)) r z J =
      gs (r ≫ (fst T A).left) z ⊤ a *
      secVal (SecM.toSec A v) r z J :=
  (gs_mul r z _ (hJ.mem _ r) _ _).trans (congrArg (· * _)
    ((gs_res r z le_top (hJ.mem _ r) _).trans (gs_pull r _ z ⊤ trivial a)))

theorem secM_ext (hL : L.IsLB) {k : ℤ} {v w : SecM A L k T} (h : ∀ y J, Good L y J →
    secVal (SecM.toSec A v) (𝟙 _) y J =
      secVal (SecM.toSec A w) (𝟙 _) y J) : v = w :=
  Subtype.ext (funext fun j => sec_ext_val hL h j)

variable (σ : A ⟶ A) (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))

theorem exists_twist_map (hL : L.IsLB) (hc : c.IsGen) (k : ℤ) (T : Over S) :
    ∃ F : SecM A L k T →ₗ[Γ(T.left, ⊤)] SecM A L k T, ∀ (v) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J),
      Good L z J →
      secVal (SecM.toSec A (F v)) r z J =
        secVal (SecM.toSec A v)
          (r ≫ (T ◁ σ).left) z J * ((val c (r ≫ (snd T A).left) z J ^ k)⁻¹).val := by
  choose F hF using fun v : SecM A L k T => exists_twist_sec c hL hc (φ' := fun _ : Fin 1 => (snd T A).left)
    (fun _ : Fin 1 => (snd T A).left) (ε := fun _ => k) (T ◁ σ).left
    (fun _ => by rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left]) (SecM.toSec A v)
  have hF' : ∀ (v) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      secVal
        (SecM.toSec A (SecM.ofSec A (F v))) r z J =
        secVal (SecM.toSec A v)
          (r ≫ (T ◁ σ).left) z J * ((val c (r ≫ (snd T A).left) z J ^ k)⁻¹).val := fun v Z r z J hJ =>
    (hF v Z r z J hJ).trans (by rw [Fintype.prod_unique]; rfl)
  refine ⟨⟨⟨fun v => SecM.ofSec A (F v), fun v w => secM_ext hL fun y J hJ => ?_⟩,
    fun a v => secM_ext hL fun y J hJ => ?_⟩, hF'⟩
  · rw [sval_add _ _ _ _ hJ, hF' _ _ _ _ _ hJ, hF' _ _ _ _ _ hJ, hF' _ _ _ _ _ hJ, sval_add _ _ _ _ hJ, add_mul]
  · have e : (𝟙 (T ⊗ A).left ≫ (T ◁ σ).left) ≫ (fst T A).left = 𝟙 _ ≫ (fst T A).left := by
      rw [Category.assoc, ← Over.comp_left, whiskerLeft_fst]
    refine (hF' _ _ _ _ _ hJ).trans (Eq.trans ?_ (sval_smul a (SecM.ofSec A (F v)) _ y hJ).symm)
    rw [hF' _ _ _ _ _ hJ, sval_smul a v _ y hJ, e, _root_.mul_assoc]

variable [IsMonHom σ]

theorem whisker_translPt {x : T ⟶ A} (hx : x ≫ σ = x) : T ◁ σ ≫ translPt A x = translPt A x ≫ σ := by
  show T ◁ σ ≫ ((fst T A ≫ x) * snd T A) = ((fst T A ≫ x) * snd T A) ≫ σ
  rw [MonObj.comp_mul, MonObj.mul_comp, whiskerLeft_snd, whiskerLeft_fst_assoc, Category.assoc, hx]

theorem whisker_translT {x : T ⟶ A} (hx : x ≫ σ = x) : translT A x ≫ T ◁ σ = T ◁ σ ≫ translT A x := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [translT]
  · simp [translT, whisker_translPt σ hx]

theorem whisker_negT : negT A T ≫ T ◁ σ = T ◁ σ ≫ negT A T := by
  apply CartesianMonoidalCategory.hom_ext
  · simp [negT]
  · simp [negT]

omit [IsMonHom σ] in
theorem translT_translPt (x y : T ⟶ A) : translT A y ≫ translPt A x = translPt A (x * y) := by
  show translT A y ≫ ((fst T A ≫ x) * snd T A) = (fst T A ≫ (x * y)) * snd T A
  rw [MonObj.comp_mul, MonObj.comp_mul, translT, lift_snd, lift_fst_assoc, _root_.mul_assoc]
  rfl

theorem exists_twist_symLift [IsCommMonObj A] (hL : L.IsLB) (hc : c.IsGen) {k : ℤ} {n : ℕ} (θ : ThetaGrp A L k T)
    (hn : θ.pt ^ n = 1) (hx : θ.pt ≫ σ = θ.pt) (hθ : SymLift A L k n θ.pt θ) :
    ∃ (t : LB.Gen (thetaLB A L k θ.pt)) (ht : t.IsGen), SymLift A L k n θ.pt ⟨θ.pt, t, ht⟩ ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
        thetaVal t r z J =
        thetaVal θ.φ (r ≫ (T ◁ σ).left) z J *
          (val c (r ≫ (snd T A).left) z J ^ k * val c (r ≫ (translPt A θ.pt).left) z J ^ (-k))⁻¹ := by
  obtain ⟨t, ht, hv₀⟩ := exists_twist_gen c hL hc (φ' := ![(snd T A).left, (translPt A θ.pt).left])
    ![(snd T A).left, (translPt A θ.pt).left] (ε := ![k, -k]) (T ◁ σ).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T σ)
      · exact congrArg (fun q => q.left) (whisker_translPt σ hx)) θ.φ θ.isGen
  have hv : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      thetaVal (x := θ.pt) t r z J = thetaVal θ.φ (r ≫ (T ◁ σ).left) z J *
        (val c (r ≫ (snd T A).left) z J ^ k * val c (r ≫ (translPt A θ.pt).left) z J ^ (-k))⁻¹ :=
    fun Z r z J hJ => (hv₀ Z r z J hJ).trans (by rw [Fin.prod_univ_two]; rfl)
  obtain ⟨nu, hnu, hsym⟩ := hθ.sym
  obtain ⟨nu', hnu', hw₀⟩ := exists_twist_gen c hL hc (φ' := ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left])
    ![(snd T A).left, (snd T A ≫ (GrpObj.inv : A ⟶ A)).left] (ε := ![k, -k]) (T ◁ σ).left (fun i => by
      fin_cases i
      · exact congrArg (fun q => q.left) (whiskerLeft_snd T σ)
      · exact congrArg (fun q => q.left) (show T ◁ σ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) =
          (snd T A ≫ (GrpObj.inv : A ⟶ A)) ≫ σ by simp)) nu hnu
  have hw : ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      negVal nu' r z J = negVal nu (r ≫ (T ◁ σ).left) z J *
        (val c (r ≫ (snd T A).left) z J ^ k * val c (r ≫ (snd T A ≫ (GrpObj.inv : A ⟶ A)).left) z J ^ (-k))⁻¹ :=
    fun Z r z J hJ => (hw₀ Z r z J hJ).trans (by rw [Fin.prod_univ_two]; rfl)
  have fix : ∀ j : ℕ, (θ.pt ^ j) ≫ σ = θ.pt ^ j := fun j => by rw [MonObj.pow_comp, hx]
  refine ⟨t, ht, ⟨rfl, corr_of_val hL fun y J hJ => ?_, nu', hnu', corr_of_val hL fun y J hJ => ?_⟩, hv⟩
  · have h₀ := val_corr hJ hθ.pow_eq (T ◁ σ).left
    rw [val_one, val_thetaPow θ n _ y hJ] at h₀
    let f : ℕ → ((T ⊗ A).left.presheaf.stalk y)ˣ := fun j => val c (translPt A (θ.pt ^ j)).left y J ^ k
    rw [val_one, val_thetaPow _ n _ y hJ]
    have step : ∀ j : Fin n, thetaVal (x := θ.pt) t
        (𝟙 _ ≫ (translT A (θ.pt ^ (j : ℕ))).left) y J =
        thetaVal θ.φ
          ((T ◁ σ).left ≫ (translT A (θ.pt ^ (j : ℕ))).left) y J * (f (j + 1) / f j) := fun j => by
      rw [hv _ _ y J hJ, Category.id_comp, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left, ← Over.comp_left,
        whisker_translT σ (fix j), translT_translPt, ← pow_succ', translT, lift_snd, zpow_neg, mul_inv, inv_inv,
        div_eq_mul_inv, mul_comm (f _)]
    refine (Finset.prod_congr rfl fun j _ => step j).trans ?_
    rw [Finset.prod_mul_distrib, h₀, _root_.one_mul, Fin.prod_univ_eq_prod_range (fun j => f (j + 1) / f j),
      Finset.prod_range_div]
    simp only [f, hn, pow_zero, div_self']
  · have h₀ := val_corr hJ hsym (T ◁ σ).left
    rw [val_one, val_symGen θ nu _ y hJ] at h₀
    have fixi : θ.pt⁻¹ ≫ σ = θ.pt⁻¹ := by rw [GrpObj.inv_comp, hx]
    have e₁ : translT A θ.pt⁻¹ ≫ translPt A θ.pt = snd T A := by
      rw [translT_translPt, mul_inv_cancel]
      show (fst T A ≫ 1) * snd T A = _
      rw [MonObj.comp_one, _root_.one_mul]
    have e₂ : negT A T ≫ snd T A = snd T A ≫ (GrpObj.inv : A ⟶ A) := lift_snd _ _
    have e₃ : negT A T ≫ translPt A θ.pt = translT A θ.pt⁻¹ ≫ snd T A ≫ (GrpObj.inv : A ⟶ A) := by
      rw [translT, lift_snd_assoc]
      show negT A T ≫ ((fst T A ≫ θ.pt) * snd T A) = ((fst T A ≫ θ.pt⁻¹) * snd T A)⁻¹
      rw [MonObj.comp_mul, e₂, negT, lift_fst_assoc, mul_inv, GrpObj.comp_inv, inv_inv]
      rfl
    rw [val_one, val_symGen _ nu' _ y hJ]
    dsimp only
    rw [hv _ _ y J hJ, hv _ _ y J hJ, hw _ _ y J hJ, hw _ _ y J hJ]
    simp only [Category.id_comp, ← Over.comp_left] at h₀ ⊢
    rw [whisker_translT σ fixi, whisker_negT σ, e₁, e₂, e₃, ← h₀]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, zpow_neg]
    abel

end Theta

section Assemble

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] {L : LB A.left} (σ : A ⟶ A)
  (c : LB.Gen (LB.LinComb L (K := Fin 2) ![σ.left, 𝟙 A.left] ![1, -1]))

theorem twist_comm [IsMonHom σ] (hL : L.IsLB) {k : ℤ} {T : Over S} (F : SecM A L k T → SecM A L k T)
    (hF : ∀ (v) (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) (J), Good L z J →
      secVal (SecM.toSec A (F v)) r z J =
        secVal (SecM.toSec A v) (r ≫ (T ◁ σ).left) z J * ((val c (r ≫ (snd T A).left) z J ^ k)⁻¹).val)
    (θ : ThetaGrp A L k T) (hx : θ.pt ≫ σ = θ.pt)
    (hθ : ∀ y J, Good L y J → thetaVal θ.φ (𝟙 _) y J = thetaVal θ.φ (𝟙 _ ≫ (T ◁ σ).left) y J *
      (val c (𝟙 _ ≫ (snd T A).left) y J ^ k * val c (𝟙 _ ≫ (translPt A θ.pt).left) y J ^ (-k))⁻¹)
    {v v' w' : SecM A L k T} (a₁ : IsActOf A L k θ (SecM.toSec A v) (SecM.toSec A v'))
    (a₂ : IsActOf A L k θ (SecM.toSec A (F v)) (SecM.toSec A w')) : F v' = w' := by
  refine secM_ext hL fun y J hJ => ?_
  have e₁ : translT A θ.pt ≫ snd T A = translPt A θ.pt := lift_snd _ _
  rw [hF _ _ _ _ _ hJ, sval_isActOf a₁ _ y hJ, sval_isActOf a₂ _ y hJ, hF _ _ _ _ _ hJ, hθ y J hJ]
  simp only [Category.id_comp, ← Over.comp_left]
  rw [whisker_translT σ hx, e₁, zpow_neg, mul_inv, inv_inv, Units.val_mul, Units.val_mul]
  generalize val c (translPt A θ.pt).left y J ^ k = p
  have := p.mul_inv
  linear_combination (-(thetaVal θ.φ (T ◁ σ).left y J).val * secVal (SecM.toSec A v) (T ◁ σ ≫ translT A θ.pt).left y J *
    ((val c (snd T A).left y J ^ k)⁻¹).val) * this

theorem eq_id_of_twist_smul (hL : L.IsLB) (hS : IsAffineOpen (⊤ : S.Opens)) {n : ℕ} (hV : VeryAmpleAt A L n)
    (a : Γ((baseOver S).left, ⊤))
    (hF : ∀ (v : SecM A L n (baseOver S)) (Z : Scheme.{0}) (r : Z ⟶ (baseOver S ⊗ A).left) (z : Z) (J), Good L z J →
      secVal (SecM.toSec A (a • v)) r z J = secVal (SecM.toSec A v) (r ≫ (baseOver S ◁ σ).left) z J *
        ((val c (r ≫ (snd (baseOver S) A).left) z J ^ (n : ℤ))⁻¹).val) : σ = 𝟙 A := by
  obtain ⟨M, s, hcov, haff⟩ := hV ⊤ hS
  obtain ⟨i', hi, hi'⟩ : ∃ i' : A.left ⟶ (A.hom ⁻¹ᵁ ⊤).toScheme,
      i' ≫ (A.hom ⁻¹ᵁ ⊤).ι = 𝟙 _ ∧ (A.hom ⁻¹ᵁ ⊤).ι ≫ i' = 𝟙 _ :=
    ⟨A.left.topIso.inv, A.left.topIso.inv_hom_id, A.left.topIso.hom_inv_id⟩
  obtain ⟨g, hg⟩ : ∃ g : A.left ⟶ (baseOver S ⊗ A).left, g ≫ (snd (baseOver S) A).left = 𝟙 _ :=
    ⟨(lift (X := baseOver S) (Over.homMk A.hom (Category.comp_id _)) (𝟙 A)).left, by
      rw [← Over.comp_left, lift_snd, Over.id_left]⟩
  have hgσ : g ≫ (baseOver S ◁ σ).left ≫ (snd (baseOver S) A).left = σ.left := by
    rw [← Over.comp_left, whiskerLeft_snd, Over.comp_left, reassoc_of% hg]
  have sec : ∀ j, ∃ v : SecM A L n (baseOver S), ∀ (Z : Scheme.{0}) (r : Z ⟶ (baseOver S ⊗ A).left) (z : Z) (J),
      Good L z J → secVal (SecM.toSec A v) r z J =
        sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
          (r ≫ (snd (baseOver S) A).left ≫ i') z J := fun j => by
    obtain ⟨s', hs'⟩ := exists_sec hL (φ' := fun _ : Fin 1 => (snd (baseOver S) A).left) (ε' := fun _ => (n : ℤ))
      (fun U _ f => by
        refine (Fintype.prod_sum_type _).trans ?_
        simp only [Sum.elim_inl, Category.assoc, hi, Category.comp_id, zpow_one, Finset.prod_const, Finset.card_univ,
          Fintype.card_fin, Fintype.prod_empty, _root_.mul_one, pow_one, zpow_natCast])
      (pullMulSec (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) (s j)
        ((snd (baseOver S) A).left ≫ i') (LB.oneGen L) (isGen_of_germs _ fun y j j' _ _ =>
          (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm))
    refine ⟨SecM.ofSec A s', fun Z r z J hJ => (hs' Z r z J hJ).trans ?_⟩
    refine (sval_pullMulSec _ _ _ _ r z hJ).trans ?_
    rw [val_one, Units.val_one, _root_.mul_one]
  choose v hv using sec
  have key : (A.hom ⁻¹ᵁ ⊤).ι ≫ σ.left ≫ i' = 𝟙 _ := by
    refine eq_id_of_sval (L := L) (φ := fun _ : Fin n => (A.hom ⁻¹ᵁ ⊤).ι) (ε := fun _ => 1) s (A.hom ∣_ ⊤) _ ?_ hcov haff
      fun y => ?_
    · rw [← cancel_mono (⊤ : S.Opens).ι, Category.assoc, morphismRestrict_ι, Category.assoc, Category.assoc,
        reassoc_of% hi, Over.w]
    · choose J hJ using fun χ : (A.hom ⁻¹ᵁ ⊤).toScheme ⟶ A.left => exists_chart hL (χ y)
      refine ⟨J, hJ, gs (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (fst (baseOver S) A).left) y ⊤ a *
        (val c (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (snd (baseOver S) A).left) y J ^ (n : ℤ)).val, fun j => ?_⟩
      have h₁ := hF (v j) _ ((A.hom ⁻¹ᵁ ⊤).ι ≫ g) y J hJ
      have e₁ : ((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (snd (baseOver S) A).left ≫ i' = 𝟙 _ := by
        rw [Category.assoc, reassoc_of% hg, hi']
      have e₂ : (((A.hom ⁻¹ᵁ ⊤).ι ≫ g) ≫ (baseOver S ◁ σ).left) ≫ (snd (baseOver S) A).left ≫ i' =
          (A.hom ⁻¹ᵁ ⊤).ι ≫ σ.left ≫ i' := by
        rw [Category.assoc, Category.assoc, reassoc_of% hgσ]
      rw [sval_smul _ _ _ _ hJ, hv _ _ _ _ _ hJ, hv _ _ _ _ _ hJ, Units.eq_mul_inv_iff_mul_eq, e₁, e₂] at h₁
      exact h₁.symm.trans (mul_right_comm _ _ _)
  apply Over.OverMorphism.ext
  have := congrArg (fun q => i' ≫ q ≫ (A.hom ⁻¹ᵁ ⊤).ι) key
  simpa only [Category.assoc, hi, reassoc_of% hi, Category.comp_id, Category.id_comp, Over.id_left] using this

end Assemble

set_option maxHeartbeats 1000000 in

theorem eq_id_of_fixes_torsion : GlobalFnsSt → SymLiftSt → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℤ) (T : Over S), ∃ ρ : ThetaGrp P.A P.L k T → (SecM P.A P.L k T ≃ₗ[Γ(T.left, ⊤)] SecM P.A P.L k T), (∀ θ s s', IsActOf P.A P.L k θ s s' ↔ ρ θ (SecM.ofSec P.A s) = SecM.ofSec P.A s') ∧ (∀ θx θy c, CommIsOf P.A P.L k θx θy c → ∀ v, ρ θx (ρ θy v) = (c : Γ(T.left, ⊤)) • ρ θy (ρ θx v)) ∧ (∀ θ θ', θ.pt = θ'.pt → ∃ c : Γ(T.left, ⊤)ˣ, ∀ v, ρ θ' v = (c : Γ(T.left, ⊤)) • ρ θ v) ∧ ∀ θx θy, ∃ θ, θ.pt = θx.pt * θy.pt ∧ ∀ v, ρ θ v = ρ θx (ρ θy v)) → (∀ (S : Scheme.{0}) (P : PolAV S) (k : ℕ) (T : Over S), (∀ (θx θy : ThetaGrp P.A P.L k T) (c : Γ(T.left, ⊤)ˣ), WeilIs P.A P.L k θx.pt θy.pt c ↔ CommIsOf P.A P.L k θx θy c) ∧ (∀ x : T ⟶ P.A, x ^ k = 1 → Subsingleton T.left → ∃ θ : ThetaGrp P.A P.L k T, θ.pt = x ∧ (Odd k → SymLift P.A P.L k k x θ))) → IrredSt → GlobalSectionsRankAlgClosed → AmpleSt → KerPowSt → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (n : ℕ), Odd n → 5 ≤ n → (n : K) ≠ 0 → ∀ σ : P.A ≅ P.A, IsMonHom σ.hom → (∃ c : LB.Gen (LB.LinComb P.L (K := Fin 2) ![σ.hom.left, 𝟙 P.A.left] ![1, -1]), c.IsGen) → (∀ x : baseOver (Spec (CommRingCat.of K)) ⟶ P.A, x ^ n = 1 → x ≫ σ.hom = x) → σ.hom = 𝟙 P.A := by
  intro _ hSym hρ hWC hIrr hH0 hAmp hKer K _ _ P n hodd h5 hnK σ hσ ⟨c, hc⟩ hfix
  have := P.isAb.comm
  let S := Spec (CommRingCat.of K)
  let T : Over S := baseOver S
  let e : K ≃+* Γ(T.left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv
  have hsub : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  have hunit : IsUnit (n : Γ(S, ⊤)) := by
    have := (Ne.isUnit hnK).map e
    rwa [map_natCast] at this
  obtain ⟨ρ, hact, -, hsc, -⟩ := hρ S P n T
  obtain ⟨F, hF⟩ := exists_twist_map σ.hom c P.isLB hc n T
  have comm : ∀ (θ : ThetaGrp P.A P.L n T) (v), F (ρ θ v) = ρ θ (F v) := by
    intro θ v
    have hn : θ.pt ^ n = 1 := (hKer S P n (by omega) T θ.pt).1 fun p =>
      ⟨⊤, trivial, exists_gen_pull _ θ.φ θ.isGen _⟩
    obtain ⟨θ₀, h₀, hs⟩ := (hWC S P n T).2 θ.pt hn hsub
    obtain ⟨a, ha⟩ := hsc θ₀ θ h₀
    rw [ha, ha, map_smul]
    congr 1
    rw [← h₀] at hn hs
    obtain ⟨t, ht, hst, hv⟩ := exists_twist_symLift σ.hom c P.isLB hc θ₀ hn (hfix _ hn) (hs hodd)
    have hcorr := (hSym S P n hodd hunit T θ₀.pt hn).2 _ _ hst (hs hodd)
    exact twist_comm σ.hom c P.isLB F hF θ₀ (hfix _ hn) (fun y J hJ => (val_corr hJ hcorr _).symm.trans (hv _ _ y J hJ))
      ((hact _ _ _).2 rfl) ((hact _ _ _).2 rfl)
  obtain ⟨a, v₀, hv₀, hav⟩ := exists_eigenvector e (M := SecM P.A P.L n T)
    (by rw [hH0 K P n (by omega)]; exact pow_ne_zero _ (by omega)) F
  obtain ⟨V, hV⟩ : ∃ V : Submodule Γ(T.left, ⊤) (SecM P.A P.L n T), ∀ v, v ∈ V ↔ F v = a • v :=
    ⟨LinearMap.eqLocus F (a • LinearMap.id), fun v => LinearMap.mem_eqLocus⟩
  have hW := hIrr K P n (Or.inr (by omega)) hnK V fun θ s s' h hs => by
    have stable : ∀ w : SecM P.A P.L n T, w ∈ V → ρ θ w ∈ V := fun w hw =>
      (hV _).2 ((comm θ w).trans ((congrArg (ρ θ) ((hV w).1 hw)).trans (map_smul (ρ θ) a w)))
    exact (congrArg (· ∈ V) ((hact θ s s').1 h)).mp (stable _ hs)
  have hall : ∀ v, F v = a • v := by
    rcases hW with h | h
    · exact absurd ((Submodule.eq_bot_iff _).1 h v₀ ((hV _).2 hav)) hv₀
    · exact fun v => (hV v).1 (h.ge Submodule.mem_top)
  exact eq_id_of_twist_smul σ.hom c P.isLB (isAffineOpen_top S) (hAmp S P n (by omega)).2 a fun v Z r z J hJ => by
    rw [← hall]; exact hF v Z r z J hJ

end GlobalTheory.TorsionFixedAut
