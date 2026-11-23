import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ThetaPowOrder

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {S : Scheme.{0}} (A : Over S) [GrpObj A]

theorem translPt_eq {T : Over S} (x : T ⟶ A) : translPt A x = (fst T A ≫ x) * snd T A := rfl

theorem translT_one (T : Over S) : translT A (1 : T ⟶ A) = 𝟙 _ := by
  unfold translT
  rw [translPt_eq, MonObj.comp_one, _root_.one_mul, lift_fst_snd]

theorem translT_comp {T : Over S} (x y : T ⟶ A) : translT A x ≫ translT A y = translT A (y * x) := by
  unfold translT
  simp only [translPt_eq, comp_lift, lift_fst, MonObj.comp_mul, lift_snd, lift_fst_assoc, _root_.mul_assoc]

theorem translT_comp_left {T : Over S} (x : T ⟶ A) (m : ℕ) :
    (translT A x).left ≫ (translT A (x ^ m)).left = (translT A (x ^ (m + 1))).left := by
  rw [← Over.comp_left, translT_comp, ← pow_succ]

private theorem mem_wchart_of_good {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    r z ∈ L.wchart φ (fun k => J (r ≫ φ k)) := by
  unfold LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  intro k
  simpa using hJ (r ≫ φ k)

private theorem germ_presheaf_map_eq_germ {X : Scheme.{0}} {U V : X.Opens} (i : U ⟶ V) (x : X) (hx : x ∈ U) (s : Γ(X, V)) :
    (X.presheaf.germ U x hx).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.germ V x (i.le hx)).hom s :=
  TopCat.Presheaf.germ_res_apply _ i x hx s

private theorem germ_app_eq_stalkMap_germ {X Y : Scheme.{0}} (f : X ⟶ Y) (U : Y.Opens) (x : X) (hx : f x ∈ U) (y : Γ(Y, U)) :
    (X.presheaf.germ (f ⁻¹ᵁ U) x hx).hom ((f.app U).hom y) =
      (f.stalkMap x).hom ((Y.presheaf.germ U (f x) hx).hom y) :=
  (Scheme.Hom.germ_stalkMap_apply f U x hx y).symm

private theorem sval_lPow_eq_of_index_eq {L : LB A.left} {k : ℤ} {T : Over S} (s : LB.Sec (LPow A L k T)) {Z : Scheme.{0}}
    (p : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (c : L.ι) (hc : J (p ≫ (snd T A).left) = c) :
    sval (L := L) s p z J = gs p z (L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c)) (s.f (fun _ => c)) := by
  subst hc
  rfl

private theorem mem_wchart_of_good_of_index_eq {X Y : Scheme.{0}} (L : LB X) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : K → L.ι)
    (hc : ∀ k, J (r ≫ φ k) = c k) : r z ∈ L.wchart φ c := by
  have hm := mem_wchart_of_good L φ r z hJ
  have hfun : (fun k => J (r ≫ φ k)) = c := funext hc
  rw [hfun] at hm
  exact hm

private theorem val_thetaGrp_eq_of_index_eq {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) {Z : Scheme.{0}}
    (p : Z ⟶ (T ⊗ A).left) (z : Z) (J : (Z ⟶ A.left) → L.ι) (c : Fin 2 → L.ι)
    (hc : (fun b => J (p ≫ ![(snd T A).left, (translPt A θ.pt).left] b)) = c) :
    val (L := L) θ.φ p z J = gm p z (L.wchart ![(snd T A).left, (translPt A θ.pt).left] c) (θ.φ.s c) := by
  subst hc
  rfl

private theorem germ_app_presheaf_map_app_eq_germ_comp_app {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (f : Y ⟶ X) (z : Z) (U : X.Opens) (V V' : Y.Opens)
    (h1 : V ≤ V') (h2 : V' ≤ f ⁻¹ᵁ U) (hz : r z ∈ V) (hz' : (r ≫ f) z ∈ U) (x : Γ(X, U)) :
    (Z.presheaf.germ (r ⁻¹ᵁ V) z hz).hom ((r.app V).hom ((Y.presheaf.map (homOfLE h1).op).hom
        ((Y.presheaf.map (homOfLE h2).op).hom ((f.app U).hom x)))) =
      (Z.presheaf.germ ((r ≫ f) ⁻¹ᵁ U) z hz').hom (((r ≫ f).app U).hom x) := by
  rw [germ_app_eq_stalkMap_germ r V z hz, germ_presheaf_map_eq_germ, germ_presheaf_map_eq_germ, Scheme.Hom.comp_app]
  exact (germ_app_eq_stalkMap_germ r (f ⁻¹ᵁ U) z _ _).symm

variable {A}

theorem act_sval {L : LB A.left} {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T} {s s' : LB.Sec (LPow A L k T)}
    (h : IsActOf A L k θ s s') {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι}
    (hJ : Good L z J) :
    sval (L := L) s' r z J = (val (L := L) θ.φ r z J).val * sval (L := L) s (r ≫ (translT A θ.pt).left) z J := by
  have hpt : (translT A θ.pt).left ≫ (snd T A).left = (translPt A θ.pt).left := by
    rw [← Over.comp_left]
    unfold translT
    rw [lift_snd]
  have e : J ((r ≫ (translT A θ.pt).left) ≫ (snd T A).left) =
      J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] 1) := by
    rw [Category.assoc, hpt]
    rfl
  rw [sval_lPow_eq_of_index_eq A s (r ≫ (translT A θ.pt).left) z J _ e]
  unfold IsActOf IsTwistPull at h
  have hj := h (fun i => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] i))
  have m := mem_wchart_of_good L ![(snd T A).left, (translPt A θ.pt).left] r z hJ
  have m0 := mem_wchart_of_good L (fun _ : Fin 1 => (snd T A).left) r z hJ
  have m1 : (r ≫ (translT A θ.pt).left) z ∈ L.wchart (fun _ : Fin 1 => (snd T A).left)
      (fun _ => J (r ≫ ![(snd T A).left, (translPt A θ.pt).left] 1)) := by
    rw [← e]
    exact mem_wchart_of_good L (fun _ : Fin 1 => (snd T A).left) (r ≫ (translT A θ.pt).left) z hJ
  have key := congrArg (fun x => ((T ⊗ A).left.presheaf.germ _ (r z) m).hom x) hj
  simp only at key
  erw [TopCat.Presheaf.germ_res_apply, map_mul, TopCat.Presheaf.germ_res_apply] at key
  have key2 := congrArg (r.stalkMap z).hom key
  simp only [map_mul, Scheme.Hom.germ_stalkMap_apply] at key2
  erw [Scheme.Hom.germ_stalkMap_apply, Scheme.Hom.germ_stalkMap_apply] at key2
  unfold sval val gs gm
  simp only [m0, m, m1, ↓reduceDIte]
  simp only [Scheme.Hom.comp_app, Scheme.Hom.comp_preimage, CommRingCat.hom_comp]
  convert key2 using 1
  · rfl
  · erw [Units.coe_map]
    rfl

theorem val_powGen {L : LB A.left} {k : ℤ} {T : Over S} (θ : ThetaGrp A L k T) (n : ℕ)
    {Z : Scheme.{0}} (r : Z ⟶ (T ⊗ A).left) (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) :
    val (Out.powGen A L k θ n) r z J =
      ∏ i ∈ Finset.range n, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) z J := by
  rw [← Fin.prod_univ_eq_prod_range]
  have hmem := mem_wchart_of_good L (powφ A θ.pt n) r z hJ
  have hfac : ∀ i : Fin n, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z J =
      gm (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z
        (L.wchart ![(snd T A).left, (translPt A θ.pt).left] (fun b => J (r ≫ powφ A θ.pt n (i, b))))
        (θ.φ.s (fun b => J (r ≫ powφ A θ.pt n (i, b)))) := by
    intro i
    apply val_thetaGrp_eq_of_index_eq
    funext b
    rw [Category.assoc]
    rfl
  have hmi : ∀ i : Fin n, (r ≫ (translT A (θ.pt ^ (i : ℕ))).left) z ∈
      L.wchart ![(snd T A).left, (translPt A θ.pt).left] (fun b => J (r ≫ powφ A θ.pt n (i, b))) := by
    intro i
    apply mem_wchart_of_good_of_index_eq L _ _ z hJ
    intro b
    rw [Category.assoc]
    rfl
  simp only [hfac]
  unfold val Out.powGen LB.pullGen gm
  simp only [hmem, hmi, ↓reduceDIte]
  erw [map_prod]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  apply Units.ext
  exact germ_app_presheaf_map_app_eq_germ_comp_app r _ z _ _ _ _ _ _ _ _

theorem iter_sval {L : LB A.left} {k : ℤ} {T : Over S} {θ : ThetaGrp A L k T} {n : ℕ}
    (t : Fin (n + 1) → LB.Sec (LPow A L k T)) (ht : ∀ i : Fin n, IsActOf A L k θ (t i.castSucc) (t i.succ))
    {Z : Scheme.{0}} (z : Z) {J : (Z ⟶ A.left) → L.ι} (hJ : Good L z J) (m : ℕ) (hm : m < n + 1)
    (r : Z ⟶ (T ⊗ A).left) :
    sval (L := L) (t ⟨m, hm⟩) r z J =
      (∏ i ∈ Finset.range m, val (L := L) θ.φ (r ≫ (translT A (θ.pt ^ i)).left) z J).val *
        sval (L := L) (t 0) (r ≫ (translT A (θ.pt ^ m)).left) z J := by
  induction m generalizing r with
  | zero =>
    simp only [Finset.range_zero, Finset.prod_empty, Units.val_one, _root_.one_mul, pow_zero, translT_one,
      Over.id_left, Category.comp_id]
    rfl
  | succ m ih =>
    have hm' : m < n + 1 := by omega
    have hact : sval (L := L) (t ⟨m + 1, hm⟩) r z J =
        (val (L := L) θ.φ r z J).val * sval (L := L) (t ⟨m, hm'⟩) (r ≫ (translT A θ.pt).left) z J :=
      act_sval (ht ⟨m, by omega⟩) r z hJ
    rw [hact, ih hm' (r ≫ (translT A θ.pt).left)]
    simp only [Category.assoc, translT_comp_left, Finset.prod_range_succ', pow_zero, translT_one, Over.id_left,
      Category.comp_id, Units.val_mul]
    ring

private theorem germ_unit_eq_one_of_map_eq_one {X : Scheme.{0}} {V W : X.Opens} (i : V ⟶ W) (x : X) (hxV : x ∈ V) (hxW : x ∈ W)
    (u : (Γ(X, W))ˣ) (h : Units.map (X.presheaf.map i.op).hom.toMonoidHom u = 1) :
    (X.presheaf.germ W x hxW).hom (u : Γ(X, W)) = 1 := by
  have h2 := congrArg (fun v : (Γ(X, V))ˣ => (X.presheaf.germ V x hxV).hom (v : Γ(X, V))) h
  simp only [Units.coe_map, Units.val_one, map_one] at h2
  rw [← h2]
  exact (germ_presheaf_map_eq_germ i x hxV _).symm

end GlobalTheory.ThetaPowOrder

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThetaPowOrder in

theorem thetaGrp_act_iterate_eq_of_pow_eq_one : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : LB A.left), L.IsLB → ∀ (k : ℤ) (T : Over S) (θ : ThetaGrp A L k T) (n : ℕ), θ.pt ^ n = 1 → LB.Gen.Corr L _ _ _ _ (Out.powGen A L k θ n) (LB.oneGen L) → ∀ t : Fin (n + 1) → LB.Sec (LPow A L k T), (∀ i : Fin n, IsActOf A L k θ (t i.castSucc) (t i.succ)) → ∀ j, (t (Fin.last n)).f j = (t 0).f j := by
  intro S A _ _ L hL k T θ n hn hc t ht j
  obtain ⟨c, rfl⟩ : ∃ c, j = fun _ => c := ⟨j 0, funext fun i => by fin_cases i; rfl⟩
  apply TopCat.Presheaf.section_ext (T ⊗ A).left.sheaf
  intro x hx
  classical
  have hcov : ∀ ψ : (T ⊗ A).left ⟶ A.left, ∃ i, ψ x ∈ L.U i := by
    intro ψ
    have h1 : ψ x ∈ (⨆ i, L.U i) := by
      rw [hL.cover]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp h1
  let J : ((T ⊗ A).left ⟶ A.left) → L.ι := fun ψ => if ψ = (snd T A).left then c else (hcov ψ).choose
  have hJ : Good L x J := by
    intro ψ
    by_cases hψ : ψ = (snd T A).left
    · have hx' : x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c) := hx
      unfold LB.wchart at hx'
      simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage] at hx'
      simp only [J, hψ, if_true]
      exact hx' 0
    · simp only [J, hψ, if_false]
      exact (hcov ψ).choose_spec
  have hJc : J (𝟙 _ ≫ (snd T A).left) = c := by
    simp [J]
  have hit := iter_sval t ht x hJ n (Nat.lt_succ_self n) (𝟙 _)
  rw [← val_powGen θ n (𝟙 _) x hJ, hn, translT_one, Over.id_left, Category.comp_id] at hit
  have hv : val (L := L) (Out.powGen A L k θ n) (𝟙 _) x J = 1 := by
    have hm := mem_wchart_of_good L (powφ A θ.pt n) (𝟙 _) x hJ
    have hcc := hc (fun kk => J (𝟙 _ ≫ powφ A θ.pt n kk)) (fun e => e.elim)
      (fun k₁ k₂ h => by simp only [h]) (fun k₁ => k₁.elim) (fun _ e => e.elim)
    unfold val gm
    simp only [hm, ↓reduceDIte]
    apply Units.ext
    unfold LB.oneGen at hcc
    erw [map_one] at hcc
    exact germ_unit_eq_one_of_map_eq_one _ x (by exact ⟨hm, by simp [LB.wchart]⟩) hm _ hcc
  rw [hv, Units.val_one, _root_.one_mul] at hit
  rw [sval_lPow_eq_of_index_eq A (t ⟨n, _⟩) (𝟙 _) x J c hJc, sval_lPow_eq_of_index_eq A (t 0) (𝟙 _) x J c hJc] at hit
  unfold gs at hit
  have hx2 : (𝟙 (T ⊗ A).left) x ∈ L.wchart (fun _ : Fin 1 => (snd T A).left) (fun _ => c) := hx
  simp only [hx2, ↓reduceDIte] at hit
  exact hit

end GlobalTheory
