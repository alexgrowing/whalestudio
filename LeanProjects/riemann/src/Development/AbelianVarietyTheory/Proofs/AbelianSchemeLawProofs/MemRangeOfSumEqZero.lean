import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfLocalOnBase

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.EndDivisible

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic TopologicalSpace

def germPull {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) :
    Γ(Y, U) →+* Z.presheaf.stalk z :=
  (Z.presheaf.germ (r ⁻¹ᵁ U) z h).hom.comp (r.app U).hom

theorem germPull_apply {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    germPull r z U h a = gs r z U a := (gs_eq r z U h a).symm

theorem gs_appLE {Z Y X : Scheme.{0}} (f : Z ⟶ Y) (r : Y ⟶ X) (z : Z) (U : X.Opens) (V : Y.Opens)
    (hle : V ≤ r ⁻¹ᵁ U) (h : f z ∈ V) (a : Γ(X, U)) :
    gs f z V ((r.appLE U V hle).hom a) = gs (f ≫ r) z U a :=
  (gs_res f z hle h _).trans (gs_pull f r z U (hle h) a)

theorem exists_factor {X W Y S : Scheme.{0}} [IsIntegral X] [Y.IsSeparated] [IsAffine S] (f : X ⟶ W)
    (w : W ⟶ Y) (g : X ⟶ S) (hS : IsField Γ(S, ⊤)) (D : W.Opens) (hD : IsAffineOpen D) (z : X) (hz : f z ∈ D)
    (h : ∀ a : Γ(W, D), ∃ c : Γ(S, ⊤), gs g z ⊤ c = gs f z D a) : ∃ p : S ⟶ Y, f ≫ w = g ≫ p := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hzV, hVD⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show z ∈ ((f ⁻¹ᵁ D : X.Opens) : Set X) from hz)
      (f ⁻¹ᵁ D).isOpen
  have hVD' : V ≤ f ⁻¹ᵁ D := hVD
  have : Nonempty V := ⟨⟨z, hzV⟩⟩
  let κ := (g.appLE ⊤ V le_top).hom
  let φ := (f.appLE D V hVD').hom
  have hκ : Function.Injective κ := by
    letI := hS.toField
    exact κ.injective
  have hr : ∀ a, φ a ∈ κ.range := fun a => by
    obtain ⟨c, hc⟩ := h a
    refine ⟨c, germ_injective_of_isIntegral X z hzV ?_⟩
    refine (gs_eq (𝟙 X) z V hzV _).symm.trans (Eq.trans ?_ (gs_eq (𝟙 X) z V hzV _))
    refine (gs_appLE (𝟙 X) g z ⊤ V le_top hzV c).trans
      (Eq.trans ?_ (gs_appLE (𝟙 X) f z D V hVD' hzV a).symm)
    rw [Category.id_comp, Category.id_comp, hc]
  let e : Γ(S, ⊤) ≃+* κ.range := RingEquiv.ofBijective κ.rangeRestrict
    ⟨fun a b hab => hκ (congrArg Subtype.val hab), κ.rangeRestrict_surjective⟩
  let χ : Γ(W, D) ⟶ Γ(S, ⊤) := CommRingCat.ofHom (e.symm.toRingHom.comp (φ.codRestrict κ.range hr))
  have hχ : f.appLE D V hVD' = χ ≫ g.appLE ⊤ V le_top := by
    ext a
    exact (congrArg Subtype.val (e.apply_symm_apply ⟨φ a, hr a⟩)).symm
  refine ⟨S.isoSpec.hom ≫ Spec.map χ ≫ hD.fromSpec ≫ w, ?_⟩
  have : IsDominant hV.fromSpec := ⟨by
    rw [DenseRange, hV.range_fromSpec]
    exact V.isOpen.dense ⟨z, hzV⟩⟩
  refine ext_of_isDominant hV.fromSpec ?_
  rw [← Category.assoc, ← hD.SpecMap_appLE_fromSpec f hV hVD', ← Category.assoc hV.fromSpec,
    ← (isAffineOpen_top S).SpecMap_appLE_fromSpec g hV le_top, hχ, IsAffineOpen.fromSpec_top]
  simp

theorem exists_monomials {X W Z : Scheme.{0}} (L : LB X) (hL : L.IsLB) (w : W ⟶ X) (N : ℕ)
    (s s' : LB.Sec (LB.LinComb L (K := Fin N) (fun _ => w) (fun _ => 1))) (m : X ⟶ X) (t : ℕ)
    (α : LB.Gen (LB.LinComb L (K := Fin 2) ![𝟙 X, m] ![(t : ℤ), -1])) (hα : α.IsGen)
    (f : Z ⟶ W) (u : Z ⟶ X) (hu : u = f ≫ w ≫ m) (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    ∃ b : (Z.presheaf.stalk z)ˣ, ∀ a ≤ t,
      ∃ σ : LB.Sec (LB.LinComb L (K := Unit) (fun _ => u) (fun _ => (N : ℤ))),
        sval σ (𝟙 Z) z J = sval s' f z J ^ a * sval s f z J ^ (t - a) * b.val := by
  obtain ⟨β, hβ⟩ : ∃ β : LB.Gen (LB.LinComb L (K := Fin 2) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k)
      (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)), β.IsGen :=
    exists_gen_zsmul _ (DVR.pullGen_isGen _ _ _ _ hα (f ≫ w)) _
  refine ⟨val β (𝟙 Z) z J, fun a ha => ?_⟩
  have hF : FormEq (K := (Fin a ⊕ Fin (t - a)) × Fin N ⊕ Fin 2)
      (Sum.elim (fun _ => f ≫ w) (fun k => (f ≫ w) ≫ ![𝟙 X, m] k))
      (Sum.elim (fun _ => 1) (fun k => -(N : ℤ) * ![(t : ℤ), -1] k)) (fun _ : Unit => u) (fun _ => (N : ℤ)) := by
    intro U _ h
    rw [Fintype.prod_sum_type, Fin.prod_univ_two, hu]
    simp only [Sum.elim_inl, Sum.elim_inr, zpow_one, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
      Fintype.card_sum, Fintype.card_fin, Matrix.cons_val_zero, Matrix.cons_val_one, Category.comp_id,
      Category.assoc, Fintype.card_unit, pow_one, Nat.add_sub_of_le ha]
    rw [← _root_.mul_assoc, ← zpow_natCast, ← zpow_add]
    simp [mul_comm]
  obtain ⟨σ, hσ⟩ := exists_sec hL hF
    (pullMulSec (powSec (I := Fin a ⊕ Fin (t - a)) (Sum.elim (fun _ => s') (fun _ => s))) f β hβ)
  refine ⟨σ, (hσ _ _ z J hJ).trans ((sval_pullMulSec _ _ _ _ _ z hJ).trans ?_)⟩
  rw [sval_powSec _ _ z hJ, Fintype.prod_sum_type, Category.id_comp]
  simp

theorem mem_range_of_sum_eq_zero {K R : Type} [Field K] [IsAlgClosed K] [CommRing R] [IsDomain R]
    (κ : K →+* R) {n : ℕ} (c : Fin n → K) (hc : c ≠ 0) (x : R) (h : ∑ k, κ (c k) * x ^ (k : ℕ) = 0) :
    x ∈ κ.range := by
  let p : Polynomial K := ∑ k : Fin n, Polynomial.monomial (k : ℕ) (c k)
  have hp : p ≠ 0 := fun h0 => hc (funext fun k => by
    have := congrArg (fun q => Polynomial.coeff q k) h0
    simp only [p, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial, Fin.val_inj,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Polynomial.coeff_zero] at this
    exact this)
  refine (IsAlgClosed.splits p).mem_range_of_isRoot hp ?_
  rw [Polynomial.IsRoot, Polynomial.eval_map, Polynomial.eval₂_finset_sum]
  simpa [Polynomial.eval₂_monomial] using h

theorem eq_one_of_forall_pow_dvd :
    (∀ (X S : Scheme.{0}) (f : X ⟶ S), Smooth f → GeometricallyConnected f → GeometricallyIntegral f) → (∀ (S : Scheme.{0}) (P : PolAV S) (n : ℕ), ∃ α : LB.Gen (LB.LinComb P.L (K := Fin 2) ![𝟙 P.A.left, (mulA P.A n).left] ![(n : ℤ) ^ 2, -1]), α.IsGen) → (∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (M : LB P.A.left), M.IsLB → ∃ n : ℕ, ∀ s : Fin n → LB.Sec M, ∃ c : Fin n → Γ(Spec (CommRingCat.of K), ⊤), c ≠ 0 ∧ ∀ i, ∑ k, (P.A.hom.appLE ⊤ (M.U i) le_top).hom (c k) * (s k).f i = 0) → ∀ (K : Type) [Field K] [IsAlgClosed K] (P : PolAV (Spec (CommRingCat.of K))) (q : ℕ), 2 ≤ q → ∀ u : P.A ⟶ P.A, (∀ k : ℕ, ∃ ψ : P.A ⟶ P.A, IsMonHom ψ ∧ u = ψ ^ (q ^ k)) → u = 1 := by
  intro hGI hmul hfin K _ _ P q hq u hu
  have := P.isAb.proper
  have : GeometricallyIntegral P.A.hom := hGI _ _ _ P.isAb.smooth P.isAb.geomConnected
  have : IsIntegral P.A.left := GeometricallyIntegral.isIntegral_of_subsingleton P.A.hom
  have : P.A.left.IsSeparated := ⟨by
    rw [← terminal.comp_from P.A.hom]; infer_instance⟩
  let E := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have hk : IsField Γ(Spec (CommRingCat.of K), ⊤) := E.toMulEquiv.isField (Field.toIsField K)
  obtain ⟨N, -, M, s, hcov, hs⟩ := P.ample ⊤ (isAffineOpen_top _)
  obtain ⟨n, hn⟩ := hfin K P _ (DVR.linComb_isLB P.L P.isLB (K := Unit) (fun _ => u.left) (fun _ => (N : ℤ)))
  obtain ⟨ψ, hψ, hu⟩ := hu n
  have H := hmul _ P (q ^ n)
  rw [← Nat.cast_pow] at H
  obtain ⟨α, hα⟩ := H
  have hnt : n ≤ (q ^ n) ^ 2 := (Nat.lt_pow_self hq).le.trans (Nat.le_self_pow two_ne_zero _)
  let w := (P.A.hom ⁻¹ᵁ ⊤).ι
  let f : P.A.left ⟶ (P.A.hom ⁻¹ᵁ ⊤).toScheme := IsOpenImmersion.lift w ψ.left (by
    rintro _ -
    rw [Scheme.Opens.range_ι]
    trivial)
  have hf : f ≫ w = ψ.left := IsOpenImmersion.lift_fac _ _ _
  have hu' : u.left = f ≫ w ≫ (mulA P.A (q ^ n)).left := by
    rw [← Category.assoc, hf, ← Over.comp_left, mulA, MonObj.comp_pow, Category.comp_id, hu]
  obtain ⟨z⟩ : Nonempty P.A.left := inferInstance
  obtain ⟨i, hi⟩ : ∃ i, f z ∈ nonzeroLocus (s i) := Opens.mem_iSup.1 (by rw [hcov]; trivial)
  obtain ⟨hD, r, hr, hsurj⟩ := hs i
  obtain ⟨J, hJ⟩ : ∃ J, Good P.L z J := by
    choose I hI using fun χ : P.A.left ⟶ P.A.left => exists_chart P.isLB (χ z)
    exact ⟨I, hI⟩
  let κ := germPull P.A.hom z ⊤ trivial
  let ρ := germPull f z _ hi
  have hy : IsUnit (sval (s i) f z J) := by
    obtain ⟨k, hk⟩ := Opens.mem_iSup.1 hi
    exact isUnit_sval (s i) f z hJ k hk
  have hrj : ∀ j, ρ (r j) ∈ κ.range := fun j => by
    have e : sval (s j) f z J = ρ (r j) * sval (s i) f z J := by
      have hm := hJ.mem (K := Fin N) (fun _ => w) f
      have hm' : f z ∈ nonzeroLocus (s i) ⊓ (powOver P.A P.L ⊤ N).U (fun _ => J (f ≫ w)) := ⟨hi, hm⟩
      have := congrArg (gs f z _) (hr j (fun _ => J (f ≫ w)))
      rw [gs_mul f z _ hm', gs_res f z _ hm', gs_res f z _ hm', gs_res f z _ hm'] at this
      rw [germPull_apply]
      exact this
    obtain ⟨b, hb⟩ := exists_monomials P.L P.isLB w N (s i) (s j) _ _ α hα f u.left hu' z J hJ
    choose σ hσ using fun a : Fin n => hb a (a.2.le.trans hnt)
    obtain ⟨c, hc, h0⟩ := hn σ
    have hm := hJ.mem (K := Unit) (fun _ => u.left) (𝟙 _)
    have h1 := (map_sum _ _ _).symm.trans
      ((congrArg (germPull (𝟙 _) z _ hm) (h0 (fun _ => J (𝟙 _ ≫ u.left)))).trans (map_zero _))
    have h2 : (∑ k : Fin n, (κ.comp E.symm.toRingHom) (E (c k)) * ρ (r j) ^ (k : ℕ)) *
        (sval (s i) f z J ^ ((q ^ n) ^ 2) * b.val) = 0 := by
      rw [Finset.sum_mul, ← h1]
      refine Finset.sum_congr rfl fun k _ => ?_
      refine Eq.trans ?_ ((germPull_apply (𝟙 _) z _ hm _).trans (gs_mul (𝟙 _) z _ hm _ _)).symm
      refine Eq.trans ?_ (congrArg₂ (· * ·) (gs_appLE (𝟙 _) P.A.hom z ⊤ _ le_top hm (c k)) (hσ k)).symm
      have e₁ : (κ.comp E.symm.toRingHom) (E (c k)) = gs (𝟙 _ ≫ P.A.hom) z ⊤ (c k) := by
        rw [Category.id_comp]
        exact (congrArg κ (E.symm_apply_apply _)).trans (germPull_apply _ _ _ _ _)
      rw [e₁, e, mul_pow]
      conv_lhs => rw [← Nat.add_sub_of_le (k.2.le.trans hnt), pow_add]
      ring
    obtain ⟨a, ha⟩ := mem_range_of_sum_eq_zero (κ.comp E.symm.toRingHom) (fun k => E (c k))
      (fun h => hc (funext fun k => E.injective ((congrFun h k).trans (map_zero E).symm))) (ρ (r j))
      ((mul_eq_zero.1 h2).resolve_right ((hy.pow _).mul b.isUnit).ne_zero)
    exact ⟨_, ha⟩
  have hall : ∀ a, ρ a ∈ κ.range := fun a => by
    obtain ⟨p, rfl⟩ := hsurj a
    induction p using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval₂Hom_C]
      obtain ⟨c', rfl⟩ : ∃ c', ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.appTop).hom c' = c :=
        have : IsIso (⊤ : (Spec (CommRingCat.of K)).Opens).ι :=
          inferInstanceAs (IsIso (Spec (CommRingCat.of K)).topIso.hom)
        (ConcreteCategory.bijective_of_isIso ((⊤ : (Spec (CommRingCat.of K)).Opens).ι.app ⊤)).2 c
      refine ⟨c', ?_⟩
      refine (germPull_apply _ _ _ _ _).trans (Eq.trans ?_ (germPull_apply _ _ _ _ _).symm)
      refine Eq.symm ((gs_appLE f _ z ⊤ _ le_top hi _).trans
        ((gs_pull _ (⊤ : (Spec (CommRingCat.of K)).Opens).ι z ⊤ trivial c').trans ?_))
      rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, hf, Over.w]
    | add p p' h h' => rw [map_add, map_add]; exact add_mem h h'
    | mul_X p j h => rw [map_mul, map_mul, MvPolynomial.eval₂Hom_X']; exact mul_mem h (hrj j)
  obtain ⟨p, hp⟩ := exists_factor f w P.A.hom hk _ hD z hi (fun a => by
    obtain ⟨c, hc⟩ := hall a
    exact ⟨c, (germPull_apply _ _ _ _ _).symm.trans (hc.trans (germPull_apply _ _ _ _ _))⟩)
  rw [hf] at hp
  have h1 : η[P.A].left ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have h2 : η[P.A].left = p := by
    have := congrArg (fun x => x.left) (IsMonHom.one_hom ψ)
    simp only [Over.comp_left] at this
    rw [← this, hp, ← Category.assoc, h1]
    exact Category.id_comp _
  have h3 : ψ = 1 := by
    apply Over.OverMorphism.ext
    rw [hp, ← h2, Hom.one_def]
    simp
  rw [hu, h3, one_pow]

end GlobalTheory.EndDivisible
