import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageEqOfAgreeOnClosedFibreDualNumbersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueAddEpsMulOnDualNumberThickeningStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.UnitPart

open GlobalTheory.KS

section Calc

variable {X Y Z : Scheme.{0}}

theorem pbT_pbT' (h : Z ⟶ Y) (f : Y ⟶ X) {U : X.Opens} {V : Y.Opens} {O : Z.Opens} (h₁ : V ≤ f ⁻¹ᵁ U)
    (h₂ : O ≤ h ⁻¹ᵁ V) (s : Γ(X, U)) : pbT h (pbT f s V) O = pbT (h ≫ f) s O := by
  rw [pbT_of_le f h₁, pbT_of_le h h₂, pbT_of_le (h ≫ f) (h₂.trans (h.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE h f U V O h₁ h₂)

theorem app_eq_pbT' (f : Z ⟶ Y) (U : Y.Opens) (s : Γ(Y, U)) : (f.app U).hom s = pbT f s (f ⁻¹ᵁ U) := by
  rw [pbT_of_le f le_rfl, Scheme.Hom.app_eq_appLE]

theorem val_res' {U V : X.Opens} (h : V ≤ U) (u : Γ(X, U)ˣ) : (res h u).val = rsT u.val V := (rsT_of_le h _).symm

theorem pbT_id_le' {O₀ O : X.Opens} (h : O ≤ O₀) (s : Γ(X, O₀)) : pbT (𝟙 X) s O = rsT s O := by
  rw [pbT, rsT, dif_pos (show O ≤ (𝟙 X : X ⟶ X) ⁻¹ᵁ O₀ from h), dif_pos h]
  rfl

theorem constFn_zero' {R : Type} [CommRing R] (q : X ⟶ Sp R) (O : X.Opens) : constFn q O 0 = 0 := by
  rw [constFn, map_zero, map_zero]

theorem constFn_comp_spMap' {R S : Type} [CommRing R] [CommRing S] (q : Y ⟶ Sp S) (x : R →+* S)
    (W : Y.Opens) (t : R) : constFn (q ≫ spMap x) W t = constFn q W (x t) := by
  have e1 : (q ≫ spMap x).appLE ⊤ W le_top = (spMap x).appLE ⊤ ⊤ le_top ≫ q.appLE ⊤ W le_top :=
    (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have h2 := congrArg (fun k => k.hom t) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom x))
  change ((q ≫ spMap x).appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom t) =
    (q.appLE ⊤ W le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of S)).inv.hom (x t))
  rw [e1, CommRingCat.comp_apply]
  congr 1
  simp only [CommRingCat.comp_apply] at h2
  exact h2.symm

theorem isUnit_of_mul_eq_one' {M : Type*} [CommMonoid M] (a b : M) (h : a * b = 1) : IsUnit a :=
  ⟨⟨a, b, h, by rw [mul_comm]; exact h⟩, rfl⟩

theorem isUnit_pbT (f : Z ⟶ Y) {U : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u : Γ(Y, U)ˣ) :
    IsUnit (pbT f u.val O) :=
  isUnit_of_mul_eq_one' _ (pbT f (u⁻¹).val O) (by rw [← pbT_mul, Units.mul_inv, pbT_one f h])

theorem exists_unit_glue {J : Type} (V : J → Y.Opens) (hV : ⨆ i, V i = ⊤) (a : ∀ i, Γ(Y, V i))
    (ha : ∀ i, IsUnit (a i)) (h : ∀ i l, rsT (a i) (V i ⊓ V l) = rsT (a l) (V i ⊓ V l)) :
    ∃ t : Γ(Y, ⊤), IsUnit t ∧ ∀ i, rsT t (V i) = a i := by
  choose b hb using fun i => (ha i).exists_right_inv
  obtain ⟨t, ht⟩ := exists_rsT_eq V (O := ⊤) (fun _ => le_top) hV.ge a h
  have hb' : ∀ i l, rsT (b i) (V i ⊓ V l) = rsT (b l) (V i ⊓ V l) := by
    intro i l
    have e1 : rsT (a i) (V i ⊓ V l) * rsT (b i) (V i ⊓ V l) = 1 := by
      rw [← rsT_mul, hb i, rsT_one inf_le_left]
    have e2 : rsT (a l) (V i ⊓ V l) * rsT (b l) (V i ⊓ V l) = 1 := by
      rw [← rsT_mul, hb l, rsT_one inf_le_right]
    rw [h i l] at e1
    calc rsT (b i) (V i ⊓ V l) = rsT (b i) (V i ⊓ V l) * (rsT (a l) (V i ⊓ V l) * rsT (b l) (V i ⊓ V l)) := by
          rw [e2, _root_.mul_one]
      _ = (rsT (a l) (V i ⊓ V l) * rsT (b i) (V i ⊓ V l)) * rsT (b l) (V i ⊓ V l) := by ring
      _ = rsT (b l) (V i ⊓ V l) := by rw [e1, _root_.one_mul]
  obtain ⟨t', ht'⟩ := exists_rsT_eq V (O := ⊤) (fun _ => le_top) hV.ge b hb'
  refine ⟨t, isUnit_of_mul_eq_one' t t' ?_, ht⟩
  refine eq_of_rsT_eq V (fun _ => le_top) hV.ge _ _ fun i => ?_
  rw [rsT_mul, ht, ht', hb, rsT_one le_top]

theorem pbT_mul_inv_eq_one (f : Z ⟶ Y) {U : Y.Opens} {O : Z.Opens} (h : O ≤ f ⁻¹ᵁ U) (u v : Γ(Y, U)ˣ)
    (huv : pbT f u.val O = pbT f v.val O) : pbT f (u * v⁻¹).val O = 1 := by
  rw [Units.val_mul, pbT_mul, huv, ← pbT_mul, ← Units.val_mul, _root_.mul_inv_cancel, Units.val_one, pbT_one f h]

theorem val_pull_g (L : LB X) (π : Y ⟶ X) (a b : PUnit → L.ι) :
    ((L.pull π).g a b).val = pbT π (L.g (a PUnit.unit) (b PUnit.unit)).val ((L.pull π).U a ⊓ (L.pull π).U b) := by
  show (∏ k : PUnit, (res _ (pullU π _ (L.g (a k) (b k)))) ^ (1 : ℤ)).val = _
  have hle : (L.pull π).U a ⊓ (L.pull π).U b ≤ π ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) :=
    fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
  rw [Fintype.prod_unique, zpow_one, pbT_of_le π hle]
  rfl

theorem pbT_pull_g {W : Scheme.{0}} (L : LB X) (π : Y ⟶ X) (j : W ⟶ Y) (a b : PUnit → L.ι) {O₁ : Y.Opens}
    (h₁ : O₁ ≤ (L.pull π).U a ⊓ (L.pull π).U b) {O : W.Opens} (hO : O ≤ j ⁻¹ᵁ O₁) :
    pbT j (res h₁ ((L.pull π).g a b)).val O = pbT (j ≫ π) (L.g (a PUnit.unit) (b PUnit.unit)).val O := by
  have hle : (L.pull π).U a ⊓ (L.pull π).U b ≤ π ⁻¹ᵁ (L.U (a PUnit.unit) ⊓ L.U (b PUnit.unit)) :=
    fun y hy => ⟨Set.mem_iInter.1 hy.1 PUnit.unit, Set.mem_iInter.1 hy.2 PUnit.unit⟩
  rw [val_res', pbT_rsT j h₁ hO, val_pull_g, pbT_pbT' j π hle (hO.trans (j.preimage_mono h₁))]

theorem pbT_div_g_pull {W : Scheme.{0}} (L : LB X) (π₁ π₂ : Y ⟶ X) (j : W ⟶ Y) (a b : PUnit → L.ι) (O : W.Opens)
    (hO : O ≤ j ⁻¹ᵁ ((LB.div (L.pull π₂) (L.pull π₁)).U (a, a) ⊓ (LB.div (L.pull π₂) (L.pull π₁)).U (b, b)))
    (hj : j ≫ π₁ = j ≫ π₂) :
    pbT j ((LB.div (L.pull π₂) (L.pull π₁)).g (a, a) (b, b)).val O = 1 := by
  refine pbT_mul_inv_eq_one j hO _ _ ?_
  refine (pbT_pull_g L π₂ j a b _ hO).trans ?_
  refine Eq.trans ?_ (pbT_pull_g L π₁ j a b _ hO).symm
  rw [hj]

end Calc

theorem pr_isPullback {k : Type} [Field k] {R : Type} [CommRing R] (ρ : R →+* DualNumber k) {X B A₀ : Scheme.{0}}
    {q : X ⟶ Sp R} {hB : B ⟶ Sp (DualNumber k)} {π₂ : B ⟶ X} {h0 : A₀ ⟶ Sp k} {m₀ : A₀ ⟶ X} {pr : B ⟶ A₀}
    (H₂ : IsPullback π₂ hB q (spMap (constHom ρ)))
    (H₀ : IsPullback m₀ h0 q (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)))
    (hpr : pr ≫ m₀ = π₂) (hpr' : pr ≫ h0 = hB ≫ spMap (algebraMap k (DualNumber k))) :
    IsPullback pr hB h0 (spMap (algebraMap k (DualNumber k))) := by
  refine IsPullback.of_right ?_ hpr' H₀
  have e : spMap (algebraMap k (DualNumber k)) ≫ spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) =
      spMap (constHom ρ) := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]; rfl
  rw [hpr, e]; exact H₂

theorem unit_eq_const {k : Type} [Field k] (A₀ : Over (Sp k)) [GrpObj A₀] (hA : IsAbelianScheme A₀)
    (u : Γ(A₀.left, ⊤)) (hu : IsUnit u) : ∃ c : kˣ, u = constFn A₀.hom ⊤ (c : k) := by
  have hb := GlobalTheory.allSixLaws.1.globalFns (Sp k) A₀ hA
  obtain ⟨x, hx⟩ := hb.2 u
  let e := RingEquiv.ofBijective A₀.hom.appTop.hom hb
  have hxu : IsUnit x := by
    have : x = e.symm u := by rw [← hx]; exact (e.symm_apply_apply x).symm
    rw [this]; exact hu.map e.symm
  have hc : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) := hxu.map _
  refine ⟨hc.unit, ?_⟩
  rw [IsUnit.unit_spec, ← hx]
  have hh : (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of k)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [hh]
  first
    | rfl
    | (rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; congr 2 <;> simp)

end GlobalTheory.UnitPart

namespace GlobalTheory.UnitPart

open GlobalTheory.KS

theorem unitPart : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι), ⨆ i, V i = ⊤ → (∀ i, V i ≤ P.L.U (jj i)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ (a : kˣ) (b : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) (algebraMap k (DualNumber k) (a : k)) + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (b i) (π₂ ⁻¹ᵁ V i) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ h₂ hagree A₀ _ m₀ hm₀ pr hpr hprA J V jj hV hVU w hw
  subst hpr
  have hpre : ∀ W : P.A.left.Opens, π₁ ⁻¹ᵁ W = (pr ≫ m₀) ⁻¹ᵁ W :=
    GlobalTheory.T.preimage_eq_of_agree_on_closedFibre_dualNumbers k P.A.left B'.left B'.hom π₁ (pr ≫ m₀) hagree
  have HP : IsPullback pr B'.hom A₀.hom (spMap (algebraMap k (DualNumber k))) :=
    pr_isPullback ρ h₂.1 hm₀.1 rfl hprA
  have hfa : spMap (TrivSqZeroExt.fstHom k k k).toRingHom ≫ spMap (algebraMap k (DualNumber k)) = 𝟙 _ := by
    have e : (TrivSqZeroExt.fstHom k k k).toRingHom.comp (algebraMap k (DualNumber k)) = RingHom.id k := by
      ext x; rfl
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, e]
    simp
  let j : A₀.left ⟶ B'.left := HP.lift (𝟙 A₀.left) (A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom)
    (by rw [Category.id_comp, Category.assoc, hfa, Category.comp_id])
  have hj1 : j ≫ pr = 𝟙 _ := HP.lift_fst _ _ _
  have hj2 : j ≫ B'.hom = A₀.hom ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom := HP.lift_snd _ _ _
  have hj12 : j ≫ π₁ = j ≫ pr ≫ m₀ := hagree A₀.left j A₀.hom hj2
  have hjm : j ≫ pr ≫ m₀ = m₀ := by rw [← Category.assoc, hj1, Category.id_comp]
  have hjm1 : j ≫ π₁ = m₀ := hj12.trans hjm
  have hmj : ∀ U : P.A.left.Opens, m₀ ⁻¹ᵁ U = j ⁻¹ᵁ ((pr ≫ m₀) ⁻¹ᵁ U) := fun U => by
    conv_lhs => rw [← hjm]
    rfl
  let c : J → (PUnit → P.L.ι) := fun i _ => jj i
  let C : J → B'.left.Opens := fun i => (LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).U (c i, c i)
  have hWC : ∀ i, (pr ≫ m₀) ⁻¹ᵁ V i ≤ C i := by
    intro i x hx
    have hx1 : x ∈ π₁ ⁻¹ᵁ V i := by rw [hpre]; exact hx
    exact ⟨Set.mem_iInter.2 fun _ => hVU i hx, Set.mem_iInter.2 fun _ => hVU i hx1⟩
  have hOj : ∀ i (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ V i → O ≤ j ⁻¹ᵁ ((pr ≫ m₀) ⁻¹ᵁ V i) := by
    intro i O hO
    rw [← hmj]; exact hO

  have hdec : ∀ i, ∃ ab : Γ(A₀.left, m₀ ⁻¹ᵁ V i) × Γ(A₀.left, m₀ ⁻¹ᵁ V i),
      rsT (w.s (c i, c i)).val ((pr ≫ m₀) ⁻¹ᵁ V i) = pbT pr ab.1 ((pr ≫ m₀) ⁻¹ᵁ V i) +
        constFn B'.hom ((pr ≫ m₀) ⁻¹ᵁ V i) DualNumber.eps * pbT pr ab.2 ((pr ≫ m₀) ⁻¹ᵁ V i) := by
    intro i
    obtain ⟨ab, hab, -⟩ := GlobalTheory.T.existsUnique_add_eps_mul_on_dualNumber_thickening k A₀.left B'.left A₀.hom B'.hom pr HP (m₀ ⁻¹ᵁ V i)
      (rsT (w.s (c i, c i)).val (pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i)))
    refine ⟨ab, ?_⟩
    rw [app_eq_pbT', app_eq_pbT'] at hab
    exact hab
  choose ab hab using hdec

  have hmod : ∀ i (O : A₀.left.Opens), O ≤ m₀ ⁻¹ᵁ V i →
      pbT j (rsT (w.s (c i, c i)).val ((pr ≫ m₀) ⁻¹ᵁ V i)) O = rsT (ab i).1 O := by
    intro i O hO
    have hle : (pr ≫ m₀) ⁻¹ᵁ V i ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i) := le_rfl
    rw [hab i, pbT_add, pbT_mul, pbT_pbT' j pr hle (hOj i O hO), pbT_pbT' j pr hle (hOj i O hO), hj1,
      pbT_constFn _ _ (hOj i O hO), hj2, constFn_comp_spMap']
    rw [show (TrivSqZeroExt.fstHom k k k).toRingHom DualNumber.eps = 0 from rfl, constFn_zero', zero_mul, add_zero,
      pbT_id_le' hO]
  have hagr : ∀ i i', rsT (ab i).1 (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') = rsT (ab i').1 (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') := by
    intro i i'
    have hOC : m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i' ≤ j ⁻¹ᵁ (C i ⊓ C i') := by
      intro x hx
      exact ⟨(hWC i) (hOj i _ le_rfl hx.1), (hWC i') (hOj i' _ le_rfl hx.2)⟩
    rw [← hmod i _ inf_le_left, ← hmod i' _ inf_le_right,
      pbT_rsT j (hWC i) ((hOj i _ inf_le_left)), pbT_rsT j (hWC i') ((hOj i' _ inf_le_right))]
    have hr := congrArg (fun u : Γ(B'.left, C i ⊓ C i')ˣ => pbT j u.val (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i')) (hw (c i, c i) (c i', c i'))
    rw [val_res', pbT_rsT j inf_le_left hOC, Units.val_mul, pbT_mul, val_res', pbT_rsT j inf_le_right hOC] at hr
    rw [hr]
    have hg : pbT j ((LB.div (P.L.pull (pr ≫ m₀)) (P.L.pull π₁)).g (c i, c i) (c i', c i')).val
        (m₀ ⁻¹ᵁ V i ⊓ m₀ ⁻¹ᵁ V i') = 1 := by
      exact pbT_div_g_pull P.L π₁ (pr ≫ m₀) j (c i) (c i') _ hOC hj12
    rw [hg, _root_.one_mul]
  have hunit : ∀ i, IsUnit (ab i).1 := by
    intro i
    have h1 := hmod i (m₀ ⁻¹ᵁ V i) le_rfl
    rw [rsT_self, pbT_rsT j (hWC i) (hOj i _ le_rfl)] at h1
    rw [← h1]
    exact isUnit_pbT j ((hOj i _ le_rfl).trans (j.preimage_mono (hWC i))) (w.s (c i, c i))
  have hcov : ⨆ i, m₀ ⁻¹ᵁ V i = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    have : m₀ x ∈ ⨆ i, V i := by rw [hV]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 this
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hi⟩
  obtain ⟨t, htu, ht⟩ := exists_unit_glue (fun i => m₀ ⁻¹ᵁ V i) hcov (fun i => (ab i).1) hunit hagr
  have hA₀ : IsAbelianScheme A₀ := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb hm₀
  obtain ⟨a, ha⟩ := unit_eq_const A₀ hA₀ t htu
  refine ⟨a, fun i => (ab i).2, fun i => ?_⟩
  have hle : (pr ≫ m₀) ⁻¹ᵁ V i ≤ pr ⁻¹ᵁ (m₀ ⁻¹ᵁ V i) := le_rfl
  rw [hab i, ← ht i, ha, rsT_constFn _ le_top, pbT_constFn _ _ hle, hprA, constFn_comp_spMap']

end GlobalTheory.UnitPart
