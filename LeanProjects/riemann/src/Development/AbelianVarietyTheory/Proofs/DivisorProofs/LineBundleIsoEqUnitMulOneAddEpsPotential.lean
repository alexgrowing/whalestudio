import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConnK
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LeISupInfPreimage
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
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
namespace GlobalTheory.ConnUnit
open GlobalTheory.KS

theorem constFn_mul {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp only [constFn, map_mul]

theorem constFn_eps_sq {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Sp (DualNumber k)) (O : X.Opens) :
    constFn q O DualNumber.eps * constFn q O DualNumber.eps = 0 := by
  rw [← constFn_mul, DualNumber.eps_mul_eps]; simp only [constFn, map_zero]

theorem rsT_resG {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT (resG Y h x) Q = rsT x Q := by
  rw [← rsT_of_le h, rsT_rsT h hQ]

theorem rsT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) {Q : Z.Opens} (hQ : Q ≤ f ⁻¹ᵁ U) :
    rsT ((f.app U).hom x) Q = pbT f x Q := by
  rw [rsT_of_le hQ, pbT_of_le f hQ]
  rfl

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem constFn_top_appTop {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (x : Γ(Sp R, ⊤)) :
    constFn q ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = q.appTop.hom x := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [e]
  exact congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_eq_app (f := q) (U := ⊤))

theorem preimage_le_of_eps {k : Type} [Field k] {B X : Scheme.{0}} (q : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X)
    (e : ∀ W : X.Opens, Γ(X, W) → Γ(B, π₂ ⁻¹ᵁ W))
    (hid : ∀ (W : X.Opens) (f : Γ(X, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W f) (W : X.Opens) : π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := by
  by_contra h
  have h1 := hid W 1
  rw [pbT, dif_neg h, pbT_one π₂ le_rfl] at h1
  have hu : (1 + constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) *
      (1 - constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) = 1 := by
    linear_combination (-(e W 1) ^ 2) * constFn_eps_sq q (π₂ ⁻¹ᵁ W)
  rw [← h1, zero_mul] at hu
  apply h
  intro y hy
  exfalso
  haveI : Nonempty (π₂ ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
  exact zero_ne_one hu

theorem rsT_inv_mul {Y : Scheme.{0}} {U : Y.Opens} (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ U) :
    rsT (↑(u⁻¹) : Γ(Y, U)) Q * rsT (u : Γ(Y, U)) Q = 1 := by
  rw [← rsT_mul, Units.inv_mul, rsT_one hQ]

theorem rsT_res_val {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT ((res h u : Γ(Y, V)ˣ) : Γ(Y, V)) Q = rsT (u : Γ(Y, U)) Q :=
  rsT_resG h (u : Γ(Y, U)) hQ

theorem rsT_pullU_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) {Q : Z.Opens}
    (hQ : Q ≤ f ⁻¹ᵁ U) : rsT ((pullU f U u : Γ(Z, f ⁻¹ᵁ U)ˣ) : Γ(Z, f ⁻¹ᵁ U)) Q = pbT f (u : Γ(Y, U)) Q :=
  rsT_app f U (u : Γ(Y, U)) hQ

theorem rsT_pull_g {Y Z : Scheme.{0}} (L : LB Y) (f : Z ⟶ Y) (a b : L.ι) (Q : Z.Opens)
    (hQ : Q ≤ f ⁻¹ᵁ (L.U a ⊓ L.U b)) (hQ' : Q ≤ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    rsT ((L.pull f).g (fun _ => a) (fun _ => b) : Γ(Z, (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b))) Q =
      pbT f (L.g a b : Γ(Y, L.U a ⊓ L.U b)) Q := by
  simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [rsT_res_val _ _ hQ', rsT_pullU_val _ _ _ hQ]

theorem isGen_rel {B X : Scheme.{0}} (L : LB X) (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂))
    (hw : w.IsGen) (a b : L.ι) (Q : B.Opens) (hQ1 : Q ≤ π₁ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (hQ2 : Q ≤ π₂ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    rsT (w.s (fun _ => a, fun _ => a)).val Q * pbT π₁ (L.g a b).val Q =
      pbT π₂ (L.g a b).val Q * rsT (w.s (fun _ => b, fun _ => b)).val Q := by
  have hQa : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => a, fun _ => a) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).1, Set.mem_iInter.2 fun _ => (hQ1 hy).1⟩
  have hQb : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => b, fun _ => b) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).2, Set.mem_iInter.2 fun _ => (hQ1 hy).2⟩
  have hQab := le_inf hQa hQb
  have h := congrArg (fun u => rsT (Units.val u) Q) (hw (fun _ => a, fun _ => a) (fun _ => b, fun _ => b))
  rw [rsT_res_val _ _ hQab, Units.val_mul, rsT_mul, rsT_res_val _ _ hQab] at h
  rw [h]
  simp only [LB.div]
  rw [Units.val_mul, rsT_mul]
  erw [rsT_res_val _ _ hQab]
  have hM := rsT_pull_g L π₂ a b Q hQ2 (le_inf (hQa.trans inf_le_left) (hQb.trans inf_le_left))
  have hN := rsT_pull_g L π₁ a b Q hQ1 (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [← map_inv]
  erw [rsT_res_val _ _ hQab]
  have hI := rsT_inv_mul ((L.pull π₁).g (fun _ => a) (fun _ => b))
    (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [hN] at hI
  rw [hM]
  rw [show ∀ x y z t : Γ(B, Q), x * y * z * t = x * z * (y * t) from fun _ _ _ _ => by ring]
  erw [hI]
  exact _root_.mul_one _

theorem unit_mul_one_add_eps : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ _ _ A₀ _ m₀ _ pr hpr _ J V jj ed pb hconn hid w hw
  obtain ⟨-, hcov, hVU, hcoc⟩ := hconn
  have hle : ∀ W, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W :=
    preimage_le_of_eps B'.hom π₁ π₂ (fun W f => pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) hid
  have hpre : ∀ U, π₂ ⁻¹ᵁ U = pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U => by rw [← hpr]; rfl
  have hE2 : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 :=
    fun O => constFn_eps_sq B'.hom O
  have hchart : ∀ i, π₂ ⁻¹ᵁ V i ≤ ((P.L.pull π₂).div (P.L.pull π₁)).U (fun _ => jj i, fun _ => jj i) :=
    fun i y hy => ⟨Set.mem_iInter.2 fun _ => hVU i hy, Set.mem_iInter.2 fun _ => hVU i (hle _ hy)⟩
  have hcovB : (⊤ : B'.left.Opens) ≤ ⨆ i, π₂ ⁻¹ᵁ V i := by
    have := GlobalTheory.KS.le_iSup_inf_preimage π₂ V hcov ⊤
    simpa only [top_inf_eq] using this

  let u : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i)
  let E : ∀ O : B'.left.Opens, Γ(B'.left, O) := fun O => constFn B'.hom O DualNumber.eps
  let Pf : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => pbT pr (pb i) (π₂ ⁻¹ᵁ V i)
  let t : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => u i * (1 - E _ * Pf i)
  let s : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i =>
    rsT ((w.s (fun _ => jj i, fun _ => jj i))⁻¹).val (π₂ ⁻¹ᵁ V i) * (1 + E _ * Pf i)

  have hres : ∀ i i', rsT (u i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i)) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i) inf_le_left _, rsT_pbT pr (hpre (V i)).le inf_le_left _,
      rsT_constFn B'.hom inf_le_left _⟩
  have hres' : ∀ i i', rsT (u i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i')) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i') inf_le_right _, rsT_pbT pr (hpre (V i')).le inf_le_right _,
      rsT_constFn B'.hom inf_le_right _⟩

  have key : ∀ i i', rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))) := by
    intro i i'
    have hVV : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
    have hQ2 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₂ ⁻¹ᵁ (V i ⊓ V i') := le_rfl
    have hQ1 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₁ ⁻¹ᵁ (V i ⊓ V i') := hQ2.trans (hle _)
    have rel := isGen_rel P.L π₁ π₂ w hw (jj i) (jj i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')
      (hQ1.trans (π₁.preimage_mono hVV)) (hQ2.trans (π₂.preimage_mono hVV))
    have h := hid (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
    rw [hcoc i i', pbT_mul, pbT_sub, pbT_pbT pr m₀ (m₀.preimage_mono hVV) (hpre _).le, hpr,
      pbT_rsT pr (m₀.preimage_mono inf_le_right) (hpre _).le, pbT_rsT pr (m₀.preimage_mono inf_le_left) (hpre _).le,
      pbT_rsT π₁ hVV (hle _), pbT_rsT π₂ hVV le_rfl] at h
    have hQeq : π₂ ⁻¹ᵁ (V i ⊓ V i') = π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' := rfl
    rw [hQeq] at h
    have hG : pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        pbT π₂ (P.L.g (jj i) (jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = 1 := by
      rw [← pbT_mul, Units.inv_mul, pbT_one π₂ (hQ2.trans (π₂.preimage_mono hVV))]
    rw [h] at rel
    linear_combination (-(rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') -
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))))) * hG
      - pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * rel

  have ht : ∀ i i', rsT (t i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (t i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    obtain ⟨a1, a2, a3⟩ := hres i i'
    obtain ⟨b1, b2, b3⟩ := hres' i i'
    simp only [t, rsT_mul, rsT_sub, rsT_one inf_le_left, rsT_one inf_le_right, a1, a2, a3, b1, b2, b3, key i i']
    linear_combination (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
      (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) *
      pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) * hE2 _
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    have hinv := rsT_inv_mul (w.s (fun _ => jj i, fun _ => jj i)) (hchart i)
    simp only [t, s, u]
    linear_combination (1 - E _ * Pf i * (E _ * Pf i)) * hinv - (Pf i * Pf i) * hE2 _
  have hs : ∀ i i', rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    have e1 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i)
    have e2 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i')
    simp only [rsT_mul, rsT_one inf_le_left, rsT_one inf_le_right] at e1 e2
    rw [← ht i i'] at e2
    linear_combination rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e1 - rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e2
  obtain ⟨T, hT⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB s hs
  have hTS : T * S = 1 := by
    refine GlobalTheory.KS.eq_of_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB _ _ fun i => ?_
    rw [rsT_mul, hT, hS, hts, rsT_one le_top]

  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb h₁
  have hbij := GlobalTheory.allSixLaws.1.globalFns (Sp (DualNumber k)) B' hab
  obtain ⟨x, hx⟩ := hbij.2 T
  obtain ⟨y, hy⟩ := hbij.2 S
  have hxy : x * y = 1 := hbij.1 (by rw [map_mul, hx, hy, hTS, map_one])
  refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x,
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom y,
    by rw [← map_mul, hxy, map_one], by rw [← map_mul, _root_.mul_comm, hxy, map_one]⟩, fun i => ?_⟩
  have hκ : constFn B'.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x) = T :=
    (constFn_top_appTop B'.hom x).trans hx
  have hc := hT i
  rw [← hκ, rsT_constFn B'.hom le_top] at hc
  simp only [t, u, Pf, E] at hc
  show u i = _
  simp only [u]
  linear_combination (-(1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i))) * hc +
    (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) * pbT pr (pb i) (π₂ ⁻¹ᵁ V i) ^ 2) * hE2 _

end GlobalTheory.ConnUnit
