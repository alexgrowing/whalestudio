import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

noncomputable section

namespace GlobalTheory.TangentOrigin

section Points

variable {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}}

def evalPt (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) : Γ(X, U) →+* R :=
  (x.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom

theorem evalPt_res (x : Sp R ⟶ X) {U V : X.Opens} (e : V ≤ U) (hU : ⊤ ≤ x ⁻¹ᵁ U)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) (f : Γ(X, U)) : evalPt x V hV (resG X e f) = evalPt x U hU f := by
  have := congrArg (fun φ => ((φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R)).hom).hom f))
    (x.map_appLE hV (homOfLE e).op)
  exact this

theorem evalPt_spMap_comp (φ : R →+* R') (x : Sp R ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U)
    (h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U) (f : Γ(X, U)) :
    evalPt (spMap φ ≫ x) U h' f = φ (evalPt x U h f) := by
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  unfold evalPt
  rw [e1, Category.assoc, e2]
  rfl

theorem eq_spec_fromSpec {U : X.Opens} (hU : IsAffineOpen U) (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U) :
    x = Spec.map (CommRingCat.ofHom (evalPt x U h)) ≫ hU.fromSpec := by
  have := IsAffineOpen.SpecMap_appLE_fromSpec x hU (isAffineOpen_top _) h
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at this
  unfold evalPt
  rw [CommRingCat.ofHom_hom, Spec.map_comp, Category.assoc, this, ← Category.assoc,
    ← Spec.map_comp, Iso.inv_hom_id, Spec.map_id, Category.id_comp]

theorem ext_evalPt {U : X.Opens} (hU : IsAffineOpen U) {x y : Sp R ⟶ X} (hx : ⊤ ≤ x ⁻¹ᵁ U)
    (hy : ⊤ ≤ y ⁻¹ᵁ U) (e : evalPt x U hx = evalPt y U hy) : x = y := by
  exact (eq_spec_fromSpec hU x hx).trans (e ▸ (eq_spec_fromSpec hU y hy).symm)

theorem exists_evalPt_eq {U : X.Opens} (hU : IsAffineOpen U) (ψ : Γ(X, U) →+* R) :
    ∃ (x : Sp R ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ U), evalPt x U h = ψ := by
  have h : ⊤ ≤ (Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec) ⁻¹ᵁ U := by
    rw [Scheme.Hom.comp_preimage, hU.fromSpec_preimage_self]
    exact le_rfl
  refine ⟨Spec.map (CommRingCat.ofHom ψ) ≫ hU.fromSpec, h, ?_⟩
  have := eq_spec_fromSpec hU _ h
  rw [cancel_mono] at this
  have := Spec.map_injective this
  exact (congrArg CommRingCat.Hom.hom this).symm

theorem evalPt_constFn {k : Type} [CommRing k] (p : X ⟶ Sp k) (x : Sp R ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (a : k) :
    evalPt x U h (constFn p U a) = evalPt (x ≫ p) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) := by
  have := Scheme.Hom.appLE_comp_appLE x p ⊤ U ⊤ (fun _ _ => trivial) h
  unfold evalPt constFn
  rw [← this]
  rfl

theorem evalPt_spMap (φ : R →+* R') (a : R) :
    evalPt (spMap φ) ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = φ a := by
  have := evalPt_spMap_comp φ (𝟙 (Sp R)) ⊤ le_rfl le_rfl ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a)
  simp only [Category.comp_id] at this
  rw [this]
  congr 1
  have e : Scheme.Hom.appLE (𝟙 (Sp R)) ⊤ ⊤ le_rfl = 𝟙 _ := by
    simp [Scheme.Hom.appLE]
  unfold evalPt
  rw [e, Category.id_comp]
  exact Iso.inv_hom_id_apply (Scheme.ΓSpecIso (CommRingCat.of R)) a

theorem eq_spMap_of_evalPt {k : Type} [CommRing k] (y : Sp R ⟶ Sp k) (φ : k →+* R)
    (h : ∀ a, evalPt y ⊤ le_rfl ((Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom a) = φ a) :
    y = spMap φ := by
  refine ext_evalPt (isAffineOpen_top _) le_rfl le_rfl (RingHom.ext fun b => ?_)
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2 b
  exact (h a).trans (evalPt_spMap φ a).symm

theorem valAt'_eq_evalPt (x : Sp ℂ ⟶ X) (U : X.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) :
    valAt' x U f = evalPt x U h f := by
  unfold valAt'
  rw [dif_pos h]
  rfl

abbrev fstC : DualNumber ℂ →+* ℂ := (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom

theorem spMap_fst_surjective : Function.Surjective (spMap fstC) := by
  intro p
  refine ⟨(⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum ℂ), ?_⟩
  refine PrimeSpectrum.ext (Ideal.ext fun x => ?_)
  change x.fst ∈ (⊥ : Ideal ℂ) ↔ x ∈ PrimeSpectrum.asIdeal p
  rw [Ideal.mem_bot]
  constructor
  · intro hx
    apply p.isPrime.mem_of_pow_mem 2
    have : x ^ 2 = 0 := by
      rw [pow_two, show x = TrivSqZeroExt.inr x.snd from TrivSqZeroExt.ext hx rfl,
        TrivSqZeroExt.inr_mul_inr]
    rw [this]
    exact Ideal.zero_mem _
  · intro hx
    by_contra h0
    have hu : IsUnit x := TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx hu)

theorem top_le_preimage_iff (x : Sp (DualNumber ℂ) ⟶ X) (W : X.Opens) :
    ⊤ ≤ x ⁻¹ᵁ W ↔ ⊤ ≤ (spMap fstC ≫ x) ⁻¹ᵁ W := by
  constructor
  · intro h p _
    exact h (Set.mem_univ (spMap fstC p))
  · intro h p _
    obtain ⟨q, rfl⟩ := spMap_fst_surjective p
    exact h (Set.mem_univ q)

end Points

section Jets

variable {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g)

theorem ex_zero : u.ex 0 = 1 := by
  have := u.ex_add 0 0
  rw [add_zero] at this
  exact (mul_eq_left.1 this.symm)

theorem ex_zero_left : (u.ex 0).left = η[A].left := by
  rw [ex_zero, Hom.one_def, toUnit_unit, Category.id_comp]

theorem ex_left_comp (z : Fin g → ℂ) : (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ) := Over.w (u.ex z)

theorem eventually_mem {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) :
    ∀ᶠ z in 𝓝 (0 : Fin g → ℂ), ⊤ ≤ (u.ex z).left ⁻¹ᵁ W :=
  (u.hol W 0).1.mem_nhds h

theorem differentiableAt_val {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    DifferentiableAt ℂ (fun z => valAt' (u.ex z).left W f) 0 :=
  (u.hol W f).2.differentiableAt (eventually_mem u h)

theorem fderiv_val_const {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (a : ℂ) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (constFn A.hom W a)) 0 = 0 := by
  have : (fun z => valAt' (u.ex z).left W (constFn A.hom W a)) =ᶠ[𝓝 0] fun _ => a := by
    filter_upwards [eventually_mem u h] with z hz
    rw [valAt'_eq_evalPt _ _ hz, evalPt_constFn]
    have e : (u.ex z).left ≫ A.hom = spMap (RingHom.id ℂ) :=
      (ex_left_comp u z).trans (Spec.map_id _).symm
    exact (congrArg (fun y : Sp ℂ ⟶ Sp ℂ => evalPt y ⊤ le_rfl
      ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (evalPt_spMap _ a)
  rw [this.fderiv_eq]
  simp

theorem fderiv_val_add {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f f' : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (f + f')) 0 =
      fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 +
        fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 := by
  have : (fun z => valAt' (u.ex z).left W (f + f')) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left W f + valAt' (u.ex z).left W f' := by
    filter_upwards [eventually_mem u h] with z hz
    simp only [valAt'_eq_evalPt _ _ hz, map_add]
  rw [this.fderiv_eq, fderiv_fun_add (differentiableAt_val u h f) (differentiableAt_val u h f')]

theorem fderiv_val_mul {W : A.left.Opens} (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f f' : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left W (f * f')) 0 =
      valAt' (u.ex 0).left W f • fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 +
        valAt' (u.ex 0).left W f' • fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 := by
  have : (fun z => valAt' (u.ex z).left W (f * f')) =ᶠ[𝓝 0]
      fun z => valAt' (u.ex z).left W f * valAt' (u.ex z).left W f' := by
    filter_upwards [eventually_mem u h] with z hz
    simp only [valAt'_eq_evalPt _ _ hz, map_mul]
  rw [this.fderiv_eq, fderiv_fun_mul (differentiableAt_val u h f) (differentiableAt_val u h f')]

theorem fderiv_val_res {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    fderiv ℂ (fun z => valAt' (u.ex z).left V (resG A.left e f)) 0 =
      fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 := by
  apply Filter.EventuallyEq.fderiv_eq
  filter_upwards [eventually_mem u hW, eventually_mem u hV] with z hz hz'
  rw [valAt'_eq_evalPt _ _ hz, valAt'_eq_evalPt _ _ hz', evalPt_res]

def jet (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) :
    Γ(A.left, W) →+* DualNumber ℂ where
  toFun f := (evalPt (u.ex 0).left W h f, fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)
  map_one' := by
    refine TrivSqZeroExt.ext (map_one (evalPt (u.ex 0).left W h)) ?_
    have := fderiv_val_const u h 1
    rw [show constFn A.hom W 1 = 1 by simp [constFn]] at this
    change fderiv ℂ (fun z => valAt' (u.ex z).left W 1) 0 w = 0
    rw [this]
    rfl
  map_zero' := by
    refine TrivSqZeroExt.ext (map_zero (evalPt (u.ex 0).left W h)) ?_
    have := fderiv_val_const u h 0
    rw [show constFn A.hom W 0 = 0 by simp [constFn]] at this
    change fderiv ℂ (fun z => valAt' (u.ex z).left W 0) 0 w = 0
    rw [this]
    rfl
  map_add' f f' := by
    refine TrivSqZeroExt.ext (map_add (evalPt (u.ex 0).left W h) f f') ?_
    change fderiv ℂ (fun z => valAt' (u.ex z).left W (f + f')) 0 w = _
    rw [fderiv_val_add u h]
    rfl
  map_mul' f f' := by
    refine TrivSqZeroExt.ext (map_mul (evalPt (u.ex 0).left W h) f f') ?_
    refine Eq.trans ?_ (DualNumber.snd_mul _ _).symm
    change fderiv ℂ (fun z => valAt' (u.ex z).left W (f * f')) 0 w =
      evalPt (u.ex 0).left W h f * fderiv ℂ (fun z => valAt' (u.ex z).left W f') 0 w +
        fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w * evalPt (u.ex 0).left W h f'
    rw [fderiv_val_mul u h, valAt'_eq_evalPt _ _ h, valAt'_eq_evalPt _ _ h,
      mul_comm (fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w)]
    rfl

theorem jet_fst (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (f : Γ(A.left, W)) : (jet u w W h f).fst = evalPt (u.ex 0).left W h f := rfl

theorem jet_snd (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (f : Γ(A.left, W)) :
    (jet u w W h f).snd = fderiv ℂ (fun z => valAt' (u.ex z).left W f) 0 w := rfl

theorem jet_res (w : Fin g → ℂ) {W V : A.left.Opens} (e : V ≤ W) (hW : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W)
    (hV : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ V) (f : Γ(A.left, W)) :
    jet u w V hV (resG A.left e f) = jet u w W hW f := by
  refine TrivSqZeroExt.ext (evalPt_res _ e hW hV f) ?_
  rw [jet_snd, jet_snd, fderiv_val_res u e hW hV]

theorem evalPt_ex_const (z : Fin g → ℂ) {W : A.left.Opens} (h : ⊤ ≤ (u.ex z).left ⁻¹ᵁ W) (a : ℂ) :
    evalPt (u.ex z).left W h (constFn A.hom W a) = a := by
  rw [evalPt_constFn]
  have e : (u.ex z).left ≫ A.hom = spMap (RingHom.id ℂ) :=
    (ex_left_comp u z).trans (Spec.map_id _).symm
  exact (congrArg (fun y : Sp ℂ ⟶ Sp ℂ => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (evalPt_spMap _ a)

theorem jet_const (w : Fin g → ℂ) (W : A.left.Opens) (h : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (a : ℂ) :
    jet u w W h (constFn A.hom W a) = algebraMap ℂ (DualNumber ℂ) a := by
  refine TrivSqZeroExt.ext (evalPt_ex_const u 0 h a) ?_
  rw [jet_snd, fderiv_val_const u h]
  rfl

variable {u}

theorem tangent_comp {v : epsR ℂ ⟶ A} (hv : IsTangent v) :
    spMap fstC ≫ v.left = (u.ex 0).left := hv.trans (ex_zero_left u).symm

theorem tangent_mem_iff {v : epsR ℂ ⟶ A} (hv : IsTangent v) (W : A.left.Opens) :
    ⊤ ≤ v.left ⁻¹ᵁ W ↔ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W := by
  rw [← tangent_comp (u := u) hv]
  exact top_le_preimage_iff v.left W

theorem tangent_fst {v : epsR ℂ ⟶ A} (hv : IsTangent v) {W : A.left.Opens}
    (h : ⊤ ≤ v.left ⁻¹ᵁ W) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ W) (f : Γ(A.left, W)) :
    (evalPt (R := DualNumber ℂ) v.left W h f).fst = evalPt (u.ex 0).left W h0 f := by
  have key : ∀ (y : Sp ℂ ⟶ A.left) (hy : ⊤ ≤ y ⁻¹ᵁ W), spMap fstC ≫ v.left = y →
      (evalPt (R := DualNumber ℂ) v.left W h f).fst = evalPt y W hy f := by
    rintro y hy rfl
    exact (evalPt_spMap_comp fstC v.left W h hy f).symm
  exact key _ h0 (tangent_comp hv)

theorem tangent_const (v : epsR ℂ ⟶ A) {W : A.left.Opens} (h : ⊤ ≤ v.left ⁻¹ᵁ W) (a : ℂ) :
    evalPt (R := DualNumber ℂ) v.left W h (constFn A.hom W a) = algebraMap ℂ (DualNumber ℂ) a := by
  rw [evalPt_constFn]
  have e : v.left ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := Over.w v
  exact (congrArg (fun y : Sp (DualNumber ℂ) ⟶ Sp ℂ => evalPt y ⊤ le_rfl
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom a)) e).trans (evalPt_spMap _ a)

theorem isDiff_iff {v : epsR ℂ ⟶ A} (hv : IsTangent v) {U : A.left.Opens} (hU : IsAffineOpen U)
    (h : ⊤ ≤ v.left ⁻¹ᵁ U) (h0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U) (w : Fin g → ℂ) :
    u.IsDiff w v ↔ evalPt (R := DualNumber ℂ) v.left U h = jet u w U h0 := by
  constructor
  · intro hd
    refine RingHom.ext fun f => TrivSqZeroExt.ext (tangent_fst hv h h0 f) (hd U h f)
  · intro he W hW f
    have hW0 := (tangent_mem_iff (u := u) hv W).1 hW
    let pt : (𝟙_ (Over (Sp ℂ))).left := (default : PrimeSpectrum ℂ)
    have hsub : ∀ q : (𝟙_ (Over (Sp ℂ))).left, q = pt := fun q =>
      Subsingleton.elim (α := PrimeSpectrum ℂ) q pt
    obtain ⟨s, hsW, hs⟩ := hU.exists_basicOpen_le (V := W)
      ⟨(u.ex 0).left pt, hW0 (Set.mem_univ pt)⟩ (h0 (Set.mem_univ pt))
    have hB0 : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ A.left.basicOpen s := by
      intro q _
      rw [hsub q]
      exact hs
    have hB := (tangent_mem_iff (u := u) hv _).2 hB0
    have := hU.isLocalization_basicOpen s
    have heq : evalPt (R := DualNumber ℂ) v.left _ hB = jet u w _ hB0 := by
      apply IsLocalization.ringHom_ext (Submonoid.powers s)
      refine RingHom.ext fun b => ?_
      change evalPt (R := DualNumber ℂ) v.left _ hB (resG A.left (A.left.basicOpen_le s) b) =
        jet u w _ hB0 (resG A.left (A.left.basicOpen_le s) b)
      rw [evalPt_res _ _ h, jet_res u w _ h0, he]
    change (evalPt (R := DualNumber ℂ) v.left W hW f).snd = (jet u w W hW0 f).snd
    rw [← evalPt_res _ hsW hW hB, ← jet_res u w hsW hW0 hB0, heq]

end Jets

theorem tangent_bijection :
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) := by
  rintro A _ L g u ⟨U, t, hU, h0, huniq, ht⟩
  have hjet : ∀ w i, (jet u w U h0 (t i)).snd = w i := by
    intro w i
    have := (hasFDerivAt_pi'.1 ht i).fderiv
    rw [jet_snd, this]
    rfl
  refine ⟨fun v hv => ?_, fun w => ?_⟩
  · have h := (tangent_mem_iff (u := u) hv U).2 h0
    refine ⟨fun i => (evalPt (R := DualNumber ℂ) v.left U h (t i)).snd, ?_, fun w hw => ?_⟩
    · set w : Fin g → ℂ := fun i => (evalPt (R := DualNumber ℂ) v.left U h (t i)).snd with hw
      refine (isDiff_iff hv hU h h0 w).2 ?_
      let D : Γ(A.left, U) →+ ℂ :=
        { toFun := fun f => (evalPt (R := DualNumber ℂ) v.left U h f).snd - (jet u w U h0 f).snd
          map_zero' := by simp
          map_add' := fun f f' => by
            simp only [map_add, TrivSqZeroExt.snd_add]
            ring }
      have hD : ∀ f, D f =
          (evalPt (R := DualNumber ℂ) v.left U h f).snd - (jet u w U h0 f).snd := fun _ => rfl
      have hz : D = 0 := by
        apply huniq
        · intro a
          rw [hD, tangent_const, jet_const, sub_self]
        · intro f f'
          rw [hD, hD, hD, map_mul, map_mul, DualNumber.snd_mul, DualNumber.snd_mul,
            tangent_fst hv h h0, tangent_fst hv h h0, jet_fst, jet_fst, valAt'_eq_evalPt _ _ h0,
            valAt'_eq_evalPt _ _ h0]
          ring
        · intro i
          rw [hD, hjet, sub_self]
      refine RingHom.ext fun f => TrivSqZeroExt.ext (tangent_fst hv h h0 f) ?_
      have := hD f
      rw [hz] at this
      exact sub_eq_zero.1 this.symm
    · replace hw := (isDiff_iff hv hU h h0 w).1 hw
      funext i
      rw [hw, hjet]
  · obtain ⟨x, hx, hxe⟩ := exists_evalPt_eq hU (jet u w U h0)
    have hover : x ≫ A.hom = spMap (algebraMap ℂ (DualNumber ℂ)) := by
      refine eq_spMap_of_evalPt _ _ fun a => ?_
      rw [← evalPt_constFn A.hom x U hx, hxe, jet_const]
    let v : epsR ℂ ⟶ A := Over.homMk x hover
    have hv : IsTangent v := by
      refine Eq.trans ?_ (ex_zero_left u)
      refine ext_evalPt hU ((top_le_preimage_iff x U).1 hx) h0 (RingHom.ext fun f => ?_)
      refine (evalPt_spMap_comp fstC x U hx _ f).trans ?_
      rw [hxe]
      rfl
    refine ⟨v, ⟨hv, (isDiff_iff hv hU hx h0 w).2 hxe⟩, ?_⟩
    rintro v' ⟨hv', hd'⟩
    have h' := (tangent_mem_iff (u := u) hv' U).2 h0
    rw [isDiff_iff hv' hU h' h0] at hd'
    exact Over.OverMorphism.ext (ext_evalPt hU h' hx (hd'.trans hxe.symm))

theorem tangent_bijection_of_values :
    (∀ (X : Scheme.{0}) (x : Sp ℂ ⟶ X), (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U ↔ x (default : PrimeSpectrum ℂ) ∈ U) ∧ (∀ (U : X.Opens), ⊤ ≤ x ⁻¹ᵁ U → ∃ e : Γ(X, U) →+* ℂ, ∀ f, valAt' x U f = e f) ∧ (∀ (U V : X.Opens) (h : V ≤ U) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ V → valAt' x V (resG X h f) = valAt' x U f) ∧ (∀ (Y : Scheme.{0}) (φ : X ⟶ Y) (U : Y.Opens) (f : Γ(Y, U)), valAt' x (φ ⁻¹ᵁ U) ((φ.app U).hom f) = valAt' (x ≫ φ) U f) ∧ (∀ (U : X.Opens) (f : Γ(X, U)), ⊤ ≤ x ⁻¹ᵁ X.basicOpen f ↔ valAt' x U f ≠ 0) ∧ (∀ (p : X ⟶ Sp ℂ), x ≫ p = 𝟙 _ → ∀ (U : X.Opens) (a : ℂ), ⊤ ≤ x ⁻¹ᵁ U → valAt' x U (constFn p U a) = a)) →
    (∀ (A : Over (Sp ℂ)) [GrpObj A] (L : LB A.left) (g : ℕ) (u : HolUnif A L g), (∃ (U : A.left.Opens) (t : Fin g → Γ(A.left, U)), IsAffineOpen U ∧ ⊤ ≤ (u.ex 0).left ⁻¹ᵁ U ∧ (∀ D : Γ(A.left, U) →+ ℂ, (∀ a, D (constFn A.hom U a) = 0) → (∀ f f', D (f * f') = valAt' (u.ex 0).left U f * D f' + valAt' (u.ex 0).left U f' * D f) → (∀ i, D (t i) = 0) → D = 0) ∧ HasFDerivAt (fun w i => valAt' (u.ex w).left U (t i)) (ContinuousLinearMap.id ℂ (Fin g → ℂ)) 0) → (∀ v, IsTangent v → ∃! w, u.IsDiff w v) ∧ (∀ w, ∃! v, IsTangent v ∧ u.IsDiff w v)) :=
  fun _ => tangent_bijection

end GlobalTheory.TangentOrigin
