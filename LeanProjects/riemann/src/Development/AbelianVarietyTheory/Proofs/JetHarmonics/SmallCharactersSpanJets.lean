import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.OneCHyp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.JetLemmaStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.IsUnivChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.UnivChartLoc
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallCombinationStrictMinMod
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsDivOfExpandsAt
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MemBasicOpenOfIsUnit
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.KerJetAugEqSpanTorusUnionQuotient
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.GermEvalOneStandardPointSelf
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThickenedPointToTorusExtensionGenerator

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SmallJets

section Alg

theorem isUnit_of_aug {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (aug : A →ₐ[R] R) {n : ℕ}
    (h : RingHom.ker aug ^ (n + 1) = ⊥) {a : A} (ha : IsUnit (aug a)) : IsUnit a := by
  have hm : a - algebraMap R A (aug a) ∈ RingHom.ker aug := by simp [RingHom.mem_ker]
  have hn : IsNilpotent (a - algebraMap R A (aug a)) := ⟨n + 1, by
    have := Ideal.pow_mem_pow hm (n + 1)
    rwa [h, Ideal.mem_bot] at this⟩
  have := hn.isUnit_add_right_of_commute (ha.map (algebraMap R A)) (Commute.all _ _)
  simpa using this

theorem isLocalRing_of_aug {R A : Type} [CommRing R] [IsLocalRing R] [CommRing A] [Algebra R A] (aug : A →ₐ[R] R)
    {n : ℕ} (h : RingHom.ker aug ^ (n + 1) = ⊥) : IsLocalRing A := by
  have : Nontrivial A := aug.toRingHom.domain_nontrivial
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (aug a) with h1 | h1
  · exact Or.inl (isUnit_of_aug aug h h1)
  · exact Or.inr (isUnit_of_aug aug h (by rwa [map_sub, map_one]))

theorem eq_top_of_monomials {S A : Type} [CommRing S] [CommRing A] (f : S →+* A) (I : Ideal A) (n : ℕ)
    (hI : I ^ (n + 1) = ⊥) (hc : ∀ a, ∃ s, a - f s ∈ I) {r : ℕ} (v : Fin r → A) (t : Set A) (ht : I = Ideal.span t)
    (htv : ∀ y ∈ t, (∃ s, y = f s) ∨ ∃ j s s', y = f s * v j + f s') (N : AddSubgroup A)
    (hN : ∀ e : Fin r → ℕ, ∑ j, e j ≤ n → ∀ s, f s * ∏ j, v j ^ e j ∈ N) : N = ⊤ := by
  classical
  letI := f.toAlgebra
  let M : ℕ → Submodule S A := fun m => Submodule.span S {y | ∃ e : Fin r → ℕ, ∑ j, e j ≤ m ∧ y = ∏ j, v j ^ e j}
  have mono : ∀ m, M m ≤ M (m + 1) := fun m => Submodule.span_mono fun y ⟨e, he, hy⟩ => ⟨e, by omega, hy⟩
  have mulv : ∀ m j, ∀ y ∈ M m, y * v j ∈ M (m + 1) := by
    intro m j y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨e, he, rfl⟩ := hy
      refine Submodule.subset_span ⟨e + Pi.single j 1, ?_, ?_⟩
      · simp only [Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, if_true]
        omega
      · simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
        congr 1
        rw [Finset.prod_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
        simp
    | zero => simp
    | add a b _ _ ha hb => rw [add_mul]; exact add_mem ha hb
    | smul s a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ _ ha
  have mult : ∀ m, ∀ y ∈ M m, ∀ u ∈ t, y * u ∈ M (m + 1) := by
    intro m y hy u hu
    rcases htv u hu with ⟨s, rfl⟩ | ⟨j, s, s', rfl⟩
    · rw [mul_comm]; exact mono m ((M m).smul_mem s hy)
    · have e : y * (f s * v j + f s') = s • (y * v j) + s' • y := by
        show _ = f s * _ + f s' * _
        ring
      rw [e]
      exact add_mem (Submodule.smul_mem _ _ (mulv m j y hy)) (mono m (Submodule.smul_mem _ _ hy))
  have zero : ∀ a, a ∈ M 0 ⊔ (I ^ (0 + 1)).restrictScalars S := fun a => by
    obtain ⟨s, hs⟩ := hc a
    refine Submodule.mem_sup.2 ⟨s • 1, Submodule.smul_mem _ _ (Submodule.subset_span ⟨0, by simp, by simp⟩),
      a - f s, by simpa using hs, ?_⟩
    show f s * 1 + _ = _
    ring
  have step : ∀ m, ∀ a ∈ I ^ m, a ∈ M m ⊔ (I ^ (m + 1)).restrictScalars S := by
    intro m
    induction m with
    | zero => exact fun a _ => zero a
    | succ m ih =>
      intro a ha
      rw [pow_succ] at ha
      refine Submodule.mul_induction_on ha (fun x hx y hy => ?_) fun x y hx hy => add_mem hx hy
      rw [ht] at hy
      induction hy using Submodule.span_induction generalizing x with
      | mem y hy =>
        obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (ih x hx)
        rw [add_mul]
        refine Submodule.add_mem_sup (mult m p hp y hy) ?_
        rw [Submodule.restrictScalars_mem, pow_succ]
        exact Ideal.mul_mem_mul hi (ht ▸ Ideal.subset_span hy)
      | zero => simp
      | add a b _ _ ha hb => rw [mul_add]; exact add_mem (ha x hx) (hb x hx)
      | smul s a _ ha =>
        rw [smul_eq_mul, ← _root_.mul_assoc]
        exact ha _ (Ideal.mul_mem_right _ _ hx)
  have all : ∀ m a, a ∈ M m ⊔ (I ^ (m + 1)).restrictScalars S := by
    intro m
    induction m with
    | zero => exact zero
    | succ m ih =>
      intro a
      obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (ih a)
      exact add_mem (Submodule.mem_sup_left (mono m hp)) (step (m + 1) i hi)
  have fin : ∀ y ∈ M n, ∀ s, f s * y ∈ N := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => obtain ⟨e, he, rfl⟩ := hy; exact hN e he
    | zero => simp
    | add a b _ _ ha hb => intro s; rw [mul_add]; exact add_mem (ha s) (hb s)
    | smul s' a _ ha =>
      intro s
      have := ha (s * s')
      rwa [map_mul, _root_.mul_assoc] at this
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨p, hp, i, hi, rfl⟩ := Submodule.mem_sup.1 (all n a)
  rw [Submodule.restrictScalars_mem, hI, Ideal.mem_bot] at hi
  simpa [hi] using fin p hp 1

open Chart ChartBaseChange

theorem finite_jet (R : Type) [CommRing R] [IsNoetherianRing R] (d n : ℕ) : Module.Finite R (JetR R (Fin d) n) :=
  Module.finite_of_surjective_of_ker_le_nilradical (jetAug R (Fin d) n) (aug_surj _)
    (fun a ha => elt_nil _ (ker_jetAug_nil (R := R) (Fin d) n) a ha) (IsNoetherian.noetherian _)

theorem mem_map_of_jetCoeff {R : Type} [CommRing R] (p : Ideal R) (d n : ℕ) {a : JetR R (Fin d) n}
    (ha : jetCoeff R (R ⧸ p) (Fin d) n a = 0) : a ∈ p.map (algebraMap R (JetR R (Fin d) n)) := by
  let π := Ideal.Quotient.mkₐ R (p.map (algebraMap R (JetR R (Fin d) n)))
  have hJ : ((RingHom.ker (jetAug R (Fin d) n)).map π) ^ (n + 1) = ⊥ := by
    rw [← Ideal.map_pow, ker_jetAug_pow, Ideal.map_bot]
  let g := jetLift (R ⧸ p) _ hJ (fun j => π (zR n j)) (fun j => Ideal.mem_map_of_mem _ (zR_mem_ker n j))
  have e : (g.restrictScalars R).comp (jetCoeff R (R ⧸ p) (Fin d) n) = π := jet_ext fun j => by
    show g (jetCoeff R (R ⧸ p) (Fin d) n (zR n j)) = _
    rw [jetCoeff_zR, jetLift_zR]
  have := AlgHom.congr_fun e a
  rw [AlgHom.comp_apply, ha, map_zero] at this
  exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

theorem eq_top_of_jetCoeff {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (p : Ideal R)
    (hp : p ≤ maximalIdeal R) (d n : ℕ) (N : Submodule R (JetR R (Fin d) n))
    (h : ∀ y, ∃ a ∈ N, jetCoeff R (R ⧸ p) (Fin d) n a = y) : N = ⊤ := by
  have := finite_jet R d n
  refine eq_top_iff.2 (Submodule.le_of_le_smul_of_le_jacobson_bot (I := p) Module.Finite.fg_top
    (hp.trans (maximalIdeal_le_jacobson _)) fun a _ => ?_)
  obtain ⟨a', ha', e⟩ := h (jetCoeff R (R ⧸ p) (Fin d) n a)
  have hm := mem_map_of_jetCoeff p d n (a := a - a') (by rw [map_sub, e, sub_self])
  refine Submodule.mem_sup.2 ⟨a', ha', a - a', ?_, add_sub_cancel _ _⟩
  rw [Ideal.smul_top_eq_map]
  exact hm

end Alg

section Local

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

theorem sval_pull_of_ratio (hL : L.IsLB) {Z : Scheme.{0}} (s : LB.Sec (LB.LinComb L φ ε)) (m : Z ⟶ Y)
    (τ : LB.Gen (LB.LinComb L (fun k => m ≫ φ k) ε)) (hτ : τ.IsGen) (u : Γ(Z, ⊤))
    (h : ∀ z J, Good L z J → sval s m z J = gs (𝟙 Z) z ⊤ u * (val τ (𝟙 Z) z J).val)
    {W : Scheme.{0}} (g : W ⟶ Z) (w : W) {J} (hJ : Good L w J) :
    sval s (g ≫ m) w J = gs g w ⊤ u * (val τ g w J).val := by
  have key : ∀ {W : Scheme.{0}} (g : W ⟶ Z) (w : W) {J}, Good L w J →
      sval (SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) u (Geo.Tor.genSec τ hτ)) g w J = gs g w ⊤ u * (val τ g w J).val :=
    fun g w J hJ => (gs_mul g w _ (hJ.mem _ g) _ _).trans (congrArg₂ (· * ·) (gs_res g w _ (hJ.mem _ g) _)
      (sval_genSec τ hτ g w hJ))
  have e := sec_ext_val hL (s := SectionArithmetic.pullSec s m) (s' := SectionArithmetic.secCMul (V := ⊤) (fun _ => le_top) u (Geo.Tor.genSec τ hτ))
    fun z J hJ => by rw [SectionArithmetic.sval_pullSec s m _ z hJ, Category.id_comp, h z J hJ, key _ z hJ]
  rw [← SectionArithmetic.sval_pullSec s m g w hJ, ← key g w hJ]
  exact congrArg (gs g w _) (e _)

theorem exists_val_local (c : X → L.ι) (hc : ∀ x, x ∈ L.U (c x)) {A : Type} [CommRing A] [IsLocalRing A]
    (r : Sp A ⟶ Y) (t : LB.Gen (LB.LinComb L φ ε)) : ∃ a : Aˣ, ∀ (Z : Scheme.{0}) (g : Z ⟶ Sp A) (z : Z),
      g z = closedPoint A → (val t (g ≫ r) z (fun ψ => c (ψ z))).val = cst g z a := by
  let j : K → L.ι := fun k => c ((r ≫ φ k) (closedPoint A))
  have hm : ∀ p : Sp A, r p ∈ LB.wchart L φ j := fun p =>
    (Scheme.preimage_eq_top_of_closedPoint_mem (R := .of A) r (U := LB.wchart L φ j)
      (Set.mem_iInter.2 fun k => hc ((r ≫ φ k) (closedPoint A)))).ge (Set.mem_univ p)
  have le : (⊤ : (Sp A).Opens) ≤ r ⁻¹ᵁ LB.wchart L φ j := fun p _ => hm p
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.toMonoidHom (res le (pullU r _ (t.s j))),
    fun Z g z hz => ?_⟩
  have e1 := val_of t (g ≫ r) z (fun ψ => c (ψ z)) j (fun k => congrArg c (by
    show ((g ≫ r) ≫ φ k) z = (r ≫ φ k) (closedPoint A)
    rw [Category.assoc, Scheme.Hom.comp_apply, hz]))
  refine (congrArg Units.val (e1.trans ((gm_pull g r z _ (hm _) _).symm.trans (gm_res g z le trivial _).symm))).trans
    ((gs_unit g z ⊤ trivial _).symm.trans (congrArg (gs g z ⊤) ?_))
  simp

theorem bijective_germOf (A : Type) [CommRing A] [IsLocalRing A] :
    Function.Bijective (IntegralJets.germOf (A := A) (closedPoint A)) := by
  have e : IntegralJets.germOf (A := A) (closedPoint A) = (stalkClosedPointIso (CommRingCat.of A)).inv.hom := by
    have := germ_stalkClosedPointIso_hom (CommRingCat.of A)
    rw [← Iso.eq_comp_inv, ← Iso.inv_comp_eq] at this
    exact congrArg CommRingCat.Hom.hom this
  rw [e]
  exact ConcreteCategory.bijective_of_isIso (stalkClosedPointIso (CommRingCat.of A)).inv

theorem cst_spMap {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (z : Sp B) (a : A) :
    cst (Geo.Tor.spMap f) z a = IntegralJets.germOf z (f a) := IntegralJets.gs_const f z a

end Local

theorem exists_unit_prod {S A X : Type} [CommRing S] [CommRing A] [AddCommGroup X] (f : S →+* A) (v : X → Aˣ)
    (hv : ∀ a b, ∃ u : Sˣ, (v (a + b) : A) * f u = v a * v b) {r : ℕ} (b : Fin r → X) (e : Fin r → ℕ) :
    ∃ u : Sˣ, (v (∑ j, e j • b j) : A) * f u = ∏ j, (v (b j) : A) ^ e j := by
  let H : Subgroup Aˣ := (Units.map f.toMonoidHom).range
  let θ : X →+ Additive (Aˣ ⧸ H) := AddMonoidHom.mk' (fun χ => Additive.ofMul (QuotientGroup.mk' H (v χ))) fun a b => by
    obtain ⟨u, hu⟩ := hv a b
    rw [← ofMul_mul, ← map_mul]
    refine congrArg Additive.ofMul (QuotientGroup.eq.2 ⟨u, eq_inv_mul_of_mul_eq (Units.ext hu)⟩)
  have h : QuotientGroup.mk' H (v (∑ j, e j • b j)) = QuotientGroup.mk' H (∏ j, v (b j) ^ e j) := by
    show Additive.toMul (θ (∑ j, e j • b j)) = _
    rw [map_sum, toMul_sum, map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_nsmul, toMul_nsmul, map_pow]
    rfl
  obtain ⟨u, hu⟩ := QuotientGroup.eq.1 h
  refine ⟨u, ?_⟩
  have := congrArg Units.val (mul_eq_of_eq_inv_mul hu)
  simpa using this

section Torus

open Chart ChartBaseChange
open scoped CategoryTheory.Obj

theorem ker_jetAug_eq (k : Type) [CommRing k] (hk : IsField k) (X : Type) [AddCommGroup X] (r : ℕ)
    (b : Module.Basis (Fin r) ℤ X) (G B : Over (Spec (CommRingCat.of k))) [GrpObj G] [GrpObj B] (q : G ⟶ B)
    (i : splitTorus (Spec (CommRingCat.of k)) X ⟶ G) (hq : IsMonHom q) (hi : IsMonHom i)
    (hpb : IsPullback i (toUnit _) q η[B]) (d g n : ℕ) (x : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin d) m) ⟶ G)
    (xB : ∀ m : ℕ, sp (R₀ := k) (JetR k (Fin g) m) ⟶ B) (hx : IsUnivChart G d x) (hxB : IsUnivChart B g xB)
    (ψ : JetR k (Fin g) n →ₐ[k] JetR k (Fin d) n) (hψ : x n ≫ q = Chart.spMap ψ ≫ xB n) (T : Fin r → JetR k (Fin d) n)
    (hT : ∀ j, jetAug k (Fin d) n (T j) = 0)
    (h : ∀ (φ : JetR k (Fin d) n →ₐ[k] DualNumber k)
      (y : sp (R₀ := k) (DualNumber k) ⟶ splitTorus (Spec (CommRingCat.of k)) X), Chart.spMap φ ≫ x n = y ≫ i → ∀ j,
      (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).inv.hom (1 + φ (T j)) =
        y.left.appTop.hom (charUnit (Spec (CommRingCat.of k)) X (b j)).val) :
    RingHom.ker (jetAug k (Fin d) n) = Ideal.span (Set.range T ∪ Set.range fun l => ψ (zR n l)) := by
  letI := hk.toField
  exact ker_jetAug_eq_span_torus_union_quotient k X r b G B q i hq hi hpb d g n x xB hx hxB ψ hψ T hT h

theorem ker_fst_sq (k : Type) [CommRing k] : RingHom.ker (TrivSqZeroExt.fstHom k k k) ^ (1 + 1) = ⊥ := by
  rw [← le_bot_iff, pow_two, Ideal.mul_le]
  intro u hu u' hu'
  have h1 : u.fst = 0 := hu
  have h2 : u'.fst = 0 := hu'
  rw [Ideal.mem_bot]
  ext <;> simp [h1, h2]

theorem spMap_closedPoint_dual {k : Type} [CommRing k] (hk : IsField k) {d n : ℕ} [IsLocalRing (JetR k (Fin d) n)]
    [IsLocalRing (DualNumber k)] (φ : JetR k (Fin d) n →ₐ[k] DualNumber k) :
    Geo.Tor.spMap φ.toRingHom (closedPoint _) = closedPoint _ := by
  have ha : (TrivSqZeroExt.fstHom k k k).comp φ = jetAug k (Fin d) n := jet_ext fun l => by
    letI := hk.toField
    rw [jetAug_zR]
    exact ((elt_nil _ (ker_jetAug_nil (R := k) (Fin d) n) _ (zR_mem_ker n l)).map _).eq_zero
  have : IsLocalHom φ.toRingHom := ⟨fun s hs => isUnit_of_aug _ (ker_jetAug_pow _ _)
    (ha ▸ hs.map (TrivSqZeroExt.fstHom k k k))⟩
  exact IsLocalRing.comap_closedPoint φ.toRingHom

theorem one_add_normalised {k A B : Type} [CommRing k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (φ : A →ₐ[k] B) (v : A) (w : kˣ) (χ : B) (h : φ v = χ * algebraMap k B w.val) :
    1 + φ (algebraMap k A w⁻¹.val * v - 1) = χ := by
  rw [map_sub, map_mul, map_one, AlgHom.commutes, h, add_sub_cancel, mul_left_comm, ← map_mul, Units.inv_mul,
    map_one, _root_.mul_one]

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (e : ℕ)

theorem torus_jets (hk : IsField (R ⧸ I ^ (e + 1))) (c : D.toPre.P.A.left → D.toPre.P.L.ι)
    (hc : ∀ x, x ∈ D.toPre.P.L.U (c x)) {d g : ℕ} (n : ℕ) (x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G)
    (hx : IsUnivChart G d x) (xB : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin g) m) ⟶ D.toPre.P.A)
    (hxB : IsUnivChart D.toPre.P.A g xB) {r : ℕ} (b : Module.Basis (Fin r) ℤ D.toPre.X)
    [IsLocalRing (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)] [IsLocalRing (JetR R (Fin g) n)] :
    ∃ (p : Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n) ⟶ (thickObj R I e G).left)
      (f : JetR R (Fin g) n →+* JetR (R ⧸ I ^ (e + 1)) (Fin d) n) (v : D.toPre.X → (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)ˣ),
      p ≫ fGl I G e = Geo.Tor.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin d) n).toRingHom ≫ (x n).left ∧
      p ≫ pGl U e = Geo.Tor.spMap f ≫ (xB n).left ∧ Geo.Tor.spMap f (closedPoint _) = closedPoint _ ∧
      (∀ χ, (val (tG U e χ) p (closedPoint _) (fun ψ => c (ψ (closedPoint _)))).val =
        IntegralJets.germOf (closedPoint _) (v χ).val) ∧
      ∀ N : AddSubgroup (JetR (R ⧸ I ^ (e + 1)) (Fin d) n),
        (∀ a : Fin r → ℕ, ∑ j, a j ≤ n → ∀ s, f s * v (∑ j, a j • b j) ∈ N) → N = ⊤ := by
  have hloc : IsLocalRing (R ⧸ I ^ (e + 1)) := by letI := hk.toField; infer_instance
  have hmk : IsLocalHom (algebraMap R (R ⧸ I ^ (e + 1))) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have hG : IsGrpPullback (thickObj R I e G) G (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (e + 1)))))
    (pullback.fst G.hom (thick R I e)) := isGrpPullback_pullback G (thick R I e)
  have hB : IsGrpPullback (thickObj R I e D.toPre.P.A) D.toPre.P.A
    (Spec.map (CommRingCat.ofHom (algebraMap R (R ⧸ I ^ (e + 1)))))
    (pullback.fst D.toPre.P.A.hom (thick R I e)) := isGrpPullback_pullback _ (thick R I e)
  choose x' hx' using fun m => push_surjective hG (Chart.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin d) m) ≫ x m)
  choose xB' hxB' using fun m => push_surjective hB (Chart.spMap (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) m) ≫ xB m)
  have hu := isUnivChart_baseChange hG hx hx'
  have huB := isUnivChart_baseChange hB hxB hxB'
  have hq := (U.gt e).q_hom
  obtain ⟨ψ, ⟨hψa, hψ⟩, -⟩ := huB.2.2 _ (jetAug _ (Fin d) n) n (ker_jetAug_pow _ _) (x' n ≫ (U.gt e).q)
    (by rw [← Category.assoc, spMap_jetAug_alt hu n, MonObj.one_comp])
  let p : Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n) ⟶ (thickObj R I e G).left := (x' n).left
  let fa : JetR R (Fin g) n →ₐ[R] JetR (R ⧸ I ^ (e + 1)) (Fin d) n :=
    (ψ.restrictScalars R).comp (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) n)
  let f := fa.toRingHom
  have hp : p ≫ pGl U e = Geo.Tor.spMap f ≫ (xB n).left := by
    have e1 : push hB (x' n ≫ (U.gt e).q) = Chart.spMap fa ≫ xB n := by
      rw [hψ, push_spMap, hxB', ← Category.assoc, Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm.trans (congrArg (·.left) e1)
  have hfa : ∀ s, jetAug _ (Fin d) n (f s) = algebraMap R _ (jetAug R (Fin g) n s) := fun s =>
    AlgHom.congr_fun (jet_ext (ψ₁ := ((jetAug _ (Fin d) n).restrictScalars R).comp fa)
      (ψ₂ := (Algebra.ofId R _).comp (jetAug R (Fin g) n)) fun j => by
        show (jetAug _ (Fin d) n).comp ψ (jetCoeff R (R ⧸ I ^ (e + 1)) (Fin g) n (zR n j)) =
          algebraMap R _ (jetAug R (Fin g) n (zR n j))
        rw [hψa, jetCoeff_zR, jetAug_zR, jetAug_zR, map_zero]) s
  have hfl : IsLocalHom f := ⟨fun s hs => isUnit_of_aug _ (ker_jetAug_pow (R := R) (Fin g) n)
    (hmk.1 _ (hfa s ▸ hs.map (jetAug _ (Fin d) n)))⟩
  have hfc : Geo.Tor.spMap f (closedPoint _) = closedPoint _ := IsLocalRing.comap_closedPoint f
  choose v hv using fun χ => exists_val_local c hc p (tG U e χ)
  have hv1 : ∀ χ, (val (tG U e χ) p (closedPoint _) (fun ψ => c (ψ (closedPoint _)))).val =
      IntegralJets.germOf (closedPoint _) (v χ).val := fun χ => by
    have := hv χ _ (𝟙 _) _ rfl
    rw [Category.id_comp] at this
    exact this.trans (IntegralJets.germOf_eq _ _).symm
  have hmul : ∀ χ χ', ∃ u : (JetR R (Fin g) n)ˣ, (v (χ + χ')).val * f u = v χ * v χ' := by
    intro χ χ'
    have hJ : Good (Z := Sp (JetR (R ⧸ I ^ (e + 1)) (Fin d) n)) D.toPre.P.L (closedPoint _)
      (fun ψ => c (ψ (closedPoint _))) := fun ψ => hc _
    let m : D.toPre.P.A ⟶ G3 D.toPre.P.A :=
      lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (𝟙 _))
    obtain ⟨u, hu⟩ := exists_val_local (φ := thφ D.toPre.P.A (x3 D.toPre.P.A)) (ε := thε) c hc
      ((xB n).left ≫ m.left) D.toPre.cub.t
    have e1 : lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG) = (U.gt e).pG ≫ m := by
      simp only [m, comp_lift, ← Category.assoc, comp_toUnit, Category.comp_id]
    have e2 : p ≫ (lift (toUnit _ ≫ D.toPre.c χ) (lift (toUnit _ ≫ D.toPre.c χ') (U.gt e).pG)).left =
        Geo.Tor.spMap f ≫ (xB n).left ≫ m.left := by
      rw [e1, ← Category.assoc, ← hp, Category.assoc]
      rfl
    have h := (val_mul hJ _ _ _).symm.trans ((val_corr hJ ((U.gt e).t_mul χ χ') p).trans (val_mul hJ _ _ _))
    have h2 := ((congrArg Units.val ((val_pull hJ _ _ p).trans (congrArg (fun q => val _ q _ _) e2))).trans
      (hu _ _ _ hfc)).trans (cst_spMap f _ _)
    refine ⟨u, (bijective_germOf _).1 ?_⟩
    rw [map_mul, map_mul, ← hv1, ← hv1, ← hv1, ← h2]
    exact congrArg Units.val h
  refine ⟨p, f, v, congrArg (·.left) (hx' n), hp, hfc, hv1, fun N hN => ?_⟩
  let aug := jetAug (R ⧸ I ^ (e + 1)) (Fin d) n
  let w : Fin r → (R ⧸ I ^ (e + 1))ˣ := fun j => Units.map aug.toRingHom.toMonoidHom (v (b j))
  let T : Fin r → JetR (R ⧸ I ^ (e + 1)) (Fin d) n := fun j => algebraMap _ _ (w j)⁻¹.val * v (b j) - 1
  have hconst : ∀ a : R ⧸ I ^ (e + 1), ∃ s, f s = algebraMap _ _ a := fun a => by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
    exact ⟨algebraMap R _ a, fa.commutes a⟩
  have hker := ker_jetAug_eq _ hk _ r b _ _ _ _ hq (U.gt e).i_hom (U.gt e).isKernel d g n x' xB' hu huB ψ hψ T
    (fun j => by
      simp only [T]
      rw [map_sub, map_mul, AlgHom.commutes, map_one, sub_eq_zero]
      exact (w j).inv_mul) ?_
  · refine eq_top_of_monomials f _ n (ker_jetAug_pow _ _) (fun a => ?_) (fun j => v (b j)) _ hker ?_ N
      fun a ha s => ?_
    · obtain ⟨s, hs⟩ := hconst (aug a)
      exact ⟨s, by rw [hs]; simp [RingHom.mem_ker, aug]⟩
    · rintro _ (⟨j, rfl⟩ | ⟨l, rfl⟩)
      · obtain ⟨s, hs⟩ := hconst (w j)⁻¹.val
        exact Or.inr ⟨j, s, -1, by rw [hs, map_neg, map_one, ← sub_eq_add_neg]⟩
      · exact Or.inl ⟨zR n l, congrArg ψ (jetCoeff_zR n l).symm⟩
    · obtain ⟨u, hu⟩ := exists_unit_prod f v hmul b a
      rw [← hu, mul_comm (v _).val, ← _root_.mul_assoc, ← map_mul]
      exact hN a ha _
  intro φ y hy j
  have hD : IsLocalRing (DualNumber (R ⧸ I ^ (e + 1))) := isLocalRing_of_aug _ (ker_fst_sq _)
  let φ₀ : JetR (R ⧸ I ^ (e + 1)) (Fin d) n →ₐ[R ⧸ I ^ (e + 1)] DualNumber (R ⧸ I ^ (e + 1)) :=
    (Algebra.ofId _ _).comp aug
  have h0 : Chart.spMap φ₀ ≫ x' n = 1 := JetGenerators.spMap_jetAug hu n
  have hJ : Good (Z := Sp (DualNumber (R ⧸ I ^ (e + 1)))) D.toPre.P.L (closedPoint _)
    (fun ψ => c (ψ (closedPoint _))) := fun ψ => hc _
  have h := TorusCoord.val_t_act (U.gt e) y 1 (b j) (𝟙 _) _ _ hJ
  have e1 : 𝟙 _ ≫ ((y ≫ (U.gt e).i) * 1).left = Geo.Tor.spMap φ.toRingHom ≫ p :=
    (Category.id_comp _).trans (congrArg (·.left) ((_root_.mul_one _).trans hy.symm))
  have e2 : 𝟙 _ ≫ (1 : sp (DualNumber (R ⧸ I ^ (e + 1))) ⟶ thickObj R I e G).left = Geo.Tor.spMap φ₀.toRingHom ≫ p :=
    (Category.id_comp _).trans (congrArg (·.left) h0.symm)
  replace h := (congrArg (fun q => val (tG U e (b j)) q _ _) e1).symm.trans
    (h.trans (congrArg (fun q => _ * val (tG U e (b j)) q _ _) e2))
  have h1 := (hv (b j) _ _ _ (spMap_closedPoint_dual hk φ)).trans (cst_spMap _ _ _)
  have h2 := (hv (b j) _ _ _ (spMap_closedPoint_dual hk φ₀)).trans (cst_spMap _ _ _)
  let χ : DualNumber (R ⧸ I ^ (e + 1)) := (Scheme.ΓSpecIso (CommRingCat.of (DualNumber (R ⧸ I ^ (e + 1))))).hom.hom
    (y.left.appTop.hom (charUnit _ _ (b j)).val)
  have h3 : (gm (𝟙 (Sp (DualNumber (R ⧸ I ^ (e + 1))))) (closedPoint _) ⊤
      (splitTorusPointsEquiv _ D.toPre.X _ y (Multiplicative.ofAdd (b j)))).val =
      IntegralJets.germOf (closedPoint _) χ :=
    (gs_unit _ _ ⊤ trivial _).symm.trans ((congrArg (gs _ _ ⊤) (splitTorusPointsEquiv_val _ _ _ y (b j))).trans
      (IntegralJets.germOf_hom _ _).symm)
  have h4 : φ (v (b j)) = χ * algebraMap _ _ (w j).val := (bijective_germOf _).1
    (h1.symm.trans ((congrArg Units.val h).trans ((congrArg₂ (· * ·) h3 h2).trans (map_mul _ _ _).symm)))
  exact (congrArg _ (one_add_normalised φ _ _ χ h4)).trans (Iso.hom_inv_id_apply _ _)

end Torus

section Main

open Chart ChartBaseChange

theorem expansion_single {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (U : UnifPre I D A G) (e q : ℕ) (σ : H0 U.LG.L q) (f : ∀ α, D.toPre.SecB q α)
    (hE : U.ExpandsAt e q σ f) {ϖ : R} (hϖ : ϖ ∈ I ^ (e + 1)) (χ : D.toPre.X)
    (hf : ∀ α, α ≠ χ → ∃ f' : D.toPre.SecB q α, SecIsMul D.toPre.P.A.hom ϖ (f α) f') {Z : Scheme.{0}}
    (p : Z ⟶ (thickObj R I e G).left) (z : Z) {J} (hJ : Good D.toPre.P.L z J) (jL : U.LG.L.ι)
    (hL : fGl I G e (p z) ∈ U.LG.L.U jL) :
    (wv U e p z (J (p ≫ pGl U e)) jL ^ q).val * sv U q σ (p ≫ fGl I G e) z jL =
      sval (f χ) (p ≫ pGl U e) z J * (val (tG U e χ) p z J).val := by
  obtain ⟨S, hS⟩ := expandsAt_val U e q σ f hE
  obtain ⟨h₀, h₁⟩ := hS _ p z J hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = (thickObj R I e G).hom ≫
      Geo.Tor.spMap (Ideal.Quotient.mk (I ^ (e + 1))) := Over.w (U.gt e).pG
  have h0 : cst ((p ≫ pGl U e) ≫ D.toPre.P.A.hom) z ϖ = 0 := by
    rw [Category.assoc, hc, ← Category.assoc, cst_comp, Ideal.Quotient.eq_zero_iff_mem.2 hϖ, cst, map_zero]
    exact gs_zero _ _ _ trivial
  refine (h₁ jL hL).trans (Finset.sum_eq_single χ (fun α _ hα => ?_) fun hχ => by rw [h₀ χ hχ, zero_mul])
  obtain ⟨f', hf'⟩ := hf α hα
  have : sval (f α) (p ≫ pGl U e) z J = 0 :=
    (secIsMul_gs hf' (p ≫ pGl U e) z _ (hJ.mem _ _)).trans (by rw [h0, zero_mul])
  rw [this, zero_mul]

theorem small_characters_span_jets : Laws → TwistBCSpanStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (ϖ : V), Irreducible ϖ → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Spec (CommRingCat.of V))) [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (Q : D.toPre.X → ℤ), QForm.IsQ D.toPre ϖ Q → ∀ (r : ℕ) (b : Module.Basis (Fin r) ℤ D.toPre.X) (Cc M₀ : ℝ), 0 ≤ Cc → 0 ≤ M₀ → (∀ j, (Q (b j) : ℝ) ≤ Cc) → (∀ j z, |(QForm.bOf D.toPre Q (b j) z : ℝ)| ≤ M₀ * Q z) → ∀ q n : ℕ, 4 * n + 4 ≤ q → (n : ℝ) * M₀ < q → ∀ (d : ℕ) (x : ∀ m : ℕ, Chart.sp (R₀ := V) (Chart.JetR V (Fin d) m) ⟶ G), Chart.IsUnivChart G d x → ∀ τ : LB.Gen (LB.LinComb U.LG.L (K := Fin 1) (fun _ => (x n).left ≫ 𝟙 G.left) (fun _ => (q : ℤ))), τ.IsGen → ∃ (l : ℕ) (σ : Fin l → H0 U.LG.L q) (f : Fin l → ∀ α, D.toPre.SecB q α) (χ : Fin l → D.toPre.X) (a : Fin l → Chart.JetR V (Fin d) n), (∀ i e, U.ExpandsAt e q (σ i) (f i)) ∧ (∀ i, ∃ Φ : Fam D.toPre (FractionRing V) q, (∀ α, GeneratorPullback.SecScal D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f i α) (DegPre.prB D.toPre (FractionRing V)).left 1)) ∧ (∀ i, (Q (χ i) : ℝ) ≤ (n : ℝ) ^ 2 * Cc) ∧ (∀ i α, (∀ z, α ≠ χ i + q • z) → ∀ j, (f i α).f j = 0) ∧ (∀ i, (∀ (z : (Chart.sp (R₀ := V) (Chart.JetR V (Fin d) n)).left) (J), Good U.LG.L z J → sval (σ i) (x n).left z J = gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (Chart.JetR V (Fin d) n))).inv.hom (a i)) * (val τ (𝟙 _) z J).val)) ∧ Submodule.span V (Set.range a) = ⊤ := by
  intro hL hTW V _ _ _ ϖ hϖ D A G _ _ U Q hQ r b Cc M₀ hC hM hb hB q n hq hn d x hx τ hτ
  classical
  let admitted : JetR V (Fin d) n → Prop := fun a => ∃ (σ : H0 U.LG.L q) (f : ∀ α, D.toPre.SecB q α) (χ : D.toPre.X),
    (∀ e, U.ExpandsAt e q σ f) ∧ (∃ Φ : Fam D.toPre (FractionRing V) q, ∀ α, GeneratorPullback.SecScal D.toPre.P.L
      (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε q) (Φ.s α) (D.toPre.famφB α) (DegPre.famε q) (f α)
      (DegPre.prB D.toPre (FractionRing V)).left 1) ∧ (Q χ : ℝ) ≤ (n : ℝ) ^ 2 * Cc ∧
    (∀ α, (∀ z, α ≠ χ + q • z) → ∀ j, (f α).f j = 0) ∧
    ∀ (z : (sp (R₀ := V) (JetR V (Fin d) n)).left) (J), Good U.LG.L z J → sval σ (x n).left z J =
      gs (𝟙 _) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).inv.hom a) * (val τ (𝟙 _) z J).val
  suffices h : Submodule.span V {a | admitted a} = ⊤ by
    have := finite_jet V d n
    obtain ⟨s, hs, e⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 (h ▸ Module.Finite.fg_top)
    choose σ f χ h1 h2 h3 h4 h5 using fun i : Fin s.card => hs (s.equivFin.symm i).2
    refine ⟨s.card, σ, f, χ, fun i => (s.equivFin.symm i).1, h1, h2, h3, h4, h5, ?_⟩
    rw [← h, e]
    congr 1
    ext a
    exact ⟨fun ⟨i, hi⟩ => hi ▸ (s.equivFin.symm i).2, fun ha => ⟨s.equivFin ⟨a, ha⟩, by simp⟩⟩
  have hk : IsField (V ⧸ maximalIdeal V ^ (0 + 1)) :=
    (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).1 (by rw [zero_add, pow_one]; infer_instance)
  have hloc : IsLocalRing (V ⧸ maximalIdeal V ^ (0 + 1)) := by letI := hk.toField; infer_instance
  have := D.toPre.P.isAb.smooth
  obtain ⟨g, xB, hxB⟩ := univChartLoc D.toPre.P.A
  have hl1 : IsLocalRing (JetR (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n) := isLocalRing_of_aug _ (ker_jetAug_pow _ _)
  have hl2 : IsLocalRing (JetR V (Fin g) n) := isLocalRing_of_aug _ (ker_jetAug_pow _ _)
  choose c hc using fun y : D.toPre.P.A.left => Geo.Tor.exists_chart D.toPre.P.isLB y
  obtain ⟨p, f, v, hp1, hp2, hfc, hv, hN⟩ := torus_jets U.toUnifPre 0 hk c hc n x hx xB hxB b
  let ρ := jetCoeff V (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n
  let z₀ : Sp (JetR (V ⧸ maximalIdeal V ^ (0 + 1)) (Fin d) n) := closedPoint _
  have hJ : Good D.toPre.P.L z₀ (fun ψ => c (ψ z₀)) := fun ψ => hc _
  obtain ⟨J', hJ'⟩ := TorusCoord.exists_good' U.LG.isLB z₀
  let jL := J' ((Geo.Tor.spMap ρ.toRingHom ≫ (x n).left) ≫ 𝟙 _)
  have hjL : fGl (maximalIdeal V) G 0 (p z₀) ∈ U.LG.L.U jL :=
    (congrArg (fun m => m z₀ ∈ U.LG.L.U jL) (hp1.trans (Category.comp_id _).symm)).mpr (hJ' _)
  obtain ⟨w, hw⟩ := (bijective_germOf _).2 (wv U.toUnifPre 0 p z₀ (c ((p ≫ pGl U.toUnifPre 0) z₀)) jL ^ q *
    val τ (Geo.Tor.spMap ρ.toRingHom) z₀ J').val
  have hwu : IsUnit w := by
    have : IsLocalHom (IntegralJets.germOf z₀) := IsLocalHom.of_surjective _ (bijective_germOf _).2
    exact this.1 w ((congrArg IsUnit hw).mpr (Units.isUnit _))
  have key : ∀ a : Fin r → ℕ, ∑ j, a j ≤ n → ∀ s, ∃ y, admitted y ∧ w * ρ y = f s * v (∑ j, a j • b j) := by
    intro a ha s
    obtain ⟨hQ1, hQ2⟩ := small_combination_strict_min_mod _ (QForm.bHom hϖ D hQ) Q (QForm.bOf_comm D)
      (QForm.two_Q_eq hϖ D hQ) (fun _ => QForm.Q_pos hϖ D hQ) r n q b Cc M₀ hC hM hb hB hn a ha
    generalize ∑ j, a j • b j = χ at hQ1 hQ2
    obtain ⟨t, ht⟩ := exists_gen_of_local (V := JetR V (Fin g) n) D.toPre.P.L D.toPre.P.isLB
      (fun i => (xB n).left ≫ D.toPre.famφB χ i) (DegPre.famε q)
    obtain ⟨u, hu⟩ := exists_val_local c hc (𝟙 _) t
    have hu1 := (congrArg (fun m => (val t m z₀ _).val) (Category.comp_id _).symm).trans
      ((hu _ (Geo.Tor.spMap f) z₀ hfc).trans (cst_spMap f _ _))
    obtain ⟨β, hβ⟩ := IntegralJets.integral_jets hL hTW V D.toPre q n hq χ g xB hxB t ht (s * u⁻¹.val)
    obtain ⟨Φ, F, hF1, hF2, hF3, hF4⟩ := integralFamily_of_strictMin hL V ϖ hϖ D Q hQ q (by omega) χ β hQ2
    obtain ⟨σ, hσ⟩ := IntegralExpansion.main hL V D A G U q (by omega) Φ F hF1
    obtain ⟨y, hy⟩ := IntegralJets.exists_ratio U.LG.isLB σ (x n).left τ hτ
    let y' : JetR V (Fin d) n := (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).hom.hom y
    have hy' : (Scheme.ΓSpecIso (CommRingCat.of (JetR V (Fin d) n))).inv.hom y' = y := Iso.hom_inv_id_apply _ _
    refine ⟨y', ⟨σ, F, χ, hσ, ⟨Φ, hF1⟩, hQ1, hF3, fun z J h => hy'.symm ▸ hy z J h⟩, (bijective_germOf _).1 ?_⟩
    have e1 := expansion_single U.toUnifPre 0 q σ F (hσ 0)
      (Ideal.pow_mem_pow ((mem_maximalIdeal _).2 hϖ.not_isUnit) (0 + 1)) χ (fun α hα => by
        rw [zero_add, pow_one]; exact hF4 α hα) p z₀ hJ jL hjL
    have e2 : sv U.toUnifPre q σ (p ≫ fGl (maximalIdeal V) G 0) z₀ jL =
        IntegralJets.germOf z₀ (ρ y') * (val τ (Geo.Tor.spMap ρ.toRingHom) z₀ J').val :=
      (congrArg (fun m => sv U.toUnifPre q σ m z₀ jL) hp1).trans
        ((sval_pull_of_ratio U.LG.isLB σ (x n).left τ hτ y hy (Geo.Tor.spMap ρ.toRingHom) z₀ hJ').trans
          (congrArg (· * _) ((congrArg (gs _ z₀ ⊤) hy'.symm).trans (cst_spMap ρ.toRingHom z₀ y'))))
    have e3 : sval (F χ) (p ≫ pGl U.toUnifPre 0) z₀ (fun ψ => c (ψ z₀)) = IntegralJets.germOf z₀ (f s) :=
      (congrArg₂ (fun σ m => sval σ m z₀ _) hF2 hp2).trans
        ((sval_pull_of_ratio D.toPre.P.isLB β (xB n).left t ht _ hβ (Geo.Tor.spMap f) z₀ hJ).trans
          ((congrArg₂ (· * ·) (cst_spMap f z₀ _) hu1).trans (by
            rw [← map_mul, ← map_mul, Units.inv_mul_cancel_right])))
    have e4 := (congrArg (_ * ·) e2).symm.trans (e1.trans (congrArg₂ (· * ·) e3 (hv χ)))
    refine (map_mul _ _ _).trans (Eq.trans ?_ (e4.trans (map_mul _ _ _).symm))
    exact (congrArg (· * _) (hw.trans (Units.val_mul _ _))).trans
      ((mul_right_comm _ _ _).trans (_root_.mul_assoc _ _ _))
  refine eq_top_of_jetCoeff (maximalIdeal V ^ (0 + 1)) (Ideal.pow_le_self (by omega)) d n _ fun y => ?_
  have htop := hN ((Submodule.span V {a | admitted a}).toAddSubgroup.map
    ((AddMonoidHom.mulLeft w).comp ρ.toRingHom.toAddMonoidHom)) fun a ha s => by
      obtain ⟨y, h1, h2⟩ := key a ha s
      exact ⟨y, Submodule.subset_span h1, h2⟩
  obtain ⟨a, ha, e⟩ : w * y ∈ _ := htop.ge (AddSubgroup.mem_top _)
  exact ⟨a, ha, hwu.mul_left_cancel e⟩

end Main

end GlobalTheory.SmallJets
