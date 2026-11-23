import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.BasisB
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsChartFromCoordinatesStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIsGoodStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartDividedPowersGradedConstantStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationPropertyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CechRefinementCohomologyBijectiveStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CoordinatesRestrictAffineOpenStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteModulesSerreClassStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StableFamilyPropertiesStatement

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.FinOverO

section Les

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {A : C ⥤ CommAlgCat.{0} R}

theorem sub_H {R : Type} [CommRing R] (K : Cx.{1} R) (n : ℕ) (h : Subsingleton (K.X n)) : Subsingleton (K.H n) :=
  ⟨fun x y => by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact congrArg _ (Subtype.ext (Subsingleton.elim _ _))⟩

theorem sub_CH (F : C ⥤ ModuleCat.{0} R) (h : ∀ T, Subsingleton (F.obj T)) (n : ℕ) : Subsingleton (CH.H F n) :=
  sub_H (CH.cx F) n ⟨fun x y => funext fun s => (h _).elim _ _⟩

theorem sq_sub (a b : IdF A) (h : ∀ T, a.S T ≤ b.S T) (T : C) : Subsingleton ((sq a b).obj T) :=
  ⟨fun x y => by
    have key : ∀ z : sqM a b T, z = 0 := fun z => by
      obtain ⟨z, hz⟩ := z
      obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hz
      exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 (h T hw))
    exact (key x).trans (key y).symm⟩

variable (a c b : IdF A) (hbc : ∀ T, b.S T ≤ c.S T) (hca : ∀ T, c.S T ≤ a.S T)

theorem tau_inj (T : C) (x y : (sq c b).obj T)
    (h : (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T x =
      (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y) : x = y := by
  obtain ⟨x, hx⟩ := x
  obtain ⟨y, hy⟩ := y
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  have h1 : Ideal.Quotient.mk (b.S T) x = Ideal.Quotient.mk (b.S T) y :=
    congrArg (fun z => (show sqM a b T from z).1) h
  exact Subtype.ext h1

theorem tau_surj (T : C) (z : (sq a c).obj T) :
    ∃ y : (sq a b).obj T, (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T y = z := by
  obtain ⟨x, hx⟩ := z
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact ⟨sqMk a b w hw, rfl⟩

theorem tau_ex (T : C) (z : (sq a b).obj T)
    (h : (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T z = 0) :
    ∃ y : (sq c b).obj T, (sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y = z := by
  obtain ⟨x, hx⟩ := z
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  have h2 : w ∈ c.S T := Ideal.Quotient.eq_zero_iff_mem.1 (congrArg Subtype.val h)
  exact ⟨sqMk c b w h2, rfl⟩

theorem tau_comp (T : C) (y : (sq c b).obj T) :
    (sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).τ T
      ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).τ T y) = 0 := by
  obtain ⟨x, hx⟩ := y
  obtain ⟨w, hw, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  exact Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 hw)

theorem sq_exact (j : ℕ) :
    Function.Exact ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).pull j)
      ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).pull j) := by
  have inj : ∀ n, Function.Injective ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).hom.f n) :=
    fun n f g h => funext fun s => tau_inj a c b hca _ _ _ (congrFun h s)
  have surj : ∀ n, Function.Surjective ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).hom.f n) := by
    intro n f
    choose y hy using fun s : ComposableArrows C n => tau_surj a c b hbc _ (f s)
    exact ⟨y, funext hy⟩
  have ex : ∀ n, Function.Exact ((sqLe (a := c) (b := b) (a' := a) (b' := b) hca (fun _ => le_rfl)).hom.f n)
      ((sqLe (a := a) (b := b) (a' := a) (b' := c) (fun _ => le_rfl) hbc).hom.f n) := by
    intro n f
    constructor
    · intro h
      choose y hy using fun s : ComposableArrows C n => tau_ex a c b hbc hca _ (f s) (congrFun h s)
      exact ⟨y, funext hy⟩
    · rintro ⟨g, rfl⟩
      exact funext fun s => tau_comp a c b hbc hca _ (g s)
  obtain ⟨δ, -, -, e1, -, -⟩ := CrystallineSemistableComparison.P.les _ _ inj ex surj
  exact e1 j

end Les

section Chart

theorem dividedPowerFiltration_bot (O : Type) [CommRing O] {k : ℕ} (hk : 1 ≤ k) : pdP (dividedPowersBot O) k = ⊥ := by
  classical
  refine le_bot_iff.1 (Ideal.span_le.2 ?_)
  rintro _ ⟨l, hl, hr, rfl⟩
  have : ∃ q ∈ l, 1 ≤ q.1 := by
    by_contra hcon
    push_neg at hcon
    have : (l.map Prod.fst).sum = 0 := by
      refine List.sum_eq_zero fun x hx => ?_
      obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hx
      have := hcon q hq
      omega
    omega
  obtain ⟨q, hq, h1⟩ := this
  have h0 : (dividedPowersBot O).dpow q.1 q.2 = 0 := by
    have : q.2 = 0 := by simpa using hl q hq
    rw [this]
    exact (dividedPowersBot O).dpow_eval_zero (by omega)
  exact List.prod_eq_zero (List.mem_map.2 ⟨q, hq, h0⟩)

variable {O : Type} [CommRing O]

theorem van_coord (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}}
    (q : X ⟶ Spec (CommRingCat.of O)) {W : X.Opens} {d : ℕ} (c : Coord q W d) (r : ℕ) (hr : r < s) (b : ℕ) (hne : b ≠ r) :
    Subsingleton (HU (sq (thFil (smFun X q) r) (thFil (smFun X q) ((r : ℤ) + 1)))
      (St (γ := dividedPowersBot O) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) (TF l s) {W}) b) := by
  obtain ⟨c', e, hTF, -, -, -⟩ := GlobalTheory.T.exists_chart_from_coordinates (dividedPowersBot O) l s hb q (Ideal.Quotient.mk ⊥) (fun _ => rfl) c
  have hg := GlobalTheory.T.chart_is_good c'
  let Q : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥))) := St (TF l s) {W}
  have hQ : ∀ T, Q T → InU W T := fun T hT => by
    obtain ⟨_, V, hV, h⟩ := hT
    rw [Set.mem_singleton_iff.1 hV] at h
    exact h
  have hD : Q c'.D := ⟨hTF, W, rfl, c'.inV⟩
  obtain ⟨hpd, hgc⟩ := GlobalTheory.T.chart_divided_powers_graded_constant c' hg Q hQ hD
  obtain ⟨P, hP⟩ := hPoly (dividedPowersBot O) q (Ideal.Quotient.mk ⊥) l s {W}
  let E := c'.frame hg Q hQ hD
  let σ : ∀ T, E.D ⟶ T := fun T => (E.ne T).some
  have main := hLoc P (GlobalTheory.T.sheaf_filtration_property Q) E σ hgc (r : ℤ) (fun r' hr' => (hP r' (by omega)).1) b
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, r = b + k := ⟨r - b, by omega⟩
    have hk1 : 1 ≤ k := by omega
    have hall : ∀ z : CH.H (gr (sFil Q) (r : ℤ)) b, z = 0 := by
      intro z
      obtain ⟨x, hx, f, hf, rfl, hfs⟩ := (main.2 k (by push_cast; omega)).1 z
      have hx0 : ∀ I, x I = 0 := fun I => by
        have h2 : x I ∈ c'.D.pdPow ((k : ℤ).toNat) := hx I
        rw [Int.toNat_natCast] at h2
        rw [hpd k, dividedPowerFiltration_bot O hk1, Ideal.map_bot] at h2
        exact h2
      have f0 : f = 0 := funext fun s => Subtype.ext (by
        rw [hfs s]
        simp [hx0, Frame.form])
      subst f0
      exact Submodule.Quotient.mk_zero _
    exact ⟨fun y z => (hall y).trans (hall z).symm⟩
  · exact main.1 (by exact_mod_cast hgt)

end Chart

section Glob

variable {O : Type} [CommRing O]

theorem capO_affine {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} (U : Cov q) {n : ℕ} (i : Fin (n + 1) → U.ι) :
    IsAffineOpen (capO U.U i) := by
  classical
  have h := U.inter (Finset.univ.image i) ⟨i 0, Finset.mem_image_of_mem _ (Finset.mem_univ _)⟩
  have e : (⨅ α ∈ Finset.univ.image i, U.U α) = capO U.U i := by
    refine le_antisymm (le_iInf fun a => ?_) (le_iInf₂ fun α hα => ?_)
    · exact iInf₂_le (i a) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
    · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hα
      exact capO_le U.U i a
  rwa [e] at h

set_option maxHeartbeats 2000000 in
theorem gr_range [IsNoetherianRing O] (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (hSer : KH.GlobSerreSt) (hCech : KH.GrCechFin)
    (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    (U : Cov q) (r : ℤ) (hr : r < s) (j : ℕ) : Module.Finite O (HQ (TO q l s (Set.range U.U)) r (r + 1) j) := by
  obtain ⟨𝒮, h𝒮⟩ := GlobalTheory.T.finite_modules_serre_class O
  rcases lt_or_ge r 0 with h0 | h0
  · refine (h𝒮 _).1 (𝒮.zero _ (sub_CH _ (sq_sub _ _ fun T => ?_) j))
    have e1 : r.toNat = 0 := by omega
    have e2 : (r + 1).toNat = 0 := by omega
    change T.obj.pdPow r.toNat ≤ T.obj.pdPow (r + 1).toNat
    rw [e1, e2]
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le h0
    have hn : n < s := by exact_mod_cast hr
    refine (h𝒮 _).1 (hSer (sq (thFil (smFun X q) n) (thFil (smFun X q) ((n : ℤ) + 1))) (TF l s) U.U 𝒮 j ?_)
    intro a b hab
    by_cases hbn : b = n
    · subst hbn
      exact (h𝒮 _).2 (hCech l s hb q U b hn a)
    · refine 𝒮.zero _ (sub_H _ a ⟨fun x y => funext fun i => ?_⟩)
      have e := (GlobalTheory.T.stable_family_properties).2.2.2 (TF l s : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))) U.U i
      obtain ⟨c', -⟩ := GlobalTheory.T.coordinates_restrict_affine_open (U.c (i 0)) (capO_le U.U i 0) (capO_affine U i)
      have hv := van_coord hLoc hPoly l s hb q c' n hn b hbn
      rw [← e] at hv
      exact hv.elim _ _

theorem range_fin [IsNoetherianRing O] (hLoc : KH.LocGr) (hPoly : KH.PolyTf) (hSer : KH.GlobSerreSt) (hCech : KH.GrCechFin)
    (l s : ℕ) (hb : TFBase (dividedPowersBot O) l s) {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of O)) [IsProper q]
    (U : Cov q) (n : ℕ) (r r' : ℤ) (hn : r' = r + n) (hs : r' ≤ s) (j : ℕ) :
    Module.Finite O (HQ (TO q l s (Set.range U.U)) r r' j) := by
  obtain ⟨𝒮, h𝒮⟩ := GlobalTheory.T.finite_modules_serre_class O
  have hF := GlobalTheory.T.sheaf_filtration_property (TO q l s (Set.range U.U))
  induction n generalizing r with
  | zero =>
    have e : r' = r := by simpa using hn
    subst e
    exact (h𝒮 _).1 (𝒮.zero _ (sub_CH _ (sq_sub _ _ fun T => le_rfl) j))
  | succ n ih =>
    have h1 := ih (r + 1) (by rw [hn]; push_cast; ring)
    have h3 := gr_range hLoc hPoly hSer hCech l s hb q U r (by push_cast at hn; omega) j
    exact (h𝒮 _).1 (𝒮.mid _ _ _ _ _ (sq_exact (sFil _ r) (sFil _ (r + 1)) (sFil _ r')
      (fun T => hF.anti (by push_cast at hn; omega) T) (fun T => hF.anti (by omega) T) j) ((h𝒮 _).2 h1) ((h𝒮 _).2 h3))

theorem fin_surj {M N : Type 1} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (f : M →ₗ[O] N)
    (hf : Function.Surjective f) (h : Module.Finite O M) : Module.Finite O N :=
  Module.Finite.of_surjective f hf

theorem fin_bij {M N : Type 1} [AddCommGroup M] [Module O M] [AddCommGroup N] [Module O N] (f : M →ₗ[O] N)
    (hf : Function.Bijective f) (h : Module.Finite O N) : Module.Finite O M :=
  Module.Finite.of_surjective (LinearEquiv.ofBijective f hf).symm.toLinearMap (LinearEquiv.surjective _)

theorem inU_top {R : Type} [CommRing R] {I : Ideal R} {γ : DividedPowers I} {p : ℕ} {X : Scheme.{0}}
    {q : X ⟶ Spec (CommRingCat.of O)} {κ : O →+* R ⧸ I} (T : Thick (nlFun γ p X q κ)) : InU ⊤ T :=
  fun _ _ => trivial

end Glob

theorem finO : KH.LocGr → KH.PolyTf → KH.GlobSerreSt → KH.GrCechFin → FinO := by
  intro hLoc hPoly hSer hCech O _ _ l s hb X q _ U 𝒱 h𝒱 r r' hr hr' j
  have hU : Used (TF l s : ObjectProperty (Thick (nlFun (dividedPowersBot O) 0 X q (Ideal.Quotient.mk ⊥)))) :=
    Or.inl ⟨rfl, l, s, rfl⟩
  have h1 : TO q l s (Set.range U.U) ≤ TO q l s {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have h2 : TO q l s 𝒱 ≤ TO q l s {⊤} :=
    fun T hT => ⟨hT.1, ⊤, rfl, inU_top T⟩
  have c1 : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup (Set.range U.U) := by
    rintro W rfl
    rw [sSup_range, U.cover]
  have c2 : ∀ W ∈ ({⊤} : Set X.Opens), W ≤ sSup 𝒱 := by
    rintro W rfl
    rw [h𝒱]
  have B1 := (GlobalTheory.T.cech_refinement_cohomology_bijective _ hU _ _ h1 c1 j).1 r r'
  have B2 := (GlobalTheory.T.cech_refinement_cohomology_bijective _ hU _ _ h2 c2 j).1 r r'
  obtain ⟨n, hn⟩ : ∃ n : ℕ, r' = r + n := ⟨(r' - r).toNat, by omega⟩
  have hR := range_fin hLoc hPoly hSer hCech l s hb q U n r r' hn hr' j
  exact fin_surj _ B2.2 (fin_bij _ B1 hR)

end GlobalTheory.CompanionTheory.FinOverO
