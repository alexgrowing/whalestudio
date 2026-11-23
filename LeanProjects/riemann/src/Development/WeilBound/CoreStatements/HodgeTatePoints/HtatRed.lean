import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHtBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieBc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLieIso
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Statements.GeometryStatements.HTChartExists
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TwoWeightEqOneAddRoot
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsLast
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace PositivityTheory.HtPt.Htat.ChartRed

section Alg

variable {A B : Type} [CommRing A] [CommRing B] [Algebra A B]
  {M N : Type} [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N] [Module A N] [IsScalarTower A B N]
  {g : M →ₗ[A] N}

theorem dual_ext (hg : IsBaseChange B g) {y y' : Module.Dual B N} (h : ∀ m, y (g m) = y' (g m)) : y = y' := by
  refine LinearMap.ext fun n => ?_
  refine hg.inductionOn n (fun n => y n = y' n) (by simp) h ?_ ?_
  · intro s n hn; simp [hn]
  · intro a b ha hb; simp [ha, hb]

theorem span_range_eq_top (hg : IsBaseChange B g) : Submodule.span B (Set.range g) = ⊤ := by
  refine eq_top_iff.2 fun n _ => ?_
  refine hg.inductionOn n (fun n => n ∈ Submodule.span B (Set.range g)) (Submodule.zero_mem _)
    (fun m => Submodule.subset_span ⟨m, rfl⟩) ?_ ?_
  · intro s n hn; exact Submodule.smul_mem _ _ hn
  · intro a b ha hb; exact Submodule.add_mem _ ha hb

def dualOf (hg : IsBaseChange B g) : Module.Dual A M →ₗ[A] Module.Dual B N where
  toFun w := hg.lift (Algebra.linearMap A B ∘ₗ w)
  map_add' w w' := dual_ext hg fun m => by simp [IsBaseChange.lift_eq]
  map_smul' a w := dual_ext hg fun m => by simp [IsBaseChange.lift_eq, Algebra.smul_def]

@[simp] theorem dualOf_apply (hg : IsBaseChange B g) (w : Module.Dual A M) (m : M) :
    dualOf hg w (g m) = algebraMap A B (w m) := by
  simp [dualOf, IsBaseChange.lift_eq]

theorem exists_dualBasis (A M : Type) [CommRing A] [AddCommGroup M] [Module A M] [Module.Finite A M]
    [Module.Projective A M] :
    ∃ (n : ℕ) (e : Fin n → M) (f : Fin n → Module.Dual A M), ∀ m, ∑ i, f i m • e i = m :=
  _root_.UpperTheory.Reformulated.B.DYhb1.main A M

theorem isBaseChange_dual [Module.Finite A M] [Module.Projective A M] (hg : IsBaseChange B g) :
    IsBaseChange B (dualOf hg) := by
  obtain ⟨n, e, f, hef⟩ := exists_dualBasis A M
  let Φ : B ⊗[A] Module.Dual A M →ₗ[B] Module.Dual B N := LinearMap.liftBaseChange B (dualOf hg)
  let Ψ : Module.Dual B N →ₗ[B] B ⊗[A] Module.Dual A M :=
    { toFun := fun y => ∑ i, y (g (e i)) • ((1 : B) ⊗ₜ[A] f i)
      map_add' := fun y y' => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun b y => by simp [Finset.smul_sum, mul_smul] }
  have hΨΦ : ∀ z, Ψ (Φ z) = z := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => rw [map_add, map_add, ha, hb]
    | tmul b w =>
      have hw : ∑ i, w (e i) • f i = w := by
        refine LinearMap.ext fun m => ?_
        have := congrArg w (hef m)
        simp only [map_sum, map_smul, smul_eq_mul] at this
        simp only [LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
        rw [← this]
        exact Finset.sum_congr rfl fun i _ => _root_.mul_comm _ _
      have h1 : ∀ i, (Φ (b ⊗ₜ w)) (g (e i)) • ((1 : B) ⊗ₜ[A] f i) = b ⊗ₜ[A] (w (e i) • f i) := by
        intro i
        simp only [Φ, LinearMap.liftBaseChange_tmul, LinearMap.smul_apply, dualOf_apply, smul_eq_mul]
        rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one, _root_.mul_comm,
          TensorProduct.smul_tmul', Algebra.smul_def]
      show ∑ i, (Φ (b ⊗ₜ w)) (g (e i)) • ((1 : B) ⊗ₜ[A] f i) = _
      rw [Finset.sum_congr rfl fun i _ => h1 i, ← TensorProduct.tmul_sum, hw]
  have hΦΨ : ∀ y, Φ (Ψ y) = y := by
    intro y
    refine dual_ext hg fun m => ?_
    show Φ (∑ i, y (g (e i)) • ((1 : B) ⊗ₜ[A] f i)) (g m) = _
    have h3 : y (g m) = ∑ i, algebraMap A B (f i m) * y (g (e i)) := by
      conv_lhs => rw [← hef m]
      simp [map_sum, Algebra.smul_def, ← IsScalarTower.algebraMap_smul B]
    rw [h3, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [Φ, _root_.mul_comm]
  exact IsBaseChange.of_equiv (LinearEquiv.ofBijective Φ
    ⟨Function.LeftInverse.injective hΨΦ, Function.RightInverse.surjective hΦΨ⟩)
    (fun w => by
      show Φ ((1 : B) ⊗ₜ w) = _
      simp [Φ])

end Alg

section Rank

variable {R : Type} [CommRing R] [IsDomain R] {P : Type} [AddCommGroup P] [Module R P]
  [Module.Finite R P] [Module.Projective R P]

theorem finrank_tensor_eq (F F' : Type) [Field F] [Field F'] [Algebra R F] [Algebra R F'] :
    Module.finrank F (F ⊗[R] P) = Module.finrank F' (F' ⊗[R] P) := by
  haveI : Module.FinitePresentation R P := Module.finitePresentation_of_projective R P
  have hc : ∀ a b : PrimeSpectrum R, Module.rankAtStalk (R := R) P a = Module.rankAtStalk (R := R) P b :=
    fun a b => Module.isLocallyConstant_rankAtStalk.apply_eq_of_preconnectedSpace a b
  have h1 := Module.rankAtStalk_baseChange (R := R) (M := P) (S := F) ⊥
  have h2 := Module.rankAtStalk_baseChange (R := R) (M := P) (S := F') ⊥
  rw [Module.rankAtStalk_eq_finrank_of_free] at h1 h2
  simp only [Pi.natCast_apply, Nat.cast_id] at h1 h2
  rw [h1, h2]; exact hc _ _

end Rank

section Lattice

variable {E : Type} [Field E] [NumberField E] {La : Type} [AddCommGroup La] [Module (𝓞 E) La]

theorem exists_sum_add_pow {c : E ≃+* E} {p N : ℕ} {EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ} {u : Fin N → La}
    (hu : IsPolLattice c p EF u) (n : ℕ) (b : La) :
    ∃ (z : Fin N → 𝓞 E) (x : La), b = ∑ k, z k • u k + (p ^ n) • x := by
  induction n with
  | zero => exact ⟨0, b, by simp⟩
  | succ n ih =>
    obtain ⟨z, x, rfl⟩ := ih
    obtain ⟨a, x', rfl⟩ := hu.span x
    refine ⟨z + (p ^ n) • a, x', ?_⟩
    simp only [Pi.add_apply, Pi.smul_apply, add_smul, Finset.sum_add_distrib, smul_add, Finset.smul_sum,
      smul_assoc, pow_succ, mul_smul, add_assoc]

theorem finite_lev (p : ℕ) [hp : Fact p.Prime] (hfin : Module.Finite ℤ La) (n : ℕ) : Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun t => ?_
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ t
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by exact_mod_cast (pow_pos hp.out.pos n).ne')⟩, ?_⟩
    rw [Submonoid.mk_smul, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    exact ⟨b, by rw [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

end Lattice

theorem pow_val_intCast {G : Type} [CommGroup G] {m : ℕ} [NeZero m] {g : G} (hg : g ^ m = 1) (a : ℤ) :
    g ^ ((a : ZMod m).val) = g ^ a := by
  have h1 : (((a : ZMod m).val : ℕ) : ℤ) = a % (m : ℤ) := ZMod.val_intCast a
  rw [← zpow_natCast, h1]
  conv_rhs => rw [← Int.emod_add_mul_ediv a (m : ℤ), zpow_add, zpow_mul, zpow_natCast, hg, one_zpow, _root_.mul_one]

theorem injective_of_isBaseChange {R K L Ω : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] [AddCommGroup L] [Module R L] [AddCommGroup Ω] [Module K Ω] [Module R Ω]
    [IsScalarTower R K Ω] {j : Module.Dual R L →ₗ[R] Ω} (hj : IsBaseChange K j) : Function.Injective j := by
  haveI := (isLocalizedModule_iff_isBaseChange (nonZeroDivisors R) K j).2 hj
  rw [injective_iff_map_eq_zero]
  intro w hw
  obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors R) j).1 hw
  refine LinearMap.ext fun e => ?_
  have h := LinearMap.congr_fun hc e
  have hc0 : (c : R) ≠ 0 := nonZeroDivisors.ne_zero c.2
  simpa [Submonoid.smul_def, hc0] using h

theorem finrank_chain {R O K C Ω P Q : Type} [CommRing R] [IsDomain R] [CommRing O] [Field K] [Field C]
    [Algebra R K] [Algebra R O] [Algebra O C] [Algebra R C] [IsScalarTower R O C]
    [AddCommGroup P] [Module R P] [Module.Finite R P] [Module.Projective R P]
    [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω]
    [AddCommGroup Q] [Module O Q] [Module R Q] [IsScalarTower R O Q]
    {j : P →ₗ[R] Ω} (hj : IsBaseChange K j) {D : P →ₗ[R] Q} (hD : IsBaseChange O D) :
    Module.finrank K Ω = Module.finrank C (C ⊗[O] Q) := by
  rw [← hj.equiv.finrank_eq, finrank_tensor_eq (R := R) (P := P) K C]
  exact ((AlgebraTensorModule.congr (LinearEquiv.refl C C) hD.equiv).symm.trans
    (AlgebraTensorModule.cancelBaseChange R O C C P)).symm.finrank_eq.symm ▸ rfl

section Group

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] {O : Type} [CommRing O] [IsDomain O]
  {y : Spec (CommRingCat.of O) ⟶ S}

theorem isDer_of_isHT {p : ℕ} {La : Type} [AddCommGroup La] (X : TorsTower p G y La) {L : Type} [AddCommGroup L]
    [Module O L] (M : LieModel G y L) (n : ℕ) (χ : LevGrp La p n →* Oˣ) (w : Module.Dual O L)
    (h : (X.Γ n).IsHT (X.i n) M (p ^ n) χ w) : X.IsDer M n (fun t => ((χ t : Oˣ) : O)) w := by
  obtain ⟨s, hs, he⟩ := h
  refine ⟨s, hs, fun e => ?_⟩
  obtain ⟨v, h1, h2, h3⟩ := he e
  refine ⟨v, h1, h2, ?_⟩
  rw [h3]
  simp

theorem act_comm {R : Type} [CommRing R] [Algebra R O] {x : Spec (CommRingCat.of R) ⟶ S} {L L' : Type}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module O L'] (M : LieModel G x L)
    (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) L') (β : L → L')
    (hβ : ∀ e, (M'.pt (β e)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap R O))) ≫ (M.pt e).left)
    {f : G ⟶ G} {A : L →ₗ[R] L} {A' : L' →ₗ[O] L'} (hA : M.IsDiffOf f A) (hA' : M'.IsDiffOf f A') (e : L) :
    A' (β e) = β (A e) := by
  apply M'.inj
  apply Over.OverMorphism.ext
  rw [hA' (β e), hβ (A e), hA e, Over.comp_left, hβ e, Over.comp_left, Category.assoc]

end Group

theorem reducesTo_of_isHTChartOf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [IsDomain O] [Algebra O C] (hv : v.Integers O) (hp : v (p : C) < 1) (hO : IsAdicComplete (Ideal.span {(p : O)}) O) (E : Type) [Field E] [NumberField E] (c : E ≃+* E) (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] [Algebra R O] (n N : ℕ) (Ω : Type) [AddCommGroup Ω] [Module K Ω] [Module R Ω] [IsScalarTower R K Ω] (D : HTChart R K c p n N Ω) (La : Type) [AddCommGroup La] [Module (𝓞 E) La] (EF : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (u : Fin N → La) (hu : IsPolLattice c p EF u) (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : Smooth G.hom) (x : Spec (CommRingCat.of R) ⟶ S) (Γ₀ : QFGroup R (LevGrp La p n)) (i : Γ₀.G.left ⟶ G.left) (hi : Γ₀.IsTorsionAlong G x (p ^ n) i) (L : Type) [AddCommGroup L] [Module R L] (M : LieModel G x L) (act : 𝓞 E → (G ⟶ G)) (ρ : 𝓞 E →+* Module.End R L) (hρ : M.IsActOf act ρ) (j : Module.Dual R L →ₗ[R] Ω) (hj : IsBaseChange K j) (π : Multiplicative (Fin N → 𝓞 E) →* LevGrp La p n) (ζ₀ : Rˣ) (X : TorsTower p G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) La) (F : (X.Γ n).G.left ⟶ Γ₀.G.left) (L' : Type) [AddCommGroup L'] [Module O L'] (M' : LieModel G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) L') (ρ' : 𝓞 E →+* Module.End O L') (hρ' : M'.IsActOf act ρ') (ζ : ℕ → Oˣ) (κ : O) (P : HTPoint C O c κ N (C ⊗[ℤ] La) (C ⊗[O] Module.Dual O L')), IsHTChartOf D Γ₀ i M ρ j π ζ₀ → (∀ z, π (Multiplicative.ofAdd z) = lev p n (∑ k, z k • u k)) → (∀ z z', D.e z z' = ((EF (∑ k, z k • u k) (∑ k, z' k • u k) : ℤ) : ZMod (p ^ n))) → (X.Γ n).IsBaseChange Γ₀ (algebraMap R O) F → F ≫ i = X.i n → algebraMap R O (ζ₀ : R) = (ζ n : O) → ζ n ^ p ^ n = 1 → IsPointOf p (X.IsDer M') EF ζ ρ' u P → ∃ io : D.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L'), D.ReducesTo (algebraMap R O) P io := by
  intro p _ C _ _ _ v O _ _ _ hv hp hO E _ _ c R K _ _ _ _ _ _ _ n N Ω _ _ _ _ D La _ _ EF u hu S G _ _ hG x Γ₀ i hi
    L _ _ M act ρ hρ j hj π ζ₀ X F L' _ _ M' ρ' hρ' ζ κ P hD hπ he hbc hF hζ hζn hP
  haveI := hG
  haveI : NeZero (p ^ n) := ⟨(pow_pos (Fact.out : p.Prime).pos n).ne'⟩
  haveI : Finite (LevGrp La p n) := finite_lev p hu.finite n
  letI : Module R L' := Module.compHom L' (algebraMap R O)
  haveI : IsScalarTower R O L' := ⟨fun r o l => by
    show (r • o) • l = algebraMap R O r • (o • l)
    rw [Algebra.smul_def, mul_smul]⟩
  obtain ⟨β₀, hβ₀, hβs, -⟩ := PositivityTheory.HtPt.Htat.lie_bc S G R O x L L' M M'
  let β : L →ₗ[R] L' := { toFun := β₀, map_add' := β₀.map_add, map_smul' := fun a e => hβs a e }
  have hβ : IsBaseChange O β := PositivityTheory.HtPt.Htat.lie_bc_iso S G R O x L L' M M' β (fun e => by
    unfold LieModel.Lifts
    rw [Category.comp_id]
    exact hβ₀ e)
  obtain ⟨hLf, hLp⟩ := PositivityTheory.HtPt.Htat.lie_fin S G R x L M
  have hDb := isBaseChange_dual hβ
  have hinj := injective_of_isBaseChange hj
  have hom : D.om = LinearMap.range j := hD.1
  let eq : Module.Dual R L ≃ₗ[R] D.om := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hom.symm)
  have heq : ∀ w, ((eq w : D.om) : Ω) = j w := fun _ => rfl
  let io : D.om →ₛₗ[algebraMap R O] (C ⊗[O] Module.Dual O L') :=
    { toFun := fun y => (1 : C) ⊗ₜ[O] dualOf hβ (eq.symm y)
      map_add' := fun a b => by simp [TensorProduct.tmul_add]
      map_smul' := fun r a => by
        rw [map_smul, map_smul, ← algebraMap_smul O r (dualOf hβ (eq.symm a)), TensorProduct.tmul_smul] }
  have hio : ∀ (y : D.om) (w : Module.Dual R L), (y : Ω) = j w → io y = (1 : C) ⊗ₜ[O] dualOf hβ w := by
    intro y w h
    have : y = eq w := Subtype.ext (h.trans (heq w).symm)
    subst this
    show (1 : C) ⊗ₜ[O] dualOf hβ (eq.symm (eq w)) = _
    rw [LinearEquiv.symm_apply_apply]
  have hioe : ∀ w, io (eq w) = (1 : C) ⊗ₜ[O] dualOf hβ w := fun w => hio _ w (heq w)
  obtain ⟨htP, hρP, heP, homP, hρΩP, hhtP⟩ := hP
  have htate : ∀ z : Fin N → 𝓞 E, P.tate z = (1 : C) ⊗ₜ[ℤ] ∑ k, z k • u k := by
    intro z
    simp only [HTPoint.tate, htP, hρP, TensorProduct.tmul_sum]
  refine ⟨io, ?_, ?_, ?_, ?_, ?_⟩
  · rw [homP]
    have hs := span_range_eq_top hDb
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨y, rfl⟩
      exact ⟨_, rfl⟩
    · rw [LinearMap.range_eq_map, ← hs, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨eq w, hioe w⟩
  · letI : Algebra R C := ((algebraMap O C).comp (algebraMap R O)).toAlgebra
    haveI : IsScalarTower R O C := IsScalarTower.of_algebraMap_eq fun _ => rfl
    exact finrank_chain hj hDb
  · intro a y
    obtain ⟨w, rfl⟩ := eq.surjective y
    rw [hioe w, hρΩP]
    refine (hio _ (w ∘ₗ ρ (RingOfIntegers.mapRingEquiv c a)) ?_).trans ?_
    · show D.ρΩ a ((eq w : D.om) : Ω) = _
      rw [heq w]
      exact hD.2.1 a w
    · congr 1
      refine dual_ext hβ fun m => ?_
      have hc := act_comm M M' β₀ hβ₀ (hρ (RingOfIntegers.mapRingEquiv c a))
        (hρ' (RingOfIntegers.mapRingEquiv c a)) m
      rw [dualOf_apply]
      show _ = dualOf hβ w (ρ' (RingOfIntegers.mapRingEquiv c a) (β m))
      rw [show ρ' (RingOfIntegers.mapRingEquiv c a) (β m) = β (ρ (RingOfIntegers.mapRingEquiv c a) m) from hc,
        dualOf_apply]
      rfl
  · intro z
    obtain ⟨χ, w, hχ, hh, hHT⟩ := hD.2.2 z
    have htors : (X.Γ n).IsTorsionAlong G (Spec.map (CommRingCat.ofHom (algebraMap R O)) ≫ x) (p ^ n) (F ≫ i) := by
      rw [hF]; exact X.tors n
    have hHT' := PositivityTheory.HtPt.Htat.ht_bc R (LevGrp La p n) Γ₀ S G x (p ^ n) i hi L M O (X.Γ n) F hbc htors L' M' β₀ hβ₀
      (span_range_eq_top hβ) χ w (dualOf hβ w) (fun e => dualOf_apply hβ w e) hHT
    rw [hF] at hHT'
    have hder := isDer_of_isHT X M' n _ _ hHT'
    have hz : Units.map (algebraMap R O : R →* O) ζ₀ = ζ n := Units.ext hζ
    have hf : ∀ b, ((((Units.map (algebraMap R O : R →* O)).comp χ) (lev p n b) : Oˣ) : O) =
        ((ζ n ^ EF (∑ k, z k • u k) b : Oˣ) : O) := by
      intro b
      obtain ⟨z', x', rfl⟩ := exists_sum_add_pow hu n b
      have hl : lev p n (∑ k, z' k • u k + (p ^ n) • x') = π (Multiplicative.ofAdd z') := by
        rw [hπ]
        refine congrArg Multiplicative.ofAdd ((Submodule.Quotient.eq _).2 ⟨x', ?_⟩)
        rw [LinearMap.smul_apply, LinearMap.id_apply, add_sub_cancel_left]
      rw [hl]
      congr 1
      show Units.map (algebraMap R O : R →* O) (χ (π (Multiplicative.ofAdd z'))) = _
      rw [hχ, map_pow, hz, he, pow_val_intCast hζn, map_add, map_nsmul, zpow_add, nsmul_eq_mul,
        zpow_mul, zpow_natCast, hζn, one_zpow, _root_.mul_one]
    obtain ⟨y, hy, hyeq⟩ := hhtP n (∑ k, z k • u k) _ _ hf hder
    refine ⟨-y, P.om.neg_mem hy, ?_⟩
    rw [hio _ w hh, htate, hyeq]
    simp
  · intro a b
    rw [htate, htate, heP, he]
    generalize EF (∑ k, a k • u k) (∑ k, b k • u k) = t
    have h1 : (((t : ZMod (p ^ n)).val : ℕ) : ℤ) = t % ((p ^ n : ℕ) : ℤ) := ZMod.val_intCast t
    obtain ⟨q, hq⟩ : ∃ q : ℤ, t = (((t : ZMod (p ^ n)).val : ℕ) : ℤ) + ((p ^ n : ℕ) : ℤ) * q :=
      ⟨t / ((p ^ n : ℕ) : ℤ), by rw [h1]; exact (Int.emod_add_mul_ediv _ _).symm⟩
    refine ⟨(q : O), ?_⟩
    have h2 : (t : C) = (((t : ZMod (p ^ n)).val : ℕ) : C) + (p : C) ^ n * (q : C) := by
      have := congrArg (Int.cast : ℤ → C) hq
      push_cast at this
      exact this
    rw [h2, map_add, map_mul, map_pow, map_natCast, map_natCast, map_intCast]

end PositivityTheory.HtPt.Htat.ChartRed
