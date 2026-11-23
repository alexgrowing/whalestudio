import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsNumOf
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIntegralGauge
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IntegralGaugeValuesAreValuationUnits
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.BasisValueAtOrigin
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgClosurePointFactorsThroughFiniteLocalSubalgebStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section
namespace GlobalTheory.FinGauge
open GlobalTheory.Ex

theorem spMap_val_comp {R : Type} [CommRing R] [IsDomain R] (S : Subalgebra R (Kb R)) :
    spMap (S.val : S →+* Kb R) ≫ spMap (algebraMap R S) = (TF (R := R) (Kb R)).hom := by
  simp only [spMap, TF, Over.mk_hom, jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2

theorem vF_sF_mem {F : Type} [Field F] {A : Type} [CommRing A] (f : A →+* F) {X Y : Scheme.{0}} {L : LB X}
    {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (J : (Sp F ⟶ X) → L.ι) (r₀ : Sp A ⟶ Y)
    (hJ : ∀ k, ⊤ ≤ (r₀ ≫ φ k) ⁻¹ᵁ L.U (J ((spMap f ≫ r₀) ≫ φ k))) :
    (∀ t : LB.Gen (LB.LinComb L φ ε), ∃ u : Aˣ, f u = vF t (spMap f ≫ r₀) J) ∧
      ∀ s : LB.Sec (LB.LinComb L φ ε), ∃ a : A, f a = sF s (spMap f ≫ r₀) J := by
  have key : ∀ (W : Y.Opens) (hr : ⊤ ≤ r₀ ⁻¹ᵁ W) (a : Γ(Y, W)),
      valF (spMap f ≫ r₀) W a = f ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom ((r₀.appLE W ⊤ hr).hom a)) := by
    intro W hr a
    have h' : ⊤ ≤ (spMap f ≫ r₀) ⁻¹ᵁ W := fun q _ => hr (Set.mem_univ (spMap f q))
    rw [valF, dif_pos h']
    have e : (spMap f ≫ r₀).appLE W ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of F)).hom =
        r₀.appLE W ⊤ hr ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).hom ≫ CommRingCat.ofHom f := by
      rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap f) r₀ W ⊤ ⊤ hr le_rfl,
        Category.assoc]
      rfl
    exact congrArg (fun g => g.hom a) e
  let j : K → L.ι := fun k => J ((spMap f ≫ r₀) ≫ φ k)
  have hr : ⊤ ≤ r₀ ⁻¹ᵁ LB.wchart L φ j := fun z _ => Set.mem_iInter.2 fun k => hJ k trivial
  let g : Γ(Y, LB.wchart L φ j) →* A :=
    ((Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (r₀.appLE _ ⊤ hr).hom).toMonoidHom
  refine ⟨fun t => ⟨Units.map g (t.s j), ?_⟩, fun s => ⟨_, (key _ hr (s.f j)).symm⟩⟩
  exact (key _ hr _).symm

theorem ext_unique {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] {A : Type} [CommRing A]
    [IsDomain A] (f : A →+* F) (hf : Function.Injective f) (x y : Sp A ⟶ D.P.A.left)
    (h : spMap f ≫ x = spMap f ≫ y) : x = y := by
  haveI := D.P.isAb.proper
  haveI : IsDominant (spMap f) := by
    constructor
    show DenseRange (PrimeSpectrum.comap f)
    rw [PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical]
    intro a ha
    rw [RingHom.mem_ker, ← map_zero f] at ha
    rw [hf ha]
    exact zero_mem _
  refine ext_of_isDominant_of_isSeparated D.P.A.hom ?_ (spMap f) h
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (x ≫ D.P.A.hom)
  obtain ⟨φ', hφ'⟩ := Spec.map_surjective (y ≫ D.P.A.hom)
  rw [← hφ, ← hφ']
  congr 1
  have e : spMap f ≫ Spec.map φ = spMap f ≫ Spec.map φ' := by
    rw [hφ, hφ', ← Category.assoc, ← Category.assoc, h]
  simp only [spMap, ← Spec.map_comp] at e
  have e' := Spec.map_injective e
  ext r
  exact hf (congrArg (fun g => g.hom r) e')

theorem exists_gauge_local {F : Type} [Field F] {A : Type} [CommRing A] [IsLocalRing A] (f : A →+* F) {X : Scheme.{0}}
    {L : LB X} (hL : L.IsLB) (hu : ∀ x y : Sp A ⟶ X, spMap f ≫ x = spMap f ≫ y → x = y) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ x₀ : Sp A ⟶ X, ⊤ ≤ x₀ ⁻¹ᵁ L.U (J (spMap f ≫ x₀)) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ∀ x₀ : Sp A ⟶ X, spMap f ≫ x₀ = ψ → ⊤ ≤ x₀ ⁻¹ᵁ L.U j := by
    intro ψ
    by_cases h : ∃ x₀ : Sp A ⟶ X, spMap f ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := GlobalTheory.IntegralGauge.exists_chart_local hL x₀
      exact ⟨j, fun w _ => hj (Set.mem_univ (spMap f w)), fun x₁ e => hu x₀ x₁ e.symm ▸ hj⟩
    · obtain ⟨j, hj⟩ := GlobalTheory.IntegralGauge.exists_chart_local hL ψ
      exact ⟨j, hj, fun x₀ e => (h ⟨x₀, e⟩).elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, fun x₀ => h₂ _ x₀ rfl⟩

theorem top_of_finite_local {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] (S : Subalgebra R (Kb R))
    [Module.Finite R S] [IsLocalRing S] (U : (Sp R).Opens) (h : ⊤ ≤ spMap (algebraMap R S) ⁻¹ᵁ U) : ⊤ ≤ U := by
  haveI : FaithfulSMul R S := by
    rw [faithfulSMul_iff_algebraMap_injective]
    intro a b e
    have e' := congrArg (fun s : S => (s : Kb R)) e
    simp only [Subalgebra.coe_algebraMap] at e'
    rw [IsScalarTower.algebraMap_apply R (FractionRing R) (Kb R), IsScalarTower.algebraMap_apply R (FractionRing R) (Kb R) b] at e'
    exact IsFractionRing.injective R (FractionRing R) ((algebraMap (FractionRing R) (Kb R)).injective e')
  haveI := Algebra.IsIntegral.isLocalHom R S
  have hc : (spMap (algebraMap R S)).base (IsLocalRing.closedPoint S) = IsLocalRing.closedPoint R := by
    show PrimeSpectrum.comap (algebraMap R S) _ = _
    exact IsLocalRing.comap_closedPoint _
  have hm : IsLocalRing.closedPoint R ∈ U := hc ▸ h (Set.mem_univ (IsLocalRing.closedPoint S))
  exact fun w _ => (IsLocalRing.specializes_closedPoint (R := R) w).mem_open U.isOpen hm

theorem psi_val_mem {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {F : Type} [Field F] [Algebra (FractionRing R) F]
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (χ : D.X) (I : Ideal R) (hI : D.PsiIn χ I)
    (hc : ⊤ ≤ (D.c χ).left ⁻¹ᵁ D.P.L.U (J (jFK (R := R) F ≫ D.xK χ))) :
    ∃ a ∈ I, vF (D.psi χ) (jFK (R := R) F) J = algebraMap (FractionRing R) F (algebraMap R _ a) := by
  have hV : IsAffineOpen (⊤ : (Sp R).Opens) := isAffineOpen_top _
  have h : jK R ⁻¹ᵁ ⊤ ≤ (LB.LinComb D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => -1)).U
      (fun _ => J (jFK (R := R) F ≫ D.xK χ)) := fun y _ => Set.mem_iInter.2 fun _ => hc trivial
  obtain ⟨r, hr, er⟩ := hI (fun _ => J (jFK (R := R) F ≫ D.xK χ)) ⊤ hV hc h
  have h4 : ⊤ ≤ jFK (R := R) F ⁻¹ᵁ (jK R ⁻¹ᵁ ⊤) := fun _ _ => trivial
  have a := GlobalTheory.Ex.UnitVal.valF_res' h h4 ((D.psi χ).s _).val
  rw [Scheme.Hom.app_eq_appLE] at er
  have e1 : vF (D.psi χ) (jFK (R := R) F) J = valF (jFK (R := R) F ≫ jK R) ⊤ r :=
    a.symm.trans ((congrArg (valF _ _) er.symm).trans (GlobalTheory.Ex.UnitVal.valF_appLE' (jK R) ⊤ le_rfl h4 r))
  have hsurj : Function.Surjective (DegPre.toOpen (R := R) (⊤ : (Sp R).Opens)) := by
    intro b
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b, ?_⟩
    simp [DegPre.toOpen]
  obtain ⟨a', ha', rfl⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).1 hr
  refine ⟨a', ha', e1.trans ?_⟩
  have e2 : jFK (R := R) F ≫ jK R = spMap ((algebraMap (FractionRing R) F).comp (algebraMap R _)) := by
    simp only [spMap, jFK, jK, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  rw [DegPre.toOpen, RingHom.comp_apply, GlobalTheory.Ex.UnitVal.valF_res' (le_top : (⊤ : (Sp R).Opens) ≤ ⊤) (fun _ _ => trivial), e2]
  exact GlobalTheory.OriginFrame.valF_spMap_fn _ a'

theorem exists_finite_pt (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (Z : Scheme.{0})
    (π : Z ⟶ Sp R) [IsFinite π] (k : Sp (Kb R) ⟶ Z) (hk : k ≫ π = (TF (R := R) (Kb R)).hom) :
    ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧
      ∃ k₀ : Sp S ⟶ Z, k₀ ≫ π = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ k₀ = k :=
  GlobalTheory.T.algClosurePoint_factors_through_finite_local_subalgebra R hR Z π k hk

theorem exists_finite_ext (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (hR : Base R) (D : DegPre R)
    (x : TF (R := R) (Kb R) ⟶ D.P.A) (m : ℕ) (hm : IsUnit (m : R)) (z : 𝟙_ (Over (Sp R)) ⟶ D.P.A)
    (hx : x ^ m = toUnit _ ≫ z) : ∃ S : Subalgebra R (Kb R), Module.Finite R S ∧ IsLocalRing S ∧
      ∃ x₀ : Sp S ⟶ D.P.A.left, x₀ ≫ D.P.A.hom = spMap (algebraMap R S) ∧ spMap (S.val : S →+* Kb R) ≫ x₀ = x.left := by
  haveI : IsNoetherianRing R := hR.1.1
  have hm1 : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · subst h
      simp at hm
    · exact h
  haveI : IsFinite (mulA D.P.A m).left := (GlobalTheory.firstFiveLaws.1.mulN (Sp R) D.P m hm1).1
  have hxm : x.left ≫ (mulA D.P.A m).left = (TF (R := R) (Kb R)).hom ≫ z.left := by
    have h1 : (toUnit (TF (R := R) (Kb R))).left = (TF (R := R) (Kb R)).hom := by
      simpa using Over.w (toUnit (TF (R := R) (Kb R)))
    rw [← Over.comp_left, GlobalTheory.IntDiv.comp_mulA, hx, Over.comp_left, h1]
  obtain ⟨S, hSf, hSl, k₀, hk₀, hk⟩ := exists_finite_pt R hR (pullback (mulA D.P.A m).left z.left)
    (pullback.snd _ _) (pullback.lift _ _ hxm) (pullback.lift_snd _ _ _)
  refine ⟨S, hSf, hSl, k₀ ≫ pullback.fst _ _, ?_, ?_⟩
  · have h2 : pullback.fst (mulA D.P.A m).left z.left ≫ D.P.A.hom = pullback.snd _ _ := by
      rw [← Over.w (mulA D.P.A m), ← Category.assoc, pullback.condition, Category.assoc, Over.w z]
      simp
    rw [Category.assoc, h2, hk₀]
  · rw [← Category.assoc, hk, pullback.lift_fst]

theorem gauge : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (N : GlobalTheory.Ex.NumD (Kb R)) (ν : GlobalTheory.Ex.NumOf D.toPre (Kb R) N) (m : ℕ), Odd m → IsUnit (m : R) → ∀ (p : QkPt D.toPre (Kb R) (m ^ 2)), ∃ (N' : GlobalTheory.Ex.NumD (Kb R)) (ν' : GlobalTheory.Ex.NumOf D.toPre (Kb R) N') (q' : N'.QT (m ^ 2)) (S : Subalgebra R (Kb R)), ν'.th = ν.th ∧ ν'.QPt p q' ∧ Module.Finite R S ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), ∀ x'' ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.θ x x' x'' : Kb R) ∈ S ∧ (((N'.θ x x' x'')⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ x ∈ Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}), (N'.σ x : Kb R) ∈ S ∧ (((N'.σ x)⁻¹ : (Kb R)ˣ) : Kb R) ∈ S) ∧ (∀ χ, N'.th (N'.c χ * (q'.1.2 ^ m).b) ∈ S) ∧ (∀ χ, (N'.ψ χ : Kb R) ∈ S) ∧ ∀ n : ℕ, {χ | ¬ ∃ s ∈ (maximalIdeal R ^ n • ⊤ : Submodule R S), (s : Kb R) = N'.ψ χ}.Finite := by
  intro R _ _ _ hR D N ν m hm hmu p
  obtain ⟨q, hq⟩ := GlobalTheory.SeriesCompare.exists_val D.psi_even D.tau_bimult ν p
  have hxm : (p.g.b ^ m) ^ m = toUnit _ ≫ D.toPre.c (ν.eX q.1.1.toAdd) := by
    rw [← pow_mul, ← sq, ← hq.2.1, ← map_pow, N.QT_pow_b q, ν.c_eq]
  obtain ⟨S, hSf, hSl, x₀, hx₀A, hx₀⟩ := exists_finite_ext R hR D.toPre _ m hmu _ hxm
  let f : S →+* Kb R := S.val
  have hfi : Function.Injective f := Subtype.val_injective
  let TS : Over (Sp R) := Over.mk (spMap (algebraMap R S))
  let ιS : TF (R := R) (Kb R) ⟶ TS := Over.homMk (spMap f) (spMap_val_comp S)
  obtain ⟨J', hJg, hJi⟩ := exists_gauge_local f D.toPre.P.isLB (ext_unique D.toPre f hfi)
  obtain ⟨N', ν', hJ, hth⟩ := GlobalTheory.GaugeValues.exists_numOf GlobalTheory.firstFiveLaws.1 R D.toPre D.psi_even D.tau_bimult
    (Kb R) J' hJg ν.th ν.th_gen
  subst hJ
  obtain ⟨q', hq'⟩ := GlobalTheory.SeriesCompare.exists_val D.psi_even D.tau_bimult ν' p
  set G := Subgroup.closure (Set.range N'.c ∪ {(q'.1.2 ^ m).b}) with hG
  have hExt : ∀ a ∈ G, ∃ a₀ : TS ⟶ D.toPre.P.A, ιS ≫ a₀ = ν'.eA a := by
    intro a ha
    induction ha using Subgroup.closure_induction with
    | mem a h =>
      rcases h with ⟨χ, rfl⟩ | h
      · exact ⟨toUnit _ ≫ D.toPre.c (ν'.eX χ), by rw [ν'.c_eq, ← Category.assoc]; congr 1; exact toUnit_unique _ _⟩
      · rw [Set.mem_singleton_iff] at h
        subst h
        refine ⟨Over.homMk x₀ hx₀A, Over.OverMorphism.ext ?_⟩
        rw [NumD.Gt.pow_b, map_pow, hq'.2.1]
        exact hx₀
    | one => exact ⟨1, by rw [map_one, comp_one]⟩
    | mul a b _ _ ha hb =>
      obtain ⟨a₀, ha₀⟩ := ha
      obtain ⟨b₀, hb₀⟩ := hb
      exact ⟨a₀ * b₀, by rw [comp_mul, ha₀, hb₀, map_mul]⟩
    | inv a _ ha =>
      obtain ⟨a₀, ha₀⟩ := ha
      exact ⟨a₀⁻¹, by rw [GrpObj.comp_inv, ha₀, map_inv]⟩

  have hval : ∀ (Y : Scheme.{0}) (K : Type) [Fintype K] (φ : K → (Y ⟶ D.toPre.P.A.left)) (ε : K → ℤ) (r₀ : Sp S ⟶ Y),
      (∀ t : LB.Gen (LB.LinComb D.toPre.P.L φ ε), ∃ u : Sˣ, f u = vF t (spMap f ≫ r₀) ν'.J) ∧
        ∀ s : LB.Sec (LB.LinComb D.toPre.P.L φ ε), ∃ a : S, f a = sF s (spMap f ≫ r₀) ν'.J :=
    fun Y K _ φ ε r₀ => vF_sF_mem f ν'.J r₀ fun k => by rw [Category.assoc]; exact hJi _
  have hleft : ∀ (a : N'.A) (a₀ : TS ⟶ D.toPre.P.A), ιS ≫ a₀ = ν'.eA a → (ν'.eA a).left = spMap f ≫ a₀.left := by
    intro a a₀ h
    rw [← h]
    rfl
  have hunit : ∀ (w : (Kb R)ˣ) (u : Sˣ), (w : Kb R) = f u → (w : Kb R) ∈ S ∧ ((w⁻¹ : (Kb R)ˣ) : Kb R) ∈ S := by
    intro w u h
    refine ⟨h ▸ (u : S).2, ?_⟩
    rw [Units.val_inv_eq_inv_val, h, ← map_units_inv]
    exact ((u⁻¹ : Sˣ) : S).2
  have hrig : ∃ u : Sˣ, f u = vF (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A) (ε := fun _ => 1)
      D.toPre.rig (TF (R := R) (Kb R)).hom ν'.J := by
    have := (hval _ PUnit (fun _ => eSec D.toPre.P.A) (fun _ => 1)
      (spMap (algebraMap R S) : Sp S ⟶ (𝟙_ (Over (Sp R))).left)).1 D.toPre.rig
    rwa [spMap_val_comp S] at this
  obtain ⟨u, hu⟩ := hrig
  have hxK : ∀ χ', jFK (R := R) (Kb R) ≫ D.toPre.xK χ' =
      spMap f ≫ (spMap (algebraMap R S) ≫ (D.toPre.c χ').left) := by
    intro χ'
    have h1 : (toUnit (TK R)).left = jK R := by simpa using Over.w (toUnit (TK R))
    simp only [DegPre.xK, ptK, Over.comp_left, h1]
    rw [← Category.assoc, ← Category.assoc, spMap_val_comp S]
    rfl
  have hc : ∀ χ', ⊤ ≤ (D.toPre.c χ').left ⁻¹ᵁ D.toPre.P.L.U (ν'.J (jFK (R := R) (Kb R) ≫ D.toPre.xK χ')) := by
    intro χ'
    have := hJi (spMap (algebraMap R S) ≫ (D.toPre.c χ').left)
    rw [← hxK] at this
    exact top_of_finite_local S _ fun z hz => this hz
  have hψ : ∀ χ (I : Ideal R), D.toPre.PsiIn (ν'.eX χ) I → ∃ a ∈ I, (N'.ψ χ : Kb R) = f (algebraMap R S a * u) := by
    intro χ I hI
    obtain ⟨a, ha, hv⟩ := psi_val_mem D.toPre ν'.J _ I hI (hc _)
    refine ⟨a, ha, ?_⟩
    rw [ν'.ψ_eq, hv, ← hu, map_mul]
    congr 1
  refine ⟨N', ν', q', S, hth, hq', hSf, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx x' hx' x'' hx''
    obtain ⟨a, ha⟩ := hExt x hx
    obtain ⟨b, hb⟩ := hExt x' hx'
    obtain ⟨c, hc⟩ := hExt x'' hx''
    have e : (lift (ν'.eA x) (lift (ν'.eA x') (ν'.eA x''))).left = spMap f ≫ (lift a (lift b c)).left := by
      rw [← ha, ← hb, ← hc, ← comp_lift, ← comp_lift]
      rfl
    obtain ⟨w, hw⟩ := (hval _ _ _ _ (lift a (lift b c)).left).1 D.toPre.cub.t
    refine hunit _ w ?_
    rw [ν'.θ_eq, e]
    exact hw.symm
  · intro x hx
    obtain ⟨a, ha⟩ := hExt x hx
    obtain ⟨w, hw⟩ := (hval _ _ _ _ a.left).1 D.toPre.sym
    refine hunit _ w ?_
    rw [ν'.σ_eq, hleft x a ha, hw]
  · intro χ
    have hm : N'.c χ * (q'.1.2 ^ m).b ∈ G :=
      G.mul_mem (Subgroup.subset_closure (Or.inl ⟨χ, rfl⟩)) (Subgroup.subset_closure (Or.inr rfl))
    obtain ⟨a, ha⟩ := hExt _ hm
    obtain ⟨s, hs⟩ := (hval _ _ _ _ a.left).2 ν'.th
    have e2 := ν'.th_eq (N'.c χ * (q'.1.2 ^ m).b)
    rw [hleft _ a ha, ← hs, ← hu] at e2
    have e3 : N'.th (N'.c χ * (q'.1.2 ^ m).b) = f (s * ((u⁻¹ : Sˣ) : S)) := by
      rw [map_mul, ← e2, map_units_inv, _root_.mul_assoc, mul_inv_cancel₀ ((u.isUnit.map f).ne_zero), _root_.mul_one]
    rw [e3]
    exact (s * ((u⁻¹ : Sˣ) : S)).2
  · intro χ
    by_cases h0 : ν'.eX χ = 0
    · rw [(AddEquiv.map_eq_zero_iff ν'.eX).1 h0, N'.ψ_zero]
      exact S.one_mem
    · obtain ⟨a, -, he⟩ := hψ χ _ (D.psi_pos _ h0)
      rw [he]
      exact (algebraMap R S a * (u : S)).2
  · intro n
    refine ((D.psi_tendsto n).preimage ν'.eX.injective.injOn).subset ?_
    intro χ hχ
    simp only [Set.mem_setOf_eq, Set.mem_preimage] at hχ ⊢
    intro hI
    apply hχ
    obtain ⟨a, ha, he⟩ := hψ χ _ hI
    refine ⟨algebraMap R S a * u, ?_, he.symm⟩
    rw [← Algebra.smul_def]
    exact Submodule.smul_mem_smul ha trivial
end GlobalTheory.FinGauge
