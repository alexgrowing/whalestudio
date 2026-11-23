import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StAvDefs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.FiniteAlgebraLocalCompletion
import Development.AbelianVarietyTheory.BlockTheory.JetGauges.ConjugatePlaceEigen
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CotangentBidualToTangentFunctionInjective
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.FiniteResidueFieldAdicCompletionIntegers
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.NonemptyPadicIntRingHomOfIsAdicComplete
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsTorusAndQuotientHom
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct

namespace GlobalTheory.EigenLieCompare

open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.ConjugatePlaceEigen GlobalTheory.HodgeTateCompare

section General

variable {O : Type} [CommRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G]
  {R : Type} [CommRing R] (α : RingAct G R)

theorem isEig_iff (τ : R →+* O) (x : LieG G) :
    IsEig G α τ x ↔ ∀ a : R, x.1 ≫ α.act a = ptMap (dualScale (τ a)) ≫ x.1 :=
  forall_congr' fun _ => Subtype.ext_iff

def eigEquiv (τ : R →+* O) : LieTau G α τ ≃ LieEig α τ :=
  Equiv.subtypeEquivRight (isEig_iff α τ)

def funEquiv (τ : R →+* O) : (LieTau G α τ → O) ≃ₗ[O] (LieEig α τ → O) :=
  LinearEquiv.funCongrLeft O O (eigEquiv α τ).symm

theorem map_map_restr (τ : R →+* O) (S : Submodule O (LieG G → O)) :
    (S.map (restr G α τ)).map (funEquiv α τ).toLinearMap = S.map (restrictEig α τ) := by
  rw [← Submodule.map_comp]
  rfl

theorem restrictEig_mem (τ : R →+* O) {f : LieG G → O} (hf : f ∈ omega G) :
    restrictEig α τ f ∈ omegaEig α τ := by
  refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
  · have := hf.1 x.1 y.1 (h ▸ z.1.2)
    show f z.1 = f x.1 + f y.1
    rw [← this]; congr 1; exact Subtype.ext h
  · have := hf.2 c x.1 (h ▸ z.1.2)
    show f z.1 = c * f x.1
    rw [← this]; congr 1; exact Subtype.ext h

theorem map_omTau_le (τ : R →+* O) :
    (omTau G α τ).map (funEquiv α τ).toLinearMap ≤ omegaEig α τ := by
  rw [omTau, map_map_restr]
  rintro _ ⟨f, hf, rfl⟩
  exact restrictEig_mem α τ hf

end General

section Local

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)

variable {O : Type} [CommRing O] [IsLocalRing O] {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)

theorem lie_ext {x y : Lie G} (h : (lieEquiv G x).1 = (lieEquiv G y).1) : x = y :=
  (lieEquiv G).injective (Subtype.ext h)

def eigSub (τ : R →+* O) : Submodule O (Lie G) where
  carrier := {x | ∀ a : R, (lieEquiv G x).1 ≫ α.act a = (lieEquiv G (τ a • x)).1}
  add_mem' := fun {x y} hx hy a => by
    haveI := α.hom a
    rw [smul_add, lieEquiv_add, lieEquiv_add, ← hx a, ← hy a, MonObj.mul_comp]
  zero_mem' := fun a => by
    haveI := α.hom a
    have h : (lieEquiv G 0).1 = 1 := by
      have := lieEquiv_add (G := G) 0 0
      rw [add_zero] at this
      exact left_eq_mul.1 this
    rw [smul_zero, h, MonObj.one_comp]
  smul_mem' := fun c x hx a => by
    rw [smul_comm, lieEquiv_smul, lieEquiv_smul c, ← hx a, Category.assoc]

def subEquiv (τ : R →+* O) : eigSub α τ ≃ LieEig α τ :=
  (lieEquiv G).subtypeEquiv fun x => forall_congr' fun a => by rw [lieEquiv_smul]

theorem subEquiv_val (τ : R →+* O) (x : eigSub α τ) :
    (subEquiv α τ x).1 = lieEquiv G x.1 := rfl

def ofDual (τ : R →+* O) : Module.Dual O (eigSub α τ) →ₗ[O] (LieEig α τ → O) where
  toFun F x := F ((subEquiv α τ).symm x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem ofDual_apply (τ : R →+* O) (F : Module.Dual O (eigSub α τ)) (x : eigSub α τ) :
    ofDual α τ F (subEquiv α τ x) = F x :=
  congrArg F ((subEquiv α τ).symm_apply_apply x)

theorem ofDual_injective (τ : R →+* O) : Function.Injective (ofDual α τ) := fun F F' h =>
  LinearMap.ext fun x => by rw [← ofDual_apply, h, ofDual_apply]

theorem range_ofDual (τ : R →+* O) : LinearMap.range (ofDual α τ) = omegaEig α τ := by
  ext g
  constructor
  · rintro ⟨F, rfl⟩
    refine ⟨fun x y z h => ?_, fun c x z h => ?_⟩
    · obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
      obtain ⟨y, rfl⟩ := (subEquiv α τ).surjective y
      obtain ⟨z, rfl⟩ := (subEquiv α τ).surjective z
      have : z = x + y := Subtype.ext (lie_ext (h.trans (lieEquiv_add x.1 y.1).symm))
      rw [ofDual_apply, ofDual_apply, ofDual_apply, this, map_add]
    · obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
      obtain ⟨z, rfl⟩ := (subEquiv α τ).surjective z
      have : z = c • x := Subtype.ext (lie_ext (h.trans (lieEquiv_smul c x.1).symm))
      rw [ofDual_apply, ofDual_apply, this, map_smul, smul_eq_mul]
  · rintro ⟨h₁, h₂⟩
    refine ⟨⟨⟨fun x => g (subEquiv α τ x), fun x y => h₁ _ _ _ (lieEquiv_add x.1 y.1)⟩,
      fun c x => h₂ _ _ _ (lieEquiv_smul c x.1)⟩, funext fun x => ?_⟩
    exact congrArg g ((subEquiv α τ).apply_symm_apply x)

theorem eigRank_eq (τ : R →+* O) :
    eigRank α τ = Module.finrank O (Module.Dual O (eigSub α τ)) :=
  ((LinearEquiv.ofInjective _ (ofDual_injective α τ)).trans
    (LinearEquiv.ofEq _ _ (range_ofDual α τ))).finrank_eq.symm

end Local

section Valuation

open GlobalTheory.IndefiniteRowSideFullHecke.HodgeTateCharacterSystems (Lie Cotangent)

theorem exists_retraction {O : Type} [CommRing O] [IsDomain O] [ValuationRing O] {M : Type}
    [AddCommGroup M] [Module O M] [Module.Finite O M] (N : Submodule O M)
    (hN : ∀ (c : O) (x : M), c ≠ 0 → c • x ∈ N → x ∈ N) :
    ∃ r : M →ₗ[O] N, r ∘ₗ N.subtype = LinearMap.id := by
  have h1 : Submodule.torsion O (M ⧸ N) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨c, hc⟩
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    rw [Submonoid.smul_def, ← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at hc
    exact (Submodule.Quotient.mk_eq_zero N).2 (hN _ x (nonZeroDivisors.coe_ne_zero c) hc)
  haveI : Module.Flat O (M ⧸ N) := Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.2 h1
  haveI : Module.Free O (M ⧸ N) := Module.free_of_flat_of_isLocalRing
  obtain ⟨s, hs⟩ := Module.projective_lifting_property N.mkQ LinearMap.id N.mkQ_surjective
  have hmem : ∀ x, (LinearMap.id - s ∘ₗ N.mkQ : M →ₗ[O] M) x ∈ N := fun x => by
    rw [← Submodule.Quotient.mk_eq_zero, ← Submodule.mkQ_apply]
    have := LinearMap.congr_fun hs (N.mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub, this,
      sub_self]
  refine ⟨(LinearMap.id - s ∘ₗ N.mkQ).codRestrict N hmem, ?_⟩
  ext x
  simp [(Submodule.Quotient.mk_eq_zero N).2 x.2]

variable {O : Type} [CommRing O] [IsDomain O] [ValuationRing O]
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G]
  [IsCommMonObj G] {R : Type} [CommRing R] (α : RingAct G R)

theorem eigSub_saturated (τ : R →+* O) (c : O) (x : Lie G) (hc : c ≠ 0)
    (hx : c • x ∈ eigSub α τ) : x ∈ eigSub α τ := by
  intro a
  obtain ⟨y, hy⟩ := (lieEquiv G).surjective (dAct α a (lieEquiv G x))
  have hy' : (lieEquiv G y).1 = (lieEquiv G x).1 ≫ α.act a := congrArg Subtype.val hy
  have h : c • y = c • τ a • x := by
    refine lie_ext ?_
    rw [smul_comm, ← hx a, lieEquiv_smul, lieEquiv_smul, hy', Category.assoc]
  have h' : y = τ a • x := LinearMap.ext fun m => mul_left_cancel₀ hc (LinearMap.congr_fun h m)
  rw [← hy', h']

variable [Smooth G.hom]

theorem exists_retraction_eigSub (τ : R →+* O) :
    ∃ r : Lie G →ₗ[O] eigSub α τ, r ∘ₗ (eigSub α τ).subtype = LinearMap.id := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  exact exists_retraction _ (eigSub_saturated α τ)

theorem finite_free_eigSub (τ : R →+* O) :
    Module.Finite O (eigSub α τ) ∧ Module.Free O (eigSub α τ) := by
  obtain ⟨h₁, h₂⟩ := finite_projective_of_smooth (G := G)
  obtain ⟨r, hr⟩ := exists_retraction_eigSub α τ
  haveI : Module.Finite O (eigSub α τ) :=
    Module.Finite.of_surjective r fun x => ⟨x.1, LinearMap.congr_fun hr x⟩
  haveI : Module.Projective O (eigSub α τ) := Module.Projective.of_split _ r hr
  exact ⟨inferInstance, Module.free_of_flat_of_isLocalRing⟩

theorem map_omTau (τ : R →+* O) :
    (omTau G α τ).map (funEquiv α τ).toLinearMap = omegaEig α τ := by
  refine le_antisymm (map_omTau_le α τ) ?_
  rw [omTau, map_map_restr, ← range_ofDual]
  rintro _ ⟨F, rfl⟩
  obtain ⟨r, hr⟩ := exists_retraction_eigSub α τ
  refine ⟨cotangentBidualToTangentFunction G (F ∘ₗ r), range_cotangentBidualToTangentFunction.le ⟨_, rfl⟩, funext fun x => ?_⟩
  obtain ⟨x, rfl⟩ := (subEquiv α τ).surjective x
  rw [ofDual_apply]
  exact (cotangentBidualToTangentFunction_apply (F ∘ₗ r) x.1).trans (congrArg F (LinearMap.congr_fun hr x))

def omEquiv (τ : R →+* O) : omTau G α τ ≃ₗ[O] omegaEig α τ :=
  (funEquiv α τ).ofSubmodules _ _ (map_omTau α τ)

theorem rTau_eq (τ : R →+* O) : rTau G α τ = eigRank α τ := (omEquiv α τ).finrank_eq

def cokerEquiv (p : ℕ) (τ : R →+* O) :
    (omTau G α τ ⧸ (htTau G α p τ).comap (omTau G α τ).subtype) ≃ₗ[O]
      (omegaEig α τ ⧸ htEig α p τ) :=
  Submodule.Quotient.equiv _ _ (omEquiv α τ) (by
    ext f
    obtain ⟨f, rfl⟩ := (omEquiv α τ).surjective f
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_apply_apply, Submodule.mem_comap, htEig,
      Submodule.mem_comap, ← map_map_restr, Submodule.mem_map_equiv]
    exact Iff.of_eq (congrArg (· ∈ _) ((funEquiv α τ).symm_apply_apply f.1).symm))

end Valuation

section Places

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]

theorem toPadic_apply (a : 𝓞 E) : toPadic p E a = (1 : ℤ_[p]) ⊗ₜ[ℤ] a := rfl

theorem tauExt_toPadic {O : Type} [CommRing O] [Algebra ℤ_[p] O] (τ : 𝓞 E →+* O) (a : 𝓞 E) :
    tauExt τ (toPadic p E a) = τ a := by
  simp [toPadic_apply, tauExt]

theorem exists_approx (n : ℕ) (x : PadicOrder p E) :
    ∃ (a : 𝓞 E) (y : PadicOrder p E), x = toPadic p E a + (p : PadicOrder p E) ^ n * y := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul z a =>
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec n z)
    refine ⟨(z.appr n : 𝓞 E) * a, c ⊗ₜ a, ?_⟩
    have h1 : ∀ (m : ℕ) (u : ℤ_[p]), (m : PadicOrder p E) * u ⊗ₜ a = ((m : ℤ_[p]) * u) ⊗ₜ a := by
      intro m u
      rw [← nsmul_eq_mul, ← nsmul_eq_mul, TensorProduct.smul_tmul']
    rw [map_mul, map_natCast, toPadic_apply, ← Nat.cast_pow, h1, h1, ← TensorProduct.add_tmul]
    congr 1
    push_cast
    linear_combination -hc
  | add x y hx hy =>
    obtain ⟨a, u, rfl⟩ := hx
    obtain ⟨b, w, rfl⟩ := hy
    exact ⟨a + b, u + w, by rw [map_add]; ring⟩

abbrev plId (p : ℕ) [Fact p.Prime] (w : HeightOneSpectrum (𝓞 E)) : Ideal (PadicOrder p E) :=
  w.asIdeal.map (toPadic p E)

theorem p_mem_plId {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) :
    (p : PadicOrder p E) ∈ plId p w := by
  simpa using Ideal.mem_map_of_mem (toPadic p E) hw

theorem exists_eq_plId (M : Ideal (PadicOrder p E)) [M.IsPrime] (hp : (p : PadicOrder p E) ∈ M) :
    ∃ w : HeightOneSpectrum (𝓞 E), IsOver p w ∧ w.asIdeal = M.comap (toPadic p E) ∧
      M = plId p w := by
  have h1 : (p : 𝓞 E) ∈ M.comap (toPadic p E) := by simpa [Ideal.mem_comap] using hp
  let w : HeightOneSpectrum (𝓞 E) := ⟨M.comap (toPadic p E), inferInstance, fun h => by
    rw [h, Ideal.mem_bot, Nat.cast_eq_zero] at h1
    exact (Fact.out : p.Prime).ne_zero h1⟩
  refine ⟨w, h1, rfl, le_antisymm (fun x hx => ?_) Ideal.map_comap_le⟩
  obtain ⟨a, y, rfl⟩ := exists_approx 1 x
  rw [pow_one] at hx ⊢
  have : toPadic p E a ∈ M := (M.add_mem_iff_left (M.mul_mem_right _ hp)).1 hx
  exact add_mem (Ideal.mem_map_of_mem _ this) (Ideal.mul_mem_right _ _ (p_mem_plId (w := w) h1))

theorem mem_jacobson {x : PadicOrder p E} (hx : ∀ w, IsOver p w → x ∈ plId p w) :
    x ∈ (⊥ : Ideal (PadicOrder p E)).jacobson := by
  rw [Ideal.jacobson, Ideal.mem_sInf]
  rintro M ⟨-, hM⟩
  have hp : (p : PadicOrder p E) ∈ M := by
    have := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.map_maximalIdeal_le_maximal (R := ℤ_[p]) _ M hM
    rw [PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton, map_natCast] at this
    exact this (Ideal.subset_span rfl)
  obtain ⟨w, hw, -, rfl⟩ := exists_eq_plId M hp
  exact hx w hw

theorem exists_toCompletion {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) :
    ∃ _ : Algebra ℤ_[p] (Ow w), True := by
  haveI := GlobalTheory.SelfDualGenus.isAdicComplete_adicCompletionIntegers w
  obtain ⟨φ⟩ := GlobalTheory.nonempty_padicInt_ringHom_of_isAdicComplete
    (IsLocalRing.maximalIdeal (Ow w)) p (by
      rw [← map_natCast (algebraMap (𝓞 E) (Ow w))]
      exact fun h => (GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff w _).1 h hw)
  exact ⟨φ.toAlgebra, trivial⟩

theorem comap_tauExt {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[p] O]
    {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) (τ : 𝓞 E →+* O)
    (hτ : ∀ a, a ∈ w.asIdeal ↔ τ a ∈ IsLocalRing.maximalIdeal O) :
    (IsLocalRing.maximalIdeal O).comap (tauExt (p := p) τ) = plId p w := by
  obtain ⟨u, -, h1, h2⟩ := exists_eq_plId ((IsLocalRing.maximalIdeal O).comap (tauExt (p := p) τ))
    (by rw [Ideal.mem_comap, map_natCast, ← map_natCast τ]; exact (hτ _).1 hw)
  rw [h2]
  congr 1
  ext a
  rw [h1, Ideal.mem_comap, Ideal.mem_comap, tauExt_toPadic, hτ]

theorem mem_iff_algebraMap (w : HeightOneSpectrum (𝓞 E)) (a : 𝓞 E) :
    a ∈ w.asIdeal ↔ algebraMap (𝓞 E) (Ow w) a ∈ IsLocalRing.maximalIdeal (Ow w) := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, GlobalTheory.SelfDualGenus.isUnit_algebraMap_iff,
    not_not]

theorem plId_isPrime {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) : (plId p w).IsPrime := by
  obtain ⟨_, -⟩ := exists_toCompletion hw
  rw [← comap_tauExt hw _ (mem_iff_algebraMap w)]
  infer_instance

theorem not_mem_of_isPlaceIdem {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w)
    {e : PadicOrder p E} (he : IsPlaceIdem p w e) : e ∉ plId p w := fun h =>
  (plId_isPrime hw).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using sub_mem h he.2.1))

theorem exists_isPlaceIdem {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) :
    ∃ e, IsPlaceIdem p w e := by
  classical
  have hp0 : Ideal.span {(p : 𝓞 E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot, Nat.cast_eq_zero]
    exact (Fact.out : p.Prime).ne_zero
  have hfin : {u : HeightOneSpectrum (𝓞 E) | IsOver p u}.Finite :=
    (Ideal.finite_factors hp0).subset fun u hu => Ideal.dvd_span_singleton.2 hu
  obtain ⟨a, ha⟩ := IsDedekindDomain.exists_forall_sub_mem_ideal (s := hfin.toFinset)
    (fun u => u.asIdeal) (fun _ => 1) (fun u _ => u.prime)
    (fun u _ u' _ h h' => h (HeightOneSpectrum.ext h'))
    (fun u => if u.1 = w then 1 else 0)
  have ha1 : toPadic p E a - 1 ∈ plId p w := by
    have := Ideal.mem_map_of_mem (toPadic p E) (ha w (hfin.mem_toFinset.2 hw))
    simpa using this
  have ha0 : ∀ u, IsOver p u → u ≠ w → toPadic p E a ∈ plId p u := fun u hu h => by
    have := Ideal.mem_map_of_mem (toPadic p E) (ha u (hfin.mem_toFinset.2 hu))
    simpa [h] using this
  set x := toPadic p E a
  have hj : x * x - x ∈ (⊥ : Ideal (PadicOrder p E)).jacobson := mem_jacobson fun u hu => by
    rw [← mul_sub_one]
    by_cases h : u = w
    · exact Ideal.mul_mem_left _ _ (h ▸ ha1)
    · exact Ideal.mul_mem_right _ _ (ha0 u hu h)
  obtain ⟨N, -, hN⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_pow_mem_map_maximalIdeal (R := ℤ_[p]) _ (x * x - x)
    fun M hM => Ideal.mem_sInf.1 hj ⟨bot_le, hM⟩
  haveI := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra (R := ℤ_[p]) (PadicOrder p E)
  obtain ⟨e, s, he, hs⟩ := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.exists_idempotent_henselian _ x N
    (by rw [pow_succ]; exact Ideal.mul_mem_right _ _ hN)
  refine ⟨e, he, ?_, fun u hu h => ?_⟩
  · rw [show e - 1 = (1 + s * x) * (x - 1) by linear_combination hs]
    exact Ideal.mul_mem_left _ _ ha1
  · rw [show e = (1 + s * (x - 1)) * x by linear_combination hs]
    exact Ideal.mul_mem_left _ _ (ha0 u hu h)

theorem tauExt_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] [Algebra ℤ_[p] O]
    {w : HeightOneSpectrum (𝓞 E)} (hw : IsOver p w) {e : PadicOrder p E} (he : IsPlaceIdem p w e)
    (τ : 𝓞 E →+* O) (hτ : ∀ a, a ∈ w.asIdeal ↔ τ a ∈ IsLocalRing.maximalIdeal O) :
    tauExt τ e = 1 := by
  refine (IsIdempotentElem.iff_eq_zero_or_one.1 (he.1.map (tauExt τ))).resolve_left fun h => ?_
  refine not_mem_of_isPlaceIdem hw he ?_
  rw [← comap_tauExt hw τ hτ, Ideal.mem_comap, h]
  exact zero_mem _

end Places

section Completion

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E]
  {w : HeightOneSpectrum (𝓞 E)}

theorem integers_Ow (w : HeightOneSpectrum (𝓞 E)) :
    (Valued.v : Valuation (w.adicCompletion E) _).Integers (Ow w) :=
  Valuation.valuationSubring.integers _

theorem valued_algebraMap (a : 𝓞 E) :
    Valued.v (algebraMap (Ow w) (w.adicCompletion E) (algebraMap (𝓞 E) (Ow w) a)) =
      w.intValuation a := by
  change Valued.v ((algebraMap (𝓞 E) (Ow w) a : Ow w) : w.adicCompletion E) = _
  rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation',
    HeightOneSpectrum.valuation_of_algebraMap]

variable [Algebra ℤ_[p] (Ow w)]

theorem toCompletion_surjective (hw : IsOver p w) :
    Function.Surjective (tauExt (p := p) (algebraMap (𝓞 E) (Ow w))) := by
  let I := IsLocalRing.maximalIdeal ℤ_[p]
  haveI : IsPrecomplete I (PadicOrder p E) := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isPrecomplete_finite_module I _
  have hI : I.map (algebraMap ℤ_[p] (Ow w)) = Ideal.span {(p : Ow w)} := by
    rw [show I = _ from PadicInt.maximalIdeal_eq_span_p, Ideal.map_span, Set.image_singleton,
      map_natCast]
  haveI : IsHausdorff I (Ow w) := by
    rw [← IsHausdorff.map_algebraMap_iff (S := Ow w)]
    refine IsHausdorff.of_le_jacobson _ _ ?_
    rw [hI, IsLocalRing.jacobson_eq_maximalIdeal _ bot_ne_top, Ideal.span_singleton_le_iff_mem,
      ← map_natCast (algebraMap (𝓞 E) (Ow w))]
    exact (mem_iff_algebraMap w _).1 hw
  refine surjective_of_mkQ_comp_surjective (I := I)
    (f := (tauExt (p := p) (algebraMap (𝓞 E) (Ow w))).toLinearMap) fun y => ?_
  obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ y
  have hp0 : w.intValuation (p : 𝓞 E) ≠ 0 :=
    w.intValuation_ne_zero _ (Nat.cast_ne_zero.2 (Fact.out : p.Prime).ne_zero)
  obtain ⟨r, hr⟩ := GlobalTheory.Idele.exists_valued_sub_le w (a := (y : w.adicCompletion E)) y.2
    (-(w.intValuation (p : 𝓞 E)).log).toNat
  have hd : (p : Ow w) ∣ y - algebraMap (𝓞 E) (Ow w) r := by
    refine (integers_Ow w).dvd_of_le ?_
    rw [← map_natCast (algebraMap (𝓞 E) (Ow w)), valued_algebraMap]
    refine le_trans hr ?_
    conv_rhs => rw [← WithZero.exp_log hp0]
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨toPadic p E r, ?_⟩
  rw [LinearMap.comp_apply, AlgHom.toLinearMap_apply, tauExt_toPadic, eq_comm,
    Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, Ideal.smul_top_eq_map, hI]
  exact Ideal.mem_span_singleton.2 hd

theorem mul_eq_zero_of_toCompletion (hw : IsOver p w) {e : PadicOrder p E}
    (he : IsPlaceIdem p w e) {x : PadicOrder p E}
    (hx : tauExt (p := p) (algebraMap (𝓞 E) (Ow w)) x = 0) : e * x = 0 := by
  let J := (⊥ : Ideal (PadicOrder p E)).jacobson
  haveI : IsNoetherianRing (PadicOrder p E) := Algebra.FiniteType.isNoetherianRing ℤ_[p] _
  have hH : IsHausdorff J (PadicOrder p E) := IsHausdorff.of_le_jacobson _ _ le_rfl
  have hJ : Ideal.span {e} * plId p w ≤ J := by
    refine Ideal.mul_le.2 fun a ha b hb => mem_jacobson fun u hu => ?_
    by_cases h : u = w
    · exact Ideal.mul_mem_left _ _ (h ▸ hb)
    · exact Ideal.mul_mem_right _ _
        ((Ideal.span_singleton_le_iff_mem _).2 (he.2.2 u hu h) ha)
  refine hH.haus _ fun n => ?_
  rw [SModEq.zero, smul_eq_mul, Ideal.mul_top]
  cases n with
  | zero => simp
  | succ n =>
  obtain ⟨a, y, rfl⟩ := exists_approx (n + 1) x
  have ha : a ∈ w.asIdeal ^ (n + 1) := by
    rw [map_add, map_mul, map_pow, map_natCast, tauExt_toPadic, add_eq_zero_iff_eq_neg] at hx
    rw [← HeightOneSpectrum.intValuation_le_pow_iff_mem, ← valued_algebraMap]
    refine le_trans ((integers_Ow w).le_of_dvd
      (x := algebraMap (𝓞 E) (Ow w) ((p : 𝓞 E) ^ (n + 1))) ?_) ?_
    · rw [hx, map_pow, map_natCast]
      exact (dvd_mul_right _ _).neg_right
    · rw [valued_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_mem]
      exact Ideal.pow_mem_pow hw _
  rw [mul_add]
  refine add_mem (Ideal.pow_right_mono hJ _ ?_)
    (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow
      (mem_jacobson fun u hu => p_mem_plId hu) _)))
  rw [mul_pow, ← he.1.pow_succ_eq n, ← Ideal.map_pow]
  refine Ideal.mul_mem_mul (Ideal.pow_mem_pow ?_ _) (Ideal.mem_map_of_mem _ ha)
  rw [he.1.pow_succ_eq]
  exact Ideal.subset_span rfl

end Completion

section Conj

variable {p : ℕ} [Fact p.Prime] {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem conjInt_conjInt (a : 𝓞 E) : conjInt E (conjInt E a) = a := by
  ext
  simp [conjInt]

@[reducible] def conjStar (E : Type) [Field E] [NumberField E] [IsCMField E] :
    StarRing (𝓞 E) where
  star := conjInt E
  star_involutive := conjInt_conjInt
  star_mul a b := by rw [map_mul, mul_comm]
  star_add a b := map_add _ a b

variable [StarRing (𝓞 E)] (hs : ∀ a : 𝓞 E, star a = conjInt E a)
include hs

theorem sig_tmul (z : ℤ_[p]) (a : 𝓞 E) : sig p (𝓞 E) (z ⊗ₜ a) = z ⊗ₜ conjInt E a := by
  rw [← hs]; rfl

theorem sig_mem {w : HeightOneSpectrum (𝓞 E)} {x : PadicOrder p E} (hx : x ∈ plId p w) :
    sig p (𝓞 E) x ∈ plId p (conjPlace w) := by
  have : plId p w ≤ (plId p (conjPlace w)).comap (sig p (𝓞 E)) := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap, toPadic_apply, sig_tmul hs]
    refine Ideal.mem_map_of_mem (toPadic p E) ?_
    change conjInt E (conjInt E a) ∈ w.asIdeal
    rwa [conjInt_conjInt]
  exact this hx

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O]
  [Algebra O C] [Algebra ℤ_[p] O] (hv : v.Integers O) (hp : v (p : C) < 1)
  {G : Over (Spec (CommRingCat.of O))} [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
  (α : RingAct G (𝓞 E))
include hv hp

end Conj

section TorusAction

open GlobalTheory.SplitTorus GlobalTheory.SemiRigid

end TorusAction

end GlobalTheory.EigenLieCompare
