import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapPairDetCovec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationConstantOfPowerEq
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCompleteDvrIntegralClosureFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open NumberField IsDedekindDomain
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
open Formalism.L2.Pj GlobalTheory.HTLat GlobalTheory.HTLat.OmegaRank GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore GlobalTheory.LineNorm
attribute [local instance] Over.cartesianMonoidalCategory
attribute [local instance] algPadicInt algPadicField towerPadic factPadic GlobalTheory.PadicComplexHost.isAdicComplete

namespace GlobalTheory.FlatModel

theorem exists_alg_norm_eq (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ a : PadicAlgCl p, ‖(a : ℂ_[p])‖ = ‖x‖ := by
  have hpos : 0 < ‖x‖ := norm_pos_iff.2 hx
  obtain ⟨a, ha⟩ := (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)).exists_dist_lt x hpos
  refine ⟨a, ?_⟩
  rw [dist_eq_norm] at ha
  have h1 : ‖(a : ℂ_[p])‖ ≤ max ‖x‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max x (-(x - (a : ℂ_[p])))
    rwa [norm_neg, show x + -(x - (a : ℂ_[p])) = (a : ℂ_[p]) by ring] at this
  have h2 : ‖x‖ ≤ max ‖(a : ℂ_[p])‖ ‖x - (a : ℂ_[p])‖ := by
    have := IsUltrametricDist.norm_add_le_max (a : ℂ_[p]) (x - (a : ℂ_[p]))
    rwa [show (a : ℂ_[p]) + (x - (a : ℂ_[p])) = x by ring] at this
  rw [max_eq_left ha.le] at h1
  refine le_antisymm h1 ?_
  rcases le_max_iff.1 h2 with h | h
  · exact h
  · exact absurd h (not_le.2 ha)

theorem norm_unit_int (p : ℕ) [Fact p.Prime] {u : 𝓞_ℂ_[p]} (hu : IsUnit u) : ‖(u : ℂ_[p])‖ = 1 := by
  rw [← coe_valued]
  have := (PadicComplexInt.integers p).one_of_isUnit hu
  exact_mod_cast this

theorem norm_eq_unif_pow (p : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] {ϖ : O} (hϖ : Irreducible ϖ) (φ : O →+* 𝓞_ℂ_[p]) {n : O} (hn : n ≠ 0) :
    ∃ m : ℕ, ‖((φ n : 𝓞_ℂ_[p]) : ℂ_[p])‖ = ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m := by
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hn hϖ
  refine ⟨m, ?_⟩
  rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
    norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul]

theorem exists_frac_model (p : ℕ) [Fact p.Prime] (a : PadicAlgCl p) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (φ : O →+* 𝓞_ℂ_[p]) (n d : O),
      Function.Injective φ ∧ IsLocalHom φ ∧ d ≠ 0 ∧
        ((φ n : 𝓞_ℂ_[p]) : ℂ_[p]) = (a : ℂ_[p]) * ((φ d : 𝓞_ℂ_[p]) : ℂ_[p]) := by
  let L := IntermediateField.adjoin ℚ_[p] ({a} : Set (PadicAlgCl p))
  haveI : FiniteDimensional ℚ_[p] L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  obtain ⟨W, _, _, _, _, _, _, _, hc, hfin, -, -, -, -⟩ :=
    GlobalTheory.SS.exists_complete_dvr_finite_extension ℤ_[p] ℚ_[p] L
  let φ₀ : W →+* ℂ_[p] :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).comp (L.val.toRingHom.comp (algebraMap W L))
  have hcomp : (algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp (padicIntHom p) = φ₀.comp (algebraMap ℤ_[p] W) := by
    ext z
    have h1 := congrArg (fun g => g z) hc
    simp only [RingHom.comp_apply] at h1
    simp only [RingHom.comp_apply, φ₀, h1]
    rfl
  have hint : ∀ b : W, φ₀ b ∈ 𝓞_ℂ_[p] := by
    intro b
    haveI : Algebra.IsIntegral ℤ_[p] W := Algebra.IsIntegral.of_finite ℤ_[p] W
    have h1 : IsIntegral 𝓞_ℂ_[p] (φ₀ b) :=
      IsIntegral.map_of_comp_eq (padicIntHom p) φ₀ hcomp (Algebra.IsIntegral.isIntegral b)
    exact (PadicComplexInt.integers p).mem_of_integral h1
  let φ : W →+* 𝓞_ℂ_[p] := φ₀.codRestrict 𝓞_ℂ_[p] hint
  have hinj0 : Function.Injective φ₀ :=
    (algebraMap (PadicAlgCl p) ℂ_[p]).injective.comp
      (Subtype.val_injective.comp (IsFractionRing.injective W L))
  have hinj : Function.Injective φ := fun b c h => hinj0 (congrArg Subtype.val h)
  have hle : ∀ u : 𝓞_ℂ_[p], ‖(u : ℂ_[p])‖ ≤ 1 := fun u => by
    rw [← coe_valued]
    exact_mod_cast u.2
  have hpn : ‖((φ ((p : ℕ) : W) : 𝓞_ℂ_[p]) : ℂ_[p])‖ = (p : ℝ)⁻¹ := by
    rw [map_natCast]
    rw [show (((p : ℕ) : 𝓞_ℂ_[p]) : ℂ_[p]) = ((p : ℕ) : ℂ_[p]) from map_natCast (algebraMap 𝓞_ℂ_[p] ℂ_[p]) p]
    rw [← coe_valued, PadicComplex.valuation_p]
    simp
  have hpos : (0 : ℝ) < (p : ℝ)⁻¹ := inv_pos.2 (Nat.cast_pos.2 (Fact.out : p.Prime).pos)
  have hp1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
  have hloc : IsLocalHom φ := by
    refine ⟨fun b hb => ?_⟩
    by_contra hnb
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
    have hp0 : ((p : ℕ) : W) ≠ 0 := fun h => by
      rw [h, map_zero] at hpn
      simp only [ZeroMemClass.coe_zero, norm_zero] at hpn
      exact hpos.ne hpn
    obtain ⟨e, he⟩ := norm_eq_unif_pow p hϖ φ hp0
    have hϖ1 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ < 1 := by
      refine lt_of_le_of_ne (hle _) fun h => ?_
      rw [h, one_pow, hpn] at he
      exact hp1.ne he
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [map_zero] at hb
      exact not_isUnit_zero hb
    obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hϖ
    have hm : m ≠ 0 := by
      rintro rfl
      exact hnb (by rw [pow_zero, _root_.mul_one]; exact u.isUnit)
    have h1 := norm_unit_int p hb
    rw [map_mul, map_pow, Subring.coe_mul, SubmonoidClass.coe_pow, norm_mul, norm_pow,
      norm_unit_int p ((Units.isUnit u).map φ), _root_.one_mul] at h1
    have h2 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ m ≤ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ :=
      pow_le_of_le_one (norm_nonneg _) (hle _) hm
    linarith
  let a' : L := ⟨a, IntermediateField.mem_adjoin_simple_self ℚ_[p] a⟩
  obtain ⟨n, d, hd, hnd⟩ := IsFractionRing.div_surjective (A := W) a'
  have hd0 : d ≠ 0 := nonZeroDivisors.ne_zero hd
  have hdL : algebraMap W L d ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).2 hd0
  have e1 : algebraMap W L n = a' * algebraMap W L d := by rw [← hnd, div_mul_cancel₀ _ hdL]
  refine ⟨W, inferInstance, inferInstance, inferInstance, inferInstance, φ, n, d, hinj, hloc, hd0, ?_⟩
  have e2 := congrArg (fun z : L => algebraMap (PadicAlgCl p) ℂ_[p] (z : PadicAlgCl p)) e1
  simp only [MulMemClass.coe_mul, map_mul] at e2
  exact e2

theorem exists_unif_norm (p : ℕ) [Fact p.Prime] (x : ℂ_[p]) (hx : x ≠ 0) :
    ∃ (O : Type) (_ : CommRing O) (_ : IsDomain O) (_ : IsDiscreteValuationRing O)
      (_ : IsAdicComplete (IsLocalRing.maximalIdeal O) O) (ϖ : O) (_ : Irreducible ϖ)
      (φ : O →+* 𝓞_ℂ_[p]) (k : ℤ),
      Function.Injective φ ∧ IsLocalHom φ ∧ ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ^ k = ‖x‖ := by
  obtain ⟨a, ha⟩ := exists_alg_norm_eq p x hx
  obtain ⟨O, _, _, _, _, φ, n, d, hinj, hloc, hd, hnd⟩ := exists_frac_model p a
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hne : ∀ b : O, b ≠ 0 → ((φ b : 𝓞_ℂ_[p]) : ℂ_[p]) ≠ 0 := fun b hb h =>
    hb (hinj (by rw [map_zero]; exact Subtype.ext h))
  have hxa : (a : ℂ_[p]) ≠ 0 := fun h => hx (norm_eq_zero.1 (ha ▸ (norm_eq_zero.2 h)))
  have hn : n ≠ 0 := by
    rintro rfl
    rw [map_zero, ZeroMemClass.coe_zero] at hnd
    exact mul_ne_zero hxa (hne d hd) hnd.symm
  obtain ⟨m₁, h₁⟩ := norm_eq_unif_pow p hϖ φ hn
  obtain ⟨m₂, h₂⟩ := norm_eq_unif_pow p hϖ φ hd
  have hϖ0 : ‖((φ ϖ : 𝓞_ℂ_[p]) : ℂ_[p])‖ ≠ 0 := norm_ne_zero_iff.2 (hne ϖ hϖ.ne_zero)
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, φ, (m₁ : ℤ) - m₂,
    hinj, hloc, ?_⟩
  have e := congrArg norm hnd
  rw [norm_mul, h₁, h₂, ha] at e
  rw [zpow_sub₀ hϖ0, zpow_natCast, zpow_natCast, e, mul_div_cancel_right₀ _ (pow_ne_zero _ hϖ0)]

end GlobalTheory.FlatModel

namespace GlobalTheory.FlatModel

open GlobalTheory.IndefiniteRowSideFullHecke.SpecialFibreUnits GlobalTheory.ValConstOfPowEq in

theorem packSt : PackSt := by
  intro p _ x hx
  obtain ⟨O, _, _, _, _, ϖ, hϖ, φ, k, hinj, hloc, hk⟩ := exists_unif_norm p x hx
  obtain ⟨hI, hN, hP, hF, -, hD, ht⟩ := hyp_spec O
  let f : Spec (.of O) ⟶ Spec (.of O) := 𝟙 _
  let D := trivLB (Spec (.of O))
  let sig : (D.pull (genericι f)).Gen :=
    ⟨fun _ => res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k))⟩
  have hsig : sig.IsGen := by
    intro i j
    rw [show (D.pull (genericι f)).g i j = 1 from linComb_g_one D (fun _ _ => rfl) _ _ i j, _root_.one_mul]
    exact (res_res' _ _ _).trans (res_res' _ _ _).symm
  have hg : Function.Injective ((algebraMap 𝓞_ℂ_[p] ℂ_[p]).comp φ) :=
    (IsFractionRing.injective 𝓞_ℂ_[p] ℂ_[p]).comp hinj
  let ψ : FractionRing O →+* ℂ_[p] := IsFractionRing.lift hg
  let ybar : Spec (.of 𝓞_ℂ_[p]) ⟶ Spec (.of O) := Spec.map (CommRingCat.ofHom φ)
  have hw : (Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar) ≫ f =
      Spec.map (CommRingCat.ofHom ψ) ≫ Spec.map (CommRingCat.ofHom (algebraMap O (FractionRing O))) := by
    simp only [f, ybar, Category.comp_id, ← Spec.map_comp]
    congr 1
    ext a
    simp [ψ, IsFractionRing.lift_algebraMap]
  let y : Spec (.of ℂ_[p]) ⟶ genericFibre f := pullback.lift _ _ hw
  have hy : y ≫ genericι f = Spec.map (CommRingCat.ofHom (algebraMap 𝓞_ℂ_[p] ℂ_[p])) ≫ ybar :=
    pullback.lift_fst _ _ _
  have hj₀ : ybar ⁻¹ᵁ D.U PUnit.unit = ⊤ := by simp [D, trivLB]
  have htop := top_le_generic D ybar y hy PUnit.unit hj₀
  let cc : ℂ_[p]ˣ := Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
    (res htop (pullU y _ (sig.s (fun _ => PUnit.unit))))
  have hcc : (cc : ℂ_[p]) = (algebraMap 𝓞_ℂ_[p] ℂ_[p] (φ ϖ)) ^ k := by
    have e0 : constUnit (genericStr f) (unifUnit ϖ hϖ ^ k) = constUnit (genericStr f) (unifUnit ϖ hϖ) ^ k := by
      simp only [constUnit, map_zpow]
    have e1 : res htop (pullU y _ (sig.s (fun _ => PUnit.unit))) =
        (res (le_top : ⊤ ≤ y ⁻¹ᵁ ⊤) (pullU y ⊤ (constUnit (genericStr f) (unifUnit ϖ hϖ)))) ^ k := by
      show res htop (pullU y _ (res le_top (constUnit (genericStr f) (unifUnit ϖ hϖ ^ k)))) = _
      rw [res_pullU_res', e0, map_zpow, map_zpow]
      all_goals rfl
    show ((Units.map (Scheme.ΓSpecIso (.of ℂ_[p])).hom.hom.toMonoidHom
      (res htop (pullU y _ (sig.s (fun _ => PUnit.unit)))) : ℂ_[p]ˣ) : ℂ_[p]) = _
    rw [e1, map_zpow, Units.val_zpow_eq_zpow_val]
    congr 1
    exact eval_constUnit ϖ hϖ φ ybar (Category.comp_id _) y hy le_top
  refine ⟨O, inferInstance, inferInstance, inferInstance, inferInstance, ϖ, hϖ, Spec (.of O), f, D,
    hI, hN, hP, hF, hD, ht, sig, hsig, φ, hinj, hloc, ybar, y, chartGen D ybar PUnit.unit hj₀, cc,
    Category.comp_id _, hy, chartGen_isGen D hD ybar PUnit.unit hj₀,
    isCoord_chartGen D sig hsig ybar y hy PUnit.unit hj₀, ?_⟩
  rw [hcc, norm_zpow, ← hk]
  rfl

end GlobalTheory.FlatModel
