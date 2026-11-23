import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.DimPosOfHasType

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FlatCM.Model

open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM

section Index

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem ιMulti_comb {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) K) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = c.det • exteriorPower.ιMulti K m b := by
  have h : (exteriorPower.ιMulti K m).compLinearMap (Fintype.linearCombination K b) =
      (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K).smulRight (exteriorPower.ιMulti K m b) := by
    refine (Pi.basisFun K (Fin m)).ext_alternating fun v hv => ?_
    let s : Equiv.Perm (Fin m) := Equiv.ofBijective v (Finite.injective_iff_bijective.1 hv)
    have e : (fun i => Pi.basisFun K (Fin m) (v i)) = (fun i => Pi.basisFun K (Fin m) i) ∘ s := rfl
    rw [e, AlternatingMap.map_perm, AlternatingMap.map_perm]
    congr 1
    have e1 : (Matrix.detRowAlternating : (Fin m → K) [⋀^Fin m]→ₗ[K] K) (fun i => Pi.basisFun K (Fin m) i) = 1 := by
      change Matrix.det (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1
      rw [show (Matrix.of fun i => Pi.basisFun K (Fin m) i) = 1 from by
        ext i j; simp [Matrix.one_apply, Pi.single_apply, eq_comm], Matrix.det_one]
    rw [AlternatingMap.smulRight_apply, e1, one_smul, AlternatingMap.compLinearMap_apply]
    congr 1
    funext i
    simp
  exact AlternatingMap.congr_fun h c

omit [NumberField K] in

theorem ιMulti_comb_int {m : ℕ} (b : Fin m → V) (c : Matrix (Fin m) (Fin m) (𝓞 K)) :
    exteriorPower.ιMulti K m (fun i => ∑ j, c i j • b j) = algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b := by
  have := ιMulti_comb b (c.map (algebraMap (𝓞 K) K))
  rw [← RingHom.mapMatrix_apply, ← RingHom.map_det] at this
  rw [← this]
  congr 1
  funext i
  exact Finset.sum_congr rfl fun j _ => (algebraMap_smul K _ _).symm

omit [NumberField K] in

theorem detSpan_span {m : ℕ} (b : Fin m → V) :
    detSpan K m (Submodule.span (𝓞 K) (Set.range b)) = Submodule.span (𝓞 K) {exteriorPower.ιMulti K m b} := by
  refine le_antisymm (Submodule.span_le.2 ?_) (Submodule.span_mono ?_)
  · rintro _ ⟨y, hy, rfl⟩
    choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun (𝓞 K)).1 (hy i)
    rw [show y = fun i => ∑ j, (Matrix.of c) i j • b j from funext fun i => (hc i).symm, ιMulti_comb_int]
    exact Submodule.mem_span_singleton.2 ⟨_, rfl⟩
  · rintro _ rfl
    exact ⟨b, fun i => Submodule.subset_span ⟨i, rfl⟩, rfl⟩

omit [NumberField K] in

theorem idx_span {m : ℕ} (b : Fin m → V) (hb : exteriorPower.ιMulti K m b ≠ 0) (c : Matrix (Fin m) (Fin m) (𝓞 K)) :
    idx K m (Submodule.span (𝓞 K) (Set.range b)) (Submodule.span (𝓞 K) (Set.range fun i => ∑ j, c i j • b j)) =
      Ideal.span {c.det} := by
  ext r
  rw [idx, detSpan_span, detSpan_span, ιMulti_comb_int, Submodule.mem_colon, Ideal.mem_span_singleton']
  constructor
  · intro h
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 (h _ (Submodule.mem_span_singleton_self _))
    refine ⟨a, ?_⟩
    change algebraMap (𝓞 K) K a • algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b =
      algebraMap (𝓞 K) K r • exteriorPower.ιMulti K m b at ha
    rw [smul_smul, ← map_mul] at ha
    exact RingOfIntegers.ext (smul_left_injective K hb ha)
  · rintro ⟨a, rfl⟩ w hw
    obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 hw
    refine Submodule.mem_span_singleton.2 ⟨a * s, ?_⟩
    change algebraMap (𝓞 K) K (a * s) • algebraMap (𝓞 K) K c.det • exteriorPower.ιMulti K m b =
      algebraMap (𝓞 K) K (a * c.det) • algebraMap (𝓞 K) K s • exteriorPower.ιMulti K m b
    rw [smul_smul, smul_smul, ← map_mul, ← map_mul]
    congr 2
    ring

omit [NumberField K] [IsScalarTower (𝓞 K) K V] in

theorem idx_zero (L N : Submodule (𝓞 K) V) : idx K 0 L N = ⊤ := by
  have : detSpan K 0 N = detSpan K 0 L := by
    unfold detSpan
    congr 1
    ext w
    exact exists_congr fun y => and_congr_left fun _ => ⟨fun _ i => i.elim0, fun _ i => i.elim0⟩
  rw [idx, this]
  exact (Ideal.eq_top_iff_one _).2 (Submodule.mem_colon.2 fun _ h => by simpa using h)

end Index

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ}

theorem isGram_one_zero (X : CMObj H K ρ σ₁ 1 0) : IsGram X (fun _ _ => X.hh (Sum.inl 0)) 0 :=
  ⟨fun a b => by
    obtain rfl := Subsingleton.elim a 0
    obtain rfl := Subsingleton.elim b 0
    exact X.weil (Sum.inl 0), fun a => a.elim0⟩

theorem isGram_zero_one (X : CMObj H K ρ σ₁ 0 1) : IsGram X 0 (fun _ _ => X.hh (Sum.inr 0)) :=
  ⟨fun a => a.elim0, fun a b => by
    obtain rfl := Subsingleton.elim a 0
    obtain rfl := Subsingleton.elim b 0
    exact X.weil (Sum.inr 0)⟩

theorem exists_isDiffs (hU : ThetaUnifAV) (hL : Out.Laws) {p q : ℕ} (X : CMObj H K ρ σ₁ p q) :
    ∃ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
      (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
      (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ := by
  obtain ⟨FA, FB, -, -, M, -, -, -, hM, -⟩ := NumInh.exists_data hU hL X
  exact ⟨FA true, FA false, FB, fun a => M (Sum.inl a), fun a => M (Sum.inr a), fun a => hM (Sum.inl a),
    fun a => hM (Sum.inr a)⟩

theorem index_one_zero (h : IdealSt) (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) (X : CMObj H K ρ σ₁ 1 0) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {X.hh (Sum.inl 0)} ∧
      ∀ (FP : GenFib (X.A true).pol) (FB : GenFib X.B.pol) (M : (Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)),
        FP.IsDiffOf FB (phiP X 0) M → GenFib (X.A false).pol → ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          idx K 1 (FB.eigLat X.B.t.act τ) (subP FP FB (fun _ => M) τ) = 𝔫.map τ := by
  obtain ⟨𝔫, h1, h2⟩ := h E H hH K ρ σ₁ 1 0 X _ _ (isGram_one_zero X)
  refine ⟨𝔫, by
    rw [h1, Matrix.det_isEmpty, _root_.mul_one]
    exact congrArg (fun x => Ideal.span {x}) (Matrix.det_unique (Matrix.of fun _ _ : Fin 1 => X.hh (Sum.inl 0))), fun FP FB M hM FQ τ hτ => ?_⟩
  have := h2 FP FQ FB (fun _ => M) (fun a => a.elim0)
    ⟨fun a => by obtain rfl := Subsingleton.elim a 0; exact hM, fun a => a.elim0⟩ τ hτ
  rw [idx_zero] at this
  simpa using this

end GlobalTheory.FlatCM.Model

end
