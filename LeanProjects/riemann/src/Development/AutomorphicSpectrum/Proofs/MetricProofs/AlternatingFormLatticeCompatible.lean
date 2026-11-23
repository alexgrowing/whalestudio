import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntEmbInjective
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BlockGLSupportedMemMirabolicSupported
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume GroundTheory.Automorphic GlobalTheory.CompanionTheory.Ar.Cusp.Dict
open scoped ENNReal InnerProductSpace
open scoped ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.Dict

theorem relIndex_ne_zero_of_nsmul_mem {W : Type*} [AddCommGroup W] (L G : AddSubgroup W) [AddGroup.FG L] {D : ℕ} (hD : D ≠ 0)
    (hinj : ∀ y : W, D • y = 0 → y = 0) (hG : ∀ y ∈ G, D • y ∈ L) : L.relIndex G ≠ 0 := by
  let f : G →+ L :=
    { toFun := fun y => ⟨D • (y : W), hG y y.2⟩
      map_zero' := by ext; simp
      map_add' := fun a b => by ext; simp [smul_add] }
  have hf : Function.Injective f := by
    refine (injective_iff_map_eq_zero f).2 fun a ha => ?_
    have : D • (a : W) = 0 := congrArg Subtype.val ha
    exact Subtype.ext (hinj _ this)
  haveI : Module.Finite ℤ L := Module.Finite.iff_addGroup_fg.2 inferInstance
  haveI : Module.Finite ℤ G := Module.Finite.of_injective f.toIntLinearMap hf
  haveI : AddGroup.FG G := Module.Finite.iff_addGroup_fg.1 inferInstance
  haveI : Finite (G ⧸ L.addSubgroupOf G) := by
    refine AddCommGroup.finite_of_fg_torsion _ ?_
    intro q
    induction q using QuotientAddGroup.induction_on with
    | H y =>
      refine isOfFinAddOrder_iff_nsmul_eq_zero.2 ⟨D, Nat.pos_of_ne_zero hD, ?_⟩
      rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
      simpa using hG y y.2
  exact AddSubgroup.index_ne_zero_of_finite

theorem latEmb_relIndex_dual_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Λ : Type) [AddCommGroup Λ] [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (N : ℕ) (e : Λ →+ (Fin N → E)), Function.Injective e → ∀ form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ, Function.Bijective form → ∀ B : LinearMap.BilinForm ℚ (Fin N → E), (∀ x y, B (e x) (e y) = ((form x y : ℤ) : ℚ)) → (∀ u v, B u v = - B v u) → (∀ u, (∀ v, B v u = 0) → u = 0) → (∀ v : Fin N → E, ∃ (k : ℕ) (x : Λ), k ≠ 0 ∧ e x = k • v) → ∀ (h : HermitianForm (maximalRealSubfield E) E (Fin N → E)) (m : ℕ), m ≠ 0 → (∀ (a : E) u v, Algebra.trace ℚ E (a * (((m : E) * (H.rt : E))⁻¹ * h.toSesq v u)) = B (a • u) v) → e.range.relIndex (dualLattice h e.range) ≠ 0 := by
  intro E _ _ _ H Λ _ _ _ N e he form hform B hB hskew hnd hspan h m hm htr
  classical
  have hd0 : (H.d : E) ≠ 0 := Nat.cast_ne_zero.2 H.d_prime.ne_zero
  have hm0 : (m : E) ≠ 0 := Nat.cast_ne_zero.2 hm
  have hrtsq : (H.rt : E) ^ 2 = -(H.d : E) := by
    have := congrArg (fun a : 𝓞 E => (a : E)) H.rt_sq
    simpa using this
  have hrt0 : (H.rt : E) ≠ 0 := by
    intro h0
    rw [h0] at hrtsq
    exact hd0 (by simpa using hrtsq.symm)
  have hinv : ((m * H.d : ℕ) : E) * ((m : E) * (H.rt : E))⁻¹ = -(H.rt : E) := by
    push_cast
    field_simp
    linear_combination hrtsq
  have key : ∀ y ∈ dualLattice h e.range, ∀ x, ∃ n : ℤ, (n : ℚ) = ((m * H.d : ℕ) : ℚ) * B (e x) y := by
    intro y hy x
    have hint : IsIntegral ℤ (h.toSesq y (e x)) := hy (e x) ⟨x, rfl⟩
    have ht := htr 1 (e x) y
    rw [one_smul, one_mul] at ht
    have h2 : ((m * H.d : ℕ) : ℚ) * B (e x) y
        = Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x)) := by
      rw [← ht, ← hinv, mul_assoc, ← smul_eq_mul (a := ((m * H.d : ℕ) : ℚ)), ← map_smul]
      congr 1
      rw [Algebra.smul_def]
      simp
    have hrti : IsIntegral ℤ (-(H.rt : E)) := (H.rt.2).neg
    have h3 : IsIntegral ℤ (Algebra.trace ℚ E (-(H.rt : E) * h.toSesq y (e x))) :=
      Algebra.isIntegral_trace (hrti.mul hint)
    obtain ⟨n, hn⟩ := IsIntegrallyClosed.isIntegral_iff.1 h3
    exact ⟨n, by rw [h2, ← hn]; simp⟩
  have hDy : ∀ y ∈ dualLattice h e.range, (m * H.d) • y ∈ e.range := by
    intro y hy
    choose n hn using key y hy
    have hadd : ∀ a b, n (a + b) = n a + n b := by
      intro a b
      have : ((n (a + b) : ℤ) : ℚ) = ((n a + n b : ℤ) : ℚ) := by
        push_cast
        rw [hn, hn, hn, map_add, map_add, LinearMap.add_apply, mul_add]
      exact_mod_cast this
    let φ : Λ →ₗ[ℤ] ℤ := (AddMonoidHom.mk' n hadd).toIntLinearMap
    obtain ⟨z, hz⟩ := hform.2 φ
    have hzx : ∀ x, form z x = n x := fun x => by rw [hz]; rfl
    have h0 : ∀ x, B (e x) ((m * H.d) • y + e z) = 0 := by
      intro x
      have h1 : B (e x) (e z) = -((n x : ℤ) : ℚ) := by
        rw [hskew, hB, hzx]
      rw [map_add, map_nsmul, h1, hn, nsmul_eq_mul]
      ring
    have h1 : ∀ v, B v ((m * H.d) • y + e z) = 0 := by
      intro v
      obtain ⟨k, x, hk, hx⟩ := hspan v
      have h2 := h0 x
      rw [hx, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at h2
      exact (mul_eq_zero.1 h2).resolve_left (Nat.cast_ne_zero.2 hk)
    have h2 := hnd _ h1
    exact ⟨-z, by rw [map_neg]; exact (eq_neg_of_add_eq_zero_left h2).symm⟩
  haveI : AddGroup.FG e.range := by
    haveI : Module.Finite ℤ e.range :=
      Module.Finite.of_surjective e.rangeRestrict.toIntLinearMap e.rangeRestrict_surjective
    exact Module.Finite.iff_addGroup_fg.1 inferInstance
  refine relIndex_ne_zero_of_nsmul_mem _ _ (D := m * H.d) (mul_ne_zero hm H.d_prime.ne_zero) ?_ hDy
  intro y hy
  funext i
  have h1 := congrFun hy i
  simp only [Pi.smul_apply, Pi.zero_apply] at h1
  rw [nsmul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (mul_ne_zero hm H.d_prime.ne_zero))

end GlobalTheory.CompanionTheory.Ar.Cusp.Dict
