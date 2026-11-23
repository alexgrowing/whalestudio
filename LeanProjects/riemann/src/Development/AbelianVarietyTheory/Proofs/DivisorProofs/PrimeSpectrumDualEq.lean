import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal

set_option autoImplicit false
noncomputable section
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

theorem primeSpectrum_dual_eq (x y : PrimeSpectrum (DualNumber ℂ)) : x = y := by
  have h : ∀ z : PrimeSpectrum (DualNumber ℂ), ∀ a, a ∈ z.asIdeal ↔ a.fst = 0 := fun z a => by
    constructor
    · intro ha
      by_contra h0
      exact z.2.ne_top (z.asIdeal.eq_top_of_isUnit_mem ha (TrivSqZeroExt.isUnit_iff_isUnit_fst.2 (Ne.isUnit h0)))
    · intro ha
      refine z.2.mem_of_pow_mem 2 ?_
      rw [show a ^ 2 = 0 by ext <;> simp [pow_two, ha]]
      exact z.asIdeal.zero_mem
  ext a
  rw [h, h]

theorem isDiff_epsScale {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) {w : Fin g → ℂ}
    {v : epsR ℂ ⟶ A} (h : u.IsDiff w v) (c : ℂ) : u.IsDiff (c • w) (epsScale c ≫ v) := by
  intro U hU f
  have hU' : ⊤ ≤ v.left ⁻¹ᵁ U := fun x _ => by
    have := hU (Set.mem_univ x)
    have hx : (spMap (epsScaleR c)) x = x := primeSpectrum_dual_eq _ _
    change v.left ((spMap (epsScaleR c)) x) ∈ U at this
    rwa [hx] at this
  rw [map_smul, ← h U hU' f]
  have e : (epsScale c ≫ v).left.appLE U ⊤ hU = v.left.appLE U ⊤ hU' ≫ (spMap (epsScaleR c)).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE (spMap (epsScaleR c)) v.left U ⊤ ⊤ hU' le_rfl).symm
  have e2 := congrArg (fun k => k.hom ((v.left.appLE U ⊤ hU').hom f))
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (epsScaleR c)))
  rw [e]
  refine (congrArg TrivSqZeroExt.snd e2).trans ?_
  simp [epsScaleR]

section Ext

variable {E : Type} {V : Type*} [AddCommGroup E] [AddCommGroup V] [Module ℂ V] (L : AddSubgroup E)

theorem inv_smul_eq (Q : L →+ V) {x : E} {n m : ℕ} (hn : 0 < n) (hm : 0 < m) (h : n • x ∈ L) (h' : m • x ∈ L) :
    (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ = (m : ℂ)⁻¹ • Q ⟨m • x, h'⟩ := by
  have key : m • Q ⟨n • x, h⟩ = n • Q ⟨m • x, h'⟩ := by
    rw [← map_nsmul, ← map_nsmul]
    congr 1
    ext
    simp only [AddSubgroup.coe_nsmul]
    rw [smul_smul, smul_smul, mul_comm]
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have key' : (m : ℂ) • Q ⟨n • x, h⟩ = (n : ℂ) • Q ⟨m • x, h'⟩ := by
    rw [Nat.cast_smul_eq_nsmul, Nat.cast_smul_eq_nsmul, key]
  calc (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ = ((n : ℂ)⁻¹ * (m : ℂ)⁻¹) • ((m : ℂ) • Q ⟨n • x, h⟩) := by
        rw [smul_smul]; congr 1; field_simp
    _ = ((n : ℂ)⁻¹ * (m : ℂ)⁻¹) • ((n : ℂ) • Q ⟨m • x, h'⟩) := by rw [key']
    _ = (m : ℂ)⁻¹ • Q ⟨m • x, h'⟩ := by rw [smul_smul]; congr 1; field_simp

theorem exists_ext (hfull : ∀ x : E, ∃ n : ℕ, 0 < n ∧ n • x ∈ L) (Q : L →+ V) :
    ∃ P : E →+ V, ∀ (x : E) (n : ℕ) (hn : 0 < n) (h : n • x ∈ L), P x = (n : ℂ)⁻¹ • Q ⟨n • x, h⟩ := by
  choose N hN hNL using hfull
  let P : E →+ V :=
    { toFun := fun x => (N x : ℂ)⁻¹ • Q ⟨N x • x, hNL x⟩
      map_zero' := by
        rw [show (⟨N 0 • (0 : E), hNL 0⟩ : L) = 0 from Subtype.ext (by simp), map_zero, smul_zero]
      map_add' := fun x y => by
        have hxy : (N x * N y) • (x + y) ∈ L := by
          rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
          exact add_mem (L.nsmul_mem (hNL x) _) (L.nsmul_mem (hNL y) _)
        have hx : (N x * N y) • x ∈ L := by rw [mul_comm, mul_smul]; exact L.nsmul_mem (hNL x) _
        have hy : (N x * N y) • y ∈ L := by rw [mul_smul]; exact L.nsmul_mem (hNL y) _
        have hpos : 0 < N x * N y := Nat.mul_pos (hN x) (hN y)
        rw [inv_smul_eq L Q (hN _) hpos _ hxy, inv_smul_eq L Q (hN _) hpos _ hx,
          inv_smul_eq L Q (hN _) hpos _ hy, ← smul_add, ← map_add]
        congr 2
        ext
        simp [smul_add] }
  exact ⟨P, fun x n hn h => inv_smul_eq L Q (hN x) hn (hNL x) h⟩

end Ext

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

theorem exists_nsmul_mem {E : Type} [AddCommGroup E] [Module ℚ E] [FiniteDimensional ℚ E] {g : ℕ} (L : AddSubgroup E)
    (ι : E →ₗ[ℚ] (Fin g → ℂ)) (hdim : Module.finrank ℚ E ≤ 2 * g)
    (hsp : Submodule.span ℝ (ι '' (L : Set E)) = ⊤) (x : E) : ∃ n : ℕ, 0 < n ∧ n • x ∈ L := by
  set W := Submodule.span ℚ (L : Set E)
  let b := Module.finBasis ℚ W
  have hsub : ι '' (L : Set E) ⊆ Submodule.span ℝ (Set.range fun k => ι (b k)) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyW : y ∈ W := Submodule.subset_span hy
    have e : (⟨y, hyW⟩ : W) = ∑ k, b.repr ⟨y, hyW⟩ k • b k := (b.sum_repr _).symm
    have e' : y = ∑ k, b.repr ⟨y, hyW⟩ k • (b k : E) := by
      have := congrArg Subtype.val e
      rw [Submodule.coe_sum] at this
      exact this.trans (Finset.sum_congr rfl fun k _ => Submodule.coe_smul _ _)
    rw [e', map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul, ← algebraMap_smul ℝ]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  have htop : Submodule.span ℝ (Set.range fun k => ι (b k)) = ⊤ :=
    top_unique (hsp ▸ Submodule.span_le.2 hsub)
  have h1 : Module.finrank ℝ (Fin g → ℂ) ≤ Module.finrank ℚ W := by
    have := finrank_span_le_card (R := ℝ) (Set.range fun k => ι (b k))
    rw [htop, finrank_top] at this
    refine this.trans ?_
    refine (Set.toFinset_card _).le.trans ?_
    exact (Fintype.card_range_le _).trans (by simp)
  have h2 : Module.finrank ℝ (Fin g → ℂ) = 2 * g := by
    rw [Module.finrank_pi_fintype, Complex.finrank_real_complex]; simp [mul_comm]
  have hW : W = ⊤ := Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) (by omega))
  have hx : x ∈ W := hW ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem y hy => exact ⟨1, one_pos, by simpa using hy⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, hn, hny⟩ := hy
    obtain ⟨m, hm, hmz⟩ := hz
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add, mul_comm, mul_smul, mul_comm, mul_smul]
    exact add_mem (L.nsmul_mem hny _) (L.nsmul_mem hmz _)
  | smul q y _ hy =>
    obtain ⟨n, hn, hny⟩ := hy
    refine ⟨q.den * n, Nat.mul_pos q.den_pos hn, ?_⟩
    have : (q.den * n) • (q • y) = q.num • (n • y) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, smul_smul, ← Nat.cast_smul_eq_nsmul ℚ n y, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
      congr 1
      push_cast
      rw [mul_comm (q.den : ℚ) n, mul_assoc, Rat.den_mul_eq_num, mul_comm]
    rw [this]
    exact L.zsmul_mem hny _

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

end GlobalTheory.PeriodLattice

namespace GlobalTheory.PeriodLattice

open GlobalTheory.GrpTangent

end GlobalTheory.PeriodLattice
