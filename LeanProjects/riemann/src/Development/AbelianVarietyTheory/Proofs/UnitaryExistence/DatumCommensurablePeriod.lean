import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SymplecticGenerators.SymplecticCharacters.InversionStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Signature
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Matrix nonZeroDivisors
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G.Key ReciprocityTheory.ChartRestriction.G.Key.Chi

namespace GlobalTheory.TwoLattices

open Module

theorem natAbs_det_gram {M κ : Type} [AddCommGroup M] [Fintype κ] [DecidableEq κ] (b : Basis κ ℤ M)
    (B : LinearMap.BilinForm ℤ M) (hB : Function.Bijective B) :
    (Matrix.of fun i k => B (b i) (b k)).det.natAbs = 1 := by
  have h := LinearEquiv.isUnit_det (LinearEquiv.ofBijective B hB) b b.dualBasis
  have e : LinearMap.toMatrix b b.dualBasis (LinearEquiv.ofBijective B hB : M →ₗ[ℤ] _) =
      (Matrix.of fun i k => B (b i) (b k))ᵀ := by
    ext i k
    simp [LinearMap.toMatrix_apply]
  rw [e, Matrix.det_transpose] at h
  exact Int.isUnit_iff_natAbs_eq.mp h

theorem index_similitude {M M' : Type} [AddCommGroup M] [AddCommGroup M'] [Module.Free ℤ M] [Module.Finite ℤ M]
    [Module.Free ℤ M'] [Module.Finite ℤ M'] (B : LinearMap.BilinForm ℤ M) (B' : LinearMap.BilinForm ℤ M')
    (hB : Function.Bijective B) (hB' : Function.Bijective B') (j : M →+ M') (hj : Function.Injective j)
    (n N : ℕ) (hn : finrank ℤ M = n) (hn' : finrank ℤ M' = n)
    (h : ∀ a b, B' (j a) (j b) = (N : ℤ) ^ 2 * B a b) : j.range.index = N ^ n := by
  let b : Basis (Fin n) ℤ M := Module.finBasisOfFinrankEq ℤ M hn
  let b' : Basis (Fin n) ℤ M' := Module.finBasisOfFinrankEq ℤ M' hn'
  let bN : Basis (Fin n) ℤ j.range := b.map (AddMonoidHom.ofInjective hj).toIntLinearEquiv
  have hbN : ∀ i, (bN i : M') = j (b i) := fun i => rfl
  rw [AddSubgroup.index_eq_natAbs_det b' j.range bN, Basis.det_apply]
  set J := b'.toMatrix (fun i => (bN i : M')) with hJ
  have key : Jᵀ * (Matrix.of fun i k => B' (b' i) (b' k)) * J =
      ((N : ℤ) ^ 2) • Matrix.of fun i k => B (b i) (b k) := by
    ext i k
    have e1 : ∀ i, j (b i) = ∑ l, J l i • b' l := fun i => by
      rw [← hbN]
      exact (b'.sum_repr _).symm
    simp only [Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, ← h, e1, Matrix.mul_apply,
      Matrix.transpose_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
      Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have k2 := congrArg (fun X => X.det.natAbs) key
  simp only [Matrix.det_mul, Matrix.det_transpose, Matrix.det_smul, Int.natAbs_mul, natAbs_det_gram b B hB,
    natAbs_det_gram b' B' hB', _root_.mul_one, Int.natAbs_pow, Int.natAbs_natCast, Fintype.card_fin] at k2
  have : J.det.natAbs ^ 2 = (N ^ n) ^ 2 := by
    rw [sq, k2]; ring
  exact Nat.pow_left_injective (by norm_num) this

variable {E : Type} [Field E] [NumberField E]

theorem exists_mul_mem {M' V : Type} [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) (v : V) : ∃ N : ℕ, 0 < N ∧ ∃ b, φ' b = N • v := by
  have hv : v ∈ Submodule.span E (Set.range φ') := hs ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => obtain ⟨b, rfl⟩ := hx; exact ⟨1, one_pos, b, by simp⟩
  | zero => exact ⟨1, one_pos, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨N, hN, b, hb⟩ := hx
    obtain ⟨K, hK, c, hc⟩ := hy
    refine ⟨N * K, Nat.mul_pos hN hK, K • b + N • c, ?_⟩
    rw [map_add, map_nsmul, map_nsmul, hb, hc, smul_add, smul_smul, smul_smul, mul_comm K N]
  | smul e x _ hx =>
    obtain ⟨N, hN, b, hb⟩ := hx
    have halg : IsAlgebraic ℤ e :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr (Algebra.IsAlgebraic.isAlgebraic e)
    obtain ⟨m, s, hm, hs⟩ := halg.exists_nsmul_eq (S := 𝓞 E)
    refine ⟨m * N, Nat.mul_pos (Nat.pos_of_ne_zero hm) hN, s • b, ?_⟩
    rw [map_smul, hb, ← IsScalarTower.algebraMap_smul E s, ← hs, smul_assoc, smul_comm e N x, mul_smul]

theorem exists_mul_le {M M' V : Type} [AddCommGroup M] [Module (𝓞 E) M] [Module.Finite (𝓞 E) M]
    [AddCommGroup M'] [Module (𝓞 E) M'] [AddCommGroup V] [Module E V]
    [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V] (φ : M →ₗ[𝓞 E] V) (φ' : M' →ₗ[𝓞 E] V)
    (hs : Submodule.span E (Set.range φ') = ⊤) : ∃ N : ℕ, 0 < N ∧ ∀ a, ∃ b, φ' b = N • φ a := by
  obtain ⟨s, hS⟩ := Module.Finite.fg_top (R := 𝓞 E) (M := M)
  choose n hn c hc using exists_mul_mem φ' hs
  refine ⟨∏ x ∈ s, n (φ x), Finset.prod_pos fun x _ => hn _, fun a => ?_⟩
  have ha : a ∈ Submodule.span (𝓞 E) (s : Set M) := hS ▸ Submodule.mem_top
  induction ha using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem (fun x => n (φ x)) (Finset.mem_coe.mp hx)
    exact ⟨k • c (φ x), by rw [map_nsmul, hc, smul_smul, hk, mul_comm]⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b, hb⟩ := hx
    obtain ⟨d, hd⟩ := hy
    exact ⟨b + d, by rw [map_add, map_add, hb, hd, smul_add]⟩
  | smul e x _ hx =>
    obtain ⟨b, hb⟩ := hx
    exact ⟨e • b, by rw [map_smul, map_smul, hb, smul_comm]⟩

theorem exists_lift {R M M' V : Type} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup M'] [Module R M'] [AddCommGroup V] [Module R V] (φ : M →ₗ[R] V) (φ' : M' →ₗ[R] V)
    (hi : Function.Injective φ') (N : ℕ) (h : ∀ a, ∃ b, φ' b = N • φ a) :
    ∃ j : M →ₗ[R] M', ∀ a, φ' (j a) = N • φ a := by
  choose f hf using h
  refine ⟨⟨⟨f, fun x y => hi ?_⟩, fun c x => hi ?_⟩, hf⟩
  · rw [map_add, hf, hf, hf, map_add, smul_add]
  · simp only [RingHom.id_apply]
    rw [map_smul, hf, hf, map_smul, smul_comm]

theorem rank_of_lattice {M : Type} [AddCommGroup M] {g : ℕ} (P : M →+ (Fin g → ℂ)) (hi : Function.Injective P)
    (hd : DiscreteTopology P.range) (hs : Submodule.span ℝ (Set.range P) = ⊤) :
    finrank ℤ M = 2 * g := by
  let L : Submodule ℤ (Fin g → ℂ) := P.range.toIntSubmodule
  haveI : DiscreteTopology L := hd
  haveI : IsZLattice ℝ L := ⟨hs⟩
  have h := ZLattice.rank ℝ L
  have e : M ≃ₗ[ℤ] L := (AddMonoidHom.ofInjective hi).toIntLinearEquiv
  rw [e.finrank_eq, h, Module.finrank_pi_fintype]
  simp [mul_comm]

variable [IsCMField E]

theorem herm_nsmul {r : ℕ} (G : Matrix (Fin r) (Fin r) E) (N : ℕ) (x y : Fin r → E) :
    FD.herm G (N • x) (N • y) = (N : E) ^ 2 * FD.herm G x y := by
  simp only [FD.herm, FD.cc, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, Finset.mul_sum]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

theorem form_lift {H : Host E} (D D' : Datum H) {r : ℕ} (ξ : E) (Gm : Matrix (Fin r) (Fin r) E)
    (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E))
    (h : ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y)))
    (h' : ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y)))
    (N : ℕ) (j : D.La → D'.La) (hj : ∀ a, φ' (j a) = N • φ a) (a b : D.La) :
    D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b := by
  apply Int.cast_injective (α := ℚ)
  rw [h', hj, hj, herm_nsmul]
  push_cast
  rw [h, ← smul_eq_mul ((N : ℚ) ^ 2), ← map_smul]
  congr 1
  rw [Algebra.smul_def]
  simp only [map_pow, map_natCast]
  ring

theorem hermForm_real_smul {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (t : ℝ) (z w : Fin g → ℂ) :
    hermForm Hm ((t : ℂ) • z) ((t : ℂ) • w) = ((t ^ 2 : ℝ) : ℂ) * hermForm Hm z w := by
  simp only [hermForm, star_smul, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    Complex.star_def, Complex.conj_ofReal]
  push_cast
  ring

end GlobalTheory.TwoLattices

open GlobalTheory.TwoLattices in

theorem GlobalTheory.datum_commensurable_period :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (g : ℕ) (ty : Fin g → (E →+* ℂ)), FD.cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, FD.cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * FD.herm Gm (φ' x) (φ' y))) → ∀ P, IsPeriod D ty P → ∃ (N : ℕ) (j : D.La →ₗ[𝓞 E] D'.La) (j' : D'.La →ₗ[𝓞 E] D.La) (P' : D'.La →+ (Fin g → ℂ)), (0 < N ∧ (∀ a, j' (j a) = (N ^ 2) • a) ∧ (∀ a, j (j' a) = (N ^ 2) • a) ∧ (∀ a b, D'.EF (j a) (j b) = (N : ℤ) ^ 2 * D.EF a b) ∧ (∀ a b, D.EF (j' a) (j' b) = (N : ℤ) ^ 2 * D'.EF a b) ∧ Nat.card (D'.La ⧸ LinearMap.range j) = N ^ (2 * g)) ∧ IsPeriod D' ty P' ∧ (∀ a, P' (j a) = (N : ℂ) • P a) ∧ ∀ a, P (j' a) = (N : ℂ) • P' a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' g ty _ ⟨hi, hs, _, _, hE⟩ ⟨hi', hs', _, _, hE'⟩ P ⟨hPl, hPi, hPd, hPs, Hm, hH, hpos, hIm⟩
  haveI := D.fin
  haveI := D'.fin
  obtain ⟨N₁, hN₁, h₁⟩ := exists_mul_le φ φ' hs'
  obtain ⟨N₂, hN₂, h₂⟩ := exists_mul_le φ' φ hs
  set N := N₁ * N₂ with hNdef
  have hN : 0 < N := Nat.mul_pos hN₁ hN₂
  obtain ⟨j, hj⟩ := exists_lift φ φ' hi' N fun a => by
    obtain ⟨b, hb⟩ := h₁ a
    exact ⟨N₂ • b, by rw [map_nsmul, hb, smul_smul, mul_comm]⟩
  obtain ⟨j', hj'⟩ := exists_lift φ' φ hi N fun a => by
    obtain ⟨b, hb⟩ := h₂ a
    exact ⟨N₁ • b, by rw [map_nsmul, hb, smul_smul]⟩
  clear_value N
  have hNE : (N : E) ≠ 0 := by exact_mod_cast hN.ne'
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have c₁ : ∀ a, j' (j a) = (N ^ 2) • a := fun a => hi (by rw [hj', hj, map_nsmul, smul_smul, sq])
  have c₂ : ∀ a, j (j' a) = (N ^ 2) • a := fun a => hi' (by rw [hj, hj', map_nsmul, smul_smul, sq])
  have f₁ := form_lift D D' ξ Gm φ φ' hE hE' N j hj
  have f₂ := form_lift D' D ξ Gm φ' φ hE' hE N j' hj'
  have cancel : ∀ v w : Fin r → E, N • v = N • w → v = w := fun v w h => by
    rw [← Nat.cast_smul_eq_nsmul E, ← Nat.cast_smul_eq_nsmul E] at h
    exact smul_right_injective _ hNE h
  have ji : Function.Injective j := fun a b h => hi (cancel _ _ (by rw [← hj, ← hj, h]))
  have ji' : Function.Injective j' := fun a b h => hi' (cancel _ _ (by rw [← hj', ← hj', h]))
  let P' : D'.La →+ (Fin g → ℂ) :=
    { toFun := fun a => (N : ℂ)⁻¹ • P (j' a)
      map_zero' := by simp
      map_add' := fun a b => by simp only [map_add, smul_add] }
  have hP' : ∀ a, P' a = (N : ℂ)⁻¹ • P (j' a) := fun _ => rfl
  have p₂ : ∀ a, P (j' a) = (N : ℂ) • P' a := fun a => by
    rw [hP', smul_smul, mul_inv_cancel₀ hNC, one_smul]
  have p₁ : ∀ a, P' (j a) = (N : ℂ) • P a := fun a => by
    rw [hP', c₁, map_nsmul, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    push_cast
    field_simp
  have P'i : Function.Injective P' := fun a b h => ji' (hPi (by rw [p₂, p₂, h]))
  have P'd : DiscreteTopology P'.range := by
    let f : P'.range → P.range := fun x => ⟨(N : ℂ) • (x : Fin g → ℂ), by
      obtain ⟨a, ha⟩ := x.2
      exact ⟨j' a, by rw [p₂, ha]⟩⟩
    refine DiscreteTopology.of_continuous_injective (f := f) ?_ ?_
    · exact Continuous.subtype_mk (continuous_subtype_val.const_smul (N : ℂ)) _
    · intro x y h
      exact Subtype.ext (smul_right_injective _ hNC (congrArg Subtype.val h))
  have P's : Submodule.span ℝ (Set.range P') = ⊤ := by
    rw [eq_top_iff, ← hPs, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    have : P a = (N : ℝ)⁻¹ • P' (j a) := by
      rw [p₁]
      ext i
      simp only [Pi.smul_apply, Complex.real_smul, smul_eq_mul]
      push_cast
      field_simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hper : IsPeriod D' ty P' := by
    refine ⟨fun a x i => ?_, P'i, P'd, P's, Hm, hH, hpos, fun x y => ?_⟩
    · simp only [hP', map_smul, Pi.smul_apply, hPl, smul_eq_mul]
      ring
    · have e : ((N : ℂ))⁻¹ = (((N : ℝ)⁻¹ : ℝ) : ℂ) := by push_cast; rfl
      rw [hP', hP', e, hermForm_real_smul, Complex.im_ofReal_mul, hIm, f₂]
      push_cast
      field_simp
  haveI : Module.Finite ℤ D.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.Finite ℤ D'.La := Module.Finite.trans (𝓞 E) _
  haveI : Module.IsTorsionFree ℤ D.La := hPi.moduleIsTorsionFree P (fun c x => map_zsmul P c x)
  haveI : Module.IsTorsionFree ℤ D'.La := P'i.moduleIsTorsionFree P' (fun c x => map_zsmul P' c x)
  refine ⟨N, j, j', P', ⟨hN, c₁, c₂, f₁, f₂, ?_⟩, hper, p₁, p₂⟩
  exact index_similitude D.EF D'.EF D.unimod D'.unimod j.toAddMonoidHom ji (2 * g) N
    (rank_of_lattice P hPi hPd hPs) (rank_of_lattice P' P'i P'd P's) f₁
