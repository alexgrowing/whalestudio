import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqTopOfSpanImage
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HerrAAndNatural
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeGaloisTrivialModUniformizer
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fKsOntoUpToPow
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeHeightsFromHodgeJumpsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemWachNOfMapMemSaturatedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachNCokernelKilledByPowerStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachIntegralComplexCocycleClassFiniteStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.H1fClassWachPairJumpsStatement

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.DefectTorsion

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n)

theorem isUnit_φ (a : LetA O n) (ha : IsUnit (algebraMap (LetA O n) W.EE a)) :
    IsUnit (algebraMap (LetA O n) W.EE (W.φA a)) := by
  show IsUnit (algebraMap (LetA O n) W.EE (letφ W.φ₀ a))
  rw [← W.φE_ext a]
  exact ha.map W.φE

theorem isUnit_X : IsUnit (algebraMap (LetA O n) W.EE W.X) := by
  show IsUnit (algebraMap (LetA O n) W.EE ((W.φA ^ (W.s - 1)) letπ))
  induction W.s - 1 with
  | zero => exact W.EE_π
  | succ k ih => rw [pow_succ']; exact isUnit_φ W _ ih

private theorem letπ_dvd_phiA_of_dvd (a : LetA O n) (h : (letπ : LetA O n) ∣ a) :
    (letπ : LetA O n) ∣ W.φA a := by
  obtain ⟨c, rfl⟩ := h
  rw [map_mul]
  refine Dvd.dvd.mul_right ⟨fun _ => W.q₀, ?_⟩ _
  funext i
  show W.φ₀ PowerSeries.X = PowerSeries.X * W.q₀
  exact W.φ₀_X

theorem π_dvd_X : (letπ : LetA O n) ∣ W.X := by
  show (letπ : LetA O n) ∣ (W.φA ^ (W.s - 1)) letπ
  induction W.s - 1 with
  | zero => exact dvd_refl _
  | succ k ih => rw [pow_succ']; exact letπ_dvd_phiA_of_dvd W _ ih

theorem isUnit_of_sub_one (w : LetA O n) (hw : w - 1 ∈ Ideal.span {W.X}) : IsUnit w := by
  obtain ⟨c, hc⟩ := (π_dvd_X W).trans (Ideal.mem_span_singleton.1 hw)
  rw [Pi.isUnit_iff]
  intro i
  have h1 : w i - 1 = PowerSeries.X * c i := by
    have := congrFun hc i
    simpa only [Pi.sub_apply, Pi.one_apply, Pi.mul_apply, letπ] using this
  have h2 : w i = 1 + PowerSeries.X * c i := by rw [← h1]; ring
  rw [PowerSeries.isUnit_iff_constantCoeff, h2]
  simp

theorem exists_X_smul (T : LocLat G Qp LL O) (x : W.DD T) : ∃ y, W.X • y = x := by
  obtain ⟨u, hu⟩ := isUnit_X W
  refine ⟨(↑u⁻¹ : W.EE) • x, ?_⟩
  rw [← algebraMap_smul W.EE W.X ((↑u⁻¹ : W.EE) • x), smul_smul, ← hu, Units.mul_inv, one_smul]

theorem X_smul_inj (T : LocLat G Qp LL O) {x y : W.DD T} (h : W.X • x = W.X • y) : x = y := by
  obtain ⟨u, hu⟩ := isUnit_X W
  rw [← algebraMap_smul W.EE W.X x, ← algebraMap_smul W.EE W.X y, ← hu] at h
  have h' := congrArg (fun z => (↑u⁻¹ : W.EE) • z) h
  simpa only [smul_smul, Units.inv_mul, one_smul] using h'

theorem mem_aN (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    x ∈ aN W T a ↔ ∃ y ∈ W.N T, a • y = x := by
  simp only [aN, smulA, Submodule.mem_map, LinearMap.smul_apply, LinearMap.id_apply]

theorem mem_invN (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    x ∈ invN W T a ↔ a • x ∈ W.N T := by
  simp only [invN, smulA, Submodule.mem_comap, LinearMap.smul_apply, LinearMap.id_apply]

theorem map_smulA {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) (a : LetA O n) (x : W.DD T) :
    W.map f (a • x) = a • W.map f x := by
  rw [← algebraMap_smul W.EE a x, (W.map f).map_smul, algebraMap_smul]

theorem φD_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.φD T (a • x) = W.φA a • W.φD T x := by
  rw [← algebraMap_smul W.EE a x, W.φD_smul, W.φE_ext, algebraMap_smul]
  rfl

theorem γ_smulA (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) :
    W.γ T (a • x) = W.γA W.gam a • W.γ T x := by
  show W.γD T W.gam (a • x) = W.γA W.gam a • W.γD T W.gam x
  rw [← algebraMap_smul W.EE a x, W.γD_smul, W.γE_ext, algebraMap_smul]
  rfl

theorem mem_Z1D (T : LocLat G Qp LL O) (y z : W.DD T) :
    (y, z) ∈ W.divisibleCocycles T ↔ (W.γ T y - y) - (W.φD T z - z) = 0 := by
  unfold LocWach.divisibleCocycles herrCocycles
  rw [LinearMap.mem_ker, LinearMap.coprod_apply, LinearMap.neg_apply, ← sub_eq_add_neg]
  exact Iff.rfl

theorem mem_X_invN (T : LocLat G Qp LL O) (a : LetA O n) (x : W.DD T) (hx : a • x ∈ aN W T W.X) :
    x ∈ (invN W T a).map (smulA W T W.X) := by
  obtain ⟨y, rfl⟩ := exists_X_smul W T x
  rw [Submodule.mem_map]
  refine ⟨y, ?_, rfl⟩
  rw [mem_invN]
  obtain ⟨m, hm, hmx⟩ := (mem_aN W T W.X _).1 hx
  rw [smul_comm a W.X y] at hmx
  exact (X_smul_inj W T hmx) ▸ hm

private theorem sum_letE_eq_one' [NeZero n] : ∑ j : ZMod n, (letE j : LetA O n) = 1 := by
  funext i
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem φ_mem [NeZero n] (T : LocLat G Qp LL O) (M h : ZMod n → ℕ) (h5 : p5 W T M h) (x : W.DD T)
    (hx : x ∈ W.N T) : W.Q ^ mx M • W.φD T x ∈ W.N T := by
  have hx' : x = ∑ j, (letE j : LetA O n) • x := by
    rw [← Finset.sum_smul, sum_letE_eq_one', one_smul]
  rw [hx', map_sum, Finset.smul_sum]
  refine Submodule.sum_mem _ (fun j _ => ?_)
  have hj : (letE j : LetA O n) • x ∈ W.Nl T (j + 1 - 1) := by
    rw [add_sub_cancel_right]
    show (letE j : LetA O n) • x ∈ Submodule.map ((letE j : LetA O n) • LinearMap.id) (W.N T)
    exact Submodule.mem_map_of_mem hx
  have hle : M (j + 1) ≤ mx M := le_ciSup (Finite.bddAbove_range M) (j + 1)
  have h1 := h5.1 (j + 1) _ hj
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul]
  exact Submodule.smul_mem _ _ h1

private theorem phiA_X_eq_X_mul_Q : W.φA W.X = W.X * W.Q := by
  have hπ : W.φA letπ = letπ * W.q := by
    funext i
    show W.φ₀ PowerSeries.X = PowerSeries.X * W.q₀
    exact W.φ₀_X
  show (W.φA * W.φA ^ (W.s - 1)) letπ = (W.φA ^ (W.s - 1)) letπ * (W.φA ^ (W.s - 1)) W.q
  rw [← pow_succ', pow_succ]
  show (W.φA ^ (W.s - 1)) (W.φA letπ) = _
  rw [hπ, map_mul]

theorem differential_one_mem_scaled_lattice (T : LocLat G Qp LL O) (M : ℕ) (h2 : p2 W T)
    (hφ : ∀ x ∈ W.N T, W.Q ^ M • W.φD T x ∈ W.N T)
    (hQ : ∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X})
    (y z : W.DD T) (hy : y ∈ invN W T (W.Q ^ M)) (hz : z ∈ aN W T W.X) :
    W.Q ^ M • ((W.γ T y - y) - (W.φD T z - z)) ∈ aN W T W.X := by
  obtain ⟨w, hw, hw1⟩ := hQ
  obtain ⟨u, rfl⟩ := isUnit_of_sub_one W w hw1
  have hm : W.Q ^ M • y ∈ W.N T := (mem_invN W T _ y).1 hy
  obtain ⟨m', hm', rfl⟩ := (mem_aN W T W.X z).1 hz
  have hA : W.Q ^ M • W.γ T y = (↑(u⁻¹ ^ M) : LetA O n) • W.γ T (W.Q ^ M • y) := by
    rw [γ_smulA, map_pow, hw, mul_pow, ← smul_smul, smul_smul (↑(u⁻¹ ^ M) : LetA O n),
      Units.val_pow_eq_pow_val, ← mul_pow, Units.inv_mul, one_pow, one_smul]
  have hX1 : W.X ∣ (↑u⁻¹ : LetA O n) - 1 := by
    have e : (↑u⁻¹ : LetA O n) - 1 = -(↑u⁻¹ : LetA O n) * (↑u - 1) := by
      linear_combination (Units.inv_mul u)
    rw [e]
    exact Dvd.dvd.mul_left (Ideal.mem_span_singleton.1 hw1) _
  have hXc : W.X ∣ (↑(u⁻¹ ^ M) : LetA O n) - 1 := by
    rw [Units.val_pow_eq_pow_val]
    have h3 := sub_dvd_pow_sub_pow ((↑u⁻¹ : LetA O n)) 1 M
    rw [one_pow] at h3
    exact hX1.trans h3
  obtain ⟨c, hc⟩ := hXc
  rw [smul_sub]
  refine Submodule.sub_mem _ ?_ ?_
  · have e : W.Q ^ M • (W.γ T y - y) = (↑(u⁻¹ ^ M) : LetA O n) • (W.γ T (W.Q ^ M • y) - W.Q ^ M • y)
        + (W.X * c) • (W.Q ^ M • y) := by
      rw [← hc, smul_sub, hA, sub_smul, one_smul, smul_sub]
      abel
    rw [e]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (h2.2.2 _ hm)) ?_
    rw [mul_smul]
    exact (mem_aN W T W.X _).2 ⟨_, Submodule.smul_mem _ c hm, rfl⟩
  · rw [smul_sub]
    refine Submodule.sub_mem _ ?_ ?_
    · rw [φD_smulA, phiA_X_eq_X_mul_Q W]
      refine (mem_aN W T W.X _).2 ⟨W.Q • (W.Q ^ M • W.φD T m'), Submodule.smul_mem _ _ (hφ m' hm'), ?_⟩
      simp only [smul_smul]
      congr 1
      ring
    · exact (mem_aN W T W.X _).2 ⟨W.Q ^ M • m', Submodule.smul_mem _ _ hm', smul_comm _ _ _⟩

variable {T₀ T₁ T₂ : LocLat G Qp LL O} (ι : LatHom T₀.L T₁.L) (π : LatHom T₁.L T₂.L)

theorem aN_sat (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (x : W.DD T₀)
    (hx : W.map ι x ∈ aN W T₁ W.X) : x ∈ aN W T₀ W.X := by
  obtain ⟨y, rfl⟩ := exists_X_smul W T₀ x
  obtain ⟨m, hm, hmx⟩ := (mem_aN W T₁ W.X _).1 hx
  rw [map_smulA] at hmx
  have e := X_smul_inj W T₁ hmx
  exact (mem_aN W T₀ W.X _).2 ⟨y, hsat y (e ▸ hm), rfl⟩

set_option maxHeartbeats 1000000 in
private theorem lift_multiple_lemma (l M : ℕ) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ)
    (hnat : W.ClNat) (h2 : p2 W T₁) (hφ : ∀ x ∈ W.N T₁, W.Q ^ M • W.φD T₁ x ∈ W.N T₁)
    (hc : p2c W T₂ M)
    (hcok : ∃ c : ℕ, ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : LetA O n) ^ c • z)
    (hrex : ∀ κ₂ ∈ H1fIntegralCyclotomicLayer W T₂, ∃ (c : ℕ), ∃ κ₁ ∈ H1fIntegralCyclotomicLayer W T₁,
      (resHom π W.GKs).H1map κ₁ = (l ^ c : ℕ) • κ₂)
    (hc3 : ∀ κ ∈ H1fIntegralCyclotomicLayer W T₁, ∃ (c : ℕ) (y z : W.DD T₁) (hyz : (y, z) ∈ W.divisibleCocycles T₁),
      y ∈ invN W T₁ (W.Q ^ M) ∧ z ∈ aN W T₁ W.X ∧ W.cl T₁ ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ)
    (y₂ z₂ : W.DD T₂) (hy₂ : y₂ ∈ invN W T₂ (W.Q ^ M)) (hz₂ : z₂ ∈ aN W T₂ W.X)
    (hyz₂ : (y₂, z₂) ∈ W.divisibleCocycles T₂) :
    ∃ (k : ℕ) (y z : W.DD T₁), (y, z) ∈ W.divisibleCocycles T₁ ∧ y ∈ invN W T₁ (W.Q ^ M) ∧ z ∈ aN W T₁ W.X ∧
      W.map π y = (l ^ k : ℕ) • y₂ ∧ W.map π z = (l ^ k : ℕ) • z₂ := by
  obtain ⟨-, hc'⟩ := hc
  have mγ : ∀ {S S' : LocLat G Qp LL O} (f : LatHom S.L S'.L) (x : W.DD S),
      W.map f (W.γ S x) = W.γ S' (W.map f x) := fun f x => W.map_γ f W.gam x
  have mφ : ∀ {S S' : LocLat G Qp LL O} (f : LatHom S.L S'.L) (x : W.DD S),
      W.map f (W.φD S x) = W.φD S' (W.map f x) := fun f x => W.map_φ f x
  obtain ⟨hκ₂, -⟩ := hc' y₂ z₂ hy₂ hz₂ hyz₂
  obtain ⟨c, κ₁, hκ₁, hres⟩ := hrex _ hκ₂
  obtain ⟨c', y, z, hyz, hy, hz, hcl⟩ := hc3 κ₁ hκ₁
  obtain ⟨c'', hcok'⟩ := hcok
  have hyz' : (W.map π y, W.map π z) ∈ W.divisibleCocycles T₂ := by
    rw [mem_Z1D]
    have h0 := (mem_Z1D W T₁ y z).1 hyz
    rw [← mγ, ← mφ, ← map_sub, ← map_sub, ← map_sub, h0, map_zero]
  have hnat' := hnat π ⟨(y, z), hyz⟩ ⟨(W.map π y, W.map π z), hyz'⟩ rfl
  have hD : (W.map π y - (l ^ c' * l ^ c) • y₂, W.map π z - (l ^ c' * l ^ c) • z₂) ∈ W.divisibleCocycles T₂ := by
    have h := Submodule.sub_mem _ hyz' (Submodule.smul_of_tower_mem _ (l ^ c' * l ^ c) hyz₂)
    rwa [Prod.smul_mk, Prod.mk_sub_mk] at h
  have hcl0 : W.cl T₂ ⟨(W.map π y - (l ^ c' * l ^ c) • y₂, W.map π z - (l ^ c' * l ^ c) • z₂), hD⟩ = 0 := by
    have e2 : W.cl T₂ ⟨(W.map π y - (l ^ c' * l ^ c) • y₂, W.map π z - (l ^ c' * l ^ c) • z₂), hD⟩ =
        W.cl T₂ ⟨(W.map π y, W.map π z), hyz'⟩ - (l ^ c' * l ^ c) • W.cl T₂ ⟨(y₂, z₂), hyz₂⟩ := by
      rw [← map_nsmul, ← map_sub]
      congr 1
    have e3 : W.cl T₂ ⟨(W.map π y, W.map π z), hyz'⟩ = (l ^ c' * l ^ c) • W.cl T₂ ⟨(y₂, z₂), hyz₂⟩ := by
      have h1 : W.cl T₂ ⟨(W.map π y, W.map π z), hyz'⟩ =
          (resHom π W.GKs).H1map (W.cl T₁ ⟨(y, z), hyz⟩) := hnat'.symm
      rw [h1, hcl, map_nsmul, hres, smul_smul]
    rw [e2, e3, sub_self]
  have hyD : W.map π y - (l ^ c' * l ^ c) • y₂ ∈ invN W T₂ (W.Q ^ M) := by
    rw [mem_invN, smul_sub, ← map_smulA, smul_comm (W.Q ^ M) (l ^ c' * l ^ c)]
    exact Submodule.sub_mem _ (W.map_N π c₁ c₂ _ ((mem_invN W T₁ _ _).1 hy))
      (Submodule.smul_of_tower_mem _ _ ((mem_invN W T₂ _ _).1 hy₂))
  have hπz : W.map π z ∈ aN W T₂ W.X := by
    obtain ⟨m, hm, rfl⟩ := (mem_aN W T₁ W.X z).1 hz
    exact (mem_aN W T₂ W.X _).2 ⟨_, W.map_N π c₁ c₂ _ hm, (map_smulA W π _ _).symm⟩
  have hzD : W.map π z - (l ^ c' * l ^ c) • z₂ ∈ aN W T₂ W.X :=
    Submodule.sub_mem _ hπz (Submodule.smul_of_tower_mem _ _ hz₂)
  obtain ⟨m, hm, hym, hzm⟩ := (hc' _ _ hyD hzD hD).2 hcl0
  obtain ⟨m₁, hm₁, hπm₁⟩ := hcok' m hm
  rw [← Nat.cast_pow, Nat.cast_smul_eq_nsmul] at hπm₁
  refine ⟨c'' + (c' + c), (l ^ c'' : ℕ) • y - (W.φD T₁ m₁ - m₁), (l ^ c'' : ℕ) • z - (W.γ T₁ m₁ - m₁),
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_Z1D]
    have h0 := (mem_Z1D W T₁ y z).1 hyz
    have hc0 : W.φD T₁ (W.γ T₁ m₁) = W.γ T₁ (W.φD T₁ m₁) := W.φγ_comm T₁ W.gam m₁
    have e0 : W.γ T₁ y = y + (W.φD T₁ z - z) := by
      rw [← sub_eq_zero, ← h0]
      abel
    simp only [map_sub, map_nsmul, hc0, e0]
    simp only [smul_add, smul_sub]
    abel
  · rw [mem_invN, smul_sub, smul_sub, smul_comm (W.Q ^ M) (l ^ c'')]
    exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ ((mem_invN W T₁ _ _).1 hy))
      (Submodule.sub_mem _ (hφ m₁ hm₁) (Submodule.smul_mem _ _ hm₁))
  · exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hz) (h2.2.2 m₁ hm₁)
  · simp only [map_sub, map_nsmul, mφ, hπm₁]
    rw [← smul_sub, ← smul_sub, ← hym, sub_sub_cancel, smul_smul, pow_add, pow_add]
  · simp only [map_sub, map_nsmul, mγ, hπm₁]
    rw [← smul_sub, ← smul_sub, ← hzm, sub_sub_cancel, smul_smul, pow_add, pow_add]

theorem lift_multiple (l M : ℕ) (c₁ : IsCrys PD T₁.ρ) (c₂ : IsCrys PD T₂.ρ)
    (hnat : W.ClNat) (h2 : p2 W T₁) (hφ : ∀ x ∈ W.N T₁, W.Q ^ M • W.φD T₁ x ∈ W.N T₁)
    (hc : p2c W T₂ M)
    (hcok : ∃ c : ℕ, ∀ z ∈ W.N T₂, ∃ y ∈ W.N T₁, W.map π y = ((l : ℕ) : LetA O n) ^ c • z)
    (hrex : ∀ κ₂ ∈ H1fIntegralCyclotomicLayer W T₂, ∃ (c : ℕ), ∃ κ₁ ∈ H1fIntegralCyclotomicLayer W T₁,
      (resHom π W.GKs).H1map κ₁ = (l ^ c : ℕ) • κ₂)
    (hc3 : ∀ κ ∈ H1fIntegralCyclotomicLayer W T₁, ∃ (c : ℕ) (y z : W.DD T₁) (hyz : (y, z) ∈ W.divisibleCocycles T₁),
      y ∈ invN W T₁ (W.Q ^ M) ∧ z ∈ aN W T₁ W.X ∧ W.cl T₁ ⟨(y, z), hyz⟩ = (l ^ c : ℕ) • κ)
    (y₂ z₂ : W.DD T₂) (hy₂ : y₂ ∈ invN W T₂ (W.Q ^ M)) (hz₂ : z₂ ∈ aN W T₂ W.X)
    (hyz₂ : (y₂, z₂) ∈ W.divisibleCocycles T₂) :
    ∃ (k : ℕ) (y z : W.DD T₁), (y, z) ∈ W.divisibleCocycles T₁ ∧ y ∈ invN W T₁ (W.Q ^ M) ∧ z ∈ aN W T₁ W.X ∧
      W.map π y = (l ^ k : ℕ) • y₂ ∧ W.map π z = (l ^ k : ℕ) • z₂ := by
  exact lift_multiple_lemma W π l M c₁ c₂ hnat h2 hφ hc hcok hrex hc3 y₂ z₂ hy₂ hz₂ hyz₂

theorem defect_of_lift (M : ℕ) (hinj : Function.Injective (W.map ι))
    (hex : Function.Exact (W.map ι) (W.map π))
    (hsat : ∀ x : W.DD T₀, W.map ι x ∈ W.N T₁ → x ∈ W.N T₀) (h2 : p2 W T₁)
    (hφ : ∀ x ∈ W.N T₁, W.Q ^ M • W.φD T₁ x ∈ W.N T₁)
    (hQ : ∃ w : LetA O n, W.γA W.gam W.Q = w * W.Q ∧ w - 1 ∈ Ideal.span {W.X})
    (hl : ∀ (y₂ z₂ : W.DD T₂), y₂ ∈ invN W T₂ (W.Q ^ M) → z₂ ∈ aN W T₂ W.X → (y₂, z₂) ∈ W.divisibleCocycles T₂ →
      ∃ (k : ℕ) (y z : W.DD T₁), (y, z) ∈ W.divisibleCocycles T₁ ∧ y ∈ invN W T₁ (W.Q ^ M) ∧ z ∈ aN W T₁ W.X ∧
        W.map π y = (PD.p ^ k : ℕ) • y₂ ∧ W.map π z = (PD.p ^ k : ℕ) • z₂) :
    p2d W ι π M := by
  intro _ y₂ z₂ hy₂ hz₂ hyz₂ y₁ z₁ hy₁ hz₁ hπy₁ hπz₁
  subst hπy₁ hπz₁
  have mγ : ∀ {S S' : LocLat G Qp LL O} (f : LatHom S.L S'.L) (x : W.DD S),
      W.map f (W.γ S x) = W.γ S' (W.map f x) := fun f x => W.map_γ f W.gam x
  have mφ : ∀ {S S' : LocLat G Qp LL O} (f : LatHom S.L S'.L) (x : W.DD S),
      W.map f (W.φD S x) = W.φD S' (W.map f x) := fun f x => W.map_φ f x
  have hπd : W.map π ((W.γ T₁ y₁ - y₁) - (W.φD T₁ z₁ - z₁)) = 0 := by
    simp only [map_sub, mγ, mφ]
    exact (mem_Z1D W T₂ _ _).1 hyz₂
  obtain ⟨w, hw⟩ := (hex _).1 hπd
  have hdX := differential_one_mem_scaled_lattice W T₁ M h2 hφ hQ y₁ z₁ hy₁ hz₁
  rw [← hw, ← map_smulA] at hdX
  have hw0 := mem_X_invN W T₀ _ w (aN_sat W ι hsat _ hdX)
  obtain ⟨k, y, z, hyz, hy, hz, hπy, hπz⟩ := hl _ _ hy₂ hz₂ hyz₂
  have ey : W.map π ((PD.p ^ k : ℕ) • y₁ - y) = 0 := by rw [map_sub, map_nsmul, hπy, sub_self]
  have ez : W.map π ((PD.p ^ k : ℕ) • z₁ - z) = 0 := by rw [map_sub, map_nsmul, hπz, sub_self]
  obtain ⟨y₀, hy₀⟩ := (hex _).1 ey
  obtain ⟨z₀, hz₀⟩ := (hex _).1 ez
  have hy₀m : y₀ ∈ invN W T₀ (W.Q ^ M) := by
    rw [mem_invN]
    apply hsat
    rw [map_smulA, hy₀, smul_sub, smul_comm (W.Q ^ M) (PD.p ^ k : ℕ)]
    exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ ((mem_invN W T₁ _ _).1 hy₁))
      ((mem_invN W T₁ _ _).1 hy)
  have hz₀m : z₀ ∈ aN W T₀ W.X := by
    apply aN_sat W ι hsat
    rw [hz₀]
    exact Submodule.sub_mem _ (Submodule.smul_of_tower_mem _ _ hz₁) hz
  refine ⟨w, hw, hw0, k, y₀, hy₀m, z₀, hz₀m, ?_⟩
  apply hinj
  rw [map_smulA, hw, ← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  simp only [map_sub, mγ, mφ, hy₀, hz₀, map_nsmul]
  have hyz' := (mem_Z1D W T₁ y z).1 hyz
  have e3 : W.φD T₁ z = W.γ T₁ y - y + z := by
    rw [eq_comm, ← sub_eq_zero, ← hyz']
    abel
  rw [e3]
  simp only [smul_sub]
  abel

theorem jumpsLet_quot (M h : ZMod n → ℕ)
    (hj : ∀ τ a, IsJumpV PD T₁.ρ τ a ↔ IsJumpV PD T₀.ρ τ a ∨ IsJumpV PD T₂.ρ τ a)
    (h₁ : JumpsLet W T₁ M h) : JumpsLet W T₂ M h := by
  intro τ i hτ a ha
  exact h₁ τ i hτ a ((hj τ a).2 (Or.inr ha))

end Generic

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem defect_torsion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), Pr2d D HW F := by
  intro D HW F Cm l _ K s LL h T₀ T₁ T₂ ι π M hh c₀ c₁ c₂ hJ hses
  have : NeZero (Module.finrank ℚ_[l] ↥(K0 K)) := ⟨Module.finrank_pos.ne'⟩
  have hp : ((D.loc l).PD K).p = l := (D.loc l).PD_p K
  obtain ⟨hinj, hex, -⟩ := GlobalTheory.EtaleExact.DD_exact D HW F (GlobalTheory.HerrFull.fontaine_decompletion D HW F)
    l K s LL h T₀ T₁ T₂ ι π hses
  have hsat := GlobalTheory.T.mem_wachN_of_map_mem_saturated D HW F l K s LL h T₀ T₁ T₂ ι π c₀ c₁ c₂ hses
  have h2 := GlobalTheory.NL.WachLatticeTrivialModUniformizer.wachLattice_galois_trivial_mod_uniformizer D HW F Cm l K s LL h T₁ c₁
  have hP5 := GlobalTheory.T.wachLattice_heights_from_hodgeJumps D HW F Cm l K s LL h T₁ M hh c₁ hJ
  have hφ : ∀ x ∈ ((HW l).W K s LL h).N T₁,
      ((HW l).W K s LL h).Q ^ mx M • ((HW l).W K s LL h).φD T₁ x ∈ ((HW l).W K s LL h).N T₁ :=
    fun x hx => φ_mem ((HW l).W K s LL h) T₁ M hh hP5 x hx
  have hc₁ := GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F l K s LL h T₁ M hh c₁ hJ
  have hj := (GlobalTheory.NL.JumpsSES.jumps_ses_and_one D HW l K s LL h T₀ T₁ T₂ ι π c₁ hses).1
  have hJ₂ := jumpsLet_quot ((HW l).W K s LL h) M hh hj hJ
  have hc₂ := GlobalTheory.T.wachIntegralComplex_cocycle_class_finite D HW F l K s LL h T₂ M hh c₂ hJ₂
  obtain ⟨cc, hcz⟩ := GlobalTheory.T.wachN_cokernel_killed_by_power D HW F Cm l K s LL h T₀ T₁ T₂ ι π c₀ c₁ c₂ hses
  have hrex := GlobalTheory.NL.RightExactKs.h1fKs_onto_up_to_pow D HW l K s LL h T₁ T₂ π hses.2.1 c₁ c₂
  have hc3 := GlobalTheory.T.H1f_class_wach_pair_filtration_jumps D HW F Cm l K s LL h T₁ c₁ M hh hJ
  have hnat : ((HW l).W K s LL h).ClNat := (GlobalTheory.HerrFull.herr_a_and_natural D HW F l K s LL h).2.2
  refine defect_of_lift ((HW l).W K s LL h) ι π (mx M) hinj hex hsat h2 hφ hc₁.1 ?_ hses
  intro y₂ z₂ hy₂ hz₂ hyz₂
  rw [hp]
  exact lift_multiple ((HW l).W K s LL h) π l (mx M) c₁ c₂ hnat h2 hφ hc₂ ⟨cc, fun z hz => (hcz z hz).1⟩
    hrex hc3 y₂ z₂ hy₂ hz₂ hyz₂

end GlobalTheory.NL.DefectTorsion
