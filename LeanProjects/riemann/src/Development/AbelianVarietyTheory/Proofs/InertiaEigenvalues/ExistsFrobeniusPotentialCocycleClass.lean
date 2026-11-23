import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotentialPhiSub
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsLogAExtends
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KisinInfGaloisActsThroughDescentDatumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinBcrisComparisonFrobeniusNaturalityStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinMuPowSmulFrobeniusMemAinfStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyMemRangeOfInvariantVectorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGaloisDecompTameCoverActionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorOneInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HorizEqXiRedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPrimePowSmulMemLocalLatticeStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.GalPot

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e}
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]

theorem inclL_smul (P : PhiMod O K l e a ι) (r : OA l O) (d : ι → OA l O) :
    inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := by
  rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
  exact congrArg _ (funext fun i => map_mul _ _ _)

theorem isCrisVal_add {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w w' : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w' b') :
    IsCrisVal t ϖ P jB (w + w') (b + b') := by
  obtain ⟨m, c, hm, h1, h2⟩ := h
  obtain ⟨m', c', hm', h1', h2'⟩ := h'
  refine ⟨m * m', m' • c + m • c', by rw [map_mul]; exact hm.mul hm', ?_, ?_⟩
  · rw [map_add, inclL_smul, inclL_smul, ← h1, ← h1', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (inclO l O m) (inclO l O m') w]
  · have e1 : (fun i => toB l O ((m' • c + m • c') i)) =
        toB l O m' • (fun i => toB l O (c i)) + toB l O m • (fun i => toB l O (c' i)) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul]
    rw [e1, map_add, map_smul, map_smul, ← h2, ← h2', map_mul, smul_add, mul_smul, mul_smul,
      smul_comm (toB l O m) (toB l O m') b]

theorem isCrisVal_zero {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} : IsCrisVal t ϖ P jB 0 0 :=
  ⟨1, 0, by rw [map_one]; exact isUnit_one, by rw [smul_zero, map_zero], by
    rw [smul_zero]
    have e0 : (fun i => toB l O ((0 : ι → OA l O) i)) = 0 := funext fun i => map_zero (toB l O)
    rw [e0, map_zero]⟩

theorem isCrisVal_nsmul {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w : ι → OW l O} {b : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (n : ℕ) : IsCrisVal t ϖ P jB (n • w) (n • b) := by
  induction n with
  | zero => rw [zero_smul, zero_smul]; exact isCrisVal_zero
  | succ n ih => rw [succ_nsmul, succ_nsmul]; exact isCrisVal_add ih h

variable [TameDescentExponentData K l e a] {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}

theorem isPotential_add (R : GalDat t ϖ s D T) {y y' : Vec K a ι} {b b' : TW (OB l O) T}
    (h : R.IsPotential y b) (h' : R.IsPotential y' b') : R.IsPotential (y + y') (b + b') := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  obtain ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩ := h'
  refine ⟨add_mem hy hy', m₀ + m₀', σ + σ', b₀ + b₀', ?_, add_mem h2 h2', ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (⟨y, hy⟩ + ⟨y', hy'⟩)
    rw [map_add, map_add, ← h1, ← h1']
    abel
  · rw [Submodule.coe_add, map_add, map_add, h3, h3']
  · rw [map_add]
    exact isCrisVal_add h4 h4'
  · rw [h5, h5', map_add, map_add]
    abel

theorem isPotential_nsmul (R : GalDat t ϖ s D T) {y : Vec K a ι} {b : TW (OB l O) T}
    (h : R.IsPotential y b) (n : ℕ) : R.IsPotential (n • y) (n • b) := by
  obtain ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩ := h
  refine ⟨(ME D.toPhiMod).nsmul_mem hy n, n • m₀, n • σ, n • b₀, ?_, D.desc.inv.nsmul_mem h2 n, ?_, ?_, ?_⟩
  · change _ = toW t ϖ D.toPhiMod (n • ⟨y, hy⟩)
    rw [map_nsmul, map_nsmul, ← h1, smul_sub]
  · show D.conn (n • σ.1) = _
    rw [map_nsmul, map_nsmul, h3]
  · rw [map_nsmul]
    exact isCrisVal_nsmul h4 n
  · rw [h5, map_nsmul, map_nsmul, nsmul_sub]

theorem isCobOf_pow {b : TW (OB l O) T} {c : G → T.V} (h : IsCobOf s T b c) (k : ℕ) :
    IsCobOf s T ((l ^ k : ℕ) • b) ((l : K) ^ k • c) := by
  intro g n x hx
  have h1 := h g (n + k) x (by rw [hx, Pi.smul_apply, smul_smul, pow_add])
  rw [h1, map_nsmul, ← nsmul_sub, ← Nat.cast_smul_eq_nsmul O, smul_smul, Nat.cast_pow, pow_add]

theorem exists_isEps : ∃ ε : OCb l, IsEps ε := by
  obtain ⟨ε, h1, h2⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
  exact ⟨ε, h1, (frobeniusEquiv (Per.Fl l) l).symm ε, frobeniusEquiv_symm_pow_p _ _ _, h2⟩

theorem isUnit_toB_muOf {ε : OCb l} (hε : IsEps ε) (n : ℕ) :
    IsUnit (toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n))) := by
  obtain ⟨δ, hδ, -⟩ := hε.2
  have hu : IsUnit (acrisToBcris l (ainfToAcris l (muOf ε))) :=
    ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.2.2.1
  have e1 : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ n)) =
      (Algebra.TensorProduct.includeRight : Per.Bcris l →ₐ[ℤ_[l]] OB l O)
        (acrisToBcris l (ainfToAcris l (muOf ε)) ^ n) := by
    simp only [toB, toOB, toOCr, AlgHom.comp_apply, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
      Algebra.TensorProduct.includeRight_apply, map_pow, Algebra.TensorProduct.tmul_pow, one_pow]
  rw [e1]
  exact (hu.pow n).map _

theorem actB_mul (s : G →* GQ l) (T : LocLat G ℚ_[l] K O) (g g' : G) (z : TW (OB l O) T) :
    actB s T (g * g') z = actB s T g (actB s T g' z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add, hx, hy]
  | tmul w x =>
    have hw : galOB O (s (g * g')) w = galOB O (s g) (galOB O (s g') w) := by
      rw [map_mul]
      induction w using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | add u v hu hv => simp only [map_add, hu, hv]
      | tmul o c =>
        simp only [galOB, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg (fun z : Per.Bcris l => o ⊗ₜ[ℤ_[l]] z) ((GlobalTheory.MemLoc.ActLaws.act_laws l).1 _ _ c)
    have hx : T.actT (g * g') x = T.actT g (T.actT g' x) :=
      Subtype.ext (LinearMap.congr_fun (map_mul T.ρ g g') (x : T.V))
    simp only [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, hw, hx]

theorem sub_mem_B1T {s : G →* GQ l} {T : LocLat G ℚ_[l] K O} {b b' ξ : TW (OB l O) T} {c c' : G → T.V}
    (x : ↥T.L.T) (hb : IsCobOf s T b c) (hb' : IsCobOf s T b' c') (hξ : ∀ g, actB s T g ξ = ξ)
    (h : b - b' = ξ - (1 : OB l O) ⊗ₜ[O] x) : c - c' ∈ latticeCoboundaries T.L := by
  refine ⟨-(x : T.V), neg_mem x.2, funext fun g => ?_⟩
  obtain ⟨n₁, hn₁⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c g)
  obtain ⟨n₂, hn₂⟩ := GlobalTheory.T.exists_prime_pow_smul_mem_localLattice l O K G T (c' g)
  obtain ⟨x₁, hx₁⟩ := hn₁ (max n₁ n₂) (le_max_left _ _)
  obtain ⟨x₂, hx₂⟩ := hn₂ (max n₁ n₂) (le_max_right _ _)
  have e1 := hb g _ x₁ hx₁
  have e2 := hb' g _ x₂ hx₂
  have hact : actB s T g ((1 : OB l O) ⊗ₜ[O] x) = (1 : OB l O) ⊗ₜ[O] (T.actT g x) := by
    rw [actB, TWact, TensorProduct.map_tmul, AlgHom.toLinearMap_apply, map_one]
  have hbb : b = b' + (ξ - (1 : OB l O) ⊗ₜ[O] x) := by rw [← h]; abel
  have e3 : (1 : OB l O) ⊗ₜ[O] (x₁ - x₂) =
      (1 : OB l O) ⊗ₜ[O] (((l : O) ^ max n₁ n₂) • (x - T.actT g x)) := by
    rw [TensorProduct.tmul_sub, e1, e2, ← smul_sub, TensorProduct.tmul_smul, TensorProduct.tmul_sub, ← hact,
      hbb, map_add, map_sub, hξ]
    congr 1
    abel
  have e4 := congrArg (fun z : ↥T.L.T => (z : T.V)) (GlobalTheory.T.one_tmul_injective_locLat l O K G T e3)
  simp only [Submodule.coe_sub, Submodule.coe_smul] at e4
  have eO : ∀ v : T.V, ((l : O) ^ max n₁ n₂) • v = (l : K) ^ max n₁ n₂ • v := fun v => by
    rw [← algebraMap_smul K ((l : O) ^ max n₁ n₂) v, map_pow, map_natCast]
  rw [hx₁, hx₂, ← smul_sub, eO] at e4
  have hl0 : (l : K) ≠ 0 := by
    rw [← map_natCast (algebraMap ℚ_[l] K)]
    exact (map_ne_zero _).2 (Nat.cast_ne_zero.2 hl.out.ne_zero)
  have e5 := (smul_right_inj (pow_ne_zero (max n₁ n₂) hl0)).1 e4
  simp only [LinearMap.restrictScalars_apply, Pi.sub_apply]
  rw [e5]
  change T.ρ g (-(x : T.V)) - (-(x : T.V)) = (x : T.V) - T.ρ g (x : T.V)
  rw [map_neg]
  abel

section Ql

variable [TameDescentExponentData K l e a] {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat (Gl l) ℚ_[l] K O}

theorem exists_isCrisVal (R : GalDat t ϖ (sQ l) D T) {y : Vec K a ι} (hyY : y ∈ D.Y) (hy : y ∈ ME D.toPhiMod)
    (m₀ : ι → OW l O) (h : phiW t ϖ D.toPhiMod m₀ - m₀ = toW t ϖ D.toPhiMod ⟨y, hy⟩) :
    ∃ b₀, IsCrisVal t ϖ D.toPhiMod R.jB (phiW t ϖ D.toPhiMod m₀) b₀ := by
  obtain ⟨ε, hε⟩ := exists_isEps (l := l)
  obtain ⟨δ, hδ, -⟩ := hε.2
  obtain ⟨c, hc⟩ := (GlobalTheory.T.breuilKisin_mu_pow_smul_frobenius_mem_ainf l a e O K t ϖ ι D.toPhiMod T R.I η H D.upper D.lower ε δ hε hδ ⟨y, hy⟩
    hyY.1 m₀ h).2
  obtain ⟨u, hu⟩ := isUnit_toB_muOf (O := O) hε (H + η)
  refine ⟨(↑u⁻¹ : OB l O) • R.jB (fun i => toB l O (c i)), (1 : O) ⊗ₜ[ℤ_[l]] (muOf ε ^ (H + η)), c,
    ⟨u, hu⟩, hc.symm, ?_⟩
  rw [← hu, smul_smul, Units.mul_inv, one_smul]

theorem fix_of_horiz (R : GalDat t ϖ (sQ l) D T) (σ : D.MMl) (hinv : σ.1 ∈ D.desc.inv)
    (hc : D.conn σ.1 = 0) (g : Gl l) :
    actB (sQ l) T g (R.jB (toBcris t ϖ D.toPhiMod σ)) = R.jB (toBcris t ϖ D.toPhiMod σ) := by
  obtain ⟨h, k, rfl, hh, γ, hk⟩ := GlobalTheory.T.exists_galois_decomp_tameCover_action l a e O K t ϖ g
  have hx := GlobalTheory.T.eq_xi_red_of_conn_eq_zero' O K l e a ι D.toPhiMod σ.1 hc
  have hm : D.xi (red σ.1) ∈ D.MMl := by rw [← hx]; exact σ.2
  have hσ : (⟨D.xi (red σ.1), hm⟩ : D.MMl) = σ := Subtype.ext hx.symm
  have h2 := R.horiz h hh (red σ.1) hm
  rw [hσ] at h2
  have h3 := GlobalTheory.T.kisinInfGalois_acts_through_descentDatum l a e O K t ϖ ι D.toPhiMod T R.I R.jB D.desc R.cmp R.desc k γ hk σ σ (hinv γ).symm
  rw [actB_mul, h3, h2]

end Ql

theorem potential_class : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), (∀ y ∈ D.Y, ∃ b, R.IsPotential y b) ∧ (∀ y c c', R.ClassOf y c → R.ClassOf y c' → c - c' ∈ latticeCoboundaries T.L) ∧ (∀ y c (k : ℕ), R.ClassOf y c → R.ClassOf ((l : K) ^ k • y) ((l : K) ^ k • c)) ∧ ∀ y c, ∀ m ∈ D.Minv, R.ClassOf y c → R.ClassOf (y + (D.phi m - m)) c := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ η H D T R
  haveI : FiniteDimensional ℚ_[l] K := TameDescentExponentData.finite (K := K) (l := l) (e := e) (a := a)
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro y hyY
    have hy : y ∈ ME D.toPhiMod := BKDat.mem_invE_of_mem_Y hyY
    obtain ⟨m₀, hm₀⟩ := R.I.exists_phiW_sub (toW t ϖ D.toPhiMod ⟨y, hy⟩)
    have hYl : y ∈ D.Yl := D.desc.mem_Yl_iff.2 ⟨0, by rw [pow_zero, one_smul]; exact hyY⟩
    obtain ⟨⟨σ, hσ, hinv, hconn, -⟩, -⟩ := GlobalTheory.T.monodromy_mem_range_of_invariant_vector O K l e a ι η H D y hYl
    obtain ⟨b₀, hb₀⟩ := exists_isCrisVal R hyY hy m₀ hm₀
    exact ⟨_, hy, m₀, ⟨σ, hσ⟩, b₀, hm₀, hinv, hconn, hb₀, rfl⟩
  · rintro y c c' ⟨b, ⟨hy, m₀, σ, b₀, h1, h2, h3, h4, h5⟩, hc⟩ ⟨b', ⟨hy', m₀', σ', b₀', h1', h2', h3', h4', h5'⟩, hc'⟩
    have hT : m₀ - m₀' ∈ Treal t ϖ D.toPhiMod := by
      rw [mem_Treal, map_sub]
      exact sub_eq_sub_iff_sub_eq_sub.1 (h1.trans h1'.symm)
    obtain ⟨x, hx⟩ : m₀ - m₀' ∈ LinearMap.range R.I.ofT := by rw [R.I.range_ofT]; exact hT
    have hphi : phiW t ϖ D.toPhiMod m₀' + R.I.ofT x = phiW t ϖ D.toPhiMod m₀ := by
      rw [hx, ← mem_Treal.1 hT, map_sub]
      abel
    have hof := ((GlobalTheory.T.breuilKisin_bcris_comparison_frobenius_naturality l a e O K t ϖ ι D.toPhiMod T R.I).2 R.jB R.cmp).2.2.2.1 x
    have hsum := isCrisVal_add h4' hof
    rw [hphi] at hsum
    have hb₀ : b₀ = b₀' + (1 : OB l O) ⊗ₜ[O] x := UnitModel.isCrisVal_unique t ϖ h4 hsum
    refine sub_mem_B1T x hc hc' (fix_of_horiz R (σ - σ') (sub_mem h2 h2') ?_) ?_
    · show D.conn (σ.1 - σ'.1) = 0
      rw [map_sub, h3, h3', sub_self]
    · rw [h5, h5', hb₀, map_sub, map_sub]
      abel
  · rintro y c k ⟨b, hb, hc⟩
    refine ⟨(l ^ k : ℕ) • b, ?_, isCobOf_pow hc k⟩
    have := isPotential_nsmul R hb (l ^ k)
    rwa [← Nat.cast_smul_eq_nsmul K, Nat.cast_pow] at this
  · rintro y c m hm ⟨b, hb, hc⟩
    exact ⟨b + 0, isPotential_add R hb (UnitModel.isPotential_phi_sub t ϖ R hm), by rwa [add_zero]⟩

end GlobalTheory.GalPot
