import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneNotMemFilOne

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.UnitModel

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e)
  {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G]

omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem xi_unit (d : (unitMod l a e O K ι).D) : (unitMod l a e O K ι).xi d = cst d :=
  (PhiMod.xi_unique _ (s := fun d => cst d) red_cst (fun d => by
    ext1 τ
    rw [PhiMod.phi_apply, mx_unitMod, Matrix.one_mulVec]
    ext1 i
    rw [cst_apply, PhiMod.phiD_apply, PhiMod.mx0, mx_unitMod, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mulVec]
    simp [PhiMod.phiD_apply, PhiMod.mx0, mx_unitMod, frob_C]) d).symm

omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem nabla_bas (i : ι) : (unitMod l a e O K ι).nabla (bas i) = 0 := by
  rw [← cst_single, ← xi_unit (O := O) (l := l) (e := e), PhiMod.nabla_xi]

omit [NeZero a] [NeZero e] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedAlgebra ℚ_[l] K] in

theorem phi_bas_unit (i : ι) : (unitMod l a e O K ι).phi (bas i) = bas i := by
  ext1 τ
  rw [PhiMod.phi_bas, mx_unitMod]
  ext1 j
  simp [bas, Matrix.one_apply, Pi.single_apply]

variable [TameDescentExponentData K l e a]

variable (O K l e a ι) in

def unitDesc : Descent (unitMod l a e O K ι) :=
  Descent.ofMatrix _ (fun _ _ => 1)
    (fun _ _ i j => by rw [Matrix.one_apply]; split_ifs; exacts [one_mem _, zero_mem _])
    (fun _ => rfl)
    (fun _ _ _ => by rw [Matrix.map_one _ (map_zero _) (map_one _), one_mul])
    fun _ _ => by
      rw [mx_unitMod, mx_unitMod, Matrix.map_one _ (map_zero _) (map_one _),
        Matrix.map_one _ (map_zero _) (map_one _)]

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in

theorem unitDesc_act (γ : TameGal K l e a) (v : Vec K a ι) (τ : ZMod a) (i : ι) :
    (unitDesc l a e O K ι).act γ v τ i = ringAct γ (fun σ => v σ i) τ := by
  change Descent.matAct γ (fun _ => 1) v τ i = _
  rw [Descent.matAct_apply, Matrix.one_mulVec, ringAct_apply]

variable (O K l e a ι) in

def unitDat (η H : ℕ) : BKDat O K l e a ι η H where
  toPhiMod := unitMod l a e O K ι
  desc := unitDesc l a e O K ι
  nabla_mem _ := PhiMod.nabla_mem_MM_of_basis _
    (fun i => by rw [phi_bas_unit, nabla_bas]; exact zero_mem _)
    fun i => PhiMod.ext_mono _ (A_le_S l e) (PhiMod.phi_mem_L _ (PhiMod.bas_mem_M _ i))
  EN_mem _ hm := PhiMod.EN_mem_Man_of_basis _ (fun i => by
    rw [PhiMod.EN_apply, PhiMod.conn_apply, nabla_bas, smul_zero, smul_zero]
    exact zero_mem _) (PhiMod.M_le_Man _ hm)
  lower m hm := mem_ext_unitMod.2 fun τ i => mul_mem (pow_mem (E_mem l e _) _) (mem_tot.1 hm τ i)
  upper m hm := mem_tot.2 fun τ i => mul_mem (pow_mem (E_mem l e _) _) (mem_ext_unitMod.1 hm τ i)

theorem galOW_iW_of_covers {h : GQ l} {γ : TameGal K l e a} (hc : Covers K t ϖ h γ)
    (f f' : ZMod a → invE l e (A O K))
    (hf : ∀ τ, (f' τ : K⟦X⟧) = ringAct γ (fun σ => (f σ : K⟦X⟧)) τ) :
    galOW O h (ϖ.iW t K f) = ϖ.iW t K f' := by
  choose n hn using fun τ => mem_away.1 (f τ).2
  let N := ∑ τ, n τ
  have hN : ∀ τ, E K l e ^ N * (f τ : K⟦X⟧) ∈ A O K := fun τ => by
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ τ))
    rw [show N = k + n τ from hk, pow_add, mul_assoc]
    exact mul_mem (pow_mem (E_mem l e _) _) (hn τ)
  have hE : ringAct γ (fun σ => E K l e ^ N * (f σ : K⟦X⟧)) =
      fun τ => E K l e ^ N * (f' τ : K⟦X⟧) := by
    have : (fun σ => E K l e ^ N * (f σ : K⟦X⟧)) =
        (fun _ : ZMod a => E K l e) ^ N * fun σ => (f σ : K⟦X⟧) := rfl
    rw [this, map_mul, map_pow, ringAct_E]
    exact funext fun τ => by rw [hf τ]; rfl
  have hN' : ∀ τ, E K l e ^ N * (f' τ : K⟦X⟧) ∈ A O K := fun τ => by
    rw [← congrFun hE τ]
    exact rot_A.ringAct_mem γ hN τ
  have h1 := hc (fun τ => ⟨_, hN τ⟩) (fun τ => ⟨_, hN' τ⟩) fun τ => (congrFun hE τ).symm
  have h2 := hc (fun _ => EIn l e _) (fun _ => EIn l e _) fun τ => (congrFun (ringAct_E γ) τ).symm
  set ε : OW l O := inclO l O (ϖ.iTot t K fun _ => EIn l e _) with hε
  have hu : IsUnit ε := by
    rw [hε, PiSys.iTot_E, ← ϖ.iA_E a O K]
    exact ϖ.isUnit_inclO_iA_E O K
  have key : ∀ (g : ZMod a → invE l e (A O K)) (hg : ∀ τ, E K l e ^ N * (g τ : K⟦X⟧) ∈ A O K),
      inclO l O (ϖ.iTot t K fun τ => ⟨_, hg τ⟩) = ε ^ N * ϖ.iW t K g := fun g hg => by
    rw [hε, ← ϖ.iW_of_mem t K, ← ϖ.iW_of_mem t K, ← map_pow, ← map_mul]
    rfl
  have h3 := congrArg (inclO l O) h1
  rw [← galOW_inclO, key, key, map_mul, map_pow, hε, galOW_inclO, h2] at h3
  exact (hu.pow N).mul_left_cancel h3

omit [TameDescentExponentData K l e a] in

theorem galOB_iB_const {h : GQ l} (hh : h ∈ GK (ϖ.field a)) (f : ZMod a → invL l (S O K e))
    (c : ZMod a → K) (hf : ∀ τ, (f τ : K⟦X⟧) = C (c τ)) : galOB O h (ϖ.iB t K f) = ϖ.iB t K f := by
  rw [PiSys.iB, glue_apply, map_sum]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [map_mul]
  congr 1
  · exact (galOB_toOB h _).trans (congrArg _ (galOCr_idem t ϖ ⟨h, hh⟩ τ))
  · obtain ⟨n, hn⟩ := monomial_mem_invL (O := O) l 0 (c τ)
    obtain ⟨o, ho⟩ := (IsUnitBall.mem_range_iff (O := O) ((l : K) ^ n * c τ)).2 (by
      have h0 := mem_A.1 hn 0
      rwa [SubringClass.coe_natCast, ← map_natCast (C : K →+* K⟦X⟧), ← map_pow, coeff_C_mul,
        coeff_monomial_same] at h0)
    have h1 : (l : invL l (S O K e)) ^ n * f τ = algebraMap O _ o := Subtype.ext (by
      rw [Subalgebra.coe_algebraMap, algebraMap_eq_C, ho]
      simp [hf τ])
    have h2 := congrArg (ϖ.iSl O K) h1
    rw [map_mul, map_pow, map_natCast, AlgHom.commutes] at h2
    have h3 := congrArg (galOB O h) h2
    rw [map_mul, map_pow, map_natCast, AlgHom.commutes, ← h2] at h3
    exact (isUnit_l_OB.pow n).mul_left_cancel h3

def coordEq (R : Type) [CommRing R] [Algebra O R] (T : LocLat G ℚ_[l] K O) (b : Module.Basis ι O ↥T.L.T) :
    (ι → R) ≃ₗ[R] TW R T := (b.baseChange R).equivFun.symm

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsUltrametricDist K] [IsUnitBall O K]
  [DecidableEq ι] in

theorem coordEq_apply (R : Type) [CommRing R] [Algebra O R] (T : LocLat G ℚ_[l] K O)
    (b : Module.Basis ι O ↥T.L.T) (v : ι → R) : coordEq R T b v = ∑ i, v i ⊗ₜ[O] b i := by
  simp only [coordEq, Module.Basis.equivFun_symm_apply, Module.Basis.baseChange_apply, smul_tmul',
    smul_eq_mul, mul_one]

def unitGal (s : G →* GQ l) (η H : ℕ) (T : LocLat G ℚ_[l] K O) (hT : ∀ g x, T.ρ g x = x)
    (b : Module.Basis ι O ↥T.L.T) : GalDat t ϖ s (unitDat l a e O K ι η H) T where
  I := unitIdent t ϖ T b
  jB := coordEq (OB l O) T b
  cmp c z h := by
    obtain ⟨c', rfl⟩ := (coordEq (OA l O) T b).surjective z
    have h1 : (unitIdent t ϖ T b).j (inclL t ϖ (unitMod l a e O K ι) c) =
        (unitIdent t ϖ T b).j (inclL t ϖ (unitMod l a e O K ι) c') := by
      refine h.trans ?_
      rw [unitIdent_j, coordEq_apply, map_sum, inclL_apply, frobMat_unitMod, Matrix.one_mulVec]
      rfl
    obtain rfl := inclL_injective t ϖ _ ((unitIdent t ϖ T b).j.injective h1)
    rw [coordEq_apply, coordEq_apply, map_sum]
    rfl
  desc g γ hc v v' hv := by
    refine (unitIdent_act t ϖ T b (s g) (hT g) _).trans (funext fun i => ?_)
    exact galOW_iW_of_covers t ϖ hc _ _ fun τ =>
      (congrFun (congrFun hv τ) i).trans (unitDesc_act γ v.1 τ i)
  stable g := (Ident.exists_isLMat_iff _ _ _).1 ⟨1, isLMat_unitIdent t ϖ T b (s g) (hT g)⟩
  horiz g hg d h := by
    rw [coordEq_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : T.actT g (b i) = b i := Subtype.ext (hT g _)
    rw [actB, TWact, TensorProduct.map_tmul, h1, AlgHom.toLinearMap_apply, toBcris_apply,
      galOB_iB_const t ϖ hg _ (fun τ => d τ i) fun τ => ?_]
    change ((unitMod l a e O K ι).mxInv τ *ᵥ (unitMod l a e O K ι).xi d τ) i = _
    rw [mxInv_unitMod, Matrix.one_mulVec, xi_unit, cst_apply]

def unitPack {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] (η H : ℕ) (T : QLat LL)
    (hT : ∀ g x, T.ρ g x = x) : Pack a ϖ η H T where
  n := _
  D := unitDat l a e _ _ _ η H
  R := unitGal _ ϖ (sQ l) η H T hT (latBasis T)
  isBK := isBK_unitIdent (thetaW a LL) ϖ (T := resF T (ϖ.field a)) (fun g x => hT _ x) (latBasis T)

omit [TameDescentExponentData K l e a] in

theorem isCrisVal_unique {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}
    {jB : (ι → OB l O) ≃ₗ[OB l O] TW (OB l O) T} {w : ι → OW l O} {b b' : TW (OB l O) T}
    (h : IsCrisVal t ϖ P jB w b) (h' : IsCrisVal t ϖ P jB w b') : b = b' := by
  obtain ⟨m, c, hm, h1, h2⟩ := h
  obtain ⟨m', c', hm', h1', h2'⟩ := h'
  have key : ∀ (r : OA l O) (d : ι → OA l O), inclL t ϖ P (r • d) = inclO l O r • inclL t ϖ P d := fun r d => by
    rw [inclL_apply, inclL_apply, ← Matrix.mulVec_smul]
    exact congrArg _ (funext fun i => map_mul _ _ _)
  have h3 : m' • c = m • c' := inclL_injective t ϖ P (by rw [key, key, ← h1, ← h1', smul_comm])
  have h4 : toB l O m' • (fun i => toB l O (c i)) = toB l O m • fun i => toB l O (c' i) :=
    funext fun i => by
      have := congrArg (toB l O) (congrFun h3 i)
      simpa only [Pi.smul_apply, smul_eq_mul, map_mul] using this
  have h5 := congrArg jB h4
  rw [map_smul, map_smul, ← h2, ← h2', smul_comm] at h5
  exact (hm'.smul_left_cancel).1 ((hm.smul_left_cancel).1 h5)

theorem isPotential_phi_sub {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}
    (R : GalDat t ϖ s D T) {m : Vec K a ι} (hm : m ∈ D.Minv) : R.IsPotential (D.phi m - m) 0 := by
  have hL := D.phi_mem_L hm.1
  have hS : D.phi m ∈ D.MMl := D.ext_mono ((A_le_S l e).trans (le_away _ _)) hL
  refine ⟨sub_mem (mem_ME_of_mem_L hL) (mem_ME_of_mem_M hm.1), toW t ϖ D.toPhiMod ⟨m, mem_ME_of_mem_M hm.1⟩, ⟨_, hS⟩,
    R.jB (toBcris t ϖ D.toPhiMod ⟨_, hS⟩), ?_, fun g => ?_, (D.zeta_phi_sub m).symm, ?_, (sub_self _).symm⟩
  · rw [← toW_phi t ϖ D.toPhiMod hm.1, ← map_sub]
    rfl
  · change D.desc.act g (D.phi m) = D.phi m
    rw [D.desc.act_phi, hm.2 g]
  · refine ⟨1, fun i => ϖ.iTot t K (coordL D.toPhiMod _ ⟨_, hL⟩ i), by rw [map_one]; exact isUnit_one, ?_, ?_⟩
    · rw [map_one, one_smul, ← toW_phi t ϖ D.toPhiMod hm.1]
      exact (toW_toCris_of_mem_L t ϖ D.toPhiMod hL (D.ext_mono (A_le_S l e) hL)).1
    · rw [map_one, one_smul]
      refine congrArg _ (funext fun i => ?_)
      rw [toBcris_apply, toB, AlgHom.comp_apply, ← ϖ.iC_of_mem t K, ← ϖ.iB_of_mem t K]
      rfl

theorem classOf_phi_sub {s : G →* GQ l} {η H : ℕ} {D : BKDat O K l e a ι η H} {T : LocLat G ℚ_[l] K O}
    (R : GalDat t ϖ s D T) {m : Vec K a ι} (hm : m ∈ D.Minv) : R.ClassOf (D.phi m - m) 0 :=
  ⟨0, isPotential_phi_sub t ϖ R hm, fun g n x hx => by
    obtain rfl : x = 0 := Subtype.ext (by simpa using hx)
    simp⟩

theorem covers_one {g : GQ l} (hg : g ∈ ϖ.GfieldInf a) : Covers K t ϖ g (1 : TameGal K l e a) := fun f f' h => by
  obtain rfl : f' = f := funext fun τ => Subtype.ext (by rw [h τ, map_one]; rfl)
  exact ϖ.galOA_iTot t K hg f'

theorem fix_Kur {F : FinExt l} {g : ↥(GK F)} (hg : g ∈ IK F) : (g : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup := by
  refine (Subgroup.closure_le ((MaximalUnramifiedExtension l).fixingSubgroup.comap (GK F).subtype)).2 (fun σ hσ => ?_) hg
  change (σ : GQ l) ∈ (MaximalUnramifiedExtension l).fixingSubgroup
  rw [← Subgroup.zpowers_le, ← IntermediateField.le_iff_le, MaximalUnramifiedExtension, IntermediateField.adjoin_le_iff]
  rintro x ⟨m, hm, hlm, hx⟩
  have hx1 : ‖x‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg x) hm.ne').1 (by rw [← norm_pow, hx, norm_one])
  have hx0 : x ≠ 0 := norm_ne_zero_iff.1 (by rw [hx1]; exact one_ne_zero)
  have key : (σ : GQ l) x = x := by
    set y := (σ : GQ l) x / x with hy
    have hy1 : y ^ m = 1 := by rw [hy, div_pow, ← map_pow, hx, map_one, div_one]
    have hy2 : ‖y - 1‖ < 1 := by
      rw [hy, div_sub_one hx0, norm_div, hx1, div_one]
      exact hσ x hx1.le
    have hyn : ‖y‖ = 1 := (pow_eq_one_iff_of_nonneg (norm_nonneg y) hm.ne').1 (by rw [← norm_pow, hy1, norm_one])
    by_contra hne
    have hy3 : y - 1 ≠ 0 := sub_ne_zero.2 fun h => hne ((div_eq_one_iff_eq hx0).1 h)
    have hs : ∑ i ∈ Finset.range m, y ^ i = 0 :=
      (mul_eq_zero.1 ((geom_sum_mul y m).trans (by rw [hy1, sub_self]))).resolve_right hy3
    have hi : ∀ i : ℕ, ‖1 - y ^ i‖ ≤ ‖y - 1‖ := fun i => by
      induction i with
      | zero => simp
      | succ i ih =>
        rw [show 1 - y ^ (i + 1) = (1 - y ^ i) + -(y ^ i * (y - 1)) by ring]
        refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
        rw [norm_neg, norm_mul, norm_pow, hyn, one_pow, one_mul]
    have h4 : (m : Om l) = ∑ i ∈ Finset.range m, (1 - y ^ i) := by
      rw [Finset.sum_sub_distrib, hs]
      simp
    have h5 : ‖(m : Om l)‖ ≤ ‖y - 1‖ := by
      rw [h4]
      exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (norm_nonneg _) fun i _ => hi i
    have h6 : ‖(m : Om l)‖ = 1 := by
      rw [← map_natCast (algebraMap ℚ_[l] (Om l)), norm_algebraMap', Padic.norm_natCast_eq_one_iff]
      exact (Nat.Prime.coprime_iff_not_dvd hl.out).2 hlm
    linarith
  rintro ⟨_, k, rfl⟩
  exact MulAction.mem_fixedBy_zpow (α := Om l) (g := (σ : GQ l)) (a := x) key k

omit [NeZero e] [TameDescentExponentData K l e a] in

theorem isGood_of_trivial (Pl : LocPrime l) {LL : FinExt l} (T : QLat LL) (hT : ∀ g x, T.ρ g x = x) :
    IsGood a ϖ Pl T {0} {0} := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] T.V := Module.Finite.trans ↥LL.1 T.V
  have : FiniteDimensional ℚ_[l] (resF T (ϖ.field a)).V := this
  refine ⟨GlobalTheory.TrivCrys.isCrys_of_trivial _ _ fun g x => hT _ x, fun g hg w _ x hx => ?_,
    fun τ j hj => by simpa using GlobalTheory.NL.JumpsSES.jumps_of_trivial _ _ hT τ j hj⟩
  rw [GlobalTheory.TrivCrys.dcris_of_trivial _ (resF T (ϖ.field a)).ρ fun g x => hT _ x] at hx
  have key : ∀ y : T.V ⊗[ℚ_[l]] ↥(K0 (ϖ.field a)),
      actVB (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)) T.ρ g (AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V)
        (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 (ϖ.field a)) Pl.R.B).toLinearMap y) =
      AlgebraTensorModule.map (LinearMap.id : T.V →ₗ[↥LL.1] T.V)
        (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 (ϖ.field a)) Pl.R.B).toLinearMap y := fun y => by
    induction y using TensorProduct.induction_on with
    | zero => simp only [map_zero]
    | add x y hx hy => simp only [map_add, hx, hy]
    | tmul v c =>
      have h1 : (Pl.PD (Formalism.MainNotions.ElementDenominator.qlExt l)).actB g (algebraMap _ Pl.R.B c) = algebraMap _ Pl.R.B c :=
        (Pl.PD_actB _ g _).trans (Pl.actQ_Kur _ ⟨c, c.2.2⟩ ⟨c, c.2.2⟩
          ((IntermediateField.mem_fixingSubgroup_iff _ _).1 (fix_Kur hg) _ c.2.2))
      exact congrArg₂ (fun (x : T.V) (b : Pl.R.B) => x ⊗ₜ[ℚ_[l]] b) (hT g v) h1
  obtain ⟨y, rfl⟩ := hx
  simp only [Finset.prod_singleton, ZMod.val_zero, pow_zero, map_one, map_sub, Polynomial.aeval_X]
  exact sub_eq_zero.2 (key y)

omit [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] in
variable (O K G l) in

theorem finrank_unitLat : Module.finrank O ↥(unitLat G : LocLat G ℚ_[l] K O).L.T = 1 := by
  have : Nontrivial O := (algebraMap O K).domain_nontrivial
  exact (LinearEquiv.ofInjective (Algebra.linearMap O K) IsUnitBall.inj).finrank_eq.symm.trans
    (Module.finrank_self O)

example {LL : FinExt l} [HasUnr a LL] [TameDescentExponentData ↥LL.1 l e a] :
    (unitPack (a := a) ϖ 1 2 (unitLat (Gl l) : QLat LL) fun _ _ => rfl).n = 1 :=
  finrank_unitLat l ↥(OL LL) ↥LL.1 (Gl l)

end GlobalTheory.BKGal.UnitModel
