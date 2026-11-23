import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.XiQuotientInvariantsLiftRationally
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteDimensionalKsOfGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamSubrepQuotientAndStrictness
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamRepresentationTensorComparison
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData

section

noncomputable section

namespace GlobalTheory.CompanionTheory.TBOne

open TensorProduct Module GlobalTheory.InvariantLift

section Abstract

variable {R F T V B M : Type} [CommRing R] [Field F] [Algebra R F] [AddCommGroup T] [Module R T]
  [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B] [AddCommGroup M] [Module R M]

theorem cob_core {ι : Type} [Fintype ι] (bT : Basis ι R T) (bV : Basis ι F V)
    (i : T →+ V) (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (β : M →+ B)
    (hβ : ∀ (c : R) m, β (c • m) = algebraMap R F c • β m) (hb : ∀ k, i (bT k) = bV k)
    (r : R) (Sa Sb : Submodule F B) (Nb : Submodule R M)
    (hbb : ∀ m, β m ∈ Sb ↔ m ∈ Nb)
    (hden : ∀ x ∈ Sa, ∃ (k : ℕ) (m : M), algebraMap R F r ^ k • x - β m ∈ Sb)
    {G : Type} (ρT : G → T →ₗ[R] T) (ρM : G → M →ₗ[R] M) (ρV : G → V →ₗ[F] V) (ρB : G → B →ₗ[F] B)
    (hiρ : ∀ g t, i (ρT g t) = ρV g (i t)) (hβρ : ∀ g m, β (ρM g m) = ρB g (β m))
    (hSb : ∀ g, ∀ x ∈ Sb, ρB g x ∈ Sb)
    (qb : G → (M ⧸ Nb) →ₗ[R] (M ⧸ Nb))
    (hqb : ∀ g m, qb g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρM g m))
    (y : V ⊗[F] B) (hy : y ∈ LinearMap.range (LinearMap.lTensor V Sa.subtype))
    (c : G → T) (one : M)
    (hc : ∀ g, TensorProduct.map (ρV g) (ρB g) y - y = i (c g) ⊗ₜ[F] β one) :
    ∃ (k : ℕ) (x : T ⊗[R] (M ⧸ Nb)), ∀ g,
      r ^ k • (c g ⊗ₜ[R] (Submodule.Quotient.mk one : M ⧸ Nb)) =
        TensorProduct.map (ρT g) (qb g) x - x := by
  classical
  set Φ := Phi i hi β hβ with hΦ
  have hco : ∀ x k, co bV k (Φ x) = β (co bT k x) := co_Phi bT bV i hi β hβ hb
  have hker : ∀ x, Φ x ∈ LinearMap.range (LinearMap.lTensor V Sb.subtype) ↔
      LinearMap.lTensor T Nb.mkQ x = 0 := by
    intro x
    rw [← LinearMap.mem_ker, lTensor_mkQ, mem_range_iff bV, mem_range_iff bT]
    simp only [hco, hbb]
  have hequi : ∀ g x, Φ (TensorProduct.map (ρT g) (ρM g) x) =
      TensorProduct.map (ρV g) (ρB g) (Φ x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t m => simp only [hΦ, map_tmul, Phi_tmul, hiρ, hβρ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsm : ∀ (c : R) x, Φ (c • x) = algebraMap R F c • Φ x := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t m => rw [smul_tmul', hΦ, Phi_tmul, Phi_tmul, hi, smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  have hq : ∀ g x,
      TensorProduct.map (ρT g) (qb g) (LinearMap.lTensor T Nb.mkQ x) =
        LinearMap.lTensor T Nb.mkQ (TensorProduct.map (ρT g) (ρM g) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t m => simp [hqb]
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [mem_range_iff bV] at hy
  choose n m hm using fun k => hden _ (hy k)
  set N := ∑ k, n k with hN
  have hle : ∀ k, n k ≤ N := fun k =>
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  set x' : T ⊗[R] M := ∑ k, bT k ⊗ₜ[R] (r ^ (N - n k) • m k) with hx'
  have hx : algebraMap R F r ^ N • y - Φ x' ∈ LinearMap.range (LinearMap.lTensor V Sb.subtype) := by
    rw [mem_range_iff bV]
    intro k
    rw [map_sub, map_smul, hco, hx', co_sum, hβ, map_pow]
    have := Sb.smul_mem (algebraMap R F r ^ (N - n k)) (hm k)
    rwa [smul_sub, smul_smul, ← pow_add, Nat.sub_add_cancel (hle k)] at this
  refine ⟨N, LinearMap.lTensor T Nb.mkQ x', fun g => ?_⟩
  have h1 : TensorProduct.map (ρV g) (ρB g) (algebraMap R F r ^ N • y - Φ x') ∈
      LinearMap.range (LinearMap.lTensor V Sb.subtype) := by
    obtain ⟨u, hu⟩ := hx
    rw [← hu]
    clear hu
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul t m => exact ⟨ρV g t ⊗ₜ[F] ⟨_, hSb g _ m.2⟩, rfl⟩
    | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
  have h2 : Φ (r ^ N • (c g ⊗ₜ[R] one)) = algebraMap R F r ^ N • (i (c g) ⊗ₜ[F] β one) := by
    rw [hsm, hΦ, Phi_tmul, map_pow]
  have h3 : LinearMap.lTensor T Nb.mkQ (r ^ N • (c g ⊗ₜ[R] one)) =
      r ^ N • (c g ⊗ₜ[R] (Submodule.Quotient.mk one : M ⧸ Nb)) := by
    rw [map_smul]; rfl
  rw [← h3, hq, ← map_sub, ← sub_eq_zero, ← map_sub, ← hker, map_sub, map_sub, hequi, h2, ← hc g]
  have e : ∀ (a : F) (y y' p p' : V ⊗[F] B),
      -((a • y - p) - (a • y' - p')) = a • (y' - y) - (p' - p) := by
    intro a y y' p p'
    rw [smul_sub]
    abel
  have h4 := Submodule.neg_mem _ (Submodule.sub_mem _ hx h1)
  rw [map_sub, map_smul, e] at h4
  exact h4

end Abstract

section Period

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

theorem exists_beta_unit (LT : LocTied l P AI) (J : ThetaL P AI) (K : FinExt l) (a : ℤ) :
    ∃ β : ↥(Mxi (AinfSub l) (xiU AI) a) →+ P.R.BdR,
      (∀ (c : ℤ_[l]) m, β (c • m) = algebraMap ℤ_[l] ℚ_[l] c • β m) ∧
      (∀ m, β m ∈ (P.PD K).Fil a) ∧
      (∀ b, a ≤ b → ∀ m, β m ∈ (P.PD K).Fil b ↔ (m : WCb l) ∈ Mxi (AinfSub l) (xiU AI) b) ∧
      (∀ b, a ≤ b → ∀ x ∈ (P.PD K).Fil a, ∃ (k : ℕ) (m : ↥(Mxi (AinfSub l) (xiU AI) a)),
        algebraMap ℤ_[l] ℚ_[l] (l : ℤ_[l]) ^ k • x - β m ∈ (P.PD K).Fil b) ∧
      (∀ (g : GQ l) (m m' : ↥(Mxi (AinfSub l) (xiU AI) a)), (m' : WCb l) = AI.actWCbHom g m →
        β m' = P.actQdR g (β m)) ∧
      (a = 0 → ∀ m : ↥(Mxi (AinfSub l) (xiU AI) a), (m : WCb l) = 1 → β m = 1) := by
  have hF : ∀ c x, x ∈ (P.PD K).Fil c ↔ x ∈ (P.PD (botExt l)).Fil c := fun c x => by
    rw [← SetLike.mem_coe, P.PD_Fil K (botExt l) c, SetLike.mem_coe]
  obtain ⟨-, -, w, hw, ht, -⟩ := GlobalTheory.BdRQuot.fil_quotient l P AI LT J 0
  have hunit : IsUnit (P.ιB P.tB) := by
    have := (P.PD (botExt l)).t_unit
    rw [P.period_datum_t_eq] at this
    exact this.map P.ιB
  rw [ht] at hunit
  obtain ⟨u, hu⟩ := isUnit_of_mul_isUnit_left hunit
  have H := zpow_mul_mem AI u hu J w hw ht a
  refine ⟨beta AI u a, beta_smul AI u LT a, ?_, ?_, ?_, beta_act AI u hu a, ?_⟩
  · intro m
    obtain ⟨y, rfl⟩ := (eE AI a).surjective m
    rw [hF, beta_eE]
    have := (H 0 (iD AI y)).mpr (AI.ainf_image_mem_filtration_zero (botExt l) y)
    rwa [zero_add] at this
  · intro b hab m
    obtain ⟨n, rfl⟩ := Int.exists_add_of_le hab
    obtain ⟨y, rfl⟩ := (eE AI a).surjective m
    obtain ⟨-, h2, -⟩ := GlobalTheory.BdRQuot.fil_quotient l P AI LT J n
    rw [hF, beta_eE, add_comm a, H, iD_apply, h2, eE_coe]
    have key : ∀ y' : Ainf l, (((xiU AI) ^ ((n : ℤ) + a) : (WCb l)ˣ) : WCb l) * inclW l y' =
        (((xiU AI) ^ a : (WCb l)ˣ) : WCb l) * inclW l (AI.ξ ^ n * y') := by
      intro y'
      rw [zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val, xiU_coe, map_mul, map_pow]
      ring
    constructor
    · rintro ⟨y', rfl⟩
      exact ⟨inclW l y', ⟨y', rfl⟩, key y'⟩
    · rintro ⟨_, ⟨y', rfl⟩, h⟩
      refine ⟨y', inclW_inj (((xiU AI) ^ a).isUnit.mul_left_cancel ?_)⟩
      rw [← key]
      exact h.symm
  · intro b hab x hx
    obtain ⟨n, rfl⟩ := Int.exists_add_of_le hab
    obtain ⟨h1, -, -⟩ := GlobalTheory.BdRQuot.fil_quotient l P AI LT J n
    have hx' : (((u ^ a)⁻¹ : (P.R.BdR)ˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil 0 := by
      rw [← H 0, ← mul_assoc, Units.mul_inv, one_mul, zero_add, ← hF]
      exact hx
    obtain ⟨k, y, hy⟩ := h1 _ hx'
    refine ⟨k, eE AI a y, ?_⟩
    rw [← H, add_comm, ← hF] at hy
    convert hy using 1
    rw [beta_eE, mul_sub, iD_apply, mul_left_comm, ← mul_assoc _ _ x, Units.mul_inv, one_mul,
      map_natCast, Algebra.smul_def, map_pow, map_natCast]
  · rintro rfl m hm
    obtain ⟨y, rfl⟩ := (eE AI 0).surjective m
    have h1 : inclW l y = 1 := by
      have := hm
      rw [eE_coe] at this
      simpa using this
    have h2 : y = 1 := inclW_inj (h1.trans (map_one _).symm)
    rw [beta_eE, h2]
    simp

end Period

section Main

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l}

section Fil

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V V' : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    [AddCommGroup V'] [Module LL V'] [Module Qp V'] [IsScalarTower Qp LL V']

theorem map_mem_filV (φ : V →ₗ[LL] V') (a : ℤ) (x : V ⊗[Qp] BdR)
    (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    AlgebraTensorModule.map φ (LinearMap.id : BdR →ₗ[Qp] BdR) x ∈
      FilV PD (LL := LL) (V := V') a := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨AlgebraTensorModule.map φ (LinearMap.id : _ →ₗ[Qp] _) w, ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem mem_range_of_filV (a : ℤ) (x : V ⊗[Qp] BdR) (hx : x ∈ FilV PD (LL := LL) (V := V) a) :
    x ∈ LinearMap.range (LinearMap.lTensor V ((PD.Fil a).restrictScalars Qp).subtype) := by
  obtain ⟨w, rfl⟩ := hx
  refine ⟨w, ?_⟩
  induction w using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem map_eq_actVdR (ρ : Representation LL G V) (g : G) (x : V ⊗[Qp] BdR) :
    TensorProduct.map ((ρ g).restrictScalars Qp) ((PD.actdR g).toLinearMap.restrictScalars Qp) x =
      actVdR PD ρ g x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Fil

set_option maxHeartbeats 4000000 in

theorem exists_rational (AI : LocAinf l P) (LT : LocTied l P AI) (K LL : FinExt l)
    (h1F : (1 : P.R.BdR) ∈ (P.PD K).Fil 0)
    (Yt T Z : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (hse : IsSESLat (Qp := ℚ_[l]) ι π) (hZ : ∀ g x, Z.ρ g x = x) (hdR : IsDR (P.PD K) Yt.ρ)
    (yt : Yt.V) (f : ↥(GK K) → ↥T.L.T) (hf : ∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt) :
    ∃ w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 0, ∀ g : ↥(GK K),
      actVdR (P.PD K) T.ρ g w - w = (f g : T.V) ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
  obtain ⟨hi, hs, -, hk, -⟩ := hse
  have hk' : LinearMap.range ι.f = LinearMap.ker π.f := by
    ext x
    rw [LinearMap.mem_ker, hk, LinearMap.mem_range]
  have hone' : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] ↥LL.1 W] (v : W),
      v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) ∈ FilV (P.PD K) (LL := ↥LL.1) (V := W) 0 := by
    intro W _ _ _ _ v
    exact ⟨v ⊗ₜ[ℚ_[l]] ⟨1, h1F⟩, rfl⟩
  have hact : ∀ (W : Type) [AddCommGroup W] [Module ↥LL.1 W] [Module ℚ_[l] W]
      [IsScalarTower ℚ_[l] ↥LL.1 W] (ρ : Representation ↥LL.1 ↥(GK K) W) (g : ↥(GK K)) (v : W),
      actVdR (P.PD K) ρ g (v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) = ρ g v ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) := by
    intro W _ _ _ _ ρ g v
    simp [actVdR]
  obtain ⟨-, hst⟩ := (GlobalTheory.DRSubQuot.deRham_sub_quot l P AI LT K LL Yt.V Yt.ρ Z.V Z.ρ π.f π.equiv).2 hs hdR
  have hz2 : π.f yt ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) ∈
      DdR (P.PD K) Z.ρ ⊓ FilV (P.PD K) (LL := ↥LL.1) (V := Z.V) 0 := by
    refine ⟨?_, hone' _ _⟩
    refine (Submodule.mem_iInf _).mpr fun g => ?_
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, hact, hZ, sub_self]
  obtain ⟨x1, ⟨hx1D, hx1F⟩, hx1π⟩ := hst 0 _ hz2
  have hx1G : ∀ g, actVdR (P.PD K) Yt.ρ g x1 = x1 := by
    intro g
    have := (Submodule.mem_iInf _).mp hx1D g
    rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
  obtain ⟨t1, t2⟩ := GlobalTheory.Per.ExactMult.tensor_exact (Qp := ℚ_[l]) (BdR := P.R.BdR) ι.f π.f hi hs hk'
  set u : Yt.V ⊗[ℚ_[l]] P.R.BdR := yt ⊗ₜ[ℚ_[l]] (1 : P.R.BdR) - x1 with hu
  have hu0 : u ∈ LinearMap.ker (AlgebraTensorModule.map π.f (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR)) := by
    rw [LinearMap.mem_ker, hu, map_sub, hx1π, AlgebraTensorModule.map_tmul, LinearMap.id_apply, sub_self]
  rw [← t2] at hu0
  obtain ⟨w, hw⟩ := hu0
  obtain ⟨r, hr⟩ := ι.f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hi)
  have hwr : w = AlgebraTensorModule.map r (LinearMap.id : P.R.BdR →ₗ[ℚ_[l]] P.R.BdR) u := by
    rw [← hw]
    clear hw
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul v b =>
      have : r (ι.f v) = v := LinearMap.congr_fun hr v
      simp [this]
    | add x y hx hy => simp only [map_add, ← hx, ← hy]
  refine ⟨w, ?_, fun g => ?_⟩
  · rw [hwr]
    exact map_mem_filV (P.PD K) r 0 u (Submodule.sub_mem _ (hone' _ _) hx1F)
  · apply t1
    rw [map_sub, GlobalTheory.Per.ExactMult.map_act (P.PD K) T.ρ Yt.ρ ι.f ι.equiv g w, hw, hu, map_sub, hact,
      hx1G, AlgebraTensorModule.map_tmul, LinearMap.id_apply, hf, sub_tmul]
    abel

set_option maxHeartbeats 4000000 in

theorem cob_of_rational (AI : LocAinf l P) (K LL : FinExt l)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (f : ↥(GK K) → ↥T.L.T)
    (e j : ℕ) (hle : Gj K j ≤ GK K)
    (one : ↥(Mxi (AinfSub l) (xiU AI) 0))
    (β : ↥(Mxi (AinfSub l) (xiU AI) 0) →+ P.R.BdR)
    (b1 : ∀ (c : ℤ_[l]) m, β (c • m) = algebraMap ℤ_[l] ℚ_[l] c • β m)
    (b3 : ∀ m, β m ∈ (P.PD K).Fil ((e : ℤ) + 1) ↔
      (m : WCb l) ∈ Mxi (AinfSub l) (xiU AI) ((e : ℤ) + 1))
    (b4 : ∀ x ∈ (P.PD K).Fil 0, ∃ (k : ℕ) (m : ↥(Mxi (AinfSub l) (xiU AI) 0)),
        algebraMap ℤ_[l] ℚ_[l] (l : ℤ_[l]) ^ k • x - β m ∈ (P.PD K).Fil ((e : ℤ) + 1))
    (b5 : ∀ (g : GQ l) (m m' : ↥(Mxi (AinfSub l) (xiU AI) 0)), (m' : WCb l) = AI.actWCbHom g m →
        β m' = P.actQdR g (β m))
    (hβ1 : β one = 1)
    (w : T.V ⊗[ℚ_[l]] P.R.BdR) (hwF : w ∈ FilV (P.PD K) (LL := ↥LL.1) (V := T.V) 0)
    (hcob : ∀ g : ↥(GK K), actVdR (P.PD K) T.ρ g w - w = (f g : T.V) ⊗ₜ[ℚ_[l]] (1 : P.R.BdR)) :
    letI := zlMod LL T
    ∃ k : ℕ, IsCob (repQ AI (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 ((e : ℤ) + 1)))) := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := modTopLL LL
  haveI := finOL LL
  letI := zlMod LL T
  obtain ⟨n, bT, bV, hb⟩ := lat_bases (R := ℤ_[l]) (F := ℚ_[l]) (LL := ↥LL.1) (O := ↥(OL LL))
    (fun _ => rfl) (denom LL) T
  have hX : XiOK (AinfSub l) (AI.actWCbHom.comp (Gj K j).subtype) (xiU AI) :=
    ⟨fun g x hx => (xiOK AI).1 (g : GQ l) x hx, (xiOK AI).2.1, fun g => (xiOK AI).2.2 (g : GQ l)⟩
  obtain ⟨k, x, hx⟩ := cob_core bT bV T.L.T.subtype.toAddMonoidHom
    (lat_smul (R := ℤ_[l]) (F := ℚ_[l]) (LL := ↥LL.1) (O := ↥(OL LL)) (fun _ => rfl) T) β b1 hb
    (l : ℤ_[l]) (((P.PD K).Fil 0).restrictScalars ℚ_[l])
    (((P.PD K).Fil ((e : ℤ) + 1)).restrictScalars ℚ_[l])
    ((Mxi (AinfSub l) (xiU AI) ((e : ℤ) + 1)).comap (Mxi (AinfSub l) (xiU AI) 0).subtype)
    b3 b4 (G := ↥(Gj K j))
    (fun g => (actTZ LL T).comp (Subgroup.inclusion hle) g) (fun g => actM hX 0 g)
    (fun g => (T.ρ (Subgroup.inclusion hle g)).restrictScalars ℚ_[l])
    (fun g => ((P.PD K).actdR (Subgroup.inclusion hle g)).toLinearMap.restrictScalars ℚ_[l])
    (fun _ _ => rfl)
    (fun g m => (b5 (g : GQ l) m _ rfl).trans (P.PD_actdR K (Subgroup.inclusion hle g) _).symm)
    (fun g x hx => (P.PD K).Fil_G (Subgroup.inclusion hle g) _ x hx)
    (fun g => actQab hX 0 ((e : ℤ) + 1) g) (fun _ _ => rfl)
    w (mem_range_of_filV (P.PD K) 0 w hwF) (fun g => f (Subgroup.inclusion hle g)) one
    (fun g => by
      rw [map_eq_actVdR (P.PD K) T.ρ, hcob, hβ1]
      rfl)
  exact ⟨k, x, fun g => hx g⟩

set_option maxHeartbeats 4000000 in

theorem cob_of_strict (AI : LocAinf l P) (LT : LocTied l P AI) (J : ThetaL P AI) (K LL : FinExt l)
    (Yt T Z : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L)
    (hse : IsSESLat (Qp := ℚ_[l]) ι π) (hZ : ∀ g x, Z.ρ g x = x) (hdR : IsDR (P.PD K) Yt.ρ)
    (yt : Yt.V) (f : ↥(GK K) → ↥T.L.T) (hf : ∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt)
    (e j : ℕ) (hle : Gj K j ≤ GK K)
    (one : ↥(Mxi (AinfSub l) (xiU AI) 0)) (hone : (one : WCb l) = 1) :
    letI := zlMod LL T
    ∃ k : ℕ, IsCob (repQ AI (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1))
      (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]]
        (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU AI) 0 ((e : ℤ) + 1)))) := by
  obtain ⟨β, b1, b2, b3, b4, b5, b6⟩ := exists_beta_unit AI LT J K 0
  have hβ1 : β one = 1 := b6 rfl one hone
  have h1F : (1 : P.R.BdR) ∈ (P.PD K).Fil 0 := hβ1 ▸ b2 one
  have hpos : (0 : ℤ) ≤ (e : ℤ) + 1 := by omega
  obtain ⟨w, hwF, hcob⟩ := exists_rational AI LT K LL h1F Yt T Z ι π hse hZ hdR yt f hf
  exact cob_of_rational AI K LL T f e j hle one β b1 (b3 _ hpos) (b4 _ hpos) b5 hβ1 w hwF hcob

end Main

section Top

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem connecting_torsion : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (e : ℕ) (Yt T Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L) (hle : Gj K s ≤ GK K), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → IsCrysOn S S.W.GKs Yt → ∀ yt ∈ Yt.L.T, ∀ f : S.G → ↥T.L.T, (∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → letI := zlMod LL T; ∃ k : ℕ, IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) := by
  intro D HW F _ h7 l _ K s LL h S E e Yt T Z ι π hle hse hZ hcr yt _ f hf one hone
  obtain ⟨J⟩ := GlobalTheory.ThetaTie.nonempty_thetaL D l
  exact cob_of_strict (D.locA l) (D.locT l) J K LL Yt T Z ι π hse hZ
    (GlobalTheory.Cyc.CrysDeRham.isDR_of_isCrysOn D HW h7 l K s LL h Yt hcr) yt f hf e s hle one hone

end Top

end GlobalTheory.CompanionTheory.TBOne

end
end

section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc
theorem _root_.GlobalTheory.Adopt.ses_lattice_trivial_quotient : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (e : ℕ) (Yt T Z : LocLat S.G S.Qp S.LL S.O) (ι : LatHom T.L Yt.L) (π : LatHom Yt.L Z.L) (hle : Gj K s ≤ GK K), IsSESLat (Qp := S.Qp) ι π → (∀ g x, Z.ρ g x = x) → IsCrysOn S S.W.GKs Yt → ∀ yt ∈ Yt.L.T, ∀ f : S.G → ↥T.L.T, (∀ g, ι.f (f g : T.V) = Yt.ρ g yt - yt) → ∀ one : ↥(Mxi (AinfSub l) (xiU (D.locA l)) 0), (one : WCb l) = 1 → letI := zlMod LL T; ∃ k : ℕ, IsCob (repQ (D.locA l) (Gj K s) ((actTZ LL T).comp (Subgroup.inclusion hle)) 0 ((e : ℤ) + 1)) (fun g => (l : ℤ_[l]) ^ k • (f (Subgroup.inclusion hle g) ⊗ₜ[ℤ_[l]] (Submodule.Quotient.mk one : Qab (AinfSub l) (xiU (D.locA l)) 0 ((e : ℤ) + 1)))) := by
  first | exact @GlobalTheory.CompanionTheory.TBOne.connecting_torsion | exact GlobalTheory.CompanionTheory.TBOne.connecting_torsion | (intros; apply GlobalTheory.CompanionTheory.TBOne.connecting_torsion <;> assumption)

end
