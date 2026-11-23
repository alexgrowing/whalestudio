import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamFilQuotientXiPowerAinf
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyThetaOnBdRPlusPeriodData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankCyclotomicExtAndCyclotomicCharSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharacterPadicBasicProperties
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface

noncomputable section

namespace GlobalTheory.InvariantLift

open TensorProduct Module

section Coord

variable {R T M ι : Type} [CommRing R] [AddCommGroup T] [Module R T] [AddCommGroup M] [Module R M]
  [Fintype ι] (b : Basis ι R T)

def co (k : ι) : T ⊗[R] M →ₗ[R] M :=
  (TensorProduct.lid R M).toLinearMap ∘ₗ LinearMap.rTensor M (b.coord k)

omit [Fintype ι] in
theorem co_tmul (k : ι) (t : T) (m : M) : co b k (t ⊗ₜ[R] m) = b.repr t k • m := by
  simp [co]

theorem sum_co (x : T ⊗[R] M) : ∑ k, b k ⊗ₜ[R] co b k x = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul t m =>
    simp only [co_tmul, ← smul_tmul]
    rw [← sum_tmul, b.sum_repr]
  | add x y hx hy => simp only [map_add, tmul_add, Finset.sum_add_distrib, hx, hy]

theorem mem_range_iff (S : Submodule R M) (x : T ⊗[R] M) :
    x ∈ LinearMap.range (LinearMap.lTensor T S.subtype) ↔ ∀ k, co b k x ∈ S := by
  constructor
  · rintro ⟨u, rfl⟩ k
    induction u using TensorProduct.induction_on with
    | zero => simp
    | tmul t m =>
      rw [LinearMap.lTensor_tmul, co_tmul]
      exact S.smul_mem _ m.2
    | add x y hx hy => rw [map_add, map_add]; exact S.add_mem hx hy
  · intro h
    rw [← sum_co b x]
    exact Submodule.sum_mem _ fun k _ => ⟨b k ⊗ₜ[R] ⟨_, h k⟩, rfl⟩

theorem co_sum [DecidableEq ι] (m : ι → M) (k : ι) : co b k (∑ j, b j ⊗ₜ[R] m j) = m k := by
  simp [map_sum, co_tmul, Finsupp.single_apply]

end Coord

section Abstract

variable {R F T V B M : Type} [CommRing R] [Field F] [Algebra R F] [AddCommGroup T] [Module R T]
  [AddCommGroup V] [Module F V] [AddCommGroup B] [Module F B] [AddCommGroup M] [Module R M]

def Phi (i : T →+ V) (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (β : M →+ B)
    (hβ : ∀ (c : R) m, β (c • m) = algebraMap R F c • β m) : T ⊗[R] M →+ V ⊗[F] B :=
  TensorProduct.liftAddHom
    (AddMonoidHom.mk' (fun t => AddMonoidHom.mk' (fun m => i t ⊗ₜ[F] β m)
      (fun m m' => by rw [map_add, tmul_add]))
      (fun t t' => by ext m; simp [add_tmul]))
    (fun c t m => by simp [hi, hβ, smul_tmul])

theorem Phi_tmul (i : T →+ V) (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (β : M →+ B)
    (hβ : ∀ (c : R) m, β (c • m) = algebraMap R F c • β m) (t : T) (m : M) :
    Phi i hi β hβ (t ⊗ₜ[R] m) = i t ⊗ₜ[F] β m := by
  simp [Phi]

theorem co_Phi {ι : Type} [Fintype ι] (bT : Basis ι R T) (bV : Basis ι F V)
    (i : T →+ V) (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (β : M →+ B)
    (hβ : ∀ (c : R) m, β (c • m) = algebraMap R F c • β m) (hb : ∀ k, i (bT k) = bV k)
    (x : T ⊗[R] M) (k : ι) : co bV k (Phi i hi β hβ x) = β (co bT k x) := by
  classical
  conv_lhs => rw [← sum_co bT x]
  rw [map_sum]
  simp only [Phi_tmul, hb]
  exact co_sum bV _ k

theorem core {ι : Type} [Fintype ι] (bT : Basis ι R T) (bV : Basis ι F V)
    (i : T →+ V) (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (β : M →+ B)
    (hβ : ∀ (c : R) m, β (c • m) = algebraMap R F c • β m) (hb : ∀ k, i (bT k) = bV k)
    (r : R) (Sa Se Sb : Submodule F B) (Ne Nb : Submodule R M) (hbe : Sb ≤ Se)
    (ha : ∀ m, β m ∈ Sa) (he : ∀ m, β m ∈ Se ↔ m ∈ Ne) (hbb : ∀ m, β m ∈ Sb ↔ m ∈ Nb)
    (hden : ∀ x ∈ Sa, ∃ (k : ℕ) (m : M), algebraMap R F r ^ k • x - β m ∈ Sb)
    {G : Type} (ρT : G → T →ₗ[R] T) (ρM : G → M →ₗ[R] M) (ρV : G → V →ₗ[F] V) (ρB : G → B →ₗ[F] B)
    (hiρ : ∀ g t, i (ρT g t) = ρV g (i t)) (hβρ : ∀ g m, β (ρM g m) = ρB g (β m))
    (hSb : ∀ g, ∀ x ∈ Sb, ρB g x ∈ Sb)
    (qe : G → (M ⧸ Ne) →ₗ[R] (M ⧸ Ne)) (hqe : ∀ g m, qe g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρM g m))
    (qb : G → (M ⧸ Nb) →ₗ[R] (M ⧸ Nb)) (hqb : ∀ g m, qb g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρM g m))
    (ht : ∀ y ∈ LinearMap.range (LinearMap.lTensor V Sa.subtype),
      (∀ g, TensorProduct.map (ρV g) (ρB g) y - y ∈ LinearMap.range (LinearMap.lTensor V Se.subtype)) →
      ∃ w, (∀ g, TensorProduct.map (ρV g) (ρB g) w = w) ∧
        w ∈ LinearMap.range (LinearMap.lTensor V Sa.subtype) ∧
        y - w ∈ LinearMap.range (LinearMap.lTensor V Se.subtype))
    (p : (M ⧸ Nb) →ₗ[R] (M ⧸ Ne)) (hp : ∀ m, p (Submodule.Quotient.mk m) = Submodule.Quotient.mk m)
    (z : T ⊗[R] (M ⧸ Ne)) (hz : ∀ g, TensorProduct.map (ρT g) (qe g) z = z) :
    ∃ (k : ℕ) (x : T ⊗[R] (M ⧸ Nb)), (∀ g, TensorProduct.map (ρT g) (qb g) x = x) ∧
      LinearMap.lTensor T p x = r ^ k • z := by
  classical
  set Φ := Phi i hi β hβ with hΦ
  have hco : ∀ x k, co bV k (Φ x) = β (co bT k x) := co_Phi bT bV i hi β hβ hb
  have hker : ∀ (S : Submodule F B) (N : Submodule R M), (∀ m, β m ∈ S ↔ m ∈ N) → ∀ x,
      Φ x ∈ LinearMap.range (LinearMap.lTensor V S.subtype) ↔ LinearMap.lTensor T N.mkQ x = 0 := by
    intro S N h x
    rw [← LinearMap.mem_ker, lTensor_mkQ, mem_range_iff bV, mem_range_iff bT]
    simp only [hco, h]
  have hequi : ∀ g x, Φ (TensorProduct.map (ρT g) (ρM g) x) = TensorProduct.map (ρV g) (ρB g) (Φ x) := by
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
  have hq : ∀ (N : Submodule R M) (q : G → (M ⧸ N) →ₗ[R] (M ⧸ N)),
      (∀ g m, q g (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρM g m)) → ∀ g x,
      TensorProduct.map (ρT g) (q g) (LinearMap.lTensor T N.mkQ x) =
        LinearMap.lTensor T N.mkQ (TensorProduct.map (ρT g) (ρM g) x) := by
    intro N q h g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul t m => simp [h]
    | add x y hx hy => simp only [map_add, hx, hy]
  obtain ⟨z', rfl⟩ := LinearMap.lTensor_surjective T Ne.mkQ_surjective z
  obtain ⟨w, hwG, hwa, hwe⟩ := ht (Φ z') (by
      rw [mem_range_iff bV]; intro k; rw [hco]; exact ha _) (by
      intro g
      rw [← hequi, ← map_sub, hker Se Ne he, map_sub, ← hq Ne qe hqe, hz, sub_self])
  rw [mem_range_iff bV] at hwa
  choose n m hm using fun k => hden _ (hwa k)
  set N := ∑ k, n k with hN
  have hle : ∀ k, n k ≤ N := fun k => Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  set x' : T ⊗[R] M := ∑ k, bT k ⊗ₜ[R] (r ^ (N - n k) • m k) with hx'
  have hx : algebraMap R F r ^ N • w - Φ x' ∈ LinearMap.range (LinearMap.lTensor V Sb.subtype) := by
    rw [mem_range_iff bV]
    intro k
    rw [map_sub, map_smul, hco, hx', co_sum, hβ, map_pow]
    have := Sb.smul_mem (algebraMap R F r ^ (N - n k)) (hm k)
    rwa [smul_sub, smul_smul, ← pow_add, Nat.sub_add_cancel (hle k)] at this
  refine ⟨N, LinearMap.lTensor T Nb.mkQ x', fun g => ?_, ?_⟩
  · rw [hq Nb qb hqb, ← sub_eq_zero, ← map_sub, ← hker Sb Nb hbb, map_sub, hequi]
    have h1 : TensorProduct.map (ρV g) (ρB g) (algebraMap R F r ^ N • w - Φ x') ∈
        LinearMap.range (LinearMap.lTensor V Sb.subtype) := by
      obtain ⟨u, hu⟩ := hx
      rw [← hu]
      clear hu
      induction u using TensorProduct.induction_on with
      | zero => simp
      | tmul t m => exact ⟨ρV g t ⊗ₜ[F] ⟨_, hSb g _ m.2⟩, rfl⟩
      | add x y hx hy => rw [map_add, map_add]; exact Submodule.add_mem _ hx hy
    rw [map_sub, map_smul, hwG] at h1
    have := Submodule.sub_mem _ hx h1
    convert this using 1
    abel
  · have h2 : LinearMap.lTensor T p (LinearMap.lTensor T Nb.mkQ x') = LinearMap.lTensor T Ne.mkQ x' := by
      rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
      congr 2
      ext m
      exact hp m
    rw [h2, ← map_smul, ← sub_eq_zero, ← map_sub, ← hker Se Ne he, map_sub, hsm, map_pow]
    have h3 : algebraMap R F r ^ N • w - Φ x' ∈ LinearMap.range (LinearMap.lTensor V Se.subtype) := by
      rw [mem_range_iff bV] at hx ⊢
      exact fun k => hbe (hx k)
    have := Submodule.neg_mem _ (Submodule.add_mem _ h3 (Submodule.smul_mem _ (algebraMap R F r ^ N) hwe))
    convert this using 1
    rw [smul_sub]
    abel

end Abstract

section Period

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation
open scoped Formalism.Per

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P)

def iD : Ainf l →+* P.R.BdR := (P.ιB : P.R.B →+* P.R.BdR).comp AI.ιA

theorem iD_apply (a : Ainf l) : iD AI a = P.ιB (AI.ιA a) := rfl

theorem iD_act (g : GQ l) (a : Ainf l) : iD AI (AI.actWHom g a) = P.actQdR g (iD AI a) := by
  have h2 : AI.ιA (AI.actWHom g a) = P.actQ g (AI.ιA a) := AI.ιA_act g a
  have h3 := (P.PD (botExt l)).ι_comm ⟨g, mem_GK_bot g⟩ (AI.ιA a)
  rw [P.PD_ι, P.PD_ι, P.PD_actB, P.PD_actdR] at h3
  rw [iD_apply, iD_apply, h2, h3]

theorem iD_zl (LT : LocTied l P AI) (c : ℤ_[l]) :
    iD AI (algebraMap ℤ_[l] (Ainf l) c) = algebraMap ℚ_[l] P.R.BdR (c : ℚ_[l]) := by
  have h : AI.ιA (algebraMap ℤ_[l] (Ainf l) c) = algebraMap ℚ_[l] P.R.B (c : ℚ_[l]) := by
    apply LT.eB.injective
    rw [LT.ιA, LT.zB]
    exact GlobalTheory.RingIface.aB_algebraMap_padicInt l c
  rw [iD_apply, h, AlgHom.commutes]

theorem inclW_inj : Function.Injective (inclW l) :=
  WittVector.map_injective _ (IsFractionRing.injective (OCb l) (Cb l))

def eM (a : ℤ) : Ainf l →ₗ[ℤ_[l]] ↥(Mxi (AinfSub l) (xiU AI) a) :=
  LinearMap.codRestrict _
    ((LinearMap.mulLeft ℤ_[l] (((xiU AI) ^ a : (WCb l)ˣ) : WCb l)) ∘ₗ (inclWA l).toLinearMap)
    (fun y => ⟨inclWA l y, ⟨y, rfl⟩, rfl⟩)

theorem eM_coe (a : ℤ) (y : Ainf l) :
    (eM AI a y : WCb l) = (((xiU AI) ^ a : (WCb l)ˣ) : WCb l) * inclW l y := rfl

theorem eM_bij (a : ℤ) : Function.Bijective (eM AI a) := by
  constructor
  · intro y y' h
    have h1 := congrArg (fun m : ↥(Mxi (AinfSub l) (xiU AI) a) => (m : WCb l)) h
    simp only [eM_coe] at h1
    exact inclW_inj ((Units.isUnit _).mul_left_cancel h1)
  · rintro ⟨x, y, ⟨y', rfl⟩, rfl⟩
    exact ⟨y', rfl⟩

def eE (a : ℤ) : Ainf l ≃ₗ[ℤ_[l]] ↥(Mxi (AinfSub l) (xiU AI) a) :=
  LinearEquiv.ofBijective (eM AI a) (eM_bij AI a)

theorem eE_coe (a : ℤ) (y : Ainf l) :
    (eE AI a y : WCb l) = (((xiU AI) ^ a : (WCb l)ˣ) : WCb l) * inclW l y := rfl

theorem xiU_coe : ((xiU AI : (WCb l)ˣ) : WCb l) = inclW l AI.ξ := rfl

variable (u : (P.R.BdR)ˣ)

def beta (a : ℤ) : ↥(Mxi (AinfSub l) (xiU AI) a) →+ P.R.BdR :=
  (AddMonoidHom.mulLeft ((u ^ a : (P.R.BdR)ˣ) : P.R.BdR)).comp
    ((iD AI).toAddMonoidHom.comp (eE AI a).symm.toLinearMap.toAddMonoidHom)

theorem beta_eE (a : ℤ) (y : Ainf l) :
    beta AI u a (eE AI a y) = ((u ^ a : (P.R.BdR)ˣ) : P.R.BdR) * iD AI y := by
  simp [beta]

theorem beta_smul (LT : LocTied l P AI) (a : ℤ) (c : ℤ_[l]) (m : ↥(Mxi (AinfSub l) (xiU AI) a)) :
    beta AI u a (c • m) = algebraMap ℤ_[l] ℚ_[l] c • beta AI u a m := by
  obtain ⟨y, rfl⟩ := (eE AI a).surjective m
  rw [← map_smul, beta_eE, beta_eE, Algebra.smul_def, map_mul, iD_zl AI LT, Algebra.smul_def]
  change _ = algebraMap ℚ_[l] P.R.BdR (c : ℚ_[l]) * _
  ring

variable (hu : (u : P.R.BdR) = iD AI AI.ξ)
include hu

theorem beta_clear (a : ℤ) (N : ℕ) (hN : 0 ≤ a + N) (m : ↥(Mxi (AinfSub l) (xiU AI) a)) :
    ∃ y : Ainf l, inclW l AI.ξ ^ N * (m : WCb l) = inclW l y ∧
      (u : P.R.BdR) ^ N * beta AI u a m = iD AI y := by
  obtain ⟨y, rfl⟩ := (eE AI a).surjective m
  obtain ⟨n, hn⟩ := Int.eq_ofNat_of_zero_le hN
  refine ⟨AI.ξ ^ n * y, ?_, ?_⟩
  · rw [eE_coe, map_mul, map_pow, ← xiU_coe, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add, ← hn,
      add_comm]
  · rw [beta_eE, map_mul, map_pow, ← hu, ← mul_assoc, ← Units.val_pow_eq_pow_val,
      ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← zpow_natCast, ← zpow_natCast, ← zpow_add, ← hn,
      add_comm]

theorem beta_act (a : ℤ) (g : GQ l) (m m' : ↥(Mxi (AinfSub l) (xiU AI) a))
    (h : (m' : WCb l) = AI.actWCbHom g m) : beta AI u a m' = P.actQdR g (beta AI u a m) := by
  obtain ⟨N, hN⟩ : ∃ N : ℕ, 0 ≤ a + N := ⟨a.natAbs, by omega⟩
  obtain ⟨y0, h0, h0'⟩ := beta_clear AI u hu a N hN m
  obtain ⟨y1, h1, h1'⟩ := beta_clear AI u hu a N hN m'
  obtain ⟨b, hb⟩ := xi_dvd_act AI g AI.ξ ⟨1, (mul_one _).symm⟩
  have h2 := congrArg (AI.actWCbHom g) h0
  rw [map_mul, map_pow, inclW_act, inclW_act, hb, ← h, map_mul, mul_pow, mul_right_comm, h1,
    ← map_pow, ← map_mul] at h2
  have h3 := congrArg (iD AI) (inclW_inj h2)
  rw [iD_act, ← h0', map_mul, ← h1', map_mul, map_pow, map_pow] at h3
  have h4 : P.actQdR g u = u * iD AI b := by rw [hu, ← iD_act, hb, map_mul]
  have h5 : IsUnit (P.actQdR g u ^ N) := ((Units.isUnit u).map (P.actQdR g)).pow N
  apply h5.mul_left_cancel
  rw [← h3, h4]
  ring

theorem u_mul_mem (J : ThetaL P AI) (w : P.R.BdR) (hw : w ∈ (P.PD (botExt l)).Fil 0)
    (ht : P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w) (c : ℤ) (x : P.R.BdR) :
    (u : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil (c + 1) ↔ x ∈ (P.PD (botExt l)).Fil c := by
  constructor
  · intro h
    have h1 := (P.PD (botExt l)).Fil_mul _ _ _ _ hw h
    rw [zero_add, J.fil_succ_iff_mul_t] at h1
    obtain ⟨y, hy, hxy⟩ := h1
    have hunit : IsUnit (P.ιB P.tB) := by
      have := (P.PD (botExt l)).t_unit
      rw [P.period_datum_t_eq] at this
      exact this.map P.ιB
    have : x = y := by
      apply hunit.mul_left_cancel
      rw [← hxy, ht, hu, iD_apply]
      ring
    rwa [this]
  · intro h
    have h1 : (u : P.R.BdR) ∈ (P.PD (botExt l)).Fil 1 := by
      rw [hu, iD_apply]
      exact (AI.ainf_image_mem_filtration_one_iff (botExt l) AI.ξ).mpr ⟨1, (mul_one _).symm⟩
    rw [add_comm]
    exact (P.PD (botExt l)).Fil_mul _ _ _ _ h1 h

theorem zpow_mul_mem (J : ThetaL P AI) (w : P.R.BdR) (hw : w ∈ (P.PD (botExt l)).Fil 0)
    (ht : P.ιB P.tB = P.ιB (AI.ιA AI.ξ) * w) (a : ℤ) : ∀ (c : ℤ) (x : P.R.BdR),
    ((u ^ a : (P.R.BdR)ˣ) : P.R.BdR) * x ∈ (P.PD (botExt l)).Fil (c + a) ↔
      x ∈ (P.PD (botExt l)).Fil c := by
  have H := u_mul_mem AI u hu J w hw ht
  induction a using Int.induction_on with
  | zero => simp
  | succ k ih =>
    intro c x
    rw [zpow_add_one, Units.val_mul, mul_assoc, ← H c x, ← ih (c + 1),
      show c + ((k : ℤ) + 1) = c + 1 + k by ring]
  | pred k ih =>
    intro c x
    rw [zpow_sub_one, Units.val_mul, mul_assoc, show c + (-(k : ℤ) - 1) = c - 1 + -k by ring,
      ih (c - 1), ← H (c - 1), ← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

omit hu in

theorem exists_beta (LT : LocTied l P AI) (J : ThetaL P AI) (K : FinExt l) (a : ℤ) :
    ∃ β : ↥(Mxi (AinfSub l) (xiU AI) a) →+ P.R.BdR,
      (∀ (c : ℤ_[l]) m, β (c • m) = algebraMap ℤ_[l] ℚ_[l] c • β m) ∧
      (∀ m, β m ∈ (P.PD K).Fil a) ∧
      (∀ b, a ≤ b → ∀ m, β m ∈ (P.PD K).Fil b ↔ (m : WCb l) ∈ Mxi (AinfSub l) (xiU AI) b) ∧
      (∀ b, a ≤ b → ∀ x ∈ (P.PD K).Fil a, ∃ (k : ℕ) (m : ↥(Mxi (AinfSub l) (xiU AI) a)),
        algebraMap ℤ_[l] ℚ_[l] (l : ℤ_[l]) ^ k • x - β m ∈ (P.PD K).Fil b) ∧
      ∀ (g : GQ l) (m m' : ↥(Mxi (AinfSub l) (xiU AI) a)), (m' : WCb l) = AI.actWCbHom g m →
        β m' = P.actQdR g (β m) := by
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
  refine ⟨beta AI u a, beta_smul AI u LT a, ?_, ?_, ?_, beta_act AI u hu a⟩
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

end Period

section Bases

theorem exists_bases {R F T V : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R] [Field F]
    [Algebra R F] [IsFractionRing R F] [AddCommGroup T] [Module R T] [Module.Finite R T]
    [AddCommGroup V] [Module F V] (i : T →+ V)
    (hi : ∀ (c : R) t, i (c • t) = algebraMap R F c • i t) (hinj : Function.Injective i)
    (hsp : Submodule.span F (Set.range i) = ⊤) :
    ∃ (n : ℕ) (bT : Basis (Fin n) R T) (bV : Basis (Fin n) F V), ∀ k, i (bT k) = bV k := by
  letI : Module R V := Module.compHom V (algebraMap R F)
  haveI : IsScalarTower R F V := ⟨fun c x v => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  let j : T →ₗ[R] V := { toFun := i, map_add' := map_add i, map_smul' := hi }
  haveI : Module.IsTorsionFree R V := Module.IsTorsionFree.trans_faithfulSMul R F V
  haveI : Module.IsTorsionFree R T := Function.Injective.moduleIsTorsionFree j hinj (map_smul j)
  let bT := Module.finBasis R T
  have hli : LinearIndependent F (j ∘ bT) :=
    (LinearIndependent.iff_fractionRing R F).mp
      (bT.linearIndependent.map' j (LinearMap.ker_eq_bot.mpr hinj))
  have hs : ⊤ ≤ Submodule.span F (Set.range (j ∘ bT)) := by
    rw [← hsp, Submodule.span_le]
    rintro _ ⟨t, rfl⟩
    change j t ∈ _
    rw [← bT.sum_repr t, map_sum]
    refine Submodule.sum_mem _ fun k _ => ?_
    rw [map_smul]
    exact Submodule.smul_of_tower_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)
  exact ⟨_, bT, Basis.mk hli hs, fun k => by rw [Basis.mk_apply]; rfl⟩

end Bases

section Generic

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.N

variable {R F LL O G : Type} [CommRing R] [Field F] [Field LL] [CommRing O] [Algebra R F]
  [Algebra F LL] [Algebra O LL] [Algebra R O] [TopologicalSpace LL] [Group G] [TopologicalSpace G]

theorem lat_smul
    (hc : ∀ c, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (T : LocLat G F LL O) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∀ (c : R) (t : ↥T.L.T), T.L.T.subtype.toAddMonoidHom (c • t) =
      algebraMap R F c • T.L.T.subtype.toAddMonoidHom t := by
  intro c t
  change algebraMap R O c • (t : T.V) = algebraMap R F c • (t : T.V)
  rw [← algebraMap_smul LL (algebraMap R O c), ← algebraMap_smul LL (algebraMap R F c), hc]

theorem lat_bases [IsDomain R] [IsPrincipalIdealRing R] [IsFractionRing R F] [Module.Finite R O]
    (hc : ∀ c, algebraMap O LL (algebraMap R O c) = algebraMap F LL (algebraMap R F c))
    (hd : ∀ c : LL, ∃ (z : F) (a : O), c = z • algebraMap O LL a)
    (T : LocLat G F LL O) :
    letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
    ∃ (n : ℕ) (bT : Basis (Fin n) R ↥T.L.T) (bV : Basis (Fin n) F T.V),
      ∀ k, T.L.T.subtype.toAddMonoidHom (bT k) = bV k := by
  letI : Module R ↥T.L.T := Module.compHom ↥T.L.T (algebraMap R O)
  haveI : IsScalarTower R O ↥T.L.T := ⟨fun c x v => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  haveI : Module.Finite O ↥T.L.T := Module.Finite.iff_fg.mpr T.L.fg
  haveI : Module.Finite R ↥T.L.T := Module.Finite.trans O _
  refine exists_bases _ (lat_smul hc T) Subtype.val_injective ?_
  rw [eq_top_iff]
  have key : ∀ v ∈ Submodule.span LL (T.L.T : Set T.V), ∀ c : LL,
      c • v ∈ Submodule.span F (Set.range T.L.T.subtype.toAddMonoidHom) := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      intro c
      obtain ⟨z, a, rfl⟩ := hd c
      rw [smul_assoc, algebraMap_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨_, T.L.T.smul_mem _ hx⟩, rfl⟩)
    | zero => intro c; simp
    | add x y _ _ hx hy => intro c; rw [smul_add]; exact Submodule.add_mem _ (hx c) (hy c)
    | smul a x _ hx => intro c; rw [smul_smul]; exact hx _
  intro v _
  have := key v (by rw [T.L.span]; trivial) 1
  rwa [one_smul] at this

theorem modTop_trans [TopologicalSpace F] [IsTopologicalRing LL] [IsModuleTopology F LL] (V : Type)
    [AddCommGroup V] [Module LL V] [Module F V] [IsScalarTower F LL V] [FiniteDimensional LL V]
    [TopologicalSpace V] [IsModuleTopology LL V] : IsModuleTopology F V := by
  haveI : ContinuousAdd V := IsModuleTopology.toContinuousAdd LL V
  let e := (Module.finBasis LL V).equivFun
  let e' : (Fin (finrank LL V) → LL) ≃L[F] V :=
    { e.symm.restrictScalars F with
      continuous_toFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap
      continuous_invFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap }
  exact IsModuleTopology.iso e'

def resRep (R : Type) [CommRing R] [Algebra R F] [TopologicalSpace F] [IsTopologicalRing LL]
    [IsModuleTopology F LL] [FiniteDimensional F LL] {H : Type} [Group H] [TopologicalSpace H]
    (f : H →* G) (hf : Continuous f) (T : LocLat G F LL O) : GRep H F F R where
  V := T.V
  modLL := T.modQp
  modQp := T.modQp
  modO := Module.compHom T.V (algebraMap R F)
  towO := letI : Module R T.V := Module.compHom T.V (algebraMap R F)
    ⟨fun c x v => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  fd := Module.Finite.trans LL T.V
  mtop := modTop_trans (LL := LL) T.V
  csmul := ⟨fun c => by
    simpa only [algebraMap_smul] using continuous_const_smul (T := T.V) (algebraMap F LL c)⟩
  ρ :=
    { toFun := fun g => (T.ρ (f g)).restrictScalars F
      map_one' := by rw [map_one, map_one]; rfl
      map_mul' := fun g h => by rw [map_mul, map_mul]; rfl }
  cont := fun x => (T.cont x).comp hf

end Generic

section Lattice

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

variable {l : ℕ} [Fact l.Prime]

theorem denom (LL : FinExt l) (c : ↥LL.1) :
    ∃ (z : ℚ_[l]) (a : ↥(OL LL)), c = z • algebraMap ↥(OL LL) ↥LL.1 a := by
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have halg : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] ↥LL.1).mpr (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz, hint⟩ := halg.exists_integral_multiple
  have hz' : (z : ℚ_[l]) ≠ 0 := fun h => hz (Subtype.ext h)
  refine ⟨(z : ℚ_[l])⁻¹, ⟨z • c, hint⟩, ?_⟩
  change c = (z : ℚ_[l])⁻¹ • ((z : ℚ_[l]) • c)
  rw [smul_smul, inv_mul_cancel₀ hz', one_smul]

theorem finOL (LL : FinExt l) : Module.Finite ℤ_[l] ↥(OL LL) :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)

theorem modTopLL (LL : FinExt l) : IsModuleTopology ℚ_[l] ↥LL.1 :=
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  isModuleTopologyOfFiniteDimensional

theorem goodO : GoodO (Qp := ℚ_[l]) ℚ_[l] ℤ_[l] := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, inferInstance, inferInstance, inferInstance, ?_⟩
  exact PadicInt.isOpenEmbedding_coe.isOpen_range

theorem finKs (K : FinExt l) (s : ℕ) : FiniteDimensional ℚ_[l] ↥(Ks K s) := by
  classical
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) := FiniteDimensional.of_injective
    (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
    (IntermediateField.inclusion_injective (inf_le_left : K0 K ≤ K.1))
  have hpos : 0 < l ^ s := pow_pos (Fact.out : l.Prime).pos s
  haveI : Finite {x : Om l | x ^ (l ^ s) = 1} := by
    refine Set.Finite.to_subtype (Set.Finite.subset
      (Polynomial.nthRoots (l ^ s) (1 : Om l)).toFinset.finite_toSet ?_)
    intro x hx
    simpa [Polynomial.mem_nthRoots hpos] using hx
  haveI : FiniteDimensional ℚ_[l]
      ↥(IntermediateField.adjoin ℚ_[l] {x : Om l | x ^ (l ^ s) = 1}) :=
    IntermediateField.finiteDimensional_adjoin fun x _ =>
      (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  exact IntermediateField.finiteDimensional_sup _ _

def lev (K : FinExt l) (j : ℕ) : FinExt l := ⟨Ks K j, finKs K j⟩

theorem finrank_maxUnramified_cyclotomicLevel (K : FinExt l) (j : ℕ) (hj : 1 ≤ j) :
    finrank ℚ_[l] ↥(K0 (lev K j)) = finrank ℚ_[l] ↥(K0 K) := by
  have h1 := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l K).1 j hj
  have h2 := (GlobalTheory.Cyc.finrank_Ks_and_chi_surjective l (lev K j)).1 j hj
  have h3 : Ks (lev K j) j = Ks K j := by
    apply le_antisymm
    · exact sup_le inf_le_left le_sup_right
    · refine sup_le (le_sup_of_le_left (le_inf ?_ inf_le_right)) le_sup_right
      exact le_sup_left
  rw [h3, h1] at h2
  have hl : 2 ≤ l := (Fact.out : l.Prime).two_le
  have hpos : 0 < (l - 1) * l ^ (j - 1) := Nat.mul_pos (by omega) (by positivity)
  exact (Nat.eq_of_mul_eq_mul_right hpos h2).symm

theorem le_val (P : LocPrime l) (LL : FinExt l) (s : ℕ) (x : ℚ_[l]) (hx : ‖x‖ ≤ (l : ℝ) ^ (-(s : ℤ))) :
    (s : WithTop ℚ) ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 x) := by
  have hl0 : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hlR : (0 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).pos
  have h1 : ‖x / (l : ℚ_[l]) ^ s‖ ≤ 1 := by
    rw [norm_div, norm_pow, Padic.norm_p, div_le_one (by positivity), inv_pow]
    simpa using hx
  have h2 : 0 ≤ P.v LL (algebraMap ℚ_[l] ↥LL.1 (x / (l : ℚ_[l]) ^ s)) := by
    rw [P.v_O]
    exact (OL LL).algebraMap_mem (⟨_, h1⟩ : ℤ_[l])
  have h3 : x = (l : ℚ_[l]) ^ s * (x / (l : ℚ_[l]) ^ s) := by field_simp
  rw [h3, map_mul, map_pow, map_natCast, AddValuation.map_mul, AddValuation.map_pow, P.v_l]
  have : (s : WithTop ℚ) = s • (1 : WithTop ℚ) := by simp
  rw [← this]
  exact le_add_of_nonneg_right h2

end Lattice

section Crys

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.N Formalism.MainNotions.LocalSituation

variable {R F LL O G H : Type} [CommRing R] [Field F] [Field LL] [CommRing O] [Algebra R F]
  [Algebra F LL] [Algebra O LL] [TopologicalSpace LL] [Group G] [TopologicalSpace G]
  [Group H] [TopologicalSpace H] [TopologicalSpace F] [IsTopologicalRing LL]
  [IsModuleTopology F LL] [FiniteDimensional F LL]
  {K₀ K K₀' K' : Type} [Field K₀] [Field K] [Field K₀'] [Field K']
  [Algebra F K₀] [Algebra F K] [Algebra K₀ K] [IsScalarTower F K₀ K]
  [Algebra F K₀'] [Algebra F K'] [Algebra K₀' K'] [IsScalarTower F K₀' K']
  {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra F B] [Algebra F BdR]
  [Algebra K₀ B] [IsScalarTower F K₀ B] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower F K BdR]
  [IsScalarTower K₀ K BdR] [IsScalarTower F K₀ BdR]
  [Algebra K₀' B] [IsScalarTower F K₀' B] [Algebra K₀' BdR] [Algebra K' BdR] [IsScalarTower F K' BdR]
  [IsScalarTower K₀' K' BdR] [IsScalarTower F K₀' BdR]

omit [TopologicalSpace H] [TopologicalSpace F] in
theorem mem_Dcris (PD' : PeriodData H F K₀' K' B BdR) {V : Type} [AddCommGroup V] [Module F V]
    (ρ : Representation F H V) (x : V ⊗[F] B) : x ∈ Dcris PD' ρ ↔ ∀ g, actVB PD' ρ g x = x := by
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero]

theorem isDR_res (PD : PeriodData G F K₀ K B BdR) (PD' : PeriodData H F K₀' K' B BdR)
    (f : H →* G) (hf : Continuous f) (T : LocLat G F LL O) (S : Subgroup G) (hS : ∀ h, f h ∈ S)
    (hact : ∀ h b, PD'.actB h b = PD.actB (f h) b)
    (hcr : finrank LL ↥(⨅ g : S, LinearMap.ker (actVB PD T.ρ (g : G) - LinearMap.id)) =
      finrank F K₀ * finrank LL T.V)
    (hK : finrank F K₀' = finrank F K₀) (hO : GoodO (Qp := F) F R) (hF : fontCore PD') :
    IsDR PD' (resRep R f hf T).ρ := by
  obtain ⟨⟨hfin, hle⟩, -, h3⟩ := hF F R hO (resRep R f hf T)
  apply h3
  apply le_antisymm hle
  set W := ⨅ g : S, LinearMap.ker (actVB PD T.ρ (g : G) - LinearMap.id) with hW
  have hmem : ∀ x : W, (x : T.V ⊗[F] B) ∈ Dcris PD' (resRep R f hf T).ρ := by
    rintro ⟨x, hx⟩
    rw [hW, Submodule.mem_iInf] at hx
    refine (mem_Dcris PD' (resRep R f hf T).ρ x).mpr fun h => ?_
    have h1 := hx ⟨f h, hS h⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
    have h2 : ∀ y : T.V ⊗[F] B, actVB PD' (resRep R f hf T).ρ h y = actVB PD T.ρ (f h) y := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => exact (map_zero _).trans (map_zero _).symm
      | tmul v b =>
        change T.ρ (f h) v ⊗ₜ[F] PD'.actB h b = T.ρ (f h) v ⊗ₜ[F] PD.actB (f h) b
        rw [hact]
      | add x y hx hy => exact (map_add _ x y).trans ((congrArg₂ (· + ·) hx hy).trans (map_add _ x y).symm)
    exact (h2 x).trans h1
  let j : W →ₗ[F] ↥(Dcris PD' (resRep R f hf T).ρ) :=
    LinearMap.codRestrict _ (W.subtype.restrictScalars F) hmem
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg Subtype.val h :)
  have h4 := LinearMap.finrank_le_finrank_of_injective hj
  rw [← Module.finrank_mul_finrank F LL W, hcr, mul_left_comm, Module.finrank_mul_finrank, ← hK] at h4
  exact h4

theorem lift_res (PD' : PeriodData H F K₀' K' B BdR)
    (f : H →* G) (hf : Continuous f) (T : LocLat G F LL O)
    (hO : GoodO (Qp := F) F R) (ht : TateFilteredInvariants PD') (hdR : IsDR PD' (resRep R f hf T).ρ) (a e : ℤ) :
    ∀ y ∈ LinearMap.range (LinearMap.lTensor T.V ((PD'.Fil a).restrictScalars F).subtype),
      (∀ g : H, TensorProduct.map ((T.ρ (f g)).restrictScalars F)
          ((PD'.actdR g).toLinearMap.restrictScalars F) y - y ∈
        LinearMap.range (LinearMap.lTensor T.V ((PD'.Fil e).restrictScalars F).subtype)) →
      ∃ w, (∀ g : H, TensorProduct.map ((T.ρ (f g)).restrictScalars F)
          ((PD'.actdR g).toLinearMap.restrictScalars F) w = w) ∧
        w ∈ LinearMap.range (LinearMap.lTensor T.V ((PD'.Fil a).restrictScalars F).subtype) ∧
        y - w ∈ LinearMap.range (LinearMap.lTensor T.V ((PD'.Fil e).restrictScalars F).subtype) := by
  intro y hy hG
  obtain ⟨w, ⟨hw1, hw2⟩, hw3⟩ := ht F R hO (resRep R f hf T) hdR a e y hy hG
  refine ⟨w, fun g => ?_, hw2, hw3⟩
  have h1 := (Submodule.mem_iInf _).mp hw1 g
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h1
  exact h1

end Crys

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc

theorem mem_GKs {l : ℕ} [Fact l.Prime] (P : LocPrime l) (HW : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (j : ℕ) (hj : s ≤ j) (g : ↥(GK K)) (hg : (g : GQ l) ∈ Gj K j) :
    g ∈ (HW.W K s LL h).GKs := by
  rw [(HW.W K s LL h).GKs_def, HW.W_s, P.PD_χ, ← map_one (algebraMap ℚ_[l] ↥LL.1), ← map_sub]
  apply le_val
  have h0 : (g : GQ l) ∈ (K0 K).fixingSubgroup := fun x => hg ⟨x.1, (le_sup_left : K0 K ≤ Ks K j) x.2⟩
  have h1 := (((GlobalTheory.Cyc.cyc_basic l P.χQ P.χQ_cyc).2.2 K g h0).1 j).mp hg
  refine h1.trans (zpow_le_zpow_right₀ ?_ (by omega))
  exact_mod_cast (Fact.out : l.Prime).one_le

theorem isDR_lev {l : ℕ} [Fact l.Prime] (P : LocPrime l) (HW : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (j : ℕ) (hj : s ≤ j) (hle : GK (lev K j) ≤ GK K)
    [FiniteDimensional ℚ_[l] ↥LL.1] [IsModuleTopology ℚ_[l] ↥LL.1]
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h7 : fontCore (P.PD (lev K j)))
    (hcr : finrank ↥LL.1 ↥(⨅ g : (HW.W K s LL h).GKs,
        LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - LinearMap.id)) =
      finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V) :
    IsDR (P.PD (lev K j))
      (resRep ℤ_[l] (Subgroup.inclusion hle) (continuous_inclusion hle) T).ρ :=
  isDR_res (R := ℤ_[l]) (P.PD K) (P.PD (lev K j)) (Subgroup.inclusion hle) (continuous_inclusion hle) T
    (HW.W K s LL h).GKs (fun g => mem_GKs P HW K s LL h j hj _ g.2)
    (fun g x => by rw [P.PD_actB, P.PD_actB]; rfl) hcr
    (finrank_maxUnramified_cyclotomicLevel K j (h.1.trans hj)) goodO h7

theorem lift_of_isDR {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LT : LocTied l P AI)
    (J : ThetaL P AI) (K' : FinExt l) {LL O G : Type} [Field LL] [CommRing O] [Algebra ℚ_[l] LL]
    [Algebra O LL] [Algebra ℤ_[l] O] [TopologicalSpace LL] [Group G] [TopologicalSpace G]
    [IsTopologicalRing LL] [IsModuleTopology ℚ_[l] LL] [FiniteDimensional ℚ_[l] LL]
    [Module.Finite ℤ_[l] O]
    (hc : ∀ c, algebraMap O LL (algebraMap ℤ_[l] O c) = algebraMap ℚ_[l] LL (algebraMap ℤ_[l] ℚ_[l] c))
    (hd : ∀ c : LL, ∃ (z : ℚ_[l]) (a : O), c = z • algebraMap O LL a)
    (f : ↥(GK K') →* G) (hf : Continuous f) (T : LocLat G ℚ_[l] LL O) (h5 : TateFilteredInvariants (P.PD K'))
    (hdR : IsDR (P.PD K') (resRep ℤ_[l] f hf T).ρ) (a e b : ℤ) (hae : a ≤ e) (heb : e ≤ b)
    (p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e)
    (hp : ∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) :
    letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
    ∀ (ρT : ↥(GK K') →* (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)), (∀ g t, (ρT g t : T.V) = T.ρ (f g) (t : T.V)) →
    ∀ z : ↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e, (∀ g, repQ AI (GK K') ρT a e g z = z) →
      ∃ (k : ℕ) (x : ↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU AI) a b),
        (∀ g, repQ AI (GK K') ρT a b g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  intro ρT hρ z hz
  obtain ⟨β, b1, b2, b3, b4, b5⟩ := exists_beta AI LT J K' a
  obtain ⟨n, bT, bV, hb⟩ := lat_bases hc hd T
  have ht := lift_res (R := ℤ_[l]) (P.PD K') f hf T goodO h5 hdR a e
  have hX := xiOK_res AI K'
  have hanti : ∀ c d : ℤ, c ≤ d → (P.PD K').Fil d ≤ (P.PD K').Fil c :=
    fun c d hcd => antitone_int_of_succ_le (P.PD K').Fil_anti hcd
  exact core bT bV T.L.T.subtype.toAddMonoidHom (lat_smul hc T) β b1 hb (l : ℤ_[l])
    (((P.PD K').Fil a).restrictScalars ℚ_[l])
    (((P.PD K').Fil e).restrictScalars ℚ_[l])
    (((P.PD K').Fil b).restrictScalars ℚ_[l])
    ((Mxi (AinfSub l) (xiU AI) e).comap (Mxi (AinfSub l) (xiU AI) a).subtype)
    ((Mxi (AinfSub l) (xiU AI) b).comap (Mxi (AinfSub l) (xiU AI) a).subtype)
    (fun x hx => hanti e b heb hx) b2 (b3 e hae) (b3 b (hae.trans heb)) (b4 b (hae.trans heb))
    (G := ↥(GK K')) (fun g => ρT g) (fun g => actM hX a g)
    (fun g => (T.ρ (f g)).restrictScalars ℚ_[l])
    (fun g => ((P.PD K').actdR g).toLinearMap.restrictScalars ℚ_[l])
    hρ (fun g m => (b5 g m _ rfl).trans (P.PD_actdR K' g _).symm)
    (fun g x hx => (P.PD K').Fil_G g b x hx)
    (fun g => actQab hX a e g) (fun _ _ => rfl) (fun g => actQab hX a b g) (fun _ _ => rfl)
    ht p hp z hz

theorem lift_lev {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LT : LocTied l P AI)
    (J : Nonempty (ThetaL P AI)) (HW : LocHW l P) (K : FinExt l) (s : ℕ)
    (LL : FinExt l) (h : Good K s LL) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (a e b : ℤ) (j : ℕ)
    (hle : Gj K j ≤ GK K) (hj : s ≤ j) (hae : a ≤ e) (heb : e ≤ b)
    (h5 : TateFilteredInvariants (P.PD (lev K j))) (h7 : fontCore (P.PD (lev K j)))
    (hcr : finrank ↥LL.1 ↥(⨅ g : (HW.W K s LL h).GKs,
        LinearMap.ker (actVB (P.PD K) T.ρ (g : ↥(GK K)) - LinearMap.id)) =
      finrank ℚ_[l] ↥(K0 K) * finrank ↥LL.1 T.V)
    (p : Qab (AinfSub l) (xiU AI) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e)
    (hp : ∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) :
    letI := zlMod LL T
    ∀ z : ↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU AI) a e,
      (∀ g, repQ AI (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e g z = z) →
      ∃ (k : ℕ) (x : ↥T.L.T ⊗[ℤ_[l]] Qab (AinfSub l) (xiU AI) a b),
        (∀ g, repQ AI (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b g x = x) ∧
        LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z := by
  obtain ⟨J⟩ := J
  haveI : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  haveI := modTopLL LL
  haveI := finOL LL
  have hle' : GK (lev K j) ≤ GK K := hle
  have hdR := isDR_lev P HW K s LL h j hj hle' T h7 hcr
  letI := zlMod LL T
  exact lift_of_isDR AI LT J (lev K j) (LL := ↥LL.1) (O := ↥(OL LL)) (G := ↥(GK K))
    (fun _ => rfl) (denom LL) (Subgroup.inclusion hle') (continuous_inclusion hle') T
    h5 hdR a e b hae heb p hp ((actTZ LL T).comp (Subgroup.inclusion hle'))
    (fun _ _ => rfl)

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc in

theorem invariants_lift : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW), adm5 D → adm7 D → ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let S := sit D.loc HW l (D.locA l) K s LL h; let E : S.Comparison₂ := ((F l).E K s LL h).tie; ∀ (T : LocLat S.G S.Qp S.LL S.O) (a e b : ℤ) (j : ℕ) (hle : Gj K j ≤ GK K), s ≤ j → a ≤ e → e ≤ b → IsCrysOn S S.W.GKs T → ∀ p : Qab (AinfSub l) (xiU (D.locA l)) a b →ₗ[ℤ_[l]] Qab (AinfSub l) (xiU (D.locA l)) a e, (∀ x, p (Submodule.Quotient.mk x) = Submodule.Quotient.mk x) → letI := zlMod LL T; ∀ z : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a e)), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a e) g z = z) → ∃ (k : ℕ) (x : (TensorProduct ℤ_[l] ↥T.L.T (Qab (AinfSub l) (xiU (D.locA l)) a b))), (∀ g, (repQ (D.locA l) (Gj K j) ((actTZ LL T).comp (Subgroup.inclusion hle)) a b) g x = x) ∧ LinearMap.lTensor ↥T.L.T p x = (l : ℤ_[l]) ^ k • z :=
  fun D HW _ h5 h7 l _ K s LL h T a e b j hle hsj hae heb hcr p hp =>
    lift_lev (D.locA l) (D.locT l) (GlobalTheory.ThetaTie.nonempty_thetaL D l) (HW l) K s LL h T a e b j hle hsj hae heb
      (h5 l (lev K j)) (h7 l (lev K j)) hcr p hp

end GlobalTheory.InvariantLift
