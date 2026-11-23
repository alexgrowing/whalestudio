import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActMatApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaBaseChangeFiniteProjectiveReflexive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCycPerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankDualAndRangeDualMapBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct
open scoped Pointwise ChangeOfRings

namespace GlobalTheory.ChainPts.SysB.RingEx

open GlobalTheory.PDivGroup GlobalTheory.RingChain GlobalTheory.PerfdLat GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.Published

theorem omegaBCMap_bijective {p : ℕ} [Fact p.Prime] {R : Type} (R' : Type)
    [CommRing R] [CommRing R'] [Algebra R R'] [IsAdicComplete (Ideal.span {(p : R')}) R']
    (G : GlobalTheory.PDivGroup p R) {M : Type} [AddCommGroup M] [Module R M] [Module.Finite R M]
    [Module.Projective R M] (c : M →ₗ[R] G.omega) (hc : IsLevels c) :
    Function.Bijective (G.omegaBCMap (R' := R') c) := by
  obtain ⟨hs, hk⟩ := hc
  set Φ := G.omegaBCMap (R' := R') c with hΦ
  haveI : IsAdicComplete (Ideal.span {(p : R')}) (R' ⊗[R] M) :=
    isAdicComplete_of_finite_projective _ _
  have hker : ∀ n x, (Φ x).1 n = 0 → ∃ y, x = (p : R') ^ n • y := by
    intro n x hx
    rw [omegaBCMap_level, LinearEquiv.map_eq_zero_iff] at hx
    have hex : Function.Exact ((p : R) ^ n • LinearMap.id : M →ₗ[R] M)
        ((G.omegaLevel n).comp c) := by
      intro y
      rw [LinearMap.comp_apply, omegaLevel_apply, hk n y]
      exact ⟨fun ⟨w', hw'⟩ => ⟨w', by simp [hw']⟩, fun ⟨w', hw'⟩ => ⟨w', by simp [← hw']⟩⟩
    have hex' := lTensor_exact R' hex (hs n)
    have hx' : LinearMap.lTensor R' ((G.omegaLevel n).comp c) x = 0 := by
      rwa [← LinearMap.baseChange_eq_ltensor]
    obtain ⟨y, hy⟩ := (hex' x).1 hx'
    refine ⟨y, ?_⟩
    rw [← hy, LinearMap.lTensor_smul, LinearMap.lTensor_id, LinearMap.smul_apply,
      LinearMap.id_apply, ← algebraMap_smul R', map_pow, map_natCast]
  have hpow : ∀ n y, (Φ ((p : R') ^ n • y)).1 n = 0 := fun n y => by
    rw [map_smul]
    exact (G.baseChange R').pow_smul_cot n _
  have hsurj : ∀ n v, ∃ x, (Φ x).1 n = v := by
    intro n v
    obtain ⟨x, hx⟩ := LinearMap.lTensor_surjective R' (g := (G.omegaLevel n).comp c) (hs n)
      ((G.cotBase_isBaseChange n).equiv.symm v)
    refine ⟨x, ?_⟩
    rw [omegaBCMap_level, LinearMap.baseChange_eq_ltensor, hx, LinearEquiv.apply_symm_apply]
  constructor
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {(p : R')}) (R' ⊗[R] M)) x
      fun n => ?_
    rw [SModEq.sub_mem, sub_zero, mem_span_singleton_pow_smul_top_iff_exists]
    exact hker n x (by rw [hx]; rfl)
  · intro w
    choose x hx using fun n => hsurj n (w.1 n)
    have hc : ∀ m n, m ≤ n → ∃ y, x n - x m = (p : R') ^ m • y := by
      intro m n hmn
      apply hker m
      rw [map_sub]
      change (Φ (x n)).1 m - (Φ (x m)).1 m = 0
      rw [hx m, sub_eq_zero]
      have h := (G.baseChange R').omega_val_eq_zero_of_le hmn (w := Φ (x n) - w)
        (by change (Φ (x n)).1 n - w.1 n = 0; rw [hx n, sub_self])
      exact sub_eq_zero.1 h
    obtain ⟨L, hL⟩ := IsPrecomplete.prec
      (inferInstance : IsPrecomplete (Ideal.span {(p : R')}) (R' ⊗[R] M)) (f := x)
      fun {m n} hmn => by
        rw [SModEq.sub_mem, mem_span_singleton_pow_smul_top_iff_exists]
        obtain ⟨y, hy⟩ := hc m n hmn
        exact ⟨-y, by rw [smul_neg, ← hy, neg_sub]⟩
    refine ⟨L, Subtype.ext (funext fun n => ?_)⟩
    obtain ⟨y, hy⟩ := (mem_span_singleton_pow_smul_top_iff_exists _ n _).1 (SModEq.sub_mem.1 (hL n))
    have h1 : (Φ (x n - L)).1 n = 0 := by rw [hy]; exact hpow n y
    rw [map_sub] at h1
    change (Φ (x n)).1 n - (Φ L).1 n = 0 at h1
    rw [hx n, sub_eq_zero] at h1
    exact h1.symm

theorem smul_top_of_isUnit {A X : Type} [CommRing A] [AddCommGroup X] [Module A X] {a : A} (ha : IsUnit a) :
    a • (⊤ : Submodule A X) = ⊤ := by
  obtain ⟨u, rfl⟩ := ha
  refine eq_top_iff.2 fun x _ => (Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨(↑u⁻¹ : A) • x, trivial, ?_⟩
  rw [smul_smul, Units.mul_inv, one_smul]

theorem isFrobLin_of_isUnit {A : Type} [CommRing A] {p : ℕ} (hp : IsUnit (p : A)) (q : ℕ) {M N : Type} [AddCommGroup M]
    [Module A M] [AddCommGroup N] [Module A N] [Subsingleton N] (ψ : M →+ N) : IsFrobLin A p q ψ := by
  intro f _
  haveI : Subsingleton (A ⧸ Ideal.span {(p : A)}) :=
    Ideal.Quotient.subsingleton_iff.2 (Ideal.span_singleton_eq_top.2 hp)
  haveI : Subsingleton ((ModuleCat.extendScalars f).obj (ModuleCat.of A M)) :=
    Module.subsingleton (A ⧸ Ideal.span {(p : A)}) _
  exact ⟨AddEquiv.ofBijective (0 : _ →+ N) ⟨fun _ _ _ => Subsingleton.elim _ _, fun _ => ⟨0, Subsingleton.elim _ _⟩⟩,
    fun _ _ => Subsingleton.elim _ _⟩

theorem nonempty_rChain_of_isUnit {A : Type} [CommRing A] {p : ℕ} (hp : IsUnit (p : A)) (h o : ℕ) {π : A} (hπ : IsUnit π)
    (γ : ℕ → A) (Lie Om : Type) [AddCommGroup Lie] [Module A Lie] [AddCommGroup Om] [Module A Om] :
    Nonempty (RChain p A h o π γ Lie Om) := by
  have hb : baseOf π h = ⊤ := smul_top_of_isUnit hπ
  haveI h1 : Subsingleton (Qt (⊤ : Submodule A (Fin h → A)) (baseOf π h)) :=
    Submodule.Quotient.subsingleton_iff.2 (by rw [hb, Submodule.comap_top])
  haveI h2 : Subsingleton (Qt (⊤ : Submodule A (Fin h → A)) ⊤) :=
    Submodule.Quotient.subsingleton_iff.2 (by rw [Submodule.comap_top])
  haveI h3 : Subsingleton (Lie ⧸ (p : A) • (⊤ : Submodule A Lie)) :=
    Submodule.Quotient.subsingleton_iff.2 (smul_top_of_isUnit hp)
  exact ⟨{
    L := fun _ => ⊤
    finite := fun _ => inferInstance
    projective := fun _ => Module.Projective.of_equiv Submodule.topEquiv.symm
    base_le := fun _ => le_top
    succ_le := fun _ => le_top
    kill := fun _ _ => le_top.trans hb.ge
    gam := fun _ _ => le_top
    lfree := fun _ _ => inferInstance
    j := 0
    ρ := 0
    ρ_surj := fun x => ⟨0, by
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [Subsingleton.elim y 0]; rfl⟩
    ψ := fun _ => 0
    ψ_lin := fun _ _ => isFrobLin_of_isUnit hp _ _
    κ := fun _ => 0
    κ_lin := fun _ _ => isFrobLin_of_isUnit hp _ _ }⟩

theorem sub_one_dvd {A : Type} [CommRing A] [IsDomain A] {p : ℕ} [Fact p.Prime] {ζ : ℕ → A}
    (h1 : IsPrimitiveRoot (ζ 1) (p ^ 1)) (hs : ∀ n, ζ (n + 1) ^ p = ζ n) (n : ℕ) : ζ (n + 1) - 1 ∣ (p : A) := by
  induction n with
  | zero =>
    have h0 : ∑ i ∈ Finset.range p, ζ 1 ^ i = 0 := by
      simpa using h1.geom_sum_eq_zero (by simpa using (Fact.out : p.Prime).one_lt)
    have h2 : (p : A) = -∑ i ∈ Finset.range p, (ζ 1 ^ i - 1) := by simp [h0]
    rw [h2, dvd_neg]
    exact Finset.dvd_sum fun i _ => sub_one_dvd_pow_sub_one _ i
  | succ n ih => exact (hs (n + 1) ▸ sub_one_dvd_pow_sub_one _ p).trans ih

theorem omegaMap_bijective {p : ℕ} [Fact p.Prime] {R : Type} [CommRing R] {G H : PDivGroup p R} (e : G ≅ H) :
    Function.Bijective (omegaMap G H e.hom) := by
  refine Function.bijective_iff_has_inverse.2 ⟨omegaMap H G e.inv, fun x => ?_, fun x => ?_⟩
  · rw [← LinearMap.comp_apply, ← omegaMap_comp, e.inv_hom_id, omegaMap_id, LinearMap.id_apply]
  · rw [← LinearMap.comp_apply, ← omegaMap_comp, e.hom_inv_id, omegaMap_id, LinearMap.id_apply]

theorem ringExSt_of_existsSt : GlobalTheory.RingChain.ExistsSt → GlobalTheory.ChainPts.SysB.RingExSt := by
  intro hE p _ D A K _ _ _ _ _ _ _ _ GG pol ε c h o e π γ Lie Om _ _ _ _ _ _ _ _ cω pr hprim hlev hpr hπ hγ
  have hdv := sub_one_dvd (ζ := muRoot ε) (hprim 1) (muRoot_succ_pow ε)
  have hπp : π ∣ (p : A) := hπ ▸ hdv 0
  by_cases hp : IsUnit (p : A)
  · obtain ⟨C⟩ := nonempty_rChain_of_isUnit hp h o (isUnit_of_dvd_unit hπp hp) γ Lie Om
    exact ⟨C, fun h => absurd hp h⟩
  obtain ⟨S, ec, hS⟩ := GlobalTheory.PerfdCompletion.exists_cycPerfd p A K hp (muRoot ε) hprim (muRoot_succ_pow ε)
  letI : Algebra A S.R := (ec.toRingHom.comp (algebraMap A _)).toAlgebra
  have hec : ∀ a, ec (algebraMap A _ a) = algebraMap A S.R a := fun _ => rfl
  have hz : ∀ n, zeta S.ε n = algebraMap A S.R (muRoot ε n) := hS
  have hε : ∀ n, muRoot (eps S) n = algebraMap A S.R (muRoot ε n) := fun n => (muRoot_eps S n).trans (hz n)
  haveI : CharZero A := RingHom.charZero (algebraMap A K)
  let eω := LinearEquiv.ofBijective _ (omegaBCMap_bijective S.R GG cω hlev)
  have heω : ∀ w, eω (1 ⊗ₜ w) = (GG.toBase S.R).omega (cω w) := fun w => by
    change GG.omegaBCMap cω (1 ⊗ₜ w) = _
    rw [omegaBCMap, LinearMap.liftBaseChange_tmul, one_smul]
    rfl
  let eP := LinearEquiv.ofBijective _
    (omegaMap_bijective ((baseChangeFunctor p A S.R).mapIso pol ≪≫ (dualBaseChange S.R GG).symm))
  let eO : S.R ⊗[A] Om ≃ₗ[S.R] (GG.baseChange S.R).dual.omega := eω.trans eP.symm
  let eL : S.R ⊗[A] Lie ≃ₗ[S.R] (GG.baseChange S.R).Lie :=
    ((LinearEquiv.ofBijective pr hpr).baseChange A S.R _ _).trans
      ((LinearEquiv.ofBijective _ (GlobalTheory.DualFibreRank.cmp_bijective S.R (O := A) (M := Om))).trans eω.symm.dualMap)
  obtain ⟨C, hC⟩ := hE p D S (GG.baseChange S.R) (c.baseChange S.R hε) A ec hec h o e π γ hπp
    (fun n hn => by
      refine Dvd.dvd.trans ?_ (hdv n)
      rw [hγ n hn, ← muRoot_succ_pow ε (n + 1), ← geom_sum_mul]
      exact dvd_mul_right _ _)
    (by rw [hπ, map_sub, map_one, hz])
    (fun n hn => by
      rw [hγ n hn, xiN, GlobalTheory.Sandwich.xi, map_sum, map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_pow, map_pow, WittVector.fontaineTheta_teichmuller, ← hz, zeta, Function.iterate_succ_apply'])
    Lie Om eL eO
  refine ⟨C, fun _ => ⟨S, inferInstance, ec, hec, hε, eL, eO, fun y w => ?_, fun w => ?_, hC⟩⟩
  · rw [← heω]
    simp [eL, GlobalTheory.DualFibreRank.cmp, Algebra.smul_def]
  · rw [← heω]
    exact eP.apply_symm_apply _

end GlobalTheory.ChainPts.SysB.RingEx

end
