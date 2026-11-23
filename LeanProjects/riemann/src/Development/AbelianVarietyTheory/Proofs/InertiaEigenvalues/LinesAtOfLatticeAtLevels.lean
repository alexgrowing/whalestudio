import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Saturated
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.GradedSeries
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfDiagWith
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPtPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachLatticeEqFiltrationSumAtLevelStatement

noncomputable section

namespace GlobalTheory.SenOperator

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.SenLines GlobalTheory.WachUse TensorProduct
open GlobalTheory.WachTie.MatF

section Algebra

variable {O F Q : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup Q] [Module O Q]

theorem aeval_eq_zero_of_diagWith [Module.Free O Q] (hinj : Function.Injective (algebraMap O F))
    (f : Module.End O Q) (S : Multiset F) (h : DiagWith (f.baseChange F) S) (p : Polynomial O)
    (hp : ∀ s ∈ S, Polynomial.aeval s p = 0) : Polynomial.aeval f p = 0 := by
  obtain ⟨m, b, e, he, rfl⟩ := h
  have h1 : ∀ (p : Polynomial O) (s : Fin m),
      (Polynomial.aeval f p).baseChange F (b s) = Polynomial.aeval (e s) p • b s := by
    intro p s
    induction p using Polynomial.induction_on with
    | C a => simp [Algebra.algebraMap_eq_smul_one, LinearMap.baseChange_smul]
    | add p q hp hq => simp only [map_add, LinearMap.baseChange_add, LinearMap.add_apply, hp, hq, add_smul]
    | monomial k a ih =>
      rw [pow_succ, ← mul_assoc, map_mul _ _ Polynomial.X, map_mul _ _ Polynomial.X, Polynomial.aeval_X,
        Polynomial.aeval_X, LinearMap.baseChange_mul, Module.End.mul_apply, he, map_smul, ih, smul_smul, mul_comm]
  have h2 : (Polynomial.aeval f p).baseChange F = 0 := b.ext fun s => by
    rw [h1, hp _ (Multiset.mem_map_of_mem _ (Finset.mem_univ_val s)), zero_smul, LinearMap.zero_apply]
  ext x
  have h3 : (1 : F) ⊗ₜ[O] (Polynomial.aeval f p x) = 0 := by
    rw [← LinearMap.baseChange_tmul, h2, LinearMap.zero_apply]
  have h4 := Module.Flat.rTensor_preserves_injective_linearMap (M := Q) (Algebra.linearMap O F) hinj
  have h5 : (1 : O) ⊗ₜ[O] (Polynomial.aeval f p x) = 0 := h4 (by simpa using h3)
  simpa using congrArg (TensorProduct.lid O Q) h5

theorem charpoly_of_integral [Module.Free O Q] [Module.Finite O Q] (hinj : Function.Injective (algebraMap O F))
    (f : Q →ₗ[O] Q) (S : Multiset O) (h : DiagWith (f.baseChange F) (S.map (algebraMap O F))) :
    f.charpoly = (S.map fun s => Polynomial.X - Polynomial.C s).prod := by
  have h1 := charpoly_of_diagWith _ _ h
  rw [LinearMap.charpoly_baseChange] at h1
  apply Polynomial.map_injective _ hinj
  rw [h1, Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  congr 2
  funext s
  simp

theorem exists_basis_quot (P' : Submodule O Q) {r : ℕ} (θ : (Fin r → O⟦X⟧) ≃ₗ[O] Q)
    (h : ∀ c, θ c ∈ P' ↔ ∀ k, (X : O⟦X⟧) ∣ c k) :
    ∃ β : Module.Basis (Fin r) O (Q ⧸ P'), ∀ j, β j = Submodule.Quotient.mk (θ (Pi.single j 1)) := by
  let tr : (Fin r → O⟦X⟧) →ₗ[O] (Fin r → O) := LinearMap.pi fun x => (coeff 0).comp (LinearMap.proj x)
  let f : Q →ₗ[O] (Fin r → O) := tr.comp θ.symm.toLinearMap
  have hs : Function.Surjective f := fun y => ⟨θ fun k => C (y k), by funext x; simp [f, tr]⟩
  have hk : P' = LinearMap.ker f := by
    ext x
    obtain ⟨c, rfl⟩ := θ.surjective x
    rw [h, LinearMap.mem_ker, funext_iff]
    simp [X_dvd_iff, f, tr]
  let e := (Submodule.quotEquivOfEq _ _ hk).trans (f.quotKerEquivOfSurjective hs)
  refine ⟨Module.Basis.ofEquivFun e, fun j => ?_⟩
  rw [Module.Basis.coe_ofEquivFun, LinearEquiv.symm_apply_eq]
  change _ = f _
  funext x
  by_cases hx : x = j
  · subst hx; simp [f, tr]
  · simp [f, tr, Pi.single_eq_of_ne hx]

theorem aeval_intertwine {Q' : Type} [AddCommGroup Q'] [Module O Q'] (π : Q →ₗ[O] Q') (f : Module.End O Q)
    (f' : Module.End O Q') (h : ∀ x, π (f x) = f' (π x)) (p : Polynomial O) (x : Q) :
    π (Polynomial.aeval f p x) = Polynomial.aeval f' p (π x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul _ _ Polynomial.X, map_mul _ _ Polynomial.X, Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

end Algebra

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K] [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K] {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B] [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR] [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem letE_mul (i j : ZMod n) : (letE i * letE j : LetA O n) = if i = j then letE i else 0 := by
  rw [letE, letE, mul_single]
  split_ifs with h
  · subst h; simp
  · simp [Pi.single_eq_of_ne (Ne.symm h)]

theorem γD_letE (g : W.Gam) (i : ZMod n) (x : W.DD T) :
    W.γD T g ((letE i : LetA O n) • x) = (letE i : LetA O n) • W.γD T g x := by
  rw [γD_smulA, letE, γA_single, map_one]

def pr (i : ZMod n) : ↥(W.NΔ T) →ₗ[O] ↥(qN W T i 0) :=
  ((mulD W T (letE i)).comp (W.NΔ T).subtype).codRestrict _ fun x => by
    rw [qN_zero]
    refine ⟨⟨(W.N T).smul_mem _ x.2.1, fun δ hδ => ?_⟩, x, x.2.1, rfl⟩
    change W.γD T δ ((letE i : LetA O n) • (x : W.DD T)) = (letE i : LetA O n) • (x : W.DD T)
    rw [γD_letE, x.2.2 δ hδ]

theorem pr_apply (i : ZMod n) (x : ↥(W.NΔ T)) : (pr W T i x : W.DD T) = (letE i : LetA O n) • (x : W.DD T) := rfl

theorem qN_zero_le (i : ZMod n) : qN W T i 0 ≤ W.NΔ T := (qN_zero W T i).le.trans inf_le_left

theorem letE_smul (i j : ZMod n) (x : ↥(qN W T j 0)) :
    (letE i : LetA O n) • (x : W.DD T) = if i = j then (x : W.DD T) else 0 := by
  obtain ⟨-, y, -, hy⟩ := (qN_zero W T j).le x.2
  have hy' : (letE j : LetA O n) • y = x := hy
  rw [← hy', smul_smul, letE_mul]
  split_ifs with h
  · rw [h]
  · rw [zero_smul]

theorem exists_glue (g : W.Gam) (nb : ∀ i, ↥(qN W T i 0) →ₗ[O] ↥(qN W T i 0)) (h : ∀ i, IsNab W T g 1 i 0 (nb i)) :
    ∃ ν : Module.End O ↥(W.NΔ T), (∀ y : ↥(W.NΔ T), W.γD T g y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) ∧
      ∀ i y, pr W T i (ν y) = nb i (pr W T i y) := by
  have := PD.finK₀
  have : NeZero n := ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩
  let ν : Module.End O ↥(W.NΔ T) :=
    ∑ i, (Submodule.inclusion (qN_zero_le W T i)).comp ((nb i).comp (pr W T i))
  have hν : ∀ y, (ν y : W.DD T) = ∑ i, (nb i (pr W T i y) : W.DD T) := fun y => by
    simp only [ν, LinearMap.sum_apply, Submodule.coe_sum, LinearMap.comp_apply, Submodule.coe_inclusion]
  refine ⟨ν, fun y => ?_, fun i y => Subtype.ext ?_⟩
  · have h1 : ∀ i, W.π₀ • (nb i (pr W T i y) : W.DD T) = (letE i : LetA O n) • (W.γD T g y - y) := fun i => by
      have := h i (pr W T i y)
      rw [one_mul, one_smul, pr_apply, γD_letE] at this
      rw [this, smul_sub]
    rw [hν, Finset.smul_sum]
    simp only [h1]
    rw [← Finset.sum_smul, show (∑ i, letE i : LetA O n) = 1 from Finset.univ_sum_single (1 : LetA O n), one_smul]
  · rw [pr_apply, hν, Finset.smul_sum]
    simp only [letE_smul]
    simp

theorem exists_of_mem_qN (i : ZMod n) (s : ℕ) {x : W.DD T} (hx : x ∈ qN W T i s) :
    ∃ z ∈ W.N T, x = (W.π₀ + (PD.p : LetA O n)) ^ s • z := by
  obtain ⟨z, hz, h⟩ := hx
  refine ⟨z, hz.1.1, ?_⟩
  have h' : qΔ W ^ (s : ℤ).toNat • z = qΔ W ^ (-(s : ℤ)).toNat • x := h
  rw [show (-(s : ℤ)).toNat = 0 by omega, pow_zero, one_smul, Int.toNat_natCast] at h'
  exact h'.symm

theorem senOp_at [CharZero LL] (hinj : Function.Injective (algebraMap O LL)) {g : W.Gam}
    {J : O⟦X⟧ →ₐ[O] O⟦X⟧} (hJ : QFrame W g J) (U : ZMod n → Multiset ℤ)
    (hD : ∀ i (j' : ℤ), 0 < j' → DiagQuot W T g 1 i 0 j' (eigMs LL PD.p (U i) 0 0 j'))
    (c : ℤ → O) (hc : IsC PD LL c) :
    ∃ ν : Module.End O ↥(W.NΔ T), (∀ y : ↥(W.NΔ T), W.γD T g y - y = W.π₀ • ((ν y : ↥(W.NΔ T)) : W.DD T)) ∧
    (∀ (i : ZMod n) (s : ℕ) (y : ↥(W.NΔ T)), ∃ z ∈ W.N T, (letE i : LetA O n) •
      ((Polynomial.aeval ν (∏ m ∈ ((Finset.range s) ×ˢ (U i).toFinset).image (fun p => (p.1 : ℤ) - p.2),
        (Polynomial.X - Polynomial.C (c m))) y : ↥(W.NΔ T)) : W.DD T) = (W.π₀ + (PD.p : LetA O n)) ^ s • z) ∧
    ∀ (m : ℕ) (b : Fin m → ↥(W.NΔ T)), LinearIndependent (LetA O n) (fun j => (b j : W.DD T)) →
      W.N T = Submodule.span (LetA O n) (Set.range fun j => (b j : W.DD T)) →
      ∀ i : ZMod n, ∃ A : Matrix (Fin m) (Fin m) O,
        A.charpoly = ((U i).map fun u => Polynomial.X - Polynomial.C (c (-u))).prod ∧
        ∀ j, ∃ z ∈ W.N T, (letE i : LetA O n) • (((ν (b j) - ∑ j', A j' j • b j' : ↥(W.NΔ T))) : W.DD T) =
          (W.π₀ + (PD.p : LetA O n)) • z := by
  have hcc : ∀ a, algebraMap O LL (c a) = ((cc PD.p a : ℚ) : LL) := fun a => by
    have h0 : (PD.p : LL) ≠ 0 := Nat.cast_ne_zero.2 PD.hp.ne_zero
    have h1 := hc a
    simp only [cc]
    push_cast
    rw [eq_div_iff (neg_ne_zero.2 h0)]
    linear_combination -h1
  choose nb hnb using fun i => (hD i 1 one_pos).2.2.2.2.1
  obtain ⟨ν, hν, hpr⟩ := exists_glue W T g nb hnb
  refine ⟨ν, hν, fun i s y => ?_, fun m b hli hsp i => ?_⟩
  · rw [← pr_apply]
    rcases Nat.eq_zero_or_pos s with rfl | hs
    · exact exists_of_mem_qN W T i 0 (Subtype.property _)
    obtain ⟨-, hfree, -, -, -, hall⟩ := hD i s (by exact_mod_cast hs)
    obtain ⟨hst, hd⟩ := hall _ (hnb i)
    refine exists_of_mem_qN W T i s ?_
    rw [aeval_intertwine _ _ _ (hpr i)]
    refine (Submodule.Quotient.mk_eq_zero ((qN W T i s).submoduleOf (qN W T i 0))).1 ?_
    rw [← Submodule.mkQ_apply, aeval_intertwine (Submodule.mkQ _) (nb i) (Submodule.mapQ _ _ (nb i) hst) (fun _ => rfl),
      aeval_eq_zero_of_diagWith hinj _ _ hd, LinearMap.zero_apply]
    intro x hx
    obtain ⟨u, hu, hx⟩ := Multiset.mem_bind.1 hx
    obtain ⟨j, hj, rfl⟩ := Multiset.mem_map.1 hx
    obtain ⟨hj0, hj1⟩ := Finset.mem_Ico.1 (Finset.mem_def.2 hj)
    rw [map_prod]
    refine Finset.prod_eq_zero (i := j - (u - 0)) (Finset.mem_image.2 ⟨(j.toNat, u), Finset.mem_product.2
      ⟨Finset.mem_range.2 (by omega), Multiset.mem_toFinset.2 hu⟩, by simp only; omega⟩) ?_
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hcc, sub_self]
  · obtain ⟨-, hfree, hfin, -, -, hall⟩ := hD i 1 one_pos
    obtain ⟨hst, hd⟩ := hall _ (hnb i)
    obtain ⟨Qu, hQ⟩ : IsUnit (algebraMap (LetA O n) W.EE (qΔ W)) := hJ.2.2.2.2.2.2
    let b' : Module.Basis (Fin m) (LetA O n) ↥(W.N T) :=
      (Module.Basis.span hli).map (LinearEquiv.ofEq _ _ hsp.symm)
    have hb' : ∀ k, (b' k : W.DD T) = b k := fun k => by simp [b']
    have hb : ∀ k, (b' k : W.DD T) ∈ W.NΔ T := fun k => by rw [hb']; exact (b k).2
    obtain ⟨θ, hθ⟩ := exists_theta W T J b' i hJ hb Qu hQ 0
    obtain ⟨β, hβ⟩ := exists_basis_quot ((qN W T i 1).submoduleOf (qN W T i 0)) θ fun d => by
      have := theta_mem W T J b' i hJ hb Qu hQ zero_le_one d
      rw [← hθ] at this
      exact Iff.trans this (by simp)
    have hβ' : ∀ j, β j = Submodule.Quotient.mk (pr W T i (b j)) := fun j => by
      rw [hβ]
      congr 1
      apply Subtype.ext
      rw [hθ, zpow_zero, one_smul, th_apply, Finset.sum_eq_single j (fun k _ hk => by
        simp [Pi.single_eq_of_ne hk]) (by simp), pr_apply, hb', Pi.single_eq_same, map_one, letE]
    refine ⟨LinearMap.toMatrix β β (Submodule.mapQ _ _ (nb i) hst), ?_, fun j => ?_⟩
    · have e1 : eigMs LL PD.p (U i) 0 0 1 = ((U i).map fun x => c (-x)).map (algebraMap O LL) := by
        rw [eigMs, show Finset.Ico (0 : ℤ) 1 = {0} from rfl, Multiset.map_map, ← Multiset.bind_singleton]
        refine Multiset.bind_congr fun x _ => ?_
        simp only [Finset.singleton_val, Multiset.map_singleton, Function.comp, hcc, sub_zero, zero_sub]
      rw [e1] at hd
      rw [LinearMap.charpoly_toMatrix, charpoly_of_integral hinj _ _ hd, Multiset.map_map]
      rfl
    · rw [← pr_apply, ← pow_one (W.π₀ + (PD.p : LetA O n))]
      refine exists_of_mem_qN W T i 1 ?_
      rw [Nat.cast_one, ← Submodule.subtype_apply, ← Submodule.mem_comap]
      refine (Submodule.Quotient.mk_eq_zero ((qN W T i 1).submoduleOf (qN W T i 0))).1 ?_
      rw [← Submodule.mkQ_apply, map_sub, map_sub, hpr, map_sum, map_sum, sub_eq_zero]
      simp only [map_smul, Submodule.mkQ_apply, ← hβ', LinearMap.toMatrix_apply]
      rw [β.sum_repr, hβ']
      rfl

omit T in
theorem senOp_of_diag [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    (h : ∀ (T : LocLat G Qp LL O) (U : ZMod n → Multiset ℤ), CrysWith PD W.emb T.ρ U → ∀ g : W.Gam,
      (W.χΓ g : O) = 1 + (PD.p : O) → (∃ J, QFrame W g J) ∧
        ∀ i (j' : ℤ), 0 < j' → DiagQuot W T g 1 i 0 j' (eigMs LL PD.p (U i) 0 0 j')) : SenOp W := by
  intro T U hcr g hg c hc
  obtain ⟨⟨J, hJ⟩, hD⟩ := h T U hcr g hg
  exact senOp_at W T hinj hJ U hD c hc

end Generic

set_option maxHeartbeats 1000000 in

theorem senOp_of_lines {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {H : LocHW l P}
    {E : LocFon l P AI H} (C : LocCmpT l P AI H E) {K LL : FinExt l} (hA : CaseA K LL)
    (hL : ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ),
      CrysWith (P.PD K) (H.W K 1 LL hA.2.2).emb T.ρ U → ∀ i,
      ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l ∧ LinesAt (H.W K 1 LL hA.2.2) T i ζ (U i)) :
    SenOp (H.W K 1 LL hA.2.2) := by
  have hinj : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  refine senOp_of_diag _ hinj fun T U hcr g hg => ?_
  have hp := P.PD_p K
  obtain ⟨hdvr, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨hcard, J, hJ⟩ := GlobalTheory.SenLines.exists_qFrame P K LL (H.W K 1 LL hA.2.2) g hA (by rw [hg, hp])
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  have hχ : algebraMap ↥(OL LL) ↥LL.1 ((H.W K 1 LL hA.2.2).χΓ g : ↥(OL LL)) = 1 + ((P.PD K).p : ↥LL.1) := by
    rw [hg, map_add, map_one, map_natCast]
  have hl' : ¬ IsUnit (((P.PD K).p : ℕ) : ↥(OL LL)) := hp.symm ▸ hl
  obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free P H K 1 LL hA.2.2 T hcr.1
  obtain ⟨b, hb⟩ := GlobalTheory.WachTie.exists_invariant_basis _ T hcard ⟨b₀.reindex (finCongr (finrank_lattice T.L))⟩
  refine ⟨⟨J, hJ⟩, fun i j' hj => ?_⟩
  obtain ⟨ζ, hζ, hlines⟩ := hL T U hcr i
  have hζ' : IsPrimitiveRoot ζ (P.PD K).p := hp.symm ▸ hζ
  obtain ⟨hρ, hγ⟩ := tie_γ _ (C.C K 1 LL hA.2.2).tie hχ hζ'
  exact (senPair _ T J i hinj hl' hJ b hb ζ hζ' (hρ i) _ (coords_of_lines _ T i g ζ _ hlines (hγ T hcr.1 i))
    1 1 (by simp) (by simp) 0 1 (by simp)).1 0 j' hj

section Series

open GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries

variable {F M M' N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup M'] [Module F M']

theorem serSpan_eq_map (j : M →ₗ[F] M') (ex : N → ℤ → M) (hex : ∀ x, IsLaurent (ex x)) (L : N → ℤ → M')
    (hL : ∀ x k, L x k = j (ex x k)) :
    serSpan F (Set.range L) = (GlobalTheory.NL.latSpan (LL := F) ex).map (j.compLeft ℤ) := by
  have h1 : ∀ (e : F⟦X⟧) x, j.compLeft ℤ (GlobalTheory.NL.conv e (ex x)) = serMul e (L x) := fun e x => by
    funext k
    change j (∑ᶠ m : ℕ, coeff m e • ex x (k - m)) = ∑ᶠ m : ℕ, coeff m e • L x (k - m)
    rw [map_finsum j (serMul_finite e (hex x) k)]
    simp only [map_smul, hL]
  rw [GlobalTheory.NL.latSpan, Submodule.map_span, serSpan]
  congr 1
  ext w
  constructor
  · rintro ⟨e, _, ⟨x, rfl⟩, -, rfl⟩
    exact ⟨_, ⟨e, x, rfl⟩, h1 e x⟩
  · rintro ⟨_, ⟨e, x, rfl⟩, rfl⟩
    obtain ⟨m, hm⟩ := hex x
    exact ⟨e, _, ⟨x, rfl⟩, ⟨m, fun k hk => by rw [hL, hm k hk, map_zero]⟩, h1 e x⟩

theorem mem_gradedSer_iff {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) (y : ℤ → M) :
    y ∈ gradedSer A ↔ IsLaurent y ∧ ∀ k, y k ∈ A (-k) := by
  constructor
  · intro hy
    refine Submodule.iSup_induction _ (motive := fun y => IsLaurent y ∧ ∀ k, y k ∈ A (-k)) hy ?_ ?_ ?_
    · rintro a y ⟨h0, h1⟩
      refine ⟨⟨-a, h0⟩, fun k => ?_⟩
      by_cases hk : k < -a
      · rw [h0 k hk]; exact zero_mem _
      · have := h1 k
        rw [hA] at this ⊢
        exact Submodule.span_mono (Set.image_mono fun s (hs : a ≤ u s) => show -k ≤ u s by omega) this
    · exact ⟨⟨0, fun _ _ => rfl⟩, fun _ => zero_mem _⟩
    · rintro y z ⟨⟨m, hm⟩, hy⟩ ⟨⟨m', hm'⟩, hz⟩
      exact ⟨⟨min m m', fun k hk => by
        rw [Pi.add_apply, hm k (by omega), hm' k (by omega), add_zero]⟩, fun k => add_mem (hy k) (hz k)⟩
  · rintro ⟨-, hy⟩
    rw [SplitFil.gradedSer_eq_range u d A hA]
    have hex : ∀ m : ℤ, ∃ c : Fin r → F, (∀ k, u k < -m → c k = 0) ∧ y m = ∑ k, c k • d k := fun m =>
      SplitFil.exists_coef u d (-m) (y m) (hA _ ▸ hy m)
    choose c hc hyc using hex
    refine ⟨fun k => PowerSeries.mk fun j => c ((j : ℤ) - u k) k, ?_⟩
    funext m
    change (∑ k, serLine (u k) (d k) (PowerSeries.mk fun j => c ((j : ℤ) - u k) k)) m = y m
    rw [Finset.sum_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold serLine
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc m k (by omega), zero_smul]

theorem spanIsLines_of_coeff (j : M →ₗ[F] M') (ex : N → ℤ → M) (hex : ∀ x, IsLaurent (ex x)) (L : N → ℤ → M')
    (hL : ∀ x k, L x k = j (ex x k)) (G : ℤ → Submodule F M)
    (hG : ∀ f, f ∈ GlobalTheory.NL.latSpan (LL := F) ex ↔ (∃ m : ℤ, ∀ k < m, f k = 0) ∧ ∀ k, f k ∈ G (-k))
    {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M') (hA : ∀ a, (G a).map j = Submodule.span F (d '' {k | a ≤ u k})) :
    SpanIsLines L u d F := by
  classical
  refine SplitFil.spanIsLines_of_graded L u d (fun a => (G a).map j) (fun x => ?_) hA ?_
  · obtain ⟨m, hm⟩ := hex x
    exact ⟨m, fun k hk => by rw [hL, hm k hk, map_zero]⟩
  rw [serSpan_eq_map j ex hex L hL]
  ext y
  rw [mem_gradedSer_iff u d _ hA]
  constructor
  · rintro ⟨f, hf, rfl⟩
    obtain ⟨⟨m, hm⟩, h⟩ := (hG f).1 hf
    exact ⟨⟨m, fun k hk => show j (f k) = 0 by rw [hm k hk, map_zero]⟩, fun k => ⟨f k, h k, rfl⟩⟩
  · rintro ⟨⟨m, hm⟩, h⟩
    choose f hf hfy using h
    refine ⟨fun k => if k < m then 0 else f k, (hG _).2 ⟨⟨m, fun k hk => if_pos hk⟩, fun k => ?_⟩, ?_⟩
    · split_ifs
      · exact zero_mem _
      · exact hf k
    · funext k
      change j (if k < m then 0 else f k) = y k
      split_ifs with hk
      · rw [map_zero, hm k hk]
      · exact hfy k

end Series

theorem linesAt_of_record (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] {K LL : FinExt l} (hA : CaseA K LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (U : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → Multiset ℤ)
    (hc : CrysWith ((D.loc l).PD K) ((HW l).W K 1 LL hA.2.2).emb T.ρ U) (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) :
    ∃ ζ : ↥LL.1, IsPrimitiveRoot ζ l ∧ LinesAt ((HW l).W K 1 LL hA.2.2) T i ζ (U i) := by
  obtain ⟨ζ, τ, hpt, hζ⟩ := GlobalTheory.exists_isPt_primitiveRoot (HW l) hA.2.2 i
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  have hτ : (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ).comp (IsScalarTower.toAlgHom ℚ_[l] ↥(K0 K) ↥K.1) =
      ((HW l).W K 1 LL hA.2.2).emb i := AlgHom.ext fun x => hpt.1 x _ rfl
  obtain ⟨hfd, hr, hfil⟩ :=
    (GlobalTheory.T.map_Dcris_eq_DdR_crystalline_unramified l (D.loc l) (D.locA l) (D.locT l) K LL hbij T.V T.ρ hc.1).2 (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)
  rw [hτ] at hfil
  obtain ⟨u, d, hu, hd, hs⟩ := GlobalTheory.Per.Sen.adapted_basis_jumps
    (DdRE ((D.loc l).PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ))
    (FildR ((D.loc l).PD K) T.ρ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ)) (U i) _ hr
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone ((D.loc l).PD K) hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Per.FilCount.filV_exhaustive ((D.loc l).PD K) (LL := ↥LL.1) x).imp fun a ha => ⟨hx, ha⟩)
    (fun x hx => GlobalTheory.Cmp.JumpDict.filV_sep ((D.loc l).PD K) (LL := ↥LL.1) x fun a => (hx a).2)
    (hc.2 i _ fun x => congrArg (fun f => f x) hτ)
  have hP : GlobalTheory.NL.Pt (HW l) hA.2.2 i ζ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ) :=
    ⟨τ, hpt, fun x y hxy => congrArg τ (Subtype.ext hxy.symm)⟩
  refine ⟨ζ, by simpa using hζ, u, d, hu, hd, spanIsLines_of_coeff (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V))
    (GlobalTheory.NL.ex (Cm l) hA.2.2 T i ζ) (((Cm l).C K 1 LL hA.2.2).tie.levB_supp T i ζ) _
    (((Cm l).C K 1 LL hA.2.2).tie.levN_eq T i ζ)
    (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.FilLet ((HW l).W K 1 LL hA.2.2) T i (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ))
    (GlobalTheory.T.wach_lattice_eq_filtration_sum_at_level D HW F Cm l K 1 LL hA.2.2 T hc.1 i ζ _ hP) u d fun a => ?_⟩
  exact (GlobalTheory.Per.FilLetUnram.toDR_FilLet _ T i _ a hbij.2 hτ (hfil a)).trans (hs a)

theorem senOp_of_record : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (hA : CaseA K LL), GlobalTheory.WachUse.SenOp ((HW l).W K 1 LL hA.2.2) :=
  fun D HW F Cm l _ _ _ hA => senOp_of_lines (Cm l) hA (linesAt_of_record D HW F Cm l hA)

end GlobalTheory.SenOperator
