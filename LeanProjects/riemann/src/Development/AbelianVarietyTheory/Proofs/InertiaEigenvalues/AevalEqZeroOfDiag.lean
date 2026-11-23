import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.InvariantsGenerators
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.JSmul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CharpolyOfDiagWith
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqOfExhaustive
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyClosedOfDictClosed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapDcrisEqDdRCrystallineUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankSpanImageEqCard
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanIsLinesOfGraded
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsPtPrimitiveRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ISupIndepDdRE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachExpansionLatticeGradedOfLevelLe

noncomputable section

namespace GlobalTheory.SenMult

open PowerSeries Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.IndefiniteRowSideFullHecke.DiagonalQuotientEigen GlobalTheory.SenLines TensorProduct
open GlobalTheory.WachTie.MatF

section Algebra

variable {O F Q : Type} [CommRing O] [Field F] [Algebra O F] [AddCommGroup Q] [Module O Q]

theorem aeval_eq_zero_of_diag [Module.Free O Q] (hinj : Function.Injective (algebraMap O F))
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

theorem aeval_comm {Q' : Type} [AddCommGroup Q'] [Module O Q'] (π : Q →ₗ[O] Q') (f : Module.End O Q)
    (f' : Module.End O Q') (h : ∀ x, π (f x) = f' (π x)) (p : Polynomial O) (x : Q) :
    π (Polynomial.aeval f p x) = Polynomial.aeval f' p (π x) := by
  induction p using Polynomial.induction_on generalizing x with
  | C a => simp
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k a ih =>
    rw [pow_succ, ← mul_assoc, map_mul _ _ Polynomial.X, map_mul _ _ Polynomial.X, Polynomial.aeval_X,
      Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply, ih, h]

open Classical in

theorem finrank_ker_of_diag [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O F] [Module.Free O Q]
    [Module.Finite O Q] (f : Q →ₗ[O] Q) (S : Multiset F) (h : DiagWith (f.baseChange F) S) (c : O) :
    Module.finrank O (LinearMap.ker (f - c • LinearMap.id)) = S.count (algebraMap O F c) := by
  obtain ⟨m, b, e, he, rfl⟩ := h
  haveI : Module.Flat O F := IsLocalization.flat F (nonZeroDivisors O)
  have h1 : LinearMap.ker (AlgebraTensorModule.lTensor F F (f - c • LinearMap.id)) =
      Submodule.span F (b '' {s | algebraMap O F c = e s}) := by
    have h2 : ∀ s, AlgebraTensorModule.lTensor F F (f - c • LinearMap.id) (b s) =
        (e s - algebraMap O F c) • b s := fun s => by
      change (f - c • LinearMap.id).baseChange F (b s) = _
      rw [LinearMap.baseChange_sub, LinearMap.baseChange_smul, LinearMap.baseChange_id, LinearMap.sub_apply, he,
        sub_smul, algebraMap_smul]
      rfl
    apply le_antisymm
    · intro x hx
      rw [b.mem_span_image]
      intro s hs
      rw [LinearMap.mem_ker, ← b.sum_repr x, map_sum] at hx
      simp only [map_smul, h2, smul_smul] at hx
      have := Fintype.linearIndependent_iff.1 b.linearIndependent _ hx s
      exact (sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left (Finsupp.mem_support_iff.1 hs))).symm
    · rw [Submodule.span_le]
      rintro _ ⟨s, hs, rfl⟩
      rw [SetLike.mem_coe, LinearMap.mem_ker, h2, show algebraMap O F c = e s from hs, sub_self, zero_smul]
  rw [← Module.finrank_baseChange (R := F), (LinearMap.tensorKerEquiv F F (f - c • LinearMap.id)).finrank_eq, h1,
    GlobalTheory.Per.Sen.finrank_span_image_eq_card b b.linearIndependent, Multiset.count_map]
  rfl

open Classical in

theorem quot_clauses [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O F] (P P' : Submodule O Q)
    (γ : Q →ₗ[O] Q) (hP : ∀ x ∈ P, γ x ∈ P)
    (hs : P'.submoduleOf P ≤ (P'.submoduleOf P).comap (γ.restrict hP))
    [Module.Free O (P ⧸ P'.submoduleOf P)] [Module.Finite O (P ⧸ P'.submoduleOf P)] (S : Multiset F)
    (h : DiagWith ((Submodule.mapQ _ _ _ hs).baseChange F) S) :
    (∀ p : Polynomial O, (∀ s ∈ S, Polynomial.aeval s p = 0) → ∀ m ∈ P, Polynomial.aeval γ p m ∈ P') ∧
    ∀ c : O, Module.finrank O (↥(P ⊓ P'.comap (γ - c • LinearMap.id)) ⧸
      P'.comap (P ⊓ P'.comap (γ - c • LinearMap.id)).subtype) = S.count (algebraMap O F c) := by
  refine ⟨fun p hp m hm => ?_, fun c => ?_⟩
  · have h1 := aeval_comm P.subtype (γ.restrict hP) γ (fun _ => rfl) p ⟨m, hm⟩
    rw [Submodule.subtype_apply, Submodule.subtype_apply] at h1
    rw [← h1]
    refine (Submodule.Quotient.mk_eq_zero (P'.submoduleOf P)).1 ?_
    rw [← Submodule.mkQ_apply, aeval_comm (Submodule.mkQ _) _ (Submodule.mapQ _ _ _ hs) (fun _ => rfl),
      aeval_eq_zero_of_diag (IsFractionRing.injective O F) _ _ h p hp, LinearMap.zero_apply]
  · let φ : ↥(P ⊓ P'.comap (γ - c • LinearMap.id)) →ₗ[O] (P ⧸ P'.submoduleOf P) :=
      (Submodule.mkQ _).comp (Submodule.inclusion inf_le_left)
    have hk : P'.comap (P ⊓ P'.comap (γ - c • LinearMap.id)).subtype = LinearMap.ker φ := by
      ext x
      exact (Submodule.Quotient.mk_eq_zero (P'.submoduleOf P) (x := Submodule.inclusion inf_le_left x)).symm
    have key : ∀ x : P, Submodule.Quotient.mk x ∈ LinearMap.ker (Submodule.mapQ _ _ _ hs - c • LinearMap.id) ↔
        (x : Q) ∈ P'.comap (γ - c • LinearMap.id) := fun x =>
      Submodule.Quotient.mk_eq_zero (P'.submoduleOf P) (x := γ.restrict hP x - c • x)
    have hr : LinearMap.range φ = LinearMap.ker (Submodule.mapQ _ _ _ hs - c • LinearMap.id) := by
      apply le_antisymm
      · rintro _ ⟨x, rfl⟩
        exact (key _).2 x.2.2
      · intro y hy
        obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
        exact ⟨⟨x, x.2, (key x).1 hy⟩, rfl⟩
    rw [hk, φ.quotKerEquivRange.finrank_eq, hr, finrank_ker_of_diag _ S h]

theorem diagWith_add_one {M : Type} [AddCommGroup M] [Module F M] (f g : M →ₗ[F] M) (hg : g = f + LinearMap.id)
    (S : Multiset F) (h : DiagWith f S) : DiagWith g (S.map (· + 1)) := by
  obtain ⟨m, b, e, he, rfl⟩ := h
  exact ⟨m, b, fun s => e s + 1, fun s => by simp [hg, he, add_smul], by rw [Multiset.map_map]; rfl⟩

end Algebra

section Lines

variable {F M : Type} [Field F] [AddCommGroup M] [Module F M]

theorem adapted_basis (D : Submodule F M) [FiniteDimensional F D] (A : ℤ → Submodule F M) (r : ℕ)
    (hr : Module.finrank F D = r) (hA : Antitone A) (hle : ∀ a, A a ≤ D) (hex : ∀ x ∈ D, ∃ a, x ∈ A a)
    (hsep : ∀ x, (∀ a, x ∈ A a) → x = 0) :
    ∃ (u : Fin r → ℤ) (d : Fin r → M), LinearIndependent F d ∧
      (∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) ∧
      ∀ a : ℤ, (Module.finrank F (A a) : ℤ) - Module.finrank F (A (a + 1)) =
        ((Finset.univ.filter fun k => a = u k).card : ℤ) := by
  classical
  obtain ⟨m, d, k, hd, hsp⟩ := GlobalTheory.filtration_adapted_basis A hA
    (Submodule.finiteDimensional_of_le (iSup_le hle)) hsep
  have hU : ∀ a : ℤ, (Module.finrank F (A a) : ℤ) - Module.finrank F (A (a + 1)) =
      ((Finset.univ.val.map k).count a : ℤ) := fun a => by
    rw [hsp a, hsp (a + 1), GlobalTheory.Per.Sen.finrank_span_image_eq_card d hd,
      GlobalTheory.Per.Sen.finrank_span_image_eq_card d hd]
    have e : (Finset.univ.filter fun i => a ≤ k i).card
        = (Finset.univ.filter fun i => a + 1 ≤ k i).card + (Finset.univ.filter fun i => a = k i).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        ext i
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
        omega
      · rw [Finset.disjoint_filter]
        intro i _ h1 h2
        omega
    have e2 : Multiset.count a (Finset.univ.val.map k) = (Finset.univ.filter fun i => a = k i).card := by
      rw [Multiset.count_map]; rfl
    omega
  obtain ⟨u, d', hu, hd', hs⟩ := GlobalTheory.Per.Sen.adapted_basis_jumps D A _ r hr hA hle hex hsep hU
  refine ⟨u, d', hd', hs, fun a => ?_⟩
  rw [hU, ← hu, Multiset.count_map]
  rfl

open GlobalTheory.SenLines.Coords in

theorem spanIsLines_of_onto {N : Type} (L : N → ℤ → M) {r : ℕ} (u : Fin r → ℤ) (d : Fin r → M)
    (hd : LinearIndependent F d) (A : ℤ → Submodule F M)
    (hA : ∀ a, A a = Submodule.span F (d '' {k | a ≤ u k})) (h1 : ∀ x k, L x k ∈ A (-k))
    (h2 : ∀ k, ∀ w ∈ A (-k), ∃ (x : N) (c : F), (∀ j < k, c • L x j ∈ A (-j + 1)) ∧ c • L x k - w ∈ A (-k + 1)) :
    SpanIsLines L u d F := by
  classical
  have hex : ∀ x (m : ℤ), ∃ c : Fin r → F, (∀ k, u k < -m → c k = 0) ∧ L x m = ∑ k, c k • d k := fun x m =>
    SplitFil.exists_coef u d (-m) _ (hA _ ▸ h1 x m)
  choose c hc hyc using hex
  let e : N → Fin r → F⟦X⟧ := fun x k => PowerSeries.mk fun j => c x ((j : ℤ) - u k) k
  have he : ∀ x, L x = lines u d (e x) := fun x => by
    funext m
    rw [lines_apply, hyc]
    refine Finset.sum_congr rfl fun k _ => ?_
    unfold zc
    split_ifs with h
    · rw [coeff_mk, Int.toNat_of_nonneg h, add_sub_cancel_right]
    · rw [hc x m k (by omega)]
  have hz : ∀ (a : ℤ) (v : Fin r → F), ∑ k, v k • d k ∈ A a → ∀ k, u k < a → v k = 0 := fun a v hv k hk => by
    obtain ⟨c', hc', h⟩ := SplitFil.exists_coef u d a _ (hA _ ▸ hv)
    have := Fintype.linearIndependent_iff.1 hd (fun k => v k - c' k)
      (by simp only [sub_smul, Finset.sum_sub_distrib, h, sub_self]) k
    rw [sub_eq_zero.1 this, hc' k hk]
  choose x a hx hx' using fun s => h2 (-u s) (d s) (by
    rw [hA]; exact Submodule.subset_span ⟨s, by simp, rfl⟩)
  let Mx : Matrix (Fin r) (Fin r) F⟦X⟧ := Matrix.of fun k s => C (a s) * e (x s) k
  have hM0 : ∀ k s, constantCoeff (Mx k s) = a s * c (x s) (-u k) k := fun k s => by
    simp [Mx, e, ← coeff_zero_eq_constantCoeff_apply]
  have hlt : ∀ k s, u s < u k → constantCoeff (Mx k s) = 0 := fun k s h => by
    have h3 := hx s (-u k) (by omega)
    rw [hyc, Finset.smul_sum] at h3
    simp only [smul_smul] at h3
    rw [hM0]
    exact hz _ _ h3 k (by omega)
  have heq : ∀ k s, u s = u k → constantCoeff (Mx k s) = if k = s then 1 else 0 := fun k s h => by
    have h3 := hx' s
    have h4 : d s = ∑ k, (if k = s then (1 : F) else 0) • d k := by simp
    rw [hyc, Finset.smul_sum, h4, ← Finset.sum_sub_distrib] at h3
    simp only [smul_smul, ← sub_smul] at h3
    rw [hM0, ← h]
    exact sub_eq_zero.1 (hz _ _ h3 k (by omega))
  have hdet : IsUnit Mx.det := by
    rw [isUnit_iff_constantCoeff, RingHom.map_det, isUnit_iff_ne_zero, Ne, ← Matrix.exists_mulVec_eq_zero_iff]
    rintro ⟨v, hv, h0⟩
    obtain ⟨k, hk, hmax⟩ := Finset.exists_max_image (Finset.univ.filter fun k => v k ≠ 0) u (by
      obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
      exact ⟨k, by simpa using hk⟩)
    have h3 := congrFun h0 k
    rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single k] at h3
    · change constantCoeff (Mx k k) * v k = 0 at h3
      rw [heq k k rfl, if_pos rfl, one_mul] at h3
      exact (Finset.mem_filter.1 hk).2 h3
    · intro s _ hs
      change constantCoeff (Mx k s) * v s = 0
      by_cases hvs : v s = 0
      · rw [hvs, mul_zero]
      rcases (hmax s (by simpa using hvs)).lt_or_eq with h | h
      · rw [hlt k s h, zero_mul]
      · rw [heq k s h, if_neg (Ne.symm hs), zero_mul]
    · simp
  intro y
  constructor
  · rintro ⟨s, z, f, rfl⟩
    refine ⟨∑ j, f j • e (z j), ?_⟩
    change _ = lines u d _
    rw [lines_sum]
    simp only [he, serAct_lines]
  · rintro ⟨c', rfl⟩
    obtain ⟨f, hf⟩ := Matrix.mulVec_surjective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det Mx).2 hdet) c'
    refine ⟨r, x, fun s => f s * C (a s), ?_⟩
    change lines u d _ = _
    simp only [he, serAct_lines]
    rw [← lines_sum, ← hf]
    congr 1
    funext k
    simp only [Matrix.mulVec, dotProduct, Mx, Matrix.of_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun s _ => by ring

end Lines

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O) (J : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n)

theorem diag_quot [CharZero LL] (hinj : Function.Injective (algebraMap O LL))
    {g : W.Gam} (hJ : QFrame W g J) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p) (χ : LL) (hχ : χ ≠ 0)
    (hχ' : ∀ k : ℕ, 0 < k → χ ^ k ≠ 1)
    (hρ : ∀ f, W.lev i ζ (W.γA g f) = rescale χ (W.lev i ζ f))
    (u : Fin r → ℤ) (e : ↥(W.N T) →+ (Fin r → LL⟦X⟧))
    (he : ∀ a x, e (a • x) = W.lev i ζ a • e x) (hsp : Submodule.span LL⟦X⟧ (Set.range e) = ⊤)
    (hγ : ∀ (x : ↥(W.N T)) hx k, e ⟨W.γD T g x, hx⟩ k = C (χ ^ (-u k)) * rescale χ (e x k))
    (j j' : ℤ) (hj : j ≤ j') :
    Module.Free O (qQuot W T i j j') ∧ Module.Finite O (qQuot W T i j j') ∧
    ∃ (hP : ∀ x ∈ qN W T i j, W.γD T g x ∈ qN W T i j)
      (hs : (qN W T i j').submoduleOf (qN W T i j) ≤
        ((qN W T i j').submoduleOf (qN W T i j)).comap ((W.γD T g).restrict hP)),
      DiagWith ((Submodule.mapQ _ _ _ hs).baseChange LL)
        ((Finset.univ : Finset (Fin r × Fin (j' - j).toNat)).val.map fun x => χ ^ (j - u x.1 + (x.2 : ℕ))) := by
  obtain ⟨s, hs, -⟩ := hJ.2.2.2.2.1
  obtain ⟨Qu, hQ⟩ : IsUnit (algebraMap (LetA O n) W.EE (qΔ W)) := hJ.2.2.2.2.2.2
  obtain ⟨θ, hθ⟩ := exists_theta W T J b i hJ hb Qu hQ j
  have hP' : ∀ c, θ c ∈ (qN W T i j').submoduleOf (qN W T i j) ↔
      ∀ k, (X : O⟦X⟧) ^ (j' - j).toNat ∣ c k := fun c => by
    rw [← theta_mem W T J b i hJ hb Qu hQ hj, ← hθ]; rfl
  obtain ⟨eq⟩ := quot_equiv _ _ θ hP'
  have hγθ : ∀ c d, W.γD T g (th W T J b i c) = th W T J b i d →
      W.γD T g (θ c) = θ (((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • d) := fun c d hd => by
    rw [hθ, hθ, γD_zpow W T J hJ s hs Qu hQ, hd, smul_th W T J b i (cst_apply J i _)]
  have hP : ∀ x ∈ qN W T i j, W.γD T g x ∈ qN W T i j := fun x hx => by
    obtain ⟨c, hc⟩ := θ.surjective ⟨x, hx⟩
    obtain ⟨d, hd⟩ := γD_th W T J b i hJ hb c
    have := hγθ c _ hd
    rw [hc] at this
    rw [this]
    exact Subtype.property _
  refine ⟨Module.Free.of_equiv eq.symm, Module.Finite.equiv eq.symm, hP, ?_⟩
  obtain ⟨η, hη⟩ := exists_eta W J i hJ ζ hζ
  obtain ⟨M, hM, hMe⟩ := exists_matrix W T J b i ζ e he
  have hMu : IsUnit M.det :=
    (Matrix.isUnit_iff_isUnit_det M).1 (Matrix.mulVec_surjective_iff_isUnit.1 (hM hsp))
  let Λu : (O⟦X⟧)ˣ →* (LL⟦X⟧)ˣ := Units.map (abelian₂ W J i ζ).toRingHom.toMonoidHom
  obtain ⟨μ, hμ⟩ := exists_mu _ hχ η 1 (Λu s) 1 j 0 (by
    have h1 := hρ (cst J X)
    rw [lev_eq W J i ζ (e := X * (s : O⟦X⟧)) (by rw [map_mul, ← hs]; rfl), map_mul] at h1
    change _ = rescale _ (abelian₂ W J i ζ X) at h1
    rw [hη, map_mul, rescale_X] at h1
    apply mul_left_cancel₀ (X_ne_zero (R := LL))
    change X * ((η : LL⟦X⟧) * abelian₂ W J i ζ s) = _
    linear_combination h1) (by simp)
  rw [← map_zpow, add_zero, Units.val_one, mul_one] at hμ
  change abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) * (μ : LL⟦X⟧) = _ at hμ
  obtain ⟨hst, hd⟩ := GlobalTheory.TruncDiag.diagWith_trunc _ _ _ θ (abelian₂ W J i ζ) η 1 ((μ : LL⟦X⟧) • M) χ
    (fun k => χ ^ (j - u k)) ((W.γD T g).restrict hP - LinearMap.id) hinj hP' hη η.isUnit
    (by rw [Matrix.det_smul]; exact (μ.isUnit.pow _).mul hMu) (by simp) hχ hχ' (fun k => zpow_ne_zero _ hχ) (by
      intro c c' hcc k
      obtain ⟨d, hd⟩ := γD_th W T J b i hJ hb c
      set d' := c + (X - ((PD.p : ℕ) : O⟦X⟧)) • d
      have h1 : c' = ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • d' - c := by
        apply θ.injective
        rw [← hcc, map_sub]
        apply Subtype.ext
        change W.γD T g (θ c) - θ c = (θ _ : W.DD T) - θ c
        rw [hγθ c _ hd]
      have h2 : (fun k => abelian₂ W J i ζ (c' k)) =
          abelian₂ W J i ζ ((s ^ j : (O⟦X⟧)ˣ) : O⟦X⟧) • (fun k => abelian₂ W J i ζ (d' k)) -
            (fun k => abelian₂ W J i ζ (c k)) := by
        funext k
        simp [h1]
      have h3 := congrFun (congrArg M.mulVec h2) k
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul] at h3
      have h4 := hγ ⟨_, th_mem_N W T J b i c⟩ (hd ▸ th_mem_N W T J b i d') k
      simp only [hd] at h4
      rw [hMe, hMe] at h4
      simp only [Matrix.smul_mulVec, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, map_mul] at h3 ⊢
      rw [h4] at h3
      rw [sub_eq_add_neg j, zpow_add₀ hχ, map_mul]
      linear_combination (μ : LL⟦X⟧) * h3 + C (χ ^ (-u k)) *
        rescale χ (M.mulVec (fun k => abelian₂ W J i ζ (c k)) k) * hμ)
  have hs' : (qN W T i j').submoduleOf (qN W T i j) ≤
      ((qN W T i j').submoduleOf (qN W T i j)).comap ((W.γD T g).restrict hP) := fun x hx => by
    have := Submodule.add_mem _ (Submodule.mem_comap.1 (hst hx)) hx
    simpa using this
  refine ⟨hs', ?_⟩
  have := diagWith_add_one _ ((Submodule.mapQ _ _ _ hs').baseChange LL) (by
    rw [← LinearMap.baseChange_id (R := O), ← LinearMap.baseChange_add]
    congr 1
    ext x
    simp) _ hd
  rw [Multiset.map_map] at this
  convert this using 3 with x
  simp [zpow_add₀ hχ]

open Formalism.MainNotions in
theorem ENΔ_eq {g : W.Gam} (hJ : QFrame W g J) (y : ℕ) : tableLineDegreeTwo.ENΔ W T i y = qN W T i (-(y : ℤ)) := by
  obtain ⟨Qu, hQ⟩ : IsUnit (algebraMap (LetA O n) W.EE (qΔ W)) := hJ.2.2.2.2.2.2
  have hinj : ∀ x x' : W.DD T, qΔ W ^ y • x = qΔ W ^ y • x' → x = x' := fun x x' h => by
    rw [← algebraMap_smul W.EE, ← algebraMap_smul W.EE _ x', map_pow, ← hQ, ← Units.val_pow_eq_pow_val] at h
    exact MulAction.injective (Qu ^ y) h
  have hδ : ∀ δ ∈ W.DelF, ∀ x : W.DD T, W.γD T δ (qΔ W ^ y • x) = qΔ W ^ y • W.γD T δ x := fun δ hδ x => by
    rw [γD_smulA, map_pow]
    congr 2
    rw [qΔ_eq W J hJ]
    exact funext fun _ => (hJ.2.1 _).1 ⟨X, rfl⟩ δ hδ
  have hE : (letE i * letE i : LetA O n) = letE i := by rw [letE, mul_single]; simp
  ext x
  have h1 : x ∈ qN W T i (-(y : ℤ)) ↔ qΔ W ^ y • x ∈ NΔl W T i := by
    rw [qN, show (-(y : ℤ)).toNat = 0 by omega, neg_neg, Int.toNat_natCast, pow_zero,
      show mulD W T 1 = LinearMap.id from LinearMap.ext fun z => one_smul _ z, Submodule.map_id]
    rfl
  have h2 : x ∈ tableLineDegreeTwo.ENΔ W T i y ↔ (qΔ W ^ y • x ∈ W.N T ∧ (letE i : LetA O n) • x = x) ∧
      ∀ δ ∈ W.DelF, W.γD T δ x = x := by
    simp only [tableLineDegreeTwo.ENΔ, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.id_apply, sub_eq_zero]
    rfl
  rw [h1, h2]
  constructor
  · rintro ⟨⟨h3, h4⟩, h5⟩
    refine ⟨⟨h3, fun δ h => by rw [hδ δ h, h5 δ h]⟩, _, h3, ?_⟩
    change (letE i : LetA O n) • qΔ W ^ y • x = _
    rw [smul_comm, h4]
  · rintro ⟨⟨h3, h4⟩, z, -, hz⟩
    have hz' : (letE i : LetA O n) • z = qΔ W ^ y • x := hz
    refine ⟨⟨h3, hinj _ _ ?_⟩, fun δ h => hinj _ _ (by rw [← hδ δ h, h4 δ h])⟩
    rw [smul_comm, ← hz', smul_smul, hE]

open Formalism.MainNotions in
theorem EkNΔ_eq {g : W.Gam} (hJ : QFrame W g J) (k : ℕ) : tableLineDegreeTwo.EkNΔ W T i k = qN W T i k := by
  rw [tableLineDegreeTwo.EkNΔ, ENΔ_eq W T J i hJ, Nat.cast_zero, neg_zero, qN_zero, qN,
    show (-(k : ℤ)).toNat = 0 by omega, Int.toNat_natCast]
  ext x
  simp only [Submodule.mem_comap, pow_zero]
  rw [show mulD W T 1 x = x from one_smul _ x]
  rfl

omit T J i in

theorem count_pairs {r : ℕ} (u : Fin r → ℤ) (y k : ℕ) (x : ℤ) :
    ((Finset.univ.filter fun p : Fin r × Fin ((k : ℤ) - -(y : ℤ)).toNat => -x = -(y : ℤ) - u p.1 + (p.2 : ℕ)).card : ℤ) =
      ∑ j ∈ Finset.Icc (1 - (k : ℤ)) (y : ℤ), ((Finset.univ.filter fun s => x - j = u s).card : ℤ) := by
  rw [← Nat.cast_sum, ← Finset.card_sigma]
  congr 1
  refine Finset.card_bij (fun p _ => ⟨(y : ℤ) - (p.2 : ℕ), p.1⟩) (fun p hp => ?_) (fun p _ q _ h => ?_)
    (fun p hp => ?_)
  · have := p.2.2
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    omega
  · obtain ⟨h1, h2⟩ := Sigma.mk.inj h
    exact Prod.ext (eq_of_heq h2) (Fin.ext (by omega))
  · obtain ⟨a, s⟩ := p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sigma, Finset.mem_Icc] at hp ⊢
    refine ⟨(s, ⟨((y : ℤ) - a).toNat, by omega⟩), by simp only; omega, ?_⟩
    congr 1
    simp only
    omega

open Formalism.MainNotions in

theorem lines_of_coeff (hK : Function.Surjective (algebraMap K₀ K)) (τ : K →ₐ[Qp] LL)
    (hτ : τ.comp (IsScalarTower.toAlgHom Qp K₀ K) = W.emb i) (ζ : LL)
    (hD : ∀ x k, W.levN T i ζ x k ∈ DeltaInvariantLattices.ιDi W T i)
    (h1 : ∀ (x : ↥(W.N T)) (k : ℤ), W.levN T i ζ ((letE i : LetA O n) • x) k ∈
      DeltaInvariantLattices.ιDi W T i ⊓ DeltaInvariantLattices.FilC (PD := PD) T τ (-k))
    (h2 : ∀ (k : ℤ), ∀ w ∈ FildR PD T.ρ τ (-k), ∃ (x : ↥(W.N T)) (c : LL), c ≠ 0 ∧
      (∀ j < k, c • W.levN T i ζ ((letE i : LetA O n) • x) j ∈ DeltaInvariantLattices.FilC (PD := PD) T τ (-j + 1)) ∧
      c • W.levN T i ζ ((letE i : LetA O n) • x) k - w ∈ DeltaInvariantLattices.FilC (PD := PD) T τ (-k + 1))
    {r : ℕ} (u : Fin r → ℤ) (d : Fin r → T.V ⊗[Qp] BdR) (hd : LinearIndependent LL d)
    (hA : ∀ a, FildR PD T.ρ τ a = Submodule.span LL (d '' {k | a ≤ u k})) :
    SpanIsLines (W.levN T i ζ) u d LL := by
  have hE : ∀ x : ↥(W.N T), W.levN T i ζ ((letE i : LetA O n) • x) = W.levN T i ζ x := fun x => by
    have h3 := W.lev_letter i ζ (letE i - 1) (by simp [letE])
    rw [map_sub, map_one, sub_eq_zero] at h3
    refine Eq.trans (funext fun k => ?_) (serAct_one (F := LL) _)
    rw [W.levN_smul, h3]
    rfl
  have hD' : ∀ x k, W.levN T i ζ x k ∈ DdRE PD T.ρ τ := fun x k => by
    obtain ⟨z, hz, h⟩ := hD x k
    rw [← h]
    exact GlobalTheory.Per.FilLetUnram.ι_mem_DdRE PD T.ρ hK τ (by rw [hτ]; exact hz)
  have hF : ∀ a z, z ∈ DdRE PD T.ρ τ → z ∈ DeltaInvariantLattices.FilC (PD := PD) T τ a → z ∈ FildR PD T.ρ τ a := fun a x hx hx' => by
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hx'
    have hzD : z ∈ DdRE PD T.ρ τ := by
      rw [eq_sub_of_add_eq' hyz]
      exact Submodule.sub_mem _ hx hy.1
    rw [← hyz, (Submodule.disjoint_def.1 (GlobalTheory.Per.FilLetUnram.iSupIndep_DdRE PD T.ρ τ)) z hzD hz, add_zero]
    exact hy
  simp only [hE] at h1 h2
  refine spanIsLines_of_onto _ u d hd _ hA (fun x k => hF _ _ (hD' x k) (h1 x k).2) fun k w hw => ?_
  obtain ⟨x, c, -, h3, h4⟩ := h2 k w hw
  exact ⟨x, c, fun j hj => hF _ _ (Submodule.smul_mem _ _ (hD' x j)) (h3 j hj),
    hF _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ (hD' x k)) hw.1) h4⟩

open Formalism.MainNotions in

theorem clauses_of_lines [CharZero LL] [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    (hJ : QFrame W W.gam J) {r : ℕ} (b : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    (hb : ∀ k, (b k : W.DD T) ∈ W.NΔ T) (ζ : LL) (hζ : IsPrimitiveRoot ζ PD.p)
    (hχ' : ∀ k : ℤ, k ≠ 0 → algebraMap O LL (W.χΓ W.gam : O) ^ k ≠ 1)
    (hρ : ∀ f, W.lev i ζ (W.γA W.gam f) = rescale (algebraMap O LL (W.χΓ W.gam : O)) (W.lev i ζ f))
    (hγ : ∀ (x : ↥(W.N T)) hx (k : ℤ), W.levN T i ζ ⟨W.γD T W.gam x, hx⟩ k =
      algebraMap O LL (W.χΓ W.gam : O) ^ k • W.levN T i ζ x k)
    (u : Fin r → ℤ) (d : Fin r → T.V ⊗[Qp] BdR) (hd : LinearIndependent LL d)
    (hL : SpanIsLines (W.levN T i ζ) u d LL) (y k : ℕ) :
    Module.Free O (↥(tableLineDegreeTwo.ENΔ W T i y) ⧸ (tableLineDegreeTwo.EkNΔ W T i k).comap (tableLineDegreeTwo.ENΔ W T i y).subtype) ∧
      Module.Finite O (↥(tableLineDegreeTwo.ENΔ W T i y) ⧸ (tableLineDegreeTwo.EkNΔ W T i k).comap (tableLineDegreeTwo.ENΔ W T i y).subtype) ∧
      (∃ F : Finset ℤ, ∀ m ∈ tableLineDegreeTwo.ENΔ W T i y, Polynomial.aeval (W.γ T) (∏ x ∈ F,
        (Polynomial.X - Polynomial.C ((((DeltaInvariantLattices.uU W) ^ (-x) : Oˣ)) : O))) m ∈ tableLineDegreeTwo.EkNΔ W T i k) ∧
      ∀ x : ℤ, (Module.finrank O (↥(tableLineDegreeTwo.SenEig W T i y k x) ⧸
          (tableLineDegreeTwo.EkNΔ W T i k).comap (tableLineDegreeTwo.SenEig W T i y k x).subtype) : ℤ) =
        ∑ j ∈ Finset.Icc (1 - (k : ℤ)) (y : ℤ), ((Finset.univ.filter fun s => x - j = u s).card : ℤ) := by
  classical
  have hinj := IsFractionRing.injective O LL
  have hχ : algebraMap O LL (W.χΓ W.gam : O) ≠ 0 := ((W.χΓ W.gam).isUnit.map _).ne_zero
  have hu : ∀ a : ℤ, algebraMap O LL ((DeltaInvariantLattices.uU W ^ a : Oˣ) : O) = algebraMap O LL (W.χΓ W.gam : O) ^ a := fun a => by
    have := map_zpow (Units.map (algebraMap O LL).toMonoidHom) (DeltaInvariantLattices.uU W) a
    have h2 := congrArg Units.val this
    rw [Units.val_zpow_eq_zpow_val] at h2
    exact h2
  obtain ⟨e, h1, h2, h3⟩ := GlobalTheory.SenLines.Coords.exists_coords (W.lev i ζ) (W.levN T i ζ) u d hd
    (fun a x => funext fun k => W.levN_smul T i ζ a x k) hL
  obtain ⟨hfr, hfi, hP, hs, hdiag⟩ := diag_quot W T J i hinj hJ b hb ζ hζ _ hχ
    (fun k hk => by rw [← zpow_natCast]; exact hχ' k (by omega)) hρ u e h1 h2
    (fun x hx k => h3 _ x _ hχ (hγ x hx) k) (-(y : ℤ)) k (by omega)
  obtain ⟨c1, c2⟩ := quot_clauses (F := LL) _ _ _ hP hs _ hdiag
  unfold tableLineDegreeTwo.SenEig
  rw [ENΔ_eq W T J i hJ, EkNΔ_eq W T J i hJ]
  refine ⟨hfr, hfi, ⟨Finset.univ.image fun p : Fin r × Fin ((k : ℤ) - -(y : ℤ)).toNat =>
    -(-(y : ℤ) - u p.1 + (p.2 : ℕ)), c1 _ fun s hs => ?_⟩, fun x => ?_⟩
  · obtain ⟨p, -, rfl⟩ := Multiset.mem_map.1 hs
    rw [map_prod]
    refine Finset.prod_eq_zero (Finset.mem_image_of_mem _ (Finset.mem_univ p)) ?_
    rw [map_sub, Polynomial.aeval_X, Polynomial.aeval_C, hu, neg_neg, sub_self]
  · rw [← count_pairs]
    congr 1
    refine (c2 _).trans ?_
    rw [Multiset.count_map, hu]
    change (Finset.univ.filter _).card = _
    congr 1
    refine Finset.filter_congr fun p _ => ⟨fun h => ?_, fun h => by rw [h]⟩
    by_contra hne
    exact hχ' _ (sub_ne_zero.2 hne) (by rw [zpow_sub₀ hχ, h, div_self (zpow_ne_zero _ hχ)])

open Formalism.MainNotions in

theorem senLat_of_tie [CharZero LL] [IsDomain O] [IsPrincipalIdealRing O] [IsFractionRing O LL]
    {Zl Ai : Type} [CommRing Zl] [CommRing Ai] [Algebra Zl O] [Algebra Zl Ai]
    {RW : Type} [CommRing RW] [Algebra O RW]
    {inclR : (O ⊗[Zl] Ai) →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : O ⊗[Zl] Ai}
    {E : EtTie W (O ⊗[Zl] Ai) RW inclR φR gR πA} {ιdR : Ai →+* BdR} {p1 : Ai} {tS zS : BdR}
    (tie : CmpTie W E ιdR p1 tS zS) (hs : W.s = 1) (hK : Function.Surjective (algebraMap K₀ K))
    (hJ : QFrame W W.gam J) (Pt : ZMod n → LL → (K →ₐ[Qp] LL) → Prop) (h4 : DeltaInvariantLattices.P4W W Pt)
    (hPt : ∀ i τ, tableLineDegreeTwo.Over W.emb i τ → ∃ ζ, IsPrimitiveRoot ζ PD.p ∧ Pt i ζ τ)
    (hb : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ →
      ∃ b : Module.Basis (Fin (Module.finrank LL T.V)) (LetA O n) ↥(W.N T), ∀ k, (b k : W.DD T) ∈ W.NΔ T)
    (hd : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ τ : K →ₐ[Qp] LL, FiniteDimensional LL ↥(DdRE PD T.ρ τ) ∧
      Module.finrank LL ↥(DdRE PD T.ρ τ) = Module.finrank LL T.V) : tableLineDegreeTwo.SenLat W := by
  intro T hcr i τ hτ y k
  obtain ⟨ζ, hζ, hP⟩ := hPt i τ hτ
  obtain ⟨b, hb⟩ := hb T hcr
  obtain ⟨hfd, hr⟩ := hd T hcr τ
  obtain ⟨u, d, hd, hsp, hu⟩ := adapted_basis (DdRE PD T.ρ τ) (FildR PD T.ρ τ) _ hr
    (fun a b hab => inf_le_inf_left _ (GlobalTheory.Per.FilCount.filV_antitone PD hab)) (fun a => inf_le_left)
    (fun x hx => (GlobalTheory.Per.FilCount.filV_exhaustive PD (LL := LL) x).imp fun a ha => ⟨hx, ha⟩)
    (fun x hx => GlobalTheory.Cmp.JumpDict.filV_sep PD (LL := LL) x fun a => (hx a).2)
  obtain ⟨-, h41, h42⟩ := (h4 T hcr).2 i ζ τ hP
  have hL := lines_of_coeff W T i hK τ hτ ζ
    (fun x k => ⟨_, tie.levB_mem T i ζ x k, (tie.levN_eq T i ζ x k).symm⟩) h41 h42 u d hd hsp
  have hg := W.gam_gen
  have hζ' : IsPrimitiveRoot ζ (PD.p ^ 1) := by rwa [pow_one]
  have hv : ((1 : ℕ) : WithTop ℚ) ≤ v (algebraMap O LL (W.χΓ W.gam : O) - ((1 : ℕ) : LL)) := by
    rw [Nat.cast_one (R := LL), hg, hs]
  have := clauses_of_lines W T J i hJ b hb ζ hζ
    (GlobalTheory.NL.GradedLat.zpow_ne_one _ PD.hp W.v_l W.s_pos W.s_two hg)
    (tie.lev_Γ _ i ζ ζ 1 1 hζ' hv (pow_one ζ).symm)
    (fun x hx k => by
      rw [tie.levN_eq, tie.levN_eq, tie.levB_Γ T hcr _ i ζ ζ 1 1 hζ' hv (pow_one ζ).symm x hx k, map_smul])
    u d hd hL y k
  simp only [multV, hu]
  exact this

end Generic

open Formalism.MainNotions in
set_option maxHeartbeats 1000000 in

theorem senLat_of_coeff {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} (hT : LocTied l P AI)
    {H : LocHW l P} {E : LocFon l P AI H} (C : LocCmpT l P AI H E) {K LL : FinExt l} (hA : CaseA K LL)
    (Pt : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥LL.1 → (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Prop)
    (hPt : ∀ i ζ τ, H.IsPt hA.2.2 i ζ τ → Pt i ζ (GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τ))
    (h4 : DeltaInvariantLattices.P4W (H.W K 1 LL hA.2.2) Pt) : tableLineDegreeTwo.SenLat (H.W K 1 LL hA.2.2) := by
  have hp := P.PD_p K
  have hs := H.W_s K 1 LL hA.2.2
  have hbij : Function.Bijective (algebraMap ↥(K0 K) ↥K.1) :=
    ⟨(algebraMap ↥(K0 K) ↥K.1).injective, fun x => ⟨⟨x.1, x.2, hA.1 x.2⟩, rfl⟩⟩
  obtain ⟨hdvr, -, hl⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  have : FiniteDimensional ℚ_[l] ↥LL.1 := LL.2
  have : IsFractionRing ↥(OL LL) ↥LL.1 := integralClosure.isFractionRing_of_finite_extension ℚ_[l] ↥LL.1
  have hc := GlobalTheory.TorsionCard.card_torsion_mul_finrank P K LL (H.W K 1 LL hA.2.2) hA.2.1 hA.2.2.2.2.1
  rw [Algebra.finrank_eq_one_iff_bijective_algebraMap.2 hbij, mul_one] at hc
  have hcard : IsUnit ((H.W K 1 LL hA.2.2).DelF.card : ↥(OL LL)) := by
    have h1 := IsLocalRing.isUnit_or_isUnit_one_sub_self (l : ↥(OL LL))
    rw [hc, Nat.cast_sub (Fact.out : l.Prime).one_le, Nat.cast_one, ← IsUnit.neg_iff, neg_sub]
    exact h1.resolve_left hl
  obtain ⟨χ, hχ, hχ1⟩ := GlobalTheory.exists_cyclotomicChar_padicInt_units P K LL (H.W K 1 LL hA.2.2)
  obtain ⟨_, _, hu⟩ := GlobalTheory.FinExtIntegers.dvr_complete LL
  obtain ⟨σ, hσ⟩ := GlobalTheory.NB.LT.exists_algEquiv_X_add_C (IsLocalRing.maximalIdeal ↥(OL LL)) (l : ↥(OL LL)) hu
  obtain ⟨J, hJ⟩ := exists_qFrame_of_card (H.W K 1 LL hA.2.2) hp χ hχ hA.2.1 hc σ hσ _ (hχ1 hs).symm.dvd
  refine senLat_of_tie _ J (C.C K 1 LL hA.2.2).tie hs hbij.2 hJ Pt h4 (fun i τ hτ => ?_) (fun T hcr => ?_)
    fun T hcr τ => ?_
  · obtain ⟨ζ, τs, hpt, hζ⟩ := GlobalTheory.exists_isPt_primitiveRoot H hA.2.2 i
    have hτs : GlobalTheory.IndefiniteRowSideFullHecke.GradedSeries.resEmb hA.2.2 τs = τ := AlgHom.ext fun x => by
      obtain ⟨x, rfl⟩ := hbij.2 x
      exact (hpt.1 x _ rfl).trans (congrArg (fun f => f x) hτ).symm
    exact ⟨ζ, by rw [hp]; simpa using hζ, hτs ▸ hPt i ζ τs hpt⟩
  · obtain ⟨b₀⟩ := GlobalTheory.WachFree.wach_free P H K 1 LL hA.2.2 T hcr
    exact GlobalTheory.WachTie.exists_invariant_basis _ T hcard ⟨b₀.reindex (finCongr (finrank_lattice T.L))⟩
  · obtain ⟨h1, h2, -⟩ := (GlobalTheory.Per.DdREqDcris.map_Dcris_eq_DdR l P AI hT K LL hbij T.V T.ρ hcr).2 τ
    exact ⟨h1, h2⟩

end GlobalTheory.SenMult

open GlobalTheory.AdmLoc GlobalTheory.TopSteps Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions in

theorem GlobalTheory.SenMult.stmtSen : ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F), InvariantsGenerators.SenOperatorTheorem D HW F Cm :=
  fun D HW _ Cm h l _ K LL hA => GlobalTheory.SenMult.senLat_of_coeff (D.locT l) (Cm l) hA (DeltaInvariantLattices.ptK D.loc HW hA.2.2)
    (fun _ _ τ hτ => ⟨τ, hτ, fun _ _ hxy => congrArg τ (Subtype.ext hxy.symm)⟩) (h.2.1 l K 1 LL hA.2.2)
