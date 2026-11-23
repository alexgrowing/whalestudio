import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardLeOfSpan
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.T2SpaceLocalLatticeRepresentationSpace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DvrComplete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GammaActionReduction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachModuleGeneratorReductionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionCyclotomicEndoEqFrobeniusLaurentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsDiagonalRingHomOfLetterwiseReductionsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusFixedTensorEqConstantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentWittTiltEqZeroOfResidueZeroStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KernelInverseFibreProductLatticesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeQuotientsClosedSubQuotSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FixedOfFixedByDeltaGammaLiftsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerRootsActFaithfullyLaurentStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsLetterBijectionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ReductionMapPi0Statement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankAndKernelOfLetterImageTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsExactFunctorPhiGammaOfFramesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFrameOfTorsionInvariantsStatement

noncomputable section

namespace GlobalTheory.RedFun

open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models GlobalTheory.Present Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions TensorProduct
open scoped LaurentSeries PowerSeries

section Alg

variable {k Rk : Type} [Field k] [CommRing Rk] [Algebra k Rk]

theorem one_tmul_inj [Nontrivial Rk] {m : ℕ} {t t' : Fin m → k}
    (h : (1 : Rk) ⊗ₜ[k] t = (1 : Rk) ⊗ₜ[k] t') : t = t' := by
  classical
  funext j
  have := congrFun (congrArg (TensorProduct.piScalarRight k Rk Rk (Fin m)) h) j
  simp only [TensorProduct.piScalarRight_apply, TensorProduct.piScalarRightHom_tmul,
    ← Algebra.algebraMap_eq_smul_one] at this
  exact (algebraMap k Rk).injective this

theorem fixed_tensor (φ : Rk →ₐ[k] Rk) (hφ : ∀ x, φ x = x → ∃ c : k, x = algebraMap k Rk c) {m : ℕ}
    (y : Rk ⊗[k] (Fin m → k)) (hy : Phi φ m y = y) : ∃ t, y = (1 : Rk) ⊗ₜ[k] t := by
  classical
  have key : ∀ (z : Rk ⊗[k] (Fin m → k)) j, TensorProduct.piScalarRight k Rk Rk (Fin m) (Phi φ m z) j =
      φ (TensorProduct.piScalarRight k Rk Rk (Fin m) z j) := by
    intro z j
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a t => simp
    | add a b ha hb => simp only [map_add, Pi.add_apply, ha, hb]
  have h1 := fun j => hφ _ (by rw [← key y j, hy])
  choose c hc using h1
  refine ⟨c, (TensorProduct.piScalarRight k Rk Rk (Fin m)).injective (funext fun j => ?_)⟩
  rw [hc j]
  simp [Algebra.algebraMap_eq_smul_one]

theorem laurent_ext {R : Type} [CommRing R] {f g : k⸨X⸩ →+* R}
    (h : ∀ a : k⟦X⟧, f (a : k⸨X⸩) = g (a : k⸨X⸩)) (x : k⸨X⸩) : f x = g x := by
  have : f = g := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (PowerSeries.X : k⟦X⟧))
    exact RingHom.ext h
  rw [this]

end Alg

section Letters

variable {O : Type} [CommRing O] {n : ℕ}

theorem letE_mul_self (i : ZMod n) : (letE i : LetA O n) * letE i = letE i := by
  funext j
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

theorem letE_mul_ne {i j : ZMod n} (h : i ≠ j) : (letE i : LetA O n) * letE j = 0 := by
  funext t
  by_cases h1 : t = i
  · subst h1; simp [letE, h]
  · simp [letE, h1]

theorem sum_letE [NeZero n] : ∑ i, (letE i : LetA O n) = 1 := by
  funext t
  simp [letE, Finset.sum_apply, Pi.single_apply]

theorem letφ_letE (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letφ f (letE (i - 1) : LetA O n) = letE i := by
  funext j
  change f ((letE (i - 1) : LetA O n) (j - 1)) = _
  by_cases h : j = i
  · subst h; simp [letE]
  · have : j - 1 ≠ i - 1 := fun e => h (sub_left_injective e)
    simp [letE, h, this]

theorem letγ_letE (f : O⟦X⟧ →ₐ[O] O⟦X⟧) (i : ZMod n) : letγ f (letE i : LetA O n) = letE i := by
  funext j
  change f ((letE i : LetA O n) j) = _
  by_cases h : j = i
  · subst h; simp [letE]
  · simp [letE, h]

end Letters

section Comparison₂

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA) {k : Type} [Field k] [Algebra O k]
    {Rk : Type} [CommRing Rk] [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] (ρ : RW →ₐ[O] Rk)

theorem eps_orth {i j : ZMod n} (h : i ≠ j) : eps E ρ i * eps E ρ j = 0 := by
  rw [eps, eps, ← map_mul, ← map_mul, letE_mul_ne h, map_zero, map_zero]

theorem eps_sum [NeZero n] : ∑ i, eps E ρ i = 1 := by
  simp only [eps, ← map_sum, sum_letE, map_one]

theorem eps_ext [NeZero n] {x y : Rk} (h : ∀ i, eps E ρ i * x = eps E ρ i * y) : x = y := by
  rw [← one_mul x, ← one_mul y, ← eps_sum E ρ, Finset.sum_mul, Finset.sum_mul]
  exact Finset.sum_congr rfl fun i _ => h i

theorem exists_isRed [NeZero n] (lam : O) (h1 : Function.Surjective (algebraMap O k))
    (h2 : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (h3 : algebraMap O LL lam ≠ 0) (hp : ((PD.p : ℕ) : k) = 0)
    (h4 : ∀ i, eps E ρ i ≠ 0) : ∃ κ : k⸨X⸩ →+* Rk, IsRed E ρ (k := k) lam κ := by
  obtain ⟨p, p1, p2, p3⟩ := GlobalTheory.T.exists_wachModule_generator_reduction W lam h1 h2 hp
  obtain ⟨κ, hκ⟩ := GlobalTheory.T.exists_ringHom_of_idempotent_surjective_family (ZMod n) W.EE k⸨X⸩ Rk (fun i => algebraMap (LetA O n) W.EE (letE i))
    (fun i => by rw [← map_mul, letE_mul_self]) (fun i j h => by rw [← map_mul, letE_mul_ne h, map_zero])
    (by rw [← map_sum, sum_letE, map_one]) p (rE E ρ) p2 (fun i x hx => by
      obtain ⟨e', he'⟩ := p3 i x hx
      rw [← map_mul, he', map_mul, rE_O (k := k), (h2 lam).2 dvd_rfl, map_zero, zero_mul])
  refine ⟨κ, h1, h2, h3, h4, fun i c => ?_, fun i e => ⟨p i e, (hκ i e).symm⟩, fun i e he => ?_, fun i c => ?_⟩
  · obtain ⟨e, rfl⟩ := p2 i c
    exact ⟨e, hκ i e⟩
  · refine p3 i e ?_
    by_contra hne
    have hu : IsUnit (κ (p i e)) := (IsUnit.mk0 _ hne).map κ
    exact h4 i (hu.mul_left_eq_zero.1 ((hκ i e).trans he))
  · rw [← p1]; exact (hκ i _).symm

variable {E ρ}

theorem IsRed.κ_const [NeZero n] {lam : O} {κ : k⸨X⸩ →+* Rk} (h : IsRed E ρ (k := k) lam κ) (b : O⟦X⟧) :
    κ ((PowerSeries.map (algebraMap O k) b : k⟦X⟧) : k⸨X⸩) =
      rE E ρ (algebraMap (LetA O n) W.EE (fun _ => b)) :=
  eps_ext E ρ fun i => (h.κ_A i (fun _ => b)).symm

theorem IsRed.κ_k [NeZero n] {lam : O} {κ : k⸨X⸩ →+* Rk} (h : IsRed E ρ (k := k) lam κ) (c : k) :
    κ (algebraMap k k⸨X⸩ c) = algebraMap k Rk c := by
  obtain ⟨o, rfl⟩ := h.res_surj c
  have := h.κ_const (PowerSeries.C o)
  rw [PowerSeries.map_C] at this
  rw [← rE_O E ρ, IsScalarTower.algebraMap_apply O (LetA O n) W.EE]
  exact this

theorem φ_rE (hO : Function.Injective (algebraMap O LL)) {φ : Rk →ₐ[k] Rk} (hφ : ∀ w, φ (ρ w) = ρ (φR w))
    (c : LetA O n) : φ (rE E ρ (algebraMap (LetA O n) W.EE c)) =
      rE E ρ (algebraMap (LetA O n) W.EE (letφ W.φ₀ c)) := by
  rw [rE_apply, hφ, ← GlobalTheory.TorsionBoundCompare.ioE_φ E hO, W.φE_ext, rE_apply]

theorem a_rE (hO : Function.Injective (algebraMap O LL)) {a : G → (Rk →ₐ[k] Rk)}
    (ha : ∀ g w, a g (ρ w) = ρ (gR g w)) (g : G) (c : LetA O n) :
    a g (rE E ρ (algebraMap (LetA O n) W.EE c)) =
      rE E ρ (algebraMap (LetA O n) W.EE (letγ (W.γ₀ (W.resΓ g)) c)) := by
  rw [rE_apply, ha, ← GlobalTheory.TorsionBoundCompare.ioE_γ E hO, W.γE_ext, rE_apply]

theorem a_eps (hO : Function.Injective (algebraMap O LL)) {a : G → (Rk →ₐ[k] Rk)}
    (ha : ∀ g w, a g (ρ w) = ρ (gR g w)) (g : G) (i : ZMod n) : a g (eps E ρ i) = eps E ρ i := by
  rw [eps, a_rE hO ha, letγ_letE]

theorem IsRed.a_κ [NeZero n] {lam : O} {κ : k⸨X⸩ →+* Rk} (h : IsRed E ρ (k := k) lam κ)
    (hO : Function.Injective (algebraMap O LL)) {a : G → (Rk →ₐ[k] Rk)}
    (ha : ∀ g w, a g (ρ w) = ρ (gR g w)) (g : G) (b : O⟦X⟧) :
    a g (κ ((PowerSeries.map (algebraMap O k) b : k⟦X⟧) : k⸨X⸩)) =
      κ ((PowerSeries.map (algebraMap O k) (W.γ₀ (W.resΓ g) b) : k⟦X⟧) : k⸨X⸩) := by
  rw [h.κ_const, h.κ_const, a_rE hO ha]; rfl

theorem IsRed.φ_κ [NeZero n] {lam : O} {κ : k⸨X⸩ →+* Rk} (h : IsRed E ρ (k := k) lam κ)
    (hO : Function.Injective (algebraMap O LL)) {φ : Rk →ₐ[k] Rk} (hφ : ∀ w, φ (ρ w) = ρ (φR w))
    (l : ℕ) [Fact l.Prime] [CharP k l] (hp : PD.p = l) (c : k⸨X⸩) :
    φ (κ c) = κ (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l c) := by
  refine laurent_ext (f := (φ : Rk →+* Rk).comp κ) (g := κ.comp (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l)) (fun b => ?_) c
  obtain ⟨b, rfl⟩ := PowerSeries.map_surjective _ h.res_surj b
  change φ (κ _) = κ (GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.phiPi k l _)
  rw [← GlobalTheory.T.reduction_cyclotomic_endo_eq_frobenius_laurent l O k W.φ₀ (by rw [W.φ₀_X, W.q₀_def, hp]), h.κ_const, h.κ_const, φ_rE hO hφ]; rfl

theorem IsRed.exists_isDel [NeZero n] {lam : O} {κ : k⸨X⸩ →+* Rk} (h : IsRed E ρ (k := k) lam κ)
    (hO : Function.Injective (algebraMap O LL)) {a : G → (Rk →ₐ[k] Rk)}
    (ha : ∀ g w, a g (ρ w) = ρ (gR g w)) (l : ℕ) [Fact l.Prime] [CharP k l] (R : RingPG k l)
    (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1})
    (he : ∀ δ b, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 b) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) b))
    (hc : ((W.DelF.card : ℕ) : k) ≠ 0) : ∃ σ, IsDel E ρ κ a (ι : k⸨X⸩ →+* k⸨X⸩) σ := by
  obtain ⟨σ, s1, s2, s3⟩ := GlobalTheory.T.teichmuller_roots_act_faithfully_laurent l k R ι hι
  refine ⟨fun δ => σ (e δ), ha, a_eps hO ha, fun g δ hg c => ?_, s2.comp e.injective, fun c => ?_, hc⟩
  · refine laurent_ext (f := (a g : Rk →+* Rk).comp κ) (g := κ.comp (σ (e δ))) (fun b => ?_) c
    obtain ⟨b, rfl⟩ := PowerSeries.map_surjective _ h.res_surj b
    change a g (κ _) = κ (σ (e δ) _)
    rw [h.a_κ hO ha, hg, he, s1]
  · refine Iff.trans ?_ (s3 c)
    exact ⟨fun h z => by simpa using h (e.symm z), fun h δ => h _⟩

theorem map_surj (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) {T T' : LocLat G Qp LL O}
    (f : LatHom T.L T'.L) (hf : ∀ x ∈ T'.L.T, ∃ z ∈ T.L.T, f.f z = x) : Function.Surjective (W.map f) := by
  have hπ : Function.Surjective (EtaleExact.latMap f) := fun y => by
    obtain ⟨x, hx, hxy⟩ := hf y y.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hπR : Function.Surjective ((EtaleExact.latMap f).baseChange RW) :=
    LinearMap.lTensor_surjective RW hπ
  rw [← LinearMap.range_eq_top]
  refine EtaleExact.eq_top_DD E hm T' _ ?_
  rw [EtaleExact.span_range_map, LinearMap.range_eq_top.2 hπR]

theorem IsRed.push [IsDomain O] [IsPrincipalIdealRing O] {lam : O} {κ : k⸨X⸩ →+* Rk}
    (h : IsRed E ρ (k := k) lam κ) (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (hc : ((W.DelF.card : ℕ) : k) ≠ 0) {T T' : LocLat G Qp LL O} {A A' : Ob k G}
    {q : ↥T.L.T →ₗ[O] (Fin A.m → k)} {q' : ↥T'.L.T →ₗ[O] (Fin A'.m → k)}
    {g : (Fin A.m → k) →ₗ[k] (Fin A'.m → k)} (hq : Onto T A q) (hq' : Onto T' A' q') (hg : IsHom A A' g)
    (x : ↥(DΔ W T)) : ∃ x' : ↥(DΔ W T'), J E ρ T' q' x' = g.baseChange Rk (J E ρ T q x) := by
  obtain ⟨T'', f, f', h1, h2⟩ := (GlobalTheory.T.kernel_inverse_fibreProduct_lattices lam h.lam_ne ((h.res_ker lam).2 dvd_rfl)).2.2 T A q T' A' q' g hq hq' hg
  obtain ⟨z, hz⟩ := map_surj hm f h1 x
  obtain ⟨u, hu⟩ := h.res_surj ((W.DelF.card : ℕ) : k)⁻¹
  set z' := ∑ δ ∈ W.DelF, W.γD T'' δ z with hz'
  have hzΔ : z' ∈ DΔ W T'' := sum_mem_DΔ T'' z
  have h3 : W.map f z' = W.DelF.card • (x : W.DD T) := by
    rw [hz', map_sum, ← Finset.sum_const]
    exact Finset.sum_congr rfl fun δ hδ => (W.map_γ f δ z).trans (by rw [hz]; exact x.2 δ hδ)
  refine ⟨⟨u • W.map f' z', fun δ hδ => by rw [map_smul, ← W.map_γ, hzΔ δ hδ]⟩, ?_⟩
  have h4 : J E ρ T' q' (W.map f' z') = g.baseChange Rk (J E ρ T q (W.map f z')) := by
    rw [J_map E ρ f (q ∘ₗ EtaleExact.latMap f) q LinearMap.id
        (fun y y' e => congrArg q (Subtype.ext e)),
      J_map E ρ f' (q ∘ₗ EtaleExact.latMap f) q' g
        (fun y y' e => (congrArg q' (Subtype.ext e)).trans (h2 y)), LinearMap.baseChange_id]
    rfl
  change J E ρ T' q' (u • W.map f' z') = _
  rw [J_smulO, h4, h3, map_nsmul, map_nsmul, hu, algebraMap_smul, ← Nat.cast_smul_eq_nsmul k, inv_smul_smul₀ hc]

theorem exists_frames [IsDomain O] [IsPrincipalIdealRing O] {lam : O} {κ : k⸨X⸩ →+* Rk}
    {a : G → (Rk →ₐ[k] Rk)} {ι : k⸨X⸩ →+* k⸨X⸩} {σ : {δ // δ ∈ W.DelF} → (k⸨X⸩ →+* k⸨X⸩)}
    (h : IsRed E ρ (k := k) lam κ) (hd : IsDel E ρ κ a ι σ)
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤) (A : Ob k G) (i : ZMod n) :
    ∃ β : Vc k A.m →+ Rk ⊗[k] (Fin A.m → k), ∀ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)),
      Onto T A q → IsFrame (κ.comp ι) (eps E ρ i) β ∧
        ∀ y, (∃ x, β x = y) ↔ ∃ x : ↥(DΔ W T), y = eps E ρ i • J E ρ T q x := by
  by_cases hA : ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q
  · obtain ⟨T₀, q₀, h₀⟩ := hA
    obtain ⟨T', f, hf⟩ := (GlobalTheory.T.kernel_inverse_fibreProduct_lattices lam h.lam_ne ((h.res_ker lam).2 dvd_rfl)).1 T₀ A q₀ h₀
    obtain ⟨β, h1, h2⟩ := GlobalTheory.T.exists_frame_of_torsion_invariants W E ρ lam κ a ι σ h hd T₀ A q₀ h₀ i
      (GlobalTheory.T.finrank_and_kernel_of_letter_image_tensor W E ρ lam κ h T₀ A.m q₀ h₀.1 T' f hf i).1
    refine ⟨β, fun T q hq => ⟨h1, fun y => (h2 y).trans ⟨?_, ?_⟩⟩⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := h.push hm hd.card_ne h₀ hq (g := LinearMap.id) (fun _ _ => rfl) x
      exact ⟨x', by rw [hx', LinearMap.baseChange_id]; rfl⟩
    · rintro ⟨x, rfl⟩
      obtain ⟨x', hx'⟩ := h.push hm hd.card_ne hq h₀ (g := LinearMap.id) (fun _ _ => rfl) x
      exact ⟨x', by rw [hx', LinearMap.baseChange_id]; rfl⟩
  · exact ⟨0, fun T q hq => absurd ⟨T, q, hq⟩ hA⟩

theorem exists_unit (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : ↥(DΔ W W.one)) (e₀ : ↥W.one.L.T), Submodule.span O {e₀} = ⊤ ∧ e₀ ≠ 0 ∧
      E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧ W.N W.one = Submodule.span (LetA O n) {(e : W.DD W.one)} ∧
      ∀ c c' : LetA O n, c • (e : W.DD W.one) = c' • (e : W.DD W.one) → c = c' := by
  obtain ⟨e, e₀, h1, h2, h3⟩ := E.one_e
  obtain ⟨e', e₀', -, h4⟩ := GlobalTheory.TorsionBoundCompare.unit_cancel E hO
  obtain ⟨o, ho⟩ := Submodule.mem_span_singleton.1 (show e₀' ∈ Submodule.span O {e₀} by rw [h1]; trivial)
  refine ⟨⟨e, fun δ _ => ?_⟩, e₀, h1, ?_, h2, h3, fun c c' hc => ?_⟩
  · obtain ⟨g, rfl⟩ := W.resΓ_onto δ
    have h5 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
    apply E.jD_inj
    rw [E.jD_act, h2]
    simp [TWact, h5]
  · rintro rfl
    obtain ⟨x, hx, hT⟩ := W.one_line
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {(0 : ↥W.one.L.T)} := by rw [h1]; trivial
    rw [Submodule.span_zero_singleton, Submodule.mem_bot] at hm
    exact hx (congrArg Subtype.val hm)
  · apply W.EE_inj
    apply EtaleExact.ioE_injective E
    apply h4
    have h6 := congrArg (E.jD W.one) hc
    change E.jD W.one (c • e) = E.jD W.one (c' • e) at h6
    rw [← algebraMap_smul W.EE c, ← algebraMap_smul W.EE c', E.jD_smul, E.jD_smul, h2] at h6
    rw [← ho, tmul_smul, smul_comm _ o, smul_comm _ o, h6]

set_option maxHeartbeats 1000000 in
theorem exists_pres [IsDomain O] [IsPrincipalIdealRing O] [NeZero n] (hO : Function.Injective (algebraMap O LL))
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (l : ℕ) [Fact l.Prime] [CharP k l] (hp : PD.p = l) {lam : O} {κ : k⸨X⸩ →+* Rk}
    (h : IsRed E ρ (k := k) lam κ) {φ : Rk →ₐ[k] Rk} (hφ : ∀ w, φ (ρ w) = ρ (φR w))
    {a : G → (Rk →ₐ[k] Rk)} (ha : ∀ g w, a g (ρ w) = ρ (gR g w))
    (amul : ∀ g h x, a (g * h) x = a g (a h x)) (aone : ∀ x, a 1 x = x)
    (hcomm : ∀ g x, φ (a g x) = a g (φ x)) (hfix : ∀ x, φ x = x → ∃ c : k, x = algebraMap k Rk c)
    (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hv : ι (vv k) = ((PowerSeries.map (algebraMap O k) W.π₀₁ : k⟦X⟧) : k⸨X⸩))
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1})
    (he : ∀ δ b, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 b) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) b))
    (hc : ((W.DelF.card : ℕ) : k) ≠ 0) (γ : W.Gam)
    (hγ : ∀ b, PowerSeries.map (algebraMap O k) (W.γ₀ γ b) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap O k) b))
    (hden : ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q →
      ∀ t : Fin A.m → k, (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t)
    {n' : ℕ} [NeZero n'] (τ : ZMod n' → ZMod n) (hτ : Function.Bijective τ) (hτ1 : ∀ i, τ (i - 1) = τ i - 1) :
    ∃ F : DFun R n' G, Nonempty (Pres W F ι τ γ) := by
  obtain ⟨σ, hd⟩ := h.exists_isDel hO ha l R ι hι e he hc
  have hlam : algebraMap O k lam = 0 := (h.res_ker lam).2 dvd_rfl
  obtain ⟨g₀, hg₀⟩ := W.resΓ_onto γ
  choose β₀ hβ₀ using exists_frames h hd hm
  haveI : Nontrivial Rk := nontrivial_of_ne _ _ (h.eps_ne 0)
  obtain ⟨c1, c2, c3, c4⟩ := GlobalTheory.T.latticeQuotients_closed_sub_quot_sum (G := G) (Qp := Qp) lam h.lam_ne hlam h.res_surj
    (fun x => (h.res_ker x).1)
  obtain ⟨u, u₀, u1, u2, u3, u4, u5⟩ := exists_unit (E := E) hO
  have hJu : ∀ q : ↥W.one.L.T →ₗ[O] (Fin 1 → k), J E ρ W.one q u = (1 : Rk) ⊗ₜ[k] q u₀ := fun q => by
    rw [J_apply, u3, redT_tmul, map_one]
  have hεφ : ∀ i, φ (eps E ρ (τ (i - 1))) = eps E ρ (τ i) := fun i => by
    rw [hτ1, eps, φ_rE hO hφ, letφ_letE]; rfl
  have hsum : ∑ i, eps E ρ (τ i) = 1 := by
    rw [← eps_sum E ρ]; exact hτ.sum_comp _
  have hact : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → ∀ g i (x : W.DD T),
      Act a A g (eps E ρ i • J E ρ T q x) = eps E ρ i • J E ρ T q (W.γD T (W.resΓ g) x) := by
    intro T A q hq g i x
    rw [Act_smul, hd.a_eps, J_act E ρ ha T A q hq]
  have hΔγ : ∀ (T : LocLat G Qp LL O) (g : W.Gam) (x : ↥(DΔ W T)), W.γD T g x ∈ DΔ W T := by
    intro T g x δ hδ
    rw [← W.γD_mul, mul_comm, W.γD_mul, x.2 δ hδ]
  have hfr : IsFrames R (κ.comp (ι : k⸨X⸩ →+* k⸨X⸩)) φ a g₀ (fun i => eps E ρ (τ i))
      (fun A => ∃ (T : LocLat G Qp LL O) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q)
      (fun A i => β₀ A (τ i)) :=
    { κ_k := fun c => by
        change κ (ι _) = _
        rw [AlgHom.commutes, h.κ_k]
      κ_φ := fun c => by
        change φ (κ (ι c)) = κ (ι _)
        rw [hι.2.2.2.1, h.φ_κ hO hφ l hp]
      κ_γ := fun c => by
        refine laurent_ext (f := (a g₀ : Rk →+* Rk).comp (κ.comp (ι : k⸨X⸩ →+* k⸨X⸩)))
          (g := (κ.comp (ι : k⸨X⸩ →+* k⸨X⸩)).comp (R.γ : k⸨X⸩ →+* k⸨X⸩)) (fun b => ?_) c
        obtain ⟨b', hb'⟩ := hι.2.1 b
        obtain ⟨b'', rfl⟩ := PowerSeries.map_surjective _ h.res_surj b'
        change a g₀ (κ (ι _)) = κ (ι (R.γ _))
        rw [hι.2.2.2.2 b _ hb', hb', h.a_κ hO ha, hg₀, hγ]
      comm := hcomm g₀
      ε_idem := fun i => eps_idem E ρ _
      ε_orth := fun i j hij => eps_orth E ρ fun e => hij (hτ.1 e)
      ε_sum := hsum
      ε_ne := fun i => h.eps_ne _
      ε_φ := hεφ
      ε_γ := fun i => hd.a_eps _ _
      obj_sub := c1
      obj_quot := c2
      obj_sum := c3
      obj_one := by
        obtain ⟨q, hq, -⟩ := c4 W.one u₀ W.one_triv u2 u1
        exact ⟨_, q, hq⟩
      frame := by
        rintro A ⟨T, q, hq⟩ i
        exact (hβ₀ A _ T q hq).1
      st_φ := by
        rintro A ⟨T, q, hq⟩ i x
        obtain ⟨x', hx'⟩ := ((hβ₀ A (τ (i - 1)) T q hq).2 _).1 ⟨x, rfl⟩
        refine ((hβ₀ A (τ i) T q hq).2 _).2 ⟨⟨W.φD T x', fun δ hδ => by rw [← W.φγ_comm, x'.2 δ hδ]⟩, ?_⟩
        rw [hx', Phi_smul, hεφ, ← J_φ E ρ hφ]
      st_γ := by
        rintro A ⟨T, q, hq⟩ i x
        obtain ⟨x', hx'⟩ := ((hβ₀ A (τ i) T q hq).2 _).1 ⟨x, rfl⟩
        refine ((hβ₀ A (τ i) T q hq).2 _).2 ⟨⟨_, hΔγ T (W.resΓ g₀) x'⟩, ?_⟩
        rw [hx', hact T A q hq]
      γ_inj := fun A => Function.LeftInverse.injective (g := Act a A g₀⁻¹) fun y => by
        rw [← Act_mul a amul, inv_mul_cancel, Act_one a aone]
      γ_surj := by
        rintro A ⟨T, q, hq⟩ i y
        obtain ⟨y', hy'⟩ := ((hβ₀ A (τ i) T q hq).2 _).1 ⟨y, rfl⟩
        obtain ⟨x, hx⟩ := ((hβ₀ A (τ i) T q hq).2 _).2 ⟨⟨_, hΔγ T (W.resΓ g₀⁻¹) y'⟩, rfl⟩
        refine ⟨x, ?_⟩
        rw [hx, hy', hact T A q hq, ← W.γD_mul, ← map_mul, mul_inv_cancel, map_one, W.γD_one]
      st_map := by
        rintro A A' f ⟨T, q, hq⟩ ⟨T', q', hq'⟩ hf i x
        obtain ⟨x', hx'⟩ := ((hβ₀ A (τ i) T q hq).2 _).1 ⟨x, rfl⟩
        obtain ⟨y, hy⟩ := h.push hm hc hq hq' hf x'
        refine ((hβ₀ A' (τ i) T' q' hq').2 _).2 ⟨y, ?_⟩
        rw [hx', hy, map_smul]
      unit := fun i => by
        obtain ⟨q, hq, hq1⟩ := c4 W.one u₀ W.one_triv u2 u1
        refine ((hβ₀ (chr 1) (τ i) W.one q hq).2 _).2 ⟨u, ?_⟩
        rw [hJu, hq1, smul_tmul', smul_eq_mul, mul_one]
      fix := by
        rintro A ⟨T, q, hq⟩ y h1 h2 h3
        obtain ⟨t, rfl⟩ := fixed_tensor φ hfix y h1
        choose x hx using fun i => ((hβ₀ A (τ i) T q hq).2 _).1 (h3 i)
        have hy : (1 : Rk) ⊗ₜ[k] t = ∑ i, eps E ρ (τ i) • J E ρ T q (x i) := by
          simp only [← hx]
          rw [← Finset.sum_smul, hsum, one_smul]
        refine ⟨t, rfl, hden T A q hq t fun g hg => one_tmul_inj (Rk := Rk) ?_⟩
        have h4 : (1 : Rk) ⊗ₜ[k] A.ρ g t = Act a A g ((1 : Rk) ⊗ₜ[k] t) := by rw [Act_tmul, map_one]
        rw [h4]
        rcases hg with hg | hg
        · rw [hy, map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hact T A q hq, (x i).2 _ hg]
        · refine Eq.trans ?_ h2
          rw [hy, map_sum, map_sum]
          exact Finset.sum_congr rfl fun i _ => by rw [hact T A q hq, hact T A q hq, hg, hg₀] }
  obtain ⟨F, F1, F2, F3, F4, F5⟩ := GlobalTheory.T.exists_exact_functor_phiGamma_of_frames R _ φ a g₀ _ _ _ hfr
  have hj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)) (i : ZMod n'),
      ∃ j : ↥(DΔ W T) →+ Vc k A.m, Onto T A q →
        ∀ x, β₀ A (τ i) (j x) = eps E ρ (τ i) • J E ρ T q x := by
    intro T A q i
    by_cases hq : Onto T A q
    · choose j hj using fun x : ↥(DΔ W T) => ((hβ₀ A (τ i) T q hq).2 _).2 ⟨x, rfl⟩
      refine ⟨AddMonoidHom.mk' j fun x y => (hβ₀ A (τ i) T q hq).1.1 ?_, fun _ => hj⟩
      rw [map_add, hj, hj, hj, AddSubgroup.coe_add, map_add, smul_add]
    · exact ⟨0, fun h => absurd h hq⟩
  choose j hj using hj
  have hinj : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → ∀ i, Function.Injective (β₀ A i) := fun T A q hq i => (hβ₀ A i T q hq).1.1
  have hsm : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → ∀ i (c : k⟦X⟧) x, β₀ A i (c • x) = κ (ι (c : k⸨X⸩)) • β₀ A i x := by
    intro T A q hq i c x
    rw [← algebraMap_smul k⸨X⸩ c x]
    exact (hβ₀ A i T q hq).1.2.1 _ x
  have hjs : ∀ (T : LocLat G Qp LL O) (A : Ob k G) q, Onto T A q → ∀ i (b : LetA O n) (c : k⟦X⟧) (x y : ↥(DΔ W T)),
      ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (b (τ i)) : k⟦X⟧) : k⸨X⸩) →
      (y : W.DD T) = b • (x : W.DD T) → j T A q i y = c • j T A q i x := by
    intro T A q hq i b c x y h1 h2
    apply hinj T A q hq
    rw [hsm T A q hq, hj T A q i hq, hj T A q i hq, h2, J_smulA, smul_smul, h.κ_A, h1, smul_smul, mul_comm]
  refine ⟨F, ⟨{
    ι_v := hv
    obj := fun T A q hq => by rw [F1]; exact ⟨T, q, hq⟩
    j := j
    j_surj := fun T A q hq i y => ?_
    j_smul := hjs
    j_φ := fun T A q hq i x y hy => hinj T A q hq (τ i) ?_
    j_γ := fun T A q hq i x y hy => hinj T A q hq (τ i) ?_
    j_ker := fun T A q hq T' f hf hk i x => ?_
    j_map := fun T A q T' A' q' hq hq' f g hg hfg i x y hy => hinj T' A' q' hq' (τ i) ?_
    j_unit := fun q hq x hx i => ?_ }⟩⟩
  · obtain ⟨x, hx⟩ := ((hβ₀ A (τ i) T q hq).2 _).1 ⟨y, rfl⟩
    exact ⟨x, hinj T A q hq (τ i) (by rw [hj T A q i hq, hx])⟩
  · rw [F2 A ⟨T, q, hq⟩, hj T A q i hq, hj T A q _ hq, hy, Phi_smul, hεφ, J_φ E ρ hφ]
  · rw [F3 A ⟨T, q, hq⟩, hj T A q i hq, hj T A q _ hq, hy, hact T A q hq, hg₀]
  · have h0 : j T A q i x = 0 ↔ eps E ρ (τ i) • J E ρ T q x = 0 := by
      rw [← hj T A q i hq, map_eq_zero_iff _ (hinj T A q hq (τ i))]
    rw [h0]
    constructor
    · obtain ⟨s, hs⟩ := (GlobalTheory.T.kernel_inverse_fibreProduct_lattices (G := G) (Qp := Qp) lam h.lam_ne hlam).2.1 T T' f hf (fun z hz =>
        (hk (lam • ⟨z, hz⟩)).1 (by rw [map_smul, ← algebraMap_smul k lam, hlam, zero_smul]))
      exact (GlobalTheory.T.finrank_and_kernel_of_letter_image_tensor W E ρ lam κ h T A.m q hq.1 T' f hk (τ i)).2 s hs x
    · rintro ⟨y, hy⟩
      have h1 := J_map E ρ f (0 : ↥T'.L.T →ₗ[O] (Fin A.m → k)) q 0
        (fun z z' e => (hk z').2 ⟨z, z.2, e.symm⟩) y
      rw [hy, J_smulA, LinearMap.baseChange_zero] at h1
      exact h1
  · rw [F4 A A' g ⟨T, q, hq⟩ ⟨T', q', hq'⟩ hg, hj T A q i hq, hj T' A' q' i hq', hy, J_map E ρ f q q' g hfg,
      map_smul]
  · obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (show (x : W.DD W.one) ∈
      Submodule.span (LetA O n) {(u : W.DD W.one)} by rw [← u4, hx]; exact Submodule.mem_span_singleton_self _)
    obtain ⟨b', hb'⟩ := Submodule.mem_span_singleton.1 (show (u : W.DD W.one) ∈
      Submodule.span (LetA O n) {(x : W.DD W.one)} by rw [← hx, u4]; exact Submodule.mem_span_singleton_self _)
    have hbb : b' * b = 1 := u5 _ _ (by rw [mul_smul, hb, hb', one_smul])
    have hbi : ∀ δ ∈ W.DelF, letγ (W.γ₀ δ) b = b := fun δ hδ => u5 _ _ (by
      have h1 := x.2 δ hδ
      rw [← hb, ← algebraMap_smul W.EE b, W.γD_smul, W.γE_ext, u.2 δ hδ, algebraMap_smul, algebraMap_smul] at h1
      exact h1)
    have hbi' : ∀ δ ∈ W.DelF, letγ (W.γ₀ δ) b' = b' := fun δ hδ => by
      have h1 := congrArg (letγ (n := n) (W.γ₀ δ)) hbb
      rw [map_mul, map_one, hbi δ hδ] at h1
      linear_combination b' * h1 - letγ (W.γ₀ δ) b' * hbb
    have hdesc : ∀ d : LetA O n, (∀ δ ∈ W.DelF, letγ (W.γ₀ δ) d = d) → ∃ c : k⟦X⟧,
        ι (c : k⸨X⸩) = ((PowerSeries.map (algebraMap O k) (d (τ i)) : k⟦X⟧) : k⸨X⸩) := fun d hd' =>
      (hι.2.2.1 _).1 fun z hz => by
        have h1 := he (e.symm ⟨z, hz⟩) (d (τ i))
        rw [Equiv.apply_symm_apply] at h1
        rw [← h1]
        exact congrArg _ (congrFun (hd' _ (e.symm ⟨z, hz⟩).2) (τ i))
    obtain ⟨c, hc1⟩ := hdesc b hbi
    obtain ⟨c', hc1'⟩ := hdesc b' hbi'
    have h1 := hjs _ _ q hq i b c u x hc1 hb.symm
    have h2 := hjs _ _ q hq i b' c' x u hc1' hb'.symm
    obtain ⟨w, hw⟩ := hq.1 (fun _ => 1)
    obtain ⟨o, rfl⟩ := Submodule.mem_span_singleton.1 (show w ∈ Submodule.span O {u₀} by rw [u1]; trivial)
    have hκC : ∀ s : k, κ (ι ((PowerSeries.C s : k⟦X⟧) : k⸨X⸩)) = algebraMap k Rk s := fun s => hfr.κ_k s
    have h3 : F.unit i = (PowerSeries.C (algebraMap O k o) : k⟦X⟧) • j W.one (chr 1) q i u := by
      apply hinj _ _ q hq (τ i)
      rw [F5, hsm _ _ q hq, hj _ _ q i hq, hJu, hκC, ← hw, map_smul, ← algebraMap_smul k o, algebraMap_smul Rk,
        smul_tmul', smul_eq_mul, mul_one, tmul_smul]
    have h4 : j W.one (chr 1) q i u = (PowerSeries.C (q u₀ 0) : k⟦X⟧) • F.unit i := by
      apply hinj _ _ q hq (τ i)
      rw [hsm _ _ q hq, F5, hj _ _ q i hq, hJu, hκC, algebraMap_smul Rk,
        smul_tmul', smul_eq_mul, mul_one, ← tmul_smul]
      congr 1
      funext s
      rw [Subsingleton.elim s 0]; simp
    apply le_antisymm
    · rw [Submodule.span_singleton_le_iff_mem, h1, h4, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
    · rw [Submodule.span_singleton_le_iff_mem, h3, h2, smul_smul]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)

omit [Algebra k Rk] [Algebra O Rk] [IsScalarTower O k Rk] in

theorem exists_pres_tensor (E : EtTie W RA RW inclR φR gR πA) [IsDomain O] [IsPrincipalIdealRing O]
    (hO : Function.Injective (algebraMap O LL))
    (hm : ∀ m : Ideal W.EE, m.IsMaximal → m.map E.ioE.toRingHom ≠ ⊤)
    (l : ℕ) [Fact l.Prime] [CharP k l] (hp : PD.p = l) (lam : O) (h1 : Function.Surjective (algebraMap O k))
    (h2 : ∀ x, algebraMap O k x = 0 ↔ lam ∣ x) (h3 : lam ≠ 0)
    (hidem : ∀ x : RW, IsIdempotentElem x → ((1 : k) ⊗ₜ[O] x : k ⊗[O] RW) = 0 → x = 0)
    (amul : ∀ g h x, gR (g * h) x = gR g (gR h x)) (aone : gR 1 = AlgHom.id O RW)
    (hcomm : ∀ g x, φR (gR g x) = gR g (φR x))
    (hfix : ∀ x : k ⊗[O] RW, Algebra.TensorProduct.map (AlgHom.id k k) φR x = x →
      ∃ c : k, x = algebraMap k (k ⊗[O] RW) c)
    (R : RingPG k l) (ι : k⸨X⸩ →ₐ[k] k⸨X⸩) (hι : GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.IsCyclotomic R ι)
    (hv : ι (vv k) = ((1 + ∑ᶠ z : {z : ℤ_[l] // z ^ (l - 1) = 1},
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.onePlusPow k l z.1 : k⟦X⟧) : k⸨X⸩))
    (e : {δ // δ ∈ W.DelF} ≃ {z : ℤ_[l] // z ^ (l - 1) = 1})
    (he : ∀ δ b, PowerSeries.map (algebraMap O k) (W.γ₀ δ.1 b) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.deltaPi k l (e δ).1 (PowerSeries.map (algebraMap O k) b))
    (hc : ((W.DelF.card : ℕ) : k) ≠ 0) (γ : W.Gam)
    (hγ : ∀ b, PowerSeries.map (algebraMap O k) (W.γ₀ γ b) =
      GlobalTheory.IndefiniteRowSideFullHecke.OnePlusPowerCharacters.gammaPi k l (PowerSeries.map (algebraMap O k) b))
    (hden : ∀ (T : LocLat G Qp LL O) (A : Ob k G) (q : ↥T.L.T →ₗ[O] (Fin A.m → k)), Onto T A q →
      ∀ t : Fin A.m → k, (∀ g, (W.resΓ g ∈ W.DelF ∨ W.resΓ g = γ) → A.ρ g t = t) → ∀ g, A.ρ g t = t)
    {n' : ℕ} [NeZero n'] (τ : ZMod n' → ZMod n) (hτ : Function.Bijective τ) (hτ1 : ∀ i, τ (i - 1) = τ i - 1) :
    ∃ F : DFun R n' G, Nonempty (Pres W F ι τ γ) := by
  haveI := PD.finK₀
  haveI : NeZero n := ⟨by rw [W.n_eq]; exact Module.finrank_pos.ne'⟩
  let ρ : RW →ₐ[O] k ⊗[O] RW := Algebra.TensorProduct.includeRight
  obtain ⟨κ, hκ⟩ := exists_isRed E ρ (k := k) lam h1 h2
    (fun h => h3 (hO (h.trans (map_zero _).symm)))
    (by rw [hp]; exact CharP.cast_eq_zero k l) (fun i h => by
      have h4 := hidem _ (eps_idem E (AlgHom.id _ _) i) h
      have h5 := W.EE_inj (EtaleExact.ioE_injective E
        (h4.trans ((map_zero E.ioE).symm.trans (congrArg _ (map_zero (algebraMap _ _)).symm))))
      simpa [letE] using congrFun h5 i)
  exact exists_pres (E := E) (ρ := ρ) hO hm l hp hκ
    (φ := Algebra.TensorProduct.map (AlgHom.id k k) φR) (fun _ => rfl)
    (a := fun g => Algebra.TensorProduct.map (AlgHom.id k k) (gR g)) (fun _ _ => rfl)
    (fun g h x => HerrClass.map_id_comp _ _ _ (amul g h) x)
    (fun x => by rw [aone, Algebra.TensorProduct.map_id]; rfl)
    (fun g x => HerrClass.map_id_comm _ _ _ _ (hcomm g) x)
    hfix R ι hι (by rw [hv, GlobalTheory.T.reduction_map_pi0 W l hp e he]) e he hc γ hγ hden τ hτ hτ1

end Comparison₂

open GlobalTheory.TopSteps Formalism.BasicNotions.Loc

theorem gRW_one {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (LL : FinExt l) :
    AI.gRW LL 1 = AlgHom.id _ _ := by
  rw [LocAinf.gRW, map_one]
  exact Algebra.TensorProduct.map_id

theorem realD : ∀ {l : ℕ} [Fact l.Prime] {P : LocPrime l} (AI : LocAinf l P) (H : LocHW l P) (E : LocFon l P AI H) (S : TopSit P), S.RealD H := by
  intro l _ P AI H E S k _ _ _ hk
  obtain ⟨R, ι, hι, hv⟩ := GlobalTheory.CycRing.exists_cyclotomic l k S.hyp.1.1
  obtain ⟨⟨γ, hγ1, hγ2⟩, e, he⟩ := GlobalTheory.RedAct.gamma_action_reduction H S k
  obtain ⟨τ, t1, t2, t3⟩ := GlobalTheory.T.exists_letter_bijection' H S
  obtain ⟨hc, hden⟩ := GlobalTheory.T.fixed_of_fixed_by_delta_gamma_lifts AI H S k hk
  have hp : (P.PD S.K).p = l := P.PD_p S.K
  obtain ⟨_, -⟩ := GlobalTheory.FinExtIntegers.dvr_complete S.LL
  have hm := EtaleExact.map_ne_top_of_tie (E.E S.K 1 S.LL S.hyp.1.2.1.2.2).tie
    (by rw [hp]; exact EtaleExact.isUnit_or_dvd_pow P S.LL) (by rw [hp]; exact EtaleExact.sep_RW S.LL)
  obtain ⟨F, hF⟩ := exists_pres_tensor (E.E S.K 1 S.LL S.hyp.1.2.1.2.2).tie Subtype.val_injective hm l hp
    S.Γ.lam hk.1 hk.2 S.hyp.1.2.2.2.2.2.ne_zero (GlobalTheory.T.idempotent_witt_tilt_eq_zero_of_residue_zero P S.LL k S.Γ.lam hk.1 hk.2)
    (fun g h => HerrClass.gRW_mul AI S.LL g h) (gRW_one AI S.LL) (fun g => HerrClass.phi_gRW AI S.LL g)
    (GlobalTheory.T.frobenius_fixed_tensor_eq_constant S.LL k) R ι hι hv e he hc γ hγ2 (hden γ hγ1) τ t1 t3
  exact ⟨R, ι, hι, F, τ, γ, t2, hγ1, hF⟩

end GlobalTheory.RedFun
