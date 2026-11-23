import Formalism.LocalToGlobal.Columns.CoefModX
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds

open MvPolynomial NumberField IsDedekindDomain
open scoped Matrix

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions

section Fields

variable {K K' : Type} [Field K] [Field K'] (j : K →+* K')

theorem bc_map_smul {σ : Type} (c : K) (P : MvPolynomial σ K) :
    MvPolynomial.map j (c • P) = j c • MvPolynomial.map j P := by
  rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem bc_map_ten (f : ι → MvPolynomial (Fin n × Fin n) K) :
    MvPolynomial.map j (ten f) = ten fun τ => MvPolynomial.map j (f τ) := by
  unfold ten
  rw [map_prod]
  exact Finset.prod_congr rfl fun τ _ => fk_map_blockEmb j τ (f τ)

theorem bc_map_blockAct (g : ι → Matrix (Fin n) (Fin n) K) (P : Pol K ι n) :
    MvPolynomial.map j (Formalism.GradedWeylDivisibility.blockAct K g P) =
      Formalism.GradedWeylDivisibility.blockAct K' (fun τ => (g τ).map j) (MvPolynomial.map j P) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [Formalism.GradedWeylDivisibility.blockAct]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p x hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp [Formalism.GradedWeylDivisibility.blockAct]

theorem bc_VV_eq (K : Type) [Field K] (lam : ι → DomWeight n) :
    VV K lam = Submodule.span K (nbGen fun τ => bideterminantsOfShape K (lam τ).natW) := by
  have h : (fun τ => nablaSq K n (lam τ)) = fun τ => Submodule.span K (bideterminantsOfShape K (lam τ).natW) := by
    funext τ
    unfold nablaSq
    rw [Formalism.GradedWeylDivisibility.standardMonomialSpanDomain K n n (lam τ).natW]
    rfl
  rw [VV, h, nb_tensorLat_span]

theorem bc_gen_bid (lam : ι → DomWeight n) :
    (nbGen fun τ => bideterminantsOfShape K' (lam τ).natW) =
      (fun F : Pol K ι n => MvPolynomial.map j F) '' (nbGen fun τ => bideterminantsOfShape K (lam τ).natW) := by
  ext P
  constructor
  · rintro ⟨f, hf, rfl⟩
    choose N sz hsz I h1 h2 using hf
    refine ⟨ten fun τ => Formalism.GradedWeylDivisibility.bideterminant K (sz τ) (hsz τ) (I τ), ⟨_, fun τ => ⟨N τ, sz τ, hsz τ, I τ, h1 τ, rfl⟩, rfl⟩, ?_⟩
    simp only
    rw [bc_map_ten]
    congr 1
    funext τ
    rw [fk_map_bidet, h2 τ]
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    choose N sz hsz I h1 h2 using hf
    refine ⟨fun τ => MvPolynomial.map j (f τ), fun τ => ⟨N τ, sz τ, hsz τ, I τ, h1 τ, ?_⟩, bc_map_ten j f⟩
    show MvPolynomial.map j (f τ) = _
    rw [h2 τ, fk_map_bidet]

theorem bc_gen_word (lam : ι → DomWeight n) :
    (nbGen fun τ => nbWord K' (lam τ).natW) =
      (fun F : Pol K ι n => MvPolynomial.map j F) '' (nbGen fun τ => nbWord K (lam τ).natW) := by
  ext P
  constructor
  · rintro ⟨f, hf, rfl⟩
    choose w hw using hf
    refine ⟨ten fun τ => Formalism.GradedWeylDivisibility.applyWord K (w τ) (Formalism.GradedWeylDivisibility.hw K le_rfl (lam τ).natW), ⟨_, fun τ => ⟨w τ, rfl⟩, rfl⟩, ?_⟩
    simp only
    rw [bc_map_ten]
    congr 1
    funext τ
    rw [← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map, ← hw τ]
  · rintro ⟨_, ⟨f, hf, rfl⟩, rfl⟩
    choose w hw using hf
    refine ⟨fun τ => MvPolynomial.map j (f τ), fun τ => ⟨w τ, ?_⟩, bc_map_ten j f⟩
    simp only
    rw [← hw τ, ← Formalism.GradedWeylDivisibility.lclosedeq_applyWord_map, Formalism.GradedWeylDivisibility.lclosedeq_hw_map]

theorem bc_map_mem_span {σ : Type} (S : Set (MvPolynomial σ K)) {F : MvPolynomial σ K} (hF : F ∈ Submodule.span K S) :
    MvPolynomial.map j F ∈ Submodule.span K' ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' S) := by
  induction hF using Submodule.span_induction with
  | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [bc_map_smul]; exact Submodule.smul_mem _ _ hx

theorem bc_descent_span {σ κ : Type} [Fintype κ] (v : κ → MvPolynomial σ K) (c : κ → K') (F : MvPolynomial σ K)
    (h : MvPolynomial.map j F = ∑ i, c i • MvPolynomial.map j (v i)) :
    ∃ d : κ → K, F = ∑ i, d i • v i := by
  let _ : Algebra K K' := j.toAlgebra
  obtain ⟨π, hπ⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K K')
    (LinearMap.ker_eq_bot.mpr (algebraMap K K').injective)
  have hπ' : ∀ a : K, π (j a) = a := fun a => congrArg (fun φ : K →ₗ[K] K => φ a) hπ
  have hmul : ∀ (a : K) (z : K'), π (z * j a) = π z * a := by
    intro a z
    have : z * j a = a • z := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, mul_comm]
  refine ⟨fun i => π (c i), ?_⟩
  ext m
  have h1 := congrArg (fun P => π (coeff m P)) h
  simp only [coeff_map, hπ', coeff_sum, coeff_smul, smul_eq_mul, map_sum, hmul] at h1
  rw [h1, coeff_sum]
  simp only [coeff_smul, smul_eq_mul]

theorem baseChangeSpace_holds : BaseChangeSpace := by
  intro K K' _ _ j ι _ n lam
  have h2 : Submodule.span K' ((fun F : Pol K ι n => MvPolynomial.map j F) '' (VV K lam : Set (Pol K ι n))) =
      VV K' lam := by
    apply le_antisymm
    · rw [Submodule.span_le]
      rintro _ ⟨F, hF, rfl⟩
      rw [SetLike.mem_coe, bc_VV_eq K lam] at hF
      have := bc_map_mem_span j _ hF
      rw [← bc_gen_bid] at this
      rw [SetLike.mem_coe, bc_VV_eq K' lam]
      exact this
    · rw [bc_VV_eq K' lam, bc_gen_bid j]
      refine Submodule.span_mono (Set.image_mono ?_)
      rw [bc_VV_eq K lam]
      exact Submodule.subset_span
  refine ⟨fun F => ⟨fun hF => ?_, fun hF => ?_⟩, h2⟩
  · rw [← h2]
    exact Submodule.subset_span ⟨F, hF, rfl⟩
  · have h3 : VV K' lam = Submodule.span K' (Set.range fun i => MvPolynomial.map j (bVVfun K lam i)) := by
      rw [← h2, ← (bVVfun_spec K lam).2]
      apply le_antisymm
      · rw [Submodule.span_le]
        rintro _ ⟨G, hG, rfl⟩
        have := bc_map_mem_span j _ hG
        rwa [← Set.range_comp] at this
      · refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨_, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    rw [h3] at hF
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K').1 hF
    obtain ⟨d, hd⟩ := bc_descent_span j (bVVfun K lam) c F hc.symm
    rw [hd, ← (bVVfun_spec K lam).2]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end Fields

section Act

theorem baseChangeAction_holds : BaseChangeAct := by
  intro K K' _ _ j ι _ n lam g F
  have h1 : j (detTwK lam g) = detTwK lam (fun τ => Formalism.UG.bc j (g τ)) := by
    unfold detTwK
    rw [map_prod]
    exact Finset.prod_congr rfl fun τ _ => nb_map_detPow j (g τ) _
  simp only [actP, LinearMap.smul_apply, AlgHom.toLinearMap_apply]
  rw [bc_map_smul, h1]
  unfold trAct
  rw [bc_map_blockAct]
  rfl

theorem bc_map_fockS {K K' : Type} [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K')
    (hj : ∀ x, j (star x) = star (j x)) {σ : Type} (f g : MvPolynomial σ K) :
    fockS (MvPolynomial.map j f) (MvPolynomial.map j g) = j (fockS f g) := by
  rw [fockS_eq_sum _ _ f.support (support_map_subset j f), fockS, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, map_mul, hj, coeff_map, coeff_map, map_natCast]

theorem bc_map_extNorm {K K' : Type} [Field K] [StarRing K] [Field K'] [StarRing K'] (j : K →+* K')
    (hj : ∀ x, j (star x) = star (j x)) {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) :
    j (extNorm K lam) = extNorm K' lam := by
  unfold extNorm
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [← bc_map_fockS j hj, map_extremal]

theorem bc_map_gramTw {K K' : Type} [Field K] [Field K'] (j : K →+* K') {ι : Type} [Fintype ι] {n : ℕ}
    (lam : ι → DomWeight n) (G : ι → Matrix (Fin n) (Fin n) K) :
    j (gramTw lam G) = gramTw lam fun τ => (G τ).map j := by
  unfold gramTw
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [map_zpow₀, RingHom.map_det, RingHom.mapMatrix_apply]

theorem baseChangePairing_holds : BaseChangePair := by
  intro K K' _ _ _ _ j hj ι _ n lam G F F'
  rw [pairP_apply, pairP_apply, fockL_apply, fockL_apply, map_mul, map_div₀, bc_map_gramTw, bc_map_extNorm j hj,
    ← bc_map_fockS j hj, bc_map_blockAct]
  rfl

theorem baseChangePairingV_holds : BaseChangePairV := by
  intro E K K' _ _ _ _ _ j hj ι _ n emb lam J x x' y y' hxy hxy'
  constructor
  · unfold pairV
    rw [pairK_apply, pairK_apply, ← baseChangePairing_holds K K' j hj, hxy, hxy']
    congr 3
  · unfold pairVr
    rw [pairK_apply, pairK_apply, ← baseChangePairing_holds K K' j hj, hxy, hxy']
    congr 3
    funext τ
    unfold gramKd
    rw [Matrix.transpose_map, Formalism.L2.Col.map_inv_matrix, Matrix.map_map]
    rfl

end Act

section Places

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')

abbrev bcO : 𝓞 K →+* 𝓞 K' := RingOfIntegers.mapRingHom j

theorem bc_coe_bcO (r : 𝓞 K) : algebraMap (𝓞 K') K' (bcO j r) = j (algebraMap (𝓞 K) K r) := rfl

theorem bc_bcO_injective : Function.Injective (bcO j) := by
  intro a b h
  have h1 := congrArg (algebraMap (𝓞 K') K') h
  rw [bc_coe_bcO, bc_coe_bcO] at h1
  exact FaithfulSMul.algebraMap_injective (𝓞 K) K (j.injective h1)

theorem bc_map_osmul {σ : Type} (r : 𝓞 K) (F : MvPolynomial σ K) :
    MvPolynomial.map j (r • F) = bcO j r • MvPolynomial.map j F := by
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, IsScalarTower.algebraMap_apply (𝓞 K) K (MvPolynomial σ K),
    IsScalarTower.algebraMap_apply (𝓞 K') K' (MvPolynomial σ K'), MvPolynomial.algebraMap_eq, MvPolynomial.algebraMap_eq,
    map_C]
  rfl

theorem bc_osmul_map_mem_iff {σ : Type} (N : Submodule (𝓞 K') (MvPolynomial σ K')) (r : 𝓞 K) (F : MvPolynomial σ K) :
    bcO j r • MvPolynomial.map j F ∈ N ↔ MvPolynomial.map j (r • F) ∈ N := by
  rw [bc_map_osmul]

theorem bc_map_osmul_mem {σ : Type} (N : Submodule (𝓞 K') (MvPolynomial σ K')) (r : 𝓞 K) {F : MvPolynomial σ K}
    (h : MvPolynomial.map j F ∈ N) : MvPolynomial.map j (r • F) ∈ N := by
  rw [bc_map_osmul]
  exact N.smul_mem _ h

def bcV {n : ℕ} (x : Fin n → K) : Fin n → K' := fun a => j (x a)

theorem bc_bcV_osmul {n : ℕ} (r : 𝓞 K) (x : Fin n → K) : bcV j (r • x) = bcO j r • bcV j x := by
  funext a
  simp only [bcV, Pi.smul_apply, Algebra.smul_def, map_mul]
  rfl

theorem bc_bcLat_eq {n : ℕ} (M : Submodule (𝓞 K) (Fin n → K)) :
    bcLat j M = Submodule.span (𝓞 K') (bcV j '' (M : Set (Fin n → K))) := rfl

theorem bc_bcV_mem {n : ℕ} {M : Submodule (𝓞 K) (Fin n → K)} {x : Fin n → K} (hx : x ∈ M) : bcV j x ∈ bcLat j M :=
  Submodule.subset_span ⟨x, hx, rfl⟩

theorem bc_map_mem {σ : Type} {T : Submodule (𝓞 K) (MvPolynomial σ K)} {F : MvPolynomial σ K} (hF : F ∈ T) :
    MvPolynomial.map j F ∈ bcPol j T := Submodule.subset_span ⟨F, hF, rfl⟩

theorem bc_bcLat_span {n : ℕ} (S : Set (Fin n → K)) :
    bcLat j (Submodule.span (𝓞 K) S) = Submodule.span (𝓞 K') (bcV j '' S) := by
  apply le_antisymm
  · rw [bc_bcLat_eq, Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero =>
      have : bcV j (0 : Fin n → K) = 0 := by funext a; simp [bcV]
      rw [this]; exact Submodule.zero_mem _
    | add x y _ _ hx hy =>
      have : bcV j (x + y) = bcV j x + bcV j y := by funext a; simp [bcV]
      rw [this]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => rw [bc_bcV_osmul]; exact Submodule.smul_mem _ _ hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem bc_bcPol_span {σ : Type} (S : Set (MvPolynomial σ K)) :
    bcPol j (Submodule.span (𝓞 K) S) =
      Submodule.span (𝓞 K') ((fun F : MvPolynomial σ K => MvPolynomial.map j F) '' S) := by
  apply le_antisymm
  · unfold bcPol
    rw [Submodule.span_le]
    rintro _ ⟨x, hx, rfl⟩
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span ⟨x, hx, rfl⟩
    | zero => simp only [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => simp only [map_add]; exact Submodule.add_mem _ hx hy
    | smul r x _ hx => exact bc_map_osmul_mem j _ r hx
  · exact Submodule.span_mono (Set.image_mono Submodule.subset_span)

theorem baseChangeTauLattice_holds : BaseChangeTauLat := by
  intro E K K' _ _ _ _ _ _ j ι n emb τ L
  unfold tauLat
  rw [bc_bcLat_span, ← Set.image_comp]
  rfl

theorem baseChangeStandard_holds : BaseChangeStd := by
  intro K K' _ _ _ _ j ι _ n lam
  constructor
  · rw [nb_nabStd_eq, nb_nabStd_eq, bc_bcPol_span, ← bc_gen_bid]
  · rw [nb_delStd_eq, nb_delStd_eq, bc_bcPol_span, ← bc_gen_word]

def bcBelow (w' : HeightOneSpectrum (𝓞 K')) : HeightOneSpectrum (𝓞 K) where
  asIdeal := w'.asIdeal.comap (bcO j)
  isPrime := Ideal.comap_isPrime _ _
  ne_bot := by
    intro h
    have h0 : Ideal.absNorm w'.asIdeal ≠ 0 := fun h0 => w'.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    have h1 : ((Ideal.absNorm w'.asIdeal : ℕ) : 𝓞 K) ∈ w'.asIdeal.comap (bcO j) := by
      rw [Ideal.mem_comap, map_natCast]
      exact Ideal.absNorm_mem _
    rw [h, Ideal.mem_bot] at h1
    exact h0 (by exact_mod_cast h1)

theorem bc_mem_below (w' : HeightOneSpectrum (𝓞 K')) (s : 𝓞 K) :
    s ∈ (bcBelow j w').asIdeal ↔ bcO j s ∈ w'.asIdeal := Iff.rfl

theorem bc_exists_above (w : HeightOneSpectrum (𝓞 K)) : ∃ w' : HeightOneSpectrum (𝓞 K'), bcBelow j w' = w := by
  let _ : Algebra (𝓞 K) (𝓞 K') := (bcO j).toAlgebra
  have hint : Algebra.IsIntegral (𝓞 K) (𝓞 K') := ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  obtain ⟨Q, -, hQ, hQw⟩ := Ideal.exists_ideal_over_prime_of_isIntegral w.asIdeal (⊥ : Ideal (𝓞 K')) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := bc_bcO_injective j (by rw [map_zero]; exact hx)
    rw [this]; exact Ideal.zero_mem _)
  refine ⟨⟨Q, hQ, ?_⟩, ?_⟩
  · rintro rfl
    apply w.ne_bot
    rw [← hQw, eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [Ideal.mem_bot]
    exact bc_bcO_injective j (by rw [map_zero]; exact hx)
  · apply HeightOneSpectrum.ext
    exact hQw

end Places

section LocBC

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')

theorem bc_notMem (w' : HeightOneSpectrum (𝓞 K')) {s : 𝓞 K} (hs : s ∉ (bcBelow j w').asIdeal) :
    bcO j s ∉ w'.asIdeal := hs

theorem bc_bcLat_le_locP {n : ℕ} (w' : HeightOneSpectrum (𝓞 K')) {A A' : Submodule (𝓞 K) (Fin n → K)}
    (h : A ≤ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal A') : bcLat j A ≤ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcLat j A') := by
  rw [bc_bcLat_eq, Submodule.span_le]
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨s, hs, hsx⟩ := (lc_mem_locP _ _ _).1 (h hx)
  refine (lc_mem_locP _ _ _).2 ⟨bcO j s, bc_notMem j w' hs, ?_⟩
  rw [← bc_bcV_osmul]
  exact bc_bcV_mem j hsx

theorem localized_baseChange_eq_of_localized_eq {n : ℕ} (w' : HeightOneSpectrum (𝓞 K')) {A A' : Submodule (𝓞 K) (Fin n → K)}
    (h : Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal A = Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal A') :
    Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcLat j A) = Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcLat j A') := by
  apply le_antisymm
  · rw [← localized_localized w' (bcLat j A')]
    exact localization_mono _ (bc_bcLat_le_locP j w' (h ▸ lc_le_locP _ A))
  · rw [← localized_localized w' (bcLat j A)]
    exact localization_mono _ (bc_bcLat_le_locP j w' (h ▸ lc_le_locP _ A'))

theorem bc_colLat {n : ℕ} (B : GL (Fin n) K) : bcLat j (colLat B) = colLat (Formalism.UG.bc j B) := by
  unfold colLat
  rw [bc_bcLat_span, ← Set.range_comp]
  rfl

theorem bc_isBasisAt {n : ℕ} (w' : HeightOneSpectrum (𝓞 K')) {M : Submodule (𝓞 K) (Fin n → K)} {B : GL (Fin n) K}
    (h : IsBasisAt (bcBelow j w') M B) : IsBasisAt w' (bcLat j M) (Formalism.UG.bc j B) := by
  unfold IsBasisAt
  rw [← bc_colLat]
  exact localized_baseChange_eq_of_localized_eq j w' h

theorem bc_map_mem_locP {σ : Type} (w' : HeightOneSpectrum (𝓞 K')) {T : Submodule (𝓞 K) (MvPolynomial σ K)}
    {F : MvPolynomial σ K} (h : F ∈ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal T) :
    MvPolynomial.map j F ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcPol j T) := by
  obtain ⟨s, hs, hsx⟩ := (lc_mem_locP _ _ _).1 h
  refine (lc_mem_locP _ _ _).2 ⟨bcO j s, bc_notMem j w' hs, ?_⟩
  exact (bc_osmul_map_mem_iff j _ s F).2 (bc_map_mem j hsx)

theorem bc_inv_bc {ι : Type} {n : ℕ} (B : ι → GL (Fin n) K) :
    (fun τ => Formalism.UG.bc j (B τ))⁻¹ = fun τ => Formalism.UG.bc j (B⁻¹ τ) := by
  funext τ
  rw [Pi.inv_apply, Pi.inv_apply, map_inv]

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem bc_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (T' : Submodule (𝓞 K') (Pol K' ι n))
    (hT : bcPol j T = T') (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ))
    (hind : ∀ (w' : HeightOneSpectrum (𝓞 K')) (B B' : ι → GL (Fin n) K'),
      (∀ τ, IsBasisAt w' (bcLat j (M τ)) (B τ)) → (∀ τ, IsBasisAt w' (bcLat j (M τ)) (B' τ)) → ∀ F : Pol K' ι n,
      (actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal T' ↔ actP lam B'⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal T'))
    (hloc : ∀ (w : HeightOneSpectrum (𝓞 K)) (B : ι → GL (Fin n) K), (∀ τ, IsBasisAt w (M τ) (B τ)) →
      Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (transLat lam T M) =
        (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal T).map ((actP lam B).restrictScalars (𝓞 K))) :
    bcPol j (transLat lam T M) = transLat lam T' (fun τ => bcLat j (M τ)) := by
  subst hT
  apply le_antisymm
  · unfold bcPol
    rw [Submodule.span_le]
    rintro _ ⟨F, hF, rfl⟩
    rw [SetLike.mem_coe]
    simp only [transLat, Submodule.mem_iInf]
    intro w' B' hB'
    choose B hB using fun τ => latticeBasisExists_holds K n (M τ) (hM τ) (bcBelow j w')
    have h1 : actP lam B⁻¹ F ∈ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal T := by
      have h := hF
      simp only [SetLike.mem_coe, transLat, Submodule.mem_iInf] at h
      exact h _ B hB
    have h2 := bc_map_mem_locP j w' h1
    rw [baseChangeAction_holds, ← bc_inv_bc] at h2
    exact (hind w' _ B' (fun τ => bc_isBasisAt j w' (hB τ)) hB' _).1 h2
  · refine lc_le_of_le_locP fun w' F' hF' => ?_
    choose B hB using fun τ => latticeBasisExists_holds K n (M τ) (hM τ) (bcBelow j w')
    have h1 : actP lam (fun τ => Formalism.UG.bc j (B τ))⁻¹ F' ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcPol j T) := by
      have h := hF'
      simp only [transLat, Submodule.mem_iInf] at h
      exact h w' (fun τ => Formalism.UG.bc j (B τ)) fun τ => bc_isBasisAt j w' (hB τ)
    have key : ∀ z ∈ bcPol j T, actP lam (fun τ => Formalism.UG.bc j (B τ)) z ∈
        Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcPol j (transLat lam T M)) := by
      intro z hz
      unfold bcPol at hz
      induction hz using Submodule.span_induction with
      | mem z hz =>
        obtain ⟨P, hP, rfl⟩ := hz
        simp only
        rw [← baseChangeAction_holds]
        apply bc_map_mem_locP
        rw [hloc _ B hB]
        exact ⟨P, lc_le_locP _ _ hP, rfl⟩
      | zero => rw [map_zero]; exact Submodule.zero_mem _
      | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
      | smul r x _ hx => rw [LinearMap.map_smul_of_tower]; exact Submodule.smul_mem _ _ hx
    obtain ⟨s, hs, hsx⟩ := (lc_mem_locP _ _ _).1 h1
    have h3 := key _ hsx
    rw [LinearMap.map_smul_of_tower] at h3
    have h4 := (smul_mem_localized_iff w' _ hs _).1 h3
    rw [← polyAction_mul, mul_inv_cancel, polyAction_one₂] at h4
    exact h4

end LocBC

theorem nabDelBaseChange_of (h1 : NabIndep) (h2 : DelIndep) (h3 : NabDelLoc) : NabDelBaseChange := by
  intro K K' _ _ _ _ j ι _ n lam M hM
  constructor
  · exact bc_transLat j lam _ _ (baseChangeStandard_holds K K' j ι n lam).1 M hM
      (fun w' B B' hB hB' F => h1 K' ι n lam w' _ B B' hB hB' F)
      (fun w B hB => (h3 K ι n lam M hM w B hB).1)
  · exact bc_transLat j lam _ _ (baseChangeStandard_holds K K' j ι n lam).2 M hM
      (fun w' B B' hB hB' F => h2 K' ι n lam w' _ B B' hB hB' F)
      (fun w B hB => (h3 K ι n lam M hM w B hB).2)

section Descent

theorem bc_linearIndependent_map {K K' : Type} [Field K] [Field K'] (j : K →+* K') {σ κ : Type}
    (v : κ → MvPolynomial σ K) (hv : LinearIndependent K v) :
    LinearIndependent K' fun i => MvPolynomial.map j (v i) := by
  classical
  let _ : Algebra K K' := j.toAlgebra
  let I : Set (MvPolynomial σ K) := hv.linearIndepOn_id.extend (Set.subset_univ _)
  let b : Module.Basis I K (MvPolynomial σ K) := .extend hv.linearIndepOn_id
  let b' : Module.Basis I K' (MvPolynomial σ K') :=
    (b.baseChange K').map (MvPolynomial.algebraTensorAlgEquiv K K').toLinearEquiv
  let v' (i : κ) : I := ⟨v i, hv.linearIndepOn_id.subset_extend _ <| Set.mem_range_self i⟩
  have hv' : b' ∘ v' = fun i => MvPolynomial.map j (v i) := by
    funext i
    simp [b', b, v', Module.Basis.extend, MvPolynomial.algebraTensorAlgEquiv_tmul]
    rfl
  have h_inj : Function.Injective v' := fun i j hij => hv.injective (congrArg Subtype.val hij)
  rw [← hv']
  exact b'.linearIndependent.comp _ h_inj

open Formalism.L2.Col in

theorem bc_local_basis {K : Type} [Field K] [NumberField K] {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [IsScalarTower (𝓞 K) K V] (w : HeightOneSpectrum (𝓞 K)) {A : Submodule (𝓞 K) V} (hfg : A.FG) :
    ∃ (κ : Type) (_ : Fintype κ) (β : κ → V), LinearIndependent K β ∧
      ∀ x, x ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ↔
        ∃ c : κ → K, (∀ i, c i ∈ Formalism.HermitianLatticesTheory.localization₂ w.asIdeal (1 : Submodule (𝓞 K) K)) ∧ x = ∑ i, c i • β i := by
  have := atW_finite w hfg
  have := atW_free w hfg
  let b := Module.Free.chooseBasis (Ow w) (atW w A)
  have hli : LinearIndependent (Ow w) (fun i => ((b i : atW w A) : V)) :=
    b.linearIndependent.map' (atW w A).subtype (Submodule.ker_subtype _)
  have hliK : LinearIndependent K (fun i => ((b i : atW w A) : V)) :=
    (LinearIndependent.iff_fractionRing (Ow w) K).1 hli
  have hs : Submodule.span (Ow w) (Set.range fun i => ((b i : atW w A) : V)) = atW w A := by
    have h1 : (Set.range fun i => ((b i : atW w A) : V)) = (atW w A).subtype '' Set.range b := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← Submodule.map_span, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  refine ⟨_, inferInstance, fun i => ((b i : atW w A) : V), hliK, fun x => ?_⟩
  have hx : x ∈ atW w A ↔ x ∈ Submodule.span (Ow w) (Set.range fun i => ((b i : atW w A) : V)) := by rw [hs]
  rw [mem_localized_iff_mem_baseChange, hx, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨fun i => algebraMap (Ow w) K (r i), fun i => (mem_localized_one_iff w _).2 ⟨r i, rfl⟩, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    choose r hr using fun i => (mem_localized_one_iff w _).1 (hc i)
    exact ⟨r, Finset.sum_congr rfl fun i _ => by rw [← hr i]; rfl⟩

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')

theorem map_mem_localized_one (w' : HeightOneSpectrum (𝓞 K')) {x : K}
    (h : x ∈ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal (1 : Submodule (𝓞 K) K)) :
    j x ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (1 : Submodule (𝓞 K') K') := by
  obtain ⟨s, hs, hsx⟩ := (lc_mem_locP _ _ _).1 h
  obtain ⟨r, hr⟩ := (lc_mem_one_iff _).1 hsx
  refine (lc_mem_locP _ _ _).2 ⟨bcO j s, bc_notMem j w' hs, (lc_mem_one_iff _).2 ⟨bcO j r, ?_⟩⟩
  rw [bc_coe_bcO, hr, Algebra.smul_def, Algebra.smul_def, map_mul, bc_coe_bcO]

theorem mem_localized_one_of_map_mem (w' : HeightOneSpectrum (𝓞 K')) {x : K}
    (h : j x ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (1 : Submodule (𝓞 K') K')) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal (1 : Submodule (𝓞 K) K) := by
  set w := bcBelow j w' with hw
  rw [mem_localized_one_iff]
  by_cases hx : x = 0
  · exact ⟨0, by rw [hx, map_zero]⟩
  rcases ValuationRing.isInteger_or_isInteger (Formalism.L2.Col.Ow w) x with ⟨r, hr⟩ | ⟨r, hr⟩
  · exact ⟨r, hr⟩
  · by_cases hu : IsUnit r
    · obtain ⟨u, rfl⟩ := hu
      refine ⟨((u⁻¹ : (Formalism.L2.Col.Ow w)ˣ) : Formalism.L2.Col.Ow w), ?_⟩
      have h1 : algebraMap (Formalism.L2.Col.Ow w) K ((u⁻¹ : (Formalism.L2.Col.Ow w)ˣ) : Formalism.L2.Col.Ow w) *
          algebraMap (Formalism.L2.Col.Ow w) K (u : Formalism.L2.Col.Ow w) = 1 := by
        rw [← map_mul, Units.inv_mul, map_one]
      rw [hr] at h1
      field_simp at h1
      exact h1
    · exfalso
      obtain ⟨a, t, rfl⟩ := IsLocalization.exists_mk'_eq w.asIdeal.primeCompl r
      have ha : a ∈ w.asIdeal := by
        have h2 : IsLocalization.mk' (Formalism.L2.Col.Ow w) a t ∈ IsLocalRing.maximalIdeal (Formalism.L2.Col.Ow w) :=
          (IsLocalRing.mem_maximalIdeal _).2 hu
        exact (IsLocalization.AtPrime.mk'_mem_maximal_iff (Formalism.L2.Col.Ow w) w.asIdeal a t).1 h2
      have h1 : algebraMap (Formalism.L2.Col.Ow w) K (IsLocalization.mk' (Formalism.L2.Col.Ow w) a t) * algebraMap (𝓞 K) K (t : 𝓞 K)
          = algebraMap (𝓞 K) K a := by
        rw [IsScalarTower.algebraMap_apply (𝓞 K) (Formalism.L2.Col.Ow w) K, ← map_mul, IsLocalization.mk'_spec,
          ← IsScalarTower.algebraMap_apply]
      rw [hr] at h1
      have ht0 : algebraMap (𝓞 K) K (t : 𝓞 K) ≠ 0 := by
        intro h0
        have : (t : 𝓞 K) = 0 := FaithfulSMul.algebraMap_injective (𝓞 K) K (by rw [h0, map_zero])
        exact t.2 (this ▸ w.asIdeal.zero_mem)
      have h2 : algebraMap (𝓞 K) K (t : 𝓞 K) = algebraMap (𝓞 K) K a * x := by
        rw [← h1]; field_simp
      obtain ⟨s', hs', hsx⟩ := (lc_mem_locP _ _ _).1 h
      obtain ⟨c, hc⟩ := (lc_mem_one_iff _).1 hsx
      have h3 : s' * bcO j (t : 𝓞 K) = bcO j a * c := by
        apply FaithfulSMul.algebraMap_injective (𝓞 K') K'
        rw [map_mul, map_mul, bc_coe_bcO, bc_coe_bcO, hc, h2, map_mul, Algebra.smul_def]
        ring
      have h4 : s' * bcO j (t : 𝓞 K) ∈ w'.asIdeal := by
        rw [h3]
        exact Ideal.mul_mem_right _ _ ha
      rcases w'.isPrime.mem_or_mem h4 with h5 | h5
      · exact hs' h5
      · exact t.2 h5

end Descent

section Descent2

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K'] (j : K →+* K')

theorem bc_local_descent {σ : Type} {T : Submodule (𝓞 K) (MvPolynomial σ K)} (hfg : T.FG)
    (w' : HeightOneSpectrum (𝓞 K')) (P : MvPolynomial σ K)
    (h : MvPolynomial.map j P ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcPol j T)) :
    P ∈ Formalism.HermitianLatticesTheory.localization₂ (bcBelow j w').asIdeal T := by
  classical
  obtain ⟨κ, _, β, hβ, hT⟩ := bc_local_basis (bcBelow j w') hfg
  have hA : ∀ y ∈ bcPol j T, ∃ c : κ → K', (∀ i, c i ∈ Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (1 : Submodule (𝓞 K') K')) ∧
      y = ∑ i, c i • MvPolynomial.map j (β i) := by
    intro y hy
    unfold bcPol at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨t, ht, rfl⟩ := hy
      obtain ⟨c, hc, rfl⟩ := (hT t).1 (lc_le_locP _ _ ht)
      refine ⟨fun i => j (c i), fun i => map_mem_localized_one j w' (hc i), ?_⟩
      simp only [map_sum, bc_map_smul]
    | zero => exact ⟨0, fun i => Submodule.zero_mem _, by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨c, hc, rfl⟩ := hx
      obtain ⟨d, hd, rfl⟩ := hy
      refine ⟨c + d, fun i => Submodule.add_mem _ (hc i) (hd i), ?_⟩
      simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
    | smul r x _ hx =>
      obtain ⟨c, hc, rfl⟩ := hx
      refine ⟨fun i => r • c i, fun i => Submodule.smul_mem _ r (hc i), ?_⟩
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl fun i _ => (smul_assoc r (c i) _).symm
  obtain ⟨s, hs, hsx⟩ := (lc_mem_locP _ _ _).1 h
  obtain ⟨c, hc, hcs⟩ := hA _ hsx
  have hs0 : algebraMap (𝓞 K') K' s ≠ 0 := by
    intro h0
    exact lc_ne_zero_of_notMem w' hs (FaithfulSMul.algebraMap_injective (𝓞 K') K' (by rw [h0, map_zero]))
  have h1 : MvPolynomial.map j P = ∑ i, ((algebraMap (𝓞 K') K' s)⁻¹ * c i) • MvPolynomial.map j (β i) := by
    have h2 : algebraMap (𝓞 K') K' s • MvPolynomial.map j P = ∑ i, c i • MvPolynomial.map j (β i) := by
      rw [← hcs, algebraMap_smul]
    simp only [mul_smul]
    rw [← Finset.smul_sum, ← h2, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  obtain ⟨d, hd⟩ := bc_descent_span j β _ P h1
  have h3 : ∑ i, (j (d i) - (algebraMap (𝓞 K') K' s)⁻¹ * c i) • MvPolynomial.map j (β i) = 0 := by
    simp only [sub_smul, Finset.sum_sub_distrib]
    rw [← h1, hd, sub_eq_zero]
    simp only [map_sum, bc_map_smul]
  have h4 := Fintype.linearIndependent_iff.1 (bc_linearIndependent_map j β hβ) _ h3
  refine (hT P).2 ⟨d, fun i => mem_localized_one_of_map_mem j w' ?_, hd⟩
  rw [sub_eq_zero.1 (h4 i)]
  refine (smul_mem_localized_iff w' _ hs _).1 ?_
  rw [Algebra.smul_def, ← mul_assoc, mul_inv_cancel₀ hs0, one_mul]
  exact hc i

variable {ι : Type} [Fintype ι] {n : ℕ}

theorem bc_nabStd_fg (K : Type) [Field K] [NumberField K] (lam : ι → DomWeight n) : (nabStd K lam).FG := by
  classical
  let S : ι → Set (MvPolynomial (Fin n × Fin n) K) := fun τ =>
    Set.range fun m => toK K _ ((Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW).choose m)
  have h : (fun τ => (nablaSq (𝓞 K) n (lam τ)).map (toK K _)) = fun τ => Submodule.span (𝓞 K) (S τ) := by
    funext τ
    unfold nablaSq
    rw [← (Formalism.GradedWeylDivisibility.sSBasis (𝓞 K) n n (lam τ).natW).choose_spec.1.2.1, Submodule.map_span, ← Set.range_comp]
    rfl
  rw [nabStd, h, nb_tensorLat_span]
  apply Submodule.fg_span
  have hS : ∀ τ, (S τ).Finite := fun τ =>
    haveI : Finite (Formalism.GradedWeylDivisibility.ssIdx n n (lam τ).natW) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
    Set.finite_range _
  have : nbGen S = (fun f => ten f) '' Set.pi Set.univ S := by
    ext P
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, fun τ _ => hf τ, rfl⟩
    · rintro ⟨f, hf, rfl⟩
      exact ⟨f, fun τ => hf τ (Set.mem_univ τ), rfl⟩
  rw [this]
  exact (Set.Finite.pi fun τ => hS τ).image _

theorem bc_delStd_fg (K : Type) [Field K] [NumberField K] (lam : ι → DomWeight n) : (delStd K lam).FG :=
  Submodule.FG.of_le (bc_nabStd_fg K lam) (delStd_le_nabStd K lam)

theorem bc_descent_transLat (lam : ι → DomWeight n) (T : Submodule (𝓞 K) (Pol K ι n)) (hfg : T.FG)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (F : Pol K ι n)
    (h : MvPolynomial.map j F ∈ transLat lam (bcPol j T) (fun τ => bcLat j (M τ))) : F ∈ transLat lam T M := by
  simp only [transLat, Submodule.mem_iInf]
  intro w B hB
  obtain ⟨w', rfl⟩ := bc_exists_above j w
  have h1 : actP lam (fun τ => Formalism.UG.bc j (B τ))⁻¹ (MvPolynomial.map j F) ∈
      Formalism.HermitianLatticesTheory.localization₂ w'.asIdeal (bcPol j T) := by
    have h' := h
    simp only [transLat, Submodule.mem_iInf] at h'
    exact h' w' (fun τ => Formalism.UG.bc j (B τ)) fun τ => bc_isBasisAt j w' (hB τ)
  rw [bc_inv_bc, ← baseChangeAction_holds] at h1
  exact bc_local_descent j hfg w' _ h1

end Descent2

theorem nabDelDescent_of (h : NabDelBaseChange) : NabDelDescent := by
  intro K K' _ _ _ _ j ι _ n lam M hM F
  obtain ⟨h1, h2⟩ := h K K' j ι n lam M hM
  obtain ⟨e1, e2⟩ := baseChangeStandard_holds K K' j ι n lam
  refine ⟨⟨fun hF => ?_, fun hF => ?_⟩, ⟨fun hF => ?_, fun hF => ?_⟩⟩
  · rw [← h1]; exact bc_map_mem j hF
  · unfold nabP at hF ⊢
    rw [← e1] at hF
    exact bc_descent_transLat j lam _ (bc_nabStd_fg K lam) M F hF
  · rw [← h2]; exact bc_map_mem j hF
  · unfold delP at hF ⊢
    rw [← e2] at hF
    exact bc_descent_transLat j lam _ (bc_delStd_fg K lam) M F hF

section AtE

variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι] {n : ℕ}

theorem bc_polOfVV_comap (lam : ι → DomWeight n) (N : Submodule (𝓞 K) (Pol K ι n)) (hN : ∀ F ∈ N, F ∈ VV K lam) :
    polOfVV lam (N.comap ((VV K lam).subtype.restrictScalars (𝓞 K))) = N := by
  ext F
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hF
    exact ⟨⟨F, hN F hF⟩, hF, rfl⟩

theorem usage₁₁ (lam : ι → DomWeight n) (M : ι → Submodule (𝓞 K) (Fin n → K)) : delP lam M ≤ nabP lam M :=
  transLat_mono lam (delStd_le_nabStd K lam) M

theorem bc_dualFr_lattice (h : DualFrLattice) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K (dualFr M) :=
  (@h K _ _ starRingOfComm n 1 M (by simp) hM).1

variable {K' : Type} [Field K'] [NumberField K'] (j : K →+* K')

theorem bc_bcLat_lattice (h : TauLatLattice) (M : Submodule (𝓞 K) (Fin n → K)) (hM : Submodule.IsLattice K M) :
    Submodule.IsLattice K' (bcLat j M) := h K K' Unit n (fun _ => j) () M hM

theorem bc_at (hbc : NabDelBaseChange) (hle : NabLeVV) (htl : TauLatLattice) (lam : ι → DomWeight n)
    (M : ι → Submodule (𝓞 K) (Fin n → K)) (hM : ∀ τ, Submodule.IsLattice K (M τ)) :
    polOfVV lam (nabK lam fun τ => bcLat j (M τ)) = bcPol j (polOfVV lam (nabK lam M)) ∧
    polOfVV lam (delK lam fun τ => bcLat j (M τ)) = bcPol j (polOfVV lam (delK lam M)) := by
  have hM' : ∀ τ, Submodule.IsLattice K' (bcLat j (M τ)) := fun τ => bc_bcLat_lattice j htl (M τ) (hM τ)
  obtain ⟨h1, h2⟩ := hbc K K' j ι n lam M hM
  unfold nabK delK
  rw [bc_polOfVV_comap lam _ (hle K' ι n lam _ hM'), bc_polOfVV_comap lam _ (hle K ι n lam M hM),
    bc_polOfVV_comap lam _ (fun F hF => hle K' ι n lam _ hM' F (usage₁₁ lam _ hF)),
    bc_polOfVV_comap lam _ (fun F hF => hle K ι n lam M hM F (usage₁₁ lam _ hF))]
  exact ⟨h1.symm, h2.symm⟩

end AtE

theorem nabDelBaseChangeAt_of (hbc : NabDelBaseChange) (hle : NabLeVV) (htl : TauLatLattice) (hdl : DualFrLattice)
    (hdf : BaseChangeDualFr) : NabDelBaseChangeAt := by
  intro E K K' _ _ _ _ _ _ j ι _ n emb lam L hL
  have hM : ∀ τ, Submodule.IsLattice K (tauLat emb τ L) := fun τ => htl E K ι n emb τ L hL
  have e1 : (fun τ => tauLat (fun τ => j.comp (emb τ)) τ L) = fun τ => bcLat j (tauLat emb τ L) :=
    funext fun τ => baseChangeTauLattice_holds E K K' j ι n emb τ L
  have e2 : (fun τ => dualFr (tauLat (fun τ => j.comp (emb τ)) τ L)) = fun τ => bcLat j (dualFr (tauLat emb τ L)) :=
    funext fun τ => by rw [baseChangeTauLattice_holds E K K' j ι n emb τ L, hdf K K' j n _ (hM τ)]
  unfold nabAt delAt nabAtr delAtr
  rw [e1, e2]
  obtain ⟨h1, h2⟩ := bc_at j hbc hle htl lam _ hM
  obtain ⟨h3, h4⟩ := bc_at j hbc hle htl lam _ fun τ => bc_dualFr_lattice hdl _ (hM τ)
  exact ⟨h1, h2, h3, h4⟩

theorem nabDelDescentAt_of (hd : NabDelDescent) (htl : TauLatLattice) (hdl : DualFrLattice)
    (hdf : BaseChangeDualFr) : NabDelDescentAt := by
  intro E K K' _ _ _ _ _ _ j ι _ n emb lam L hL x y hxy
  have hM : ∀ τ, Submodule.IsLattice K (tauLat emb τ L) := fun τ => htl E K ι n emb τ L hL
  have e1 : (fun τ => tauLat (fun τ => j.comp (emb τ)) τ L) = fun τ => bcLat j (tauLat emb τ L) :=
    funext fun τ => baseChangeTauLattice_holds E K K' j ι n emb τ L
  have e2 : (fun τ => dualFr (tauLat (fun τ => j.comp (emb τ)) τ L)) = fun τ => bcLat j (dualFr (tauLat emb τ L)) :=
    funext fun τ => by rw [baseChangeTauLattice_holds E K K' j ι n emb τ L, hdf K K' j n _ (hM τ)]
  unfold nabAt delAt nabAtr delAtr
  rw [e1, e2]
  obtain ⟨h1, h2⟩ := hd K K' j ι n lam _ hM x.1
  obtain ⟨h3, h4⟩ := hd K K' j ι n lam _ (fun τ => bc_dualFr_lattice hdl _ (hM τ)) x.1
  rw [← hxy] at h1 h2 h3 h4
  exact ⟨h1, h2, h3, h4⟩

theorem baseChangeDualFrame_holds : BaseChangeDualFr := by
  intro K K' _ _ _ _ j n M hM
  exact du_dualFr_tl latticeBasisExists_holds j M hM

theorem nablaDeltaBaseChange_holds : NabDelBaseChange :=
  nabDelBaseChange_of nablaIndependence_holds deltaIndependence_holds nablaDeltaLocal_holds

theorem nablaDeltaDescent_holds : NabDelDescent := nabDelDescent_of nablaDeltaBaseChange_holds

theorem nablaDeltaBaseChangeAt_holds : NabDelBaseChangeAt :=
  nabDelBaseChangeAt_of nablaDeltaBaseChange_holds nablaLeVV_holds tauLatticeLattice_holds dualFrameLattice_holds
    baseChangeDualFrame_holds

theorem nablaDeltaDescentAt_holds : NabDelDescentAt :=
  nabDelDescentAt_of nablaDeltaDescent_holds tauLatticeLattice_holds dualFrameLattice_holds baseChangeDualFrame_holds

end Formalism.L2.DIV
