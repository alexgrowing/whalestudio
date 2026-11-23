import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasSigFramesOfIsotropic
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.PointShiftStOfPlaceShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.PointMap GlobalTheory.FlatCM GlobalTheory.IndexIdeal GlobalTheory.HTIndex GlobalTheory.PointSig
open GlobalTheory.LieIndex GlobalTheory.HTLat.OmegaRank

namespace GlobalTheory.CMIdeal

theorem ideal_eq_of_map_eq {K : Type} [Field K] [NumberField K] {I J : Ideal (𝓞 K)} (hI : I ≠ ⊥) (hJ : J ≠ ⊥)
    (h : ∀ (ℓ : ℕ) [Fact ℓ.Prime] (i : K →+* ℂ_[ℓ]), ∃ d : 𝓞_ℂ_[ℓ],
      I.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d} ∧
      J.map (embO (PadicComplexInt.integers ℓ) i) = Ideal.span {d}) : I = J := by
  have key : ∀ P : Ideal (𝓞 K), Prime P → emultiplicity P I = emultiplicity P J := fun P hP => by
    let 𝔭 : HeightOneSpectrum (𝓞 K) := ⟨P, Ideal.isPrime_of_prime hP, hP.ne_zero⟩
    obtain ⟨ℓ, hℓ, hm⟩ : ∃ ℓ : ℕ, ℓ.Prime ∧ (ℓ : 𝓞 K) ∈ P := by
      have h0 : Ideal.absNorm P ≠ 0 := Ideal.absNorm_eq_zero_iff.not.2 hP.ne_zero
      have h1 := Ideal.absNorm_mem P
      rw [← Nat.prod_primeFactorsList h0, Nat.cast_list_prod, ← Ideal.Quotient.eq_zero_iff_mem, map_list_prod] at h1
      haveI := 𝔭.isPrime
      haveI : IsDomain (𝓞 K ⧸ P) := Ideal.Quotient.isDomain 𝔭.asIdeal
      obtain ⟨_, h2, h3⟩ := List.mem_map.1 (List.prod_eq_zero_iff.1 h1)
      obtain ⟨ℓ, h4, rfl⟩ := List.mem_map.1 h2
      exact ⟨ℓ, Nat.prime_of_mem_primeFactorsList h4, Ideal.Quotient.eq_zero_iff_mem.1 h3⟩
    haveI : Fact ℓ.Prime := ⟨hℓ⟩
    obtain ⟨i, he, hi⟩ := GlobalTheory.PrimeEmbedding.exists_embedding_norm_eq K 𝔭 ℓ hm
    obtain ⟨d, h1, h2⟩ := h ℓ i
    have e := (norm_of_map_eq_span he hi (algebraMap_embO _ i) hI h1).symm.trans
      (norm_of_map_eq_span he hi (algebraMap_embO _ i) hJ h2)
    have hℓ' : (1 : ℝ) < ℓ := by exact_mod_cast hℓ.one_lt
    have he' : (Formalism.BasicNotions.vAdd 𝔭 (ℓ : K) : ℝ) ≠ 0 := by exact_mod_cast he.ne'
    have e' := (Real.strictMono_rpow_of_base_gt_one hℓ').injective e
    rw [neg_inj, div_left_inj' he', Nat.cast_inj] at e'
    rw [(FiniteMultiplicity.of_prime_left hP hI).emultiplicity_eq_multiplicity,
      (FiniteMultiplicity.of_prime_left hP hJ).emultiplicity_eq_multiplicity]
    exact congrArg _ e'
  exact le_antisymm
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hJ).2 fun P hP => (key P hP).ge))
    (Ideal.le_of_dvd ((UniqueFactorizationMonoid.dvd_iff_emultiplicity_le hI).2 fun P hP => (key P hP).le))

theorem cancel_shift {p q : ℕ} {κ₁ κ₂ : ℝ} {g g' c c' a b : ℝ≥0} (hg : g ≠ 0) (hg' : g' ≠ 0) (hc : c ≠ 0) (hc' : c' ≠ 0)
    (h₀ : Real.log g - Real.log g' = p * κ₁ + q * κ₂) (h₁ : Real.log c = κ₁) (h₂ : -Real.log c' = κ₂)
    (h : c ^ p * g' * a = c' ^ q * g * b) : a = b := by
  have e : c ^ p * g' = c' ^ q * g := by
    refine NNReal.coe_injective (Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity)) (Set.mem_Ioi.2 (by positivity)) ?_)
    push_cast
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
      Real.log_pow]
    subst h₁ h₂
    linarith
  rw [e] at h
  exact mul_left_cancel₀ (mul_ne_zero (pow_ne_zero _ hc') hg) h

theorem exists_matrix_of_mem {O C U : Type} [CommRing O] [Field C] [Algebra O C] [AddCommGroup U] [Module C U]
    [Module O U] [IsScalarTower O C U] {n : ℕ} {x u : Fin n → U} (h : ∀ a, u a ∈ Submodule.span O (Set.range x)) :
    ∃ m : Matrix (Fin n) (Fin n) C, ∀ a, u a = ∑ k, m a k • x k := by
  choose m hm using fun a => (Submodule.mem_span_range_iff_exists_fun C).1 (Submodule.span_le_restrictScalars O C _ (h a))
  exact ⟨m, fun a => (hm a).symm⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {K : Type} [Field K] [NumberField K]
  {ρ : 𝓞 K} {σ₁ : K →+* ℂ} {p q : ℕ} {X : CMObj H K ρ σ₁ p q} {FP : GenFib (X.A true).pol}
  {FQ : GenFib (X.A false).pol} {FB : GenFib X.B.pol}
  {MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))} {MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))}
  {τ : 𝓞 E →+* 𝓞 K}

section At

variable {ℓ : ℕ} [Fact ℓ.Prime] {C : Type} [Field C] [IsAlgClosed C] [CharZero C] {v : Valuation C ℝ≥0} {O : Type}
  [CommRing O] [Algebra O C] [Fact ¬IsUnit (ℓ : O)] [IsAdicComplete (Ideal.span {(ℓ : O)}) O] [Algebra ℤ_[ℓ] O]
  [Algebra ℤ_[ℓ] C] [IsScalarTower ℤ_[ℓ] O C] (hv : v.Integers O) (ε : Eps ℓ C) (i : K →+* C)

open Classical in

theorem map_eq_at (hD : IsDiffs FP FQ FB MP MQ) (hτ : τ H.rt = ρ) {φ : E →+* C} (hφ : embO hv φ = (embO hv i).comp τ)
    {n δ : O} (hR : IsIndexRel hv ε i X φ (Ideal.span {n}) δ) {κ₁ κ₂ : ℝ} : letI := H.starRing
    HasSigFrames (pointB hv ε i X) H.rt φ p q → HasSigFrames (pointA hv ε i X true) H.rt φ 1 0 →
    HasSigFrames (pointA hv ε i X false) H.rt φ 0 1 →
    (∀ (P : Point ℓ v O (𝓞 E)) (p q : ℕ),
      (∀ ψ : E →+* C, Module.finrank C (P.eigW (embO P.integers ψ)) = if ψ (H.rt : E) = φ (H.rt : E) then p else q) →
      ∀ (x : Fin p → LieG P.Gt) (x' : Fin q → LieG P.Gt) (g : Matrix (Fin p) (Fin p) C) (g' : Matrix (Fin q) (Fin q) C),
        Submodule.span O (Set.range fun i => P.bLie (x i)) = P.wRec (embO P.integers φ) →
        Submodule.span O (Set.range fun i => P.bLie (x' i)) = P.wRec ((embO P.integers φ).comp (starRingEnd (𝓞 E))) →
        IsLatBasis C (P.latTQuot (σ := fun φ : E →+* C => embO P.integers φ) (isSplitting_embO P.integers) φ)
          (fun i => ∑ j, g i j • P.bLie (x j)) →
        IsLatBasis C (P.latTSub ((embO P.integers φ).comp (starRingEnd (𝓞 E)))) (fun i => ∑ j, g' i j • P.bLie (x' j)) →
        Real.log (v g.det) - Real.log (v g'.det) = p * κ₁ + q * κ₂) →
    ∃ d : O, (idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ)).map (embO hv i) * Ideal.span {δ} = Ideal.span {d} ∧
      Ideal.span {n} * (idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
        (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))).map (embO hv i) = Ideal.span {d} := by
  letI := H.starRing
  rintro ⟨b0, x, x', g, g', b1, b2, b3, b4, b5, b6, -, -, b7, b8, b9, b10⟩
    ⟨p0, y, y₀, c, c₀, p1, p2, p3, p4, p5, -, -, -, -, -, p9, -⟩
    ⟨q0, z₀, z, e₀, e, q1, q2, q3, q4, -, q6, -, -, -, -, -, q10⟩ hS
  have sB := hS _ p q b0 x x' g g' b1 b2 b3 b4
  have sP := hS _ 1 0 p0 y y₀ c c₀ p1 p2 p3 p4
  have sQ := hS _ 0 1 q0 z₀ z e₀ e q1 q2 q3 q4
  simp only [Matrix.det_isEmpty, map_one, NNReal.coe_one, Real.log_one, sub_zero, zero_sub, Nat.cast_one, Nat.cast_zero,
    one_mul, zero_mul, add_zero, zero_add] at sP sQ
  obtain ⟨m, hm⟩ := exists_matrix_of_mem (C := C) fun a => b1.ge (patV_mem_wRec (T := X.A true) hv ε i (X.lin (.inl a)) _ _
    (p1.le (Submodule.subset_span ⟨0, rfl⟩)))
  obtain ⟨m', hm'⟩ := exists_matrix_of_mem (C := C) fun a => b2.ge (patV_mem_wRec (T := X.A false) hv ε i
    (X.lin (.inr a)) _ _ (q2.le (Submodule.subset_span ⟨0, rfl⟩)))
  have e₁ := hR.val_det x x' y z g m g' m' c e b5 b6 p5 q6 b9 b10 p9 q10 b3 b4 p3 q4 hm hm'
  obtain ⟨-, hP, hQ⟩ := lie_index hv ε i hD hτ
  rw [Set.range_unique] at p1 q2
  obtain ⟨d₁, hd₁, f₁⟩ := hP _ hφ x (fun _ => y 0) m b7 b1 (fun _ => p1) hm
  obtain ⟨d₂, hd₂, f₂⟩ := hQ ((embO hv φ).comp (starRingEnd (𝓞 E))) (by rw [hφ]; rfl) x' (fun _ => z 0) m' b8 b2
    (fun _ => q2) hm'
  have e₂ : v (algebraMap O C (d₁ * δ)) = v (algebraMap O C (n * d₂)) := by
    refine cancel_shift ((map_ne_zero v).2 b5) ((map_ne_zero v).2 b6) ((map_ne_zero v).2 p5) ((map_ne_zero v).2 q6)
      sB sP sQ ?_
    rw [map_mul, map_mul, map_mul, map_mul, hd₁, hd₂]
    calc _ = _ := by ring
      _ = _ := e₁
      _ = _ := by ring
  refine ⟨d₁ * δ, by rw [f₁, Ideal.span_singleton_mul_span_singleton], ?_⟩
  rw [f₂, Ideal.span_singleton_mul_span_singleton]
  exact le_antisymm (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.ge))
    (Ideal.span_singleton_le_span_singleton.2 (hv.le_iff_dvd.1 e₂.le))

end At

theorem ideal_of_frames (hS : PlaceShiftSt) (hH : GlobalTheory.IndefiniteRowSideFullHecke.EigenvectorLieDegree.IsHostField H) (X : CMObj H K ρ σ₁ p q)
    {gP : Matrix (Fin p) (Fin p) (𝓞 E)} {gQ : Matrix (Fin q) (Fin q) (𝓞 E)} (h : IsGram X gP gQ)
    (hF : ∀ (ℓ : ℕ) [Fact ℓ.Prime] [IsAdicComplete (Ideal.span {(ℓ : 𝓞_ℂ_[ℓ])}) 𝓞_ℂ_[ℓ]] (ε : Eps ℓ ℂ_[ℓ])
      (i : K →+* ℂ_[ℓ]) (τ : E →+* ℂ_[ℓ]), τ (H.rt : E) = i (ρ : K) →
      letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
      HasSigFrames (pointB (PadicComplexInt.integers ℓ) ε i X) H.rt τ p q ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X true) H.rt τ 1 0 ∧
        HasSigFrames (pointA (PadicComplexInt.integers ℓ) ε i X false) H.rt τ 0 1) :
    ∃ 𝔫 : Ideal (𝓞 E), 𝔫 * 𝔫.map (H.bar : 𝓞 E →+* 𝓞 E) = Ideal.span {gP.det * gQ.det} ∧
      ∀ (FP : GenFib (X.A true).pol) (FQ : GenFib (X.A false).pol) (FB : GenFib X.B.pol)
        (MP : Fin p → ((Fin FP.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K)))
        (MQ : Fin q → ((Fin FQ.P₀.g → K) →ₗ[K] (Fin FB.P₀.g → K))), IsDiffs FP FQ FB MP MQ →
        ∀ τ : 𝓞 E →+* 𝓞 K, τ H.rt = ρ →
          idx K p (FB.eigLat X.B.t.act τ) (subP FP FB MP τ) * Ideal.span {τ gQ.det} =
            𝔫.map τ * idx K q (FB.eigLat X.B.t.act (τ.comp (H.bar : 𝓞 E →+* 𝓞 E)))
              (subQ FQ FB MQ (τ.comp (H.bar : 𝓞 E →+* 𝓞 E))) := by
  obtain ⟨𝔫, h1, h2⟩ := index_ideal X h
  refine ⟨𝔫, h1, fun FP FQ FB MP MQ hD τ hτ => ?_⟩
  obtain ⟨n1, n2⟩ := idx_sub_ne_bot hD hτ
  obtain ⟨g1, g2, -⟩ := GlobalTheory.GramAt.gram_det X h
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    by_contra h0
    have h := Ideal.absNorm_mem (RingHom.ker τ)
    rw [RingHom.mem_ker, map_natCast, Nat.cast_eq_zero] at h
    exact h0 (Ideal.absNorm_eq_zero_iff.1 h)
  have h𝔫 : 𝔫 ≠ ⊥ := by
    rintro rfl
    rw [Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h1
    exact mul_ne_zero g1 g2 h1
  refine ideal_eq_of_map_eq (mul_ne_zero n1 (Ideal.span_singleton_eq_bot.not.2 ((map_ne_zero_iff τ hinj).2 g2)))
    (mul_ne_zero ((Ideal.map_eq_bot_iff_of_injective hinj).not.2 h𝔫) n2) fun ℓ _ i => ?_
  letI := H.starRing; letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
  haveI := PadicComplexHost.isAdicComplete ℓ
  obtain ⟨ε⟩ : Nonempty (Eps ℓ ℂ_[ℓ]) := inferInstance
  obtain ⟨φ, hφ, hI⟩ := h2 ℓ ε i τ
  have hrt : φ (H.rt : E) = i (ρ : K) := by
    rw [← algebraMap_embO (PadicComplexInt.integers ℓ) φ, hφ, RingHom.comp_apply, hτ, algebraMap_embO]
  obtain ⟨fB, fP, fQ⟩ := hF ℓ ε i φ hrt
  have hR := isIndexRel_of_hasSigFrames (PadicComplexInt.integers ℓ) ε i X h φ fB fP fQ _ hI
  obtain ⟨-, n, -, -, -, -, hn⟩ := hI
  obtain ⟨κ₁, κ₂, hκ⟩ := PlaceShiftModel.pointShiftSt_of_placeShiftSt hS E H hH ℓ φ
  rw [← hn] at hR
  have hn' : ∀ x : ℂ_[ℓ], ‖x‖ = ((Valued.v x : ℝ≥0) : ℝ) := fun x => by
    rw [PadicComplex.norm_eq_norm, Valued.v.norm_def, PadicComplex.RankOne.hom_eq_embedding,
      Valuation.embedding_restrict]
  obtain ⟨d, e₁, e₂⟩ := map_eq_at (PadicComplexInt.integers ℓ) ε i hD hτ hφ hR fB fP fQ
    fun P p q a x x' g g' b c d e => by rw [← hn', ← hn']; exact hκ P p q a x x' g g' b c d e
  refine ⟨d, ?_, ?_⟩
  · rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton, ← e₁, hφ]
    rfl
  · rw [Ideal.map_mul, Ideal.map_map, ← hn, e₂]

theorem idealSt_of_placeShiftSt : PlaceShiftSt → IdealSt := fun hS _ _ _ _ H hH _ _ _ _ _ _ _ X _ _ h =>
  ideal_of_frames hS hH X h fun ℓ _ _ ε i τ hτ => by
    letI := algPadicInt ℓ; letI := algPadicField ℓ; haveI := towerPadic ℓ; haveI := factPadic ℓ
    exact CMKernel.hasSigFrames_of_isGram _ ε i X h τ hτ

end GlobalTheory.CMIdeal
