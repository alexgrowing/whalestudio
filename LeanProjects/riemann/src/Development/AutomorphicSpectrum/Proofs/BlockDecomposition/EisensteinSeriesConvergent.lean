import Mathlib
import Development.WeilBound.ThetaLifts.LatticeBasics.HypothesesE
import Development.WeilBound.ThetaLifts.LatticeBasics.UnfoldC
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EmbBar
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegersBoundedEmbeddingsCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DenominatorBoundByHeightStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuadraticIntegralCoefficientsBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SummableHeightPowOfPolynomialCountStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LeftInvertibleExistsNonzeroMinorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PluckerMinorsDetermineColumnSpaceStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinitePlaceMinorHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchimedeanMinorHeightBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardCompactEntriesIntegralStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormFinitePlaceBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormInfinitePlaceBoundStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
open GlobalTheory.Doubling (absE)
open GlobalTheory.CompanionTheory.GodementH

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}
  {J : Type} [Fintype J]

theorem absBar_one (v : Pl F) : absBar F v 1 = 1 := by
  simpa using absBar_algebraMap F v 1

theorem le_supBar (v : Pl F) (τ : E →ₐ[F] FvBar F v) (u : J → E) (f : J) : absBar F v (τ (u f)) ≤ supBar v τ u :=
  Finset.le_sup (f := fun f => absBar F v (τ (u f))) (Finset.mem_univ f)

theorem one_le_supBar (v : Pl F) (τ : E →ₐ[F] FvBar F v) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ supBar v τ u := by
  have := le_supBar v τ u f₀
  rwa [hu, map_one, absBar_one] at this

theorem one_le_locFin (v : Pl F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ locFin σ v u :=
  one_le_mul_of_one_le_of_one_le (one_le_supBar v _ hu) (one_le_supBar v _ hu)

open Classical in
theorem le_supInf (w : InfinitePlace F) (τ : EmbOver E w) (u : J → E) (f : J) :
    ‖τ.1 (u f)‖₊ ≤ Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊ :=
  Finset.le_sup (f := fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊) (Finset.mem_univ (τ, f))

open Classical in
theorem one_le_supInf (w : InfinitePlace F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    1 ≤ Finset.univ.sup fun p : EmbOver E w × J => ‖p.1.1 (u p.2)‖₊ := by
  obtain ⟨τ⟩ := nonempty_embOver (E := E) F w
  have := le_supInf w τ u f₀
  rwa [hu, map_one, nnnorm_one] at this

theorem one_le_locInf (w : InfinitePlace F) {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ locInf w u :=
  one_le_pow₀ (one_le_supInf w hu)

theorem absBar_le_absFin (v : Pl F) (τ : E →ₐ[F] FvBar F v) (x : E) : absBar F v (τ x) ≤ absFin F v ((1 : Fv F v) ⊗ₜ[F] x) := by
  have := le_absFin F v τ ((1 : Fv F v) ⊗ₜ[F] x)
  simpa using this

theorem compFin_inclR (v : Pl F) (x : E) : compFin F E v (inclR (F := F) (AF F) x) = (1 : Fv F v) ⊗ₜ[F] x := by
  simp [compFin, inclR]

theorem eventually_abs_le_one (x : E) : ∀ᶠ v : Pl F in cofinite, ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ x) ≤ 1 := by
  refine (eventually_absFin_le_one F (inclR (F := F) (AF F) x)).mono fun v hv τ => ?_
  rw [compFin_inclR] at hv
  exact (absBar_le_absFin v τ x).trans hv

theorem finite_mulSupport_locFin (σ : E →ₐ[F] E) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    (Function.mulSupport fun v : Pl F => locFin σ v u).Finite := by
  have h : ∀ᶠ v : Pl F in cofinite, ∀ f, ∀ τ : E →ₐ[F] FvBar F v, absBar F v (τ (u f)) ≤ 1 :=
    eventually_all.2 fun f => eventually_abs_le_one (u f)
  refine (eventually_cofinite.1 h).subset fun v hv hv' => hv ?_
  have h1 : ∀ τ : E →ₐ[F] FvBar F v, supBar v τ u ≤ 1 := fun τ => Finset.sup_le fun f _ => hv' f τ
  exact le_antisymm (by simpa [locFin] using mul_le_mul' (h1 (embBar F E v)) (h1 ((embBar F E v).comp σ))) (one_le_locFin v hu)

theorem one_le_vecHt {u : J → E} {f₀ : J} (hu : u f₀ = 1) : 1 ≤ vecHt σ u :=
  one_le_mul_of_one_le_of_one_le (Finset.one_le_prod' fun w _ => one_le_locInf w hu)
    (one_le_finprod' fun v => one_le_locFin v hu)

theorem absE_mul_vecHt_le (hcm : IsCMExt F E σ) (e : ∀ w : InfinitePlace F, EmbOver E w) {u : J → E} {f₀ : J} (hu : u f₀ = 1)
    (δ : (AE F E)ˣ) (z : J → AE F E) (hz : ∀ f, z f = inclR (F := F) (AF F) (u f) * δ.1)
    (Bi : InfinitePlace F → ℝ≥0) (Bf : Pl F → ℝ≥0) (hB : (Function.mulSupport Bf).Finite)
    (hi : ∀ w f, ‖piInf (e w) (z f)‖₊ ≤ Bi w) (hf : ∀ v f, absFin F v (compFin F E v (z f)) ≤ Bf v) :
    absE F E δ * vecHt σ u ≤ (∏ w, Bi w ^ 2) * ∏ᶠ v, Bf v ^ 2 := by
  have hs := finite_mulSupport_locFin σ hu
  have hs2 := GlobalTheory.Doubling.finite_mulSupport_absEv δ
  rw [GlobalTheory.Doubling.absE_apply, vecHt, mul_mul_mul_comm, ← Finset.prod_mul_distrib, ← finprod_mul_distrib hs2 hs]
  refine mul_le_mul' (Finset.prod_le_prod' fun w _ => ?_) (finprod_le_finprod' (hs2.union hs |>.subset (Function.mulSupport_mul _ _))
    (hB.subset (Function.mulSupport_pow _ _)) fun v => ?_)
  · refine GlobalTheory.T.local_norm_infinite_place_bound F E σ hcm J w (e w) u _ (fun f => compInf F E w (z f)) (Bi w) (fun f => ?_) (fun f => hi w f)
    rw [hz, map_mul]
    congr 1
  · refine GlobalTheory.T.local_norm_finite_place_bound F E σ hcm J v u _ (fun f => compFin F E v (z f)) (Bf v) (fun f => ?_) (fun f => hf v f)
    rw [hz, map_mul, compFin_inclR]
    rfl

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {J : Type} [Fintype J]

theorem exists_embOver (hcm : IsCMExt F E σ) (τ : E →+* ℂ) : ∃ (w : InfinitePlace F) (e : EmbOver E w), e.1 = τ := by
  have := hcm.1
  let φ : F →+* ℂ := τ.comp (algebraMap F E)
  have hr : ComplexEmbedding.IsReal φ := InfinitePlace.isReal_mk_iff.1 (IsTotallyReal.isReal (InfinitePlace.mk φ))
  exact ⟨InfinitePlace.mk φ, ⟨τ, (InfinitePlace.embedding_mk_eq_of_isReal hr).symm⟩, rfl⟩

theorem isIntegral_of_quad {z b c : E} (hb : IsIntegral ℤ b) (hc : IsIntegral ℤ c) (h : z ^ 2 - b * z + c = 0) : IsIntegral ℤ z := by
  let R := integralClosure ℤ E
  let b' : R := ⟨b, hb⟩
  let c' : R := ⟨c, hc⟩
  have hz : IsIntegral R z := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-b') * Polynomial.X + Polynomial.C c'), ?_, ?_⟩
    · refine Polynomial.monic_X_pow_add (lt_of_le_of_lt Polynomial.degree_linear_le ?_)
      norm_num
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C]
      change z ^ 2 + (-b * z + c) = 0
      linear_combination h
  exact isIntegral_trans z hz

theorem denom_one (hcm : IsCMExt F E σ) {u : J → E} {f₀ : J} (hu : u f₀ = 1) (f : J) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ (∏ᶠ v, locFin σ v u) ^ 2 ∧ IsIntegral ℤ ((m : E) * u f) := by
  obtain ⟨y₁, y₂, hq, hy⟩ := GlobalTheory.T.quadratic_integral_coefficients_bound F E σ hcm (u f)
  have hloc : ∀ (v : Pl F), max 1 ‖algebraMap F (Fv F v) y₁‖₊ ≤ locFin σ v u ∧ max 1 ‖algebraMap F (Fv F v) y₂‖₊ ≤ locFin σ v u := by
    intro v
    obtain ⟨h1, h2⟩ := hy v (embBar F E v)
    have a1 := le_supBar v (embBar F E v) u f
    have b1 := le_supBar v ((embBar F E v).comp σ) u f
    have a2 : 1 ≤ supBar v (embBar F E v) u := one_le_supBar v _ hu
    have b2 : 1 ≤ supBar v ((embBar F E v).comp σ) u := one_le_supBar v _ hu
    have hl : locFin σ v u = supBar v (embBar F E v) u * supBar v ((embBar F E v).comp σ) u := rfl
    have hb1 : absBar F v (embBar F E v (σ (u f))) ≤ supBar v ((embBar F E v).comp σ) u := b1
    refine ⟨max_le (one_le_locFin v hu) ?_, max_le (one_le_locFin v hu) ?_⟩
    · refine h1.trans (max_le ?_ ?_)
      · rw [hl]; exact a1.trans (le_mul_of_one_le_right' b2)
      · rw [hl]; exact hb1.trans (le_mul_of_one_le_left' a2)
    · rw [h2, hl]; exact mul_le_mul' a1 hb1
  have hs := finite_mulSupport_locFin σ hu
  have hsup : ∀ y : F, (∀ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ locFin σ v u) →
      ∏ᶠ v : Pl F, max 1 ‖algebraMap F (Fv F v) y‖₊ ≤ ∏ᶠ v, locFin σ v u := by
    intro y hy
    have hsub : (Function.mulSupport fun v : Pl F => max 1 ‖algebraMap F (Fv F v) y‖₊).Finite := by
      refine hs.subset fun v hv hv' => hv ?_
      exact le_antisymm ((hy v).trans (le_of_eq hv')) (le_max_left _ _)
    exact finprod_le_finprod' hsub hs hy
  obtain ⟨m₁, p₁, l₁, i₁⟩ := GlobalTheory.T.denominator_bound_by_height F y₁
  obtain ⟨m₂, p₂, l₂, i₂⟩ := GlobalTheory.T.denominator_bound_by_height F y₂
  refine ⟨m₁ * m₂, Nat.mul_pos p₁ p₂, ?_, ?_⟩
  · rw [sq]; push_cast
    exact mul_le_mul' (l₁.trans (hsup _ fun v => (hloc v).1)) (l₂.trans (hsup _ fun v => (hloc v).2))
  · have j₁ : IsIntegral ℤ ((m₁ : E) * algebraMap F E y₁) := by
      have := i₁.map (IsScalarTower.toAlgHom ℤ F E)
      simpa using this
    have j₂ : IsIntegral ℤ ((m₂ : E) * algebraMap F E y₂) := by
      have := i₂.map (IsScalarTower.toAlgHom ℤ F E)
      simpa using this
    have n₁ : IsIntegral ℤ (m₁ : E) := isIntegral_natCast _
    have n₂ : IsIntegral ℤ (m₂ : E) := isIntegral_natCast _
    refine isIntegral_of_quad (b := (m₂ : E) * ((m₁ : E) * algebraMap F E y₁))
      (c := (m₁ : E) ^ 2 * (m₂ : E) * ((m₂ : E) * algebraMap F E y₂)) (n₂.mul j₁) (((n₁.pow 2).mul n₂).mul j₂) ?_
    push_cast
    linear_combination ((m₁ : E) * m₂) ^ 2 * hq

theorem denom_all (hcm : IsCMExt F E σ) {u : J → E} {f₀ : J} (hu : u f₀ = 1) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ≥0) ≤ (∏ᶠ v, locFin σ v u) ^ (2 * Fintype.card J) ∧ ∀ f, IsIntegral ℤ ((m : E) * u f) := by
  classical
  choose m hm hl hi using denom_one hcm hu
  refine ⟨∏ f, m f, Finset.prod_pos fun f _ => hm f, ?_, fun f => ?_⟩
  · push_cast
    calc ∏ f, (m f : ℝ≥0) ≤ ∏ _f : J, (∏ᶠ v, locFin σ v u) ^ 2 := Finset.prod_le_prod' fun f _ => hl f
      _ = _ := by rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
  · rw [← Finset.mul_prod_erase Finset.univ m (Finset.mem_univ f)]
    push_cast
    have : ((m f : E) * ∏ x ∈ Finset.univ.erase f, (m x : E)) * u f = (∏ x ∈ Finset.univ.erase f, (m x : E)) * ((m f : E) * u f) := by ring
    rw [this]
    refine IsIntegral.mul ?_ (hi f)
    exact_mod_cast (isIntegral_natCast (R := ℤ) (B := E) (∏ x ∈ Finset.univ.erase f, m x))

theorem count (hcm : IsCMExt F E σ) (J : Type) [Fintype J] : ∃ (C : ℝ) (c : ℕ), 0 < C ∧ ∀ T : ℝ, 1 ≤ T →
    {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T}.Finite ∧
    (Set.ncard {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} : ℝ) ≤ C * T ^ c := by
  classical
  obtain ⟨C₀, hC₀, hlat⟩ := GlobalTheory.T.integers_bounded_embeddings_count E
  set Jc := Fintype.card J with hJc
  set d := Module.finrank ℚ E with hd
  refine ⟨C₀ ^ Jc, 2 * Jc + (2 * Jc + 1) * d * Jc, pow_pos hC₀ _, fun T hT => ?_⟩
  set R : ℝ := T ^ (2 * Jc + 1) with hR
  have hR1 : 1 ≤ R := one_le_pow₀ hT
  obtain ⟨hLf, hLc⟩ := hlat R hR1
  set N₀ : ℕ := ⌊T ^ (2 * Jc)⌋₊ with hN₀
  let P : Finset (ℕ × (J → 𝓞 E)) := Finset.Icc 1 N₀ ×ˢ Fintype.piFinset fun _ : J => hLf.toFinset
  let φ : ℕ × (J → 𝓞 E) → J → E := fun p f => (p.2 f : E) / (p.1 : E)
  have hsub : {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ⊆ φ '' (P : Set _) := by
    rintro u ⟨⟨f₀, hu⟩, huT⟩
    obtain ⟨m, hm, hl, hi⟩ := denom_all hcm hu
    have hHi : 1 ≤ ∏ w : InfinitePlace F, locInf w u := Finset.one_le_prod' fun w _ => one_le_locInf w hu
    have hHf : 1 ≤ ∏ᶠ v, locFin σ v u := one_le_finprod' fun v => one_le_locFin v hu
    have hHf' : ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ≤ T := by
      refine le_trans ?_ huT
      exact_mod_cast le_mul_of_one_le_left' hHi
    have hHi' : ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ) ≤ T := by
      refine le_trans ?_ huT
      exact_mod_cast le_mul_of_one_le_right' hHf
    have hmT : (m : ℝ) ≤ T ^ (2 * Jc) := by
      have h1 : (m : ℝ) ≤ ((∏ᶠ v, locFin σ v u : ℝ≥0) : ℝ) ^ (2 * Jc) := by exact_mod_cast hl
      exact h1.trans (pow_le_pow_left₀ (by positivity) hHf' _)
    have hconj : ∀ (τ : E →+* ℂ) f, ‖τ (u f)‖ ≤ T := by
      intro τ f
      obtain ⟨w, e, rfl⟩ := exists_embOver hcm τ
      have h1 := le_supInf w e u f
      have h2 := one_le_supInf w (u := u) hu
      have h3 : locInf w u ≤ ∏ w : InfinitePlace F, locInf w u :=
        Finset.single_le_prod' (f := fun w : InfinitePlace F => locInf w u) (fun w _ => one_le_locInf w hu) (Finset.mem_univ w)
      have h4 : ‖e.1 (u f)‖₊ ≤ locInf w u := by
        refine h1.trans ?_
        rw [locInf]
        exact le_self_pow₀ h2 two_ne_zero
      have h5 : (‖e.1 (u f)‖₊ : ℝ) ≤ ((∏ w : InfinitePlace F, locInf w u : ℝ≥0) : ℝ) := by exact_mod_cast h4.trans h3
      exact h5.trans hHi'
    refine ⟨(m, fun f => ⟨(m : E) * u f, hi f⟩), ?_, ?_⟩
    · refine Finset.mem_coe.2 (Finset.mem_product.2 ⟨Finset.mem_Icc.2 ⟨hm, Nat.le_floor hmT⟩,
        Fintype.mem_piFinset.2 fun f => hLf.mem_toFinset.2 fun τ => ?_⟩)
      change ‖τ ((m : E) * u f)‖ ≤ R
      rw [map_mul, map_natCast, norm_mul, Complex.norm_natCast, hR, pow_succ]
      exact mul_le_mul hmT (hconj τ f) (norm_nonneg _) (by positivity)
    · funext f
      have : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
      change (m : E) * u f / (m : E) = u f
      field_simp
  have hfin : (φ '' (P : Set _)).Finite := P.finite_toSet.image φ
  refine ⟨hfin.subset hsub, ?_⟩
  have h1 : Set.ncard {u : J → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} ≤ P.card :=
    (Set.ncard_le_ncard hsub hfin).trans ((Set.ncard_image_le P.finite_toSet).trans (Set.ncard_coe_finset P).le)
  have h2 : (P.card : ℝ) ≤ T ^ (2 * Jc) * (C₀ * R ^ d) ^ Jc := by
    have e1 : P.card = N₀ * hLf.toFinset.card ^ Jc := by
      simp [P, Finset.card_product, Fintype.card_piFinset, hJc]
    rw [e1]
    push_cast
    have e2 : (N₀ : ℝ) ≤ T ^ (2 * Jc) := Nat.floor_le (by positivity)
    have e3 : (hLf.toFinset.card : ℝ) ≤ C₀ * R ^ d := by
      rw [← Set.ncard_eq_toFinset_card _ hLf]; exact hLc
    exact mul_le_mul e2 (pow_le_pow_left₀ (by positivity) e3 _) (by positivity) (by positivity)
  calc _ ≤ (P.card : ℝ) := by exact_mod_cast h1
    _ ≤ _ := h2
    _ = _ := by rw [hR]; ring

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {n : ℕ}

theorem mnr_mul_det {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι] (M : Matrix ι (Fin n) R) (t : Matrix (Fin n) (Fin n) R) (f : Fin n → ι) :
    mnr (M * t) f = mnr M f * t.det := by
  rw [mnr, mnr, ← Matrix.det_mul]; congr 1

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

abbrev Ix (n : ℕ) : Type := Fin n ⊕ Fin n

def pl (b g : GL (Ix n) E) : Matrix (Ix n) (Fin n) E :=
  ((b⁻¹).1 * (g⁻¹).1 : Matrix (Ix n) (Ix n) E) * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E)

theorem incM_diagCols : incM F (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = diagCols (Fin n) := by
  ext i j
  rcases i with i | i <;> simp [incM, diagCols, Matrix.one_apply, apply_ite]

theorem incM_mul {l m o : Type} [Fintype m] (A : Matrix l m E) (B : Matrix m o E) : incM F (A * B) = incM F A * incM F B :=
  Matrix.map_mul

theorem incM_one {m : Type} [Fintype m] [DecidableEq m] : incM F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem incM_inv_mul {m : Type} [Fintype m] [DecidableEq m] (b : GL m E) : incM F (b⁻¹).1 * incM F b.1 = 1 := by
  rw [← incM_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, incM_one]

theorem incM_mul_inv {m : Type} [Fintype m] [DecidableEq m] (b : GL m E) : incM F b.1 * incM F (b⁻¹).1 = 1 := by
  rw [← incM_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, incM_one]

theorem frame_identity {b g : GL (Ix n) E} {t₀ : GL (Fin n) E} (h0 : b.1.toCols₁ = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E)) {γ x p k : G2 σ Y}
    {t : GL (Fin n) (AE F E)} (hγ : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1)
    (hp : IsPar p t) (hy : γ * x = p * k) :
    incM F (pl b g) * (t.1 * incM F t₀.1) = ((inFrame b x * inFrame b k⁻¹).submatrix id Sum.inl) := by
  have hg : mat2 γ⁻¹ = incM F (g⁻¹).1 := by
    have : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g⁻¹ = (γ⁻¹).1 := by
      rw [map_inv, hγ]; rfl
    exact (congrArg Units.val this).symm
  have h1 : mat2 x * mat2 k⁻¹ = mat2 γ⁻¹ * mat2 p := by
    have : x * k⁻¹ = γ⁻¹ * p := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]
    exact congrArg mat2 this
  have h2 : (incM F b.1).submatrix id Sum.inl = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * incM F t₀.1 := by
    have : (incM F b.1).submatrix id Sum.inl = incM F b.1.toCols₁ := rfl
    rw [this, h0, incM_mul, incM_diagCols]
  have h3 : inFrame b x * inFrame b k⁻¹ = incM F (b⁻¹).1 * (mat2 x * mat2 k⁻¹) * incM F b.1 := by
    unfold inFrame
    calc _ = incM F (b⁻¹).1 * mat2 x * (incM F b.1 * incM F (b⁻¹).1) * mat2 k⁻¹ * incM F b.1 := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [incM_mul_inv, Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have h4 : ∀ (A : Matrix (Ix n) (Ix n) (AE F E)), (A * incM F b.1).submatrix id Sum.inl = A * (incM F b.1).submatrix id Sum.inl := by
    intro A; ext i j; simp [Matrix.mul_apply]
  rw [h3, h4, h2, h1, hg, pl, incM_mul, incM_mul, incM_diagCols]
  calc _ = incM F (b⁻¹).1 * incM F (g⁻¹).1 * ((diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * t.1) * incM F t₀.1 := by
        simp only [Matrix.mul_assoc]
    _ = _ := by
        have hp' : mat2 p * (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) (AE F E)) * t.1 := hp
        rw [← hp']; simp only [Matrix.mul_assoc]

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ} {Y : Spc F E n}

theorem exists_widePullback_of_iteratedLine {ι : Type} [Fintype ι] (N : ℝ≥0) (h : ι → ℝ≥0) (n : ℕ) :
    ∏ w, (N * h w ^ n) ^ 2 = N ^ (2 * Fintype.card ι) * (∏ w, h w) ^ (2 * n) := by
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const, Finset.card_univ]
  ring

theorem key_bound (hcm : IsCMExt F E σ) {B : Base F E} {b : GL (Ix n) E} {K : Subgroup (G2 σ Y)} {a : G2 σ Y → ℝ}
    (h0 : ∃ t₀ : GL (Fin n) E, b.1.toCols₁ = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * (t₀.1 : Matrix (Fin n) (Fin n) E))
    (hK : IsStdK (σ := σ) (Y := Y) B b K) (ha : IsHgt K a) :
    ∃ C : ℝ≥0, ∀ (γ : G2 σ Y) (g : GL (Ix n) E),
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1 →
      ∀ f₀ : Fin n → Ix n, mnr (pl b g) f₀ ≠ 0 → ∀ x : G2 σ Y,
      a (γ * x) * (vecHt σ (fun f => mnr (pl b g) f / mnr (pl b g) f₀) : ℝ) ≤ C * (ht2 x : ℝ) ^ (2 * n) := by
  obtain ⟨t₀, h0⟩ := h0
  set bA := Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) b with hbA
  refine ⟨(n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n), ?_⟩
  intro γ g hγ f₀ hf₀ x
  obtain ⟨p, t, hp, k, hk, hy⟩ := ha.iwa (γ * x)
  have hval : a (γ * x) = absE F E (Matrix.GeneralLinearGroup.det t) := by rw [hy]; exact ha.val p t hp k hk
  set M := pl b g with hM
  set u : (Fin n → Ix n) → E := fun f => mnr M f / mnr M f₀ with hu
  have hu1 : u f₀ = 1 := div_self hf₀
  let c : Eˣ := Matrix.GeneralLinearGroup.det t₀ * Units.mk0 (mnr M f₀) hf₀
  let δ : (AE F E)ˣ := Matrix.GeneralLinearGroup.det t * Units.map (inclR (F := F) (AF F)).toMonoidHom c
  let X : GL (Ix n) (AE F E) := bA⁻¹ * x.1 * bA
  have hX : X.1 = inFrame b x := by
    have : (bA⁻¹).1 = incM F (b⁻¹).1 := by
      have : bA⁻¹ = Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) b⁻¹ := by rw [map_inv]
      rw [this]; rfl
    change (bA⁻¹).1 * x.1.1 * bA.1 = _
    rw [this]; rfl
  let κ := inFrame b k⁻¹
  let z : (Fin n → Ix n) → AE F E := fun f => ((X.1 * κ).submatrix f Sum.inl).det
  have hz : ∀ f, z f = inclR (F := F) (AF F) (u f) * δ.1 := by
    intro f
    have hid := frame_identity h0 hγ hp hy
    have e1 : z f = mnr ((inFrame b x * inFrame b k⁻¹).submatrix id Sum.inl) f := by
      change ((X.1 * κ).submatrix f Sum.inl).det = _
      rw [hX]; rfl
    have e2 : mnr (incM F M) f = inclR (F := F) (AF F) (mnr M f) := by
      rw [mnr, mnr, RingHom.map_det]; rfl
    have e3 : (t.1 * incM F t₀.1).det = (Matrix.GeneralLinearGroup.det t).1 * inclR (F := F) (AF F) t₀.1.det := by
      rw [Matrix.det_mul, incM, ← RingHom.mapMatrix_apply, ← RingHom.map_det]; rfl
    rw [e1, ← hid, mnr_mul_det, e2, e3]
    have e4 : mnr M f = u f * mnr M f₀ := by
      simp only [hu]; field_simp
    change _ = _ * ((Matrix.GeneralLinearGroup.det t).1 * inclR (F := F) (AF F) (t₀.1.det * mnr M f₀))
    rw [e4, map_mul, map_mul]
    ring
  have hδ : absE F E δ = absE F E (Matrix.GeneralLinearGroup.det t) := by
    simp only [δ, map_mul]
    rw [GlobalTheory.Doubling.absE_inclR, mul_one]
  have hmain := absE_mul_vecHt_le hcm B.emb hu1 δ z hz
    (fun w => (n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n)
    (fun v => htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n)
    ((finite_mulSupport_htFin F X).subset (Function.mulSupport_pow _ _))
    (fun w f => GlobalTheory.T.archimedean_minor_height_bound F E n (Ix n) w (B.emb w) X κ (((hK k⁻¹).1 (inv_mem hk)).1 w) f Sum.inl)
    (fun v f => GlobalTheory.T.finite_place_minor_height_bound F E n (Ix n) v X κ (fun i j => GlobalTheory.T.standard_compact_entries_integral F E σ n Y B b K hK _ (inv_mem hk) v i j) f Sum.inl)
  rw [hδ] at hmain
  have hprod : (∏ w, ((n.factorial : ℝ≥0) * htInf F w (Formalism.UG.bc (compInf F E w) X) ^ n) ^ 2) *
      ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 =
      (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * heightGL F X ^ (2 * n) := by
    have h1 : ∏ᶠ v, (htFin F v (Formalism.UG.bc (compFin F E v) X) ^ n) ^ 2 =
        (∏ᶠ v, htFin F v (Formalism.UG.bc (compFin F E v) X)) ^ (2 * n) := by
      rw [finprod_pow (finite_mulSupport_htFin F X)]
      simp only [← pow_mul, mul_comm]
    rw [exists_widePullback_of_iteratedLine, h1, heightGL, mul_pow]
    ring
  have hX2 : heightGL F X ≤ heightGL F bA ^ 2 * ht2 x := by
    calc heightGL F X ≤ heightGL F (bA⁻¹ * x.1) * heightGL F bA := heightGL_mul_le F _ _
      _ ≤ heightGL F bA⁻¹ * heightGL F x.1 * heightGL F bA := mul_le_mul_left (heightGL_mul_le F _ _) _
      _ = _ := by rw [heightGL_inv, ht2]; ring
  have hfin : absE F E (Matrix.GeneralLinearGroup.det t) * vecHt σ u ≤
      (n.factorial : ℝ≥0) ^ (2 * Fintype.card (InfinitePlace F)) * (heightGL F bA ^ 2) ^ (2 * n) * ht2 x ^ (2 * n) := by
    refine hmain.trans ?_
    rw [hprod, mul_assoc, ← mul_pow]
    exact mul_le_mul_right (pow_le_pow_left' hX2 _) _
  rw [hval]
  exact_mod_cast hfin

theorem isPar_of_pl {b g g' : GL (Ix n) E} {c : GL (Fin n) E} {γ γ' : G2 σ Y}
    (hγ : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = γ.1)
    (hγ' : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g' = γ'.1)
    (h : pl b g' = pl b g * c.1) :
    IsPar (γ * γ'⁻¹) (Matrix.GeneralLinearGroup.map (n := Fin n) (inclR (F := F) (E := E) (AF F)) c) := by
  have e1 : (g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (g⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1 := by
    have := congrArg (fun A => b.1 * A) h
    simpa [pl, ← Matrix.mul_assoc, ← Units.val_mul] using this
  have e2 : (g * g'⁻¹).1 * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) * c.1 := by
    rw [Units.val_mul, Matrix.mul_assoc, e1, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel]
    simp
  have e3 : mat2 (γ * γ'⁻¹) = incM F (g * g'⁻¹).1 := by
    have : Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) (g * g'⁻¹) = (γ * γ'⁻¹).1 := by
      rw [map_mul, map_inv, hγ, hγ']; rfl
    exact (congrArg Units.val this).symm
  have e4 := congrArg (incM F) e2
  rw [incM_mul, incM_mul, incM_diagCols] at e4
  unfold IsPar
  rw [e3]
  exact e4

end GlobalTheory.CompanionTheory.GodementH
end

noncomputable section
namespace GlobalTheory.CompanionTheory.GodementH

theorem godement_sum : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n : ℕ) (Y : Spc F E n) (r s : ℕ), B.IsGood σ → 1 ≤ n → (Y.IsHerm σ B r s ∨ Y.IsSkew σ B r s) → ∀ (b : GL (Fin n ⊕ Fin n) E) (K : Subgroup (G2 σ Y)) (a : G2 σ Y → ℝ), IsFrame2 σ Y b → IsStdK (σ := σ) (Y := Y) B b K → IsHgt K a → ∃ σ₀ : ℝ, ∀ σ' : ℝ, σ₀ < σ' → ∃ (C : ℝ) (N : ℕ), ∀ x : G2 σ Y, Summable (fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ σ') ∧ ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ σ' ≤ C * (ht2 x : ℝ) ^ N := by
  intro F E _ _ _ _ _ σ B n Y r s hB hn hY b K a hb hK ha
  have hcm : IsCMExt F E σ := hB.cm
  obtain ⟨C, hC⟩ := key_bound hcm hb.2 hK ha
  have hrat : ∀ q : Cos σ Y, ∃ g : GL (Ix n) E,
      Matrix.GeneralLinearGroup.map (n := Ix n) (inclR (F := F) (E := E) (AF F)) g = (Quotient.out q).1.1 := fun q => by
    obtain ⟨g, hg⟩ := Subgroup.mem_subgroupOf.1 (Quotient.out q).2
    exact ⟨g, hg⟩
  choose g hg using hrat
  have hnz : ∀ q, ∃ f, mnr (pl b (g q)) f ≠ 0 := fun q => by
    have hP : ∃ P : Matrix (Fin n) (Ix n) E, P * (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) = 1 :=
      ⟨Matrix.fromCols 1 0, by rw [diagCols, Matrix.fromCols_mul_fromRows]; simp⟩
    obtain ⟨P, hP⟩ := hP
    have hg1 : ((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hb1 : (b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1 = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    refine GlobalTheory.T.left_invertible_exists_nonzero_minor E (Ix n) n (pl b (g q)) ((P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E)) ?_
    calc (P * ((g q).1 : Matrix (Ix n) (Ix n) E)) * (b.1 : Matrix (Ix n) (Ix n) E) * pl b (g q)
        = P * ((g q).1 : Matrix (Ix n) (Ix n) E) * ((b.1 : Matrix (Ix n) (Ix n) E) * (b⁻¹).1) * ((g q)⁻¹).1 *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by simp only [pl, Matrix.mul_assoc]
      _ = P * (((g q).1 : Matrix (Ix n) (Ix n) E) * ((g q)⁻¹).1) *
          (diagCols (Fin n) : Matrix (Ix n) (Fin n) E) := by rw [hb1, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = 1 := by
        rw [hg1, Matrix.mul_one, hP]
  choose f₀ hf₀ using hnz
  let u : Cos σ Y → (Fin n → Ix n) → E := fun q f => mnr (pl b (g q)) f / mnr (pl b (g q)) (f₀ q)
  have hu1 : ∀ q, u q (f₀ q) = 1 := fun q => div_self (hf₀ q)
  have hinj : Function.Injective u := by
    intro q q' e
    obtain ⟨c, hc⟩ := GlobalTheory.T.plucker_minors_determine_column_space E (Ix n) n _ _ _ _ (hf₀ q) (hf₀ q') (fun f => congrFun e f)
    have hp := isPar_of_pl (hg q) (hg q') hc
    have : (Quotient.mk _ (Quotient.out q') : Cos σ Y) = Quotient.mk _ (Quotient.out q) :=
      cos_eq.2 (Subgroup.subset_closure ⟨_, hp⟩)
    rw [Quotient.out_eq, Quotient.out_eq] at this
    exact this.symm
  obtain ⟨C₁, c, hC₁, hcount⟩ := count hcm (Fin n → Ix n) (σ := σ)
  let h : Cos σ Y → ℝ := fun q => vecHt σ (u q)
  have h1 : ∀ q, 1 ≤ h q := fun q => by
    have := one_le_vecHt (σ := σ) (hu1 q)
    exact_mod_cast this
  have hcnt : ∀ T : ℝ, 1 ≤ T → {q | h q ≤ T}.Finite ∧ (Set.ncard {q | h q ≤ T} : ℝ) ≤ C₁ * T ^ c := by
    intro T hT
    obtain ⟨hfin, hle⟩ := hcount T hT
    have hmaps : Set.MapsTo u {q | h q ≤ T} {u : (Fin n → Ix n) → E | (∃ f₀, u f₀ = 1) ∧ (vecHt σ u : ℝ) ≤ T} :=
      fun q hq => ⟨⟨f₀ q, hu1 q⟩, hq⟩
    refine ⟨Set.Finite.of_injOn hmaps hinj.injOn hfin, le_trans ?_ hle⟩
    exact_mod_cast Set.ncard_le_ncard_of_injOn u hmaps hinj.injOn hfin
  have a_nonneg : ∀ y, 0 ≤ a y := fun y => by
    obtain ⟨p, t, hp, k, hk, rfl⟩ := ha.iwa y
    rw [ha.val p t hp k hk]; exact NNReal.coe_nonneg _
  refine ⟨c, fun s' hs' => ?_⟩
  have hs0 : 0 < s' := lt_of_le_of_lt (Nat.cast_nonneg c) hs'
  have hsum : Summable fun q => h q ^ (-s') := GlobalTheory.T.summable_height_pow_of_polynomial_count _ h h1 C₁ c hcnt s' hs'
  have hterm : ∀ (x : G2 σ Y) (q : Cos σ Y), a ((Quotient.out q).1 * x) ^ s' ≤
      ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') := by
    intro x q
    have hb1 := hC (Quotient.out q).1 (g q) (hg q) (f₀ q) (hf₀ q) x
    have hpos : 0 < h q := lt_of_lt_of_le one_pos (h1 q)
    have hb2 : a ((Quotient.out q).1 * x) ≤ ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hpos]; exact hb1
    calc _ ≤ (((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) * (h q)⁻¹) ^ s' := Real.rpow_le_rpow (a_nonneg _) hb2 hs0.le
      _ = _ := by
        rw [Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hpos.le, Real.rpow_neg hpos.le]
  refine ⟨(C : ℝ) ^ s' * ∑' q, h q ^ (-s'), ⌈2 * n * s'⌉₊, fun x => ?_⟩
  have hS : Summable fun q : Cos σ Y => a ((Quotient.out q).1 * x) ^ s' :=
    Summable.of_nonneg_of_le (fun q => Real.rpow_nonneg (a_nonneg _) _) (hterm x) (hsum.mul_left _)
  refine ⟨hS, ?_⟩
  have hx1 : (1 : ℝ) ≤ ht2 x := by exact_mod_cast one_le_heightGL F x.1
  have hx0 : (0 : ℝ) ≤ ht2 x := by positivity
  have hpow : ((ht2 x : ℝ) ^ (2 * n)) ^ s' ≤ (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0, ← Real.rpow_natCast]
    refine Real.rpow_le_rpow_of_exponent_le hx1 ?_
    push_cast
    exact Nat.le_ceil _
  have hT : 0 ≤ ∑' q, h q ^ (-s') := tsum_nonneg fun q => Real.rpow_nonneg (lt_of_lt_of_le one_pos (h1 q)).le _
  calc ∑' q : Cos σ Y, a ((Quotient.out q).1 * x) ^ s' ≤ ∑' q, ((C : ℝ) * (ht2 x : ℝ) ^ (2 * n)) ^ s' * h q ^ (-s') :=
        hS.tsum_le_tsum (hterm x) (hsum.mul_left _)
    _ = (C : ℝ) ^ s' * ((ht2 x : ℝ) ^ (2 * n)) ^ s' * ∑' q, h q ^ (-s') := by
        rw [tsum_mul_left, Real.mul_rpow (by positivity) (by positivity)]
    _ ≤ (C : ℝ) ^ s' * (ht2 x : ℝ) ^ ⌈2 * n * s'⌉₊ * ∑' q, h q ^ (-s') := by gcongr
    _ = _ := by ring

end GlobalTheory.CompanionTheory.GodementH
end
