import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSncModel
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.Proportional
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRed
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AdjoinCoordsArithVar
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularValuesInAdjoinedField
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StandardSmoothChartOfNonzero
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HomogeneousFormNonvanishingPoint

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap PSpace valR)
open ReciprocityTheory.ChartRestriction.G.Geo.ResK
open GlobalTheory.ProjSpace GlobalTheory.Points GlobalTheory.TuplePoint GlobalTheory.CompanionTheory.Ar.SncRes
attribute [local instance] MvPolynomial.gradedAlgebra
namespace GlobalTheory.CompanionTheory.Ar.Giv

theorem exists_point_of_hom {X : Scheme.{0}} {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) {F : Type} [Field F]
    (ψ : Γ(X, W₀) →+* F) : ∃ t ∈ W₀, ∀ a : Γ(X, W₀), t ∈ X.basicOpen a ↔ ψ a ≠ 0 := by
  let P : PrimeSpectrum Γ(X, W₀) := ⟨RingHom.ker ψ, RingHom.ker_isPrime ψ⟩
  refine ⟨hW₀.fromSpec P, ?_, fun a => ?_⟩
  · have := hW₀.range_fromSpec
    have h2 : hW₀.fromSpec P ∈ Set.range hW₀.fromSpec := ⟨P, rfl⟩
    rw [this] at h2
    exact h2
  · have h := hW₀.fromSpec_preimage_basicOpen a
    have h2 : hW₀.fromSpec P ∈ X.basicOpen a ↔ P ∈ hW₀.fromSpec ⁻¹ᵁ X.basicOpen a := Iff.rfl
    rw [h2, h]
    change a ∉ RingHom.ker ψ ↔ _
    rw [RingHom.mem_ker]

theorem exists_local_quot {Ω : Type} [Field Ω] [CharZero Ω] {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U))
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) {r : ℕ} (q : X' ⟶ PSpace ℚ r)
    (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (hq : ζ ≫ q = point ℚ x' hx') (t : X) (htU : t ∈ U) (htW : t ∈ W₀)
    (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) :
    ∃ l, x' l ≠ 0 ∧ ∃ b : Γ(X, W₀), t ∈ X.basicOpen b ∧
      ∀ i, ∃ a : Γ(X, W₀), x' i / x' l * valR ξ W₀ b = valR ξ W₀ a := by
  haveI : IsOpenImmersion ((f ⁻¹ᵁ U).ι ≫ f) := by
    rw [← morphismRestrict_ι]
    infer_instance
  have hr : Set.range ζ ⊆ Set.range (f ⁻¹ᵁ U).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨y, rfl⟩
    exact hU (Set.mem_univ y)
  let y : Sp Ω ⟶ (f ⁻¹ᵁ U).toScheme := IsOpenImmersion.lift (f ⁻¹ᵁ U).ι ζ hr
  have hy : y ≫ (f ⁻¹ᵁ U).ι = ζ := IsOpenImmersion.lift_fac _ _ _
  have hyr : y ≫ ((f ⁻¹ᵁ U).ι ≫ f) = ξ := by rw [← Category.assoc, hy, hζ]
  obtain ⟨t', ht'⟩ := (f ∣_ U).surjective ⟨t, htU⟩
  have ht'eq : ((f ⁻¹ᵁ U).ι ≫ f) t' = t := by
    rw [← morphismRestrict_ι]
    change U.ι ((f ∣_ U) t') = t
    rw [ht']
    rfl
  let φ : (f ⁻¹ᵁ U).toScheme ⟶ PSpace ℚ r := (f ⁻¹ᵁ U).ι ≫ q
  have hφ : y ≫ φ = point ℚ x' hx' := by
    simp only [φ]
    rw [← Category.assoc, hy, hq]
  obtain ⟨l, hl⟩ := exists_mem_chart ℚ r (φ t')
  let V : (f ⁻¹ᵁ U).toScheme.Opens := φ ⁻¹ᵁ chart ℚ r l
  let O : X.Opens := ((f ⁻¹ᵁ U).ι ≫ f) ''ᵁ V
  have htO : t ∈ O := ⟨t', hl, ht'eq⟩
  obtain ⟨b, hbO, htb⟩ := hW₀.exists_basicOpen_le (V := O) ⟨t, htO⟩ htW
  have hD : ⊤ ≤ ξ ⁻¹ᵁ X.basicOpen b := le_preimage_of_mem ξ htb
  have hyV : ⊤ ≤ y ⁻¹ᵁ V := fun u _ => by
    have h1 : ξ u ∈ O := hbO (hD (Set.mem_univ u))
    rw [← hyr] at h1
    have h2 := (((f ⁻¹ᵁ U).ι ≫ f).preimage_image_eq V).le h1
    exact h2
  have hl0 : x' l ≠ 0 := ne_zero_of_le hφ hyV le_rfl
  let s : Fin (r + 1) → Γ(X, O) := fun i => (((f ⁻¹ᵁ U).ι ≫ f).appIso V).inv.hom (pullRatio φ V l le_rfl i)
  have hs : ∀ i, valR ξ O (s i) = x' i / x' l := fun i => by
    have := valR_appIso_inv ((f ⁻¹ᵁ U).ι ≫ f) y V hyV (pullRatio φ V l le_rfl i)
    rw [hyr] at this
    rw [this]
    exact valR_pullRatio hφ hyV le_rfl i
  have hloc := hW₀.isLocalization_basicOpen b
  obtain ⟨⟨_, n, rfl⟩, hn⟩ := IsLocalization.exist_integer_multiples_of_finite (Submonoid.powers b)
    (fun i => (X.presheaf.map (homOfLE hbO).op).hom (s i))
  have hres : ∀ c : Γ(X, W₀), valR ξ (X.basicOpen b) (algebraMap Γ(X, W₀) Γ(X, X.basicOpen b) c) =
      valR ξ W₀ c := fun c => valR_res ξ (X.basicOpen_le b) hD c
  refine ⟨l, hl0, b ^ (n + 1), ?_, fun i => ?_⟩
  · rw [Scheme.basicOpen_pow _ _ n.succ_pos]
    exact htb
  · obtain ⟨a, ha⟩ := hn i
    refine ⟨a * b, ?_⟩
    have hv := congrArg (valR ξ (X.basicOpen b)) ha
    simp only [Algebra.smul_def] at hv
    rw [valR_mul ξ _ hD, hres, hres, valR_res ξ hbO hD, hs i] at hv
    rw [valR_mul ξ _ h₀, hv, pow_succ, valR_mul ξ _ h₀]
    ring

theorem local_of_hom {Ω : Type} [Field Ω] [CharZero Ω] {X X' : Scheme.{0}} (ξ : Sp Ω ⟶ X) [IsDominant ξ] (f : X' ⟶ X)
    (U : X.Opens) [IsIso (f ∣_ U)] (ζ : Sp Ω ⟶ X') (hζ : ζ ≫ f = ξ) (hU : ⊤ ≤ ζ ⁻¹ᵁ (f ⁻¹ᵁ U))
    {W₀ : X.Opens} (hW₀ : IsAffineOpen W₀) (h₀ : ⊤ ≤ ξ ⁻¹ᵁ W₀) (A : Subalgebra ℚ Ω)
    (hA : Set.range (valMap ξ W₀ h₀).hom = A) (σ₀ : Γ(X, W₀)) (hσ : X.basicOpen σ₀ = U) (g₀ : A)
    (hg : (g₀ : Ω) = valR ξ W₀ σ₀) {r : ℕ} (q : X' ⟶ PSpace ℚ r)
    (x' : Fin (r + 1) → Ω) (hx' : x' ≠ 0) (hq : ζ ≫ q = point ℚ x' hx') (ψ : A →+* ℂ) (hψ : ψ g₀ ≠ 0) :
    ∃ l, x' l ≠ 0 ∧ ∃ b : A, ψ b ≠ 0 ∧ ∀ i, ∃ a : A, x' i / x' l * (b : Ω) = a := by
  have hmem : ∀ a : Γ(X, W₀), valR ξ W₀ a ∈ A := fun a => by
    rw [valR_eq ξ W₀ h₀, ← SetLike.mem_coe, ← hA]
    exact ⟨a, rfl⟩
  let v : Γ(X, W₀) →+* A := (valMap ξ W₀ h₀).hom.codRestrict A fun a => by
    rw [← SetLike.mem_coe, ← hA]
    exact ⟨a, rfl⟩
  have hv : ∀ a, ((v a : A) : Ω) = valR ξ W₀ a := fun a => (valR_eq ξ W₀ h₀ a).symm
  obtain ⟨t, htW, ht⟩ := exists_point_of_hom hW₀ (ψ.comp v)
  have hvσ : v σ₀ = g₀ := Subtype.ext (by rw [hv, hg])
  have htU : t ∈ U := by
    rw [← hσ, ht]
    simpa [hvσ] using hψ
  obtain ⟨l, hl, b, hb, hi⟩ := exists_local_quot ξ f U ζ hζ hU hW₀ q x' hx' hq t htU htW h₀
  refine ⟨l, hl, v b, (ht b).1 hb, fun i => ?_⟩
  obtain ⟨a, ha⟩ := hi i
  exact ⟨v a, by rw [hv, hv, ha]⟩

theorem exists_homog_poly {σ : Type} (c₀ : σ) (P : MvPolynomial σ ℚ) :
    ∃ (m : ℤ) (n : ℕ) (H : MvPolynomial σ ℤ), m ≠ 0 ∧ H.IsHomogeneous n ∧
      ∀ (R : Type) [Field R] [CharZero R] (v : σ → R), v c₀ = 1 → aeval v H = (m : R) * aeval v P := by
  induction P using MvPolynomial.induction_on with
  | C q =>
    refine ⟨q.den, 0, C q.num, by exact_mod_cast q.den_nz, isHomogeneous_C _ _, fun R _ _ v _ => ?_⟩
    have hd : (q.den : R) ≠ 0 := by exact_mod_cast q.den_nz
    simp only [algHom_C, algebraMap_eq, eq_intCast, eq_ratCast, Int.cast_natCast, map_intCast]
    rw [Rat.cast_def]
    field_simp
  | add P Q ihP ihQ =>
    obtain ⟨m₁, n₁, G₁, hm₁, hG₁, e₁⟩ := ihP
    obtain ⟨m₂, n₂, G₂, hm₂, hG₂, e₂⟩ := ihQ
    refine ⟨m₁ * m₂, n₁ + n₂, C m₂ * X c₀ ^ n₂ * G₁ + C m₁ * X c₀ ^ n₁ * G₂, mul_ne_zero hm₁ hm₂, ?_,
      fun R _ _ v hv => ?_⟩
    · refine MvPolynomial.IsHomogeneous.add ?_ ?_
      · have := ((isHomogeneous_C σ m₂).mul ((isHomogeneous_X ℤ c₀).pow n₂)).mul hG₁
        convert this using 1
        ring
      · have := ((isHomogeneous_C σ m₁).mul ((isHomogeneous_X ℤ c₀).pow n₁)).mul hG₂
        convert this using 1
        ring
    · simp only [map_add, map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, e₁ R v hv,
        e₂ R v hv]
      push_cast
      ring
  | mul_X P i ih =>
    obtain ⟨m, n, G, hm, hG, e⟩ := ih
    refine ⟨m, n + 1, G * X i, hm, hG.mul (isHomogeneous_X ℤ i), fun R _ _ v hv => ?_⟩
    simp only [map_mul, aeval_X, e R v hv]
    ring

theorem exists_homog_family {σ κ : Type} [Fintype κ] (c₀ : σ) (P : κ → MvPolynomial σ ℚ) :
    ∃ (m : ℤ) (n : ℕ) (H : κ → MvPolynomial σ ℤ), m ≠ 0 ∧ (∀ i, (H i).IsHomogeneous n) ∧
      ∀ (R : Type) [Field R] [CharZero R] (v : σ → R), v c₀ = 1 →
        ∀ i, aeval v (H i) = (m : R) * aeval v (P i) := by
  classical
  choose m₀ n₀ H₀ h1 h2 h3 using fun i => exists_homog_poly c₀ (P i)
  refine ⟨∏ i, m₀ i, ∑ i, n₀ i, fun i => C (∏ j ∈ Finset.univ.erase i, m₀ j) * X c₀ ^ (∑ j, n₀ j - n₀ i) * H₀ i,
    Finset.prod_ne_zero_iff.2 fun i _ => h1 i, fun i => ?_, fun R _ _ v hv i => ?_⟩
  · have hle : n₀ i ≤ ∑ j, n₀ j := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    have := ((isHomogeneous_C σ (∏ j ∈ Finset.univ.erase i, m₀ j)).mul
      ((isHomogeneous_X ℤ c₀).pow (∑ j, n₀ j - n₀ i))).mul (h2 i)
    convert this using 1
    omega
  · have e : (∏ j, m₀ j) = (∏ j ∈ Finset.univ.erase i, m₀ j) * m₀ i :=
      (Finset.prod_erase_mul _ _ (Finset.mem_univ i)).symm
    simp only [map_mul, map_pow, aeval_X, hv, one_pow, mul_one, eq_intCast, map_intCast, h3 i R v hv, e]
    push_cast
    ring

theorem exists_adjoin_hom {σ Ω : Type} [Field Ω] [CharZero Ω] (r : σ → Ω) (w : σ → ℂ)
    (hker : ∀ P : MvPolynomial σ ℚ, aeval r P = 0 → aeval w P = 0) :
    ∃ ψ : Algebra.adjoin ℚ (Set.range r) →+* ℂ, ∀ (P : MvPolynomial σ ℚ) (t : Algebra.adjoin ℚ (Set.range r)),
      (t : Ω) = aeval r P → ψ t = aeval w P := by
  let f : MvPolynomial σ ℚ →ₐ[ℚ] Algebra.adjoin ℚ (Set.range r) :=
    aeval fun j => ⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩
  have hcoe : ∀ P, ((f P : Algebra.adjoin ℚ (Set.range r)) : Ω) = aeval r P := fun P => by
    have := comp_aeval_apply (R := ℚ) (fun j => (⟨r j, Algebra.subset_adjoin ⟨j, rfl⟩⟩ : Algebra.adjoin ℚ (Set.range r)))
      (Algebra.adjoin ℚ (Set.range r)).val P
    simpa [f] using this
  have hf : Function.Surjective f := by
    rintro ⟨t, ht⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at ht
    obtain ⟨P, rfl⟩ := ht
    exact ⟨P, Subtype.ext (hcoe P)⟩
  have hle : RingHom.ker f.toRingHom ≤ RingHom.ker (aeval w : MvPolynomial σ ℚ →ₐ[ℚ] ℂ).toRingHom := by
    intro P hP
    have h0 : f P = 0 := hP
    have h1 : aeval r P = 0 := by rw [← hcoe, h0]; rfl
    exact hker P h1
  let ψ := f.toRingHom.liftOfSurjective hf ⟨_, hle⟩
  refine ⟨ψ, fun P t ht => ?_⟩
  have e : t = f P := Subtype.ext (by rw [ht, hcoe])
  rw [e]
  exact RingHom.liftOfRightInverse_comp_apply _ _ _ _ P

theorem snc_of_res_local {Ω : Type} [Field Ω] [CharZero Ω] (hR : ResKStatement) (N e d : ℕ) (x : Fin (N + 1) → Ω)
    (c₀ : Fin (N + 1)) (hc₀ : x c₀ ≠ 0)
    (G : MvPolynomial (Fin (N + 1)) ℚ) (hG : G.IsHomogeneous (d + 1)) (hdiv : (X c₀ : MvPolynomial _ ℚ) ∣ G)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀))
    (hg₀ : (g₀ : Ω) = aeval (fun j => x j / x c₀) G) (h0 : g₀ ≠ 0)
    [Algebra.IsStandardSmoothOfRelativeDimension e ℚ (Localization.Away g₀)] :
    ∃ (r : ℕ) (x' : Fin (r + 1) → Ω), x' ≠ 0 ∧
      (∀ i l, x' l ≠ 0 → x' i / x' l ∈
        IntermediateField.adjoin ℚ ((Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) : Subalgebra ℚ Ω) : Set Ω)) ∧
      (∀ a l, x a ≠ 0 → x' l ≠ 0 →
        SncChart (Algebra.adjoin ℚ (Set.range (fun k => x k / x a) ∪ Set.range (fun k => x' k / x' l))) e
          (aeval (fun j => x j / x a) G)) ∧
      ∀ ψ : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀) →+* ℂ, ψ g₀ ≠ 0 →
        ∃ l, x' l ≠ 0 ∧ ∃ b : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀), ψ b ≠ 0 ∧
          ∀ i, ∃ a : Algebra.adjoin ℚ (Set.range fun j => x j / x c₀), x' i / x' l * (b : Ω) = a := by
  have hx : x ≠ 0 := fun h => hc₀ (by simp [h])
  obtain ⟨hred, hdom⟩ := closure_facts x hx
  set p := point ℚ x hx with hp
  have hπ : p.toImage ≫ p.imageι = point ℚ x hx := Scheme.Hom.toImage_imageι p
  obtain ⟨hW₀, h₀, hA₀⟩ := chart_single p.imageι p.toImage x hx hπ c₀ hc₀
  obtain ⟨σ₀, hσ₀, hb₀⟩ := form_section p.imageι p.toImage x hx hπ h₀ le_rfl hG
  have hsub : Proj.basicOpen (grading ℚ N) G ≤ chart ℚ N c₀ := by
    obtain ⟨G', rfl⟩ := hdiv
    rw [Proj.basicOpen_mul]
    exact inf_le_left
  set U : (p.image).Opens := p.imageι ⁻¹ᵁ Proj.basicOpen (grading ℚ N) G with hUdef
  have hUb : p.image.basicOpen σ₀ = U := by
    rw [hb₀]
    exact inf_eq_right.2 (p.imageι.preimage_mono hsub)
  have hval : valR p.toImage _ σ₀ = g₀ := by rw [hσ₀, hg₀]
  have hUtop : ⊤ ≤ p.toImage ⁻¹ᵁ U := by
    rw [← hUb, le_preimage_basicOpen_iff _ h₀, hval]
    exact isUnit_iff_ne_zero.2 (by simpa using h0)
  have hsmU : SmoothOfRelativeDimension e (U.ι ≫ p.imageι ≫ PSpace.str ℚ N) := by
    have := smooth_basicOpen p.toImage (p.imageι ≫ PSpace.str ℚ N) e hW₀ h₀ _ hA₀ σ₀ g₀ hval.symm
    rwa [hUb] at this
  have hdense : Dense (U : Set p.image) := by
    refine p.toImage.denseRange.mono ?_
    rintro _ ⟨y, rfl⟩
    exact hUtop (Set.mem_univ y)
  obtain ⟨r, X', j, f, hj, hf, hsm, hiso, hd, hco⟩ := hR ℚ N e p.image p.imageι U ⟨inferInstance, hred, hdense, hsmU⟩
  obtain ⟨ζ, hζ, hdomζ, hζU⟩ := lift_generic p.toImage f U hd hUtop
  obtain ⟨x', hx', hp₂⟩ := exists_coords (ζ ≫ j ≫ pullback.snd _ _)
  have hp₁ : ζ ≫ j ≫ pullback.fst _ _ = point ℚ x hx := by
    rw [← hf, reassoc_of% hζ, hπ]
  have : Smooth (f ≫ p.imageι ≫ PSpace.str ℚ N) := hsm.smooth
  have hredX' : IsReduced X' := GlobalTheory.isReduced_of_smooth_of_isReduced (f ≫ p.imageι ≫ PSpace.str ℚ N)
  refine ⟨r, x', hx', fun i l hl => ?_, fun a l ha hl => ?_, fun ψ hψ => ?_⟩
  · have hW : ⊤ ≤ ζ ⁻¹ᵁ ((j ≫ pullback.snd _ _) ⁻¹ᵁ chart ℚ r l) := le_preimage_chart (by simpa using hp₂) hl
    have := val_mem_field p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ _ hW
      (pullRatio (j ≫ pullback.snd _ _) _ l le_rfl i)
    rwa [valR_pullRatio (by simpa using hp₂) hW] at this
  · obtain ⟨hWa, hW, hAW⟩ := prod_chart j ζ x hx x' hx' hp₁ hp₂ a l ha hl
    obtain ⟨σ, hσ, hb⟩ := form_section (j ≫ pullback.fst _ _) ζ x hx (by simpa using hp₁) hW inf_le_left hG
    rw [← hσ]
    refine snc_transfer ζ (f ≫ p.imageι ≫ PSpace.str ℚ N) e _ hsm hco hWa hW _ hAW σ fun t ht => ?_
    rw [hb]
    have e₁ : (j ≫ pullback.fst _ _) t = p.imageι (f t) := by
      rw [← hf]
      rfl
    constructor
    · rintro h ⟨-, h2⟩
      exact h (show p.imageι (f t) ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2)
    · intro h h2
      exact h ⟨ht, show (j ≫ pullback.fst _ _) t ∈ Proj.basicOpen (grading ℚ N) G from e₁ ▸ h2⟩
  · exact local_of_hom p.toImage f U ζ hζ hζU hW₀ h₀ _ hA₀ σ₀ hUb g₀ hval.symm (j ≫ pullback.snd _ _) x' hx' hp₂ ψ hψ

section Top
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P GlobalTheory.CompanionTheory.Ar.Cmp GlobalTheory.CompanionTheory.Ar.PB Filter Topology
open GlobalTheory.CompanionTheory.Ar.SegreChart (segForm aeval_segForm segForm_multiHomog)
open GlobalTheory.CompanionTheory.Ar.SncRes.SegreForm (aeval_const_mul)

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]

theorem seg_eq_mul {F : Type} [Field F] (v : (Σ k, ι k) → F) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k))
    (c₀ : Fin (N + 1)) (h0 : (∏ k, v ⟨k, E c₀ k⟩) ≠ 0) :
    (fun j => ∏ k, v ⟨k, E j k⟩) =
      fun j => (∏ k, v ⟨k, E c₀ k⟩) * ((∏ k, v ⟨k, E j k⟩) / ∏ k, v ⟨k, E c₀ k⟩) :=
  funext fun j => (mul_div_cancel₀ _ h0).symm

theorem ker_ratio (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y))
    (hz0 : (∏ k, z ⟨k, E c₀ k⟩) ≠ 0) (P : MvPolynomial (Fin (N + 1)) ℚ)
    (hP : aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) P = 0) :
    aeval (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) P = 0 := by
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  obtain ⟨m, n, H, hm, hH, e⟩ := exists_homog_poly c₀ P
  have e₁ := e Ω (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) (div_self h0)
  have e₂ := e ℂ (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (div_self hz0)
  rw [hP, mul_zero] at e₁
  have hy : aeval y (segForm E H) = 0 := by
    rw [aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul hH, e₁, mul_zero]
  have hmem : segForm E H ∈ mCoordIdeal y := (form_mem_mCoordIdeal_iff y (segForm_multiHomog E hH)).2 hy
  have hZ := hz.2 _ hmem
  rw [GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul hH] at hZ
  have h2 := (mul_eq_zero.1 hZ).resolve_left (pow_ne_zero _ hz0)
  rw [e₂] at h2
  exact (mul_eq_zero.1 h2).resolve_left (by exact_mod_cast hm)

theorem exists_forms (y : (Σ k, ι k) → Ω) {N : ℕ} (E : Fin (N + 1) ≃ ((k : K) → ι k)) (c₀ : Fin (N + 1))
    (hc : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0) (d : ℕ) (Gz : MvPolynomial (Fin (N + 1)) ℤ) (hG : Gz.IsHomogeneous (d + 1))
    (hdiv : (X c₀ : MvPolynomial _ ℤ) ∣ Gz)
    (g₀ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩))
    (hg₀ : (g₀ : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) Gz) {M : ℕ} (x' : Fin M → Ω)
    (hloc : ∀ ψ : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) →+* ℂ, ψ g₀ ≠ 0 →
      ∃ l, x' l ≠ 0 ∧ ∃ b : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩), ψ b ≠ 0 ∧
        ∀ i, ∃ a : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩),
          x' i / x' l * (b : Ω) = a)
    {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal y)) (hne : evC z (segForm E Gz) ≠ 0) :
    ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧
      (∀ i j, x' i * aeval y (G j) = x' j * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0 := by
  classical
  have h0 : (∏ k, y ⟨k, E c₀ k⟩) ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hc k
  have hZne : aeval (fun j => ∏ k, z ⟨k, E j k⟩) Gz ≠ 0 := by
    rwa [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm] at hne
  have hz0 : (∏ k, z ⟨k, E c₀ k⟩) ≠ 0 := by
    obtain ⟨G', rfl⟩ := hdiv
    intro h
    apply hZne
    rw [map_mul, aeval_X, h, zero_mul]
  obtain ⟨ψ, hψ⟩ := exists_adjoin_hom (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩)
    (fun j => (∏ k, z ⟨k, E j k⟩) / ∏ k, z ⟨k, E c₀ k⟩) (fun P hP => ker_ratio y E c₀ hc hz hz0 P hP)
  have hψg : ψ g₀ ≠ 0 := by
    rw [hψ (map (algebraMap ℤ ℚ) Gz) g₀ (by rw [hg₀, aeval_map_algebraMap]), aeval_map_algebraMap]
    intro h
    apply hZne
    rw [seg_eq_mul z E c₀ hz0, aeval_const_mul hG, h, mul_zero]
  obtain ⟨l, hl, b, hb, hi⟩ := hloc ψ hψg
  choose a ha using hi
  have hsurj : ∀ t : Algebra.adjoin ℚ (Set.range fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩),
      ∃ P : MvPolynomial (Fin (N + 1)) ℚ, (t : Ω) = aeval (fun j => (∏ k, y ⟨k, E j k⟩) / ∏ k, y ⟨k, E c₀ k⟩) P := by
    rintro ⟨t, ht⟩
    rw [Algebra.adjoin_range_eq_range_aeval] at ht
    obtain ⟨P, rfl⟩ := ht
    exact ⟨P, rfl⟩
  choose P hP using hsurj
  obtain ⟨m, n, H, hm, hH, e⟩ := exists_homog_family c₀ (fun i => P (a i))
  have hv : ∀ i, aeval y (segForm E (H i)) =
      (∏ k, y ⟨k, E c₀ k⟩) ^ n * ((m : Ω) * (x' i / x' l * (b : Ω))) := fun i => by
    rw [aeval_segForm, seg_eq_mul y E c₀ h0, aeval_const_mul (hH i), e Ω _ (div_self h0) i, ← hP, ← ha i]
  refine ⟨fun i => segForm E (H i), fun _ => n, fun i => segForm_multiHomog E (hH i), fun i j => ?_, l, ?_⟩
  · simp only [hv]
    field_simp
  · have hal : a l = b := Subtype.ext (by rw [← ha l, div_self hl, one_mul])
    have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
    rw [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm, seg_eq_mul z E c₀ hz0, aeval_const_mul (hH l),
      e ℂ _ (div_self hz0) l, ← hψ _ (a l) (hP _), hal]
    exact mul_ne_zero (pow_ne_zero _ hz0) (mul_ne_zero hm' hb)

theorem exists_snc_model_iso : ReciprocityTheory.ChartRestriction.G.Geo.ResK.ResKStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (β : MRing ι) (b : K → ℕ), IsArithVar (mCoordIdeal y) (e + 1) → IsMultiHomog β b → β ∉ mCoordIdeal y → ∃ (β' : MRing ι) (b' : K → ℕ) (M : ℕ) (y' : (Σ _ : Unit, Fin M) → Ω) (J : Ideal (MRing (joinIdx ι fun _ : Unit => Fin M))), IsMultiHomog β' b' ∧ β' ∉ mCoordIdeal y ∧ (∀ z ∈ mcPts (mCoordIdeal y), evC z β = 0 → evC z β' = 0) ∧ (∃ i, y' ⟨(), i⟩ ≠ 0) ∧ blockFnField (joinVec y y') = blockFnField y ∧ IsMultiHomogIdeal J ∧ ¬ J ≤ mCoordIdeal (joinVec y y') ∧ IsSncModel (joinVec y y') e J ∧ (∀ z ∈ mcPts (mCoordIdeal (joinVec y y')), evC z (rename (joinInl ι fun _ : Unit => Fin M) β') = 0 → z ∈ mcPts J) ∧ ∀ z ∈ mcPts (mCoordIdeal y), evC z β' ≠ 0 → ∃ (G : Fin M → MRing ι) (g : K → ℕ), (∀ i, IsMultiHomog (G i) g) ∧ (∀ i j, y' ⟨(), i⟩ * aeval y (G j) = y' ⟨(), j⟩ * aeval y (G i)) ∧ ∃ i, evC z (G i) ≠ 0 := by
  intro hR K _ ι _ Ω _ _ y e β b hA hb hβ
  classical
  obtain ⟨-, ⟨-, -, hrel⟩, -, -⟩ := id hA
  choose c hc using hrel
  have hc' : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k h0 => hc k (by
    rw [mCoordIdeal, RingHom.mem_ker, mConeMap, aeval_X, h0, C_0, zero_mul])
  have : Nonempty ((k : K) → ι k) := ⟨c⟩
  obtain ⟨N, hN⟩ : ∃ N, Fintype.card ((k : K) → ι k) = N + 1 :=
    Nat.exists_eq_succ_of_ne_zero Fintype.card_ne_zero
  let E : Fin (N + 1) ≃ ((k : K) → ι k) := (Fintype.equivFinOfCardEq hN).symm
  let c₀ := E.symm c
  have hE : ∀ k, y ⟨k, E c₀ k⟩ ≠ 0 := fun k => by simpa [c₀] using hc' k
  obtain ⟨s, hs, hsm⟩ := exists_smooth y e hA N E c₀ hE
  obtain ⟨d, Gz, g₀, hG, hdiv, hg₀, hg0, hsm₀, hz⟩ := exists_form y e β b hb hβ N E c₀ hE s hs
  let x : Fin (N + 1) → Ω := fun j => ∏ k, y ⟨k, E j k⟩
  have hx₀ : x c₀ ≠ 0 := Finset.prod_ne_zero_iff.2 fun k _ => hE k
  let G := map (algebraMap ℤ ℚ) Gz
  obtain ⟨r, x', hx', hF, hch, hloc⟩ := snc_of_res_local hR N e d x c₀ hx₀ G (hG.map _)
    (by simpa [G] using map_dvd (MvPolynomial.map (algebraMap ℤ ℚ)) hdiv) g₀
    (by rw [hg₀]; exact (aeval_map_algebraMap ℚ _ _).symm) hg0
  have h0 : aeval (fun j => ∏ k, y ⟨k, E j k⟩) Gz ≠ 0 := by
    intro h
    have h1 : aeval (fun j => x j / x c₀) Gz = 0 := by
      simp only [div_eq_inv_mul]
      rw [GlobalTheory.CompanionTheory.Ar.ProjCoord.aeval_mul_of_isHomogeneous x _ hG]
      exact mul_eq_zero_of_right _ h
    exact hg0 (Subtype.ext (hg₀.trans h1))
  have hmem : rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz) ∈
      Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)} :=
    Ideal.subset_span rfl
  have hev : ∀ z : (Σ k, ι k) → ℂ, evC z (segForm E Gz) =
      eval (fun j => ∏ k, z ⟨k, E j k⟩) (map (Int.castRingHom ℂ) Gz) := fun z => by
    rw [evC, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, GlobalTheory.CompanionTheory.Ar.SegreChart.eval_map_int, aeval_segForm]
  refine ⟨segForm E Gz, fun _ => d + 1, r + 1, fun p => x' p.2,
    Ideal.span {rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, segForm_multiHomog E hG, ?_,
    fun z hz' hb' => (hev z).trans (hz z hz' hb'), ?_,
    GlobalTheory.CompanionTheory.Ar.SegreChart.blockFnField_joinPt y x' fun i l hl => adjoin_seg_le y N E c₀ hE (hF i l hl), ?_, ?_,
    GlobalTheory.CompanionTheory.Ar.SegreChart.isSncModel_joinPt y x' e E Gz fun a l ha hl => hch a l ha hl,
    fun z hz' hb' => GlobalTheory.CompanionTheory.Ar.SegreChart.mem_mcPts_span y x' (segForm E Gz) E Gz
      (fun w _ hw => (hev w).symm.trans hw) z hz' hb',
    fun z hz' hne => exists_forms y E c₀ hE d Gz hG hdiv g₀ hg₀ x' hloc hz' hne⟩
  · intro hin
    have h1 := GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem y hin
    rw [aeval_segForm] at h1
    exact h0 h1
  · obtain ⟨i, hi⟩ := Function.ne_iff.1 hx'
    exact ⟨i, hi⟩
  · refine ⟨{rename (joinInl ι fun _ : Unit => Fin (r + 1)) (segForm E Gz)}, ?_, rfl⟩
    rintro f rfl
    exact ⟨_, GlobalTheory.CompanionTheory.Ar.SegreChart.multiHomog_rename_inl (segForm_multiHomog E hG)⟩
  · intro hle
    have h1 := GlobalTheory.CompanionTheory.Ar.SegreChart.aeval_eq_zero_of_mem _ (hle hmem)
    rw [aeval_rename, GlobalTheory.CompanionTheory.Ar.SegreChart.joinVec_comp_inl, aeval_segForm] at h1
    exact h0 h1
end Top

end GlobalTheory.CompanionTheory.Ar.Giv
