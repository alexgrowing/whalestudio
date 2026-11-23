import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.CompactIntegralFields.RedTan
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.SpaceMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDim
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

private theorem lifts_map {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] {Φ : Fr O Γ} {Λ : Type} [CommRing Λ]
    [IsLocalRing Λ] {a : O →+* Λ} {c : PD Φ.ι Γ (ResidueField Λ)} {R R' : Type} [CommRing R] [Algebra Λ R] [IsCO Λ R]
    [CommRing R'] [Algebra Λ R'] [IsCO Λ R'] {P : PD Φ.ι Γ R} (h : Φ.Lifts a c P) (f : R →ₐ[Λ] R') :
    Φ.Lifts a c (P.map (f : R →+* R')) := by
  refine ⟨?_, h.cont.map _ fun y hy => ?_, ?_⟩
  · have h1 := h.pair.map (f : R →+* R')
    rwa [← RingHom.comp_assoc, AlgHom.comp_algebraMap] at h1
  · show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff Λ, res_map, res_eq_zero_iff]
    exact hy
  · rw [PD.map_map, ← h.red]
    congr 1
    exact RingHom.ext fun x => res_map f x

private theorem lc_dual {Γ k : Type} [TopologicalSpace Γ] [Field k] {f : Γ → DualNumber k}
    (h : AdicCont (maximalIdeal (DualNumber k)) f) : IsLocallyConstant f := by
  have hm : ∀ x ∈ maximalIdeal (DualNumber k), x.fst = 0 := by
    intro x hx
    by_contra hne
    exact hx ((TrivSqZeroExt.isUnit_iff_isUnit_fst).mpr (isUnit_iff_ne_zero.mpr hne))
  have h2 : maximalIdeal (DualNumber k) ^ 2 = ⊥ := by
    rw [pow_two, eq_bot_iff]
    intro z hz
    refine Submodule.mul_induction_on hz ?_ ?_
    · intro x hx y hy
      rw [Ideal.mem_bot]
      ext <;> simp [hm x hx, hm y hy]
    · intro a b ha hb
      exact add_mem ha hb
  refine IsLocallyConstant.desc f (Ideal.Quotient.mk _) (h 2) ?_
  intro u v huv
  have := Ideal.Quotient.eq.mp huv
  rw [h2, Ideal.mem_bot, sub_eq_zero] at this
  exact this

private theorem hom_of_der {O A k : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing k] [Algebra O k]
    (x : A →ₐ[O] k) (D : A →ₗ[O] k) (hD : D ∈ PtDer x k) :
    ∃ y : A →ₐ[O] DualNumber k, ∀ f, (y f).fst = x f ∧ (y f).snd = D f := by
  have hD' : ∀ f g, D (f * g) = x f * D g + x g * D f := hD
  have hD1 : D 1 = 0 := by
    have := hD' 1 1
    simp only [mul_one, map_one, one_mul] at this
    linear_combination -this
  let m : A → DualNumber k := fun f => TrivSqZeroExt.inl (x f) + TrivSqZeroExt.inr (D f)
  have mf : ∀ f, (m f).fst = x f := fun f => by simp [m]
  have ms : ∀ f, (m f).snd = D f := fun f => by simp [m]
  have e1 : m 1 = 1 := by
    ext <;> simp [mf, ms, hD1]
  have e2 : ∀ f g : A, m (f * g) = m f * m g := by
    intro f g
    ext
    · simp [mf]
    · simp only [ms, TrivSqZeroExt.snd_mul, mf, hD', smul_eq_mul, MulOpposite.smul_eq_mul_unop,
        MulOpposite.unop_op]
      ring
  have e3 : m 0 = 0 := by
    ext <;> simp [mf, ms]
  have e4 : ∀ f g : A, m (f + g) = m f + m g := by
    intro f g
    ext <;> simp [mf, ms]
  have e5 : ∀ r : O, m (algebraMap O A r) = algebraMap O (DualNumber k) r := by
    intro r
    have hDa : D (algebraMap O A r) = 0 := by
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hD1, smul_zero]
    ext
    · rw [mf, AlgHom.commutes, Algebra.algebraMap_eq_smul_one r, Algebra.algebraMap_eq_smul_one r]
      simp
    · rw [ms, hDa, Algebra.algebraMap_eq_smul_one r]
      simp
  exact ⟨{ toFun := m, map_one' := e1, map_mul' := e2, map_zero' := e3, map_add' := e4, commutes' := e5 }, fun f => ⟨mf f, ms f⟩⟩

theorem UpperTheory.V.Ws.red :
    ∀ {O Γ : Type} [CommRing O] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ] (Φ : Fr O Γ) (l : ℕ) [Fact l.Prime] {Λ : Type} [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [IsAdicComplete (maximalIdeal Λ) Λ] [Finite (ResidueField Λ)] (a : O →+* Λ), Φ.Std l a → ∀ d C : ℕ, Φ.Bounds ((residue Λ).comp a) d C → ∀ c : PD Φ.ι Γ (ResidueField Λ), Φ.IsRes ((residue Λ).comp a) c → Φ.Good ((residue Λ).comp a) c →
      ∀ (R : Type) [CommRing R] [Algebra Λ R] [IsCO Λ R] (P : PD Φ.ι Γ R), Φ.IsDef a c P → ∀ S ∈ redTypes, ringKrullDim (R ⧸ redIdeal S P.r) ≤ (d + 20 * C + 1 : ℕ) := by
  intro O Γ _ _ _ _ _ _ Φ l _ Λ _ _ _ _ _ a hstd d C hB c hRes hGood R _ _ _ P hDef S hS
  by_cases hI : redIdeal S P.r = ⊤
  · haveI : Subsingleton (R ⧸ redIdeal S P.r) := Ideal.Quotient.subsingleton_iff.mpr hI
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  set I := redIdeal S P.r with hIdef
  haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI
  haveI hco : IsCO Λ (R ⧸ I) :=
    co_quot Λ R (R ⧸ I) (Ideal.Quotient.mkₐ Λ I) (Ideal.Quotient.mkₐ_surjective Λ I)
  haveI hcoD : IsCO Λ (DualNumber (ResidueField Λ)) := (co_res Λ).2
  have hIm : I ≤ maximalIdeal R := IsLocalRing.le_maximalIdeal hI
  have hlift := hDef.1
  have hcr : ∀ g i j, c.r g i j = res Λ R (P.r g i j) := by
    intro g i j
    rw [← hlift.red]
    rfl
  have hcn : ∀ v i j, c.n v i j = res Λ R (P.n v i j) := by
    intro v i j
    rw [← hlift.red]
    rfl
  have hsupp : ∀ g i j, i ≠ j → wt i j ∉ S → P.r g i j ∈ I :=
    fun g i j hij hw => Ideal.subset_span ⟨g, i, j, hij, hw, rfl⟩
  have hSc : Supp S c.r := by
    intro g i j hij hw
    rw [hcr, res_eq_zero_iff]
    exact hIm (hsupp g i j hij hw)
  have hrank := redTan Φ ((residue Λ).comp a) hstd.ok d C hB c hRes hGood S hS hSc
  have hder : ∀ D : PtDer (res Λ (R ⧸ I)) (ResidueField Λ),
      ∃ g : R →ₐ[Λ] DualNumber (ResidueField Λ), ∀ x, (g x).fst = res Λ R x ∧
        (g x).snd = (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I x) := by
    intro D
    obtain ⟨y, hy⟩ := hom_of_der (res Λ (R ⧸ I)) (D : R ⧸ I →ₗ[Λ] ResidueField Λ) D.2
    refine ⟨y.comp (Ideal.Quotient.mkₐ Λ I), fun x => ⟨?_, ?_⟩⟩
    · rw [AlgHom.comp_apply, (hy _).1]
      exact res_map (Ideal.Quotient.mkₐ Λ I) x
    · rw [AlgHom.comp_apply, (hy _).2]
      rfl
  let tv : (R ⧸ I →ₗ[Λ] ResidueField Λ) → (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ)) :=
    fun D => (fun g => Matrix.map (P.r g) (fun x => D (Ideal.Quotient.mk I x)) * c.r g⁻¹,
      fun v => Matrix.map (P.n v) (fun x => D (Ideal.Quotient.mk I x)) * adj (c.n v))
  have tv_add : ∀ D1 D2, tv (D1 + D2) = tv D1 + tv D2 := by
    intro D1 D2
    refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · show Matrix.map (P.r g) (fun x => (D1 + D2) (Ideal.Quotient.mk I x)) * c.r g⁻¹ =
        Matrix.map (P.r g) (fun x => D1 (Ideal.Quotient.mk I x)) * c.r g⁻¹ +
          Matrix.map (P.r g) (fun x => D2 (Ideal.Quotient.mk I x)) * c.r g⁻¹
      rw [← Matrix.add_mul]
      congr 1
      all_goals (ext i j; simp)
    · show Matrix.map (P.n v) (fun x => (D1 + D2) (Ideal.Quotient.mk I x)) * adj (c.n v) =
        Matrix.map (P.n v) (fun x => D1 (Ideal.Quotient.mk I x)) * adj (c.n v) +
          Matrix.map (P.n v) (fun x => D2 (Ideal.Quotient.mk I x)) * adj (c.n v)
      rw [← Matrix.add_mul]
      congr 1
      all_goals (ext i j; simp)
  have tv_smul : ∀ (t : ResidueField Λ) D, tv (t • D) = t • tv D := by
    intro t D
    refine Prod.ext (funext fun g => ?_) (funext fun v => ?_)
    · show Matrix.map (P.r g) (fun x => (t • D) (Ideal.Quotient.mk I x)) * c.r g⁻¹ =
        t • (Matrix.map (P.r g) (fun x => D (Ideal.Quotient.mk I x)) * c.r g⁻¹)
      rw [← Matrix.smul_mul]
      congr 1
      all_goals (ext i j; simp)
    · show Matrix.map (P.n v) (fun x => (t • D) (Ideal.Quotient.mk I x)) * adj (c.n v) =
        t • (Matrix.map (P.n v) (fun x => D (Ideal.Quotient.mk I x)) * adj (c.n v))
      rw [← Matrix.smul_mul]
      congr 1
      all_goals (ext i j; simp)
  let T : PtDer (res Λ (R ⧸ I)) (ResidueField Λ) →ₗ[ResidueField Λ]
      (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ)) :=
    { toFun := fun D => tv D
      map_add' := fun D1 D2 => by
        simp only [Submodule.coe_add]
        exact tv_add _ _
      map_smul' := fun t D => by
        simp only [Submodule.coe_smul, RingHom.id_apply]
        exact tv_smul _ _ }
  have hc1 : ∀ g, c.r g⁻¹ * c.r g = 1 := fun g => by
    rw [← map_mul, inv_mul_cancel, map_one]
  have hn1 : ∀ v, adj (c.n v) * c.n v = 1 := fun v => by
    have := (hRes.pair.low v).1
    simpa [IsGSp] using this
  have hT : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro D hD0
    have h0 : tv D = 0 := hD0
    obtain ⟨gD, hgD⟩ := hder D
    obtain ⟨g0, hg0⟩ := hder 0
    have hr0 : ∀ g i j, (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I (P.r g i j)) = 0 := by
      intro g i j
      have := congrArg (fun p => p.1 g * c.r g) h0
      change Matrix.map (P.r g) (fun x => (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I x)) * c.r g⁻¹ * c.r g =
        (0 : (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ))).1 g * c.r g at this
      rw [Matrix.mul_assoc, hc1, Matrix.mul_one] at this
      simpa using congrFun (congrFun this i) j
    have hnz : ∀ v i j, (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I (P.n v i j)) = 0 := by
      intro v i j
      have := congrArg (fun p => p.2 v * c.n v) h0
      change Matrix.map (P.n v) (fun x => (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I x)) * adj (c.n v) * c.n v =
        (0 : (Γ → M4 (ResidueField Λ)) × (Φ.ι → M4 (ResidueField Λ))).2 v * c.n v at this
      rw [Matrix.mul_assoc, hn1, Matrix.mul_one] at this
      simpa using congrFun (congrFun this i) j
    have heq : P.map (gD : R →+* DualNumber (ResidueField Λ)) = P.map (g0 : R →+* DualNumber (ResidueField Λ)) := by
      refine PD.ext ?_ ?_
      · apply MonoidHom.ext
        intro g
        ext i j
        · show (gD (P.r g i j)).fst = (g0 (P.r g i j)).fst
          rw [(hgD _).1, (hg0 _).1]
        · show (gD (P.r g i j)).snd = (g0 (P.r g i j)).snd
          rw [(hgD _).2, (hg0 _).2, hr0]
          simp
      · funext v
        ext i j
        · show (gD (P.n v i j)).fst = (g0 (P.n v i j)).fst
          rw [(hgD _).1, (hg0 _).1]
        · show (gD (P.n v i j)).snd = (g0 (P.n v i j)).snd
          rw [(hgD _).2, (hg0 _).2, hnz]
          simp
    have huniq := hDef.2 (DualNumber (ResidueField Λ)) (P.map (g0 : R →+* DualNumber (ResidueField Λ))) (lifts_map hlift g0)
    have hg : gD = g0 := huniq.unique heq rfl
    apply Subtype.ext
    apply LinearMap.ext
    intro z
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective z
    have := (hgD x).2
    rw [hg, (hg0 x).2] at this
    simpa using this.symm
  have hrange : LinearMap.range T ≤ Submodule.span (ResidueField Λ) (Φ.Tan S c) := by
    rintro _ ⟨D, rfl⟩
    apply Submodule.subset_span
    obtain ⟨g, hg⟩ := hder D
    have hL : Φ.Lifts a c (P.map (g : R →+* DualNumber (ResidueField Λ))) := lifts_map hlift g
    have h1 : ∀ x : O, TrivSqZeroExt.snd (((algebraMap Λ (DualNumber (ResidueField Λ))).comp a) x) = 0 := by
      intro x
      rw [RingHom.comp_apply, Algebra.algebraMap_eq_smul_one]
      simp
    have h3 : ∀ g' i j, TrivSqZeroExt.fst ((P.map (g : R →+* DualNumber (ResidueField Λ))).r g' i j) = c.r g' i j := by
      intro g' i j
      show (g (P.r g' i j)).fst = _
      rw [(hg _).1, hcr]
    have h4 : ∀ v i j, TrivSqZeroExt.fst ((P.map (g : R →+* DualNumber (ResidueField Λ))).n v i j) = c.n v i j := by
      intro v i j
      show (g (P.n v i j)).fst = _
      rw [(hg _).1, hcn]
    have h5 : Supp S (P.map (g : R →+* DualNumber (ResidueField Λ))).r := by
      intro g' i j hij hw
      have hx := hsupp g' i j hij hw
      show g (P.r g' i j) = 0
      ext
      · rw [(hg _).1, (res_eq_zero_iff Λ R _).mpr (hIm hx)]
        simp
      · rw [(hg _).2, Ideal.Quotient.eq_zero_iff_mem.mpr hx]
        simp
    have key := redDual Φ ((algebraMap Λ (DualNumber (ResidueField Λ))).comp a) S c
      (P.map (g : R →+* DualNumber (ResidueField Λ))) h1 hL.pair (fun i j => lc_dual (hL.cont i j)) h3 h4 h5
    convert key using 1
    refine Prod.ext (funext fun g' => ?_) (funext fun v => ?_)
    · show Matrix.map (P.r g') (fun x => (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I x)) * c.r g'⁻¹ = _
      congr 1
      all_goals (ext i j; exact ((hg _).2).symm)
    · show Matrix.map (P.n v) (fun x => (D : R ⧸ I →ₗ[Λ] ResidueField Λ) (Ideal.Quotient.mk I x)) * adj (c.n v) = _
      congr 1
      all_goals (ext i j; exact ((hg _).2).symm)
  have hrk : Module.rank (ResidueField Λ) (PtDer (res Λ (R ⧸ I)) (ResidueField Λ)) ≤ ↑(d + 20 * C) := by
    rw [← rank_range_of_injective T hT]
    refine (Submodule.rank_mono hrange).trans ?_
    push_cast
    exact hrank
  exact redDim (R ⧸ I) (d + 20 * C) hrk
