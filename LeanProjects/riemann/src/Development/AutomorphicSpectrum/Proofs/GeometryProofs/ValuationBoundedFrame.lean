import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsSubMemEigW
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SplitHermitianGeneratorsExistStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FamilyHodgeLatticeDataStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IntersectionHiddenSecondStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalIsomorphismTransportStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BundleDegreeEqSumValuations
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.SubAndQuotientBundles
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.Fl
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CompanionTheory.Ar.Flat.DegZ

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat.DegProd

open Module

section Alg

variable {O : Type} [CommRing O] {J : Type} [Fintype J] (b : Basis J ℤ O)
  {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  (ρ : O →+* Module.End K V) (χ : O →+* K)

abbrev eigSpan : Submodule K V := ⨆ a : O, LinearMap.range (ρ a - χ a • LinearMap.id)

theorem exists_quot_basis {r : ℕ} (x : Fin r → V)
    (hli : LinearIndependent K fun q : Fin r × J => ρ (b q.2) (x q.1))
    (hsp : Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (x q.1)) = ⊤) :
    ∃ bq : Basis (Fin r) K (V ⧸ eigSpan ρ χ), (∀ j, bq j = (eigSpan ρ χ).mkQ (x j)) ∧
      ∀ (c : Fin r × J → K) (j : Fin r),
        bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j = ∑ k, c (j, k) * χ (b k) := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Basis (Fin r × J) K V, ∀ q, B q = ρ (b q.2) (x q.1) :=
    ⟨Basis.mk hli hsp.ge, fun q => by simp⟩
  obtain ⟨φ, hφB⟩ : ∃ φ : V →ₗ[K] (Fin r → K),
      ∀ q, φ (B q) = χ (b q.2) • Pi.single q.1 (1 : K) :=
    ⟨B.constr K fun q => χ (b q.2) • Pi.single q.1 (1 : K), fun q => B.constr_basis K _ q⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : (Fin r → K) →ₗ[K] V ⧸ eigSpan ρ χ,
      ∀ j, ψ (Pi.single j 1) = (eigSpan ρ χ).mkQ (x j) :=
    ⟨(Pi.basisFun K (Fin r)).constr K fun j => (eigSpan ρ χ).mkQ (x j), fun j => by
      simpa using (Pi.basisFun K (Fin r)).constr_basis K (fun j => (eigSpan ρ χ).mkQ (x j)) j⟩
  have hχ : ∀ a : O, χ a = ∑ k, ((b.repr a k : ℤ) : K) * χ (b k) := by
    intro a
    conv_lhs => rw [← b.sum_repr a]
    simp [map_sum, zsmul_eq_mul]
  have hρ : ∀ (a : O) (v : V), ρ a v = ∑ k, (b.repr a k : ℤ) • ρ (b k) v := by
    intro a v
    conv_lhs => rw [← b.sum_repr a]
    simp [map_sum, LinearMap.sum_apply]
  have hφx : ∀ (a : O) (j : Fin r), φ (ρ a (x j)) = χ a • Pi.single j (1 : K) := by
    intro a j
    rw [hρ, map_sum, hχ a, Finset.sum_smul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have h := hφB (j, k)
    rw [hB] at h
    rw [map_zsmul, h, mul_smul, Int.cast_smul_eq_zsmul]
  have hx : ∀ j, φ (x j) = Pi.single j (1 : K) := by
    intro j
    simpa using hφx 1 j
  have hφρ : ∀ (a : O) (v : V), φ (ρ a v) = χ a • φ v := by
    intro a v
    have h : φ ∘ₗ ρ a = χ a • φ := by
      refine B.ext fun q => ?_
      rw [LinearMap.comp_apply, LinearMap.smul_apply, hφB, hB, ← Module.End.mul_apply, ← map_mul,
        hφx, map_mul, mul_smul]
    exact LinearMap.congr_fun h v
  have hWk : eigSpan ρ χ ≤ LinearMap.ker φ := by
    refine iSup_le fun a => ?_
    rintro _ ⟨v, rfl⟩
    simp [hφρ]
  have hmk : ∀ v, (eigSpan ρ χ).mkQ v = ψ (φ v) := by
    have h : (eigSpan ρ χ).mkQ = ψ ∘ₗ φ := by
      refine B.ext fun q => ?_
      rw [LinearMap.comp_apply, hφB, map_smul, hψ, hB, ← map_smul, Submodule.mkQ_apply,
        Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact Submodule.mem_iSup_of_mem (b q.2) (LinearMap.mem_range.2 ⟨x q.1, rfl⟩)
    exact fun v => LinearMap.congr_fun h v
  let e : (V ⧸ eigSpan ρ χ) ≃ₗ[K] (Fin r → K) :=
    LinearEquiv.ofLinear ((eigSpan ρ χ).liftQ φ hWk) ψ
      ((Pi.basisFun K (Fin r)).ext fun j => by simp [hψ, hx])
      (Submodule.linearMap_qext _ (LinearMap.ext fun v => by
        simp only [LinearMap.comp_apply, LinearMap.id_apply, Submodule.mkQ_apply, Submodule.liftQ_apply]
        exact (hmk v).symm))
  have he : ∀ v, e ((eigSpan ρ χ).mkQ v) = φ v := fun v => by simp [e]
  refine ⟨(Pi.basisFun K (Fin r)).map e.symm, fun j => ?_, fun c j => ?_⟩
  · simp [e, hψ]
  · rw [Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, he, Pi.basisFun_repr]
    simp_rw [← hB]
    rw [map_sum, Finset.sum_apply, Fintype.sum_prod_type, Finset.sum_eq_single j]
    · simp [hφB]
    · intro j' _ hj'
      simp [hφB, Pi.single_apply, Ne.symm hj']
    · simp

theorem isLatOf_quot {C : ACurve K} (i : C.I) {r : ℕ} {x : Fin r → V}
    (bq : Basis (Fin r) K (V ⧸ eigSpan ρ χ)) (L : AddSubgroup V) (hχ : ∀ a, C.v i (χ a) ≤ 1)
    (hbq : ∀ (c : Fin r × J → K) (j : Fin r),
      bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j = ∑ k, c (j, k) * χ (b k))
    (hL : ∀ y, y ∈ L ↔ ∃ c : Fin r × J → K, (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • ρ (b q.2) (x q.1)) :
    IsLatOf C i bq (L.map (eigSpan ρ χ).mkQ.toAddMonoidHom) := by
  classical
  delta GlobalTheory.CompanionTheory.Ar.Crv.IsLatOf
  intro w
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, hc, rfl⟩ := (hL y).1 hy
    intro j
    show C.v i (bq.repr ((eigSpan ρ χ).mkQ (∑ q, c q • ρ (b q.2) (x q.1))) j) ≤ 1
    rw [hbq c j]
    refine Valuation.map_sum_le _ fun k _ => ?_
    rw [map_mul]
    exact mul_le_one' (hc (j, k)) (hχ (b k))
  · intro hw
    have h1 : χ 1 = ∑ k, ((b.repr 1 k : ℤ) : K) * χ (b k) := by
      conv_lhs => rw [← b.sum_repr 1]
      simp [map_sum, zsmul_eq_mul]
    refine ⟨∑ q : Fin r × J, (((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) • ρ (b q.2) (x q.1),
      (hL _).2 ⟨fun q : Fin r × J => ((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1, fun q => ?_, rfl⟩, ?_⟩
    · show C.v i (((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) ≤ 1
      rw [map_mul]
      refine mul_le_one' ?_ (hw q.1)
      have h := hχ ((b.repr 1 q.2 : ℤ) : O)
      rwa [map_intCast] at h
    · show (eigSpan ρ χ).mkQ _ = w
      refine bq.repr.injective (Finsupp.ext fun j => ?_)
      rw [hbq (fun q : Fin r × J => ((b.repr 1 q.2 : ℤ) : K) * bq.repr w q.1) j]
      calc ∑ k, ((b.repr 1 k : ℤ) : K) * bq.repr w j * χ (b k)
          = bq.repr w j * ∑ k, ((b.repr 1 k : ℤ) : K) * χ (b k) := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun k _ => by ring
        _ = bq.repr w j := by rw [← h1, map_one, _root_.mul_one]

end Alg

section Place

variable {E : Type} [Field E] [NumberField E] [StarRing (𝓞 E)] {K : Type} [Field K] {C : ACurve K}
  {p d r : ℕ} (F : Family C p d (𝓞 E)) (i : C.I)

private theorem rhoH_vmap_of_isMapOf {R R₂ : Type} [CommRing R] [CommRing R₂] {n : ℕ} {O : Type} [CommRing O]
    [StarRing O] (f : R →+* R₂) {B : Germ.FB R n O} {B₂ : Germ.FB R₂ n O} (h : IsMapOf f B B₂) (a : O)
    (u : (Fin n → R) × (Fin n → R)) : rhoH B₂ a (vmap f u) = vmap f (rhoH B a u) := by
  have hrho : ∀ a : O, rho B₂ a = (rho B a).map f := by
    intro a
    ext k l
    delta GlobalTheory.CompanionTheory.Ar.Conj.rho GlobalTheory.CompanionTheory.Ar.Conj.lin
    simp only [h.act, MvPowerSeries.coeff_map]
    rfl
  have hbil : bil (B₂.ad a) 1 1 = (bil (B.ad a) 1 1).map f := by
    ext k l
    delta GlobalTheory.CompanionTheory.Ar.Conj.bil
    simp only [h.ad, MvPowerSeries.coeff_map]
    rfl
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · delta GlobalTheory.CompanionTheory.Ar.Conj.rhoH GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap
    simp [hrho, RingHom.map_mulVec, Matrix.toLin'_apply, Function.comp_def]
  · delta GlobalTheory.CompanionTheory.Ar.Conj.rhoH GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap
    simp [hrho, hbil, RingHom.map_mulVec, Matrix.toLin'_apply, Matrix.transpose_map,
      Function.comp_def]

theorem rhoH_trans (a : 𝓞 E)
    (u : (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) :
    rhoH F.B a (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype u)) =
      transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (rhoH (F.Bi i) a u)) := by
  have h := (GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (F.iso i)).2.2.2.2.1 a
  rw [← LinearMap.comp_apply, h, LinearMap.comp_apply, rhoH_vmap_of_isMapOf _ (F.mapK i)]

private theorem exists_injective_linearMap_eq_vmap {Ω : Type} [Field Ω] (A : ValuationSubring Ω) (n : ℕ) :
    ∃ L : ((Fin n → A) × (Fin n → A)) →ₗ[A] ((Fin n → Ω) × (Fin n → Ω)),
      Function.Injective L ∧ ∀ u, L u = vmap A.subtype u := by
  refine ⟨⟨⟨vmap A.subtype, ?_⟩, ?_⟩, ?_, fun u => rfl⟩
  · intro u u'
    exact Prod.ext (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp)
      (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp)
  · intro s u
    exact Prod.ext (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp [Algebra.smul_def])
      (funext fun k => by delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.vmap; simp [Algebra.smul_def])
  intro u u' h
  have h1 := congrArg Prod.fst h
  have h2 := congrArg Prod.snd h
  refine Prod.ext (funext fun k => ?_) (funext fun k => ?_)
  · exact Subtype.ext (congrFun h1 k)
  · exact Subtype.ext (congrFun h2 k)

private theorem vmap_basis_linearIndependent_and_span {Ω : Type} [Field Ω] (A : ValuationSubring Ω) {n : ℕ} {Ix : Type}
    [Fintype Ix] {v : Ix → (Fin n → A) × (Fin n → A)} (hli : LinearIndependent A v)
    (hsp : Submodule.span A (Set.range v) = ⊤) :
    LinearIndependent Ω (fun q => vmap A.subtype (v q)) ∧
      Submodule.span Ω (Set.range fun q => vmap A.subtype (v q)) = ⊤ := by
  classical
  obtain ⟨L, hLi, hL⟩ := exists_injective_linearMap_eq_vmap A n
  have hA : LinearIndependent A (L ∘ v) := hli.map' L (LinearMap.ker_eq_bot.2 hLi)
  have hK : LinearIndependent Ω (fun q => vmap A.subtype (v q)) := by
    have := (LinearIndependent.iff_fractionRing A Ω).1 hA
    simpa [Function.comp_def, hL] using this
  refine ⟨hK, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [finrank_span_eq_card hK, ← Module.finrank_eq_card_basis (Basis.mk hli hsp.ge)]
  simp [Module.finrank_prod, Module.finrank_fin_fun]

theorem isHBasis_trans
    {x : Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)}
    (hx : IsHBasis (F.Bi i) x) :
    IsHBasis F.B fun j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x j)) := by
  obtain ⟨-, -, hbij, -⟩ := GlobalTheory.T.formal_isomorphism_transport _ _ _ _ _ _ _ _ (F.iso i)
  delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsHBasis at hx ⊢
  obtain ⟨hli, hsp⟩ := vmap_basis_linearIndependent_and_span (C.v i).valuationSubring hx.1 hx.2
  refine ⟨?_, ?_⟩
  · simpa only [Function.comp_def, ← rhoH_trans F i] using
      hli.map' (transH (F.φ i) (F.ψ i) (F.lam i)) (LinearMap.ker_eq_bot.2 hbij.1)
  · have key : Submodule.span K (Set.range (transH (F.φ i) (F.ψ i) (F.lam i) ∘
        fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
          vmap (C.v i).valuationSubring.subtype
            (rhoH (F.Bi i) (RingOfIntegers.basis E q.2) (x q.1)))) = ⊤ := by
      rw [Set.range_comp, Submodule.span_image, hsp, Submodule.map_top,
        LinearMap.range_eq_top.2 hbij.2]
    simpa only [Function.comp_def, ← rhoH_trans F i] using key

theorem mem_stdLat_iff
    {x : Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)}
    (hx : IsHBasis (F.Bi i) x) (y : (Fin d → K) × (Fin d → K)) :
    y ∈ stdLat (C.v i).valuationSubring.toSubring (transH (F.φ i) (F.ψ i) (F.lam i)) ↔
      ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K, (∀ q, C.v i (c q) ≤ 1) ∧
        y = ∑ q, c q • rhoH F.B (RingOfIntegers.basis E q.2)
          (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x q.1))) := by
  classical
  delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.IsHBasis at hx
  obtain ⟨L, -, hL⟩ := exists_injective_linearMap_eq_vmap (C.v i).valuationSubring d
  set T := transH (F.φ i) (F.ψ i) (F.lam i) with hT
  set bA := Basis.mk hx.1 hx.2.ge with hbA
  have hw : ∀ q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E),
      rhoH F.B (RingOfIntegers.basis E q.2) (T (vmap (C.v i).valuationSubring.subtype (x q.1))) =
        T (L (bA q)) := by
    intro q
    rw [hT, rhoH_trans F i, hL, hbA, Basis.mk_apply]
  simp_rw [hw]
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨y₀, hy₀, rfl⟩ := hz
      let u : (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring) :=
        (fun k => ⟨y₀.1 k, (hy₀ k).1⟩, fun k => ⟨y₀.2 k, (hy₀ k).2⟩)
      have hu : L u = y₀ := by
        rw [hL]
        rfl
      refine ⟨fun q => (bA.repr u q : K), fun q => (Valuation.mem_valuationSubring_iff _ _).1 (bA.repr u q).2, ?_⟩
      conv_lhs => rw [← hu, ← bA.sum_repr u, map_sum, map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [map_smul, LinearMap.map_smul_of_tower, ← algebraMap_smul K]
      rfl
    | zero => exact ⟨0, fun q => by simp, by simp⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨c, hc, rfl⟩ := hz
      obtain ⟨c', hc', rfl⟩ := hz'
      refine ⟨c + c', fun q => Valuation.map_add_le _ (hc q) (hc' q), ?_⟩
      simp [add_smul, Finset.sum_add_distrib]
    | smul s z _ hz =>
      obtain ⟨c, hc, rfl⟩ := hz
      refine ⟨fun q => (s : K) * c q, fun q => ?_, ?_⟩
      · rw [map_mul]
        exact mul_le_one' ((Valuation.mem_valuationSubring_iff _ _).1 s.2) (hc q)
      · rw [Subring.smul_def, Finset.smul_sum]
        simp [smul_smul]
  · rintro ⟨c, hc, rfl⟩
    refine Submodule.sum_mem _ fun q _ => ?_
    have hmem : T (L (bA q)) ∈ stdLat (C.v i).valuationSubring.toSubring T :=
      Submodule.subset_span ⟨L (bA q), fun k => ⟨by rw [hL]; exact (bA q).1 k |>.2,
        by rw [hL]; exact (bA q).2 k |>.2⟩, rfl⟩
    have := Submodule.smul_mem _ (⟨c q, (Valuation.mem_valuationSubring_iff _ _).2 (hc q)⟩ :
      (C.v i).valuationSubring.toSubring) hmem
    simpa [Subring.smul_def] using this

end Place

private theorem quot_deg_lemma_4 {K : Type} [Field K] (C : ACurve K) {V : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {O : Type} [CommRing O] {J : Type} [Fintype J]
    (b : Basis J ℤ O) (ρ : O →+* Module.End K V) (χ : O →+* K) (H : C.I → AddSubgroup V)
    (hH : GlobalTheory.CompanionTheory.Ar.Crv.IsBun C H) (hχ : ∀ (i : C.I) (a : O), C.v i (χ a) ≤ 1) {r : ℕ}
    (x₀ : Fin r → V)
    (h₀li : LinearIndependent K fun q : Fin r × J => ρ (b q.2) (x₀ q.1))
    (h₀sp : Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (x₀ q.1)) = ⊤)
    (y : C.I → Fin r → V)
    (hyli : ∀ i, LinearIndependent K fun q : Fin r × J => ρ (b q.2) (y i q.1))
    (hysp : ∀ i, Submodule.span K (Set.range fun q : Fin r × J => ρ (b q.2) (y i q.1)) = ⊤)
    (hL : ∀ i z, z ∈ H i ↔ ∃ c : Fin r × J → K, (∀ q, C.v i (c q) ≤ 1) ∧
      z = ∑ q, c q • ρ (b q.2) (y i q.1))
    (N : C.I → Matrix (Fin r) (Fin r) K)
    (hN : ∀ i j, y i j - ∑ l, N i j l • x₀ l ∈ eigSpan ρ χ)
    (h0 : GlobalTheory.CompanionTheory.Ar.Crv.deg C (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ)) = 0) :
    (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧
      ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  classical
  obtain ⟨b₀, hb₀, -⟩ := exists_quot_basis b ρ χ x₀ h₀li h₀sp
  choose bq hbq1 hbq2 using fun i => exists_quot_basis b ρ χ (y i) (hyli i) (hysp i)
  have hLat : ∀ i, GlobalTheory.CompanionTheory.Ar.Crv.IsLatOf C i (bq i) (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ) i) :=
    fun i => isLatOf_quot b ρ χ i (bq i) (H i) (hχ i) (hbq2 i) (hL i)
  have hBun := (GlobalTheory.T.sub_and_quotient_bundles K C V H (eigSpan ρ χ) hH).2
  obtain ⟨hfin, hdeg⟩ :=
    GlobalTheory.T.bundle_degree_eq_sum_valuations K C _ (GlobalTheory.CompanionTheory.Ar.Crv.quot C H (eigSpan ρ χ)) r b₀ bq hBun hLat
  have hdet : ∀ i, b₀.det (bq i) = (N i).det := by
    intro i
    have hbqN : ∀ j, bq i j = ∑ l, N i j l • b₀ l := by
      intro j
      rw [hbq1 i j]
      simp_rw [hb₀]
      rw [show (∑ l, N i j l • (eigSpan ρ χ).mkQ (x₀ l)) =
          (eigSpan ρ χ).mkQ (∑ l, N i j l • x₀ l) by rw [map_sum]; simp only [map_smul]]
      rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
      exact hN i j
    have hM : b₀.toMatrix (bq i) = (N i).transpose := by
      ext a j
      rw [Basis.toMatrix_apply, hbqN, Matrix.transpose_apply, ← Basis.equivFun_symm_apply,
        ← Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    rw [Basis.det_apply, hM, Matrix.det_transpose]
  refine ⟨fun i => ?_, ?_, ?_⟩
  · rw [← hdet i]
    exact (b₀.isUnit_det (bq i)).ne_zero
  · simpa only [hdet] using hfin
  · rw [hdeg] at h0
    simpa only [hdet] using h0

theorem curve_deg : ∀ (E : Type) [Field E] [NumberField E] [StarRing (𝓞 E)] (K : Type) [Field K] (C : ACurve K) (p : ℕ) [Fact p.Prime] [CharP K p] (d r : ℕ) (F : Family C p d (𝓞 E)) (χ : 𝓞 E →+* K), (∀ a : 𝓞 E, ((Algebra.lmul ℤ (𝓞 E) a : Module.End ℤ (𝓞 E)).charpoly.map (Int.castRingHom K)).Splits) → (∀ (i : C.I) (a : 𝓞 E), C.v i (χ a) ≤ 1) → ∀ (x₀ : Fin r → (Fin d → K) × (Fin d → K)) (x : ∀ i : C.I, Fin r → (Fin d → (C.v i).valuationSubring) × (Fin d → (C.v i).valuationSubring)) (N : C.I → Matrix (Fin r) (Fin r) K), IsHBasis F.B x₀ → (∀ i, IsHBasis (F.Bi i) (x i)) → (∀ i j, transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)) - ∑ l, N i j l • x₀ l ∈ eigW F.B χ) → (∀ i, (N i).det ≠ 0) ∧ {i | C.v i (N i).det ≠ 1}.Finite ∧ ∑ᶠ i, (C.w i : ℤ) * WithZero.log (C.v i (N i).det) = 0 := by
  intro E _ _ _ K _ C p _ _ d r F χ hspl hχ x₀ x N hx₀ hx hN
  classical
  rcases isEmpty_or_nonempty C.I with hI | hI
  · refine ⟨fun i => (IsEmpty.false i).elim,
      Set.finite_empty.subset fun i _ => (IsEmpty.false i).elim, ?_⟩
    rw [finsum_of_isEmpty]
  obtain ⟨D, hDρ, hDH⟩ := GlobalTheory.T.family_hodge_lattice_data K C p d (𝓞 E) F hI
  have hW : eigW F.B χ = eigSpan D.ρH χ := by
    delta GlobalTheory.CompanionTheory.Ar.Flat.DegZ.eigW
    simp only [eigSpan, hDρ]
  obtain ⟨h₀li, h₀sp⟩ := hx₀
  have hHB := fun i => isHBasis_trans F i (hx i)
  have hL : ∀ i y, y ∈ D.H i ↔ ∃ c : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) → K,
      (∀ q, C.v i (c q) ≤ 1) ∧ y = ∑ q, c q • D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1))) := by
    intro i y
    rw [hDH i y, mem_stdLat_iff F i (hx i) y]
    simp only [hDρ]
  have hyli : ∀ i, LinearIndependent K fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1))) := by
    intro i
    obtain ⟨h1, -⟩ := hHB i
    simpa only [hDρ] using h1
  have hysp : ∀ i, Submodule.span K (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) =>
      D.ρH (RingOfIntegers.basis E q.2)
        (transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i q.1)))) = ⊤ := by
    intro i
    obtain ⟨-, h2⟩ := hHB i
    simpa only [hDρ] using h2
  have h0 := GlobalTheory.T.split_hermitian_generators_exist E K C p d r D χ hspl fun i =>
    ⟨fun j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)),
      hyli i, hL i⟩
  exact quot_deg_lemma_4 C (RingOfIntegers.basis E) D.ρH χ D.H D.H_bun hχ x₀
    (by simpa only [hDρ] using h₀li) (by simpa only [hDρ] using h₀sp)
    (fun i j => transH (F.φ i) (F.ψ i) (F.lam i) (vmap (C.v i).valuationSubring.subtype (x i j)))
    hyli hysp hL N (fun i j => by rw [← hW]; exact hN i j) h0

end GlobalTheory.CompanionTheory.Ar.Flat.DegProd
