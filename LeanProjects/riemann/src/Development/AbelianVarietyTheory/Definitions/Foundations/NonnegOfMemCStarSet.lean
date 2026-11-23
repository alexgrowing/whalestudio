import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ValuationFormPsiBalancedSymmetricPeriodForm
import Formalism.LocalToGlobal.ProjectiveLattices.TowerOfAt

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.SlopeRec

open NumberField IsDedekindDomain Module GlobalTheory.AllWt GlobalTheory.CompHt Formalism.HN Formalism.HermitianLatticesTheory
open scoped ENNReal

section Coord

variable {K V W : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

open Classical in

def coordOf (N : (K →+* ℂ) → V → ℝ) :
    Σ n : ℕ, (V →ₗ[K] (Fin n → K)) × ((Fin n → K) →ₗ[K] V) × (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ) :=
  if h : HasGram N then ⟨h.some.1, h.some.2.1.1.equivFun, h.some.2.1.1.equivFun.symm, h.some.2.1.2⟩ else ⟨0, 0, 0, 1⟩

variable (N : (K →+* ℂ) → V → ℝ) (N' : (K →+* ℂ) → W → ℝ)

def cDim : ℕ := (coordOf N).1

def toCo : V →ₗ[K] (Fin (cDim N) → K) := (coordOf N).2.1

def ofCo : (Fin (cDim N) → K) →ₗ[K] V := (coordOf N).2.2.1

def frameCo : InfinitePlace K → Matrix (Fin (cDim N)) (Fin (cDim N)) ℂ := (coordOf N).2.2.2

def mapCo (φ : V →ₗ[K] W) : (Fin (cDim N) → K) →ₗ[K] (Fin (cDim N') → K) := toCo N' ∘ₗ φ ∘ₗ ofCo N

variable {N N'}

omit [NumberField K] in

theorem exists_basis_co (h : HasGram N) : ∃ b : Basis (Fin (cDim N)) K V,
    IsGram b (frameCo N) N ∧ toCo N = b.equivFun ∧ ofCo N = b.equivFun.symm := by
  have key : ∀ s : Σ n : ℕ, (V →ₗ[K] (Fin n → K)) × ((Fin n → K) →ₗ[K] V) ×
      (InfinitePlace K → Matrix (Fin n) (Fin n) ℂ),
      s = ⟨h.some.1, h.some.2.1.1.equivFun, h.some.2.1.1.equivFun.symm, h.some.2.1.2⟩ →
      ∃ b : Basis (Fin s.1) K V, IsGram b s.2.2.2 N ∧ s.2.1 = b.equivFun ∧ s.2.2.1 = b.equivFun.symm := by
    rintro _ rfl
    exact ⟨_, h.some.2.2, rfl, rfl⟩
  exact key _ (dif_pos h)

omit [NumberField K] in

theorem cDim_eq (h : HasGram N) : cDim N = finrank K V := by
  obtain ⟨b, -⟩ := exists_basis_co h
  rw [finrank_eq_card_basis b, Fintype.card_fin]

omit [NumberField K] in

theorem ofCo_toCo (h : HasGram N) (x : V) : ofCo N (toCo N x) = x := by
  obtain ⟨b, -, h1, h2⟩ := exists_basis_co h
  rw [h1, h2]; exact b.equivFun.symm_apply_apply x

omit [NumberField K] in

theorem toCo_ofCo (h : HasGram N) (y : Fin (cDim N) → K) : toCo N (ofCo N y) = y := by
  obtain ⟨b, -, h1, h2⟩ := exists_basis_co h
  rw [h1, h2]; exact b.equivFun.apply_symm_apply y

omit [NumberField K] in

theorem toCo_bijective (h : HasGram N) : Function.Bijective (toCo N) :=
  Function.bijective_iff_has_inverse.2 ⟨ofCo N, ofCo_toCo h, toCo_ofCo h⟩

omit [NumberField K] in

theorem mapCo_toCo (h : HasGram N) (φ : V →ₗ[K] W) (x : V) : mapCo N N' φ (toCo N x) = toCo N' (φ x) := by
  simp [mapCo, ofCo_toCo h]

variable [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]

variable (N) in

def latCo (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (Fin (cDim N) → K) := L.map ((toCo N).restrictScalars (𝓞 K))

omit [NumberField K] in

theorem latCo_bijective (h : HasGram N) : Function.Bijective (latCo N) :=
  ⟨Submodule.map_injective_of_injective (toCo_bijective h).1,
    Submodule.map_surjective_of_surjective (toCo_bijective h).2⟩

omit [NumberField K] in

theorem latCo_le_iff (h : HasGram N) {L L' : Submodule (𝓞 K) V} : latCo N L ≤ latCo N L' ↔ L ≤ L' :=
  Submodule.map_le_map_iff_of_injective (f := (toCo N).restrictScalars (𝓞 K)) (toCo_bijective h).1 _ _

omit [NumberField K] in

theorem latCo_eq_bot_iff (h : HasGram N) {L : Submodule (𝓞 K) V} : latCo N L = ⊥ ↔ L = ⊥ := by
  rw [← (latCo_bijective h).1.eq_iff, latCo, latCo, Submodule.map_bot]

omit [NumberField K] in

theorem latCo_inf (h : HasGram N) (L : Submodule (𝓞 K) V) (S : Submodule K V) :
    latCo N (L ⊓ S.restrictScalars (𝓞 K)) = latCo N L ⊓ (S.map (toCo N)).restrictScalars (𝓞 K) :=
  Submodule.map_inf _ (toCo_bijective h).1

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem range_mapCo (h : HasGram N) (e : V →ₗ[K] V) : LinearMap.range (mapCo N N e) = (LinearMap.range e).map (toCo N) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩; exact ⟨_, ⟨_, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩; exact ⟨toCo N x, mapCo_toCo h e x⟩

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

theorem ker_mapCo (h : HasGram N) (e : V →ₗ[K] V) : LinearMap.ker (mapCo N N e) = (LinearMap.ker e).map (toCo N) := by
  ext y
  obtain ⟨x, rfl⟩ := (toCo_bijective h).2 y
  rw [LinearMap.mem_ker, mapCo_toCo h, map_eq_zero_iff _ (toCo_bijective h).1]
  exact ⟨fun hx => ⟨x, hx, rfl⟩, fun ⟨y, hy, e'⟩ => (toCo_bijective h).1 e' ▸ hy⟩

omit [NumberField K] in

theorem rkK_latCo (h : HasGram N) (L : Submodule (𝓞 K) V) : rkK (latCo N L) = rkK L := by
  have e : Submodule.span K (latCo N L : Set _) = (Submodule.span K (L : Set V)).map (toCo N) := by
    rw [Submodule.map_span]; rfl
  rw [rkK, rkK, e]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ (toCo_bijective h).1 _)).symm

variable [StarRing K]

theorem zl_latCo {b : Basis (Fin (cDim N)) K V} (h1 : toCo N = b.equivFun) (L : Submodule (𝓞 K) V) :
    zl (realize (Pi.basisFun K (Fin (cDim N))) (frameCo N)) (latCo N L) = zl (realize b (frameCo N)) L := by
  ext y
  have e : ∀ x, realize (Pi.basisFun K (Fin (cDim N))) (frameCo N) (toCo N x) = realize b (frameCo N) x := fun x => by
    rw [h1]; rfl
  constructor
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩; exact ⟨x, hx, (e x).symm⟩
  · rintro ⟨x, hx, rfl⟩; exact ⟨_, ⟨x, hx, rfl⟩, e x⟩

theorem muDef_latCo (h : HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) :
    muDef (Pi.basisFun K (Fin (cDim N))) (frameCo N) (latCo N L) = slope_sq N L := by
  obtain ⟨b, hb, h1, -⟩ := exists_basis_co h
  rw [slope_sq_eq hb hL, muDef, muDef, Formalism.HN.slope, Formalism.HN.slope, zl_latCo h1]

theorem muMaxDef_latCo (h : HasGram N) {L : Submodule (𝓞 K) V} (hL : L.FG) (h0 : L ≠ ⊥) :
    muMaxDef (Pi.basisFun K (Fin (cDim N))) (frameCo N) (latCo N L) = slopeMax_sq N L := by
  obtain ⟨b, hb, h1, -⟩ := exists_basis_co h
  rw [(slopeMax_slopeMin_eq hb hL h0).1, muMaxDef, muMaxDef, muMax, muMax]
  congr 4
  ext t
  constructor
  · rintro ⟨M, hM, hM0, rfl⟩
    obtain ⟨M, rfl⟩ := (latCo_bijective h).2 M
    exact ⟨M, (latCo_le_iff h).1 hM, mt (latCo_eq_bot_iff h).2 hM0, by rw [Formalism.HN.slope, Formalism.HN.slope, zl_latCo h1]⟩
  · rintro ⟨M, hM, hM0, rfl⟩
    exact ⟨latCo N M, (latCo_le_iff h).2 hM, mt (latCo_eq_bot_iff h).1 hM0,
      by rw [Formalism.HN.slope, Formalism.HN.slope, zl_latCo h1]⟩

end Coord

section Copies

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] (ι : Type) [Fintype ι]

def piNorm (N : (K →+* ℂ) → V → ℝ) (σ : K →+* ℂ) (F : ι → V) : ℝ := Real.sqrt (∑ i, N σ (F i) ^ 2)

theorem hasGram_piNorm {N : (K →+* ℂ) → V → ℝ} (h : HasGram N) : HasGram (piNorm ι N) := by
  classical
  obtain ⟨n, ⟨b, X⟩, hb⟩ := h
  refine IsGram.hasGram (b := (Pi.basis fun _ : ι => b).reindex
    ((Equiv.sigmaEquivProd ι (Fin n)).trans (Equiv.prodComm _ _)))
    (X := fun v => Matrix.blockDiagonal fun _ : ι => X v) fun v => ⟨?_, fun F => ?_⟩
  · rw [Matrix.det_blockDiagonal]
    exact IsUnit.prod_iff.2 fun _ _ => (hb v).1
  · have hi : (Matrix.blockDiagonal fun _ : ι => X v)⁻¹ = Matrix.blockDiagonal fun _ : ι => (X v)⁻¹ := by
      refine Matrix.inv_eq_left_inv ?_
      rw [← Matrix.blockDiagonal_mul]
      simp only [Matrix.nonsing_inv_mul _ (hb v).1]
      exact Matrix.blockDiagonal_one
    simp only [piNorm, ← (hb v).2, normAt, cnorm, fcoord, hi]
    congr 1
    rw [Fintype.sum_prod_type_right]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 2
    have e : ∀ k, vecAt ((Pi.basis fun _ : ι => b).reindex
        ((Equiv.sigmaEquivProd ι (Fin n)).trans (Equiv.prodComm _ _))) v F k = vecAt b v (F k.2) k.1 := fun k => by
      simp only [vecAt, Basis.repr_reindex_apply]; rfl
    simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Matrix.blockDiagonal_apply, e]

variable [Module (𝓞 K) V]

def piLat (L : Submodule (𝓞 K) V) : Submodule (𝓞 K) (ι → V) := Submodule.pi Set.univ fun _ => L

end Copies

open AlgebraicGeometry CategoryTheory IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.DVR Formalism.L2.Pj
  Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

def compMean (g : Comp Xo c → ℝ) : ℝ := (∑ᶠ Z, g Z) / (Nat.card (Comp Xo c) : ℝ)

theorem compMean_eq {g : Comp Xo c → ℝ} (h : ∀ Z Z', g Z = g Z') (Z : Comp Xo c) : compMean g = g Z := by
  haveI := CompFin.finite_comp Xo c
  haveI := Fintype.ofFinite (Comp Xo c)
  haveI : Nonempty (Comp Xo c) := ⟨Z⟩
  have hc : (Fintype.card (Comp Xo c) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp only [compMean, fun Z' => h Z' Z, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.card_eq_fintype_card]
  field_simp

section Short

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ) {D : D7} (V : (c.F →+* ℂ) → HSp D)
  (dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r)

def cStarSet (G : WTZ E) : Set ℝ :=
  {t | ∃ (n : ℕ) (w : Fin n → cuspW Xo c U G) (abelian₂ : ℝ), CompShortGen U x V dict G w abelian₂ ∧ t = cStar n abelian₂}

def cStarInf (G : WTZ E) : ℝ := sInf (cStarSet U x V dict G)

variable {U x V dict} {G : WTZ E}

theorem nonneg_of_mem_cStarSet {t : ℝ} (h : t ∈ cStarSet U x V dict G) : 0 ≤ t := by
  obtain ⟨n, w, abelian₂, hw, rfl⟩ := h
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [cStar]
  · exact Real.log_nonneg (one_le_mul_of_one_le_of_one_le (Real.one_le_sqrt.2 (by exact_mod_cast hn)) hw.one_le)

theorem cStarInf_nonneg : 0 ≤ cStarInf U x V dict G := Real.sInf_nonneg fun _ => nonneg_of_mem_cStarSet

end Short

section Ref

variable {T : CDVR} {io : c.F →+* T.Fr}

def HasPhi (y : IntFr Xo c T io) (φ : ℝ) : Prop :=
  letI := io.toAlgebra
  ∃ (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (_ : SABMap t' Xo.univ.t y.1.x)
    (_ : SABMap t' G (spMap (algebraMap T.V T.Fr))) (P : PELUnif (maximalIdeal T.V) G) (ϖ : T.V)
    (Q : P.D.toPre.X → ℤ) (β : Formalism.MainNotions.ModuliIntegralCharts.SymB (IsCMField.complexConj E : E → E) P.D.toPre.X),
    Irreducible ϖ ∧ QForm.IsQ P.D.toPre ϖ Q ∧ (∀ a, 0 ≤ Q a) ∧
      (∀ a, (β : _ →ₗ[ℤ] _ →ₗ[ℤ] ℝ) a a = 2 * (Q a : ℝ)) ∧ φ = Formalism.MainNotions.ModuliIntegralCharts.phiC _ β

theorem HasPhi.nonneg {y : IntFr Xo c T io} {φ : ℝ} (h : HasPhi y φ) : 0 ≤ φ := by
  obtain ⟨G, t', -, -, P, ϖ, Q, β, -, -, h0, hβ, rfl⟩ := h
  refine Real.sInf_nonneg ?_
  rintro _ ⟨lf, -, hl, rfl⟩
  by_cases hb : β = 0
  · rw [hb, map_zero]
  · exact (hl β (fun a => by rw [hβ]; exact mul_nonneg zero_le_two (by exact_mod_cast h0 a)) hb).le

theorem exists_hasPhi (y : IntFr Xo c T io) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr))
    (m1 : letI := io.toAlgebra; SABMap t' Xo.univ.t y.1.x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr)))
    (P : PELUnif (maximalIdeal T.V) G) : ∃ φ, HasPhi y φ := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T.V
  obtain ⟨Q, β, hQ, h0, -, hβ, -⟩ := GlobalTheory.ValForm.main E H T.V G P ϖ hϖ (IsCMField.complexConj E : E → E) fun _ => rfl
  exact ⟨_, G, t', m1, m2, P, ϖ, Q, β, hϖ, hQ, h0, hβ, rfl⟩

variable (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

def depthAt_vp (G : WTZ E) (p : ℕ) (y : IntFr Xo c T io) : EReal :=
  depth_vw U G fun f => nval T.V (vV T.V (p : T.Fr)).toNat (evI y f)

def refExp_vp (cst : ℝ) (G : WTZ E) (p : ℕ) : EReal :=
  ⨆ (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ) (_ : OverLa la.1 T.V io e) (y : IntFr Xo c T io)
    (_ : y.IsAlg) (φ : ℝ) (_ : HasPhi y φ), depthAt_vp U G p y - ((cst * φ / (vV T.V (p : T.Fr) : ℝ) : ℝ) : EReal)

theorem refExp_vp_le_iff {cst : ℝ} {G : WTZ E} {p : ℕ} {a : EReal} : refExp_vp U cst G p ≤ a ↔
    ∀ (la : PointsOfFlagModel.abelian₂ p c) (T : CDVR) (io : c.F →+* T.Fr) (e : ℕ), OverLa la.1 T.V io e → ∀ y : IntFr Xo c T io,
      y.IsAlg → ∀ φ : ℝ, HasPhi y φ →
        depthAt_vp U G p y ≤ a + ((cst * φ / (vV T.V (p : T.Fr) : ℝ) : ℝ) : EReal) := by
  simp only [refExp_vp, iSup_le_iff, EReal.sub_le_iff_le_add (Or.inl (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ne_top _))]

def refSum (cst : ℝ) (G : WTZ E) : ℝ≥0∞ :=
  ∑' p : Nat.Primes, (refExp_vp U cst G p).toENNReal * ENNReal.ofReal (Real.log (p : ℕ))

end Ref

example : cDim (piNorm (Fin 2) fun (σ : ℚ →+* ℂ) (y : ℚ) => ‖σ y‖) = 2 := by
  have h : HasGram fun (σ : ℚ →+* ℂ) (y : ℚ) => ‖σ y‖ :=
    IsGram.hasGram (b := Basis.singleton Unit ℚ) (X := fun _ => 1) fun v =>
      ⟨by simp, fun x => by simp [normAt, cnorm, fcoord, vecAt, Real.sqrt_sq_eq_abs]⟩
  rw [cDim_eq (hasGram_piNorm _ h)]; simp

end GlobalTheory.SlopeRec
