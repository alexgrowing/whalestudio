import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianLatticeLocalBases
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ScaledBlockSumSelfDualTraceSkewForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemPolarizationIdealOfMemConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatticeLatticeBlockDirectSumScaled
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsSelfDualCLatFrame

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.PlaceSpaces

open scoped ComplexOrder

theorem hasSig_map_conj {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (M.map (starRingEnd ℂ)) r s := by
  obtain ⟨h1, A, hA⟩ := h
  refine ⟨h1, A.map star, ?_⟩
  have := congrArg (fun X : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ => X.map (starRingEnd ℂ)) hA
  simp only [Matrix.map_mul] at this
  have e1 : (A.map star)ᵀ * M.map (starRingEnd ℂ) * (A.map star).map star =
      (Aᵀ).map (starRingEnd ℂ) * M.map (starRingEnd ℂ) * (A.map star).map (starRingEnd ℂ) := by
    congr 2 <;> ext i j <;> simp
  have e2 : (Matrix.fromBlocks 1 0 0 (-1) : Matrix (Fin r ⊕ Fin s) (Fin r ⊕ Fin s) ℂ).map (starRingEnd ℂ) =
      Matrix.fromBlocks 1 0 0 (-1) := by
    ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply] <;> split_ifs <;> simp
  rw [e1, this, e2]

theorem hasSig_neg {n r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (-M) s r := by
  obtain ⟨h1, A, hA⟩ := h
  refine ⟨by omega, A.submatrix id Sum.swap, ?_⟩
  have e : (A.submatrix id Sum.swap)ᵀ * -M * (A.submatrix id Sum.swap).map star =
      -((Aᵀ * M * A.map star).submatrix Sum.swap Sum.swap) := by
    ext i j
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply, Matrix.neg_apply, Finset.sum_neg_distrib]
  rw [e, hA]
  ext (i | i) (j | j) <;> simp [Matrix.fromBlocks, Matrix.one_apply]

theorem hasSig_smul_reindex {n d r s : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig M r s)
    (e : Fin n ≃ Fin d) {κ : ℝ} (hκ : 0 < κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig ((κ : ℂ) • Matrix.reindex e e M) r s := by
  obtain ⟨h1, A, hA⟩ := h
  have hnd : n = d := by simpa using Fintype.card_congr e
  refine ⟨by omega, (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • A.submatrix e.symm id, ?_⟩
  have hs : ((Real.sqrt κ)⁻¹ : ℝ) * ((Real.sqrt κ)⁻¹ : ℝ) * κ = 1 := by
    rw [← mul_inv, Real.mul_self_sqrt hκ.le, inv_mul_cancel₀ hκ.ne']
  have hs' : (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * (κ : ℂ) = 1 := by exact_mod_cast hs
  have e0 : (A.submatrix e.symm id)ᵀ * Matrix.reindex e e M * (A.submatrix e.symm id).map star = Aᵀ * M * A.map star := by
    have t1 : (A.submatrix e.symm id)ᵀ = Aᵀ.submatrix id e.symm := rfl
    have t2 : (A.submatrix e.symm id).map star = (A.map star).submatrix e.symm id := rfl
    rw [t1, t2, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv]
    rfl
  have e1 : ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • A.submatrix e.symm id)ᵀ * ((κ : ℂ) • Matrix.reindex e e M) *
      ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • A.submatrix e.symm id).map star =
      ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) * (κ : ℂ)) •
        ((A.submatrix e.symm id)ᵀ * Matrix.reindex e e M * (A.submatrix e.symm id).map star) := by
    have t3 : ((((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • A.submatrix e.symm id).map star =
        (((Real.sqrt κ)⁻¹ : ℝ) : ℂ) • (A.submatrix e.symm id).map star := by
      ext i j; simp
    rw [t3, Matrix.transpose_smul, Matrix.smul_mul, Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul,
      smul_smul, smul_smul]
  rw [e1, hs', one_smul, e0, hA]

theorem isCartan_neg {n : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan M θ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (-M) (-θ) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨by rw [neg_mul_neg, h1], ?_, fun x hx => ?_⟩
  · have e : (-θ).map star = -(θ.map star) := by ext i j; simp
    rw [e, Matrix.transpose_neg, neg_mul_neg, Matrix.mul_neg, h2]
  · have e : ((-θ) *ᵥ x) ⬝ᵥ (-M) *ᵥ star x = (θ *ᵥ x) ⬝ᵥ M *ᵥ star x := by
      rw [Matrix.neg_mulVec, Matrix.neg_mulVec, neg_dotProduct, dotProduct_neg, neg_neg]
    rw [e]; exact h3 x hx

theorem isCartan_smul_conj {k : ℕ} {G s : Matrix (Fin k) (Fin k) ℂ} (h : IsCartanInv G s) {κ : ℝ} (hκ : 0 < κ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan ((κ : ℂ) • G) (s.map (starRingEnd ℂ)) := by
  obtain ⟨hSS, hSGS, hGS⟩ := h
  have hGH : Gᴴ = G := by
    have h4 : sᴴ * Gᴴ = G * s := by rw [← Matrix.conjTranspose_mul]; exact hGS.1.eq
    have h5 : sᴴ * sᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hSS, Matrix.conjTranspose_one]
    calc Gᴴ = sᴴ * (sᴴ * Gᴴ) := by rw [← Matrix.mul_assoc, h5, Matrix.one_mul]
      _ = G := by rw [h4, ← Matrix.mul_assoc, hSGS]
  have hSG : sᴴ * G = G * s := by
    have := hGS.1.eq
    rw [Matrix.conjTranspose_mul, hGH] at this
    exact this
  have hT : (s.map (starRingEnd ℂ))ᵀ = sᴴ := by
    ext i j; simp [Matrix.conjTranspose_apply]
  have hMM : (s.map (starRingEnd ℂ)).map star = s := by
    ext i j; simp
  refine ⟨?_, ?_, ?_⟩
  · rw [← Matrix.map_mul, hSS, Matrix.map_one _ (map_zero _) (map_one _)]
  · rw [hT, hMM, Matrix.mul_smul, Matrix.smul_mul, hSGS]
  · intro x hx
    have hy : star x ≠ 0 := by simpa using hx
    have hv : s.map (starRingEnd ℂ) *ᵥ x = star (s *ᵥ star x) := by
      ext i; simp [Matrix.mulVec, dotProduct, star_sum, Pi.star_apply, mul_comm]
    have hpos : ((κ : ℂ) • (G * s)).PosDef := hGS.smul (by exact_mod_cast hκ)
    have key : (s.map (starRingEnd ℂ) *ᵥ x) ⬝ᵥ ((κ : ℂ) • G) *ᵥ star x =
        star (star x) ⬝ᵥ (((κ : ℂ) • (G * s)) *ᵥ star x) := by
      rw [hv, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mul_smul, hSG]
    rw [key]
    have := hpos.dotProduct_mulVec_pos hy
    exact (Complex.lt_def.1 this).1

theorem isCartanInv_reindex {n d : ℕ} {G s : Matrix (Fin n) (Fin n) ℂ} (h : IsCartanInv G s) (e : Fin n ≃ Fin d) :
    IsCartanInv (Matrix.reindex e e G) (Matrix.reindex e e s) := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  · simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix]
    rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, h2]
  · simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_mul_equiv]
    exact h3.submatrix e.symm.injective

end GlobalTheory.PlaceSpaces

namespace GlobalTheory.PlaceSpaces

variable {D : D7}

open scoped ComplexOrder in

theorem fr_cart_isCartanInv {V : HSp D} (A : Fr V) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) (A.cart τ) := by
  have h1 : A.fr τ * (A.fr τ)⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ))
  have h2 : (A.fr τ)⁻¹ * A.fr τ = 1 := mul_eq_one_comm.1 h1
  have hJ := Formalism.REAL.Jm_mul_self (A.ε τ)
  have hJ' := Formalism.REAL.Jm_conjTranspose (A.ε τ)
  have hG : gramAt D V τ * A.cart τ = (A.fr τ)ᴴ * A.fr τ := by
    rw [← A.fr_gram τ]; unfold Fr.cart
    calc _ = (A.fr τ)ᴴ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one]
  have hs : A.cart τ * A.cart τ = 1 := by
    unfold Fr.cart
    calc _ = (A.fr τ)⁻¹ * (Formalism.REAL.Jm (A.ε τ) * (A.fr τ * (A.fr τ)⁻¹) * Formalism.REAL.Jm (A.ε τ)) * A.fr τ := by
          simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1, Matrix.mul_one, hJ, Matrix.mul_one, h2]
  refine ⟨hs, ?_, ?_⟩
  · have hGh : (gramAt D V τ)ᴴ = gramAt D V τ := by
      rw [← A.fr_gram τ]; simp [Matrix.conjTranspose_mul, hJ', Matrix.mul_assoc]
    have h3 : (A.cart τ)ᴴ * gramAt D V τ = gramAt D V τ * A.cart τ := by
      have := congrArg Matrix.conjTranspose hG
      rw [Matrix.conjTranspose_mul, hGh, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose] at this
      rw [this, hG]
    rw [h3, Matrix.mul_assoc, hs, Matrix.mul_one]
  · rw [hG]
    exact Matrix.PosDef.conjTranspose_mul_self _ (Matrix.mulVec_injective_of_isUnit (A.fr_unit τ))

theorem herm_dual (S : HSp D) (y : Fin S.rank → D.host.E) :
    y ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame S) ↔
      ∀ x ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame S),
        IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig S.gram y x) := by
  have hV := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  have hherm : ∀ a b, star (S.gram b a) = S.gram a b := fun a b => S.herm.eq (S.frame b) (S.frame a)
  have hh' : ∀ a b, star (S.gram a b) = S.gram b a := fun a b => hherm b a
  have key : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig S.gram y x =
      star (∑ a, ∑ b, star ((star x) a) * S.gram a b * (star y) b) := fun x => by
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star,
      Pi.star_apply, hσ, hh', Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    ring
  show star y ∈ GlobalTheory.PlaceModel.latFrame S ↔ _
  rw [hV.2 (star y)]
  constructor
  · intro h x hx
    rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff]
    exact h _ hx
  · intro h x' hx'
    have := h (star x') (by rw [GlobalTheory.TripleSpaceW.mem_conjSub, star_star]; exact hx')
    rw [key, ← GlobalTheory.TripleSpaceW.exists_coe_iff, star_star] at this
    exact this

theorem form_skew (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) (x y : Fin d → D.host.E) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig (D.host.xi0 • Matrix.reindex e e S.gramᵀ) y x =
      D.host.xi0 * GlobalTheory.SkewLat.DualPair.hS S (fun k => x (e k)) (fun k => y (e k)) := by
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, GlobalTheory.SkewLat.DualPair.hS, dotProduct, Matrix.mulVec, Matrix.smul_apply,
    Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply, hσ, smul_eq_mul, Finset.mul_sum]
  rw [← e.sum_comp]
  simp only [← e.sum_comp, Equiv.symm_apply_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  ring

theorem I_smul_skew_map (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) (τ : D.what₂.Tau) (φ : D.host.E →+* ℂ)
    (hφ : ∀ x, φ x = starRingEnd ℂ (tauE D τ x)) :
    Complex.I • (D.host.xi0 • Matrix.reindex e e S.gramᵀ).map φ =
      (((tauE D τ D.host.xi0).im : ℝ) : ℂ) • Matrix.reindex e e (gramAt D S τ) := by
  have hre : (tauE D τ D.host.xi0).re = 0 := by
    have h := congrArg Complex.re (GlobalTheory.FockCompare.tauE_star τ D.host.xi0)
    rw [GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, map_neg, Complex.neg_re, Complex.conj_re] at h
    linarith
  have hx : φ D.host.xi0 = -((((tauE D τ D.host.xi0).im : ℝ) : ℂ) * Complex.I) := by
    rw [hφ]; apply Complex.ext <;> simp [hre]
  have hg : ∀ (k l : Fin S.rank), φ (S.gram l k) = tauE D τ (S.gram k l) := fun k l => by
    rw [hφ, ← GlobalTheory.FockCompare.tauE_star]
    have h1 : S.gramᴴ = S.gram := Matrix.ext fun a b => S.herm.eq _ _
    have h2 := congrFun (congrFun h1 k) l
    rw [Matrix.conjTranspose_apply] at h2
    rw [h2]
  ext k l
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
    Matrix.transpose_apply, map_mul, hx, hg, gramAt]
  linear_combination (-(((tauE D τ D.host.xi0).im : ℝ) : ℂ) * tauE D τ (S.gram (e.symm k) (e.symm l))) * Complex.I_mul_I

def skLat (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) : Submodule (𝓞 D.host.E) (Fin d → D.host.E) :=
  (GlobalTheory.SkewLat.scLat D.host.AA (GlobalTheory.PlaceModel.latFrame S)).map
    ((LinearEquiv.funCongrLeft D.host.E D.host.E e.symm).restrictScalars (𝓞 D.host.E)).toLinearMap

theorem mem_skLat (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) (y : Fin d → D.host.E) :
    y ∈ skLat S e ↔ (fun k => y (e k)) ∈ GlobalTheory.SkewLat.scLat D.host.AA (GlobalTheory.PlaceModel.latFrame S) := by
  unfold skLat
  rw [Submodule.mem_map_equiv]
  rfl

theorem AA_ne : D.host.AA ≠ 0 := fun h => by
  have := Formalism.IndefR.Fin.factPrincipalDatum D.R D.host
  rw [h, mul_zero, zero_mul, zero_mul] at this
  exact zero_ne_one this

theorem skLat_isLattice (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) : Submodule.IsLattice D.host.E (skLat S e) := by
  have hL := GlobalTheory.SkewLat.PairLatLattice.scLat_isLattice (AA_ne (D := D)) (GlobalTheory.PlaceModel.isSelfDualC_latFrame S).1
  refine ⟨Submodule.FG.map _ hL.fg, ?_⟩
  unfold skLat
  rw [Submodule.map_coe]
  have : ⇑((LinearEquiv.funCongrLeft D.host.E D.host.E e.symm).restrictScalars (𝓞 D.host.E)).toLinearMap =
      ⇑(LinearEquiv.funCongrLeft D.host.E D.host.E e.symm).toLinearMap := rfl
  rw [this, Submodule.span_image, hL.span_eq_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (LinearEquiv.funCongrLeft D.host.E D.host.E e.symm).surjective

theorem skew_dual (S : HSp D) {d : ℕ} (e : Fin S.rank ≃ Fin d) (y : Fin d → D.host.E) :
    y ∈ skLat S e ↔ ∀ x ∈ skLat S e, ∀ o : 𝓞 D.host.E,
      IsIntegral ℤ (Algebra.trace ℚ D.host.E (o * GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig
        (D.host.xi0 • Matrix.reindex e e S.gramᵀ) y x)) := by
  have hV := GlobalTheory.PlaceModel.isSelfDualC_latFrame S
  have hs : ∀ c ∈ D.host.AA, star c ∈ D.host.AAbar := fun c h => by
    rw [Formalism.BasicNotions.Examples₂.star_eq_conj]; exact Formalism.L2.Pj.conj_mem_AAbar D h
  have hc : ∀ c ∈ D.host.AAbar, star c ∈ D.host.AA := fun c h => GlobalTheory.star_mem_AA_of_mem_AAbar h
  constructor
  · intro hy x hx o
    rw [form_skew]
    exact GlobalTheory.SkewLat.DualPair.fwd hs S hV ((mem_skLat S e x).1 hx) ((mem_skLat S e y).1 hy) o
  · intro h
    refine (mem_skLat S e y).2 (GlobalTheory.SkewLat.DualPair.bwd hc S hV fun a ha s hs' => ?_)
    have hx : (fun i => (a • s) (e.symm i)) ∈ skLat S e := by
      rw [mem_skLat]
      simp only [Equiv.symm_apply_apply]
      exact GlobalTheory.SkewLat.DualPair.smul_mem_scLat ha hs'
    intro o
    have := h _ hx o
    rw [form_skew] at this
    simpa only [Equiv.symm_apply_apply] using this

end GlobalTheory.PlaceSpaces

open GlobalTheory.PlaceSpaces in

theorem GlobalTheory.PlaceSpaces.spaces_of_triple : ∀ (D : D7) (W W₁ X : HSp D) (A : Fr W) (A₁ : Fr W₁) (B : Fr X) (α β : (AE D)ˣ →* Circle), IsTriple W W₁ X α β →
    ∀ p q : ℕ, (∀ τ, Formalism.UG.HasSignature (gramAt D W τ) (W.rank - p) p ∧ Formalism.UG.HasSignature (gramAt D W₁ τ) (W₁.rank - q) q ∧
      Formalism.UG.HasSignature (gramAt D X τ) (X.rank - (p + q)) (p + q)) →
    ∀ (e : Fin X.rank ≃ Fin (W.rank + W₁.rank)) (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base D.host.F D.host.E), Bs.IsGood D.sp.cm.sig →
    (∀ w, ∃ τ, ∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) →
    ∃ (V : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W.rank) (V' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E W₁.rank)
      (Ws : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc D.host.F D.host.E (W.rank + W₁.rank)),
      V.J = (1 : D.host.E) • W.gram ∧ V'.J = (-1 : D.host.E) • W₁.gram ∧ Ws.J = D.host.xi0 • reindex e e X.gramᵀ ∧
      V.IsHerm D.sp.cm.sig Bs (W.rank - p) p ∧ V'.IsHerm D.sp.cm.sig Bs q (W₁.rank - q) ∧
      Ws.IsSkew D.sp.cm.sig Bs (W.rank + W₁.rank - (p + q)) (p + q) ∧
      ∀ w, ∃ τ, (∀ x, (Bs.emb w).1 x = starRingEnd ℂ (tauE D τ x)) ∧ V.θ w = A.cart τ ∧ V'.θ w = -A₁.cart τ ∧
        Ws.θ w = (reindex e e (B.cart τ)).map (starRingEnd ℂ) := by
  intro D W W₁ X A A₁ B α β _hT p q hsig e Bs hBs hemb
  choose τf hτf using hemb
  have hcm := hBs.cm
  have hσ : ∀ z : D.host.E, D.sp.cm.sig z = star z := fun _ => rfl
  have hherm : ∀ (S : HSp D) (a b : Fin S.rank), star (S.gram b a) = S.gram a b := fun S a b =>
    S.herm.eq (S.frame b) (S.frame a)
  haveI hlW : (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W)).IsLattice D.host.E :=
    GlobalTheory.TripleSpaceW.conjSub_isLattice (GlobalTheory.PlaceModel.isSelfDualC_latFrame W).1
  haveI hlW₁ : (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W₁)).IsLattice D.host.E :=
    GlobalTheory.TripleSpaceW.conjSub_isLattice (GlobalTheory.PlaceModel.isSelfDualC_latFrame W₁).1
  haveI hlX : (skLat X e).IsLattice D.host.E := skLat_isLattice X e
  have exW := fun v : Bs.P => GlobalTheory.AdelicU.exists_isSplitBasis (Bs.τ v) (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W)) hcm
  have exW₁ := fun v : Bs.P =>
    GlobalTheory.AdelicU.exists_isSplitBasis (Bs.τ v) (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W₁)) hcm
  have exX := fun v : Bs.P => GlobalTheory.AdelicU.exists_isSplitBasis (Bs.τ v) (skLat X e) hcm
  have emap : ∀ (S : HSp D) (w : InfinitePlace D.host.F),
      ((1 : D.host.E) • S.gram).map (Bs.emb w).1 = (gramAt D S (τf w)).map (starRingEnd ℂ) := by
    intro S w
    ext a b; simp [hτf, gramAt]
  classical
  refine ⟨GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.mk ((1 : D.host.E) • W.gram) (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W))
      (fun w => A.cart (τf w)) (fun v => if h : v ∈ Bs.P then (exW ⟨v, h⟩).choose else 1),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.mk ((-1 : D.host.E) • W₁.gram) (GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W₁))
      (fun w => -A₁.cart (τf w)) (fun v => if h : v ∈ Bs.P then (exW₁ ⟨v, h⟩).choose else 1),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc.mk (D.host.xi0 • Matrix.reindex e e X.gramᵀ) (skLat X e)
      (fun w => (Matrix.reindex e e (B.cart (τf w))).map (starRingEnd ℂ))
      (fun v => if h : v ∈ Bs.P then (exX ⟨v, h⟩).choose else 1),
    rfl, rfl, rfl, ⟨?h1, ?h2, hlW, ?h3, ?h4, ?h5⟩, ⟨?g1, ?g2, hlW₁, ?g3, ?g4, ?g5⟩, ⟨?k1, ?k2, hlX, ?k3, ?k4, ?k5⟩,
    fun w => ⟨τf w, hτf w, rfl, rfl, rfl⟩⟩
  case h1 =>
    intro a b
    show D.sp.cm.sig (((1 : D.host.E) • W.gram) b a) = ((1 : D.host.E) • W.gram) a b
    rw [one_smul, hσ]; exact hherm W a b
  case h2 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((1 : D.host.E) • W.gram).map (Bs.emb w).1) _ _
    rw [emap W w]
    exact hasSig_map_conj (GlobalTheory.TripleSpaceW.hasSig_of_hasSignature (hsig (τf w)).1)
  case h3 =>
    intro y
    show y ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W) ↔ ∀ x ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W),
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((1 : D.host.E) • W.gram) y x)
    rw [one_smul]; exact herm_dual W y
  case h4 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((1 : D.host.E) • W.gram).map (Bs.emb w).1) (A.cart (τf w))
    rw [emap W w]
    exact GlobalTheory.TripleSpaceW.isCartan_map_conj (fr_cart_isCartanInv A (τf w))
  case h5 =>
    intro v
    show GlobalTheory.AdelicU.IsSplitBasis (Bs.τ v) _ (if h : v.1 ∈ Bs.P then (exW ⟨v.1, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (exW v).choose_spec
  case g1 =>
    intro a b
    show D.sp.cm.sig (((-1 : D.host.E) • W₁.gram) b a) = ((-1 : D.host.E) • W₁.gram) a b
    simp only [Matrix.smul_apply, smul_eq_mul, hσ, star_mul', star_neg, star_one, hherm W₁ a b]
  case g2 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (((-1 : D.host.E) • W₁.gram).map (Bs.emb w).1) _ _
    have e2 : ((-1 : D.host.E) • W₁.gram).map (Bs.emb w).1 = -((gramAt D W₁ (τf w)).map (starRingEnd ℂ)) := by
      ext a b; simp [hτf, gramAt]
    rw [e2]
    exact hasSig_neg (hasSig_map_conj (GlobalTheory.TripleSpaceW.hasSig_of_hasSignature (hsig (τf w)).2.1))
  case g3 =>
    intro y
    show y ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W₁) ↔ ∀ x ∈ GlobalTheory.TripleSpaceW.conjSub (GlobalTheory.PlaceModel.latFrame W₁),
      IsIntegral ℤ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • W₁.gram) y x)
    have hf : ∀ x, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig ((-1 : D.host.E) • W₁.gram) y x =
        -GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form D.sp.cm.sig W₁.gram y x := fun x => by
      simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.form, Matrix.neg_mulVec]
    rw [herm_dual W₁ y]
    refine forall₂_congr fun x _ => ?_
    rw [hf]
    exact ⟨fun h => h.neg, fun h => by simpa using h.neg⟩
  case g4 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (((-1 : D.host.E) • W₁.gram).map (Bs.emb w).1) (-A₁.cart (τf w))
    have e2 : ((-1 : D.host.E) • W₁.gram).map (Bs.emb w).1 = -((gramAt D W₁ (τf w)).map (starRingEnd ℂ)) := by
      ext a b; simp [hτf, gramAt]
    rw [e2]
    exact isCartan_neg (GlobalTheory.TripleSpaceW.isCartan_map_conj (fr_cart_isCartanInv A₁ (τf w)))
  case g5 =>
    intro v
    show GlobalTheory.AdelicU.IsSplitBasis (Bs.τ v) _ (if h : v.1 ∈ Bs.P then (exW₁ ⟨v.1, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (exW₁ v).choose_spec
  case k1 =>
    intro a b
    show D.sp.cm.sig ((D.host.xi0 • Matrix.reindex e e X.gramᵀ) b a) = -(D.host.xi0 • Matrix.reindex e e X.gramᵀ) a b
    simp only [Matrix.smul_apply, Matrix.reindex_apply, Matrix.submatrix_apply, Matrix.transpose_apply, smul_eq_mul, hσ,
      star_mul', GlobalTheory.DualPairCheck.star_purely_imaginary_eq_neg D, hherm X]
    ring
  case k2 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.HasSig (Complex.I • (D.host.xi0 • Matrix.reindex e e X.gramᵀ).map (Bs.emb w).1) _ _
    rw [I_smul_skew_map X e (τf w) _ (hτf w)]
    have hr : X.rank = W.rank + W₁.rank := by simpa using Fintype.card_congr e
    have h := hasSig_smul_reindex (GlobalTheory.TripleSpaceW.hasSig_of_hasSignature (hsig (τf w)).2.2) e (xi_zero_im_pos D (τf w))
    convert h using 2
    omega
  case k3 => exact fun y => skew_dual X e y
  case k4 =>
    intro w
    show GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsCartan (Complex.I • (D.host.xi0 • Matrix.reindex e e X.gramᵀ).map (Bs.emb w).1) _
    rw [I_smul_skew_map X e (τf w) _ (hτf w)]
    exact isCartan_smul_conj (isCartanInv_reindex (fr_cart_isCartanInv B (τf w)) e) (xi_zero_im_pos D (τf w))
  case k5 =>
    intro v
    show GlobalTheory.AdelicU.IsSplitBasis (Bs.τ v) _ (if h : v.1 ∈ Bs.P then (exX ⟨v.1, h⟩).choose else 1)
    rw [dif_pos v.2]
    exact (exX v).choose_spec
