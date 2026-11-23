import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PredMemGamRanks
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HasRatBasisOfAct
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CoefActionReprMemSubfield
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NablaDeltaOperatorLatticePreserved
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DualLatticeIsLatticeAndHermitianDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeExtensionAlongFieldEmbeddingDuals
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNeZeroSmulMemAlt

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Forms GlobalTheory.Mem.Col2 Formalism.DivisionValues
open scoped Matrix ComplexOrder

noncomputable section

namespace GlobalTheory.Mem.LatGood

theorem map_mulVec_injective {K m k : Type} [Field K] [Fintype m] [Fintype k] (φ : K →+* ℂ) (B : Matrix m k K)
    (h : Function.Injective B.mulVec) : Function.Injective (B.map φ).mulVec := by
  classical
  have hk : LinearMap.ker (Matrix.toLin' B) = ⊥ := by
    apply LinearMap.ker_eq_bot.mpr
    intro x y hxy
    apply h
    simpa [Matrix.toLin'_apply] using hxy
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' B) hk
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.toLin' B) = 1 := by
    rw [hg]; exact LinearMap.toMatrix'_id
  rw [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin'] at h1
  have h2 : (LinearMap.toMatrix' g).map φ * B.map φ = 1 := by
    rw [← Matrix.map_mul, h1]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  intro x y hxy
  have := congrArg ((LinearMap.toMatrix' g).map φ).mulVec hxy
  simpa [Matrix.mulVec_mulVec, h2] using this

section Datum

variable {K : Type} [Field K] [NumberField K] [StarRing K] (C : CSD K)

def valMat (c : C.Cl) : Matrix C.ιV (Fin C.dim) K :=
  Matrix.of fun i a => C.bV.repr ((C.basis a : C.Cl → C.V) c) i

theorem pair_eq (x y : C.V) :
    C.pair x y = ∑ i, ∑ j, star (C.bV.repr x i) * C.gramV i j * C.bV.repr y j := by
  conv_lhs => rw [← C.bV.sum_repr x, ← C.bV.sum_repr y]
  simp only [map_sum, LinearMap.sum_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul,
    starRingEnd_apply, Finset.mul_sum, CSD.gramV, Matrix.of_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem gram_map (hb : C.HasRatBasis) (φ : K →+* ℂ) :
    C.H.map φ = ∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ • (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ) := by
  ext a b
  simp only [Matrix.map_apply, CSD.H, Matrix.of_apply, CSD.csum, map_sum, map_mul, map_inv₀, map_natCast,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, pair_eq, Matrix.mul_apply, Matrix.conjTranspose_apply, valMat]
  refine Finset.sum_congr rfl fun c _ => ?_
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [C.basis_rat hb a c i φ]
  rfl

theorem exists_val_ne (φ : K →+* ℂ) (x : Fin C.dim → ℂ) (hx : x ≠ 0) :
    ∃ c, ((valMat C c).map φ) *ᵥ x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let B : Matrix (C.Cl × C.ιV) (Fin C.dim) K := Matrix.of fun p a => valMat C p.1 p.2 a
  have hB : Function.Injective B.mulVec := by
    intro u v huv
    apply C.I_injective
    funext c
    apply C.bV.repr.injective
    ext i
    have h1 := congrFun huv (c, i)
    simp only [Matrix.mulVec, dotProduct, B, valMat, Matrix.of_apply] at h1
    simp only [CSD.I_eq_sum, Finset.sum_apply, Pi.smul_apply, map_sum, map_smul, Finsupp.coe_finsetSum,
      Finsupp.smul_apply, smul_eq_mul]
    simpa only [mul_comm] using h1
  apply hx
  apply map_mulVec_injective φ B hB
  rw [Matrix.mulVec_zero]
  funext p
  exact congrFun (hcon p.1) p.2

theorem gram_posDef (hb : C.HasRatBasis) (φ : K →+* ℂ) (hp : (C.gramV.map φ).PosDef) : (C.H.map φ).PosDef := by
  have hw : ∀ c, (0 : ℂ) < ((C.wt c : ℕ) : ℂ)⁻¹ := fun c => inv_pos.mpr (by exact_mod_cast C.wt_pos c)
  rw [gram_map C hb φ]
  have hpsd : (∑ c, ((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)).PosSemidef :=
    Matrix.posSemidef_sum _ fun c _ => (hp.posSemidef.conjTranspose_mul_mul_same _).smul (hw c).le
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hpsd.1 fun x hx => ?_
  have e : ∀ c, star x ⬝ᵥ (((C.wt c : ℕ) : ℂ)⁻¹ •
      (((valMat C c).map φ)ᴴ * C.gramV.map φ * (valMat C c).map φ)) *ᵥ x =
      ((C.wt c : ℕ) : ℂ)⁻¹ * (star (((valMat C c).map φ) *ᵥ x) ⬝ᵥ (C.gramV.map φ) *ᵥ (((valMat C c).map φ) *ᵥ x)) := by
    intro c
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Matrix.star_mulVec,
      ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  rw [Matrix.sum_mulVec, dotProduct_sum]
  simp only [e]
  obtain ⟨c, hc⟩ := exists_val_ne C φ x hx
  exact Finset.sum_pos' (fun c _ => mul_nonneg (hw c).le (hp.posSemidef.dotProduct_mulVec_nonneg _))
    ⟨c, Finset.mem_univ c, mul_pos (hw c) (hp.dotProduct_mulVec_pos hc)⟩

omit [StarRing K] in

theorem exists_smul_mem {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    {M : Submodule (𝓞 K) V} {x : V} (hx : x ∈ Submodule.span K (M : Set V)) : ∃ d : 𝓞 K, d ≠ 0 ∧ d • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem
  | exact _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem
  | (apply _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroSmulMemIntegralSpan.exists_ne_zero_smul_mem ..)

theorem values_isLattice (M : C.Cl → Submodule (𝓞 K) C.V) (hM : ∀ c, Submodule.IsLattice K (M c))
    (L : Submodule (𝓞 K) C.Forms) (hL : ∀ x, x ∈ L ↔ ∀ c, x.1 c ∈ M c) :
    L.FG ∧ Submodule.span K (L : Set C.Forms) = ⊤ := by
  classical
  constructor
  · apply Submodule.fg_of_fg_map_injective (C.Forms.subtype.restrictScalars (𝓞 K)) Subtype.val_injective
    refine Submodule.FG.of_le (Submodule.fg_pi fun c => (hM c).fg) ?_
    rintro _ ⟨x, hx, rfl⟩ c _
    exact (hL x).1 hx c
  · rw [eq_top_iff]
    intro x _
    have h : ∀ c, ∃ d : 𝓞 K, d ≠ 0 ∧ d • x.1 c ∈ M c := fun c =>
      exists_smul_mem (by rw [(hM c).span_eq_top]; trivial)
    choose d hd hdM using h
    have hx : (∏ c, d c) • x ∈ L := by
      rw [hL]
      intro c
      rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ c)]
      show ((∏ c' ∈ Finset.univ.erase c, d c') * d c) • x.1 c ∈ M c
      rw [mul_smul]
      exact (M c).smul_mem _ (hdM c)
    have hd0 : (∏ c, d c) ≠ 0 := Finset.prod_ne_zero_iff.mpr fun c _ => hd c
    have hd' : algebraMap (𝓞 K) K (∏ c, d c) ≠ 0 := by simpa only [ne_eq, FaithfulSMul.algebraMap_eq_zero_iff] using hd0
    have : x = (algebraMap (𝓞 K) K (∏ c, d c))⁻¹ • ((∏ c, d c) • x) := by
      rw [← algebraMap_smul K (∏ c, d c) x, smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)

end Datum

theorem root_mem_cmMax {K : Type} [Field K] [StarRing K] (σ : K →+* ℂ)
    (hσ : ∀ x, σ (star x) = starRingEnd ℂ (σ x)) {u : K} {m : ℕ} (hm : m ≠ 0) (hu : u ^ m = 1) : u ∈ cmMax K := by
  have key : ∀ φ : K →+* ℂ, φ u⁻¹ = starRingEnd ℂ (φ u) := by
    intro φ
    have h1 : (φ u) ^ m = 1 := by rw [← map_pow, hu, map_one]
    rw [map_inv₀]
    exact Complex.inv_eq_conj (Complex.norm_eq_one_of_pow_eq_one h1 hm)
  have hs : star u = u⁻¹ := σ.injective (by rw [hσ, key])
  intro φ
  rw [hs, key]

section Step

variable {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ}
  (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n)

theorem rho_rat (hF : FOk emb σ) (hS : S.Ok) (b : S.β) (g : S.G b) (i j : VVIdx lam) :
    (bVV K lam).repr (S.rho emb lam b g (bVV K lam j)) i ∈ cmMax K := by
  have he : ∀ τ x, emb τ x ∈ cmMax K := fun τ x φ => by
    rw [← hF.emb_star]
    exact hF.conjE (φ.comp (emb τ)) x
  have h1 := (GlobalTheory.coefAction_repr_mem_subfield emb (cmMax K) lam he (S.gam b g) i j).2
  obtain ⟨m, hm, hu⟩ := hS.root b g
  have h2 : ((S.chr b g : Kˣ) : K) ∈ cmMax K :=
    root_mem_cmMax σ hF.sig_star hm.ne' (by rw [← Units.val_pow_eq_pow_val, hu, Units.val_one])
  have e : S.rho emb lam b g (bVV K lam j) = ((S.chr b g : Kˣ) : K) • rhoVr emb lam (S.gam b g) (bVV K lam j) := rfl
  rw [e, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_mem h2 h1

theorem hasRatBasis (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) : (S.csd emb lam h).HasRatBasis :=
  GlobalTheory.FormsDescent.hasRatBasis_of_act _ fun c γ i j => rho_rat S emb σ lam hF hS c.1 γ.1 i j

theorem gramV_posDef (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) : ((S.csd emb lam h).gramV.map φ).PosDef := by
  have h1 := pairingPositive_holds K ι n lam (gramKd emb (1 : Matrix (Fin n) (Fin n) E)) φ fun τ => by
    have : gramKd emb (1 : Matrix (Fin n) (Fin n) E) τ = 1 := by
      simp [gramKd]
    rw [this, map_one']
    exact Matrix.PosDef.one
  exact h1

theorem step_gram_posDef (hF : FOk emb σ) (hS : S.Ok) (h : (S.fam emb lam).Ok) (φ : K →+* ℂ) :
    ((S.csd emb lam h).H.map φ).PosDef :=
  gram_posDef _ (hasRatBasis S emb σ lam hF hS h) φ (gramV_posDef S emb lam h φ)

omit [StarRing E] [StarRing K] in
theorem delAtr_isLattice (L : Submodule (𝓞 E) (Fin n → E)) (hL : Submodule.IsLattice E L) :
    Submodule.IsLattice K (delAtr emb lam L) :=
  (GlobalTheory.TransLattice.nabDelLattice K ι n lam _ fun τ =>
    GlobalTheory.DualLat.isLattice_dualFr _ (GlobalTheory.TauLat.tauLatLattice E K ι n emb τ L hL)).2

end Step

theorem lawGood : ∀ {E K ι : Type} [Field E] [NumberField E] [StarRing E] [Field K] [NumberField K] [StarRing K] [Fintype ι] {n : ℕ} (S : GStep E K n) (emb : ι → E →+* K) (σ : K →+* ℂ) (lam : ι → DomWeight n), FOk emb σ → S.Ok → ∀ h, S.LawGood emb lam h := by
  intro E K ι _ _ _ _ _ _ _ n S emb σ lam hF hS h
  exact ⟨fun v => (frameOfSpec _ _ (step_gram_posDef S emb σ lam hF hS h v.embedding)).1,
    values_isLattice (S.csd emb lam h) (fun c => delAtr emb lam (S.Lsh c.1 (S.rep c)))
      (fun c => delAtr_isLattice emb lam _ (hS.lsh_lat c.1 _)) _ fun _ => Iff.rfl⟩

end GlobalTheory.Mem.LatGood
