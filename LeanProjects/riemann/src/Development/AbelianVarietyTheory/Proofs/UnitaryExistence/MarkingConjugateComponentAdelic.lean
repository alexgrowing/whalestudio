import Mathlib
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.CoeSelfDualLatticeInFrameCoordinatesEq
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.PermutesRefl
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.MarkingConj
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsSplitPeriod
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumRankOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RationalPointsAdelicUnitaryEqUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletionStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvarianceStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.RelabelEmbeddingsGoodBijectiveConjCompatStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CramerMemAdelicCompletionOfElementSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameUniformEmbeddingThird
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsEqSmulOfFinrankOne

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj GlobalTheory.Member
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory.CompRat

namespace GlobalTheory.ConjMark

section Det

open GlobalTheory.AdLat

variable (F : Type) {E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

omit [NumberField E] in
theorem adelicCompletionOfElementSet_mono {J J' : Set E} (h : J ⊆ J') : hat1 F J ≤ hat1 F J' :=
  AddSubgroup.closure_mono fun _ ⟨a, ha, x, hx, e⟩ => ⟨a, ha, x, h hx, e⟩

theorem prod_sub_prod_mem {ι : Type} (s : Finset ι) (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≤ 1)
    (J : ι → FractionalIdeal (𝓞 E)⁰ E) (x y : ι → RA F E) (hy : ∀ i, y i ∈ hat1 F (J i : Set E))
    (hx : ∀ i, x i - y i ∈ hat1 F ((I * J i : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    ∏ i ∈ s, x i - ∏ i ∈ s, y i ∈ hat1 F ((I * ∏ i ∈ s, J i : FractionalIdeal (𝓞 E)⁰ E) : Set E) := by
  classical
  have hx' : ∀ i, x i ∈ hat1 F (J i : Set E) := fun i => by
    have h : I * J i ≤ J i := by simpa using mul_le_mul_left hI (J i)
    simpa using add_mem (adelicCompletionOfElementSet_mono F h (hx i)) (hy i)
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.prod_insert ha]
    have h1 := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hx a) _ (prod_mem_adelicCompletionOfElementSet F s J x fun i _ => hx' i)
    have h2 := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (hy a) _ ih
    rw [mul_assoc] at h1
    rw [mul_left_comm] at h2
    convert add_mem h1 h2 using 1
    ring

theorem det_sub_one_mem {n : ℕ} (I : FractionalIdeal (𝓞 E)⁰ E) (hI : I ≤ 1)
    (cI : Fin n → FractionalIdeal (𝓞 E)⁰ E) (hc : ∀ a, cI a ≠ 0) (k : Matrix (Fin n) (Fin n) (RA F E))
    (h : ∀ i j, (k - 1) i j ∈ hat1 F ((I * (cI i * (cI j)⁻¹) : FractionalIdeal (𝓞 E)⁰ E) : Set E)) :
    k.det - 1 ∈ hat1 F (I : Set E) := by
  rw [← Matrix.det_one (n := Fin n) (R := RA F E), Matrix.det_apply, Matrix.det_apply, ← Finset.sum_sub_distrib]
  refine sum_mem fun σ _ => ?_
  have := prod_sub_prod_mem F Finset.univ I hI (fun j => cI (σ j) * (cI j)⁻¹) (fun j => k (σ j) j)
    (fun j => (1 : Matrix (Fin n) (Fin n) (RA F E)) (σ j) j) (fun j => by
      by_cases hj : σ j = j
      · rw [hj, Matrix.one_apply_eq, mul_inv_cancel₀ (hc j), Algebra.TensorProduct.one_def]
        exact one_tmul_mem_adelicCompletionOfElementSet F (FractionalIdeal.one_mem_one _)
      · rw [Matrix.one_apply_ne hj]
        exact zero_mem _) (fun j => h _ _)
  rw [Finset.prod_mul_distrib, Equiv.prod_comp σ cI, ← Finset.prod_mul_distrib,
    Finset.prod_eq_one fun i _ => mul_inv_cancel₀ (hc i), mul_one] at this
  rw [← smul_sub, Units.smul_def]
  exact zsmul_mem this _

theorem det_sub_one_mem_of_half {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (G : Matrix (Fin n) (Fin n) (RA F E)) (M : ℕ) (hM : M ≠ 0)
    (I I' : Ideal (𝓞 E)) (hI : I * I' = Ideal.span {(M : 𝓞 E)})
    (hg : ∀ b ∈ I', ∀ x ∈ L, ∃ w ∈ hat F (L : Set (Fin n → E)), G *ᵥ fv F (b • x) - fv F (b • x) = M • w) :
    G.det - 1 ∈ hat1 F (algebraMap (𝓞 E) E '' (I : Set (𝓞 E))) := by
  obtain ⟨-, e, cI, hc, hL, -⟩ := GlobalTheory.exists_pseudoBasis_adapted E n L ⊤ hfg hsp
  have key := mem_hat_pseudoBasis_iff F E n L e cI hL
  let P : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun i a => fv F (e a) i
  let Q : Matrix (Fin n) (Fin n) (RA F E) := Matrix.of fun b i =>
    (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ e.repr (Pi.single i 1) b
  have hP : ∀ w : Fin n → RA F E, P *ᵥ w = ∑ a, w a • fv F (e a) := by
    intro w
    funext i
    simp [P, Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hQ : ∀ w b, (Q *ᵥ w) b = adCoord F e b w := by
    intro w b
    change ∑ i : Fin n, _ = ∑ i : Fin n, _
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hQP : Q * P = 1 := by
    refine Matrix.ext_of_mulVec_single fun i => ?_
    funext b
    rw [← Matrix.mulVec_mulVec, hQ, hP, adCoord_sum, Matrix.one_mulVec]
  have hPQ : P * Q = 1 := mul_eq_one_comm.1 hQP
  have key' : ∀ w ∈ hat F (L : Set (Fin n → E)), ∀ a, (Q *ᵥ w) a ∈ hat1 F (cI a : Set E) := by
    intro w hw
    rw [← key, ← hP, Matrix.mulVec_mulVec, hPQ, Matrix.one_mulVec]
    exact hw
  have hkdet : (Q * G * P).det = G.det := by
    have : Q.det * P.det = 1 := by rw [← Matrix.det_mul, hQP, Matrix.det_one]
    simp only [Matrix.det_mul]
    linear_combination G.det * this
  have hI0 : (I' : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := by
    rw [FractionalIdeal.coeIdeal_ne_zero]
    rintro rfl
    rw [Ideal.mul_bot, eq_comm, Ideal.span_singleton_eq_bot] at hI
    exact hM (by exact_mod_cast hI)
  have hMI : (M : E) ∈ ((I : FractionalIdeal (𝓞 E)⁰ E) * I' : FractionalIdeal (𝓞 E)⁰ E) := by
    rw [← FractionalIdeal.coeIdeal_mul, hI, FractionalIdeal.mem_coeIdeal]
    exact ⟨M, Ideal.mem_span_singleton_self _, map_natCast _ _⟩
  have hres := det_sub_one_mem F (I : FractionalIdeal (𝓞 E)⁰ E) FractionalIdeal.coeIdeal_le_one cI hc
    (Q * G * P) (fun i j => by
      have e1 : (I : FractionalIdeal (𝓞 E)⁰ E) * (cI i * (cI j)⁻¹) =
          (I * I' * cI i) * (cI j)⁻¹ * (I' : FractionalIdeal (𝓞 E)⁰ E)⁻¹ := by field_simp
      rw [e1]
      refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ hI0 fun b hb => ?_
      refine mem_adelicCompletion_mul_inv_fractionalIdeal F _ _ _ (hc j) fun x hx => ?_
      rw [FractionalIdeal.mem_coeIdeal] at hb
      obtain ⟨b, hb, rfl⟩ := hb
      obtain ⟨w, hw, hw'⟩ := hg b hb (x • e j) (by
        rw [hL]
        intro a
        by_cases ha : j = a
        · subst ha
          simpa using hx
        · simpa [Finsupp.single_apply, ha] using (cI a).zero_mem)
      have e2 : fv F (b • x • e j) = P *ᵥ Pi.single j
          (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E b)) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) := by
        funext a
        rw [Matrix.mulVec_single]
        simp [P, fv, Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc]
      have e3 : (Q * G * P - 1) *ᵥ Pi.single j
          (((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (algebraMap (𝓞 E) E b)) * (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x) =
          M • (Q *ᵥ w) := by
        rw [← Matrix.mulVec_smul, ← hw', e2, Matrix.mulVec_sub, Matrix.sub_mulVec, Matrix.mulVec_mulVec,
          Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQP]
      have e4 := congrFun e3 i
      rw [Matrix.mulVec_single, Pi.smul_apply, MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op] at e4
      have h5 := (adelicCompletion_fractionalIdeal_properties F E).1 _ _ _ (one_tmul_mem_adelicCompletionOfElementSet F hMI) _ (key' w hw i)
      convert h5 using 1
      rw [mul_assoc]
      refine e4.trans ?_
      rw [Pi.smul_apply, nsmul_eq_mul]
      congr 1
      exact (map_natCast (Algebra.TensorProduct.includeRight (R := F) (A := FiniteAdeleRing (𝓞 F) F) (B := E)) M).symm)
  rw [hkdet] at hres
  exact adelicCompletionOfElementSet_mono F (fun x hx => (FractionalIdeal.mem_coeIdeal _).1 hx) hres

end Det

theorem exists_matrix_split {E : Type} [Field E] [NumberField E] {n p q : ℕ} (hn : n = p + q) {La : Type}
    [AddCommGroup La] [Module (𝓞 E) La] [Module.Finite (𝓞 E) La] (φ : La →ₗ[𝓞 E] (Fin n → E))
    (hsp : Submodule.span E (Set.range φ) = ⊤) (Lp Lm : Submodule (𝓞 E) La) (hs : Lp ⊔ Lm = ⊤)
    (hp : Module.finrank (𝓞 E) Lp = p) (hq : Module.finrank (𝓞 E) Lm = q) (x y : E) :
    ∃ S : Matrix (Fin n) (Fin n) E, S.det = x ^ p * y ^ q ∧ (∀ a ∈ Lp, S *ᵥ φ a = x • φ a) ∧
      ∀ b ∈ Lm, S *ᵥ φ b = y • φ b := by
  have hle : ∀ (L : Submodule (𝓞 E) La) (m : ℕ), Module.finrank (𝓞 E) L = m →
      Module.finrank E (Submodule.span E (φ '' L)) ≤ m := by
    intro L m hm
    obtain ⟨v, c, hc, hv⟩ := GlobalTheory.CM.LatData.exists_span_smul_mem hm
    have h1 : Submodule.span E (φ '' L) ≤ Submodule.span E (Set.range fun i => φ (v i)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨a, ha, rfl⟩
      obtain ⟨s, hs⟩ := hv ⟨a, ha⟩
      have hc' : (c : E) ≠ 0 := by simpa using hc
      have e : (c : E) • φ a = ∑ i, (s i : E) • φ (v i) := by
        have := congrArg (fun z : L => φ z) hs
        simp only [Submodule.coe_smul, Submodule.coe_sum, map_smul, map_sum] at this
        exact this
      rw [SetLike.mem_coe, ← Submodule.smul_mem_iff _ hc', e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
    exact (Submodule.finrank_mono h1).trans ((finrank_range_le_card _).trans (by simp))
  set Wp := Submodule.span E (φ '' Lp)
  set Wm := Submodule.span E (φ '' Lm)
  have hsup : Wp ⊔ Wm = ⊤ := by
    rw [eq_top_iff, ← hsp, Submodule.span_le]
    rintro _ ⟨v, rfl⟩
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 (hs ▸ Submodule.mem_top : v ∈ Lp ⊔ Lm)
    rw [map_add]
    exact Submodule.add_mem_sup (Submodule.subset_span ⟨a, ha, rfl⟩) (Submodule.subset_span ⟨b, hb, rfl⟩)
  have h1 : Module.finrank E Wp ≤ p := hle Lp p hp
  have h2 : Module.finrank E Wm ≤ q := hle Lm q hq
  have h3 := Submodule.finrank_sup_add_finrank_inf_eq Wp Wm
  rw [hsup, finrank_top, Module.finrank_fin_fun] at h3
  have hc : IsCompl Wp Wm := ⟨disjoint_iff.2 (Submodule.finrank_eq_zero.1 (by omega)), codisjoint_iff.2 hsup⟩
  let e := Submodule.prodEquivOfIsCompl Wp Wm hc
  let f : (Fin n → E) →ₗ[E] (Fin n → E) :=
    (e : (Wp × Wm) →ₗ[E] (Fin n → E)) ∘ₗ ((x • LinearMap.id).prodMap (y • LinearMap.id)) ∘ₗ (e.symm : (Fin n → E) →ₗ[E] (Wp × Wm))
  refine ⟨LinearMap.toMatrix' f, ?_, fun a ha => ?_, fun b hb => ?_⟩
  · rw [LinearMap.det_toMatrix', LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_smul, LinearMap.det_smul,
      LinearMap.det_id, LinearMap.det_id, mul_one, mul_one, show Module.finrank E Wp = p by omega,
      show Module.finrank E Wm = q by omega]
  · rw [LinearMap.toMatrix'_mulVec]
    have := Submodule.prodEquivOfIsCompl_symm_apply_left Wp Wm hc ⟨φ a, Submodule.subset_span ⟨a, ha, rfl⟩⟩
    simp only [f, e, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [this]
    simp
  · rw [LinearMap.toMatrix'_mulVec]
    have := Submodule.prodEquivOfIsCompl_symm_apply_right Wp Wm hc ⟨φ b, Submodule.subset_span ⟨b, hb, rfl⟩⟩
    simp only [f, e, LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [this]
    simp

theorem mulVec_congr {R : Type} [CommRing R] {n M : ℕ} {A' A B S G : Matrix (Fin n) (Fin n) R} (hinv : A' * A = 1)
    {t y y' w w' z w₀ : Fin n → R} (e : y - G *ᵥ t = M • w) (e' : y' - A *ᵥ t = M • w')
    (e₁ : y' = B *ᵥ (S *ᵥ y) + M • z) (e₀ : A *ᵥ w₀ = w' - B *ᵥ (S *ᵥ w) - z) :
    (A' * B * S * G) *ᵥ t - t = M • w₀ := by
  have h : ∀ v, A' *ᵥ (A *ᵥ v) = v := fun v => by rw [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec]
  have h2 : B *ᵥ (S *ᵥ (G *ᵥ t)) - A *ᵥ t = M • (A *ᵥ w₀) := by
    rw [sub_eq_iff_eq_add', ← sub_eq_iff_eq_add] at e e'
    rw [← e, ← e', e₁, e₀, Matrix.mulVec_sub, Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul, smul_sub,
      smul_sub]
    abel
  have h3 := congrArg (fun v => A' *ᵥ v) h2
  simp only [Matrix.mulVec_sub, Matrix.mulVec_smul, h] at h3
  simpa only [Matrix.mulVec_mulVec, Matrix.mul_assoc] using h3

theorem gLat_eq_of_finCong {D : D7} (V : HSp D) (u : GA D V) (h : FinCong V 1 u) (h' : FinCong V 1 u⁻¹) :
    gLat V u = latHat V := by
  have key : ∀ k, FinCong V 1 k → ∀ z ∈ latHat V, (finHom V k).1 *ᵥ z ∈ latHat V := fun k hk z hz => by
    obtain ⟨y, hy, e⟩ := hk z hz
    rw [one_smul, sub_eq_iff_eq_add] at e
    rw [e]
    exact add_mem hy hz
  refine Set.Subset.antisymm ?_ fun z hz => ⟨_, key _ h' z hz, ?_⟩
  · rintro _ ⟨z, hz, rfl⟩
    exact key u h z hz
  · rw [Matrix.mulVec_mulVec, ← Units.val_mul, ← map_mul, mul_inv_cancel, map_one, Units.val_one, Matrix.one_mulVec]

set_option maxHeartbeats 1000000 in

theorem exists_of_matched {D : D7} (V : HSp D) (g g' δ : GA D V) (δ' : GL (Fin V.rank) D.host.E)
    (S : Matrix (Fin V.rank) (Fin V.rank) D.host.E) (M : ℕ) (hM : M ≠ 0) (I I' : Ideal (𝓞 D.host.E))
    (hI : I * I' = Ideal.span {(M : 𝓞 D.host.E)}) (hδ : IsRat V δ δ')
    (hΛ : ∀ v, v ∈ latG V g ↔ (δ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v ∈ latG V g')
    (hS : ∀ v ∈ latG V g, S *ᵥ v ∈ latG V g)
    (hm : ∀ b ∈ I', ∀ x ∈ latG V 1, ∃ y y' : Fin V.rank → D.host.E,
      (∃ w ∈ latGHat V g, finVec V y - (finHom V g).1 *ᵥ finVec V (b • x) = M • w) ∧
      (∃ w ∈ latGHat V g', finVec V y' - (finHom V g').1 *ᵥ finVec V (b • x) = M • w) ∧
      ∃ e ∈ latG V g', y' = (δ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ (S *ᵥ y) + M • e) :
    ∃ u : GA D V, gLat V u = latHat V ∧ finHom V g' * finHom V u = finHom V δ * finHom V g ∧
      (finHom V u).1.det * ((1 : Af D.host.F) ⊗ₜ[D.host.F] S.det) - 1 ∈
        GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (I : Set (𝓞 D.host.E))) := by
  obtain ⟨m1, -, -, m4⟩ := GlobalTheory.T.adelicUnitaryLattice_rationalTranslate_invariance D V
  obtain ⟨-, -, -, -, r5⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨m1, m2⟩ := m1 δ δ' g hδ
  have hL : latG V g' = latG V (δ * g) := by
    ext v
    have e : v = (δ' : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ
        (((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ v) := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    rw [e, ← hΛ, ← m1]
  have hu : finHom V g' * finHom V (g'⁻¹ * (δ * g)) = finHom V δ * finHom V g := by
    rw [← map_mul, mul_inv_cancel_left, map_mul]
  refine ⟨g'⁻¹ * (δ * g), gLat_eq_of_finCong V _ (m4 _ _ hL) ?_, hu, ?_⟩
  · rw [mul_inv_rev, inv_inv]
    exact m4 _ _ hL.symm
  obtain ⟨f1, f2, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V 1
  obtain ⟨-, -, -, -, a5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g
  obtain ⟨-, -, -, b4, b5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V g'
  obtain ⟨-, -, -, -, c5, -⟩ := GlobalTheory.T.adelicElementLattice_full_and_completion D V (δ * g)
  let SA := S.map (inclR (F := D.host.F) (Af D.host.F))
  have hd := det_sub_one_mem_of_half D.host.F (latG V 1) f1 f2
    ((finHom V g'⁻¹).1 * (finHom V δ).1 * SA * (finHom V g).1) M hM I I' hI (fun b hb x hx => by
      obtain ⟨y, y', ⟨w, hw, e⟩, ⟨w', hw', e'⟩, z, hz, ez⟩ := hm b hb x hx
      have h1 : (finHom V δ).1 *ᵥ (SA *ᵥ w) ∈ latGHat V g' := by
        rw [b5, hL, ← c5, ← m2, a5]
        exact GlobalTheory.RecDict.coset_mulVec_mem_hat _ S hS w (a5 ▸ hw)
      have h2 : finVec V z ∈ latGHat V g' := by
        rw [b5]
        exact GlobalTheory.AdLat.Half.fv_mem_hat' _ _ hz
      have h3 : w' - (finHom V δ).1 *ᵥ (SA *ᵥ w) - finVec V z ∈ (latGHat V g' : Set _) :=
        sub_mem (sub_mem hw' h1) h2
      rw [b4] at h3
      obtain ⟨w0, hw0, e0⟩ := h3
      refine ⟨w0, hw0, ?_⟩
      have hinv : (finHom V g'⁻¹).1 * (finHom V g').1 = 1 := by
        rw [← Units.val_mul, ← map_mul, inv_mul_cancel, map_one, Units.val_one]
      have e1 : finVec V y' = (finHom V δ).1 *ᵥ (SA *ᵥ finVec V y) + M • finVec V z := by
        have e2 : SA *ᵥ finVec V y = finVec V (S *ᵥ y) := GlobalTheory.RecDict.coset_fv_mulVec S y
        rw [e2, (r5 δ δ' hδ).1, ez]
        funext i
        simp only [finVec, Pi.smul_apply, Pi.add_apply, TensorProduct.tmul_add]
        congr 1
        exact map_nsmul (TensorProduct.mk D.host.F (Af D.host.F) D.host.E 1) M _
      exact mulVec_congr hinv e e' e1 e0)
  have e : SA.det = (1 : Af D.host.F) ⊗ₜ[D.host.F] S.det :=
    ((inclR (F := D.host.F) (Af D.host.F)).map_det S).symm
  convert hd using 2
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, ← e]
  simp only [Matrix.det_mul]
  ring

set_option maxHeartbeats 2000000 in

theorem marking_of_conjugate : ∀ (D : D7) (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (V : HSp D) (r : ℕ) (C : Ctx Xo c σ V r), C.OK → (Dw.p = 0 ∨ Dw.q = 0 ∨ 3 ≤ Dw.p + Dw.q) → ∀ τ : ℂ ≃+* ℂ, τ H.rt0 = H.rt0 → ∀ (Cv : Curve H) (io : Cv.P.A.left ⟶ Cv.P.A.left) (s : ℤ × ℤ) (π : Fin C.F.n → Fin C.F.n), Cv.ActsBy τ io l.M s → ConjugationPermutesPeriods C.F τ π → ∀ h γ k h' γ', C.Mark h k γ → C.Mark h' (π k) γ' → ∃ δ ∈ GQ V, ∃ u : GA D V, gLat V u = latHat V ∧ finHom V (γ' * h') * finHom V u = finHom V δ * finHom V (γ * h) ∧ ((Matrix.GeneralLinearGroup.det (finHom V (u)) : (Af D.host.F ⊗[D.host.F] D.host.E)ˣ) : (Af D.host.F ⊗[D.host.F] D.host.E)) * ((1 : Af D.host.F) ⊗ₜ[D.host.F] ((wE H s ^ Dw.p * H.bar (wE H s) ^ Dw.q : 𝓞 D.host.E) : D.host.E)) - 1 ∈ GlobalTheory.AdLat.hat1 D.host.F ((algebraMap (𝓞 D.host.E) D.host.E) '' (l.Mb : Set (𝓞 D.host.E))) := by
  intro D H Dw l Xo c σ V r C hC hsig τ hτ Cv io s π hact hπ h γ k h' γ' hm hm'
  obtain rfl : V.rank = r := C.hr
  have hty := (GlobalTheory.T.relabelEmbeddings_good_bijective_conj_compat _ H l c σ hC.good).2.2.2 Dw C.g C.e
  obtain ⟨P, hP, hsplit⟩ := GlobalTheory.CompRat.exists_isSplit_period _ H Dw l Xo _ C.g _ C.F hC.pos hC.good hty hC.lA
    (hsig.imp_right (Or.imp_right fun h3 => ⟨h3, GlobalTheory.RankOneDatum.exists_datum_rank_one D H Dw V C.ι hC.iota hC.pos⟩)) k
  obtain ⟨P', hP', hu⟩ := hπ k P hP
  obtain ⟨Φ, hiso, -, -, hΦ⟩ := GlobalTheory.CompRat.marking_conj _ H Dw l Xo _ C.g _ C.F hC.pos hC.good hty hC.lA τ hτ Cv io hact.1
    k P hP (π k) P' hP' hsplit hu s hact
  have hG : ∀ k, (C.M.X k).Gm = -V.gramᵀ := fun k => (hC.modelW k).1
  let φ : ∀ k, (C.F.Di k).La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E) := fun k =>
    (C.M.X k).Λ.subtype ∘ₗ (C.M.φ k).toLinearMap
  have hr : ∀ k, Set.range (φ k) = (C.M.X k).Λ := fun k => by
    ext v
    exact ⟨by rintro ⟨a, rfl⟩; exact (C.M.φ k a).2, fun hv => ⟨(C.M.φ k).symm ⟨v, hv⟩,
      congrArg Subtype.val ((C.M.φ k).apply_symm_apply ⟨v, hv⟩)⟩⟩
  have hmod : ∀ k, Function.Injective (φ k) ∧ Submodule.span D.host.E (Set.range (φ k)) = ⊤ ∧
      (∀ a b, cc ((-V.gramᵀ) a b) = (-V.gramᵀ) b a) ∧ (-V.gramᵀ).det ≠ 0 ∧
      ∀ x y, (((C.F.Di k).EF x y : ℤ) : ℚ) =
        Algebra.trace ℚ D.host.E (-(-D.host.xi0) * herm (-V.gramᵀ) (φ k x) (φ k y)) := fun k =>
    ⟨Subtype.val_injective.comp (C.M.φ k).injective, by rw [hr]; exact (C.M.X k).Λ_span,
      hG k ▸ (C.M.X k).Gm_herm, hG k ▸ (C.M.X k).Gm_det, fun x y => by
        rw [← (hC.modelW k).2, ← hG k]; exact hC.base.ef k x y⟩
  obtain ⟨δ', hδ1, hδ2⟩ := GlobalTheory.IsoExt.exists_unitary_of_isometry _ H _ _ _ (-(-D.host.xi0)) (-V.gramᵀ) (φ k) (φ (π k)) Φ
    (by
      have := (C.M.X k).ξ0_im
      rw [(hC.modelW k).2] at this
      simp only [cc, map_neg] at this ⊢
      rw [this]) (hmod k) (hmod (π k)) hiso
  obtain ⟨r1, -, r3, -⟩ := GlobalTheory.T.rational_points_adelicUnitary_eq_unitary D V
  obtain ⟨δ, hδ⟩ := r3 δ' hδ1
  have := (C.F.Di k).fin
  obtain ⟨hp, hq⟩ := GlobalTheory.CM.LatData.finrank_lat hP (by rw [(C.F.sig k).1, (C.F.sig k).2]; exact hty) one_pos
    (fun a => by rw [show _ ⊔ _ = ⊤ from hsplit]; trivial)
  obtain ⟨S, hdet, hSp, hSm⟩ := exists_matrix_split hC.base.rank (φ k) (hmod k).2.1 _ _ hsplit
    (hp.trans (C.F.sig k).1) (hq.trans (C.F.sig k).2) (wE H s : D.host.E) (H.bar (wE H s) : D.host.E)
  have hS : ∀ a ∈ GlobalTheory.PureType.lat hP H.rt0, ∀ b ∈ GlobalTheory.PureType.lat hP (-H.rt0),
      S *ᵥ φ k (a + b) = φ k (wE H s • a + H.bar (wE H s) • b) := fun a ha b hb => by
    rw [map_add, Matrix.mulVec_add, hSp a ha, hSm b hb, map_add, map_smul, map_smul]
    rfl
  have hdec : ∀ v : (C.F.Di k).La, ∃ a ∈ GlobalTheory.PureType.lat hP H.rt0, ∃ b ∈ GlobalTheory.PureType.lat hP (-H.rt0), a + b = v :=
    fun v => Submodule.mem_sup.1 (by rw [show _ ⊔ _ = ⊤ from hsplit]; trivial)
  have hL : Set.range (φ k) = latG V (γ * h) := (hr k).trans (hm.2.1.trans (Set.image_id _))
  have hL' : Set.range (φ (π k)) = latG V (γ' * h') := (hr (π k)).trans (hm'.2.1.trans (Set.image_id _))
  obtain ⟨u, h1, h2, h3⟩ := exists_of_matched V (γ * h) (γ' * h') δ δ' S l.M (by have := l.three_le; omega) l.Mb _
    l.prod hδ (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hL, ← hL']
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨_, hδ2 a⟩
      · rintro ⟨a, ha⟩
        refine ⟨Φ.symm a, ?_⟩
        have e := hδ2 (Φ.symm a)
        rw [LinearEquiv.apply_symm_apply, ha] at e
        have e' := congrArg (fun t => ((δ'⁻¹ : GL (Fin V.rank) D.host.E) : Matrix (Fin V.rank) (Fin V.rank) D.host.E) *ᵥ t) e
        simpa only [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec] using e'.symm)
    (fun v => by
      rw [← SetLike.mem_coe, ← SetLike.mem_coe, ← hL]
      rintro ⟨v, rfl⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := hdec v
      exact ⟨_, (hS a ha b hb).symm⟩)
    (fun b hb x hx => by
      rw [← hC.iota.emb.2] at hx
      obtain ⟨x, rfl⟩ := hx
      have hv : b • x ∈ l.Mb.map (H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) • (⊤ : Submodule (𝓞 D.host.E) Dw.La) :=
        Submodule.smul_mem_smul hb trivial
      rw [← map_smul]
      refine ⟨φ k (C.F.t k (b • x)), φ (π k) (C.F.t (π k) (b • x)), hm.2.2 _ hv, hm'.2.2 _ hv, ?_⟩
      obtain ⟨a, ha, a', ha', e⟩ := hdec (C.F.t k (b • x))
      obtain ⟨z, hz⟩ := hΦ _ hv a ha a' ha' e.symm
      refine ⟨φ (π k) z, by rw [← SetLike.mem_coe, ← hL']; exact ⟨z, rfl⟩, ?_⟩
      rw [hz, ← e, hS a ha a' ha', map_add, map_nsmul, hδ2])
  refine ⟨δ, (r1 δ).2 ⟨δ', hδ⟩, u, h1, h2, ?_⟩
  rw [hdet] at h3
  rw [RingOfIntegers.coe_eq_algebraMap, map_mul, map_pow, map_pow]
  exact h3

end GlobalTheory.ConjMark
