import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSymplecticBasisOfSelfD
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharOfTrace
import Development.AbelianVarietyTheory.Proofs.HeightProofs.EmbeddingXiZeroNeZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.StdCharFinitePartRationalEqExpTrace
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.RationalHermitianRankOneLatticeSelfDual
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.SmulMemOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsInvariantNatLengthLattice
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.ModelLatA
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalToGlobal.BesselHermitianTheta.LemmasSign

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.ThFr
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate

namespace GlobalTheory.Ker.Inhab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open ReciprocityTheory.ChartRestriction.G.PullbackSections.PfModelLatA

variable {D : D7}

def mulAA (D : D7) {k : ℕ} (L : Lt D.host.E k) : Lt D.host.E k :=
  Submodule.span (𝓞 D.host.E) {u | ∃ a : D.host.E, a ∈ D.host.AA ∧ ∃ t ∈ L, u = a • t}

theorem smul_mem_mulAA {k : ℕ} {L : Lt D.host.E k} {a : D.host.E} (ha : a ∈ D.host.AA)
    {t : Fin k → D.host.E} (ht : t ∈ L) : a • t ∈ mulAA D L :=
  Submodule.subset_span ⟨a, ha, t, ht, rfl⟩

theorem isAA_mulAA {k : ℕ} (L : Lt D.host.E k) : IsAA (mulAA D L) L := by
  intro v
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem v hv => exact AddSubgroup.subset_closure hv
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | smul c v _ hv =>
      clear * - hv
      induction hv using AddSubgroup.closure_induction with
      | mem w hw =>
        obtain ⟨a, ha, t, ht, rfl⟩ := hw
        exact AddSubgroup.subset_closure ⟨a, ha, c • t, L.smul_mem c ht, smul_comm _ _ _⟩
      | zero => rw [smul_zero]; exact zero_mem _
      | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
      | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  · intro hv
    exact (AddSubgroup.closure_le (mulAA D L).toAddSubgroup).2 Submodule.subset_span hv

theorem mulAA_fg {k : ℕ} {L : Lt D.host.E k} (hL : L.FG) : (mulAA D L).FG := by
  have h := Submodule.FG.map₂ (Algebra.lsmul (𝓞 D.host.E) (𝓞 D.host.E) (Fin k → D.host.E) :
      D.host.E →ₐ[𝓞 D.host.E] _).toLinearMap
    (FractionalIdeal.fg_of_isNoetherianRing le_rfl D.host.AA) hL
  rw [Submodule.map₂_eq_span_image2] at h
  rw [mulAA]
  convert h using 2
  ext u
  exact ⟨fun ⟨a, ha, t, ht, e⟩ => ⟨a, ha, t, ht, e.symm⟩, fun ⟨a, ha, t, ht, e⟩ => ⟨a, ha, t, ht, e.symm⟩⟩

theorem mulAA_span {k : ℕ} {L : Lt D.host.E k} (hL : Submodule.span D.host.E (L : Set (Fin k → D.host.E)) = ⊤) :
    Submodule.span D.host.E (mulAA D L : Set (Fin k → D.host.E)) = ⊤ := by
  obtain ⟨a, ha0, ha⟩ := FractionalIdeal.exists_ne_zero_mem_isInteger
    (AA_ne_zero Formalism.IndefR.Fin.factPrincipalDatum D)
  have h0 : algebraMap (𝓞 D.host.E) D.host.E a ≠ 0 := by simpa using ha0
  rw [eq_top_iff, ← hL, Submodule.span_le]
  intro t ht
  have := Submodule.smul_mem _ (algebraMap (𝓞 D.host.E) D.host.E a)⁻¹
    (Submodule.subset_span (R := D.host.E) (smul_mem_mulAA ha ht))
  rwa [smul_smul, inv_mul_cancel₀ h0, one_smul] at this

theorem herm_transpose (T : HSp D) (x y : Fin T.rank → D.host.E) :
    herm T.gramᵀ x y = ∑ i, ∑ j, star (y i) * T.gram i j * x j := by
  rw [herm, Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Matrix.transpose_apply, show cc (y a) = star (y a) from rfl]
  ring

theorem mem_iff_herm {T : HSp D} {L : Lt D.host.E T.rank} (hL : IsSelfDualC T L) (x : Fin T.rank → D.host.E) :
    x ∈ L ↔ ∀ y ∈ L, IsIntegral ℤ (herm T.gramᵀ x y) := by
  rw [hL.2]
  refine forall₂_congr fun y _ => ?_
  rw [herm_transpose]
  exact ⟨fun ⟨b, hb⟩ => hb ▸ b.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩

theorem herm_mem_NAA {T : HSp D} {L : Lt D.host.E T.rank} (hL : IsSelfDualC T L) {x y : Fin T.rank → D.host.E}
    (hx : x ∈ mulAA D L) (hy : y ∈ mulAA D L) : herm T.gramᵀ x y ∈ NAA D := by
  rw [isAA_mulAA L] at hx hy
  induction hx using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, s, hs, rfl⟩ := hx
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨b, hb, t, ht, rfl⟩ := hy
      rw [herm_smul_left, herm_smul_right, ← mul_assoc, mul_comm, cc_eq_conj]
      exact Submodule.smul_mem (NAA D) (⟨_, (mem_iff_herm hL s).1 hs t ht⟩ : 𝓞 D.host.E)
        (FractionalIdeal.mul_mem_mul ha (conj_mem_AAbar D hb))
    | zero => simp [herm, cc]
    | add u v _ _ hu hv => rw [herm_add_right]; exact add_mem hu hv
    | neg u _ hu =>
      rw [← neg_one_smul D.host.E u, herm_smul_right, cc, map_neg, map_one, neg_one_mul]
      exact neg_mem hu
  | zero => simp [herm]
  | add u v _ _ hu hv => rw [herm_add_left]; exact add_mem hu hv
  | neg u _ hu => rw [← neg_one_smul D.host.E u, herm_smul_left, neg_one_mul]; exact neg_mem hu

theorem mem_mulAA_of_trace {T : HSp D} {L : Lt D.host.E T.rank} (hL : IsSelfDualC T L)
    {x : Fin T.rank → D.host.E}
    (h : ∀ y ∈ mulAA D L, ∃ n : ℤ, Algebra.trace ℚ D.host.E (D.host.xi0 * herm T.gramᵀ x y) = n) :
    x ∈ mulAA D L := by
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  have h1 : ∀ t ∈ L, herm T.gramᵀ x t ∈ D.host.AA := fun t ht =>
    GlobalTheory.LatVac.RatDual.mem_AA_of_trace D _ fun a ha => by
      have := h _ (smul_mem_mulAA ha ht)
      rwa [herm_smul_right] at this
  have h2 : ∀ b ∈ D.host.AA⁻¹, b • x ∈ L := fun b hb => (mem_iff_herm hL _).2 fun t ht => by
    obtain ⟨c, hc⟩ := int_of_AA_mul hP D (h1 t ht) hb
    rw [herm_smul_left, mul_comm, ← hc]
    exact c.2
  have h3 : (1 : D.host.E) ∈ D.host.AA * D.host.AA⁻¹ := by
    rw [AA_mul_inv hP D]; exact FractionalIdeal.one_mem_one _
  have key := FractionalIdeal.mul_induction_on (C := fun w : D.host.E => w • x ∈ mulAA D L) h3
    (fun a ha b hb => by
      show (a * b) • x ∈ _
      rw [mul_smul]
      exact smul_mem_mulAA ha (h2 b hb))
    (fun u v hu hv => by
      show (u + v) • x ∈ _
      rw [add_smul]
      exact add_mem hu hv)
  simpa using key

theorem selfD_mulAA {T : HSp D} {L : Lt D.host.E T.rank} (hL : IsSelfDualC T L) (X : Data D.host.E T.rank)
    (hG : X.Gm = T.gramᵀ) (hκ : X.κ0 = 2 * D.host.xi0) : SelfD X (mulAA D L) := by
  have e : ∀ x y, EF X x y = -Algebra.trace ℚ D.host.E (D.host.xi0 * herm T.gramᵀ x y) := fun x y => by
    rw [EF_def, hG, hκ, mul_div_cancel_left₀ _ two_ne_zero, neg_mul, map_neg]
  refine ⟨mulAA_fg hL.1.fg, fun x => ⟨fun hx y hy => ?_, fun h => mem_mulAA_of_trace hL fun y hy => ?_⟩⟩
  · obtain ⟨n, hn⟩ := trace_int_of_mem Formalism.IndefR.Fin.factPrincipalDatum D (herm_mem_NAA hL hx hy)
    exact ⟨-n, by rw [e, hn, Int.cast_neg]⟩
  · obtain ⟨n, hn⟩ := h y hy
    exact ⟨-n, by rw [Int.cast_neg, ← hn, e, neg_neg]⟩

theorem exists_nat_clear {E : Type} [Field E] [NumberField E]
    (I : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) : ∃ N : ℕ, 0 < N ∧ ∀ z ∈ I, IsIntegral ℤ ((N : E) * z) := by
  obtain ⟨a, ha, h⟩ := I.isFractional
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {a}))
  refine ⟨Ideal.absNorm (Ideal.span {a}), Nat.pos_of_ne_zero ?_, fun z hz => ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact nonZeroDivisors.ne_zero ha
  · obtain ⟨b, hb⟩ := h z hz
    have e : ((Ideal.absNorm (Ideal.span {a}) : ℕ) : E) * z = algebraMap (𝓞 E) E (c * b) := by
      rw [map_mul, hb, Algebra.smul_def, ← mul_assoc, ← map_mul, hc, map_natCast]
    rw [e]
    exact (c * b).2

theorem exists_on_basis {r p q : ℕ} (hr : p + q = r) {G : Matrix (Fin r) (Fin r) ℂ}
    (h : Formalism.UG.HasSignature G p q) :
    ∃ B : Matrix (Fin r) (Fin r) ℂ, B.det ≠ 0 ∧
      Bᴴ * G * B = Matrix.diagonal fun a : Fin r => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
  subst hr
  obtain ⟨e, U, hU⟩ := h
  have hU' : (U : Matrix _ _ ℂ)ᴴ * G.reindex e e * (U : Matrix _ _ ℂ) = Formalism.UG.Jpq p q := hU
  have h1 : ((U : Matrix _ _ ℂ).submatrix e finSumFinEquiv.symm)ᴴ * G *
      (U : Matrix _ _ ℂ).submatrix e finSumFinEquiv.symm =
      Matrix.diagonal fun a : Fin (p + q) => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := by
    have h2 : G = (G.reindex e e).submatrix e e := by simp
    rw [h2, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hU']
    ext a b
    obtain ⟨a, rfl⟩ := finSumFinEquiv.surjective a
    obtain ⟨b, rfl⟩ := finSumFinEquiv.surjective b
    rw [Matrix.submatrix_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply, Matrix.diagonal_apply]
    simp only [EmbeddingLike.apply_eq_iff_eq]
    rcases a with a | a <;> rcases b with b | b <;>
      simp [Formalism.UG.Jpq, FD.sgn, Matrix.one_apply]
    all_goals split_ifs <;> simp
  refine ⟨_, fun h0 => ?_, h1⟩
  have h2 := congrArg Matrix.det h1
  rw [Matrix.det_mul, h0, mul_zero, Matrix.det_diagonal] at h2
  refine Finset.prod_ne_zero_iff.2 (fun a _ => ?_) h2.symm
  unfold FD.sgn
  split_ifs <;> norm_num

theorem gram_conj {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (B : Matrix (Fin r) (Fin r) ℂ) (hG : ∀ a b, conj (τ (G a b)) = τ (G b a)) :
    FD.gram (ComplexEmbedding.conjugate τ) Gᵀ (B.map conj) = Bᴴ * G.map τ * B := by
  ext a b
  simp only [FD.gram, hermC, FD.col, Matrix.of_apply, Matrix.map_apply, Matrix.mul_apply,
    Matrix.transpose_apply, ComplexEmbedding.conjugate_coe_eq, hG, Complex.conj_conj,
    Matrix.conjTranspose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  rfl

theorem exists_ctx : ∀ (D : D7) (S T : HSp D) (p q : ℕ) (L : Lt D.host.E T.rank), S.gram = 1 → Even S.rank →
    p + q = T.rank → T.SigOK → (∀ τ, T.sig (tauE D τ) = (p, q)) → IsSelfDualC T L →
    ∃ C : Ctx S T, C.X.p0 = p ∧ C.q0 = q ∧ IsAA C.X.Λ L ∧ ∃ B : C.Bas, C.IsB B := by
  classical
  intro D S T p q L hS hev hr hsig hpq hL
  have hP := Formalism.IndefR.Fin.factPrincipalDatum
  obtain ⟨ψ, hψ⟩ := GlobalTheory.StdAdelicChar.exists_isStdChar D
  obtain ⟨θ, hθ⟩ := GlobalTheory.DualPairCompare.exists_infFam D
  have hcc : ∀ σ : D.host.E →+* ℂ, ComplexEmbedding.conjugate (ComplexEmbedding.conjugate σ) = σ :=
    fun σ => star_star σ
  have hB : ∀ τ, ∃ B : Matrix (Fin T.rank) (Fin T.rank) ℂ, B.det ≠ 0 ∧
      Bᴴ * gramAt D T τ * B = Matrix.diagonal fun a : Fin T.rank => ((FD.sgn p (a : ℕ) : ℝ) : ℂ) := fun τ => by
    have := hsig (tauE D τ)
    rw [hpq τ] at this
    exact exists_on_basis hr this
  choose B hB0 hB using hB
  obtain ⟨N, hN, hNi⟩ := exists_nat_clear
    (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 D.host.E)) (2 * D.host.xi0) * (D.host.AA * D.host.AAbar))
  set Ψ : Finset (D.host.E →+* ℂ) := Finset.univ.image fun τ => ComplexEmbedding.conjugate (tauE D τ) with hΨ
  have hmem : ∀ σ, σ ∈ Ψ ↔ ∃ τ, tauE D τ = ComplexEmbedding.conjugate σ := fun σ => by
    simp only [hΨ, Finset.mem_image, Finset.mem_univ, true_and]
    exact exists_congr fun τ => ⟨fun h => by rw [← h, hcc], fun h => by rw [h, hcc]⟩
  obtain ⟨X, hXΨ, hG, hp, hΛ, -, hκ, -⟩ := GlobalTheory.FlagData.exists_data GlobalTheory.latMinkowski D.host.E T.rank p 3 (3 * N)
    Ψ T.gramᵀ (mulAA D L) D.host.xi0 (2 * D.host.xi0)
    (fun σ => by
      rw [hmem, hmem, hcc, GlobalTheory.StdRat.tauE_cm D σ, not_not])
    (fun a b => GlobalTheory.LatVac.gram_star T b a)
    (by rw [Matrix.det_transpose]; exact (GlobalTheory.LatVac.gram_det_isUnit T).ne_zero)
    (by omega)
    (fun σ hσ => by
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hσ
      refine ⟨(B τ).map conj, ?_, ?_⟩
      · have := RingHom.map_det (starRingEnd ℂ) (B τ)
        rw [RingHom.mapMatrix_apply] at this
        rw [← this]
        simpa using hB0 τ
      · rw [gram_conj _ _ _ fun a b => ?_]
        · exact hB τ
        · rw [← IsCMField.complexEmbedding_complexConj]
          exact congrArg _ (GlobalTheory.LatVac.gram_star T a b))
    (mulAA_fg hL.1.fg) (mulAA_span hL.1.span_eq_top) le_rfl (conj_xi0_alt D) (cmHost_imaginaryGenerator_ne_zero hP D) (Or.inl rfl)
    (fun σ hσ => by
      obtain ⟨τ, -, rfl⟩ := Finset.mem_image.1 hσ
      have := xi_zero_im_pos D τ
      simp only [ComplexEmbedding.conjugate_coe_eq, map_mul, map_ofNat, Complex.mul_im, Complex.conj_im]
      norm_num
      exact this)
    (by omega)
    (fun x hx y hy => by
      have e : ((3 * N : ℕ) : D.host.E) / ((3 : ℕ) : D.host.E) = N := by
        rw [Nat.cast_mul, mul_div_cancel_left₀ _ (Nat.cast_ne_zero.2 (by norm_num))]
      rw [e, mul_assoc]
      exact hNi _ (FractionalIdeal.mul_mem_mul (FractionalIdeal.mem_spanSingleton_self _ _)
        (herm_mem_NAA hL hx hy)))
  obtain ⟨g, bas, idx, hs⟩ := exists_symplectic_basis_of_selfD _ _ X (hΛ ▸ selfD_mulAA hL X hG hκ)
  let e : D.what₂.Tau ≃ X.Ψ := Equiv.ofBijective
    (fun τ => ⟨ComplexEmbedding.conjugate (tauE D τ), hXΨ ▸ Finset.mem_image_of_mem _ (Finset.mem_univ τ)⟩)
    ⟨fun τ τ' h => GlobalTheory.StdRat.tauE_injective D (by
        have := congrArg (fun σ : X.Ψ => ComplexEmbedding.conjugate σ.1) h
        simpa only [hcc] using this),
      fun σ => by
        obtain ⟨τ, -, h⟩ := Finset.mem_image.1 (hXΨ ▸ σ.2 : σ.1 ∈ Ψ)
        exact ⟨τ, Subtype.ext h⟩⟩
  refine ⟨⟨ψ, hψ, θ, hθ, X, ⟨hS, hG, e, fun _ => rfl, hκ⟩, g, q, by rw [hp, hr], bas, idx, hs, hev⟩,
    hp, rfl, hΛ ▸ isAA_mulAA L, B, fun τ => ?_⟩
  rw [hB τ, sgnM]
  simp only [hp]

theorem selfDual_diag {E : Type} [Field E] [NumberField E] [StarRing E] {N : ℕ} (neg : Fin N → Bool)
    (G : Matrix (Fin N) (Fin N) E) (hG : ∀ i j, G i j = if i = j then (Examples₂.sgn (neg i) : E) else 0)
    (y : Fin N → E) : y ∈ Examples₂.stdLat N ↔
      ∀ x ∈ Examples₂.stdLat (E := E) N, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * G i j * y j := by
  have hm : ∀ x : Fin N → E, x ∈ Examples₂.stdLat N ↔ ∀ i, IsIntegral ℤ (x i) := fun x => by
    rw [Examples₂.stdLat, Module.Basis.mem_span_iff_repr_mem]
    exact forall_congr' fun i => ⟨fun ⟨b, hb⟩ => by rw [← show _ = x i from hb]; exact b.2, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  have hs : ∀ b, IsIntegral ℤ (Examples₂.sgn b : E) := fun b => by
    cases b
    · exact isIntegral_one
    · exact isIntegral_one.neg
  have hf : ∀ x : Fin N → E, ∑ i, ∑ j, star (x i) * G i j * y j = ∑ i, star (x i) * Examples₂.sgn (neg i) * y i := by
    intro x
    simp [hG]
  simp only [hf]
  refine (hm y).trans ⟨fun h x hx => ?_, fun h i => ?_⟩
  · have : IsIntegral ℤ (∑ i, star (x i) * Examples₂.sgn (neg i) * y i) :=
      IsIntegral.sum _ fun i _ => ((Examples₂.star_isIntegral _ ((hm x).1 hx i)).mul (hs _)).mul (h i)
    exact ⟨⟨_, this⟩, rfl⟩
  · obtain ⟨b, hb⟩ := h (Pi.single i 1) (Submodule.subset_span ⟨i, by simp⟩)
    rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)] at hb
    have : y i = Examples₂.sgn (neg i) * (b : E) := by
      rw [hb, Pi.single_eq_same, star_one, one_mul, ← mul_assoc, Examples₂.sgn_mul_self, one_mul]
    rw [this]
    exact (hs _).mul b.2

theorem isSelfDualC_std (D : D7) (N : ℕ) (neg : Fin N → Bool) (p q : ℕ) :
    IsSelfDualC (D := D) (Examples₂.stdSpace Examples₂.star_isIntegral N neg p q) (Examples₂.stdLat N) :=
  ⟨Examples₂.stdLat_isLattice N, selfDual_diag neg _ (Examples₂.stdSpace_gram_apply _ N neg p q)⟩

theorem hasSignature_diag (p q : ℕ) (G : Matrix (Fin (p + q)) (Fin (p + q)) ℂ)
    (hG : ∀ i j, G i j = if i = j then (Examples₂.sgn (decide (p ≤ (i : ℕ))) : ℂ) else 0) :
    Formalism.UG.HasSignature G p q := by
  refine ⟨(finSumFinEquiv (m := p) (n := q)).symm, 1, ?_⟩
  simp only [Units.val_one, Formalism.UG.cT_one, Matrix.one_mul, Matrix.mul_one]
  ext i j
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_symm, hG]
  simp only [EmbeddingLike.apply_eq_iff_eq]
  rcases i with a | a <;> rcases j with b | b
  · by_cases h : a = b <;> simp [Formalism.UG.Jpq, Examples₂.sgn, h]
  · simp [Formalism.UG.Jpq]
  · simp [Formalism.UG.Jpq]
  · by_cases h : a = b <;> simp [Formalism.UG.Jpq, Examples₂.sgn, h]

theorem sigOK_std (D : D7) (p q : ℕ) :
    (Examples₂.stdSpace (E := D.host.E) Examples₂.star_isIntegral (p + q) (fun i => decide (p ≤ (i : ℕ))) p q).SigOK := by
  intro τ
  refine hasSignature_diag p q _ fun i j => ?_
  refine (congrArg τ (Examples₂.stdSpace_gram_apply _ (p + q) _ p q i j)).trans ?_
  rw [apply_ite τ, Examples₂.map_sgn, map_zero]

theorem gram_pos (D : D7) (N : ℕ) : (Examples₂.posSpace (E := D.host.E) Examples₂.star_isIntegral N).gram = 1 := by
  ext1 i j
  exact (Examples₂.stdSpace_gram_apply (E := D.host.E) _ N (fun _ => false) N 0 i j).trans rfl

theorem exists_ctx_sig (D : D7) (n p q : ℕ) : ∃ (S T : HSp D) (C : Ctx S T), S.rank = 2 * n ∧ C.X.p0 = p ∧
    C.q0 = q ∧ S.SigOK ∧ T.SigOK ∧ ∃ B : C.Bas, C.IsB B := by
  obtain ⟨C, h1, h2, -, h3⟩ := exists_ctx D (Examples₂.posSpace Examples₂.star_isIntegral (2 * n))
    (Examples₂.stdSpace Examples₂.star_isIntegral (p + q) (fun i => decide (p ≤ (i : ℕ))) p q) p q (Examples₂.stdLat (p + q))
    (gram_pos D _) (even_two_mul n) rfl (sigOK_std D p q) (fun _ => rfl) (isSelfDualC_std D _ _ p q)
  exact ⟨_, _, C, rfl, h1, h2, Examples₂.posSpace_sigOK _ _, sigOK_std D p q, h3⟩

end GlobalTheory.Ker.Inhab

end
