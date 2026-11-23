import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IdempotentAdelesAndSmallAdelicMatrices
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUnitaryAdelicDecompositionSplitSupport
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit

namespace GlobalTheory.Ker.CutAt

section General

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep GlobalTheory.UnRep.SplitRep
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

omit [NumberField E] in
theorem isUnA_mul (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (a b : Matrix (Fin n) (Fin n) (RA F E))
    (ha : IsUnA c G a) (hb : IsUnA c G b) : IsUnA c G (a * b) := by
  intro x y
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  exact (ha _ _).trans (hb x y)

omit [NumberField E] in
theorem nsmul_mem_hat (L : Submodule (𝓞 E) (Fin n → E)) (M : ℕ) (J : Ideal (𝓞 E)) (hM : (M : 𝓞 E) ∈ J)
    {z : Fin n → RA F E} (hz : z ∈ hat F (L : Set (Fin n → E))) :
    M • z ∈ hat F ((J • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hz
    apply AddSubgroup.subset_closure
    refine ⟨a, ha, (M : 𝓞 E) • x, Submodule.smul_mem_smul hM hx, ?_⟩
    funext i
    rw [Pi.smul_apply, Pi.smul_apply, Nat.cast_smul_eq_nsmul, TensorProduct.tmul_smul]
  | zero => simp
  | add x y _ _ hx hy => simpa [smul_add] using AddSubgroup.add_mem _ hx hy
  | neg x _ hx => simpa [smul_neg] using AddSubgroup.neg_mem _ hx

theorem exists_cut (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHermForm c G)
    (h2 : Module.finrank F E = 2) (L : Submodule (𝓞 E) (Fin n → E)) (hfg : L.FG)
    (hsp : Submodule.span E (L : Set (Fin n → E)) = ⊤) (I : Ideal (𝓞 F)) (hI : I ≠ ⊥) (M : ℕ) (hM : 0 < M)
    (g : GL (Fin n) (RA F E)) (hg : IsUnA c G g.1) :
    ∃ (γ : GL (Fin n) E) (h k : GL (Fin n) (RA F E)) (e : FiniteAdeleRing (𝓞 F) F),
      IsUnE c G γ.1 ∧ IsUnA c G h.1 ∧ IsUnA c G k.1 ∧ g.1 = fm F γ.1 * h.1 * k.1 ∧
      (∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → e v = 1) ∧
      (∀ v : HeightOneSpectrum (𝓞 F), ¬ I ≤ v.asIdeal → e v = 0) ∧
      (e ⊗ₜ[F] (1 : E) : RA F E) • (h.1 - 1) = 0 ∧ (e ⊗ₜ[F] (1 : E) : RA F E) • (k.1 - 1) = k.1 - 1 ∧
      (∀ z ∈ hat F (L : Set (Fin n → E)), ∃ w ∈ hat F (L : Set (Fin n → E)), k.1 *ᵥ z - z = M • w) ∧
      ∀ z ∈ hat F (L : Set (Fin n → E)), (k⁻¹).1 *ᵥ z ∈ hat F (L : Set (Fin n → E)) := by
  classical

  have ha0 : Ideal.absNorm I ≠ 0 := fun h => hI (Ideal.absNorm_eq_zero_iff.mp h)
  have haI : ((Ideal.absNorm I : ℕ) : 𝓞 F) ∈ I := Ideal.absNorm_mem I
  have hN : 0 < M * Ideal.absNorm I := Nat.mul_pos hM (Nat.pos_of_ne_zero ha0)
  obtain ⟨γ, h₀, k₀, hγ, hh₀, hk₀, hg_eq, ⟨e₀, -, -, he₀s, he₀h⟩, hk₀c, hk₀i⟩ :=
    GlobalTheory.UnRep.exists_rep_suppSplit F E c n G hG h2 L hfg hsp g (M * Ideal.absNorm I) hg hN

  have hfin : {v : HeightOneSpectrum (𝓞 F) | I ≤ v.asIdeal}.Finite := by
    have h0 : I ≠ 0 := hI
    simpa [Ideal.dvd_iff_le] using Ideal.finite_factors h0
  obtain ⟨e, he1, he0⟩ := GlobalTheory.UnRep.SmallMat.exists_indicator (F := F) hfin.toFinset
  have he1' : ∀ v : HeightOneSpectrum (𝓞 F), I ≤ v.asIdeal → e v = 1 :=
    fun v hv => he1 v (by simpa using hv)
  have he0' : ∀ v : HeightOneSpectrum (𝓞 F), ¬ I ≤ v.asIdeal → e v = 0 :=
    fun v hv => he0 v (by simpa using hv)
  have hee : e * e = e := by
    ext v
    by_cases hv : I ≤ v.asIdeal
    · simp [he1' v hv]
    · simp [he0' v hv]
  have hee₀ : e * e₀ = 0 := by
    ext v
    by_cases hv : I ≤ v.asIdeal
    · have : e₀ v = 0 := by
        by_contra hne
        apply (he₀s v hne).2
        rw [Nat.cast_mul]
        exact Ideal.mul_mem_left _ _ (hv haI)
      simp [this]
    · simp [he0' v hv]
  have hint : ∀ b : FiniteAdeleRing (𝓞 F) F, (∀ v, b v ∈ v.adicCompletionIntegers F) →
      ∀ z ∈ hat F (L : Set (Fin n → E)), (b ⊗ₜ[F] (1 : E)) • z ∈ hat F (L : Set (Fin n → E)) :=
    (GlobalTheory.UnRep.idempotent_adeles_small_matrices F E n L hfg hsp).2.2.2.2
  have he_int : ∀ v, e v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : I ≤ v.asIdeal
    · rw [he1' v hv]; exact one_mem _
    · rw [he0' v hv]; exact zero_mem _
  have he_int' : ∀ v, (1 - e) v ∈ v.adicCompletionIntegers F := by
    intro v
    by_cases hv : I ≤ v.asIdeal
    · simp [he1' v hv]
    · simp [he0' v hv]
  set ε : RA F E := e ⊗ₜ[F] (1 : E) with hεdef
  have hε : ε * ε = ε := by
    rw [hεdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hee]
  have hε1 : (1 - ε) * (1 - ε) = 1 - ε := by
    have : (1 - ε) * (1 - ε) = 1 - 2 * ε + ε * ε := by ring
    rw [this, hε]; ring
  have hε2 : (1 - (1 - ε)) * (1 - (1 - ε)) = 1 - (1 - ε) := by
    rw [sub_sub_cancel, hε]
  have hεc : ε * (1 - ε) = 0 := by rw [mul_sub, mul_one, hε, sub_self]
  have h1ε : 1 - ε = (1 - e) ⊗ₜ[F] (1 : E) := by
    rw [TensorProduct.sub_tmul, ← Algebra.TensorProduct.one_def]
  have hsε : sg (FiniteAdeleRing (𝓞 F) F) c ε = ε := by
    simp [hεdef, sg, Algebra.TensorProduct.map_tmul]
  have hs1 : sg (FiniteAdeleRing (𝓞 F) F) c (1 - ε) = 1 - ε := by
    rw [map_sub, map_one, hsε]
  have hs2 : sg (FiniteAdeleRing (𝓞 F) F) c (1 - (1 - ε)) = 1 - (1 - ε) := by
    rw [map_sub, map_one, hs1]
  set X := mix (1 - ε) hε1 k₀ with hXdef
  set Y := mix (1 - (1 - ε)) hε2 k₀ with hYdef
  have hX : X.1 - 1 = (1 - ε) • (k₀.1 - 1) := by
    rw [hXdef, mix_val]
    simp only [sub_sub_cancel, smul_sub, sub_smul, one_smul]
    abel
  have hY : Y.1 - 1 = ε • (k₀.1 - 1) := by
    rw [hYdef, mix_val]
    simp only [sub_sub_cancel, smul_sub, sub_smul, one_smul]
    abel
  have hεh : ε • (h₀.1 - 1) = 0 := by
    rw [← he₀h, smul_smul]
    have : ε * (e₀ ⊗ₜ[F] (1 : E)) = 0 := by
      rw [hεdef, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hee₀, TensorProduct.zero_tmul]
    rw [this, zero_smul]
  refine ⟨γ, h₀ * X, Y, e, hγ, ?_, ?_, ?_, he1', he0', ?_, ?_, ?_, ?_⟩
  · rw [Units.val_mul]
    exact isUnA_mul c G _ _ hh₀ (isUnA_mix c G (1 - ε) hε1 hs1 k₀ hk₀)
  · exact isUnA_mix c G _ hε2 hs2 k₀ hk₀
  · rw [hg_eq, hXdef, hYdef]
    simp only [Units.val_mul, mul_assoc, mix_mul_mix]
  · have : (h₀ * X).1 - 1 = (h₀.1 - 1) * X.1 + (X.1 - 1) := by
      rw [Units.val_mul, sub_mul, one_mul]; abel
    rw [this, smul_add, hX, smul_smul, hεc, zero_smul, add_zero, ← smul_mul_assoc, hεh, zero_mul]
  · rw [hY, smul_smul, hε]
  · intro z hz
    obtain ⟨w, hw, hkw⟩ := hk₀c z hz
    refine ⟨ε • (Ideal.absNorm I • w), hint e he_int _ (AddSubgroup.nsmul_mem _ hw _), ?_⟩
    have : Y.1 *ᵥ z - z = (Y.1 - 1) *ᵥ z := by rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [this, hY, Matrix.smul_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, hkw, mul_smul, smul_comm]
  · intro z hz
    rw [hYdef, mix_inv_val]
    simp only [sub_sub_cancel]
    rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, h1ε]
    exact AddSubgroup.add_mem _ (hint e he_int _ (hk₀i z hz)) (hint _ he_int' z hz)

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem place_mul_eq_zero {D : D7} (V : HSp D) {g : GA D V} (α : Af D.host.F)
    (h : (α ⊗ₜ[D.host.F] (1 : D.host.E) : AfE D) • ((finHom V g).1 - 1) = 0) (i j : Fin V.rank) :
    algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * (mt V g - 1) i j = 0 := by
  have hfm : (finHom V g).1 = (mt V g).map (finPart D) := GlobalTheory.UnitarySplit.val_bc _ _
  have hal : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) =
      (pairA D.host.F 0 α) ⊗ₜ[D.host.F] (1 : D.host.E) := by
    rw [Algebra.algebraMap_eq_smul_one, Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul,
      mul_one]
  apply GlobalTheory.UnitarySplit.parts_inj D
  · rw [map_mul, map_zero]
    have : infPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = 0 := by
      rw [hal]; exact (Algebra.TensorProduct.map_tmul _ _ _ _).trans (TensorProduct.zero_tmul _ _)
    rw [this, zero_mul]
  · rw [map_mul, map_zero]
    have h1 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α)) = α ⊗ₜ[D.host.F] (1 : D.host.E) := by
      rw [hal]; exact Algebra.TensorProduct.map_tmul _ _ _ _
    have h2 : finPart D ((mt V g - 1) i j) = ((finHom V g).1 - 1) i j := by
      rw [hfm, Matrix.sub_apply, Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply, Matrix.one_apply]
      split_ifs <;> simp
    rw [h1, h2]
    have := congrFun (congrFun h i) j
    simpa [Matrix.smul_apply] using this

set_option maxHeartbeats 1000000 in

theorem exists_rat_real_trivAt_cong : ∀ (D : D7) (V : HSp D) (L : Lt D.host.E V.rank) (I : Ideal (𝓞 D.host.F)) (M : ℕ), (L.FG ∧ Submodule.span D.host.E (L : Set (Fin V.rank → D.host.E)) = ⊤) → I ≠ ⊥ → 0 < M → ∀ g : GA D V, ∃ γ ∈ GQ V, ∃ a ∈ GinfC V, ∃ g' ∈ GfC V, ∃ k ∈ GfC V, g = γ * a * g' * k ∧ TrivAt V I g' ∧ TrivOff V I k ∧ CongK V L M k ∧ ∀ J : Ideal (𝓞 D.host.E), (M : 𝓞 D.host.E) ∈ J → ∀ u ∈ hatV L, fmt V k *ᵥ u - u ∈ hatV (J • L) := by
  intro D V L I M ⟨hfg, hsp⟩ hI hM g
  obtain ⟨-, -, -, -, hcc, -, hc1, hGh, hdet, -, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  have hG : GlobalTheory.UnRep.IsHermForm (GlobalTheory.Member.cF D) V.gramᵀ := ⟨hcc, hc1, hGh, hdet⟩
  obtain ⟨γ', h', k', e, hγ', hh', hk', heq, he1, he0, hh'e, hk'e, hk'c, hk'i⟩ :=
    exists_cut (GlobalTheory.Member.cF D) V.gramᵀ hG (GlobalTheory.UnRep.Space.finrank_two D) L hfg hsp I hI M hM (finHom V g)
      (GlobalTheory.UnRep.Space.isUnA_finHom V g)
  obtain ⟨hGQ, -, hrat, -, -⟩ := GlobalTheory.Member.RatElt.rational_elements D V
  obtain ⟨γ, hγ⟩ := hrat γ' (fun u v => by
    rw [GlobalTheory.UnRep.Space.herm_neg_eq V, GlobalTheory.UnRep.Space.herm_neg_eq V, hγ' u v])
  obtain ⟨-, -, -, hlift, -⟩ := GlobalTheory.UnitarySplit.real_finite_split D V
  obtain ⟨g₁, hg₁, hg₁f⟩ := hlift h' hh'
  obtain ⟨k₁, hk₁, hk₁f⟩ := hlift k' hk'
  have hfm : ∀ x : GA D V, (finHom V x).1 = (mt V x).map (finPart D) := fun x => GlobalTheory.UnitarySplit.val_bc _ _
  have hγfin : (finHom V γ).1 = GlobalTheory.UnRep.fm D.host.F γ'.1 := by
    rw [GlobalTheory.Member.RatElt.fin_eq hγ]
    rfl
  have hgu : finHom V g = finHom V γ * h' * k' :=
    Units.ext (by rw [Units.val_mul, Units.val_mul, heq, hγfin])
  have ha : γ⁻¹ * g * (g₁ * k₁)⁻¹ ∈ GinfC V := by
    rw [GinfC, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, map_mul, hg₁f, hk₁f, hgu]
    group
  have hfk : fmt V k₁ = k'.1 := by rw [fmt, ← hfm, hk₁f]
  have hhat : ∀ S : Lt D.host.E V.rank, hatV S = GlobalTheory.AdLat.hat D.host.F (S : Set (Fin V.rank → D.host.E)) :=
    fun S => rfl
  refine ⟨γ, (hGQ γ).2 ⟨γ', hγ⟩, γ⁻¹ * g * (g₁ * k₁)⁻¹, ha, g₁, hg₁, k₁, hk₁, by group, ?_, ?_, ?_, ?_⟩
  · intro v hv ε ⟨α, hε, _, hα0⟩ i j
    rw [hε]
    apply place_mul_eq_zero V α _ i j
    rw [hg₁f]
    have hαe : α * e = α := by
      ext v'
      by_cases hvv : v' = v
      · rw [hvv]; simp [he1 v hv]
      · have : α v' = 0 := hα0 v' hvv
        simp [this]
    have ht : (α * e) ⊗ₜ[D.host.F] (1 : D.host.E) = (α ⊗ₜ[D.host.F] (1 : D.host.E)) * (e ⊗ₜ[D.host.F] (1 : D.host.E)) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one]
    rw [← hαe, ht, ← smul_smul, hh'e, smul_zero]
  · intro v hv ε ⟨α, hε, _, hα0⟩ i j
    rw [hε]
    apply place_mul_eq_zero V α _ i j
    rw [hk₁f]
    have hαe : α * e = 0 := by
      ext v'
      by_cases hvv : v' = v
      · rw [hvv]; simp [he0 v hv]
      · have : α v' = 0 := hα0 v' hvv
        simp [this]
    rw [← hk'e, smul_smul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, hαe, TensorProduct.zero_tmul, zero_smul]
  · refine ⟨fun u => ?_, fun u hu => ?_⟩
    · rw [hfk, hhat]
      constructor
      · intro hu
        refine ⟨(k'⁻¹).1 *ᵥ u, hk'i u hu, ?_⟩
        rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
      · rintro ⟨u₀, hu₀, rfl⟩
        obtain ⟨w, hw, hkw⟩ := hk'c u₀ hu₀
        have : k'.1 *ᵥ u₀ = u₀ + M • w := by rw [← hkw]; abel
        rw [this]
        exact AddSubgroup.add_mem _ hu₀ (AddSubgroup.nsmul_mem _ hw _)
    · rw [hhat] at hu
      rw [hfk]
      obtain ⟨w, hw, hkw⟩ := hk'c u hu
      exact ⟨w, hw, hkw⟩
  · intro J hJ u hu
    rw [hhat] at hu
    obtain ⟨w, hw, hkw⟩ := hk'c u hu
    rw [hfk, hkw, hhat]
    exact nsmul_mem_hat (F := D.host.F) L M J hJ hw

end GlobalTheory.Ker.CutAt
