import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAtAlt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IwasawaIsotropicStabilizerInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegerAddConjEqOneUnramifiedCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceSplitOrInert
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedFiniteMapsRestriction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSkewScalarSelfDualAtPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalEmbeddingRangeCharacterizationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalStabilizerPreservesAdelicLatticeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryStabilizerIsotropicDecompositionStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.IndLine

noncomputable section

namespace GlobalTheory.IwLineInert

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem cA_eq_sigR (σ : E →ₐ[F] E) (z : AE F E) : cA σ z = sigR (AF F) σ z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a e => rfl
  | add y z hy hz => rw [map_add, map_add, hy, hz]

theorem transpose_cond {A : Type} [CommRing A] {n : ℕ} (s : A → A) (c : A) (hc : IsUnit c)
    (N G : Matrix (Fin n) (Fin n) A) :
    (G.map s)ᵀ * (c • Nᵀ) * G = c • Nᵀ ↔ Gᵀ * N * G.map s = N := by
  have e : (G.map s)ᵀ * (c • Nᵀ) * G = c • (Gᵀ * N * G.map s)ᵀ := by
    rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_smul, Matrix.smul_mul,
      Matrix.mul_assoc]
  rw [e]
  constructor
  · intro h
    have h2 := congrArg (fun M => (hc.unit⁻¹ : Aˣ) • M) h
    simp only [smul_smul, Units.smul_def, IsUnit.val_inv_mul, one_smul] at h2
    simpa using congrArg Matrix.transpose h2
  · intro h; rw [h]

theorem mem_UG_iff (σ : E →ₐ[F] E) {d : ℕ} (J : Matrix (Fin d) (Fin d) E) {δ : E} (hδ : δ ≠ 0)
    (g : GL (Fin d) (AE F E)) : g ∈ UG (cA σ) (incM F J) ↔ g ∈ HR (AF F) σ (δ • Jᵀ) := by
  have hu : IsUnit (inclR (F := F) (AF F) δ) := (isUnit_iff_ne_zero.2 hδ).map _
  have eJ : JR (AF F) (δ • Jᵀ) = inclR (F := F) (AF F) δ • (incM F J)ᵀ := by
    ext i j; simp [JR, incM, Matrix.smul_apply, smul_eq_mul, map_mul]
  have es : (g : Matrix (Fin d) (Fin d) (AE F E)).map (sigR (AF F) σ) =
      (g : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) := by
    ext i j; simp [cA_eq_sigR]
  show (g : Matrix (Fin d) (Fin d) (AE F E))ᵀ * incM F J * (g : Matrix (Fin d) (Fin d) (AE F E)).map (cA σ) = incM F J ↔
    Formalism.UG.cT (sigR (AF F) σ) (g : Matrix (Fin d) (Fin d) (AE F E)) * JR (AF F) (δ • Jᵀ) *
      (g : Matrix (Fin d) (Fin d) (AE F E)) = JR (AF F) (δ • Jᵀ)
  rw [eJ, Formalism.UG.cT, es, transpose_cond _ _ hu]

end GlobalTheory.IwLineInert

namespace GlobalTheory.IwLineInert

theorem iwasawa_line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (d d₁ : ℕ) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ r s r₁ s₁ : ℕ), B.IsGood σ →
    W.IsSkew σ B r s → W₁.IsSkew σ B r₁ s₁ → H'.IsAdapted σ B W W₁ i₀ i₁ → ∀ v : Pl F, IsEmpty (E →ₐ[F] Fv F v) →
    ∀ h ∈ UAt σ W (evFin F v), ∃ (n m k : UA σ W.J) (t : (AE F E)ˣ) (h₁ : UA σ W₁.J), n ∈ unip σ W H' ∧
      n ∈ UAt σ W (evFin F v) ∧ m ∈ UAt σ W (evFin F v) ∧ h₁ ∈ UAt σ W₁ (evFin F v) ∧ IsLevi H' t h₁ m ∧
      k ∈ KAt σ W v ∧ h = n * m * k := by
  intro F E _ _ _ _ _ σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v hv h hh
  obtain ⟨δ, hδ0, hδσ, hsd⟩ := GlobalTheory.T.exists_skew_scalar_self_dual_at_place F E σ B d r s W hB hW v hv
  have hND : IsHermND σ (δ • W.Jᵀ) := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp only [Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, map_mul, hδσ]
      rw [hW.skew]; ring
    · rw [Matrix.det_smul, Matrix.det_transpose]
      exact mul_ne_zero (pow_ne_zero _ hδ0) (GlobalTheory.FinUniq.det_ne_zero_skew hW)
  obtain ⟨θ, hθ⟩ := GlobalTheory.LatVac.exists_integer_add_conj_eq_one_of_isGood σ B hB
  obtain ⟨w, hw⟩ := (GlobalTheory.KFinLoc.split_or_inert F E σ B hB v).resolve_left (fun ⟨f⟩ => hv.false f)
  have hun : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryLatticeOrthogonal.UnramAt F E v := by
    haveI := hB.unram
    intro w _
    exact Ideal.ramificationIdx_eq_one w.asIdeal (𝓞 F)
  haveI : Submodule.IsLattice E W.L := hW.lat
  let e : Matrix (Fin d) (Fin 1) E := Matrix.of fun i _ => H'.x i
  let pr : Matrix (Fin 1) (Fin d) E := Matrix.of fun _ j => (W.J *ᵥ fun i => σ (H'.y i)) j
  have hpe : pr * e = 1 := by
    ext a b
    have h1 := hA.xy
    simp only [form, dotProduct] at h1
    simp only [pr, e, Matrix.mul_apply, Matrix.of_apply, Matrix.one_apply, Subsingleton.elim a b, if_true]
    rw [← h1]
    exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  have hee : Formalism.UG.cT (σ : E →+* E) e * (δ • W.Jᵀ) * e = 0 := by
    ext a b
    have h1 := hA.xx
    simp only [form, dotProduct, Matrix.mulVec] at h1
    simp only [Formalism.UG.cT, e, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, Matrix.of_apply,
      Matrix.smul_apply, smul_eq_mul, Matrix.zero_apply, Finset.sum_mul, RingHom.coe_coe]
    refine (?_ : _ = δ * ∑ j, H'.x j * ∑ i, W.J j i * σ (H'.x i)).trans (by rw [h1, mul_zero])
    first
    | (rw [Finset.mul_sum]
       refine Finset.sum_congr rfl fun j _ => ?_
       rw [Finset.mul_sum, Finset.mul_sum]
       refine Finset.sum_congr rfl fun i _ => ?_
       ring)
    | (rw [Finset.mul_sum]
       conv_lhs => rw [Finset.sum_comm]
       refine Finset.sum_congr rfl fun j _ => ?_
       rw [Finset.mul_sum, Finset.mul_sum]
       refine Finset.sum_congr rfl fun i _ => ?_
       ring)
  let g₀ : GAd σ (δ • W.Jᵀ) := ⟨h.1, (mem_UG_iff σ W.J hδ0 h.1).1 h.2⟩
  obtain ⟨y, hy⟩ := (GlobalTheory.T.local_embedding_range_characterization F E σ d (δ • W.Jᵀ) v g₀).2 (fun u hu => hh u hu)
  obtain ⟨q, k, ⟨β, hβ⟩, hk, hyqk⟩ :=
    GlobalTheory.InertIwasawaIso.exists_of_inert hB.cm (c := θ) hθ hND hw hun hsd hpe hee y
  let P : UA σ W.J := ⟨(emb σ (δ • W.Jᵀ) v q).1, (mem_UG_iff σ W.J hδ0 _).2 (emb σ (δ • W.Jᵀ) v q).2⟩
  let K : UA σ W.J := ⟨(emb σ (δ • W.Jᵀ) v k).1, (mem_UG_iff σ W.J hδ0 _).2 (emb σ (δ • W.Jᵀ) v k).2⟩
  have hsupp : ∀ x : GLoc σ (δ • W.Jᵀ) v, ∀ u : AF F, evFin F v u = 0 →
      u • (((emb σ (δ • W.Jᵀ) v x).1 : GL (Fin d) (AE F E)) - 1 : Matrix (Fin d) (Fin d) (AE F E)) = 0 :=
    fun x => (GlobalTheory.T.local_embedding_range_characterization F E σ d (δ • W.Jᵀ) v (emb σ (δ • W.Jᵀ) v x)).1 ⟨x, rfl⟩
  have hPv : P ∈ UAt σ W (evFin F v) := fun u hu => hsupp q u hu
  have hKv : K ∈ KAt σ W v := by
    refine ⟨fun u hu => hsupp k u hu, fun z hz => ⟨?_, ?_⟩⟩
    · exact GlobalTheory.T.local_stabilizer_preserves_adelic_lattice F E σ d (δ • W.Jᵀ) W v k hk z hz
    · have e1 : mat K⁻¹ = (HA.mat (AF F) σ (δ • W.Jᵀ) (emb σ (δ • W.Jᵀ) v k⁻¹) : Matrix (Fin d) (Fin d) (AE F E)) := by
        rw [map_inv]; rfl
      rw [e1]
      exact GlobalTheory.T.local_stabilizer_preserves_adelic_lattice F E σ d (δ • W.Jᵀ) W v k⁻¹ (inv_mem hk) z hz
  have hline : mat P *ᵥ incV F H'.x = β.1 0 0 • incV F H'.x := by
    funext i
    have h1 : ∑ j, (HA.mat (AF F) σ (δ • W.Jᵀ) (emb σ (δ • W.Jᵀ) v q) : Matrix (Fin d) (Fin d) (AE F E)) i j *
        (e.map (inclR (AF F))) j 0 = ∑ c, (e.map (inclR (AF F))) i c * (β : Matrix (Fin 1) (Fin 1) (AE F E)) c 0 :=
      congrFun (congrFun hβ i) 0
    rw [Fin.sum_univ_one] at h1
    simp only [Matrix.mulVec, dotProduct, incV, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm]
    simp only [Matrix.map_apply, e, Matrix.of_apply] at h1
    exact h1
  have hPK : h = P * K := by
    have h2 : g₀ = emb σ (δ • W.Jᵀ) v q * emb σ (δ • W.Jᵀ) v k := by rw [← hy, hyqk, map_mul]
    have h3 : g₀.1 = (emb σ (δ • W.Jᵀ) v q).1 * (emb σ (δ • W.Jᵀ) v k).1 := by rw [h2]; rfl
    exact Subtype.ext h3
  obtain ⟨n, m, t, h₁, hn, hnv, hmv, hh₁, hlev, hpnm⟩ :=
    GlobalTheory.T.unitary_stabilizer_isotropic_decomposition F E σ B d d₁ W W₁ H' i₀ i₁ r s r₁ s₁ hB hW hW₁ hA v P hPv (β.1 0 0) hline
  exact ⟨n, m, K, t, h₁, hn, hnv, hmv, hh₁, hlev, hKv, by rw [hPK, hpnm]⟩

end GlobalTheory.IwLineInert
