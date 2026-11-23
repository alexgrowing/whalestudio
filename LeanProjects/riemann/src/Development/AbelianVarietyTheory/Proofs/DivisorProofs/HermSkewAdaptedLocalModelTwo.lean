import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSplittingSplitOm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsotropicOrbitOrthogonalAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementSkewCm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section
namespace GlobalTheory.IsoAOrthLoc

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem at_transpose {m k : ℕ} {v : Pl F} {Z : Matrix (Fin m) (Fin k) (AE F E)} (hZ : At (evFin F v) Z) :
    At (evFin F v) Zᵀ := by
  intro u hu
  rw [← Matrix.transpose_smul, hZ u hu, Matrix.transpose_zero]

theorem at_mulVec_vec {n k : ℕ} {v : Pl F} (N : Matrix (Fin n) (Fin k) (AE F E)) {g : Fin k → AE F E}
    (hg : At (evFin F v) g) : At (evFin F v) (N *ᵥ g) := by
  intro u hu
  rw [← Matrix.mulVec_smul, hg u hu, Matrix.mulVec_zero]

theorem at_mul_left {n k m : ℕ} {v : Pl F} (N : Matrix (Fin n) (Fin k) (AE F E)) {Z : Matrix (Fin k) (Fin m) (AE F E)}
    (hZ : At (evFin F v) Z) : At (evFin F v) (N * Z) := by
  intro u hu
  rw [← Matrix.mul_smul, hZ u hu, Matrix.mul_zero]

theorem at_vecMulVec_right {n d : ℕ} {v : Pl F} (a : Fin n → AE F E) {b : Fin d → AE F E}
    (hb : At (evFin F v) b) : At (evFin F v) (Matrix.vecMulVec a b) := by
  intro u hu
  ext i j
  have h := congrFun (hb u hu) j
  simp only [Pi.smul_apply, Pi.zero_apply] at h
  simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, Matrix.zero_apply]
  rw [← mul_smul_comm, h, mul_zero]

theorem form_herm {σ : E →ₐ[F] E} (hσ : ∀ x, σ (σ x) = x) {n : ℕ} {J : Matrix (Fin n) (Fin n) E}
    (hJ : ∀ i j, σ (J j i) = J i j) (x w : Fin n → E) : form σ J x w = σ (form σ J w x) := by
  simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hJ, hσ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  ring

theorem hTens_add_right {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d : ℕ}
    (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (x y y' : Matrix (Fin n) (Fin d) A) :
    hTens c JA JB x (y + y') = hTens c JA JB x y + hTens c JA JB x y' := by
  unfold hTens
  simp only [Matrix.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem hTens_pure_mul {R A : Type} [CommRing R] [CommRing A] [Algebra R A] (c : A →ₐ[R] A) {n d e : ℕ}
    (JA : Matrix (Fin n) (Fin n) A) (JB : Matrix (Fin d) (Fin d) A) (a : Fin n → A) (b : Fin d → A)
    (Z : Matrix (Fin n) (Fin e) A) (N : Matrix (Fin e) (Fin d) A) :
    hTens c JA JB (Matrix.vecMulVec a b) (Z * N) =
      Matrix.vecMul (Matrix.vecMul a JA) (Z.map c) ⬝ᵥ (N.map c *ᵥ Matrix.vecMul b JB) := by
  unfold hTens
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, map_sum, map_mul, Matrix.vecMul, Matrix.mulVec, dotProduct,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  conv_lhs => enter [2, i, 2, j, 2, k]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, i]; rw [Finset.sum_comm]
  conv_lhs => rw [Finset.sum_comm]
  conv_lhs => enter [2, q, 2, i, 2, j]; rw [Finset.sum_comm]
  conv_lhs => enter [2, q, 2, i]; rw [Finset.sum_comm]
  conv_lhs => enter [2, q]; rw [Finset.sum_comm]
  conv_lhs => enter [2, q, 2, l]; rw [Finset.sum_comm]
  conv_lhs => enter [2, q, 2, l, 2, j]; rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
    Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem pair_iota_left (σ : E →ₐ[F] E) {n n₁ : ℕ} (J : Matrix (Fin n) (Fin n) E) (ι : Matrix (Fin n) (Fin n₁) E)
    (x : Fin n → E) (h0 : ∀ u, form σ J (ι *ᵥ u) x = 0) (y : Fin n₁ → AE F E) :
    ∑ i, ∑ k, (incM F ι *ᵥ y) i * incM F J i k * cA σ (incV F x k) = 0 := by
  classical
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have hq : ∀ q, ∑ i, ∑ k, inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k) = 0 := by
    intro q
    have h1 := congrArg (inclR (F := F) (AF F)) (h0 (Pi.single q 1))
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, map_sum, map_mul,
      Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have e : ∀ i k, (incM F ι *ᵥ y) i * incM F J i k * cA σ (incV F x k) =
      ∑ q, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) := by
    intro i k
    simp only [Matrix.mulVec, dotProduct, incM, Matrix.map_apply, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  have sw : ∀ i, ∑ k, ∑ q, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) =
      ∑ q, ∑ k, y q * (inclR (F := F) (AF F) (ι i q) * incM F J i k * cA σ (incV F x k)) := fun i => Finset.sum_comm
  simp only [e, sw]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun q _ => ?_
  simp only [← Finset.mul_sum]
  rw [hq q, mul_zero]

theorem isoA_orth_at : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (X₁ : Spc F E n₁) (W : Spc F E d) (W₁ : Spc F E d₁)
    (H : Plane E n n₁) (H' : Plane E d d₁) (M : Model σ X W),
    B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H.IsAdapted σ B X X₁ j₀ j₁ → H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (v : Pl F) (w : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)),
      (∀ u ∈ isoA (F := F) H H', At (evFin F v) u →
        (GlobalTheory.LatVac.locCo M.co v u).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (GlobalTheory.LatVac.locCo M.co v u).2 = 0) →
      ∃ z₀ : Fin n → AE F E, At (evFin F v) (Matrix.vecMulVec z₀ (incV F H'.x)) ∧
      ∃ y₀ : Fin d₁ → AE F E, At (evFin F v) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y₀)) ∧
      ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), At (evFin F v) z ∧
        w = GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec z₀ (incV F H'.x)) +
          GlobalTheory.LatVac.locCo M.co v (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y₀)) +
          GlobalTheory.LatVac.locCo M.co v (incM F H.ι * z * (incM F H'.ι)ᵀ) := by
  intro F E _ _ _ _ _ σ B n n₁ d d₁ r s r' s' i₀ i₁ j₀ j₁ X X₁ W W₁ H H' M hB hX hW hH hH' v w hw
  have hσ := GlobalTheory.IsoOrthLoc.sigma_sigma hB.cm
  have hc : ∀ e : E, cA σ (inclR (F := F) (AF F) e) = inclR (F := F) (AF F) (σ e) := fun e => rfl
  obtain ⟨u0, ⟨z₀, rfl⟩, hu0, Z, hZ, hwd⟩ :=
    (GlobalTheory.IsoOrthLoc.isotropic_orbit_orthogonal_at_place F E σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M hB hX hW hH' v).2 w
      (fun u hu hat => hw u (Or.inl hu) hat)
  have h1 : incM F (1 : Matrix (Fin n) (Fin n) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  rw [h1, Matrix.one_mul] at hwd
  subst hwd
  have hsp := GlobalTheory.IsoOrthLoc.span_decomp H X.L hX.lat (fun z hz => by
    obtain ⟨s, t, u, -, -, -, h⟩ := hH.split z hz
    exact ⟨s, t, u, h⟩)
  choose sX tX uX hstu using fun j : Fin n => hsp (Pi.single j 1)
  let U : Matrix (Fin n₁) (Fin n) E := fun q j => uX j q
  have hE : ∀ j l, sX j * H.x l + ∑ q, H.ι l q * U q j + tX j * H.y l = if l = j then 1 else 0 := by
    intro j l
    have h := congrFun (hstu j) l
    simp only [Pi.single_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mulVec, dotProduct] at h
    rw [h]
  have hdec := GlobalTheory.IsoOrthLoc.decomp (F := F) (n := d₁) H.x H.y H.ι sX tX U hE Zᵀ
  have hxX : ∀ k, ∑ i, H.x i * X.J i k = σ (tX k) := by
    intro k
    rw [← GlobalTheory.IsoOrthLoc.form_single σ X.J H.x k, hstu k, GlobalTheory.IsoOrthLoc.form_add_right,
      GlobalTheory.IsoOrthLoc.form_add_right, GlobalTheory.IsoOrthLoc.form_smul_right, GlobalTheory.IsoOrthLoc.form_smul_right, hH.xx, hH.xy,
      form_herm hσ hX.herm H.x (H.ι *ᵥ uX k), (hH.orth (uX k)).1]
    simp
  have hJ₁ : W₁.J.det ≠ 0 := (GlobalTheory.LeviAdapted.isUnit_det_low hσ hW hH').ne_zero
  have hgram : incM F W₁.J = (incM F H'.ι)ᵀ * incM F W.J * (incM F H'.ι).map (cA σ) := by
    rw [← hH'.gram]
    ext p q
    simp only [incM, Matrix.map_apply, Matrix.mul_apply, Matrix.transpose_apply, map_sum, map_mul, hc]
  set b : Fin d₁ → AE F E := Zᵀ *ᵥ incV F tX with hbdef
  have hb : b = 0 := by
    refine GlobalTheory.IsoOrthLoc.vanish_of_orth σ hσ W₁.J hJ₁ v b (GlobalTheory.IsoOrthLoc.at_mulVec (at_transpose hZ) _)
      fun g hg => ?_
    have h := hw (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ g)) (Or.inr ⟨g, rfl⟩)
      (at_vecMulVec_right _ (at_mulVec_vec _ hg))
    rw [← map_add, GlobalTheory.IsoOrthLoc.locCo_form M.co v] at h
    refine Eq.trans ?_ h
    unfold GlobalTheory.WeilM.symp
    rw [hTens_add_right, GlobalTheory.MixedLagr.hTens_vecMulVec,
      pair_iota_left σ W.J H'.ι H'.x (fun u => (hH'.orth u).1) g, mul_zero, zero_add, hTens_pure_mul]
    congr 3
    have hα : Matrix.vecMul (incV F H.x) (incM F X.J) = fun k => cA σ (incV F tX k) := by
      funext k
      simp only [Matrix.vecMul, dotProduct, incV, incM, Matrix.map_apply, hc, ← hxX k, map_sum, map_mul]
    have hβ : ((incM F H'.ι)ᵀ).map (cA σ) *ᵥ Matrix.vecMul (incM F H'.ι *ᵥ g) (incM F W.J) =
        Matrix.vecMul g (incM F W₁.J) := by
      rw [hgram, Matrix.transpose_map, Matrix.mulVec_transpose, ← Matrix.vecMul_transpose (incM F H'.ι) g,
        Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, Matrix.mul_assoc]
    have hγ : Matrix.vecMul (fun k => cA σ (incV F tX k)) (Z.map (cA σ)) = fun q => cA σ (b q) := by
      funext q
      simp only [Matrix.vecMul, dotProduct, Matrix.map_apply, hbdef, Matrix.mulVec, Matrix.transpose_apply, map_sum,
        map_mul]
      exact Finset.sum_congr rfl fun k _ => mul_comm _ _
    rw [hα, hβ, hγ]
    simp only [dotProduct, Matrix.vecMul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  have hZdec : Z = Matrix.vecMulVec (incV F H.x) (Zᵀ *ᵥ incV F sX) + incM F H.ι * (incM F U * Z) +
      Matrix.vecMulVec (incV F H.y) b := by
    have := congrArg Matrix.transpose hdec
    simp only [Matrix.transpose_transpose, Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_vecMulVec]
      at this
    exact this
  have hvm : ∀ (a : Fin n → AE F E) (c : Fin d₁ → AE F E),
      Matrix.vecMulVec a c * (incM F H'.ι)ᵀ = Matrix.vecMulVec a (incM F H'.ι *ᵥ c) := by
    intro a c
    ext i l
    simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.mulVec, dotProduct,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun q _ => by ring
  refine ⟨z₀, hu0, Zᵀ *ᵥ incV F sX,
    at_vecMulVec_right _ (at_mulVec_vec _ (GlobalTheory.IsoOrthLoc.at_mulVec (at_transpose hZ) _)),
    incM F U * Z, at_mul_left _ hZ, ?_⟩
  conv_lhs => rw [hZdec]
  have hz0 : Matrix.vecMulVec (incV F H.y) (0 : Fin d₁ → AE F E) = 0 := by
    ext i j
    simp [Matrix.vecMulVec_apply]
  rw [hb, hz0, add_zero, Matrix.add_mul, hvm, map_add, add_assoc]

end GlobalTheory.IsoAOrthLoc
