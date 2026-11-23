import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueArchimedeanMatrixAdeleExtensionOfCom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealScalarArchimedeanAdeleSmulMatrixRealPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanTraceSymplecticFormOrthonormalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFockVacuumGaussianFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.FockTransv

open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.RealLift GlobalTheory.FockVacuum

theorem exists_of_inj {V C : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] [AddCommGroup C] [Module ℝ C]
    (p q : C →ₗ[ℝ] V) (J : C →ₗ[ℝ] C) (hz : ∀ c, p c = 0 → p (J c) = 0 → c = 0) (hs : Function.Surjective (p.prod q))
    (v : V) : ∃ c, p c = 0 ∧ p (J c) = v := by
  have hi : Function.Injective (p.prod (p ∘ₗ J)) := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    exact hz c (congrArg Prod.fst hc) (congrArg Prod.snd hc)
  haveI : FiniteDimensional ℝ C := FiniteDimensional.of_injective _ hi
  have hsurj : Function.Surjective (p.prod (p ∘ₗ J)) := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hi
    exact le_antisymm (LinearMap.finrank_le_finrank_of_injective hi) (LinearMap.finrank_le_finrank_of_surjective hs)
  obtain ⟨c, hc⟩ := hsurj (0, v)
  exact ⟨c, congrArg Prod.fst hc, congrArg Prod.snd hc⟩

theorem cplx_eq {ι : Type} {P Q R S : ℕ} (c : ι → Matrix (Ix P Q) (Ix R S) ℂ) (w : ι) :
    cplx ι P Q R S c w = Complex.I • (Jm P Q * c w * (Jm R S)ᵀ) := by
  ext a b
  rw [cplx_apply, GlobalTheory.SympFrames.jm_eq_diagonal, GlobalTheory.SympFrames.jm_eq_diagonal, Matrix.diagonal_transpose,
    Matrix.smul_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, GlobalTheory.SympFrames.lineSign_eq, smul_eq_mul]
  ring

def cplxS {ι : Type} (ε : ι → ℤˣ) (P Q R S : ℕ) : (ι → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (ι → Matrix (Ix P Q) (Ix R S) ℂ) where
  toFun c w := ((ε w : ℤ) : ℂ) • cplx ι P Q R S c w
  map_add' c c' := by funext w; simp only [map_add, Pi.add_apply, smul_add]
  map_smul' r c := by funext w; simp only [map_smul, Pi.smul_apply, RingHom.id_apply]; exact smul_comm _ _ _

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def signAd (ε : InfinitePlace F → ℤˣ) : AF F :=
  LinearMap.inl F (Ainf F) (Af F) (fun w => ((ε w : ℤ) : w.Completion))

theorem map_signAd_smul {α β : Type} (ε : InfinitePlace F → ℤˣ) {w : InfinitePlace F} (τ : EmbOver E w)
    (u : Matrix α β (AE F E)) : (signAd ε • u).map (piInf τ) = ((ε w : ℤ) : ℂ) • u.map (piInf τ) := by
  ext i j
  simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Algebra.smul_def, map_mul, GlobalTheory.RealScalar.piInf_algebraMap]
  congr 1
  exact map_intCast (InfinitePlace.Completion.extensionEmbedding w) _

theorem incM_map {m k : Type} (J : Matrix m k E) {w : InfinitePlace F} (τ : EmbOver E w) :
    (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  change infEmb τ (compInf F E w ((1 : AF F) ⊗ₜ[F] J i j)) = _
  rw [compInf]
  change infEmb τ ((evInf F w 1) ⊗ₜ[F] ((AlgHom.id F E) (J i j))) = _
  rw [infEmb_tmul]
  simp

theorem transv_frames (σ : E →ₐ[F] E) {α β κ : Type}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a₀ b₀ : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (hCM : IsCMExt F E σ) (hFr : Framed τ JA JB a₀ b₀ A C)
    (ε : InfinitePlace F → ℤˣ) (v : κ → mixedEmbedding.mixedSpace F) :
    ∃ (u u' : Matrix α β (AE F E)) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
      (∀ w, u'.map (piInf (τ w)) = A w * cplxS ε P Q R S c w * (C w)ᵀ) ∧
      (∀ i, evI F ((d.e u).1 i) = 0) ∧ ∀ i, evI F ((d.e u').1 i) = v i := by
  have hU := fun c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ =>
    GlobalTheory.ArchMatCoords.existsUnique_at_map_piInf σ τ hCM (fun w => A w * c w * (C w)ᵀ)
  choose U hU hU' using hU
  have hadd : ∀ c c', U (c + c') = U c + U c' := fun c c' => by
    refine (hU' (c + c') _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_add, (hU c).1 u hu, (hU c').1 u hu, add_zero]
    · rw [Matrix.map_add _ (map_add _), (hU c).2, (hU c').2, Pi.add_apply, Matrix.mul_add, Matrix.add_mul]
  have hsmul : ∀ (r : ℝ) c, U (r • c) = realAd F r • U c := fun r c => by
    refine (hU' (r • c) _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU c).1 u hu, smul_zero]
    · rw [GlobalTheory.RealScalar.realAd_smul_map σ τ hCM, (hU c).2, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul]
      ext i j
      simp
  have hsign : ∀ c, U (cplx _ P Q R S c) = signAd ε • U (cplxS ε P Q R S c) := fun c => by
    refine (hU' _ _ ⟨fun u hu => ?_, fun w => ?_⟩).symm
    · rw [smul_comm, (hU _).1 u hu, smul_zero]
    · rw [map_signAd_smul, (hU _).2]
      change _ • (A w * (((ε w : ℤ) : ℂ) • cplx _ P Q R S c w) * (C w)ᵀ) = _
      rw [Matrix.mul_smul, Matrix.smul_mul, smul_smul, ← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
  let p : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).1 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  let q : (InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
    { toFun := fun c i => evI F ((d.e (U c)).2 i)
      map_add' := fun c c' => by
        funext i
        rw [hadd, map_add]
        exact map_add (evR F) _ _
      map_smul' := fun r c => by
        funext i
        rw [hsmul, map_smul]
        exact evI_realAd_mul r _ }
  have hω : ∀ c c', trPair F κ (p c) (q c') - trPair F κ (p c') (q c) =
      -2 * (∑ w, ∑ a, ∑ b, lineSign a b * c w a b * star (c' w a b)).im := fun c c' => by
    rw [← GlobalTheory.SympFrames.symp_frames σ τ JA JB a₀ b₀ A C hCM hFr (U c) (U c') c c' (hU c).1 (hU c').1 (hU c).2 (hU c').2,
      d.form, trPair_apply, trPair_apply, ← map_sub, ← evR_apply]
    simp only [dotProduct, map_sub, map_sum, map_mul]
    rfl
  have hs : Function.Surjective (p.prod q) := by
    rintro ⟨v, v'⟩
    let u := d.e.symm (fun i => infAd (v i), fun i => infAd (v' i))
    have hu : At (evI F) u := fun t ht => by
      rw [← map_smul, LinearEquiv.map_eq_zero_iff]
      ext i
      · exact mul_infAd t ht _
      · exact mul_infAd t ht _
    choose A' hA' using fun w => (hFr.2.1 w).2
    choose C' hC' using fun w => (hFr.2.2 w).2
    have huc : u = U fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ := hU' _ _ ⟨hu, fun w => by
      have : (C' w)ᵀ * (C w)ᵀ = 1 := by rw [← Matrix.transpose_mul, hC', Matrix.transpose_one]
      simp only [Matrix.mul_assoc]
      rw [this, Matrix.mul_one, ← Matrix.mul_assoc, hA', Matrix.one_mul]⟩
    refine ⟨fun w => A' w * u.map (piInf (τ w)) * (C' w)ᵀ, Prod.ext (funext fun i => ?_) (funext fun i => ?_)⟩
    · change evI F ((d.e (U _)).1 i) = v i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
    · change evI F ((d.e (U _)).2 i) = v' i
      rw [← huc, LinearEquiv.apply_symm_apply, evI_infAd]
  obtain ⟨c, h1, h2⟩ := exists_of_inj p q (cplxS ε P Q R S) (fun c h1 h2 => by
    have h3 : p (cplx _ P Q R S c) = 0 := by
      funext i
      change evI F ((d.e (U _)).1 i) = 0
      rw [hsign, map_smul]
      have h4 : evR F ((d.e (U (cplxS ε P Q R S c))).1 i) = 0 := congrFun h2 i
      change evR F (signAd ε * (d.e (U (cplxS ε P Q R S c))).1 i) = 0
      rw [map_mul, h4, mul_zero]
    by_contra hc
    have h5 := herm_cplx_pos c hc
    rw [← hω, h1, h3] at h5
    simp at h5) hs v
  exact ⟨U c, U (cplxS ε P Q R S c), c, (hU _).1, (hU _).1, (hU _).2, (hU _).2, fun i => congrFun h1 i,
    fun i => congrFun h2 i⟩

theorem transversal : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W)
    (r s r' s' : ℕ), IsPair B M χX χW om r s r' s' → ∀ (ε : InfinitePlace F → ℤˣ) (α : Fin n × Fin d → mixedEmbedding.mixedSpace F),
    ∃ u u' : Matrix (Fin n) (Fin d) (AE F E), At (evI F) u ∧ At (evI F) u' ∧
      (∀ w, u'.map (piInf (B.emb w)) = (((ε w : ℤ) : ℂ) * Complex.I) • (X.θ w * u.map (piInf (B.emb w)) * (W.θ w)ᵀ)) ∧
      (∀ i, evI F ((M.co.e u).1 i) = 0) ∧ ∀ i, evI F ((M.co.e u').1 i) = α i := by
  intro F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP ε α
  choose A hA hA' using fun w => GlobalTheory.RealLift.frameEx_holds n r s _ _ (hP.herm.sig w) (hP.herm.cartan w)
  choose C hC hC' using fun w => GlobalTheory.RealLift.frameEx_holds d r' s' _ _ (hP.skew.sig w) (hP.skew.cartan w)
  have hFr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C :=
    ⟨one_mul _, fun w => by rw [one_smul, incM_map]; exact hA w, fun w => by rw [incM_map]; exact hC w⟩
  obtain ⟨u, u', c, hu, hu', h1, h2, h3, h4⟩ := transv_frames σ B.emb _ _ M.co 1 Complex.I A C hP.base.cm hFr ε α
  refine ⟨u, u', hu, hu', fun w => ?_, h3, h4⟩
  rw [h1, h2]
  change A w * (((ε w : ℤ) : ℂ) • cplx _ r s r' s' c w) * (C w)ᵀ = _
  rw [cplx_eq, smul_smul, Matrix.mul_smul, Matrix.smul_mul]
  congr 1
  simp only [← Matrix.mul_assoc]
  rw [hA', Matrix.mul_assoc _ (C w)ᵀ, ← Matrix.transpose_mul, hC', Matrix.transpose_mul]
  simp only [← Matrix.mul_assoc]

end GlobalTheory.FockTransv
