import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrPApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxLiftMulEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceEvIDarboux
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SympVecMulVecXEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumThreeComm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HTensEqTrace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormSwapOfSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Decompose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MixedSpaceTraceFormNondegenerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrAEMixedNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceOrth
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ArchSch

noncomputable section

namespace GlobalTheory.ArchSch

variable {F : Type} [Field F] [NumberField F]

theorem lagL_evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (a.1 + b.1) = _
  exact map_add _ _ _

theorem lagL_evI_zero : evI F 0 = 0 := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F (0 : Ainf F) = 0
  exact map_zero _

theorem lagL_evI_realAd_mul (t : ℝ) (a : AF F) : evI F (realAd F t * a) = t • evI F a := by
  show InfiniteAdeleRing.ringEquiv_mixedSpace F
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (algebraMap ℝ _ t) * a.1) = _
  rw [map_mul, RingEquiv.apply_symm_apply, Algebra.smul_def]
  rfl

theorem lagL_arch_add {κ : Type} (p q : κ → AF F) : arch F (p + q) = arch F p + arch F q := by
  funext i; simp [arch, lagL_evI_add]

theorem lagL_arch_zero {κ : Type} : arch F (0 : κ → AF F) = 0 := by
  funext i; simp [arch, lagL_evI_zero]

theorem lagL_arch_smul {κ : Type} (t : ℝ) (p : κ → AF F) : arch F (realAd F t • p) = t • arch F p := by
  funext i; simp [arch, lagL_evI_realAd_mul]

theorem lagL_at_zero {M : Type} [AddCommGroup M] [Module (AF F) M] : At (evI F) (0 : M) :=
  fun u _ => smul_zero u

theorem lagL_at_add {M : Type} [AddCommGroup M] [Module (AF F) M] {x y : M} (hx : At (evI F) x)
    (hy : At (evI F) y) : At (evI F) (x + y) :=
  fun u hu => by rw [smul_add, hx u hu, hy u hu, add_zero]

theorem lagL_at_smul {M : Type} [AddCommGroup M] [Module (AF F) M] {x : M} (c : AF F) (hx : At (evI F) x) :
    At (evI F) (c • x) :=
  fun u hu => by rw [smul_comm, hx u hu, smul_zero]

theorem lagL_dar_add_left {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {Bf : V → V → AF F} (dd : Darboux Bf κ) (x y w : V) : Bf (x + y) w = Bf x w + Bf y w := by
  rw [dd.form, dd.form, dd.form, map_add]
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

theorem lagL_dar_add_right {κ : Type} [Fintype κ] {V : Type} [AddCommGroup V] [Module (AF F) V]
    {Bf : V → V → AF F} (dd : Darboux Bf κ) (x y w : V) : Bf w (x + y) = Bf w x + Bf w y := by
  rw [dd.form, dd.form, dd.form, map_add]
  simp only [Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  ring

variable {E : Type} [Field E] [NumberField E] [Algebra F E]

theorem lagL_at_vmv {n d : ℕ} {c : Fin n → AE F E} (hc : At (evI F) c) (x : Fin d → AE F E) :
    At (evI F) (Matrix.vecMulVec c x) := by
  intro u hu
  ext i j
  have := congrFun (hc u hu) i
  simp only [Pi.smul_apply, Pi.zero_apply] at this
  simp [Matrix.vecMulVec_apply, ← smul_mul_assoc, this]

theorem lagL_smul_vmv {n d : ℕ} (a : AF F) (c : Fin n → AE F E) (x : Fin d → AE F E) :
    a • Matrix.vecMulVec c x = Matrix.vecMulVec (a • c) x := by
  ext i j; simp [Matrix.vecMulVec_apply, smul_mul_assoc]

end GlobalTheory.ArchSch

namespace GlobalTheory.ArchSch

theorem lagSet_isLagrangian : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} (B : Base F E)
    (n d d₁ r s r' s' i₀ i₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (M : Model σ X W)
    (M₁ : Model σ X W₁), B.IsGood σ → X.IsHerm σ B r s → W.IsSkew σ B r' s' → H'.IsAdapted σ B W W₁ i₀ i₁ →
    (0 ∈ lagSet M M₁ H') ∧ (∀ l ∈ lagSet M M₁ H', ∀ l' ∈ lagSet M M₁ H', l + l' ∈ lagSet M M₁ H') ∧
    (∀ t : ℝ, ∀ l ∈ lagSet M M₁ H', t • l ∈ lagSet M M₁ H') ∧
    (∀ l ∈ lagSet M M₁ H', ∀ l' ∈ lagSet M M₁ H', trP F _ l.1 l'.2 = trP F _ l'.1 l.2) ∧
    ∀ v, (∀ l ∈ lagSet M M₁ H', trP F _ v.1 l.2 = trP F _ l.1 v.2) → v ∈ lagSet M M₁ H' := by
  intro F E _ _ _ _ _ σ B n d d₁ r s r' s' i₀ i₁ X W W₁ H' M M₁ hB hX hW hH
  have hω := fun w w' => GlobalTheory.ArchSch.trace_evI_darboux M.co w w'
  have hω₁ := fun z z' => GlobalTheory.ArchSch.trace_evI_darboux M₁.co z z'

  have hS₁ : ∀ z z' : Matrix (Fin n) (Fin d₁) (AE F E), arch F (M₁.co.e z).1 = 0 → arch F (M₁.co.e z').1 = 0 →
      Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
        (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W₁.J) z z')) = 0 := by
    intro z z' hz hz'
    rw [hω₁, hz, hz']
    simp
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ⟨0, ⟨0, by simp⟩, lagL_at_zero, 0, lagL_at_zero, by simp [lagL_arch_zero], ?_⟩
    simp [lagL_arch_zero]
    rfl
  ·
    rintro l ⟨u, ⟨y, rfl⟩, hu, z, hz, hz1, rfl⟩ l' ⟨u', ⟨y', rfl⟩, hu', z', hz', hz1', rfl⟩
    refine ⟨_, ⟨y + y', rfl⟩, by rw [Matrix.add_vecMulVec]; exact lagL_at_add hu hu', z + z', lagL_at_add hz hz', ?_, ?_⟩
    · rw [map_add, Prod.fst_add, lagL_arch_add, hz1, hz1', add_zero]
    · have : Matrix.vecMulVec (y + y') (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * (z + z') * (incM F H'.ι)ᵀ =
          (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) +
          (Matrix.vecMulVec y' (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ) := by
        rw [Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]; abel
      rw [this]
      ext : 1 <;> simp only [Prod.fst_add, Prod.snd_add, LinearEquiv.map_add, lagL_arch_add] <;> abel
  ·
    rintro t l ⟨u, ⟨y, rfl⟩, hu, z, hz, hz1, rfl⟩
    refine ⟨_, ⟨realAd F t • y, rfl⟩, ?_, realAd F t • z, lagL_at_smul _ hz, ?_, ?_⟩
    · rw [← lagL_smul_vmv]; exact lagL_at_smul _ hu
    · rw [map_smul, Prod.smul_fst, lagL_arch_smul, hz1, smul_zero]
    · have : Matrix.vecMulVec (realAd F t • y) (incV F H'.x) +
          incM F (1 : Matrix (Fin n) (Fin n) E) * (realAd F t • z) * (incM F H'.ι)ᵀ =
          realAd F t • (Matrix.vecMulVec y (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ) := by
        rw [← lagL_smul_vmv, smul_add, Matrix.mul_smul, Matrix.smul_mul]
      rw [this, map_smul, Prod.smul_fst, Prod.smul_snd, lagL_arch_smul, lagL_arch_smul]
      rfl
  ·
    rintro l ⟨u, ⟨y, rfl⟩, hu, z, hz, hz1, rfl⟩ l' ⟨u', ⟨y', rfl⟩, hu', z', hz', hz1', rfl⟩
    rw [← sub_eq_zero, ← hω, lagL_dar_add_left M.co, lagL_dar_add_right M.co, lagL_dar_add_right M.co,
      GlobalTheory.LagIsotropic.symp_vecMulVec_x_eq_zero B W W₁ H' i₀ i₁ X.J hH, (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH y z').2.1,
      (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH y' z).1, GlobalTheory.SympRestrict.symp_embed_eq B W W₁ H' i₀ i₁ X.J hH, zero_add, zero_add, zero_add]
    exact hS₁ z z' hz1 hz1'
  ·
    intro v hv
    obtain ⟨w, hwA, hw1, hw2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M.co v.1 v.2
    obtain ⟨a, b, z, ha, hb, hz, rfl⟩ := GlobalTheory.ThK.DecW.decompose B W W₁ H' r' s' i₀ i₁ hW hH w hwA
    have key : ∀ w', (arch F (M.co.e w').1, arch F (M.co.e w').2) ∈ lagSet M M₁ H' →
        Algebra.trace ℝ (mixedEmbedding.mixedSpace F)
          (evI F (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)
            (Matrix.vecMulVec a (incV F H'.x) + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ +
              Matrix.vecMulVec b (incV F H'.y)) w')) = 0 := by
      intro w' hl
      have := hv _ hl
      rw [hω, hw1, hw2]
      exact sub_eq_zero.mpr this
    have hb0 : b = 0 := by
      refine GlobalTheory.ArchTraceNondeg.eq_zero_of_trace_orth B X r s GlobalTheory.ArchSch.trAE_nondeg hX b hb fun c hc => ?_
      have hl : (arch F (M.co.e (Matrix.vecMulVec c (incV F H'.x))).1,
          arch F (M.co.e (Matrix.vecMulVec c (incV F H'.x))).2) ∈ lagSet M M₁ H' := by
        refine ⟨_, ⟨c, rfl⟩, lagL_at_vmv hc _, 0, lagL_at_zero, by simp [lagL_arch_zero], ?_⟩
        simp
      have := key _ hl
      rwa [lagL_dar_add_left M.co, lagL_dar_add_left M.co, GlobalTheory.LagIsotropic.symp_vecMulVec_x_eq_zero B W W₁ H' i₀ i₁ X.J hH,
        (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH c z).1, GlobalTheory.ArchSch.symp_dual_iso B W W₁ H' r' s' i₀ i₁ X.J hW hH, zero_add, zero_add] at this
    subst hb0
    have hp : arch F (M₁.co.e z).1 = 0 := by
      funext i
      refine GlobalTheory.mixedSpace_traceForm_nondegenerate F _ fun η => ?_
      obtain ⟨z', hz'A, hz'1, hz'2⟩ := GlobalTheory.ArchSch.exists_darboux_lift M₁.co 0 (Pi.single i η)
      have hl : (arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ)).1,
          arch F (M.co.e (incM F (1 : Matrix (Fin n) (Fin n) E) * z' * (incM F H'.ι)ᵀ)).2) ∈ lagSet M M₁ H' := by
        refine ⟨0, ⟨0, by simp⟩, lagL_at_zero, z', hz'A, hz'1, ?_⟩
        simp
      have := key _ hl
      rw [lagL_dar_add_left M.co, lagL_dar_add_left M.co, (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH a z').2.1,
        GlobalTheory.SympRestrict.symp_embed_eq B W W₁ H' i₀ i₁ X.J hH, (GlobalTheory.ArchSch.OrthPlane.symp_tens_orth B W W₁ H' r' s' i₀ i₁ X.J hB hW hH 0 z').2.2, zero_add, add_zero,
        hω₁, hz'1, hz'2] at this
      simpa [mixedTracePairing_apply, Pi.single_apply] using this
    refine ⟨_, ⟨a, rfl⟩, lagL_at_vmv ha _, z, hz, hp, ?_⟩
    refine Prod.ext ?_ ?_ <;> simp [← hw1, ← hw2]

end GlobalTheory.ArchSch
