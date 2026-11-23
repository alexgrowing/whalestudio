import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsGenericIffIsGenericFor
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviBlockSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WittRankLeSkewSignature
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsSplitChartSplitChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasureFundDomLtTop
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripSizesSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBlockEmb
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqId
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.LeviBlockExponent GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
  GlobalTheory.UAut GlobalTheory.SiegelSet GlobalTheory.ThK.SquareIntegrability GlobalTheory.CuspBlock GlobalTheory.LFun.SplitTie
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
open scoped TensorProduct
open Matrix
open Formalism.UG (cT)

namespace GlobalTheory.BlockFormsEmb

section Alg
variable {R : Type} [CommRing R] {n d : ℕ}

theorem cT_add' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A + B) = cT s A + cT s B :=
  Matrix.ext fun i j => by simp [cT]

theorem cT_sub' (s : R →+* R) {m p : Type} (A B : Matrix m p R) : cT s (A - B) = cT s A - cT s B :=
  Matrix.ext fun i j => by simp [cT]

def blk (a b : Matrix (Fin n) (Fin d) R) (α β : Matrix (Fin d) (Fin n) R) (H K : Matrix (Fin d) (Fin d) R) :
    Matrix (Fin n) (Fin n) R := 1 + a * (H - 1) * α + b * (K - 1) * β

variable {a b : Matrix (Fin n) (Fin d) R} {α β : Matrix (Fin d) (Fin n) R}

theorem blk_one : blk a b α β 1 1 = 1 := by simp [blk]

theorem blk_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (H K H' K' : Matrix (Fin d) (Fin d) R) :
    blk a b α β H K * blk a b α β H' K' = blk a b α β (H * H') (K * K') := by
  first
  | exact @_root_.GlobalTheory.SquareDistanceExpansion.main
  | exact _root_.GlobalTheory.SquareDistanceExpansion.main
  | (apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareDistanceExpansion.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareDistanceExpansion.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareDistanceExpansion.main ..)

theorem blk_unitary (s : R →+* R) (Jm : Matrix (Fin n) (Fin n) R)
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT s α = Jm * b) (hβ : cT s β = Jm * a) (ha : cT s a * Jm = β) (hb : cT s b * Jm = α)
    (H K : Matrix (Fin d) (Fin d) R) (h1 : cT s K * H = 1) (h2 : cT s H * K = 1) :
    cT s (blk a b α β H K) * Jm * blk a b α β H K = Jm := by
  have key : cT s (blk a b α β H K) * Jm = Jm * blk a b α β (cT s K) (cT s H) := by
    unfold blk
    rw [cT_add', cT_add', Formalism.UG.cT_one, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cT_sub', cT_sub',
      Formalism.UG.cT_one, hα, hβ]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.mul_one, Matrix.one_mul, Matrix.mul_assoc, ha, hb]
    abel
  rw [key, Matrix.mul_assoc, blk_mul hαa hβb hαb hβa, h1, h2, blk_one, Matrix.mul_one]

end Alg

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.BlockForms

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem sigR_inclR (σ : E →ₐ[F] E) (x : E) :
    sigR (AF F) σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := by
  simp [sigR, inclR]

theorem cT_adMat (σ : E →ₐ[F] E) {m p : Type} (Z : Matrix m p E) :
    cT (sigR (AF F) σ) (adMat F Z) = adMat F (cT (σ : E →+* E) Z) :=
  Matrix.ext fun i j => by simp only [cT, adMat, Matrix.transpose_apply, Matrix.map_apply, sigR_inclR]; rfl

theorem adMat_mul' {m p q : Type} [Fintype p] (A : Matrix m p E) (B : Matrix p q E) :
    adMat F (A * B) = adMat F A * adMat F B := Matrix.map_mul

theorem adMat_one' {m : Type} [Fintype m] [DecidableEq m] : adMat F (1 : Matrix m m E) = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem adMat_zero' {m p : Type} : adMat F (0 : Matrix m p E) = 0 := Matrix.map_zero _ (map_zero _)

theorem sigR_sigR' (σ : E →ₐ[F] E) (hσ : ∀ x, σ (σ x) = x) (z : AF F ⊗[F] E) :
    sigR (AF F) σ (sigR (AF F) σ z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul a x => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem blkCols_gram {n r l d : ℕ} (h : l + d ≤ r) (σ : E →ₐ[F] E) (J : Matrix (Fin n) (Fin n) E)
    (Z W : Matrix (Fin n) (Fin r) E) :
    cT (σ : E →+* E) (blkCols h Z) * J * blkCols h W =
      (cT (σ : E →+* E) Z * J * W).submatrix (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r))
        (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := by
  first
  | rfl
  | (ext i j; simp [Matrix.mul_apply, blkCols, cT])

def embMat (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
    (a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)) (α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E))
    (g : GlobalTheory.CuspRep.GA E d) : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) :=
  blk a b α β (g.1.map Φ.symm) (cT (sigR (AF F) σ) ((g⁻¹).1.map Φ.symm))

variable (σ : E →ₐ[F] E) (Φ : AF F ⊗[F] E ≃+* AdeleRing (𝓞 E) E) {n d : ℕ}
  {a b : Matrix (Fin n) (Fin d) (AF F ⊗[F] E)} {α β : Matrix (Fin d) (Fin n) (AF F ⊗[F] E)}

theorem map_symm_mul (A B : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)) :
    (A * B).map Φ.symm = A.map Φ.symm * B.map Φ.symm := Matrix.map_mul (f := Φ.symm.toRingHom)

theorem map_symm_one : (1 : Matrix (Fin d) (Fin d) (AdeleRing (𝓞 E) E)).map Φ.symm = 1 :=
  Matrix.map_one _ (map_zero _) (map_one _)

theorem embMat_one : embMat σ Φ a b α β 1 = 1 := by
  simp only [embMat, inv_one, Units.val_one, map_symm_one, Formalism.UG.cT_one, blk_one]

theorem embMat_mul (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (g g' : GlobalTheory.CuspRep.GA E d) : embMat σ Φ a b α β (g * g') = embMat σ Φ a b α β g * embMat σ Φ a b α β g' := by
  unfold embMat
  rw [blk_mul hαa hβb hαb hβa, Units.val_mul, _root_.mul_inv_rev, Units.val_mul, map_symm_mul, map_symm_mul, Formalism.UG.cT_mul]

theorem embMat_unitary (hσ : ∀ x, σ (σ x) = x) (Jm : Matrix (Fin n) (Fin n) (AF F ⊗[F] E))
    (hαa : α * a = 1) (hβb : β * b = 1) (hαb : α * b = 0) (hβa : β * a = 0)
    (hα : cT (sigR (AF F) σ) α = Jm * b) (hβ : cT (sigR (AF F) σ) β = Jm * a)
    (ha : cT (sigR (AF F) σ) a * Jm = β) (hb : cT (sigR (AF F) σ) b * Jm = α) (g : GlobalTheory.CuspRep.GA E d) :
    cT (sigR (AF F) σ) (embMat σ Φ a b α β g) * Jm * embMat σ Φ a b α β g = Jm := by
  have hcc : ∀ A : Matrix (Fin d) (Fin d) (AF F ⊗[F] E), cT (sigR (AF F) σ) (cT (sigR (AF F) σ) A) = A :=
    fun A => Matrix.ext fun i j => by simp only [cT, Matrix.transpose_apply, Matrix.map_apply]; exact sigR_sigR' σ hσ _
  have hgg : (g⁻¹).1.map Φ.symm * g.1.map Φ.symm = 1 := by
    rw [← map_symm_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, map_symm_one]
  unfold embMat
  refine blk_unitary _ Jm hαa hβb hαb hβa hα hβ ha hb _ _ ?_ ?_
  · rw [hcc, hgg]
  · rw [← Formalism.UG.cT_mul, hgg, Formalism.UG.cT_one]

end Main

theorem exists_blockEmb : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [IsTotallyComplex E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
    ∀ (r : ℕ) (Xf Yf : Matrix (Fin n) (Fin r) E), IsWittFrame σ J Xf Yf → ∀ (l d : ℕ) (h : l + d ≤ r), ∃ ι : GlobalTheory.CuspRep.GA E d →* GAd σ J, GlobalTheory.BlockForms.IsBlockEmb σ J Xf Yf h ι := by
  intro F E _ _ _ _ _ _ σ hcm n J hJ r Xf Yf hW l d h
  obtain ⟨Φ, j, hc1, hc2, hj, hΦ⟩ := GlobalTheory.HeckeBridge.exists_tensor_adele_equiv F E σ hcm
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hJT : cT (σ : E →+* E) J = J := Matrix.ext fun i j => hJ.1 i j
  have hcc : ∀ {m p : Type} (Z : Matrix m p E), cT (σ : E →+* E) (cT (σ : E →+* E) Z) = Z :=
    fun Z => Matrix.ext fun _ _ => hσ _
  have hyx : cT (σ : E →+* E) Yf * J * Xf = 1 := by
    have := congrArg (cT (σ : E →+* E)) hW.xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, hcc, hJT, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  have he : Function.Injective (fun j : Fin d => (⟨l + j.val, by omega⟩ : Fin r)) := fun i k e =>
    Fin.ext (by have := congrArg Fin.val e; simp only at this; omega)
  have q1 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Xf = 1 := by
    rw [blkCols_gram, hyx, Matrix.submatrix_one _ he]
  have q2 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Yf = 1 := by
    rw [blkCols_gram, hW.xy, Matrix.submatrix_one _ he]
  have q3 : cT (σ : E →+* E) (blkCols h Yf) * J * blkCols h Yf = 0 := by
    rw [blkCols_gram, hW.yy, Matrix.submatrix_zero]; rfl
  have q4 : cT (σ : E →+* E) (blkCols h Xf) * J * blkCols h Xf = 0 := by
    rw [blkCols_gram, hW.xx, Matrix.submatrix_zero]; rfl
  have hαa : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Xf) = 1 := by
    rw [← adMat_mul', q1, adMat_one']
  have hβb : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Yf) = 1 := by
    rw [← adMat_mul', q2, adMat_one']
  have hαb : adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) * adMat F (blkCols h Yf) = 0 := by
    rw [← adMat_mul', q3, adMat_zero']
  have hβa : adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) * adMat F (blkCols h Xf) = 0 := by
    rw [← adMat_mul', q4, adMat_zero']
  have hα : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) = adMat F J * adMat F (blkCols h Yf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have hβ : cT (sigR (AF F) σ) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J)) = adMat F J * adMat F (blkCols h Xf) := by
    rw [cT_adMat, Formalism.UG.cT_mul, hcc, hJT, adMat_mul']
  have ha : cT (sigR (AF F) σ) (adMat F (blkCols h Xf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Xf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  have hb : cT (sigR (AF F) σ) (adMat F (blkCols h Yf)) * adMat F J = adMat F (cT (σ : E →+* E) (blkCols h Yf) * J) := by
    rw [cT_adMat, ← adMat_mul']
  let M := embMat σ Φ (adMat F (blkCols h Xf)) (adMat F (blkCols h Yf))
    (adMat F (cT (σ : E →+* E) (blkCols h Yf) * J)) (adMat F (cT (σ : E →+* E) (blkCols h Xf) * J))
  have hMmul : ∀ g g', M (g * g') = M g * M g' := embMat_mul σ Φ hαa hβb hαb hβa
  have hMone : M 1 = 1 := embMat_one σ Φ
  have hMu : ∀ g, cT (sigR (AF F) σ) (M g) * JR (AF F) J * M g = JR (AF F) J :=
    embMat_unitary σ Φ hσ (adMat F J) hαa hβb hαb hβa hα hβ ha hb
  let U : GlobalTheory.CuspRep.GA E d → GL (Fin n) (AF F ⊗[F] E) := fun g =>
    ⟨M g, M g⁻¹, by rw [← hMmul, mul_inv_cancel, hMone], by rw [← hMmul, inv_mul_cancel, hMone]⟩
  let ι : GlobalTheory.CuspRep.GA E d →* GAd σ J :=
    { toFun := fun g => (⟨U g, hMu g⟩ : HR (AF F) σ J)
      map_one' := Subtype.ext (Units.ext hMone)
      map_mul' := fun g g' => Subtype.ext (Units.ext (hMmul g g')) }
  exact ⟨ι, Φ, j, hc1, hc2, hj, hΦ, fun g => rfl⟩

end GlobalTheory.BlockFormsEmb
