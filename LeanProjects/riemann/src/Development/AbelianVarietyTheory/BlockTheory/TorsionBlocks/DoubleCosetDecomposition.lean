import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers

open NumberField Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice
open scoped TensorProduct

section Level

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)

theorem finMat_one : finMat σ J (1 : HA (AF F) σ J) = 1 := by
  show (((1 : GL (Fin M) (AF F ⊗[F] E)) : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = 1
  rw [Units.val_one]
  exact Matrix.map_one _ (map_zero _) (map_one _)

theorem finMat_mul (g h : HA (AF F) σ J) : finMat σ J (g * h) = finMat σ J g * finMat σ J h := by
  show (((HA.mat (AF F) σ J g * HA.mat (AF F) σ J h : GL (Fin M) (AF F ⊗[F] E)) :
    Matrix (Fin M) (Fin M) (AF F ⊗[F] E))).map _ = _
  rw [Units.val_mul]
  exact Matrix.map_mul (f := (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)).toRingHom)

def levelK (L : Set (Fin M → E)) : Subgroup (HA (AF F) σ J) where
  carrier := {h | ∀ y, y ∈ latHat F E L ↔ (finMat σ J h).mulVec y ∈ latHat F E L}
  one_mem' := by
    intro y
    rw [finMat_one, Matrix.one_mulVec]
  mul_mem' := by
    intro a b ha hb y
    rw [finMat_mul, ← Matrix.mulVec_mulVec]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro a ha y
    have := ha ((finMat σ J a⁻¹).mulVec y)
    rw [Matrix.mulVec_mulVec, ← finMat_mul, mul_inv_cancel, finMat_one, Matrix.one_mulVec] at this
    exact this.symm

def ratPts : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J

def stabAt (K : Subgroup (HA (AF F) σ J)) (g : HA (AF F) σ J) : Subgroup (HA (AF F) σ J) :=
  ratPts σ J ⊓ K.map (MulAut.conj g).toMonoidHom

def IsDoubleCosetReps (K : Subgroup (HA (AF F) σ J)) {n : ℕ} (g : Fin n → HA (AF F) σ J) : Prop :=
  ∀ x : HA (AF F) σ J, ∃! i : Fin n, ∃ γ ∈ ratPts σ J, ∃ k ∈ K, x = γ * g i * k

theorem mem_stabAt (K : Subgroup (HA (AF F) σ J)) (g γ : HA (AF F) σ J) :
    γ ∈ stabAt σ J K g ↔ γ ∈ ratPts σ J ∧ g⁻¹ * γ * g ∈ K := by
  unfold stabAt
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  refine and_congr_right fun _ => ⟨?_, fun h => ⟨_, h, by simp [mul_assoc]⟩⟩
  rintro ⟨k, hk, rfl⟩
  simpa [mul_assoc] using hk

theorem IsDoubleCosetReps.pos {K : Subgroup (HA (AF F) σ J)} {n : ℕ} {g : Fin n → HA (AF F) σ J}
    (h : IsDoubleCosetReps σ J K g) : 0 < n := by
  obtain ⟨i, -⟩ := h 1
  exact Fin.pos i

end Level

section Space

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]

def latCoord (W : HSpace E) : Set (Fin W.rank → E) := {x | ∑ i, x i • W.frame i ∈ W.L0}

def levelW (hc : CMData F E) (W : HSpace E) : Subgroup (HA (AF F) hc.sig W.gram) :=
  levelK hc.sig W.gram (latCoord W)

def DecompAt (hc : CMData F E) (W : HSpace E) : Prop :=
  IsOpen (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  MeasurableSet (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  ∃ (n : ℕ) (g : Fin n → HA (AF F) hc.sig W.gram),
    IsDoubleCosetReps hc.sig W.gram (levelW hc W) g ∧
    (∀ i, Finite (stabAt hc.sig W.gram (levelW hc W) (g i))) ∧
    ∑ i, ((Nat.card (stabAt hc.sig W.gram (levelW hc W) (g i)) : ℕ) : ℝ)⁻¹ = Formalism.HermitianLatticesTheory.mass W.hT W.L0

def IsLatticeOf (hc : CMData F E) (W : HSpace E) (g : HA (AF F) hc.sig W.gram)
    (N : Submodule (𝓞 E) W.V) : Prop :=
  ∀ x : W.V, x ∈ N ↔ ∃ y ∈ latHat F E (latCoord W),
    (finMat hc.sig W.gram g).mulVec y = fun j => inclR (Af F) (W.frame.repr x j)

open Classical in

def DecompLatAt (hc : CMData F E) (W : HSpace E) : Prop :=
  DecompAt hc W ∧
  IsCompact (levelW hc W : Set (HA (AF F) hc.sig W.gram)) ∧
  (∀ (n : ℕ) (g : Fin n → HA (AF F) hc.sig W.gram), IsDoubleCosetReps hc.sig W.gram (levelW hc W) g →
    ∃ N : Fin n → Submodule (𝓞 E) W.V,
      (∀ i, IsLatticeOf hc W (g i) (N i)) ∧ Function.Injective N ∧
      Formalism.ThetaLiftIndependence.IsClassReps W.hT W.L0 (Finset.univ.image N) ∧
      ∀ i, Finite (stabAt hc.sig W.gram (levelW hc W) (g i)) ∧ (Formalism.ThetaLiftIndependence.autL W.hT (N i)).Finite ∧
        Nat.card (stabAt hc.sig W.gram (levelW hc W) (g i)) = Nat.card (Formalism.ThetaLiftIndependence.autL W.hT (N i))) ∧
  Formalism.HermitianLatticesTheory.genus W.hT W.L0 = {N | Submodule.IsLattice E N ∧ Formalism.HermitianLatticesTheory.IsUnimodular W.hT N}

end Space

def DecompAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompAt hc W

def DecompLatAll : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (hc : CMData F E) (W : HSpace E), W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompLatAt hc W

def Decomp (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) → DecompAt D.sp.cm W

end GlobalTheory.IndefiniteRowSideFullHecke.LevelSubgroupStabilizers
