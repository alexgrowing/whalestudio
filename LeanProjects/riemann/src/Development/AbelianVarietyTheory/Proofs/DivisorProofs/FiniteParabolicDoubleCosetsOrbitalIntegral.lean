import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ParP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedCentralizerBlockLeParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovApply
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactUnitaryIntegralPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsUnitDetKrylovMatrixOfSeparableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KrylovMatrixConjEqOfCharpolyEqStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactInvertibleKrylovMatricesStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.LeviDesc.OrbFin
open GlobalTheory.LeviDesc.Krylov

theorem exists_cyclic {F : Type} [Field F] {r : ℕ} (y : Matrix (Fin r) (Fin r) F) (hy : y.charpoly.Separable) :
    ∃ e : Fin r → F, IsUnit (krylov y e).det :=
  GlobalTheory.T.exists_isUnit_det_krylovMatrix_of_separable y hy

theorem krylov_conj_eq {F : Type} [Field F] {r : ℕ} (y y' : Matrix (Fin r) (Fin r) F) (e e' : Fin r → F)
    (hc : y.charpoly = y'.charpoly) (he : IsUnit (krylov y e).det) (he' : IsUnit (krylov y' e').det) :
    (krylov y e)⁻¹ * y * krylov y e = (krylov y' e')⁻¹ * y' * krylov y' e' :=
  GlobalTheory.T.krylovMatrix_conj_eq_of_charpoly_eq y y' e e' hc he he'

theorem isClosed_charpoly_eq (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ)
    (χ : (w.adicCompletion E)[X]) : IsClosed {y : GLw r w | y.val.charpoly = χ} := by
  haveI : CharZero (w.adicCompletion E) :=
    charZero_of_injective_algebraMap (algebraMap E (w.adicCompletion E)).injective
  haveI : Infinite (w.adicCompletion E) := Infinite.of_injective Nat.cast Nat.cast_injective
  have hset : {y : GLw r w | y.val.charpoly = χ} =
      ⋂ t : w.adicCompletion E, {y : GLw r w | ((Matrix.scalar (Fin r) t) - y.val).det = χ.eval t} := by
    ext y
    simp only [Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · intro hy t; rw [← Matrix.eval_charpoly, hy]
    · intro hy; exact Polynomial.funext fun t => by rw [Matrix.eval_charpoly]; exact hy t
  rw [hset]
  refine isClosed_iInter fun t => isClosed_eq ?_ continuous_const
  exact (continuous_const.sub Units.continuous_val).matrix_det

theorem exists_compact_krylov (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (Ω : Set (GLw r w))
    (hΩ : IsCompact Ω) (h : ∀ y ∈ Ω, ∃ e, IsUnit (krylov y.val e).det) :
    ∃ C : Set (GLw r w), IsCompact C ∧ ∀ y ∈ Ω, ∃ e, ∃ c ∈ C, c.val = krylov y.val e :=
  GlobalTheory.T.exists_compact_invertible_krylovMatrices E w r Ω hΩ h

theorem isOpen_KGL (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) :
    IsOpen (GlobalTheory.LFun.KGL w r : Set (GLw r w)) :=
  GlobalTheory.LFun.IntPtsUnitary.isOpen_GLint _ (Valued.isOpen_integer (w.adicCompletion E))

theorem orbit_fin (E : Type) [Field E] [NumberField E] (w : Pl E) (r : ℕ) (γ : GLw r w)
    (hs : γ.val.charpoly.Separable) (Ω : Set (GLw r w)) (hΩ : IsCompact Ω) :
    ∃ T : Set (GLw r w), T.Finite ∧ ∀ q : GLw r w, q⁻¹ * γ * q ∈ Ω →
      ∃ z : GLw r w, z * γ = γ * z ∧ ∃ t ∈ T, ∃ k ∈ GlobalTheory.LFun.KGL w r, q = z * t * k := by
  set Ωχ := Ω ∩ {y : GLw r w | y.val.charpoly = γ.val.charpoly} with hΩχ
  have hcpt : IsCompact Ωχ := hΩ.inter_right (isClosed_charpoly_eq E w r _)
  have hcyc : ∀ y ∈ Ωχ, ∃ e, IsUnit (krylov y.val e).det := fun y hy =>
    exists_cyclic _ (by rw [hy.2]; exact hs)
  obtain ⟨C, hC, hCy⟩ := exists_compact_krylov E w r Ωχ hcpt hcyc
  obtain ⟨f, hf⟩ := exists_cyclic γ.val hs
  have hfu : IsUnit (krylov γ.val f) := (Matrix.isUnit_iff_isUnit_det _).2 hf
  set Bf : GLw r w := hfu.unit with hBf
  set D : Set (GLw r w) := (fun c => Bf * c⁻¹) '' C with hD
  have hDc : IsCompact D := hC.image (continuous_const.mul continuous_inv)
  have hKo := isOpen_KGL E w r
  obtain ⟨T, hT⟩ := hDc.elim_finite_subcover (fun c : GLw r w => (fun x => c⁻¹ * x) ⁻¹' (GlobalTheory.LFun.KGL w r : Set (GLw r w)))
    (fun c => hKo.preimage (continuous_const.mul continuous_id)) (fun x _ => Set.mem_iUnion.2 ⟨x, by simp⟩)
  refine ⟨(T : Set (GLw r w)), T.finite_toSet, fun q hq => ?_⟩
  have hy : q⁻¹ * γ * q ∈ Ωχ := by
    refine ⟨hq, ?_⟩
    show ((q⁻¹ * γ * q : GLw r w) : Matrix (Fin r) (Fin r) (w.adicCompletion E)).charpoly = γ.val.charpoly
    have := Matrix.charpoly_units_conj (q⁻¹) γ.val
    simpa [Matrix.coe_units_inv] using this
  obtain ⟨e, c, hcC, hce⟩ := hCy _ hy
  have he : IsUnit (krylov (q⁻¹ * γ * q : GLw r w).val e).det := by
    rw [← hce, ← Matrix.isUnit_iff_isUnit_det]; exact c.isUnit
  have hconj := krylov_conj_eq _ _ e f (hy.2) he hf
  have h1 : c⁻¹ * (q⁻¹ * γ * q) * c = Bf⁻¹ * γ * Bf := by
    ext1
    rw [Units.val_mul (c⁻¹ * (q⁻¹ * γ * q)) c, Units.val_mul c⁻¹ (q⁻¹ * γ * q), Units.val_mul (Bf⁻¹ * γ) Bf,
      Units.val_mul Bf⁻¹ γ, Matrix.coe_units_inv c, Matrix.coe_units_inv Bf, hce, hBf, IsUnit.unit_spec]
    exact hconj
  have hxD : Bf * c⁻¹ ∈ D := ⟨c, hcC, rfl⟩
  obtain ⟨t, htT, ht⟩ := Set.mem_iUnion₂.1 (hT hxD)
  refine ⟨q * c * Bf⁻¹, ?_, t, htT, t⁻¹ * (Bf * c⁻¹), ht, by group⟩
  calc q * c * Bf⁻¹ * γ = q * c * (Bf⁻¹ * γ * Bf) * Bf⁻¹ := by group
    _ = q * c * (c⁻¹ * (q⁻¹ * γ * q) * c) * Bf⁻¹ := by rw [h1]
    _ = γ * (q * c * Bf⁻¹) := by group

theorem avg_ne_zero_exists {H : Type} [Group H] (u : H → ℂ) (h : avg u ≠ 0) : ∃ x, u x ≠ 0 := by
  by_contra hc
  push_neg at hc
  apply h
  simp [avg, hc]

theorem charpoly_blk_separable (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E)
    (m : GLw a w × GLw b w) (hs : (m.1.val.charpoly * m.2.val.charpoly).Separable) :
    (blk h w m 0 : GLw n w).val.charpoly.Separable := by
  have hM : IsUnit (Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
      (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val)) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_reindex_self, Matrix.mul_zero, Matrix.det_fromBlocks_zero₁₂]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).mp m.2.isUnit)
  have hval : ((blk h w m 0 : GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.reindex (finSumFinEquiv.trans (finCongr h)) (finSumFinEquiv.trans (finCongr h))
        (Matrix.fromBlocks m.1.val (m.1.val * (0 : Matrix (Fin a) (Fin b) (w.adicCompletion E))) 0 m.2.val) := by
    simp only [blk]
    rw [dif_pos hM]
    rfl
  rw [hval, Matrix.charpoly_reindex, Matrix.mul_zero, Matrix.charpoly_fromBlocks_zero₁₂]
  exact hs

theorem fin_doubleCosets : ∀ (E : Type) [Field E] [NumberField E] (n a b : ℕ) (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ), (∃ K' : Subgroup (GLw n w), IsOpen (K' : Set (GLw n w)) ∧ IsHecke K' f) → ∀ m : GLw a w × GLw b w, (m.1.val.charpoly * m.2.val.charpoly).Separable → ∀ hγ : blk h w m 0 ∈ GlobalTheory.LeviDesc.parP a n w, {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) (⟨blk h w m 0, hγ⟩ : GlobalTheory.LeviDesc.parP a n w) : Set (GlobalTheory.LeviDesc.parP a n w)) (((GlobalTheory.LFun.KGL w n).subgroupOf (GlobalTheory.LeviDesc.parP a n w) : Subgroup _) : Set (GlobalTheory.LeviDesc.parP a n w)) | GlobalTheory.LeviDesc.cavg (GlobalTheory.LFun.KGL w n) f (((Quotient.out d)⁻¹ * ⟨blk h w m 0, hγ⟩ * Quotient.out d : GlobalTheory.LeviDesc.parP a n w) : GLw n w) ≠ 0}.Finite := by
  intro E _ _ n a b h w f hf m hs hγ
  obtain ⟨K', -, hsupp, -⟩ := hf
  set γ : GLw n w := blk h w m 0 with hγdef
  set P := GlobalTheory.LeviDesc.parP a n w
  set K := GlobalTheory.LFun.KGL w n
  set γP : P := ⟨γ, hγ⟩
  obtain ⟨T, hT, hTq⟩ := orbit_fin E w n γ (charpoly_blk_separable E n a b h w m hs) (tsupport f) hsupp
  have hcent : ∀ z : GLw n w, z * γ = γ * z → z ∈ P := fun z hz =>
    GlobalTheory.LeviDesc.twCent_blk_le_parP E n a b h w m hs (show z * γ = γ * MonoidHom.id _ z from hz)
  let Q : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) → GLw n w → Prop :=
    fun d t => t ∈ T ∧ ∃ z : GLw n w, z * γ = γ * z ∧ ∃ k ∈ K, ((Quotient.out d : P) : GLw n w) = z * t * k
  have hex : ∀ d ∈ {d : DoubleCoset.Quotient (twCent (MonoidHom.id _) γP : Set P) ((K.subgroupOf P : Subgroup P) : Set P) |
      GlobalTheory.LeviDesc.cavg K f (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) ≠ 0}, ∃ t, Q d t := by
    intro d hd
    obtain ⟨k, hk⟩ := avg_ne_zero_exists _ hd
    set p : GLw n w := ((Quotient.out d : P) : GLw n w)
    have hmem : (p * k)⁻¹ * γ * (p * k) ∈ tsupport f := by
      apply subset_tsupport
      have : (p * k)⁻¹ * γ * (p * k) = (k : GLw n w)⁻¹ * (((Quotient.out d)⁻¹ * γP * Quotient.out d : P) : GLw n w) * k := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, p, γP]; group
      rw [this]; exact hk
    obtain ⟨z, hz, t, ht, k₁, hk₁, hq⟩ := hTq _ hmem
    refine ⟨t, ht, z, hz, k₁ * (k : GLw n w)⁻¹, K.mul_mem hk₁ (K.inv_mem k.2), ?_⟩
    rw [← mul_assoc, ← hq, mul_inv_cancel_right]
  refine Set.Finite.of_injOn (f := fun d => if hd : ∃ t, Q d t then hd.choose else 1) (t := T) ?_ ?_ hT
  · intro d hd
    simp only [dif_pos (hex d hd)]
    exact (hex d hd).choose_spec.1
  · intro d₁ hd₁ d₂ hd₂ heq
    simp only [dif_pos (hex d₁ hd₁), dif_pos (hex d₂ hd₂)] at heq
    obtain ⟨-, z₁, hz₁, k₁, hk₁, hp₁⟩ := (hex d₁ hd₁).choose_spec
    obtain ⟨-, z₂, hz₂, k₂, hk₂, hp₂⟩ := (hex d₂ hd₂).choose_spec
    rw [heq] at hp₁
    set t := (hex d₂ hd₂).choose
    have hzP : z₂ * z₁⁻¹ ∈ P := hcent _ (by
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group)
    set hP : P := ⟨z₂ * z₁⁻¹, hzP⟩
    have hcP : hP ∈ twCent (MonoidHom.id _) γP := by
      show hP * γP = γP * MonoidHom.id _ hP
      apply Subtype.ext
      simp only [Subgroup.coe_mul, MonoidHom.id_apply, hP, γP]
      calc z₂ * z₁⁻¹ * γ = z₂ * (z₁⁻¹ * (γ * z₁)) * z₁⁻¹ := by group
        _ = z₂ * (z₁⁻¹ * (z₁ * γ)) * z₁⁻¹ := by rw [hz₁]
        _ = (z₂ * γ) * z₁⁻¹ := by group
        _ = (γ * z₂) * z₁⁻¹ := by rw [hz₂]
        _ = γ * (z₂ * z₁⁻¹) := by group
    set kP : P := (Quotient.out d₁)⁻¹ * hP⁻¹ * Quotient.out d₂
    have hkv : (kP : GLw n w) = k₁⁻¹ * k₂ := by
      simp only [kP, hP, Subgroup.coe_mul, Subgroup.coe_inv, hp₁, hp₂]; group
    have hkK : kP ∈ K.subgroupOf P := by
      rw [Subgroup.mem_subgroupOf, hkv]; exact K.mul_mem (K.inv_mem hk₁) hk₂
    rw [← DoubleCoset.out_eq' _ _ d₁, ← DoubleCoset.out_eq' _ _ d₂, DoubleCoset.eq]
    exact ⟨hP, hcP, kP, hkK, by simp only [kP]; group⟩

end GlobalTheory.LeviDesc.OrbFin
