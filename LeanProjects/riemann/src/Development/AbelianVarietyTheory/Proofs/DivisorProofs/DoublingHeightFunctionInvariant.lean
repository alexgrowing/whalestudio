import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaOn
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFinsetOfEventually
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LintegralFintypeProdEqProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdemSmulUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompMemOfIsStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IdeleCharacterNormEulerFactorization
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEmbeddingSkewHermitian
open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling GlobalTheory.ThK.Bot GlobalTheory.ThK.ConeEuler

noncomputable section

namespace GlobalTheory.ThK.Bot.HgtMul

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem idem_mul_det {A : Type} [CommRing A] {n : ℕ} {e : A} (he : e * e = e) {M N : Matrix (Fin n) (Fin n) A}
    (h : e • M = e • N) : e * M.det = e * N.det := by
  have hp : e ^ (n + 1) = e := IsIdempotentElem.pow_succ_eq n he
  have h1 := congrArg (fun Y => e * Matrix.det Y) h
  simp only [Matrix.det_smul, Fintype.card_fin] at h1
  rwa [← mul_assoc, ← mul_assoc, ← pow_succ', hp] at h1

theorem det_idem {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} {ε : AF F} (hε : ε * ε = ε)
    (G : Matrix (Fin n) (Fin n) A) :
    (ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)).det = ε • G.det + (1 - ε) • (1 : A) := by
  have h1 := idem_mul_one_sub hε
  have h2 := one_sub_idem hε
  have e1 := idem_mul_det (e := algebraMap (AF F) A ε) (by rw [← map_mul, hε])
    (M := ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)) (N := G)
    (by simp only [algebraMap_smul, smul_add, smul_smul, hε, h1, zero_smul, add_zero])
  have e2 := idem_mul_det (e := algebraMap (AF F) A (1 - ε)) (by rw [← map_mul, h2])
    (M := ε • G + (1 - ε) • (1 : Matrix (Fin n) (Fin n) A)) (N := 1)
    (by simp only [algebraMap_smul, smul_add, smul_smul, mul_comm (1 - ε) ε, h2, h1, zero_smul, zero_add])
  rw [Matrix.det_one] at e2
  rw [Algebra.smul_def ε G.det, Algebra.smul_def (1 - ε) (1 : A), ← e1, ← e2, ← add_mul, ← map_add, add_sub_cancel,
    map_one, one_mul]

theorem blkMat_idem {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} (ε : AF F) (G : Matrix (Fin n) (Fin n) A) :
    ε • blkMat finSumFinEquiv G (1 : Matrix (Fin n) (Fin n) A) + (1 - ε) • (1 : Matrix (Fin (n + n)) (Fin (n + n)) A) =
      blkMat finSumFinEquiv (ε • G + (1 - ε) • 1) 1 := by
  rw [← blkMat_one (finSumFinEquiv (m := n) (n := n))]
  refine Matrix.ext fun a b => ?_
  obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
    simp only [blkMat, Matrix.add_apply, Matrix.smul_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.zero_apply, smul_zero, add_zero]
  rw [← add_smul, add_sub_cancel, one_smul]

theorem leviMat_lin {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} (a b : AF F)
    (M N : Matrix (Fin (n + n)) (Fin (n + n)) A) :
    leviMat finSumFinEquiv (a • M + b • N) = a • leviMat finSumFinEquiv M + b • leviMat finSumFinEquiv N := by
  refine Matrix.ext fun i j => ?_
  simp only [leviMat, Matrix.toBlocks₁₁, Matrix.toBlocks₁₂, Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply,
    Matrix.submatrix_apply, smul_add]
  abel

theorem keepsDiag_lin {A : Type} [CommRing A] [Algebra (AF F) A] {n : ℕ} (a b : AF F)
    {M N : Matrix (Fin (n + n)) (Fin (n + n)) A} (hM : KeepsDiag finSumFinEquiv M) (hN : KeepsDiag finSumFinEquiv N) :
    KeepsDiag finSumFinEquiv (a • M + b • N) := by
  rw [keepsDiag_iff] at hM hN ⊢
  intro i j
  simp only [Matrix.add_apply, Matrix.smul_apply]
  rw [add_add_add_comm, ← smul_add, ← smul_add, hM, hN, smul_add, smul_add, add_add_add_comm]

theorem hgt_idemU {n : ℕ} {J : Matrix (Fin (n + n)) (Fin (n + n)) E} {K₂ : Subgroup (UA σ J)}
    (hI : IwasawaOf finSumFinEquiv (UG (cA σ) (incM F J)).subtype (absE F E) K₂) {ε : AF F} (hε : ε * ε = ε)
    (p : siegelOf finSumFinEquiv (UG (cA σ) (incM F J)).subtype) {k : UA σ J} (hk : idemU σ J ε hε k ∈ K₂) :
    hgtOf finSumFinEquiv (UG (cA σ) (incM F J)).subtype (absE F E) K₂ (idemU σ J ε hε ((p : UA σ J) * k)) =
      absE F E (idemUnit E ε hε (aOf finSumFinEquiv (UG (cA σ) (incM F J)).subtype p)) := by
  have h1 : KeepsDiag finSumFinEquiv (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) := by
    rw [← blkMat_one (finSumFinEquiv (m := n) (n := n))]; exact (keepsDiag_blkMat _).2 rfl
  have h2 : leviMat finSumFinEquiv (1 : Matrix (Fin (n + n)) (Fin (n + n)) (AE F E)) = 1 := by
    rw [← blkMat_one (finSumFinEquiv (m := n) (n := n))]; exact leviMat_blkMat _ _ _
  have hp : idemU σ J ε hε p ∈ siegelOf finSumFinEquiv (UG (cA σ) (incM F J)).subtype :=
    mem_siegelOf.2 (keepsDiag_lin ε (1 - ε) (mem_siegelOf.1 p.2) h1)
  rw [map_mul]
  refine (hI.hgtOf_mul ⟨_, hp⟩ hk).trans (congrArg _ (Units.ext ?_))
  rw [val_idemUnit, val_aOf, val_aOf, ← det_idem hε, ← h2, ← leviMat_lin]
  rfl

theorem idemU_emb {B : Base F E} {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)}
    {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂) {ε : AF F}
    (hε : ε * ε = ε) (g : UA σ X.J) : i (idemU σ X.J ε hε g, 1) = idemU σ X₂.J ε hε (i (g, 1)) := by
  apply Subtype.ext; apply Units.ext
  change mat (i (idemU σ X.J ε hε g, 1)) = ε • mat (i (g, 1)) + (1 - ε) • 1
  rw [hD.emb, hD.emb]
  exact (blkMat_idem ε (mat g)).symm

theorem emb_mem {B : Base F E} {n : ℕ} {X : Spc F E n} {X₂ : Spc F E (n + n)}
    {i : UA σ X.J × UA σ X.J →* UA σ X₂.J} {K₂ : Subgroup (UA σ X₂.J)} (hD : IsDbl B X X₂ i K₂)
    {K : Subgroup (UA σ X.J)} (hK : IsStab B K) {k : UA σ X.J} (hk : k ∈ K) : i (k, 1) ∈ K₂ := by
  have hk' := (hK k).1 hk
  have e1 : mat (i (k, 1)) = blkMat finSumFinEquiv (mat k) 1 := hD.emb k 1
  have e2 : mat (i (k, 1))⁻¹ = blkMat finSumFinEquiv (mat k⁻¹) 1 := by
    rw [← map_inv, Prod.inv_mk, inv_one]; exact hD.emb k⁻¹ 1
  refine (hD.stab _).2 ⟨fun w => ?_, fun z hz => ?_⟩
  · rw [e1, hD.maj, blkMat_map _ _ (map_zero _), Matrix.map_one _ (map_zero _) (map_one _)]
    show _ * _ = _ * _
    rw [blkMat_mul, blkMat_mul, (hk'.1 w).eq, Matrix.mul_one, Matrix.one_mul]
  · rw [e1, e2]
    exact ⟨GlobalTheory.DefSkewStab.blkMat_mulVec_mem hD.lat (fun y hy => (hk'.2 y hy).1) hz,
      GlobalTheory.DefSkewStab.blkMat_mulVec_mem hD.lat (fun y hy => (hk'.2 y hy).2) hz⟩

theorem absE_eq_prod (l : (AE F E)ˣ) (T : Finset (Pl F)) (h : ∀ v ∉ T, absE F E (unitAt E v l) = 1) :
    absE F E l = absE F E (unitArch F E l) * ∏ v ∈ T, absE F E (unitAt E v l) := by
  have h1 := (GlobalTheory.ThK.ConeEulerChr.chr_abs_eq_finprod (1 : Chr F E) continuous_const l 1).2
  simp only [MonoidHom.one_apply, Circle.coe_one, one_mul, pow_one] at h1
  rw [finprod_eq_prod_of_mulSupport_subset (s := T) _ (fun v hv => by
    by_contra hc
    exact hv (by simp only [h v hc]; simp))] at h1
  exact_mod_cast h1

theorem hgt_one_and_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n r s' : ℕ) (X : Spc F E n), B.IsGood σ → X.IsHerm σ B r s' →
    ∀ (X₂ : Spc F E (n + n)) (i : UA σ X.J × UA σ X.J →* UA σ X₂.J) (K₂ : Subgroup (UA σ X₂.J)), IsDbl B X X₂ i K₂ →
    ∀ K : Subgroup (UA σ X.J), IsStab B K → (∀ k ∈ K, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (k, 1)) = 1) ∧
      ∀ (T : Finset (Pl F)) (g : UA σ X.J), (∀ v ∉ T, compAt σ X.J v g ∈ K) →
        hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (g, 1)) =
          hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compArch σ X.J g, 1)) *
            ∏ v ∈ T, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compAt σ X.J v g, 1)) := by
  intro F E _ _ _ _ _ σ B n r s' X _ _ X₂ i K₂ hD K hK
  have h1 : ∀ k ∈ K, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (k, 1)) = 1 :=
    fun k hk => IsIwasawa.iwAbs_of_mem hD.iwa (emb_mem hD hK hk)
  refine ⟨h1, fun T g hg => ?_⟩
  obtain ⟨p, k, hk, e⟩ := hD.iwa.1 (i (g, 1))
  obtain ⟨hkv, hki⟩ := StabComp.comp_mem_of_isStab F E σ B _ X₂ K₂ hD.stab k hk
  have hv : ∀ v, hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compAt σ X.J v g, 1)) =
      absE F E (unitAt E v (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) := fun v => by
    rw [compAt, idemU_emb hD, e]
    exact hgt_idemU hD.iwa _ p (hkv v)
  have hi : hgtOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype (absE F E) K₂ (i (compArch σ X.J g, 1)) =
      absE F E (unitArch F E (aOf finSumFinEquiv (UG (cA σ) (incM F X₂.J)).subtype p)) := by
    rw [compArch, idemU_emb hD, e]
    exact hgt_idemU hD.iwa _ p hki
  rw [hi, Finset.prod_congr rfl fun v _ => hv v, e, hD.iwa.hgtOf_mul p hk]
  exact absE_eq_prod _ T fun v hT => (hv v).symm.trans (h1 _ (hg v hT))

end GlobalTheory.ThK.Bot.HgtMul

end
