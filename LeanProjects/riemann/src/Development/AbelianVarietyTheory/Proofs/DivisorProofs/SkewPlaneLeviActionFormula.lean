import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnipParLeUnipFlag
import Development.AbelianVarietyTheory.Definitions.Foundations.ConstTermOnMulLeftOfNormalizer
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneOrthogonalGramRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsConstAlong
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousToGAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperbolicPlaneFormSkew
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteModuleGradedQuantumDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingHyperbolicThird
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineDerivativeBlockConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviCharacterCuspIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementTorusPart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewPlaneJacobianIdentityStatement
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB GlobalTheory.ThK.FlagCT GlobalTheory.ThK.FlagPar
open GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.LeviHC

noncomputable section

namespace GlobalTheory.ThK.IndCentre

open GlobalTheory.SmoothForms (gelfA)
open Formalism.REAL (GlRel qdet)
open GlobalTheory.LeviHC.MidBlock (stab mem_stab qdet_map qdet_one upperSpan_maps blk_castAdd_lt)

theorem exists_rel_qdet {M M₁ : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup M₁] [Module ℂ M₁] {n₁ : ℕ}
    (X : Fin (1 + n₁ + 1) → Fin (1 + n₁ + 1) → Module.End ℂ M) (hX : GlRel X)
    (X₁ : Fin n₁ → Fin n₁ → Module.End ℂ M₁) (M' : Submodule ℂ M) (Γ : Submodule ℂ (M × M₁))
    (hΓ : ∀ f φ, (f, φ) ∈ Γ → f ∈ M') (hM : ∀ a b, ∀ x ∈ M', X a b x ∈ M')
    (hup : ∀ a b, blk n₁ a < blk n₁ b → ∀ x ∈ M', (X a b x, (0 : M₁)) ∈ Γ)
    (hmid : ∀ a b f φ, (f, φ) ∈ Γ → (X (mid a) (mid b) f, X₁ a b φ) ∈ Γ) (lx ly : ℂ)
    (hx : ∀ f φ, (f, φ) ∈ Γ →
      (X (Fin.castAdd 1 (Fin.castAdd n₁ 0)) (Fin.castAdd 1 (Fin.castAdd n₁ 0)) f, lx • φ) ∈ Γ)
    (hy : ∀ f φ, (f, φ) ∈ Γ → (X (Fin.natAdd (1 + n₁) 0) (Fin.natAdd (1 + n₁) 0) f, ly • φ) ∈ Γ) :
    ∀ a ∈ Algebra.adjoin ℂ (Set.range (qdet X)), ∃ b ∈ Algebra.adjoin ℂ (Set.range (qdet X₁)),
      ∀ f φ, (f, φ) ∈ Γ → (a f, b φ) ∈ Γ := by
  let K : Submodule ℂ M := Γ.comap (LinearMap.inl ℂ M M₁)
  let S : Subalgebra ℂ (Module.End ℂ M × Module.End ℂ M₁) := (stab Γ).comap (LinearMap.prodMapAlgHom ℂ M M₁)
  have hS : ∀ a b, (a, b) ∈ S ↔ ∀ f φ, (f, φ) ∈ Γ → (a f, b φ) ∈ Γ := fun a b =>
    ⟨fun h f φ hf => h (f, φ) hf, fun h p hp => h p.1 p.2 hp⟩
  let X' : Fin (1 + n₁ + 1) → Fin (1 + n₁ + 1) → stab M' := fun a b => ⟨X a b, mem_stab.2 (hM a b)⟩
  have hX' : GlRel X' := by
    intro a b c d
    apply Subtype.ext
    have := hX a b c d
    split_ifs at this ⊢ <;> simpa [X'] using this
  have hF' : GlRel fun p q : Fin (1 + n₁) => X' (Fin.castAdd 1 p) (Fin.castAdd 1 q) :=
    GlobalTheory.CapHC.glRel_restrict hX' (Fin.castAdd 1) (fun a b h => Fin.ext (by simpa using congrArg Fin.val h))
  have e1 : ∀ u : ℂ, ∀ x ∈ M', qdet X (u + 1) x -
      qdet (fun p q : Fin 1 => X (Fin.natAdd (1 + n₁) p) (Fin.natAdd (1 + n₁) q)) (u + 1)
        (qdet (fun p q : Fin (1 + n₁) => X (Fin.castAdd 1 p) (Fin.castAdd 1 q)) u x) ∈ K := by
    intro u x hx
    have h := upperSpan_maps (K := K) X' (fun p q x hx => hup _ _ (blk_castAdd_lt p q) x hx)
      (GlobalTheory.CapHC.two_block (r := 1 + n₁) (m := 1) X' hX' (u + 1)) x hx
    change (stab M').val (_ - _ * _) x ∈ K at h
    rw [map_sub, map_mul, qdet_map, qdet_map, qdet_map, Nat.cast_one, add_sub_cancel_right] at h
    exact h
  have e2 : ∀ u : ℂ, ∀ x ∈ M', qdet (fun p q : Fin (1 + n₁) => X (Fin.castAdd 1 p) (Fin.castAdd 1 q)) u x -
      qdet (fun p q : Fin n₁ => X (mid p) (mid q)) u
        (qdet (fun p q : Fin 1 => X (Fin.castAdd 1 (Fin.castAdd n₁ p))
          (Fin.castAdd 1 (Fin.castAdd n₁ q))) (u - n₁) x) ∈ K := by
    intro u x hx
    have h := upperSpan_maps (K := K) (fun p q : Fin (1 + n₁) => X' (Fin.castAdd 1 p) (Fin.castAdd 1 q))
      (fun p q x hx => hup (Fin.castAdd 1 (Fin.castAdd n₁ p)) (mid q) (by rw [block_matrix_mulVec_basis, blk_mid]; norm_num) x hx)
      (GlobalTheory.CapHC.two_block (r := 1) (m := n₁) _ hF' u) x hx
    change (stab M').val (_ - _ * _) x ∈ K at h
    rw [map_sub, map_mul, qdet_map, qdet_map, qdet_map] at h
    exact h
  have hone : ∀ (i : Fin 1 → Fin (1 + n₁ + 1)) (l : ℂ), (∀ f φ, (f, φ) ∈ Γ → (X (i 0) (i 0) f, l • φ) ∈ Γ) →
      ∀ u f φ, (f, φ) ∈ Γ → (qdet (fun p q => X (i p) (i q)) u f, (u + l) • φ) ∈ Γ := fun i l hi u f φ hf => by
    have := Γ.add_mem (Γ.smul_mem u hf) (hi f φ hf)
    rw [qdet_one, add_smul]
    simpa using this
  have hq : ∀ u f φ, (f, φ) ∈ Γ → (qdet (fun p q : Fin n₁ => X (mid p) (mid q)) u f, qdet X₁ u φ) ∈ Γ := fun u => by
    have h := GlobalTheory.LeviHC.qdet_mem (fun p q : Fin n₁ => (X (mid p) (mid q), X₁ p q)) S
      (fun a b => (hS _ _).2 (hmid a b)) u
    have h1 := qdet_map (AlgHom.fst ℂ _ _) (fun p q : Fin n₁ => (X (mid p) (mid q), X₁ p q)) u
    have h2 := qdet_map (AlgHom.snd ℂ _ _) (fun p q : Fin n₁ => (X (mid p) (mid q), X₁ p q)) u
    refine (hS _ _).1 ?_
    convert h using 1
    exact Prod.ext h1.symm h2.symm
  have key : Algebra.adjoin ℂ (Set.range (qdet X)) ≤
      (S ⊓ (Algebra.adjoin ℂ (Set.range (qdet X₁))).comap (AlgHom.snd ℂ _ _)).map (AlgHom.fst ℂ _ _) := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨u', rfl⟩
    obtain ⟨u, rfl⟩ : ∃ u, u' = u + 1 := ⟨u' - 1, by ring⟩
    refine ⟨(qdet X (u + 1), ((u + 1 + ly) * (u - n₁ + lx)) • qdet X₁ u), ⟨(hS _ _).2 fun f φ hf => ?_,
      Subalgebra.smul_mem (Algebra.adjoin ℂ (Set.range (qdet X₁))) (Algebra.subset_adjoin (Set.mem_range_self u)) _⟩, rfl⟩
    have h1 := hq u _ _ (hone (fun p => Fin.castAdd 1 (Fin.castAdd n₁ p)) lx hx (u - n₁) f φ hf)
    have h2 := Γ.add_mem (e2 u f (hΓ f φ hf)) h1
    simp only [LinearMap.inl_apply, Prod.mk_add_mk, sub_add_cancel, zero_add] at h2
    have h3 := Γ.add_mem (e1 u f (hΓ f φ hf)) (hone (Fin.natAdd (1 + n₁)) ly hy (u + 1) _ _ h2)
    simp only [LinearMap.inl_apply, Prod.mk_add_mk, sub_add_cancel, zero_add, map_smul, smul_smul] at h3
    exact h3
  intro a ha
  obtain ⟨⟨a', b⟩, ⟨h1, h2⟩, rfl⟩ := key ha
  exact ⟨b, h2, (hS _ _).1 h1⟩

section Frames

variable {B : Type} [Ring B] [Algebra ℂ B] {n m : ℕ} (D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] B)
  (hD : ∀ X Y, D (X * Y - Y * X) = D X * D Y - D Y * D X) {Q : Matrix (Fin n) (Fin m) ℂ} {R : Matrix (Fin m) (Fin n) ℂ}
  (hQR : Q * R = 1) (hRQ : R * Q = 1)
include hD hQR hRQ

theorem central_of_mem_qdet {a : B}
    (ha : a ∈ Algebra.adjoin ℂ (Set.range (qdet fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R)))) :
    a ∈ Algebra.adjoin ℂ (Set.range D) ∧ ∀ X, D X * a = a * D X := by
  have hG := glRel_frame D hD hRQ
  refine ⟨Algebra.adjoin_le ?_ ha, fun X => ?_⟩
  · rintro _ ⟨u, rfl⟩
    exact GlobalTheory.LeviHC.qdet_mem _ (Algebra.adjoin ℂ (Set.range D))
      (fun a b => Algebra.subset_adjoin (Set.mem_range_self _)) u
  · have : Algebra.adjoin ℂ (Set.range (qdet fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R))) ≤
        Subalgebra.centralizer ℂ {D X} := by
      refine Algebra.adjoin_le ?_
      rintro _ ⟨u, rfl⟩ _ rfl
      rw [eq_sum_frame hQR X]
      simp only [map_sum, map_smul, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
      exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
        rw [Formalism.REAL.qDetCentral _ _ _ hG u a b]
    exact this ha _ rfl

theorem mem_qdet_of_central {a : B} (h1 : a ∈ Algebra.adjoin ℂ (Set.range D)) (h2 : ∀ X, D X * a = a * D X) :
    a ∈ Algebra.adjoin ℂ (Set.range (qdet fun a b : Fin m => D (Q * Matrix.single a b (1 : ℂ) * R))) := by
  have hG := glRel_frame D hD hRQ
  have h := GlobalTheory.T.relativeCentre' B m _ hG ⊥ (fun b hb i j => by
      obtain ⟨c, rfl⟩ := Algebra.mem_bot.1 hb
      exact (Algebra.commutes c _).symm) a (by
      rw [sup_bot_eq]
      refine Algebra.adjoin_le ?_ h1
      rintro _ ⟨Z, rfl⟩
      rw [eq_sum_frame hQR Z]
      simp only [map_sum, map_smul]
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.smul_mem _ (Algebra.subset_adjoin (Set.mem_range.2 ⟨(i, j), rfl⟩)) _) fun i j => h2 _
  rw [sup_bot_eq] at h
  refine Algebra.adjoin_le ?_ h
  rintro _ ⟨k, rfl⟩
  exact GlobalTheory.T.gelfand_generator_mem_quantum_det _ _ _ hG k

end Frames

section Geo

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n n₁ : ℕ}
  {W : Spc F E n} {W₁ : Spc F E n₁} {H : Plane E n n₁}

omit [NumberField E] in

theorem isLevi_mul {t t' : (AE F E)ˣ} {h h' : UA σ W₁.J} {m m' : UA σ W.J} (hm : IsLevi (W₁ := W₁) H t h m)
    (hm' : IsLevi (W₁ := W₁) H t' h' m') : IsLevi (W₁ := W₁) H (t * t') (h * h') (m * m') := by
  obtain ⟨ax, ay, aι⟩ := hm
  obtain ⟨cx, cy, cι⟩ := hm'
  refine ⟨?_, ?_, ?_⟩
  · change (mat m * mat m') *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cx, Matrix.mulVec_smul, ax, smul_smul, Units.val_mul, mul_comm]
  · change (mat m * mat m') *ᵥ _ = _
    rw [← Matrix.mulVec_mulVec, cy, Matrix.mulVec_smul, ay, smul_smul, mul_inv_rev, Units.val_mul, map_mul]
  · change (mat m * mat m') * _ = _ * (mat h * mat h')
    rw [Matrix.mul_assoc, cι, ← Matrix.mul_assoc, aι, Matrix.mul_assoc]

theorem isLevi_of_diag (hσ : ∀ x, σ (σ x) = x) (hxy : form σ W.J H.x H.y = 1)
    {R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E} (hQR : frame H * R = 1) (m : UA σ W.J)
    (hm : ∀ i j, i ≠ j ∨ blk n₁ j = 1 → (incM F R * (mat m - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
      Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0) : ∃ t, IsLevi (W₁ := W₁) H t 1 m := by
  set N : Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E) :=
    incM F R * (mat m - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) with hN
  have hQR' : incM F (frame H) * incM F R = 1 := by
    rw [incM, incM, ← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]
  have e : mat m * incM F (frame H) = incM F (frame H) + incM F (frame H) * N := by
    rw [hN, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hQR', Matrix.one_mul, Matrix.sub_mul, Matrix.one_mul, add_sub_cancel]
  have col : ∀ j, mat m *ᵥ (fun r => incM F (frame H) r j) = (1 + N j j) • fun r => incM F (frame H) r j := fun j => by
    funext r
    have := congrFun (congrFun e r) j
    rw [Matrix.add_apply, Matrix.mul_apply (M := incM F (frame H)), Finset.sum_eq_single j
      (fun i _ hi => by rw [hm i j (Or.inl hi), mul_zero]) (by simp)] at this
    change (mat m * incM F (frame H)) r j = _
    rw [this, Pi.smul_apply, smul_eq_mul]; ring
  have hx := col (Fin.castAdd 1 (Fin.castAdd n₁ 0))
  have hy := col (Fin.natAdd (1 + n₁) 0)
  simp only [incM, Matrix.map_apply, frame_alt, frame_y] at hx hy
  generalize (1 + N _ _ : AE F E) = α at hx
  generalize (1 + N _ _ : AE F E) = β at hy
  change mat m *ᵥ incV F H.x = α • incV F H.x at hx
  change mat m *ᵥ incV F H.y = β • incV F H.y at hy
  have h1 : α * cA σ β = 1 := by
    have h2 := GlobalTheory.AdelicPlaneLevi.fR_mulVec (cA σ).toRingHom (incM F W.J) (mat m) (incV F H.x) (incV F H.y)
    have h3 : (mat m)ᵀ * incM F W.J * (mat m).map (cA σ).toRingHom = incM F W.J := m.2
    rw [h3, hx, hy, GlobalTheory.AdelicPlaneLevi.fR_smul_left, GlobalTheory.AdelicPlaneLevi.fR_smul_right] at h2
    change _ = GlobalTheory.AdelicPlaneLevi.fR (cA σ).toRingHom (incM F W.J) (incV F H.x) (incV F H.y) at h2
    rw [GlobalTheory.AdelicPlaneLevi.fR_inc, hxy, map_one, mul_one] at h2
    exact h2
  refine ⟨⟨α, cA σ β, h1, (mul_comm _ _).trans h1⟩, hx, ?_, ?_⟩
  · rw [hy]
    congr 1
    exact (GlobalTheory.AdelicPlaneLevi.cA_cA σ hσ β).symm
  · rw [FlagPar.mat_one, Matrix.mul_one]
    ext r k
    have := congrFun (col (mid k)) r
    rw [hm _ _ (Or.inr (blk_mid k)), add_zero, one_smul] at this
    simp only [incM, Matrix.map_apply, frame_mid] at this
    exact this

theorem gram_frame_support (h : IsCMExt F E σ) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hxx : form σ W.J H.x H.x = 0)
    (hyy : form σ W.J H.y H.y = 0) (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0)
    (c : E) (τ : E →+* ℂ) (a b : Fin (1 + n₁ + 1)) (hab : blk n₁ a + blk n₁ b ≠ 2) :
    (((frame H).map τ)ᴴ * (c • W.J.map σ).map τ * (frame H).map τ) a b = 0 := by
  have hσ := GlobalTheory.SiegelSet.sigma_sigma h
  have hGf : ∀ a b, ((frame H)ᵀ * W.J * (frame H).map σ) a b =
      form σ W.J (fun r => frame H r a) (fun r => frame H r b) := by
    intro a b
    simp only [Matrix.mul_apply, form, dotProduct, Matrix.mulVec, Matrix.transpose_apply, Matrix.map_apply, Finset.sum_mul,
      Finset.mul_sum, mul_assoc]
    exact Finset.sum_comm
  have hskew : ∀ u v : Fin n → E, form σ W.J u v = -σ (form σ W.J v u) := by
    intro u v
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, Finset.mul_sum, ← Finset.sum_neg_distrib]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hsk]; ring
  have hcol : ∀ k : Fin n₁, (fun r => H.ι r k) = H.ι *ᵥ Pi.single k 1 := by
    intro k; ext r; simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hGs : ((frame H)ᵀ * W.J * (frame H).map σ) a b = 0 := by
    rw [hGf]
    rcases blk_cases a with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩ <;>
      rcases blk_cases b with ⟨b, rfl⟩ | ⟨l, rfl⟩ | ⟨b, rfl⟩ <;>
      simp only [block_matrix_mulVec_basis, blk_mid, blk_y, frame_alt, frame_mid, frame_y] at hab ⊢
    · exact hxx
    · rw [hcol, hskew, (horth _).1, map_zero, neg_zero]
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).1
    · exact absurd rfl hab
    · rw [hcol]; exact (horth _).2
    · exact absurd rfl hab
    · rw [hcol, hskew, (horth _).2, map_zero, neg_zero]
    · exact hyy
  have hA'e : (((frame H).map τ)ᴴ * (c • W.J.map σ).map τ * (frame H).map τ) a b =
      τ c * star (τ (((frame H)ᵀ * W.J * (frame H).map σ) a b)) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
      Matrix.transpose_apply, map_mul, map_sum, h.2.2.2, star_sum, star_mul', star_star, Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hA'e, hGs, map_zero, star_zero, mul_zero]

def torDiag (n₁ : ℕ) (l : ℂ) (i : Fin (1 + n₁ + 1)) : ℂ :=
  if blk n₁ i = 0 then l else if blk n₁ i = 1 then 0 else -star l

theorem exists_torus_line (h : IsCMExt F E σ) (hsk : ∀ i j, σ (W.J j i) = -W.J i j) (hxx : form σ W.J H.x H.x = 0)
    (hyy : form σ W.J H.y H.y = 0) (hxy : form σ W.J H.x H.y = 1)
    (horth : ∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0)
    {R : Matrix (Fin (1 + n₁ + 1)) (Fin n) E} (hQR : frame H * R = 1) (hRQ : R * frame H = 1)
    {c : E} (hc : c ≠ 0) (hJ : IsHermND σ (c • W.J.map σ)) {w : InfinitePlace F} (τ : EmbOver E w) (l : ℂ) :
    ∃ γ, IsLineOf σ (c • W.J.map σ) τ ((frame H).map τ.1 * Matrix.diagonal (torDiag n₁ l) * R.map τ.1) γ ∧
      ∀ s, ∃ t, IsLevi (W₁ := W₁) H t 1 ((GlobalTheory.ThK.SquareIntegrability.toGAd (sigma_sigma h) W.J hc).symm (γ s)) := by
  have hQR' : (frame H).map τ.1 * R.map τ.1 = 1 := by
    rw [← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hRQ' : R.map τ.1 * (frame H).map τ.1 = 1 := by
    rw [← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _)]
  have hG := gram_frame_support h hsk hxx hyy horth c τ.1
  generalize hA : (c • W.J.map σ).map τ.1 = A at hG
  generalize hQ : (frame H).map τ.1 = Q at hG hQR' hRQ'
  generalize hR : R.map τ.1 = R' at hG hQR' hRQ'
  have h0 : (Matrix.diagonal (torDiag n₁ l))ᴴ * (Qᴴ * A * Q) + Qᴴ * A * Q * Matrix.diagonal (torDiag n₁ l) = 0 := by
    ext a b
    rw [Matrix.add_apply, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.zero_apply]
    by_cases hab : blk n₁ a + blk n₁ b = 2
    · have : star (torDiag n₁ l a) + torDiag n₁ l b = 0 := by
        unfold torDiag
        split_ifs <;> first | omega | simp
      rw [Pi.star_apply]
      linear_combination (Qᴴ * A * Q) a b * this
    · rw [hG a b hab]; simp
  have hZ : (Q * Matrix.diagonal (torDiag n₁ l) * R')ᴴ * A + A * (Q * Matrix.diagonal (torDiag n₁ l) * R') = 0 := by
    have h1 := congrArg (fun Y => R'ᴴ * Y * R') h0
    have h2 : ∀ Y : Matrix (Fin n) (Fin n) ℂ, R'ᴴ * (Qᴴ * Y) = Y := fun Y => by
      rw [← Matrix.mul_assoc, ← Matrix.conjTranspose_mul, hQR', Matrix.conjTranspose_one, Matrix.one_mul]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, hQR', Matrix.mul_one, h2, Matrix.mul_zero,
      Matrix.zero_mul] at h1
    simpa only [Matrix.conjTranspose_mul, Matrix.mul_assoc] using h1
  subst hA
  obtain ⟨γ, hγ⟩ := exists_isLineOf h hJ hZ
  refine ⟨γ, hγ, fun s => isLevi_of_diag (sigma_sigma h) hxy hQR _ fun i j hij => ?_⟩
  obtain ⟨y, hy1, hy2⟩ := hγ s
  change (incM F R * (((γ s).1 : GL (Fin n) (AE F E)).1 - 1 : Matrix (Fin n) (Fin n) (AE F E)) * incM F (frame H) :
      Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (AE F E)) i j = 0
  rw [hy1, BlockTriLine.mat_embArch_sub_one, BlockTriLine.incM_mul_map_mul, Matrix.map_apply]
  have h3 : (R.map (inclR (F := F) w.Completion) * ((y.1 : GL (Fin n) (w.Completion ⊗[F] E)).1 - 1) *
      (frame H).map (inclR (F := F) w.Completion) :
      Matrix (Fin (1 + n₁ + 1)) (Fin (1 + n₁ + 1)) (w.Completion ⊗[F] E)) i j = 0 := by
    apply (infEmb_bijective h τ).1
    have h4 := congrFun (congrFun (BlockTriLine.map_infEmb_conj τ R (frame H) y) i) j
    rw [Matrix.map_apply] at h4
    rw [map_zero, h4, hy2, hR, hQ, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRQ', BlockTriLine.conj_exp _ _ hQR' hRQ',
      Matrix.mul_smul, Matrix.smul_mul, show R' * (Q * Matrix.diagonal (torDiag n₁ l) * R') * Q =
        Matrix.diagonal (torDiag n₁ l) by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hRQ', Matrix.one_mul, Matrix.mul_assoc, hRQ', Matrix.mul_one],
      ← Matrix.diagonal_smul, Matrix.exp_diagonal, Matrix.sub_apply]
    by_cases e : i = j
    · subst e
      have hb : blk n₁ i = 1 := hij.resolve_left (fun e => e rfl)
      simp [Pi.coe_exp, torDiag, hb]
    · simp [e]
  rw [h3, map_zero]

end Geo

theorem matrix_single_zero_eq_half_diagonal_torDiag (n₁ : ℕ) : Matrix.single (Fin.castAdd 1 (Fin.castAdd n₁ (0 : Fin 1))) (Fin.castAdd 1 (Fin.castAdd n₁ 0)) (1 : ℂ) =
    (1 / 2 : ℂ) • Matrix.diagonal (torDiag n₁ 1) + (-Complex.I / 2) • Matrix.diagonal (torDiag n₁ Complex.I) := by
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.diagonal_add]
  congr 1
  funext i
  have hI := Complex.I_mul_I
  rcases blk_cases i with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp only [Pi.single_eq_same, Pi.smul_apply, torDiag, block_matrix_mulVec_basis, if_true, smul_eq_mul]
    linear_combination (1 / 2 : ℂ) * hI
  · rw [Pi.single_eq_of_ne (fun e => by simpa [block_matrix_mulVec_basis, blk_mid] using congrArg (blk n₁) e)]
    simp [torDiag, blk_mid]
  · rw [Pi.single_eq_of_ne (fun e => by simpa [block_matrix_mulVec_basis, blk_y] using congrArg (blk n₁) e)]
    simp [torDiag, blk_y]
    linear_combination (1 / 2 : ℂ) * hI

theorem single_y (n₁ : ℕ) : Matrix.single (Fin.natAdd (1 + n₁) (0 : Fin 1)) (Fin.natAdd (1 + n₁) (0 : Fin 1)) (1 : ℂ) =
    (-1 / 2 : ℂ) • Matrix.diagonal (torDiag n₁ 1) + (-Complex.I / 2) • Matrix.diagonal (torDiag n₁ Complex.I) := by
  rw [← Matrix.diagonal_single, ← Matrix.diagonal_smul, ← Matrix.diagonal_smul, Matrix.diagonal_add]
  congr 1
  funext i
  have hI := Complex.I_mul_I
  rcases blk_cases i with ⟨a, rfl⟩ | ⟨k, rfl⟩ | ⟨a, rfl⟩
  · rw [Pi.single_eq_of_ne (fun e => by simpa [block_matrix_mulVec_basis, blk_y] using congrArg (blk n₁) e)]
    simp [torDiag, block_matrix_mulVec_basis]
    linear_combination (1 / 2 : ℂ) * hI
  · rw [Pi.single_eq_of_ne (fun e => by simpa [blk_y, blk_mid] using congrArg (blk n₁) e)]
    simp [torDiag, blk_mid]
  · obtain rfl : a = 0 := Subsingleton.elim _ _
    simp [torDiag, blk_y]
    linear_combination (1 / 2 : ℂ) * hI

section General

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

theorem exists_isCentral_of_central (h : IsCMExt F E σ) (hJ : IsHermND σ J) {w : InfinitePlace F} {τ : EmbOver E w}
    {D : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (SmG σ J)} (hD : IsDer σ J τ D) {a : Module.End ℂ (SmG σ J)}
    (h1 : a ∈ Algebra.adjoin ℂ (Set.range D)) (h2 : ∀ X, D X * a = a * D X) (v : SmG σ J) :
    ∃ z, IsCentral σ J z ∧ (a v).1 = dop z v.1 := by
  obtain ⟨z, hz1, hz2⟩ := GlobalTheory.T.universal_enveloping_line_derivatives F E σ h n J hJ w τ D hD a h1
  refine ⟨z, ⟨hz1, fun f hf b _ g => ?_⟩, (hz2 v).symm⟩
  have e := GlobalTheory.T.central_element_commutes_translates F E σ h n J hJ w τ D hD a h1 h2 b ⟨f, hf⟩ ⟨_, GlobalTheory.EisCont.CentreFinite.isSm_mul_right h hf b⟩ rfl
  rw [← hz2, ← hz2] at e
  exact congrFun e g

end General

open GlobalTheory.ThK.SquareIntegrability GlobalTheory.ThK.CuspTransfer in
set_option maxHeartbeats 1000000 in

theorem finite_of_isInd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (h : IsCMExt F E σ) (hσ : ∀ x, σ (σ x) = x) {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}
    (hsk : ∀ i j, σ (Y.J j i) = -Y.J i j) (hn : n = n₁ + 2) (hxx : form σ Y.J H.x H.x = 0) (hyy : form σ Y.J H.y H.y = 0)
    (hxy : form σ Y.J H.x H.y = 1) (horth : ∀ u, form σ Y.J (H.ι *ᵥ u) H.x = 0 ∧ form σ Y.J (H.ι *ᵥ u) H.y = 0)
    (hgram : H.ιᵀ * Y.J * H.ι.map σ = Y₁.J) {c : E} (hc : c ≠ 0) (hJ₁ : IsHermND σ (c • Y₁.J.map σ))
    (hJ : IsHermND σ (c • Y.J.map σ)) {M : UA σ Y₁.J → UA σ Y.J} (hM : ∀ h₁, IsLevi (W₁ := Y₁) H 1 h₁ (M h₁))
    {r : ℕ} {X' Y' : Matrix (Fin n) (Fin (r + 1)) E} (hW : IsWittFrame σ (c • Y.J.map σ) X' Y') (hX' : ∀ k, X' k 0 = H.x k)
    {χ : Chr F E} {Kc : Set (GAd σ (c • Y.J.map σ))} {d : ℕ} {ψs : Fin d → GAd σ (c • Y₁.J.map σ) → ℂ}
    {a : Fin d → GAd σ (c • Y.J.map σ) → ℂ} {Ψ : GAd σ (c • Y.J.map σ) → ℂ} (hΨ : IsInd hσ Y Y₁ H hc X' M χ Kc ψs a Ψ)
    (hψsm : ∀ i, IsSm σ (c • Y₁.J.map σ) (ψs i))
    (hψfin : ∀ i, FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ (c • Y₁.J.map σ) z ∧ f = dop z (ψs i)}))
    (hsm : IsSm σ (c • Y.J.map σ) Ψ) :
    FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, IsCentral σ (c • Y.J.map σ) z ∧ f = dop z Ψ}) := by
  classical
  have hdet₁ : Y₁.J.det ≠ 0 := fun h0 => hJ₁.2 (by
    have e : (Y₁.J.map σ).det = (σ : E →+* E) Y₁.J.det := by rw [RingHom.map_det]; rfl
    rw [Matrix.det_smul, e, h0, map_zero, mul_zero])
  have hyp : GlobalTheory.ThK.GLTwo.IsHypPlane σ H Y Y₁ := ⟨hn, hxx, hyy, hxy, horth, hgram⟩
  obtain ⟨R, hQR, hRQ⟩ := GlobalTheory.T.levi_embedding_hyperbolic_first F E σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet₁
  obtain ⟨ι, hι, hιl⟩ := GlobalTheory.T.levi_embedding_hyperbolic_second F E σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet₁ R hQR hRQ c hc hJ hJ₁
  let e := toGAd hσ Y.J hc
  let e₁ := toGAd hσ Y₁.J hc
  have hemb : ∀ y, CuspTransfer.emb hσ Y Y₁ hc M y = ι y := fun y => by
    obtain ⟨m, hm, em⟩ := hι (e₁.symm y) y rfl
    have := hyp.levi_unique hσ hsk hdet₁ (hM _) hm
    unfold CuspTransfer.emb
    rw [this]
    exact Subtype.ext em
  have hιM : ∀ y, ι y = e (M (e₁.symm y)) := fun y => (hemb y).symm
  have hN : ∀ u, u ∈ unip σ Y H ↔ e u ∈ GlobalTheory.StdPar.unip σ (c • Y.J.map σ) X' {0} := fun u =>
    hyp.mem_unip_iff hσ hsk hdet₁ hc hW (Nat.succ_pos r) hX' u
  simp only [IsInd, hemb] at hΨ
  obtain ⟨hdec, hval⟩ := hΨ
  have hcomm : ∀ t m y, IsLevi (W₁ := Y₁) H t 1 m → ι y * e m = e m * ι y := fun t m y hm => by
    have h1 := isLevi_mul (hM (e₁.symm y)) hm
    have h2 := isLevi_mul hm (hM (e₁.symm y))
    rw [one_mul, mul_one] at h1 h2
    rw [hιM, ← map_mul, ← map_mul, hyp.levi_unique hσ hsk hdet₁ h1 h2]
  let v : SmG σ (c • Y.J.map σ) := ⟨Ψ, hsm⟩
  let τ : ∀ w : InfinitePlace F, EmbOver E w := fun w => Classical.choice inferInstance
  choose D hD using fun w => exists_isDer h hJ (τ w)
  choose D₁ hD₁ using fun w => exists_isDer h hJ₁ (τ w)
  refine finite_of_gelf h hJ τ D hD v fun w => ?_
  let Q := (frame H).map (τ w).1
  let R' := R.map (τ w).1
  have hQR' : Q * R' = 1 := by rw [← Matrix.map_mul, hQR, Matrix.map_one _ (map_zero _) (map_one _)]
  have hRQ' : R' * Q = 1 := by rw [← Matrix.map_mul, hRQ, Matrix.map_one _ (map_zero _) (map_one _)]
  let X : Fin (1 + n₁ + 1) → Fin (1 + n₁ + 1) → Module.End ℂ (SmG σ (c • Y.J.map σ)) :=
    fun a b => D w (Q * Matrix.single a b (1 : ℂ) * R')
  have hX : GlRel X := glRel_frame (D w) (hD w).1 hRQ'
  let M' : Submodule ℂ (SmG σ (c • Y.J.map σ)) :=
    { carrier := {f | ∀ u ∈ unip σ Y H, ∀ x, f.1 (e u * x) = f.1 x}
      add_mem' := fun {f f'} hf hf' u hu x => by
        rw [Submodule.coe_add, Pi.add_apply, Pi.add_apply, hf u hu, hf' u hu]
      zero_mem' := fun _ _ _ => rfl
      smul_mem' := fun a f hf u hu x => by rw [Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply, hf u hu] }
  let Γ : Submodule ℂ (SmG σ (c • Y.J.map σ) × SmG σ (c • Y₁.J.map σ)) :=
    { carrier := {p | p.1 ∈ M' ∧ ∀ t m y, IsLevi (W₁ := Y₁) H t 1 m → p.1.1 (e m * ι y) = (χ t : ℂ) * p.2.1 y}
      add_mem' := fun {p p'} hp hp' => ⟨M'.add_mem hp.1 hp'.1, fun t m y hm => by
        rw [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Submodule.coe_add, Pi.add_apply, Pi.add_apply, hp.2 t m y hm,
          hp'.2 t m y hm, mul_add]⟩
      zero_mem' := ⟨M'.zero_mem, fun t m y _ => (mul_zero _).symm⟩
      smul_mem' := fun b p hp => ⟨M'.smul_mem b hp.1, fun t m y hm => by
        rw [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, Submodule.coe_smul, Pi.smul_apply, Pi.smul_apply,
          hp.2 t m y hm, smul_eq_mul, smul_eq_mul, mul_left_comm]⟩ }
  have hMl : ∀ Z γ, IsLineOf σ (c • Y.J.map σ) (τ w) Z γ → ∀ f ∈ M', D w Z f ∈ M' := fun Z γ hγ f hf u hu x => by
    rw [(hD w).2 Z γ hγ]
    simp only [lineDer, mul_assoc, hf u hu]
  have hM' : ∀ Z, ∀ f ∈ M', D w Z f ∈ M' := fun Z f hf => by
    obtain ⟨γ₁, γ₂, h1, h2, e2⟩ := exists_lines h hJ (τ w) Z
    rw [e2, map_add, map_smul (D w) Complex.I, LinearMap.add_apply, LinearMap.smul_apply]
    exact M'.add_mem (hMl _ _ h1 f hf) (M'.smul_mem _ (hMl _ _ h2 f hf))

  have hupl : ∀ Z γ, IsLineOf σ (c • Y.J.map σ) (τ w) Z γ → (∀ i j, blk n₁ j < blk n₁ i + 1 → (R' * Z * Q) i j = 0) →
      ∀ f ∈ M', (D w Z f, (0 : SmG σ (c • Y₁.J.map σ))) ∈ Γ := fun Z γ hγ hZ f hf => ⟨hM' Z f hf, fun t m y hm => by
    change (D w Z f).1 _ = _ * 0
    rw [(hD w).2 Z γ hγ, mul_zero]
    have h1 : ∀ s, f.1 (e m * ι y * γ s) = f.1 (e m * ι y) := fun s => by
      have h2 : e.symm (γ s) ∈ unip σ Y H := GlobalTheory.T.unipotent_block_triangular_nilpotent F E σ n n₁ Y H R hQR hRQ _ fun i j hij =>
        (BlockTriLine.blockTri_adelic F E σ h n _ hJ _ _ R hQR hRQ (blk n₁) 1 w (τ w) Z γ hγ hZ s i j hij).1
      have := hf _ (GlobalTheory.CTFirst.levi_conj_mem_unip H t m hm _
        (GlobalTheory.T.levi_normalizes_unipotent_bis F E σ n n₁ Y Y₁ H _ _ (hM (e₁.symm y)) _ h2)) (e m * ι y)
      simpa only [map_mul, map_inv, MulEquiv.apply_symm_apply, ← hιM, mul_assoc, inv_mul_cancel_left, inv_mul_cancel,
        mul_one] using this
    simp only [lineDer, h1, deriv_const]⟩
  have hup : ∀ a b, blk n₁ a < blk n₁ b → ∀ f ∈ M', (X a b f, (0 : SmG σ (c • Y₁.J.map σ))) ∈ Γ := by
    intro a b hab f hf
    obtain ⟨γ₁, γ₂, h1, h2, e2⟩ := exists_lines h hJ (τ w) (Q * Matrix.single a b (1 : ℂ) * R')
    have h0 : ∀ i j, blk n₁ j < blk n₁ i + 1 → (R' * (Q * Matrix.single a b (1 : ℂ) * R') * Q) i j = 0 :=
      fun i j hij => by
        rw [frame_unit_apply hRQ']
        refine Matrix.single_apply_of_ne _ _ _ _ _ ?_
        rintro ⟨rfl, rfl⟩
        omega
    have h0' := adj_frame_blockTri F E σ h n n₁ Y Y₁ H hsk hn hxx hyy hxy horth hgram hdet₁ R hQR hRQ c hc hJ hJ₁
      (τ w).1 1 _ h0
    have h3 := Γ.add_mem (hupl _ _ h1 (fun i j hij => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_apply, Matrix.sub_apply,
        h0 i j hij, h0' i j hij, sub_zero, smul_zero]) f hf) (Γ.smul_mem Complex.I (hupl _ _ h2 (fun i j hij => by
      rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, Matrix.smul_apply, Matrix.add_apply,
        h0 i j hij, h0' i j hij, add_zero, smul_zero]) f hf))
    change (D w _ f, _) ∈ Γ
    rw [e2, map_add, map_smul (D w) Complex.I, LinearMap.add_apply, LinearMap.smul_apply]
    rw [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] at h3
    exact h3

  have hline : ∀ Z γ, IsLineOf σ (c • Y₁.J.map σ) (τ w) Z γ → ∀ f φ, (f, φ) ∈ Γ →
      (D w (H.ι.map (τ w).1 * Z * (R.submatrix mid id).map (τ w).1) f, D₁ w Z φ) ∈ Γ := fun Z γ hγ f φ hf =>
    ⟨hM' _ f hf.1, fun t m y hm => by
      change (D w _ f).1 _ = _ * (D₁ w Z φ).1 y
      rw [(hD₁ w).2 Z γ hγ, (hD w).2 _ _ (hιl w _ Z γ hγ)]
      have h1 : ∀ s, f.1 (e m * ι y * ι (γ s)) = (χ t : ℂ) * φ.1 (y * γ s) := fun s => by
        rw [mul_assoc, ← map_mul]; exact hf.2 t m _ hm
      simp only [lineDer, h1, deriv_const_mul_field']⟩
  have hmid : ∀ a b f φ, (f, φ) ∈ Γ → (X (mid a) (mid b) f, D₁ w (1 * Matrix.single a b 1 * 1) φ) ∈ Γ :=
    fun a b f φ hf => by
    have e1 : Q * Matrix.single (mid a) (mid b) (1 : ℂ) * R' =
        H.ι.map (τ w).1 * Matrix.single a b (1 : ℂ) * (R.submatrix mid id).map (τ w).1 := by
      ext r s
      simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Q, R', frame_mid]
    obtain ⟨γ₁, γ₂, h1, h2, e2⟩ := exists_lines h hJ₁ (τ w) (Matrix.single a b 1)
    have h3 := Γ.add_mem (hline _ _ h1 f φ hf) (Γ.smul_mem Complex.I (hline _ _ h2 f φ hf))
    change (D w _ f, _) ∈ Γ
    rw [Matrix.one_mul, Matrix.mul_one, e1, e2, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul _ Complex.I,
      Matrix.smul_mul, map_add, map_add, map_smul (D₁ w) Complex.I, map_smul (D w) Complex.I]
    exact h3

  have htor : ∀ l : ℂ, ∃ μ : ℂ, ∀ f φ, (f, φ) ∈ Γ → (D w (Q * Matrix.diagonal (torDiag n₁ l) * R') f, μ • φ) ∈ Γ := fun l => by
    obtain ⟨γ, hγ, ht⟩ := exists_torus_line (W₁ := Y₁) h hsk hxx hyy hxy horth hQR hRQ hc hJ (τ w) l
    choose t ht using ht
    refine ⟨deriv (fun s => (χ (t s) : ℂ)) 0, fun f φ hf => ⟨hM' _ f hf.1, fun t₀ m y hm => ?_⟩⟩
    change (D w _ f).1 _ = _ * (_ * φ.1 y)
    rw [(hD w).2 _ _ hγ]
    have h1 : ∀ s, f.1 (e m * ι y * γ s) = (χ t₀ : ℂ) * ((χ (t s) : ℂ) * φ.1 y) := fun s => by
      have h2 := isLevi_mul hm (ht s)
      rw [mul_one] at h2
      have h3 := hf.2 _ _ y h2
      rw [map_mul, map_mul, Circle.coe_mul, mul_assoc, mul_assoc, ← hcomm _ _ y (ht s)] at h3
      rw [← h3, mul_assoc]
      exact congrArg (fun x => f.1 (e m * (ι y * x))) (e.apply_symm_apply _).symm
    simp only [lineDer, h1, deriv_const_mul_field', deriv_mul_const_field']
  have hcorner : ∀ (i : Fin (1 + n₁ + 1)) (α β : ℂ), Matrix.single i i (1 : ℂ) =
      α • Matrix.diagonal (torDiag n₁ 1) + β • Matrix.diagonal (torDiag n₁ Complex.I) →
      ∃ μ : ℂ, ∀ f φ, (f, φ) ∈ Γ → (X i i f, μ • φ) ∈ Γ := fun i α β hi => by
    obtain ⟨μ, hμ⟩ := htor 1
    obtain ⟨ν, hν⟩ := htor Complex.I
    refine ⟨α * μ + β * ν, fun f φ hf => ?_⟩
    have h3 := Γ.add_mem (Γ.smul_mem α (hμ f φ hf)) (Γ.smul_mem β (hν f φ hf))
    change (D w _ f, _) ∈ Γ
    rw [hi, Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, map_add,
      map_smul, map_smul, add_smul, mul_smul, mul_smul]
    exact h3
  obtain ⟨lx, hx⟩ := hcorner _ _ _ (matrix_single_zero_eq_half_diagonal_torDiag n₁)
  obtain ⟨ly, hy⟩ := hcorner _ _ _ (single_y n₁)
  have hrel := exists_rel_qdet X hX _ M' Γ (fun f φ hf => hf.1) (fun a b => hM' _) hup hmid lx ly hx hy

  let ψ : Fin d → SmG σ (c • Y₁.J.map σ) := fun i => ⟨ψs i, hψsm i⟩
  let vk : GAd σ (c • Y.J.map σ) → SmG σ (c • Y.J.map σ) := fun k =>
    ⟨fun x => Ψ (x * k), GlobalTheory.EisCont.CentreFinite.isSm_mul_right h hsm k⟩
  have hk : ∀ k ∈ Kc, (vk k, ∑ i, a i k • ψ i) ∈ Γ := fun k hk => ⟨fun u hu x => by
    obtain ⟨u', hu', t, m, y, k', hk', hm, e'⟩ := hdec (x * k)
    change Ψ (e u * x * k) = Ψ (x * k)
    rw [mul_assoc, e', hval u' hu' t m y k' hk' hm, ← hval _ (mul_mem ((hN u).1 hu) hu') t m y k' hk' hm]
    simp only [mul_assoc], fun t m y hm => by
    have := hval 1 (one_mem _) t m y k hk hm
    rw [one_mul] at this
    refine this.trans ?_
    simp only [Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul, Pi.smul_apply, smul_eq_mul, ψ, mul_comm]⟩
  choose u hu t m y k hkc hm hg using hdec
  let V : Fin d → Submodule ℂ (GAd σ (c • Y₁.J.map σ) → ℂ) := fun i =>
    Submodule.span ℂ {f | ∃ z, IsCentral σ (c • Y₁.J.map σ) z ∧ f = dop z (ψs i)}
  let L : (∀ i, V i) →ₗ[ℂ] (GAd σ (c • Y.J.map σ) → ℂ) :=
    { toFun := fun φ g => (χ (t g) : ℂ) * ∑ i, a i (k g) * (φ i).1 (y g)
      map_add' := fun φ φ' => funext fun g => by simp [mul_add, Finset.sum_add_distrib]
      map_smul' := fun b φ => funext fun g => by
        simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring }
  have hS : FiniteDimensional ℂ ((LinearMap.range L).comap (SmG σ (c • Y.J.map σ)).subtype) :=
    FiniteDimensional.of_injective ((SmG σ (c • Y.J.map σ)).subtype.restrict (q := LinearMap.range L) fun x hx => hx)
      fun x y e => by
        have h' := congrArg Subtype.val e
        exact Subtype.ext (Subtype.ext h')
  refine Submodule.finiteDimensional_of_le (S₂ := (LinearMap.range L).comap (SmG σ (c • Y.J.map σ)).subtype)
    (Submodule.span_le.2 ?_)
  rintro _ ⟨b, hb, rfl⟩
  have hG : GlRel fun p q : Fin n => D w (1 * Matrix.single p q (1 : ℂ) * 1) := glRel_frame (D w) (hD w).1 (Matrix.mul_one _)
  obtain ⟨hb1, hb2⟩ := central_of_mem_qdet (D w) (hD w).1 (Q := 1) (R := 1) (Matrix.mul_one _) (Matrix.mul_one _) (a := b) (by
    refine Algebra.adjoin_le ?_ hb
    rintro _ ⟨j, rfl⟩
    simpa using GlobalTheory.T.gelfand_generator_mem_quantum_det _ _ _ hG j)
  obtain ⟨b₁, hb₁, hbb⟩ := hrel b (mem_qdet_of_central (D w) (hD w).1 hQR' hRQ' hb1 hb2)
  obtain ⟨hc1, hc2⟩ := central_of_mem_qdet (D₁ w) (hD₁ w).1 (Q := 1) (R := 1) (Matrix.mul_one _) (Matrix.mul_one _) hb₁
  refine ⟨fun i => ⟨(b₁ (ψ i)).1, Submodule.subset_span (exists_isCentral_of_central h hJ₁ (hD₁ w) hc1 hc2 (ψ i))⟩,
    funext fun g => ?_⟩
  have h1 := congrFun (GlobalTheory.T.central_element_commutes_translates F E σ h n _ hJ w (τ w) (D w) (hD w) b hb1 hb2 (k g) v (vk (k g)) rfl)
    (u g * e (m g) * ι (y g))
  have h2 := hbb _ _ (hk _ (hkc g))
  have h3 := h2.1 (e.symm (u g)) ((hN _).2 (by rw [e.apply_symm_apply]; exact hu g)) (e (m g) * ι (y g))
  have h4 := h2.2 _ _ (y g) (hm g)
  rw [e.apply_symm_apply, ← mul_assoc] at h3
  change _ = (b v).1 g
  conv_rhs => rw [hg g]
  refine Eq.trans ?_ (h4.symm.trans (h3.symm.trans h1))
  simp only [L, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_smul, Submodule.coe_sum, Finset.sum_apply, Submodule.coe_smul,
    Pi.smul_apply, smul_eq_mul]

theorem finite_centre_of_isInd : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∀ i, ContinuousOn (a i) Kc) → (∀ i, ∀ k ∈ Kc, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * (List.ofFn fun j => γ j (t j)).prod)) → (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) Kc) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ k ∈ Kc, a i k = ∑ j, c j * b j k) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ k ∈ Kc, b j (k * k') = ∑ l, c l * b l k) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, GlobalTheory.UAut.IsCentral σ (c₀ • W.J.map σ) z ∧ f = GlobalTheory.UAut.dop z Ψ}) := by
  intro F E _ _ _ _ _ σ h hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c hc hJ₁ hJ M hMc hM hMr r Xf Yf hf X' Y' hW hX hY
    hXY S' χ hχ hχc K₁ hK₁ K' hK' Kc d ψs a Ψ hΨ hψ hKc ha ha' _
  exact finite_of_isInd h hσ hsk hn hxx hyy hxy horth hgram hc hJ₁ hJ hM hW hX hΨ (fun i => (hψ i).1.smooth)
    (fun i => (hψ i).1.zfin) (GlobalTheory.T.skew_plane_jacobian_identity F E σ h hσ n n₁ W W₁ H hsk hn hxx hyy hxy horth hgram c hc hJ₁ hJ M hMc hM hMr r
      Xf Yf hf X' Y' hW hX hY hXY S' χ hχ hχc K₁ hK₁ K' hK' Kc d ψs a Ψ hΨ hψ hKc ha ha')

theorem finite_centre_of_isInd_of : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (hσ : ∀ x, σ (σ x) = x) (n n₁ : ℕ) (W : Spc F E n) (W₁ : Spc F E n₁) (H : Plane E n n₁), (∀ i j, σ (W.J j i) = -W.J i j) → n = n₁ + 2 →
      form σ W.J H.x H.x = 0 → form σ W.J H.y H.y = 0 → form σ W.J H.x H.y = 1 →
      (∀ u, form σ W.J (H.ι *ᵥ u) H.x = 0 ∧ form σ W.J (H.ι *ᵥ u) H.y = 0) → H.ιᵀ * W.J * H.ι.map σ = W₁.J →
      ∀ (c₀ : E) (hc₀ : c₀ ≠ 0), IsHermND σ (c₀ • W₁.J.map σ) → IsHermND σ (c₀ • W.J.map σ) →
      ∀ M : UA σ W₁.J → UA σ W.J, Continuous M → (∀ h₁, IsLevi (W₁ := W₁) H 1 h₁ (M h₁)) →
      (∀ γ ∈ ratU σ W₁.J, M γ ∈ ratU σ W.J) →
      ∀ (r : ℕ) (Xf Yf : Matrix (Fin n₁) (Fin r) E), GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W₁.J.map σ) Xf Yf →
      ∀ X' Y' : Matrix (Fin n) (Fin (r + 1)) E, GlobalTheory.SiegelSet.IsWittFrame σ (c₀ • W.J.map σ) X' Y' →
      (∀ k, X' k 0 = H.x k) → (∀ k, Y' k 0 = c₀⁻¹ * H.y k) →
      (∀ (k : Fin n) (i : Fin r), X' k i.succ = (H.ι * Xf) k i ∧ Y' k i.succ = (H.ι * Yf) k i) → ∀ S' : Finset (Fin r),
      ∀ χ : Chr F E, (∀ t : Eˣ, χ (Units.map (inclR (F := F) (E := E) (AF F)).toMonoidHom t) = 1) → Continuous (fun t : (AE F E)ˣ => (χ t : ℂ)) →
      ∀ K₁ : Subgroup (GAd σ (c₀ • W₁.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W₁.J.map σ) K₁ →
      ∀ K' : Subgroup (GAd σ (c₀ • W.J.map σ)), GlobalTheory.UAut.IsMaxCpt σ (c₀ • W.J.map σ) K' →
      ∀ (Kc : Set (GAd σ (c₀ • W.J.map σ))) (d : ℕ) (ψs : Fin d → GAd σ (c₀ • W₁.J.map σ) → ℂ) (a : Fin d → GAd σ (c₀ • W.J.map σ) → ℂ) (Ψ : GAd σ (c₀ • W.J.map σ) → ℂ),
      GlobalTheory.ThK.CuspTransfer.IsInd hσ W W₁ H hc₀ X' M χ Kc ψs a Ψ →
      (∀ i, GlobalTheory.StdPar.IsCuspOn σ (c₀ • W₁.J.map σ) Xf Yf S' K₁ (ψs i)) →
      (IsCompact Kc ∧ (1 : GAd σ (c₀ • W.J.map σ)) ∈ Kc ∧ ∀ k ∈ Kc, ∀ k' ∈ K', k * k' ∈ Kc) → (∀ i, ContinuousOn (a i) Kc) → (∀ i, ∀ k ∈ Kc, ∀ (e : ℕ) (γ : Fin e → ℝ → GAd σ (c₀ • W.J.map σ)), (∀ j, GlobalTheory.SiegelSet.IsRealLine σ (c₀ • W.J.map σ) (γ j)) → (∀ j s, γ j s ∈ K') →
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t : Fin e → ℝ => a i (k * (List.ofFn fun j => γ j (t j)).prod)) → (∃ (e : ℕ) (b : Fin e → GAd σ (c₀ • W.J.map σ) → ℂ), (∀ j, ContinuousOn (b j) Kc) ∧ (∀ i, ∃ c : Fin e → ℂ, ∀ k ∈ Kc, a i k = ∑ j, c j * b j k) ∧
        ∀ j, ∀ k' ∈ K', ∃ c : Fin e → ℂ, ∀ k ∈ Kc, b j (k * k') = ∑ l, c l * b l k) → FiniteDimensional ℂ (Submodule.span ℂ {f | ∃ z, GlobalTheory.UAut.IsCentral σ (c₀ • W.J.map σ) z ∧ f = GlobalTheory.UAut.dop z Ψ}) :=
  fun _ => finite_centre_of_isInd

end GlobalTheory.ThK.IndCentre

end
