import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionIsPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewDeterminantNeZeroFirstSpaceStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagrA

open Matrix GlobalTheory.MixedLagrX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def IsMixedA (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ y : Fin n → AE F E, ∃ v : Fin d₁ → AE F E, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 ∧
    m = Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v) +
      incM F H.ι * z * (incM F H'.ι)ᵀ

theorem isMixedA_zero (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) : IsMixedA M₁ H H' 0 :=
  ⟨0, 0, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩

theorem IsMixedA.add {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {m m' : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixedA M₁ H H' m) (h' : IsMixedA M₁ H H' m') : IsMixedA M₁ H H' (m + m') := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  obtain ⟨y', v', z', hz', rfl⟩ := h'
  refine ⟨y + y', v + v', z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixedA.smul {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixedA M₁ H H' m) (t : AF F) : IsMixedA M₁ H H' (t • m) := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  refine ⟨t • y, t • v, t • z, by simp [hz], ?_⟩
  rw [smul_add, smul_add, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul]

def lagrA (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixedA M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat w))}
  zero_mem' := by simpa [GlobalTheory.MixedLagr.hat_zero] using isMixedA_zero M₁ H H'
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, GlobalTheory.MixedLagr.hat_add, map_add] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixedA M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat (c • a)))
    rw [GlobalTheory.MixedLagr.hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

theorem piece_b_eq (H : Plane E n n₁) (H' : Plane E d d₁) (v : Fin d₁ → AE F E) :
    Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v) =
      incM F (1 : Matrix (Fin n) (Fin n) E) * Matrix.vecMulVec (incV F H.x) v * (incM F H'.ι)ᵀ := by
  rw [incM_one, Matrix.one_mul]
  ext i j
  simp only [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun l _ => by ring

theorem piece_c_left_identity (H : Plane E n n₁) (H' : Plane E d d₁) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) :
    incM F H.ι * z * (incM F H'.ι)ᵀ = incM F (1 : Matrix (Fin n) (Fin n) E) * (incM F H.ι * z) * (incM F H'.ι)ᵀ := by
  rw [incM_one, Matrix.one_mul]

theorem piece_c_right_identity (H : Plane E n n₁) (H' : Plane E d d₁) (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) :
    incM F H.ι * z * (incM F H'.ι)ᵀ = incM F H.ι * (z * (incM F H'.ι)ᵀ) * (incM F (1 : Matrix (Fin d) (Fin d) E))ᵀ := by
  rw [incM_one, Matrix.transpose_one, Matrix.mul_one, Matrix.mul_assoc]

theorem symp_mixedA {B : Base F E} {j₀ j₁ i₀ i₁ : ℕ} {H : Plane E n n₁} {H' : Plane E d d₁}
    (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁) (M : Model σ X W) (M₁ : Model σ X₁ W₁)
    {m m' : Matrix (Fin n) (Fin d) (AE F E)} (h : IsMixedA M₁ H H' m) (h' : IsMixedA M₁ H H' m') :
    (M.co.e m).1 ⬝ᵥ (M.co.e m').2 - (M.co.e m').1 ⬝ᵥ (M.co.e m).2 = 0 := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  obtain ⟨y', v', z', hz', rfl⟩ := h'
  have hQ : ∀ a b, (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) a b := fun a b => (M.co.form a b).symm
  have ha : Matrix.vecMulVec y (incV F H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))) := ⟨y, rfl⟩
  have ha' : Matrix.vecMulVec y' (incV F H'.x) ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))) := ⟨y', rfl⟩
  have hcross := GlobalTheory.T.symplectic_isotropic_embedded_vanishes_adelic F E σ n d d₁ X.J W.J H' (fun u => (hH'.orth u).1)
  have h_aa := GlobalTheory.T.symplectic_isotropic_plane_vanishes_adelic F E σ n d d₁ X.J W.J H' hH'.xx _ ha _ ha'
  have h_ba' := hcross _ ha' (Matrix.vecMulVec (incV F H.x) v)
  have h_b'a := hcross _ ha (Matrix.vecMulVec (incV F H.x) v')
  have h_ca' := hcross _ ha' (incM F H.ι * z)
  have h_c'a := hcross _ ha (incM F H.ι * z')
  have h_bb' := symp_eq_zero (JB := W.J) _ _ _ (piece_xx hH (incM F H'.ι *ᵥ v) (incM F H'.ι *ᵥ v'))
  have h_cb' := symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH (z * (incM F H'.ι)ᵀ) (incM F H'.ι *ᵥ v'))
  have h_c'b := symp_eq_zero (JB := W.J) _ _ _ (piece_ix hH (z' * (incM F H'.ι)ᵀ) (incM F H'.ι *ᵥ v))
  have h_cc : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ)
      (incM F H.ι * z' * (incM F H'.ι)ᵀ) = 0 := by
    rw [piece_c_left_identity H H' z, piece_c_left_identity H H' z', GlobalTheory.T.symplectic_form_restricted_plane F E σ n d d₁ X.J W.J W₁.J H'.ι hH'.gram]
    have e1 := piece_ii (d := d₁) hH z z'
    have e2 := piece_ii (d := d₁) hH z' z
    simp only [incM_one, Matrix.transpose_one, Matrix.mul_one] at e1 e2
    have : symp (cA σ) (-1) (incM F X.J) (incM F W₁.J) (incM F H.ι * z) (incM F H.ι * z') =
        symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) z z' := by
      simp only [symp, hTens_eq, e1, e2]
    rw [this, M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_self]
  rw [← piece_b_eq] at h_ba' h_b'a
  rw [← piece_c_left_identity] at h_ca' h_c'a
  rw [← piece_c_right_identity] at h_cb' h_c'b
  rw [← hQ] at h_aa h_ba' h_b'a h_ca' h_c'a h_bb' h_cb' h_c'b h_cc
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination h_aa + h_ba' - h_b'a + h_ca' - h_c'a + h_bb' + h_cb' - h_c'b + h_cc

end GlobalTheory.MixedLagrA

namespace GlobalTheory.MixedLagrA

open Matrix GlobalTheory.MixedLagrX

theorem le_finrank_lagrA {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    (B : Base F E) (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁)
    {j₀ j₁ i₀ i₁ : ℕ} (hH : H.IsAdapted σ B X X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ) (h2 : Module.finrank F E = 2) (hdX : X₁.J.det ≠ 0) (hdW : W₁.J.det ≠ 0) :
    Fintype.card (Fin n × Fin d) ≤ Module.finrank F (lagrA M M₁ H H') := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ n d X W M B.ψ hM h2
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.T.quadratic_model_rational_coordinates F E σ n₁ d₁ X₁ W₁ M₁ B.ψ hM₁ h2
  let f₁ : Matrix (Fin n₁) (Fin d₁) E →ₗ[F] (Fin n₁ × Fin d₁ → F) := (LinearMap.fst F _ _).comp Φ₁.toLinearMap
  have hf₁ : Function.Surjective f₁ := fun v => ⟨Φ₁.symm (v, 0), by simp [f₁]⟩
  have hZ : Module.finrank F (LinearMap.ker f₁) = n₁ * d₁ := by
    have := LinearMap.finrank_range_add_finrank_ker f₁
    rw [LinearMap.range_eq_top.mpr hf₁, finrank_top, LinearEquiv.finrank_eq Φ₁, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    omega
  let G : (Fin n → E) × (Fin d₁ → E) × LinearMap.ker f₁ →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ p.2.1) +
        H.ι * (p.2.2 : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.add_vecMulVec, Matrix.mulVec_add,
          Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]
        abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, Matrix.smul_vecMulVec,
          Matrix.mulVec_smul, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul, smul_add] }
  have hmem : ∀ p, Φ (G p) ∈ lagrA M M₁ H H' := by
    intro p
    show IsMixedA M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat (Φ (G p))))
    have : GlobalTheory.MixedLagr.hat (Φ (G p)) = M.co.e (incM F (G p)) := (hΦ _).symm
    rw [this, LinearEquiv.symm_apply_apply]
    refine ⟨incV F p.1, incV F p.2.1, incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E), ?_, ?_⟩
    · have hz : (Φ₁ (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)).1 = 0 := p.2.2.2
      rw [hΦ₁, hz]; funext i; simp
    · rw [incM_mulVec, ← incM_transpose, ← incM_mul, ← incM_mul]
      ext i j
      simp only [incM, incV, G, LinearMap.coe_mk, AddHom.coe_mk, Matrix.map_apply, Matrix.add_apply,
        Matrix.vecMulVec_apply, map_add, map_mul]
  have hGinj : ∀ p, G p = 0 → p = 0 := by
    rintro ⟨y, v, z⟩ h
    change Matrix.vecMulVec y H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ v) +
      H.ι * (z : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ = 0 at h
    have hy : y = 0 := by
      funext i
      have hrow : (fun j => (Matrix.vecMulVec y H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ v) +
          H.ι * (z : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ) i j) =
          y i • H'.x + H.x i • (H'.ι *ᵥ v) + H'.ι *ᵥ (fun l => (H.ι * (z : Matrix (Fin n₁) (Fin d₁) E)) i l) := by
        funext j; simp [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm]
      have hi := congrArg (fun A : Fin d → E => form σ W.J A H'.y) hrow
      simp only [h, Matrix.zero_apply] at hi
      rw [form_add_left, form_add_left, form_smul_left, form_smul_left, hH'.xy, (hH'.orth _).2, (hH'.orth _).2,
        mul_one, mul_zero, add_zero, add_zero] at hi
      rw [← hi]; simp [form]
    subst hy
    rw [Matrix.mul_assoc] at h
    have hv0 : H'.ι *ᵥ v = 0 := by
      funext j
      have hcol : (fun i => (Matrix.vecMulVec (0 : Fin n → E) H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ v) +
          H.ι * ((z : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ) : Matrix (Fin n) (Fin d) E) i j) =
          (H'.ι *ᵥ v) j • H.x + H.ι *ᵥ (fun k => ((z : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ) k j) := by
        funext i; simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.zero_apply, zero_mul, zero_add,
          Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.mul_apply (M := H.ι), Matrix.mulVec, dotProduct]; ring
      have hj := congrArg (fun A : Fin n → E => form σ X.J A H.y) hcol
      simp only [h, Matrix.zero_apply] at hj
      rw [form_add_left, form_smul_left, hH.xy, (hH.orth _).2, mul_one, add_zero] at hj
      rw [← hj]; simp [form]
    have hv : v = 0 := by
      have := GlobalTheory.MixedLagr.mul_transpose_injective F E σ 1 d d₁ W.J W₁.J H'.ι hH'.gram hdW
        (a₁ := Matrix.of fun _ l => v l) (a₂ := 0) (by
          beta_reduce
          ext i j
          have := congrFun hv0 j
          simp only [Matrix.mulVec, dotProduct, Pi.zero_apply] at this
          rw [Matrix.zero_mul, Matrix.zero_apply, Matrix.mul_apply]
          simp only [Matrix.transpose_apply, Matrix.of_apply]
          exact (Finset.sum_congr rfl fun l _ => mul_comm (v l) (H'.ι j l)).trans this)
      funext l; exact congrFun (congrFun this 0) l
    subst hv
    have h0 : H.ι * ((z : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ) = 0 := by
      rw [← h]; ext i j; simp [Matrix.vecMulVec_apply]
    have hιZ : H.ι * (z : Matrix (Fin n₁) (Fin d₁) E) = 0 :=
      GlobalTheory.MixedLagr.mul_transpose_injective F E σ n d d₁ W.J W₁.J H'.ι hH'.gram hdW (a₁ := H.ι * (z : Matrix (Fin n₁) (Fin d₁) E))
        (a₂ := 0) (by beta_reduce; rw [Matrix.zero_mul]; rw [Matrix.mul_assoc]; exact h0)
    have hZt : (z : Matrix (Fin n₁) (Fin d₁) E)ᵀ = 0 :=
      GlobalTheory.MixedLagr.mul_transpose_injective F E σ d₁ n n₁ X.J X₁.J H.ι hH.gram hdX (a₁ := (z : Matrix (Fin n₁) (Fin d₁) E)ᵀ)
        (a₂ := 0) (by beta_reduce; rw [Matrix.zero_mul, ← Matrix.transpose_mul, hιZ, Matrix.transpose_zero])
    have hZ0 : (z : Matrix (Fin n₁) (Fin d₁) E) = 0 := by
      rw [← Matrix.transpose_transpose (z : Matrix (Fin n₁) (Fin d₁) E), hZt, Matrix.transpose_zero]
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext hZ0))
  let T : (Fin n → E) × (Fin d₁ → E) × LinearMap.ker f₁ →ₗ[F] lagrA M M₁ H H' := (Φ.toLinearMap.comp G).codRestrict _ hmem
  have hT : Function.Injective T := by
    intro p q hpq
    have hG : G p = G q := Φ.injective (congrArg Subtype.val hpq)
    rw [← sub_eq_zero, ← map_sub] at hG
    exact sub_eq_zero.mp (hGinj _ hG)
  have hle := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_prod, Module.finrank_prod, hZ, Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hle
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  have key : n * d = n * 2 + (d₁ * 2 + n₁ * d₁) := by rw [hH.rank, hH'.rank]; ring
  calc Fintype.card (Fin n × Fin d) = n * d := by simp
    _ = n * 2 + (d₁ * 2 + n₁ * d₁) := key
    _ ≤ _ := hle

end GlobalTheory.MixedLagrA

namespace GlobalTheory.MixedLagrA

open Matrix GlobalTheory.MixedLagrX

theorem lagrangian_isoA : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∃ L : Submodule F ((Fin (b + 2) × Fin (b + 2 + a') → F) × (Fin (b + 2) × Fin (b + 2 + a') → F)), (∀ p ∈ L, ∀ q ∈ L, p.1 ⬝ᵥ q.2 = q.1 ⬝ᵥ p.2) ∧
      Module.finrank F L = Fintype.card (Fin (b + 2) × Fin (b + 2 + a')) ∧
      ∀ (t : AF F), ∀ w ∈ L, ∃ u₁ ∈ iso0 (F := F) (b + 2) H', ∃ u₂ ∈ {u : Matrix (Fin (b + 2)) (Fin (b + 2 + a')) (AE F E) | ∃ y, u = Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y)},
        ∃ z : Matrix (Fin b) (Fin (b + a')) (AE F E), (G₁.M.co.e z).1 = 0 ∧ ∀ φ : Fn F (b + 2) (b + 2 + a'),
          schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ =
            G.M.co.rho B.ψ u₁ (G.M.co.rho B.ψ u₂ (G.M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) φ)) := by
  intro _ F E _ _ _ _ _ σ B b a' G G₁ H H' hC X om om' om₁ om₁' hT hT₁
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  have hP₁ := (GlobalTheory.ThK.Check.isPair_of_isTriple hT₁).1
  have hH := hC.hH
  have hH' := hC.hH'
  have h2 : Module.finrank F E = 2 := hP.base.cm.2.2.1
  have hdX : G₁.V.J.det ≠ 0 := by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    intro h0
    apply GlobalTheory.T.det_ne_zero_of_hasSig_divisor b _ _ _ (hP₁.herm.sig w)
    have := RingHom.map_det (B.emb w).1 G₁.V.J
    rw [h0, map_zero] at this
    exact this.symm
  have hdW : G₁.W.J.det ≠ 0 := GlobalTheory.T.skew_determinant_ne_zero_first_space F E σ B _ G₁.W _ _ hP₁.skew
  have hiso : ∀ p ∈ lagrA G.M G₁.M H H', ∀ q ∈ lagrA G.M G₁.M H H', p.1 ⬝ᵥ q.2 = q.1 ⬝ᵥ p.2 := by
    intro p hp q hq
    have h := symp_mixedA hH hH' G.M G₁.M hp hq
    simp only [LinearEquiv.apply_symm_apply, GlobalTheory.MixedLagr.hat] at h
    rw [← sub_eq_zero]
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_sub, map_zero, RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  refine ⟨lagrA G.M G₁.M H H', hiso, le_antisymm (GlobalTheory.T.finrank_isotropic_le_card F _ _ hiso)
    (le_finrank_lagrA B G.M G₁.M H H' hH hH' hP.good hP₁.good h2 hdX hdW), ?_⟩
  intro t w hw
  obtain ⟨y, v, z, hz, hm⟩ := (show IsMixedA G₁.M H H' (G.M.co.e.symm (GlobalTheory.MixedLagr.hat w)) from hw).smul t
  refine ⟨Matrix.vecMulVec y (incV F H'.x), ⟨y, rfl⟩, Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v), ⟨v, rfl⟩, z, hz,
    fun φ => ?_⟩
  have key : t • GlobalTheory.MixedLagr.hat w = G.M.co.e (Matrix.vecMulVec y (incV F H'.x) +
      Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v) + incM F H.ι * z * (incM F H'.ι)ᵀ) := by
    rw [← hm, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
  have ha : IsMixedA G₁.M H H' (Matrix.vecMulVec y (incV F H'.x)) := ⟨y, 0, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩
  have hb : IsMixedA G₁.M H H' (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v)) :=
    ⟨0, v, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩
  have hc : IsMixedA G₁.M H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) :=
    ⟨0, 0, z, hz, by ext i j; simp [Matrix.vecMulVec_apply]⟩
  change schr B.ψ (t • GlobalTheory.MixedLagr.hat w) φ = schr B.ψ (G.M.co.e _) (schr B.ψ (G.M.co.e _) (schr B.ψ (G.M.co.e _) φ))
  rw [GlobalTheory.MixedLagr.schr_comp B.ψ (G.M.co.e (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v))),
    symp_mixedA hH hH' G.M G₁.M hb hc, mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add,
    GlobalTheory.MixedLagr.schr_comp, symp_mixedA hH hH' G.M G₁.M ha (hb.add hc), mul_zero, AddChar.map_zero_eq_one, one_smul,
    ← map_add, key, add_assoc (Matrix.vecMulVec y (incV F H'.x))]

end GlobalTheory.MixedLagrA

end
