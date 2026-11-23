import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SkewAdaptedPlanePairConverse
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerGoodModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerExtension
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniquenessStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneRestrictionIsPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicPlaneVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticIsotropicEmbeddedVanishesAdelic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormRestrictedPlane
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIsotropicLeCard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuadraticModelRationalCoordinates

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.TwoPlaneUniq

open Matrix GlobalTheory.MixedLagrX

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem iota_injective {B : Base F E} {n n₁ j₀ j₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁} {H : Plane E n n₁}
    (hH : H.IsAdapted σ B Y Y₁ j₀ j₁) (hL : Y.L.IsLattice E) (u : Fin n₁ → E) (hu : H.ι *ᵥ u = 0) : u = 0 := by
  let T : E × (Fin n₁ → E) × E →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1 • H.x + H.ι *ᵥ p.2.1 + p.2.2 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, add_smul, Matrix.mulVec_add]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, smul_eq_mul, mul_smul, Matrix.mulVec_smul, RingHom.id_apply, smul_add] }
  have hsurj : Function.Surjective T := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hL.span_eq_top, Submodule.span_le]
    intro z hz
    obtain ⟨s, t, v, -, -, -, rfl⟩ := hH.split z hz
    exact ⟨(s, v, t), rfl⟩
  have hinj : Function.Injective T := by
    rw [LinearMap.injective_iff_surjective_of_finrank_eq_finrank]
    · exact hsurj
    · simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
      have := hH.rank
      omega
  have h0 : T (0, u, 0) = T 0 := by simp [T, hu]
  have := hinj h0
  exact congrArg (fun p => p.2.1) this

variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}

def IsMixed (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ y : Fin n → AE F E, ∃ y' : Fin d₁ → AE F E, ∃ z : Matrix (Fin n₁) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 ∧
    m = Matrix.vecMulVec y (incV F H'.x) + Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y') +
      incM F H.ι * z * (incM F H'.ι)ᵀ

variable {M₁ : Model σ X₁ W₁} {H : Plane E n n₁} {H' : Plane E d d₁}

theorem isMixed_zero : IsMixed M₁ H H' 0 :=
  ⟨0, 0, 0, by simp, by ext i j; simp [Matrix.vecMulVec_apply]⟩

theorem IsMixed.add {m m' : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H H' m) (h' : IsMixed M₁ H H' m') : IsMixed M₁ H H' (m + m') := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  obtain ⟨y', v', z', hz', rfl⟩ := h'
  refine ⟨y + y', v + v', z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mulVec_add, Matrix.vecMulVec_add, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixed.smul {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H H' m) (t : AF F) : IsMixed M₁ H H' (t • m) := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  refine ⟨t • y, t • v, t • z, by simp [hz], ?_⟩
  rw [smul_add, smul_add, Matrix.smul_vecMulVec, Matrix.mulVec_smul, Matrix.vecMulVec_smul, Matrix.mul_smul, Matrix.smul_mul]

def lagr (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixed M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat w))}
  zero_mem' := by simpa [GlobalTheory.MixedLagr.hat_zero] using (isMixed_zero (M₁ := M₁) (H := H) (H' := H'))
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, GlobalTheory.MixedLagr.hat_add, map_add] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixed M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat (c • a)))
    rw [GlobalTheory.MixedLagr.hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

theorem pieceB_eq (y' : Fin d₁ → AE F E) : Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ y') =
    incM F (1 : Matrix (Fin n) (Fin n) E) * Matrix.vecMulVec (incV F H.x) y' * (incM F H'.ι)ᵀ := by
  rw [incM_one, Matrix.one_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose]

theorem pieceC_eq (z : Matrix (Fin n₁) (Fin d₁) (AE F E)) : incM F H.ι * z * (incM F H'.ι)ᵀ =
    incM F (1 : Matrix (Fin n) (Fin n) E) * (incM F H.ι * z * (incM F (1 : Matrix (Fin d₁) (Fin d₁) E))ᵀ) *
      (incM F H'.ι)ᵀ := by
  rw [incM_one, incM_one, Matrix.one_mul, Matrix.transpose_one, Matrix.mul_one]

variable {B : Base F E} {Y : Spc F E n} {i₀ i₁ j₀ j₁ : ℕ}

theorem symp_mixed (hJ : Y.J = X.J) (hH : H.IsAdapted σ B Y X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (M : Model σ X W) {m m' : Matrix (Fin n) (Fin d) (AE F E)} (h : IsMixed M₁ H H' m) (h' : IsMixed M₁ H H' m') :
    (M.co.e m).1 ⬝ᵥ (M.co.e m').2 - (M.co.e m').1 ⬝ᵥ (M.co.e m).2 = 0 := by
  obtain ⟨y, v, z, hz, rfl⟩ := h
  obtain ⟨y', v', z', hz', rfl⟩ := h'
  have hQ : ∀ a b, (M.co.e a).1 ⬝ᵥ (M.co.e b).2 - (M.co.e b).1 ⬝ᵥ (M.co.e a).2 =
      symp (cA σ) (-1) (incM F X.J) (incM F W.J) a b := fun a b => (M.co.form a b).symm
  have hcross := GlobalTheory.MixedLagr.symplectic_isotropic_embedded_vanishes F E σ n d d₁ X.J W.J H' (fun u => (hH'.orth u).1)
  have hgram := GlobalTheory.MixedLagrGram.symp_restrict_gram F E σ n d d₁ X.J W.J W₁.J H'.ι hH'.gram
  have hAA := GlobalTheory.MixedLagr.symplectic_isotropic_plane_vanishes F E σ n d d₁ X.J W.J H' hH'.xx _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
  have hBA : ∀ a b, symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ a))
      (Matrix.vecMulVec b (incV F H'.x)) = 0 := fun a b => by
    rw [pieceB_eq]; exact hcross _ ⟨b, rfl⟩ _
  have hCA : ∀ (a : Matrix (Fin n₁) (Fin d₁) (AE F E)) b, symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * a * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec b (incV F H'.x)) = 0 := fun a b => by
    rw [pieceC_eq]; exact hcross _ ⟨b, rfl⟩ _
  have hBB : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v))
      (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v')) = 0 :=
    symp_eq_zero _ _ _ _ (hJ ▸ piece_xx hH _ _)
  have hCB : ∀ (a : Matrix (Fin n₁) (Fin d₁) (AE F E)) b, symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * a * (incM F H'.ι)ᵀ)
      (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ b)) = 0 := fun a b => by
    rw [pieceC_eq a, pieceB_eq b, hgram]
    exact symp_eq_zero _ _ _ _ (hJ ▸ piece_ix hH _ _)
  have hCC : symp (cA σ) (-1) (incM F X.J) (incM F W.J) (incM F H.ι * z * (incM F H'.ι)ᵀ)
      (incM F H.ι * z' * (incM F H'.ι)ᵀ) = 0 := by
    rw [pieceC_eq z, pieceC_eq z', hgram, ← hJ]
    have : symp (cA σ) (-1) (incM F Y.J) (incM F W₁.J) (incM F H.ι * z * (incM F (1 : Matrix (Fin d₁) (Fin d₁) E))ᵀ)
        (incM F H.ι * z' * (incM F (1 : Matrix (Fin d₁) (Fin d₁) E))ᵀ) =
        symp (cA σ) (-1) (incM F X₁.J) (incM F W₁.J) z z' := by
      simp only [symp, hTens_eq, piece_ii hH]
    rw [this, M₁.co.form, hz, hz', zero_dotProduct, zero_dotProduct, sub_self]
  have h1 := hBA v y'
  have h2 := hBA v' y
  have h3 := hCA z y'
  have h4 := hCA z' y
  have h5 := hCB z v'
  have h6 := hCB z' v
  rw [← hQ] at hAA hBB hCC h1 h2 h3 h4 h5 h6
  simp only [map_add, Prod.fst_add, Prod.snd_add, add_dotProduct, dotProduct_add]
  linear_combination hAA + hBB + hCC + h1 - h2 + h3 - h4 + h5 - h6

theorem form_zero_left {m : ℕ} (J : Matrix (Fin m) (Fin m) E) (c : Fin m → E) : form σ J 0 c = 0 := by
  simp [form]

theorem le_finrank_lagr (hH : H.IsAdapted σ B Y X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hY : Y.L.IsLattice E) (hW : W.L.IsLattice E) (M : Model σ X W) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (h2 : Module.finrank F E = 2) : Fintype.card (Fin n × Fin d) ≤ Module.finrank F (lagr M M₁ H H') := by
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n d X W M B.ψ hM h2
  obtain ⟨Φ₁, hΦ₁⟩ := GlobalTheory.RatCoord.ratEquiv F E σ n₁ d₁ X₁ W₁ M₁ B.ψ hM₁ h2
  let f₁ : Matrix (Fin n₁) (Fin d₁) E →ₗ[F] (Fin n₁ × Fin d₁ → F) := (LinearMap.fst F _ _).comp Φ₁.toLinearMap
  have hf₁ : Function.Surjective f₁ := fun v => ⟨Φ₁.symm (v, 0), by simp [f₁]⟩
  have hZ : Module.finrank F (LinearMap.ker f₁) = n₁ * d₁ := by
    have := LinearMap.finrank_range_add_finrank_ker f₁
    rw [LinearMap.range_eq_top.mpr hf₁, finrank_top, LinearEquiv.finrank_eq Φ₁, Module.finrank_prod,
      Module.finrank_fintype_fun_eq_card, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin] at this
    omega
  let G : (Fin n → E) × (Fin d₁ → E) × LinearMap.ker f₁ →ₗ[F] Matrix (Fin n) (Fin d) E :=
    { toFun := fun p => Matrix.vecMulVec p.1 H'.x +
        (Matrix.vecMulVec H.x p.2.1 + H.ι * (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)) * H'.ιᵀ
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, Matrix.vecMulVec_add, Matrix.add_vecMulVec,
          Matrix.mul_add, Matrix.add_mul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, RingHom.id_apply, Matrix.smul_vecMulVec,
          Matrix.vecMulVec_smul, Matrix.mul_smul, ← smul_add, Matrix.smul_mul] }
  have hmem : ∀ p, Φ (G p) ∈ lagr M M₁ H H' := by
    intro p
    show IsMixed M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat (Φ (G p))))
    have : GlobalTheory.MixedLagr.hat (Φ (G p)) = M.co.e (incM F (G p)) := (hΦ _).symm
    rw [this, LinearEquiv.symm_apply_apply]
    refine ⟨incV F p.1, incV F p.2.1, incM F (p.2.2 : Matrix (Fin n₁) (Fin d₁) E), ?_, ?_⟩
    · have hz : (Φ₁ (p.2.2 : Matrix (Fin n₁) (Fin d₁) E)).1 = 0 := p.2.2.2
      rw [hΦ₁, hz]; funext i; simp
    · rw [incM_mulVec, ← incM_mul, ← incM_transpose, ← incM_mul]
      have hG : G p = Matrix.vecMulVec p.1 H'.x + Matrix.vecMulVec H.x (H'.ι *ᵥ p.2.1) +
          H.ι * (p.2.2 : Matrix (Fin n₁) (Fin d₁) E) * H'.ιᵀ := by
        simp only [G, LinearMap.coe_mk, AddHom.coe_mk]
        rw [Matrix.add_mul, Matrix.vecMulVec_mul, Matrix.vecMul_transpose, add_assoc]
      rw [hG]
      ext i j
      simp only [incM, incV, Matrix.map_apply, Matrix.add_apply, Matrix.vecMulVec_apply, map_add, map_mul]
  have hGinj : ∀ p, G p = 0 → p = 0 := by
    rintro ⟨y, v, z⟩ h
    change Matrix.vecMulVec y H'.x + (Matrix.vecMulVec H.x v + H.ι * (z : Matrix (Fin n₁) (Fin d₁) E)) * H'.ιᵀ = 0 at h
    generalize hm : Matrix.vecMulVec H.x v + H.ι * (z : Matrix (Fin n₁) (Fin d₁) E) = m at h
    have hrow : ∀ i, y i • H'.x + H'.ι *ᵥ m i = 0 := fun i => by
      funext j
      have := congrFun (congrFun h i) j
      simpa [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    have hy : y = 0 := by
      funext i
      have hi := congrArg (fun A : Fin d → E => form σ W.J A H'.y) (hrow i)
      rwa [form_add_left, form_smul_left, hH'.xy, (hH'.orth _).2, mul_one, add_zero, form_zero_left] at hi
    subst hy
    have hm0 : m = 0 := by
      funext i
      exact iota_injective hH' hW _ (by simpa using hrow i)
    subst hm0
    have hcol : ∀ j, v j • H.x + H.ι *ᵥ (fun k => (z : Matrix (Fin n₁) (Fin d₁) E) k j) = 0 := fun j => by
      funext i
      have := congrFun (congrFun hm i) j
      simpa [Matrix.vecMulVec_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using this
    have hv : v = 0 := by
      funext j
      have hj := congrArg (fun A : Fin n → E => form σ Y.J A H.y) (hcol j)
      rwa [form_add_left, form_smul_left, hH.xy, (hH.orth _).2, mul_one, add_zero, form_zero_left] at hj
    subst hv
    have hz : (z : Matrix (Fin n₁) (Fin d₁) E) = 0 := by
      ext k j
      exact congrFun (iota_injective hH hY _ (by simpa using hcol j)) k
    exact Prod.ext rfl (Prod.ext rfl (Subtype.ext hz))
  let T : (Fin n → E) × (Fin d₁ → E) × LinearMap.ker f₁ →ₗ[F] lagr M M₁ H H' := (Φ.toLinearMap.comp G).codRestrict _ hmem
  have hT : Function.Injective T := by
    intro p q hpq
    have hG : G p = G q := Φ.injective (congrArg Subtype.val hpq)
    rw [← sub_eq_zero, ← map_sub] at hG
    exact sub_eq_zero.mp (hGinj _ hG)
  have hle := LinearMap.finrank_le_finrank_of_injective hT
  rw [Module.finrank_prod, Module.finrank_prod, hZ, Module.finrank_pi_fintype, Module.finrank_pi_fintype] at hle
  simp only [h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at hle
  have e1 := hH.rank
  have e2 := hH'.rank
  calc Fintype.card (Fin n × Fin d) = n * d := by simp
    _ = n * 2 + (d₁ * 2 + n₁ * d₁) := by rw [e1, e2]; ring
    _ ≤ _ := hle

theorem unique (hB : B.IsGood σ) (hJ : Y.J = X.J) (hH : H.IsAdapted σ B Y X₁ j₀ j₁) (hH' : H'.IsAdapted σ B W W₁ i₀ i₁)
    (hY : Y.L.IsLattice E) (hW : W.L.IsLattice E) (M : Model σ X W) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (he : IsEv B M M₁ H.ι H'.ι (isoA H H') e) (e' : Fn F n d →ₗ[ℂ] Fn F n₁ d₁)
    (hheis : ∀ z, ∀ Φ ∈ schA F (Fin n × Fin d),
      e' (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = M₁.co.rho B.ψ z (e' Φ))
    (hinv : ∀ u ∈ isoA (F := F) H H', ∀ Φ ∈ schA F (Fin n × Fin d), e' (M.co.rho B.ψ u Φ) = e' Φ)
    (hpt : ∀ y : Fin n₁ × Fin d₁ → AF F, (LinearMap.proj y : Fn F n₁ d₁ →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin n × Fin d)) :
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin n × Fin d), e' Φ = c • e Φ := by
  have hstd : IsStd B.ψ := hB.std
  have h2 : Module.finrank F E = 2 := hB.cm.2.2.1
  let δ : Fn F n₁ d₁ →ₗ[ℂ] ℂ := LinearMap.proj 0
  have hδ : δ ∈ (adeleClass F).adm (Fin n₁ × Fin d₁) := GlobalTheory.EvZeroUniq.proj_zero_mem_adm F _
  have hρ : ∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ u Φ ∈ schA F (Fin n × Fin d) :=
    fun u Φ hΦ => GlobalTheory.EvZeroUniq.schr_mem_schA _ hstd _ hΦ
  have hδe : ∀ (f : Fn F n₁ d₁) x, f x = δ (M₁.co.rho B.ψ (M₁.co.e.symm (x, 0)) f) := fun f x =>
    GlobalTheory.EvZeroUniq.apply_eq_rho _ _ f x
  have hfix : ∀ z, (M₁.co.e z).1 = 0 → ∀ f : Fn F n₁ d₁, δ (M₁.co.rho B.ψ z f) = δ f :=
    fun z hz f => GlobalTheory.EvZeroUniq.rho_apply_zero _ _ f z hz
  obtain ⟨Φ₀, hΦ₀, hne⟩ := GlobalTheory.ThK.EvNeZero.exists_ne_zero F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H.ι H'.ι _ e hM hM₁ he
  obtain ⟨x₀, hx₀⟩ : ∃ x, e Φ₀ x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  have hiso : ∀ a ∈ lagr M M₁ H H', ∀ b ∈ lagr M M₁ H H', a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2 := by
    intro a ha b hb
    have h := symp_mixed hJ hH hH' M ha hb
    simp only [LinearEquiv.apply_symm_apply, GlobalTheory.MixedLagr.hat] at h
    rw [← sub_eq_zero]
    apply AdeleRing.algebraMap_injective (𝓞 F) F
    rw [map_sub, map_zero, RingHom.map_dotProduct, RingHom.map_dotProduct]
    exact h
  have hrank : Module.finrank F (lagr M M₁ H H') = Fintype.card (Fin n × Fin d) :=
    le_antisymm (GlobalTheory.isotropic_finrank_le_card F _ _ hiso) (le_finrank_lagr hH hH' hY hW M hM hM₁ h2)
  have hcomp : ∀ m m', IsMixed M₁ H H' m → IsMixed M₁ H H' m' → ∀ φ : Fn F n d,
      M.co.rho B.ψ (m + m') φ = M.co.rho B.ψ m (M.co.rho B.ψ m' φ) := by
    intro m m' hm hm' φ
    change schr B.ψ (M.co.e _) φ = schr B.ψ (M.co.e _) (schr B.ψ (M.co.e _) φ)
    rw [GlobalTheory.MixedLagr.schr_comp, symp_mixed hJ hH hH' M hm hm', mul_zero, AddChar.map_zero_eq_one, one_smul, ← map_add]
  have hinvL : ∀ l : Fn F n d →ₗ[ℂ] ℂ, (∀ u ∈ isoA (F := F) H H', ∀ Φ ∈ schA F (Fin n × Fin d), l (M.co.rho B.ψ u Φ) = l Φ) →
      (∀ z : Matrix (Fin n₁) (Fin d₁) (AE F E), (M₁.co.e z).1 = 0 → ∀ Φ ∈ schA F (Fin n × Fin d),
        l (M.co.rho B.ψ (incM F H.ι * z * (incM F H'.ι)ᵀ) Φ) = l Φ) →
      ∀ (t : AF F), ∀ w ∈ lagr M M₁ H H', ∀ φ ∈ schA F (Fin n × Fin d),
        l (schr B.ψ (t • ((fun i => algebraMap F (AF F) (w.1 i)), (fun i => algebraMap F (AF F) (w.2 i)))) φ) = l φ := by
    intro l h1 h2 t w hw φ hφ
    obtain ⟨y, v, z, hz, hm⟩ := (show IsMixed M₁ H H' (M.co.e.symm (GlobalTheory.MixedLagr.hat w)) from hw).smul t
    have hz0 : Matrix.vecMulVec (incV F H.x) (0 : Fin d → AE F E) = 0 := by ext i j; simp [Matrix.vecMulVec_apply]
    have hA : IsMixed M₁ H H' (Matrix.vecMulVec y (incV F H'.x)) :=
      ⟨y, 0, 0, by simp, by rw [Matrix.mulVec_zero, hz0, Matrix.mul_zero, Matrix.zero_mul, add_zero, add_zero]⟩
    have hBv : IsMixed M₁ H H' (Matrix.vecMulVec (incV F H.x) (incM F H'.ι *ᵥ v)) :=
      ⟨0, v, 0, by simp, by rw [Matrix.zero_vecMulVec, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]⟩
    have hC : IsMixed M₁ H H' (incM F H.ι * z * (incM F H'.ι)ᵀ) :=
      ⟨0, 0, z, hz, by rw [Matrix.zero_vecMulVec, Matrix.mulVec_zero, hz0, zero_add, zero_add]⟩
    have key : schr B.ψ (t • GlobalTheory.MixedLagr.hat w) φ = M.co.rho B.ψ (t • M.co.e.symm (GlobalTheory.MixedLagr.hat w)) φ := by
      rw [Darboux.rho, LinearEquiv.map_smul, LinearEquiv.apply_symm_apply]
    change l (schr B.ψ (t • GlobalTheory.MixedLagr.hat w) φ) = l φ
    rw [key, hm, hcomp _ _ (hA.add hBv) hC, hcomp _ _ hA hBv, h1 _ (Or.inl ⟨y, rfl⟩) _ (hρ _ _ (hρ _ φ hφ)),
      h1 _ (Or.inr ⟨v, rfl⟩) _ (hρ _ φ hφ), h2 z hz φ hφ]
  obtain ⟨c, hc⟩ := GlobalTheory.T.adelicStoneVonNeumann_lagrangian_uniqueness F B.ψ hstd (Fin n × Fin d) _ hiso hrank (δ ∘ₗ e') (hpt 0) (δ ∘ₗ e)
    (GlobalTheory.EvAdm.comp_mem_adm F E σ B n d n₁ d₁ X W X₁ W₁ M M₁ H.ι H'.ι _ e hM hM₁ he δ hδ)
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hinv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [hheis z Φ hΦ, hfix z hz]))
    (hinvL _ (fun u hu Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.inv u hu Φ hΦ])
      (fun z hz Φ hΦ => by simp only [LinearMap.comp_apply]; rw [he.Heisenberg₂ z Φ hΦ, hfix z hz]))
    ⟨_, hρ (incM F H.ι * M₁.co.e.symm (x₀, 0) * (incM F H'.ι)ᵀ) Φ₀ hΦ₀, by
      simp only [LinearMap.comp_apply]
      rw [he.Heisenberg₂ _ Φ₀ hΦ₀, ← hδe]
      exact hx₀⟩
  refine ⟨c, fun Φ hΦ => funext fun x => ?_⟩
  have h1 := hc _ (hρ (incM F H.ι * M₁.co.e.symm (x, 0) * (incM F H'.ι)ᵀ) Φ hΦ)
  simp only [LinearMap.comp_apply] at h1
  rw [hheis _ Φ hΦ, he.Heisenberg₂ _ Φ hΦ, ← hδe, ← hδe] at h1
  simpa using h1

theorem main : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ →
    ∀ e' : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b),
    (∀ z, ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' (G.M.co.rho B.ψ (incM F H₀.ι * z * (incM F H'.ι)ᵀ) Φ) = M₂.co.rho B.ψ z (e' Φ)) →
    (∀ u ∈ isoA (F := F) H₀ H', ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' (G.M.co.rho B.ψ u Φ) = e' Φ) →
    (∀ y : Fin n₁ × Fin (a + b) → AF F, (LinearMap.proj y : Fn F n₁ (a + b) →ₗ[ℂ] ℂ) ∘ₗ e' ∈ (adeleClass F).adm (Fin a × Fin (a + (b + 2)))) →
    ∃ c : ℂ, ∀ Φ ∈ schA F (Fin a × Fin (a + (b + 2))), e' Φ = c • e₂ Φ := by
  intro _ F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT _ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV₂ hH₀ hM₂ he e' h1 h2 h3
  have hP := (GlobalTheory.ThK.Check.isPair_of_isTriple hT).1
  exact unique (X := G.V) (Y := reS G.V V₂) hP.base rfl hH₀ hC.hH' hV₂.lat hP.skew.lat G.M hP.good hM₂ e₂ he e' h1 h2 h3

end GlobalTheory.TwoPlaneUniq

end
