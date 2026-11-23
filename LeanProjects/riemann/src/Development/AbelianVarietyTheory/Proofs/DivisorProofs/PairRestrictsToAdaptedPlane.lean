import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFixingVectorPreserves
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationTripleCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SeesawPairPlaneDescentFirstStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.UnipXStep

theorem rho_comp {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  have hs : ∀ (w w' : (κ → R) × (κ → R)) (_ : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ),
      schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
    intro w w' h φ
    funext x
    simp only [schr, Prod.fst_add, Prod.snd_add]
    rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
    congr 2
    have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
    simp only [dotProduct_add, add_dotProduct]
    linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2
  simp only [Darboux.rho]
  rw [hs, map_add]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem symp_right {n d : ℕ} (JX : Matrix (Fin n) (Fin n) E) (JW : Matrix (Fin d) (Fin d) E)
    (x : Fin d → E) (h0 : form σ JW x x = 0) (p q : Fin n → AE F E) :
    symp (R := AF F) (cA σ) (-1) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x))
      (Matrix.vecMulVec q (incV F x)) = 0 := by
  have hc : ∀ x : E, cA σ (inclR (F := F) (AF F) x) = inclR (F := F) (AF F) (σ x) := fun x => rfl
  have h : ∑ j, ∑ l, incV F x j * incM F JW j l * cA σ (incV F x l) = 0 := by
    have h1 := congrArg (inclR (F := F) (AF F)) h0
    rw [map_zero] at h1
    rw [← h1]
    simp only [form, incV, incM, Matrix.map_apply, hc, dotProduct, Matrix.mulVec, Finset.mul_sum, map_sum, map_mul,
      mul_assoc]
  have ht : hTens (cA σ) (incM F JX) (incM F JW) (Matrix.vecMulVec p (incV F x)) (Matrix.vecMulVec q (incV F x)) =
      (∑ i, ∑ k, p i * incM F JX i k * cA σ (q k)) * ∑ j, ∑ l, incV F x j * incM F JW j l * cA σ (incV F x l) := by
    simp only [hTens, Matrix.vecMulVec_apply, map_mul]
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  rw [symp, ht, h, mul_zero, mul_zero, map_zero]

theorem span_E {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} (H : Plane E n d₂)
    (hn : d₂ + 2 = n) (hxx : form σ J H.x H.x = 0) (hyy : form σ J H.y H.y = 0) (hxy : form σ J H.x H.y = 1)
    (hyx : form σ J H.y H.x = 1)
    (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0 ∧ form σ J (H.ι *ᵥ u) H.y = 0) (hinj : Function.Injective H.ι.mulVec) :
    ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hadd : ∀ a b w, form σ J (a + b) w = form σ J a w + form σ J b w := fun a b w => by
    simp only [form, add_dotProduct]
  have hsmul : ∀ (c : E) a w, form σ J (c • a) w = c * form σ J a w := fun c a w => by
    simp only [form, smul_dotProduct, smul_eq_mul]
  have hzero : ∀ w, form σ J 0 w = 0 := fun w => by simp only [form, zero_dotProduct]
  let L : ((E × E) × (Fin d₂ → E)) →ₗ[E] (Fin n → E) :=
    { toFun := fun p => p.1.1 • H.x + H.ι *ᵥ p.2 + p.1.2 • H.y
      map_add' := fun p q => by
        simp only [Prod.fst_add, Prod.snd_add, Matrix.mulVec_add, add_smul]; abel
      map_smul' := fun c p => by
        simp only [Prod.smul_fst, Prod.smul_snd, Matrix.mulVec_smul, smul_eq_mul, mul_smul, RingHom.id_apply,
          smul_add] }
  have hinjL : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    rintro ⟨⟨s, t⟩, u⟩ hp
    have hp' : s • H.x + H.ι *ᵥ u + t • H.y = 0 := hp
    have h1 := congrArg (fun v => form σ J v H.y) hp'
    have h2 := congrArg (fun v => form σ J v H.x) hp'
    simp only [hadd, hsmul, hzero, hxy, hyy, (horth u).1, (horth u).2, hxx, hyx] at h1 h2
    have hs : s = 0 := by simpa using h1
    have ht : t = 0 := by simpa using h2
    subst hs ht
    have hu : H.ι *ᵥ u = H.ι *ᵥ 0 := by simpa using hp'
    have := hinj hu
    subst this
    rfl
  have hsurj : Function.Surjective L := by
    refine (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).1 hinjL
    simp only [Module.finrank_prod, Module.finrank_self, Module.finrank_fin_fun]
    omega
  intro v
  obtain ⟨⟨⟨s, t⟩, u⟩, hp⟩ := hsurj v
  exact ⟨s, t, u, hp.symm⟩

theorem span_A {n d₂ : ℕ} (H : Plane E n d₂)
    (hE : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • H.x + H.ι *ᵥ u + t • H.y) (w : Fin n → AE F E) :
    ∃ (a b : AE F E) (z : Fin d₂ → AE F E), w = a • incV F H.x + incM F H.ι *ᵥ z + b • incV F H.y := by
  suffices h : w ∈ GlobalTheory.UnipLine.spanSet (incV F H.x) (incV F H.y) (incM F H.ι) from h
  rw [pi_eq_sum_univ w]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  obtain ⟨a, b, v, h⟩ := hE (fun j => if i = j then 1 else 0)
  refine ⟨inclR (AF F) a, inclR (AF F) b, incV F v, funext fun j => ?_⟩
  have hj := congrArg (inclR (F := F) (AF F)) (congrFun h j)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_add, map_mul, RingHom.map_mulVec] at hj
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  convert hj using 1
  · split_ifs <;> simp
  · rfl

theorem mulVec_y {n d₂ : ℕ} {J : Matrix (Fin n) (Fin n) E} (H : Plane E n d₂)
    (hE : ∀ v : Fin n → E, ∃ (s t : E) (u : Fin d₂ → E), v = s • H.x + H.ι *ᵥ u + t • H.y)
    (hxx : form σ J H.x H.x = 0) (hyx : form σ J H.y H.x = 1) (horth : ∀ u, form σ J (H.ι *ᵥ u) H.x = 0)
    (u : UA σ J) (hux : mat u *ᵥ incV F H.x = incV F H.x) :
    ∃ (z₀ : Fin d₂ → AE F E) (c : AE F E), mat u *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ z₀ + c • incV F H.x := by
  set q := J *ᵥ fun i => σ (H.x i) with hq
  set g := incV F q
  have hunit : (mat u)ᵀ * incM F J * (mat u).map (cA σ) = incM F J := u.2
  have hg : g = incM F J *ᵥ fun i => cA σ (incV F H.x i) := by
    simp only [g, hq, ← GlobalTheory.UnipLine.incM_mulVec_incV]
    congr 1
  have hcx : (mat u).map (cA σ) *ᵥ (fun i => cA σ (incV F H.x i)) = fun i => cA σ (incV F H.x i) := by
    funext i
    have := ((cA σ).toRingHom.map_mulVec (mat u) (incV F H.x) i).symm
    rw [hux] at this
    exact this
  have hinv : ∀ w, (mat u *ᵥ w) ⬝ᵥ g = w ⬝ᵥ g := by
    intro w
    have hT : (mat u)ᵀ *ᵥ g = g := by
      rw [hg, ← hcx, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hunit, hcx]
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hT, dotProduct_comm]
  have gx : incV F H.x ⬝ᵥ g = 0 := by
    rw [GlobalTheory.UnipLine.incV_dot]; exact (congrArg _ hxx).trans (map_zero _)
  have gy : incV F H.y ⬝ᵥ g = 1 := by
    rw [GlobalTheory.UnipLine.incV_dot]; exact (congrArg _ hyx).trans (map_one _)
  have hιq : H.ιᵀ *ᵥ q = 0 := by
    funext j
    have := horth (Pi.single j 1)
    simp only [form, Matrix.mulVec_single_one] at this
    rw [Matrix.mulVec_transpose, Pi.zero_apply, ← this, ← hq, dotProduct_comm]
    rfl
  have gi : ∀ z, (incM F H.ι *ᵥ z) ⬝ᵥ g = 0 := by
    intro z
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    have : (incM F H.ι)ᵀ *ᵥ g = 0 := by
      rw [show (incM F H.ι)ᵀ = incM F H.ιᵀ from Matrix.transpose_map.symm, GlobalTheory.UnipLine.incM_mulVec_incV, hιq]
      funext i; simp [incV]
    rw [this, zero_dotProduct]
  obtain ⟨a, b, z, h⟩ := span_A H hE (mat u *ᵥ incV F H.y)
  have hb : b = 1 := by
    have e1 := hinv (incV F H.y)
    rw [h, add_dotProduct, add_dotProduct, smul_dotProduct, smul_dotProduct, gx, gi, gy, smul_zero, zero_add,
      smul_eq_mul, zero_add, mul_one] at e1
    exact e1
  refine ⟨z, a, ?_⟩
  rw [h, hb, one_smul]
  abel

theorem mul_tensor {R : Type} [CommRing R] {m k l : ℕ} (A : Matrix (Fin m) (Fin k) R) (a : Fin k → R) (b : Fin l → R) :
    A * Matrix.vecMulVec a b = Matrix.vecMulVec (A *ᵥ a) b := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, Matrix.mulVec, dotProduct, Finset.sum_mul, mul_assoc]

theorem ev_step : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' →
    ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B W W₁ i₀ i₁ →
    ∀ (d₂ : ℕ) (H : Plane E n d₂), (d₂ + 2 = n ∧ form σ X.J H.x H.x = 0 ∧ form σ X.J H.y H.y = 0 ∧ form σ X.J H.x H.y = 1 ∧
        (∀ u, form σ X.J (H.ι *ᵥ u) H.x = 0 ∧ form σ X.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
    ∀ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ W) (e : Fn F n d →ₗ[ℂ] Fn F d₂ d),
      V₁.J = H.ιᵀ * X.J * H.ι.map σ → M₁.IsGood B.ψ → IsEv B M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e →
    ∀ u ∈ unip σ X H, ∃ v : Fin d₂ → AE F E, (∃ a : AE F E, mat u⁻¹ *ᵥ incV F H.y = incV F H.y + incM F H.ι *ᵥ v + a • incV F H.x) ∧
      ∀ Ψ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u, 1) Ψ)) =
        M₁.co.rho B.ψ (Matrix.vecMulVec v (incV F H'.x)) (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)) := by
  intro hKP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he u hu
  obtain ⟨hn, hxx, hyy, hxy, horth, hinj⟩ := id hH
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    have hcm : IsCMExt F E σ := hP.base.cm
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hcm.2.2.2, hcm.2.2.2, star_star])
  have hyx : form σ X.J H.y H.x = 1 := by
    have h := congrArg σ hxy
    rw [map_one] at h
    rw [← h]
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hP.herm.herm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu' : u⁻¹ ∈ GlobalTheory.UnipCT.unipSet σ X H := by
    rw [← GlobalTheory.UnipCT.unip_eq]; exact (unip σ X H).inv_mem hu
  obtain ⟨v, a, hv⟩ := mulVec_y H (span_E H hn hxx hyy hxy hyx horth hinj) hxx hyx (fun u => (horth u).1) u⁻¹ hu'.1
  refine ⟨v, ⟨a, hv⟩, fun Ψ hΨ => ?_⟩
  have hstd : IsStd B.ψ := hP.base.std
  have hsch : ∀ γ, ∀ Φ ∈ schA F (Fin n × Fin d), M.co.rho B.ψ γ Φ ∈ schA F (Fin n × Fin d) :=
    fun γ Φ hΦ => GlobalTheory.ConeMeasV.schr_mem_schA hstd _ hΦ
  have ha' : mat u⁻¹ *ᵥ incV F H.y = a • incV F H.x + incM F H.ι *ᵥ v + incV F H.y := by
    rw [hv]; abel
  have hrho : ∀ (p q : Fin n → AE F E) (φ : Fn F n d),
      M.co.rho B.ψ (Matrix.vecMulVec p (incV F H'.x)) (M.co.rho B.ψ (Matrix.vecMulVec q (incV F H'.x)) φ) =
        M.co.rho B.ψ (Matrix.vecMulVec (p + q) (incV F H'.x)) φ := fun p q φ => by
    rw [rho_comp M.co B.ψ _ _ (symp_right X.J W.J H'.x hH'.xx p q)]
    congr 1
    ext i j
    simp only [Matrix.add_apply, Matrix.vecMulVec_apply, Pi.add_apply, add_mul]
  have himpl := (IsUWeilPair.isUSplitting hP.weil).impl (u, (1 : UA σ W.J))
    (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) (incV F H'.x)) Ψ hΨ
  have hact : actAB (cA σ) (u, (1 : UA σ W.J)) (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) (incV F H'.x)) =
      Matrix.vecMulVec (incV F H.y) (incV F H'.x) := by
    show mat u * _ * (1 : Matrix (Fin d) (Fin d) (AE F E))ᵀ = _
    have h1 : mat u * mat u⁻¹ = 1 := by
      have := GlobalTheory.UnipCT.mat_inv_mul' u⁻¹
      rwa [inv_inv] at this
    rw [Matrix.transpose_one, Matrix.mul_one, mul_tensor, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  rw [hact] at himpl
  have hI : incM F (1 : Matrix (Fin d) (Fin d) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have hΨA := hsch (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ hΨ
  have hΨB := hsch (Matrix.vecMulVec (incM F H.ι *ᵥ v) (incV F H'.x)) _ hΨA
  have hsm : Matrix.vecMulVec (a • incV F H.x) (incV F H'.x) = Matrix.vecMulVec (incV F H.x) (a • incV F H'.x) := by
    ext i j
    simp only [Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  calc e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) (om (u, 1) Ψ))
      = e (om (u, 1) (M.co.rho B.ψ (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) (incV F H'.x)) Ψ)) := by
        rw [himpl]
    _ = e (M.co.rho B.ψ (Matrix.vecMulVec (mat u⁻¹ *ᵥ incV F H.y) (incV F H'.x)) Ψ) :=
        GlobalTheory.T.seesaw_pair_plane_descent_first hKP F E σ B n d X W M χX χW om r s r' s' hP d₁ W₁ H' i₀ i₁ hH' d₂ H hH V₁ M₁ e hV₁ hM₁ he u hu _
          (hsch _ Ψ hΨ)
    _ = e (M.co.rho B.ψ (Matrix.vecMulVec (a • incV F H.x) (incV F H'.x))
          (M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ v) (incV F H'.x))
            (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ))) := by
        rw [hrho, hrho, ha']
    _ = e (M.co.rho B.ψ (Matrix.vecMulVec (incM F H.ι *ᵥ v) (incV F H'.x))
          (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)) :=
        he.inv _ ⟨a • incV F H'.x, hsm⟩ _ hΨB
    _ = M₁.co.rho B.ψ (Matrix.vecMulVec v (incV F H'.x))
          (e (M.co.rho B.ψ (Matrix.vecMulVec (incV F H.y) (incV F H'.x)) Ψ)) := by
        rw [← he.Heisenberg₂ _ _ hΨA, hI, Matrix.transpose_one, Matrix.mul_one, mul_tensor]

end GlobalTheory.ThK.UnipXStep
