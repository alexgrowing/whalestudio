import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsVolData
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurePreservingOfBall
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FrameDualTupleIdealsCastAdd
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralUnipotentMiddleRowMemHomLattice
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CovolumeInverseDifferentPowMulLattice

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgAlg GlobalTheory.SgGlob GlobalTheory.SnMass GlobalTheory.SnMass.VolN
open scoped TensorProduct ENNReal nonZeroDivisors

namespace GlobalTheory.SnMass.VolN.CovH

open GlobalTheory.HomCovolume GlobalTheory.SnMass.FrameDual GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase

section Alg

variable {E : Type} [Field E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

theorem form_add_left (x x' y : Fin n → E) : form σ J (x + x') y = form σ J x y + form σ J x' y := by
  simp [form, Matrix.mulVec_add, dotProduct_add]

theorem form_add_right (x y y' : Fin n → E) : form σ J x (y + y') = form σ J x y + form σ J x y' := by
  have h : (fun i => σ ((y + y') i)) = (fun i => σ (y i)) + fun i => σ (y' i) := by
    ext i; simp
  rw [form, h, add_dotProduct]; rfl

theorem form_zero_right (x : Fin n → E) : form σ J x 0 = 0 := by
  simp [form]

theorem exists_basis {r m : ℕ} (hn : n = 2 * r + m) (e g : Fin r → Fin n → E)
    (hge : ∀ c d, form σ J (g c) (e d) = if c = d then 1 else 0)
    (heg : ∀ c d, form σ J (e c) (g d) = if c = d then 1 else 0)
    (hee : ∀ c d, form σ J (e c) (e d) = 0) (hgg : ∀ c d, form σ J (g c) (g d) = 0) :
    ∃ (Y : Matrix (Fin n) (Fin m) E) (Ly : Matrix (Fin m) (Fin n) E), Ly * Y = 1 ∧
      ∀ t, (∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0) ↔ ∃ u, Y *ᵥ u = t := by
  classical
  let Φ : (Fin n → E) →ₗ[E] (Fin r → E) × (Fin r → E) :=
    { toFun := fun t => (fun b => form σ J t (e b), fun b => form σ J t (g b))
      map_add' := fun x y => by
        ext b <;> simp [form_add_left]
      map_smul' := fun c x => by
        ext b <;> simp [form_smul_left'] }
  have hs : Function.Surjective Φ := by
    rintro ⟨a, b⟩
    refine ⟨∑ c, a c • g c + ∑ c, b c • e c, ?_⟩
    refine Prod.ext (funext fun d => ?_) (funext fun d => ?_)
    · change form σ J _ (e d) = a d
      simp [form_add_left, form_sum_left', form_smul_left', hge, hee]
    · change form σ J _ (g d) = b d
      simp [form_add_left, form_sum_left', form_smul_left', heg, hgg]
  have hk : Module.finrank E (LinearMap.ker Φ) = m := by
    have h := LinearMap.finrank_range_add_finrank_ker Φ
    rw [LinearMap.range_eq_top.2 hs, finrank_top] at h
    simp only [Module.finrank_prod, Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h
    omega
  let ee : (Fin m → E) ≃ₗ[E] LinearMap.ker Φ := LinearEquiv.ofFinrankEq _ _ (by simp [hk])
  let ι : (Fin m → E) →ₗ[E] (Fin n → E) := (LinearMap.ker Φ).subtype ∘ₗ ee.toLinearMap
  have hι : LinearMap.ker ι = ⊥ := by
    refine LinearMap.ker_eq_bot.2 fun x y h => ee.injective (Subtype.ext h)
  obtain ⟨gg, hgg'⟩ := ι.exists_leftInverse_of_injective hι
  refine ⟨LinearMap.toMatrix' ι, LinearMap.toMatrix' gg, ?_, fun t => ?_⟩
  · rw [← LinearMap.toMatrix'_comp, hgg', LinearMap.toMatrix'_id]
  · constructor
    · intro h
      have ht : t ∈ LinearMap.ker Φ := by
        refine Prod.ext (funext fun b => (h b).1) (funext fun b => (h b).2)
      refine ⟨ee.symm ⟨t, ht⟩, ?_⟩
      rw [LinearMap.toMatrix'_mulVec]
      simp [ι]
    · rintro ⟨u, rfl⟩ b
      rw [LinearMap.toMatrix'_mulVec]
      have h : Φ (ι u) = 0 := (ee u).2
      exact ⟨congrFun (congrArg Prod.fst h) b, congrFun (congrArg Prod.snd h) b⟩

theorem form_projF (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {r : ℕ} (e g : Fin r → Fin n → E)
    {t : Fin n → E} (ht : ∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0) (u : Fin n → E) :
    form σ J (projF σ J e g u) t = form σ J u t := by
  have h1 : ∀ b, form σ J (e b) t = 0 := fun b => by
    rw [← form_conj σ J hσ hJ, (ht b).1, map_zero]
  have h2 : ∀ b, form σ J (g b) t = 0 := fun b => by
    rw [← form_conj σ J hσ hJ, (ht b).2, map_zero]
  simp [projF, form_sub_left', form_sum_left', form_smul_left', h1, h2]

theorem eq_zero_of_orth (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {r : ℕ}
    (e g : Fin r → Fin n → E)
    (hee : ∀ c d, form σ J (e c) (e d) = 0) (hgg : ∀ c d, form σ J (g c) (g d) = 0)
    (hge : ∀ c d, form σ J (g c) (e d) = if c = d then 1 else 0)
    (heg : ∀ c d, form σ J (e c) (g d) = if c = d then 1 else 0)
    {t : Fin n → E} (ht : ∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0)
    (h : ∀ x, (∀ b, form σ J x (e b) = 0 ∧ form σ J x (g b) = 0) → form σ J x t = 0) : t = 0 := by
  have h0 : ∀ u, form σ J u t = 0 := fun u => by
    rw [← form_projF σ J hσ hJ e g ht u]
    exact h _ (projF_orth σ J e g hee hgg hge heg u)
  have h1 : (fun i => σ (t i)) ᵥ* J = 0 := by
    ext j
    have := h0 (Pi.single j 1)
    simpa [form, Matrix.mulVec_single_one, dotProduct, Matrix.vecMul, Matrix.col_apply] using this
  have h2 : (fun i => σ (t i)) = 0 := by
    have hu : IsUnit J.det := Ne.isUnit hdet
    have := congrArg (· ᵥ* J⁻¹) h1
    simpa [Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv _ hu] using this
  ext i
  have := congrFun h2 i
  simpa using this

theorem form_mulVec_left {m : ℕ} (Y : Matrix (Fin n) (Fin m) E) (y : Fin m → E) (t : Fin n → E) :
    form σ J (Y *ᵥ y) t = ∑ j, y j * form σ J (fun i => Y i j) t := by
  have h : Y *ᵥ y = ∑ j, y j • fun i => Y i j := by
    ext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [h, form_sum_left']
  exact Finset.sum_congr rfl fun j _ => form_smul_left' σ J _ _ _

theorem exists_solve (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) {r m : ℕ}
    (e g : Fin r → Fin n → E)
    (hee : ∀ c d, form σ J (e c) (e d) = 0) (hgg : ∀ c d, form σ J (g c) (g d) = 0)
    (hge : ∀ c d, form σ J (g c) (e d) = if c = d then 1 else 0)
    (heg : ∀ c d, form σ J (e c) (g d) = if c = d then 1 else 0)
    {Y : Matrix (Fin n) (Fin m) E} {Ly : Matrix (Fin m) (Fin n) E} (hY : Ly * Y = 1)
    (hW : ∀ t, (∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0) ↔ ∃ u, Y *ᵥ u = t) (Tv : Fin m → E) :
    ∃ u, ∀ j, form σ J (fun i => Y i j) (Y *ᵥ u) = Tv j := by
  let B : (Fin m → E) →ₗ[E] (Fin m → E) :=
    { toFun := fun u j => form σ J (Y *ᵥ u) (fun i => Y i j)
      map_add' := fun x y => by
        ext j; simp [Matrix.mulVec_add, form_add_left]
      map_smul' := fun c x => by
        ext j; simp [Matrix.mulVec_smul, form_smul_left'] }
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun u hu => ?_
    have ht := (hW (Y *ᵥ u)).2 ⟨u, rfl⟩
    have h0 : ∀ j, form σ J (fun i => Y i j) (Y *ᵥ u) = 0 := fun j => by
      rw [← form_conj σ J hσ hJ]
      have : form σ J (Y *ᵥ u) (fun i => Y i j) = 0 := congrFun hu j
      rw [this, map_zero]
    have h1 : Y *ᵥ u = 0 := by
      refine eq_zero_of_orth σ J hσ hJ hdet e g hee hgg hge heg ht fun x hx => ?_
      obtain ⟨y, rfl⟩ := (hW x).1 hx
      rw [form_mulVec_left]
      simp [h0]
    have := congrArg (Ly *ᵥ ·) h1
    simpa [Matrix.mulVec_mulVec, hY] using this
  obtain ⟨u, hu⟩ := LinearMap.injective_iff_surjective.1 hinj (fun j => σ (Tv j))
  refine ⟨u, fun j => ?_⟩
  rw [← form_conj σ J hσ hJ]
  have : form σ J (Y *ᵥ u) (fun i => Y i j) = σ (Tv j) := congrFun hu j
  rw [this, hσ]

end Alg

section Lat

variable {E : Type} [Field E] [NumberField E] {n : ℕ} (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E)

theorem exists_smul_mem {Λ : Submodule (𝓞 E) (Fin n → E)} (hSD : GlobalTheory.SgGlob.SelfDual σ J Λ) (v : Fin n → E) :
    ∃ d : 𝓞 E, d ≠ 0 ∧ ((d : E)) • v ∈ Λ := by
  classical
  obtain ⟨S, hS⟩ := hSD.1
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (𝓞 E)⁰ S (fun w => form σ J v w)
  refine ⟨b, nonZeroDivisors.ne_zero b.2, (hSD.2 _).2 fun w hw => ?_⟩
  rw [← hS] at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy⟩ := hb x hx
    rw [form_smul_left']
    refine ⟨y, ?_⟩
    rw [hy]
    rfl
  | zero => exact ⟨0, by simp [form_zero_right]⟩
  | add x y _ _ hx hy =>
    rw [form_add_right]
    exact add_mem hx hy
  | smul a x _ hx =>
    have : a • x = ((a : 𝓞 E) : E) • x := (algebraMap_smul E a x).symm
    rw [this, form_smul_right']
    exact mul_mem ⟨RingOfIntegers.mapRingHom σ a, rfl⟩ hx

def coordLat {m : ℕ} (Λ : Submodule (𝓞 E) (Fin n → E)) (Y : Matrix (Fin n) (Fin m) E) :
    Submodule (𝓞 E) (Fin m → E) := Λ.comap (Y.mulVecLin.restrictScalars (𝓞 E))

theorem mem_coordLat {m : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} {Y : Matrix (Fin n) (Fin m) E} {u : Fin m → E} :
    u ∈ coordLat Λ Y ↔ Y *ᵥ u ∈ Λ := Iff.rfl

theorem isLattice_coordLat {m : ℕ} {Λ : Submodule (𝓞 E) (Fin n → E)} (hSD : GlobalTheory.SgGlob.SelfDual σ J Λ)
    {Y : Matrix (Fin n) (Fin m) E} {Ly : Matrix (Fin m) (Fin n) E} (hY : Ly * Y = 1) :
    Submodule.IsLattice E (coordLat Λ Y) := by
  have hinj : Function.Injective (Y.mulVecLin.restrictScalars (𝓞 E)) := fun x y h => by
    have h' : Y *ᵥ x = Y *ᵥ y := h
    have := congrArg (Ly *ᵥ ·) h'
    simpa [Matrix.mulVec_mulVec, hY] using this
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective _ hinj (Submodule.FG.of_le hSD.1 ?_)
    rintro _ ⟨u, hu, rfl⟩
    exact hu
  · rw [eq_top_iff]
    intro u _
    obtain ⟨d, hd, hm⟩ := exists_smul_mem σ J hSD (Y *ᵥ u)
    have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
    have h1 : ((d : E)) • u ∈ coordLat Λ Y := by
      rw [mem_coordLat, Matrix.mulVec_smul]
      exact hm
    have : u = (d : E)⁻¹ • ((d : E) • u) := by rw [smul_smul, inv_mul_cancel₀ hd', one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

theorem smul_mem_iff (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j)
    {Λ : Submodule (𝓞 E) (Fin n → E)} (hSD : GlobalTheory.SgGlob.SelfDual σ J Λ) {r : ℕ} (e g : Fin r → Fin n → E)
    (hee : ∀ c d, form σ J (e c) (e d) = 0) (hgg : ∀ c d, form σ J (g c) (g d) = 0)
    (hge : ∀ c d, form σ J (g c) (e d) = if c = d then 1 else 0)
    (heg : ∀ c d, form σ J (e c) (g d) = if c = d then 1 else 0)
    (𝔞 : Fin r → FractionalIdeal (𝓞 E)⁰ E) (h0 : ∀ c, 𝔞 c ≠ 0) (hs : ∀ c, Stab σ (𝔞 c))
    (he : ∀ c, ∀ x ∈ 𝔞 c, x • e c ∈ Λ) (hg : ∀ c, ∀ x ∈ (𝔞 c)⁻¹, x • g c ∈ Λ)
    {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (hIs : Stab σ I) {t : Fin n → E}
    (ht : ∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0) :
    (∀ c ∈ I⁻¹, c • t ∈ Λ) ↔
      ∀ x ∈ Λ, (∀ b, form σ J x (e b) = 0 ∧ form σ J x (g b) = 0) → form σ J x t ∈ I := by
  have hΛ : ∀ v ∈ Λ, ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range :=
    fun v hv w hw => (hSD.2 v).1 hv w hw
  constructor
  · intro h x hx _
    have := form_mem_inv σ J hσ hΛ (inv_ne_zero hI) (hIs.inv hσ hI) h hx
    rwa [inv_inv] at this
  · intro h c hc
    refine (hSD.2 _).2 fun w hw => ?_
    have h1 := h _ (projF_mem σ J hσ hΛ 𝔞 h0 hs e g he hg hw) (projF_orth σ J e g hee hgg hge heg w)
    rw [form_projF σ J hσ hJ e g ht] at h1
    rw [form_smul_left', ← form_conj σ J hσ hJ]
    have h2 := FractionalIdeal.mul_mem_mul hc (hIs _ h1)
    rw [inv_mul_cancel₀ hI] at h2
    exact (FractionalIdeal.mem_one_iff _).1 h2 |>.elim fun d hd => ⟨d, hd⟩

end Lat

section Model

theorem Hpk_eI_row (k r : ℕ) (a : Fin r) (j : Fin (2 * r + k + 1)) :
    Hpk k r (eI k r a) j = if j = esI k r a then 1 else 0 := by
  have ha := a.isLt
  have hj := j.isLt
  simp only [Hpk, esI, eI, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem mulVec_eI (k r : ℕ) (a : Fin r) (x : Fin (2 * r + k + 1) → ℂ) :
    x (esI k r a) = (Hpk k r *ᵥ x) (eI k r a) := by
  simp [Matrix.mulVec, dotProduct, Hpk_eI_row]

def eps (k : ℕ) (l : Fin (k + 1)) : ℂ := if l.val = k then -1 else 1

theorem eps_mul_self (k : ℕ) (l : Fin (k + 1)) : eps k l * eps k l = 1 := by
  unfold eps; split_ifs <;> simp

theorem norm_eps (k : ℕ) (l : Fin (k + 1)) : ‖eps k l‖ = 1 := by
  unfold eps; split_ifs <;> simp

theorem star_eps (k : ℕ) (l : Fin (k + 1)) : star (eps k l) = eps k l := by
  unfold eps; split_ifs <;> simp

theorem Hpk_col_wI (k r : ℕ) (l : Fin (k + 1)) (j : Fin (2 * r + k + 1)) :
    Hpk k r j (wI k r l) = if j = wI k r l then eps k l else 0 := by
  have hl := l.isLt
  have hj := j.isLt
  simp only [Hpk, wI, eps, Fin.ext_iff]
  split_ifs <;> first | rfl | (exfalso; omega)

theorem herm_bvec_wI (k r : ℕ) (l : Fin (k + 1)) (v : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) (bvec (wI k r l)) v = star (v (wI k r l)) * eps k l := by
  simp [herm, bvec, dotProduct, Matrix.mulVec_single_one, Hpk_col_wI]

theorem idx_cases' (k r : ℕ) (i : Fin (2 * r + k + 1)) :
    (∃ a, i = eI k r a) ∨ (∃ l, i = wI k r l) ∨ ∃ a, i = esI k r a := by
  have hi := i.isLt
  by_cases h1 : i.val < r
  · exact Or.inl ⟨⟨i.val, h1⟩, Fin.ext rfl⟩
  by_cases h2 : i.val ≤ r + k
  · exact Or.inr (Or.inl ⟨⟨i.val - r, by omega⟩, Fin.ext (by simp only [wI]; omega)⟩)
  · exact Or.inr (Or.inr ⟨⟨2 * r + k - i.val, by omega⟩, Fin.ext (by simp only [esI]; omega)⟩)

theorem eI_ne_wI' (k r : ℕ) (a : Fin r) (l : Fin (k + 1)) : eI k r a ≠ wI k r l := by
  intro h
  have := congrArg Fin.val h
  have ha := a.isLt
  simp only [eI, wI] at this
  omega

theorem esI_ne_wI' (k r : ℕ) (a : Fin r) (l : Fin (k + 1)) : esI k r a ≠ wI k r l := by
  intro h
  have := congrArg Fin.val h
  have ha := a.isLt
  have hl := l.isLt
  simp only [esI, wI] at this
  omega

theorem wI_injective (k r : ℕ) : Function.Injective (wI k r) := fun a b h => by
  have := congrArg Fin.val h
  simp only [wI] at this
  exact Fin.ext (by omega)

theorem mid_expand {k r : ℕ} (x : Fin (2 * r + k + 1) → ℂ) (h1 : ∀ a, x (eI k r a) = 0)
    (h2 : ∀ a, x (esI k r a) = 0) : x = ∑ l, x (wI k r l) • bvec (wI k r l) := by
  ext i
  simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
  rcases idx_cases' k r i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩
  · simp [h1, eI_ne_wI']
  · simp [(wI_injective k r).eq_iff]
  · simp [h2, esI_ne_wI']

theorem herm_smul_left' {n : ℕ} (H : Matrix (Fin n) (Fin n) ℂ) (c : ℂ) (x y : Fin n → ℂ) :
    herm H (c • x) y = c * herm H x y := by
  simp [herm, Matrix.mulVec_smul, dotProduct_smul]

theorem herm_sum_left' {n : ℕ} {ι : Type} (H : Matrix (Fin n) (Fin n) ℂ) (S : Finset ι) (g : ι → Fin n → ℂ)
    (y : Fin n → ℂ) : herm H (∑ c ∈ S, g c) y = ∑ c ∈ S, herm H (g c) y := by
  simp [herm, Matrix.mulVec_sum, dotProduct_sum]

end Model

section Cx

variable {E : Type} [Field E] {n : ℕ}

theorem herm_map_mv (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (φ : E →+* ℂ) (hφ : ∀ x, φ (σ x) = star (φ x))
    (x y : Fin n → E) : herm (J.map φ) (mv φ x) (mv φ y) = φ (form σ J x y) := by
  simp [herm, form, dotProduct, Matrix.mulVec, mv, map_sum, hφ]

variable {k r : ℕ} (σ : E →+* E) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (φ : E →+* ℂ)
  (B : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)

theorem orth_coords (hφ : ∀ x, φ (σ x) = star (φ x)) (hB : Bᴴ * Hpk k r * B = J.map φ)
    {e g : Fin r → Fin (2 * r + k + 1) → E} {s : Fin r → ℝ} (hs : ∀ a, 0 < s a)
    (he : ∀ a, B *ᵥ mv φ (e a) = (s a : ℂ) • bvec (eI k r a))
    (hg : ∀ a, B *ᵥ mv φ (g a) = ((s a)⁻¹ : ℂ) • bvec (esI k r a)) {x : Fin (2 * r + k + 1) → E}
    (hx : ∀ b, form σ J x (e b) = 0 ∧ form σ J x (g b) = 0) (a : Fin r) :
    (B *ᵥ mv φ x) (eI k r a) = 0 ∧ (B *ᵥ mv φ x) (esI k r a) = 0 := by
  have hs' : (s a : ℂ) ≠ 0 := by exact_mod_cast (hs a).ne'
  constructor
  · have h := herm_model hB (mv φ x) (mv φ (g a))
    rw [herm_map_mv σ J φ hφ, (hx a).2, map_zero, hg, herm_smul_right', herm_bvec_right, ← mulVec_esI] at h
    simpa [hs'] using h
  · have h := herm_model hB (mv φ x) (mv φ (e a))
    rw [herm_map_mv σ J φ hφ, (hx a).1, map_zero, he, herm_smul_right', herm_bvec_right, ← mulVec_eI] at h
    simpa [hs'] using h

def Cm {m : ℕ} (Y : Matrix (Fin (2 * r + k + 1)) (Fin m) E) : Matrix (Fin (k + 1)) (Fin m) ℂ :=
  Matrix.of fun l j => (B *ᵥ mv φ fun i => Y i j) (wI k r l)

theorem B_map_mulVec {m : ℕ} (Y : Matrix (Fin (2 * r + k + 1)) (Fin m) E) (c : Fin m → ℂ)
    (i : Fin (2 * r + k + 1)) :
    (B *ᵥ (Y.map φ *ᵥ c)) i = ∑ j, c j * (B *ᵥ mv φ fun i => Y i j) i := by
  simp only [Matrix.mulVec, dotProduct, mv, Matrix.map_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem Cm_mulVec {m : ℕ} (Y : Matrix (Fin (2 * r + k + 1)) (Fin m) E) (c : Fin m → ℂ) (l : Fin (k + 1)) :
    (Cm φ B Y *ᵥ c) l = (B *ᵥ (Y.map φ *ᵥ c)) (wI k r l) := by
  rw [B_map_mulVec]
  simp [Cm, Matrix.mulVec, dotProduct, mul_comm]

theorem mv_mulVec {m : ℕ} (Y : Matrix (Fin (2 * r + k + 1)) (Fin m) E) (u : Fin m → E) :
    mv φ (Y *ᵥ u) = Y.map φ *ᵥ fun j => φ (u j) := by
  ext i
  simp [mv, Matrix.mulVec, dotProduct, map_sum]

theorem isUnit_det_Cm (hφ : ∀ x, φ (σ x) = star (φ x)) (hB : Bᴴ * Hpk k r * B = J.map φ) (hBu : IsUnit B.det)
    {e g : Fin r → Fin (2 * r + k + 1) → E} {s : Fin r → ℝ} (hs : ∀ a, 0 < s a)
    (he : ∀ a, B *ᵥ mv φ (e a) = (s a : ℂ) • bvec (eI k r a))
    (hg : ∀ a, B *ᵥ mv φ (g a) = ((s a)⁻¹ : ℂ) • bvec (esI k r a))
    {Y : Matrix (Fin (2 * r + k + 1)) (Fin (k + 1)) E} {Ly : Matrix (Fin (k + 1)) (Fin (2 * r + k + 1)) E}
    (hY : Ly * Y = 1)
    (hW : ∀ j b, form σ J (fun i => Y i j) (e b) = 0 ∧ form σ J (fun i => Y i j) (g b) = 0) :
    IsUnit (Cm φ B Y).det := by
  rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.mulVec_injective_iff_isUnit]
  have hker : ∀ c, Cm φ B Y *ᵥ c = 0 → c = 0 := by
    intro c hc
    have h1 : B *ᵥ (Y.map φ *ᵥ c) = 0 := by
      ext i
      rcases idx_cases' k r i with ⟨a, rfl⟩ | ⟨l, rfl⟩ | ⟨a, rfl⟩
      · rw [B_map_mulVec]
        simp [(orth_coords σ J φ B hφ hB hs he hg (hW _) a).1]
      · rw [← Cm_mulVec, hc]; rfl
      · rw [B_map_mulVec]
        simp [(orth_coords σ J φ B hφ hB hs he hg (hW _) a).2]
    have h2 : Y.map φ *ᵥ c = 0 := by
      have := congrArg (B⁻¹ *ᵥ ·) h1
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul_cancel_left _ _ hBu] using this
    have h3 : Ly.map φ * Y.map φ = 1 := by
      rw [← Matrix.map_mul, hY, Matrix.map_one _ (map_zero _) (map_one _)]
    have := congrArg (Ly.map φ *ᵥ ·) h2
    simpa [Matrix.mulVec_mulVec, h3] using this
  intro x y hxy
  have : x - y = 0 := hker _ (by rw [Matrix.mulVec_sub]; exact sub_eq_zero.2 hxy)
  exact sub_eq_zero.1 this

theorem pairing_eq (hφ : ∀ x, φ (σ x) = star (φ x)) (hB : Bᴴ * Hpk k r * B = J.map φ)
    {e g : Fin r → Fin (2 * r + k + 1) → E} {s : Fin r → ℝ} (hs : ∀ a, 0 < s a)
    (he : ∀ a, B *ᵥ mv φ (e a) = (s a : ℂ) • bvec (eI k r a))
    (hg : ∀ a, B *ᵥ mv φ (g a) = ((s a)⁻¹ : ℂ) • bvec (esI k r a)) {m : ℕ}
    {Y : Matrix (Fin (2 * r + k + 1)) (Fin m) E}
    (hW : ∀ j b, form σ J (fun i => Y i j) (e b) = 0 ∧ form σ J (fun i => Y i j) (g b) = 0)
    (t : Fin (2 * r + k + 1) → E) (j : Fin m) :
    φ (form σ J (fun i => Y i j) t) =
      ∑ l, herm (Hpk k r) (bvec (wI k r l)) (B *ᵥ mv φ t) * Cm φ B Y l j := by
  rw [← herm_map_mv σ J φ hφ, ← herm_model hB]
  have hx := mid_expand (B *ᵥ mv φ fun i => Y i j) (fun a => (orth_coords σ J φ B hφ hB hs he hg (hW j) a).1)
    (fun a => (orth_coords σ J φ B hφ hB hs he hg (hW j) a).2)
  conv_lhs => rw [hx]
  rw [herm_sum_left']
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [herm_smul_left', mul_comm]
  rfl

end Cx

section Core

variable (E : Type) [Field E] [NumberField E]

attribute [local instance] haar_two haar_three

def lineLat (I : FractionalIdeal (𝓞 E)⁰ E) : Submodule (𝓞 E) (Fin 1 → E) :=
  (I : Submodule (𝓞 E) E).comap (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0)

theorem mem_lineLat {I : FractionalIdeal (𝓞 E)⁰ E} {y : Fin 1 → E} : y ∈ lineLat E I ↔ y 0 ∈ I := Iff.rfl

theorem isLattice_lineLat {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) : Submodule.IsLattice E (lineLat E I) := by
  let ee : E ≃ₗ[𝓞 E] (Fin 1 → E) := (LinearEquiv.funUnique (Fin 1) (𝓞 E) E).symm
  have hm : lineLat E I = (I : Submodule (𝓞 E) E).map ee.toLinearMap := by
    ext y
    rw [mem_lineLat]
    constructor
    · intro h
      refine ⟨y 0, h, ?_⟩
      ext i
      rw [Subsingleton.elim i 0]
      rfl
    · rintro ⟨x, hx, rfl⟩
      exact hx
  have hfg : (I : Submodule (𝓞 E) E).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl I
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ I, x ≠ 0 := by
    by_contra h
    push_neg at h
    exact hI (FractionalIdeal.ext fun y => ⟨fun hy => (FractionalIdeal.mem_zero_iff _).2 (h y hy),
      fun hy => by rw [(FractionalIdeal.mem_zero_iff _).1 hy]; exact FractionalIdeal.zero_mem _⟩)
  refine ⟨hm ▸ hfg.map _, ?_⟩
  rw [eq_top_iff]
  intro y _
  have h1 : (fun _ : Fin 1 => x) ∈ lineLat E I := hx
  have : y = (y 0 / x) • fun _ : Fin 1 => x := by
    ext i
    rw [Subsingleton.elim i 0]
    simp [hx0]
  rw [this]
  exact Submodule.smul_mem _ _ (Submodule.subset_span h1)

def gS (c : ℝ) : MatInf E 1 := fun _ _ _ => ((c : ℂ))⁻¹

def gC {m : ℕ} (C : InfinitePlace E → Matrix (Fin m) (Fin m) ℂ) : MatInf E m := fun w => ((C w)⁻¹ : Matrix (Fin m) (Fin m) ℂ)

theorem inv_gS {c : ℝ} (hc : 0 < c) (w : InfinitePlace E) :
    (Matrix.of (gS E c w))⁻¹ = (c : ℂ) • (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  rw [Subsingleton.elim i 0, Subsingleton.elim j 0]
  simp [gS, Matrix.mul_apply, hc']

theorem detNorm_gS {c : ℝ} (hc : 0 < c) :
    detNorm E 1 (gS E c) = (c ^ (2 * Fintype.card (InfinitePlace E)))⁻¹ := by
  simp [detNorm, gS, Matrix.det_fin_one, Finset.prod_const, Finset.card_univ, ← pow_mul, abs_of_pos hc, mul_comm]

theorem detNorm_gC {m : ℕ} {C : InfinitePlace E → Matrix (Fin m) (Fin m) ℂ} (hC : ∀ w, IsUnit (C w).det) :
    0 < detNorm E m (gC E C) := by
  refine Finset.prod_pos fun w _ => pow_pos (norm_pos_iff.2 ?_) _
  have : (Matrix.of (gC E C w)) = (C w)⁻¹ := rfl
  rw [this, Matrix.det_nonsing_inv]
  exact (((hC w).ringInverse).ne_zero)

theorem covAt_line (hE : IsTotallyComplex E) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {c : ℝ} (hc : 0 < c) :
    covAt E 1 (latAt E 1 (lineLat E I) (gS E c)) =
      (FractionalIdeal.absNorm I : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E)) := by
  have hg : 0 < detNorm E 1 (gS E c) := by
    rw [detNorm_gS E hc]; positivity
  rw [covAt_latAt E hE (lineLat E I) 1 (fun _ => I) (by simp) (fun _ => hI) (fun y => ?_) (gS E c) hg]
  · have h1 : ∏ w : InfinitePlace E, ‖(((1 : Matrix (Fin 1) (Fin 1) E).map w.embedding) * Matrix.of (gS E c w)).det‖ ^ 2 =
        detNorm E 1 (gS E c) := by
      refine Finset.prod_congr rfl fun w _ => ?_
      rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
    rw [h1, detNorm_gS E hc]
    simp
  · simp [mem_lineLat, Fin.forall_fin_one]

theorem exists_core (hE : IsTotallyComplex E) {m : ℕ} (Λ' : Submodule (𝓞 E) (Fin m → E))
    (hΛ' : Submodule.IsLattice E Λ') (C : InfinitePlace E → Matrix (Fin m) (Fin m) ℂ)
    (hC : ∀ w, IsUnit (C w).det) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) {c : ℝ} (hc : 0 < c) :
    ∃ L : Submodule ℤ (InfinitePlace E → Fin m → ℂ),
      (∀ z, z ∈ L ↔ ∃ T : Matrix (Fin 1) (Fin m) E, (∀ y ∈ Λ', (T *ᵥ y) 0 ∈ I) ∧
        ∀ w l, z w l = (c : ℂ) * (T.map w.embedding * (C w)⁻¹) 0 l) ∧
      HasCov volume L (((FractionalIdeal.absNorm I : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
          c ^ (2 * Fintype.card (InfinitePlace E))) ^ m *
        (Formalism.HermitianLatticesTheory.vInv E ^ (Formalism.HermitianLatticesTheory.fDeg E * m) / covAt E m (latAt E m Λ' (gC E C)))) := by
  have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  let L₃ : Submodule ℤ (InfinitePlace E → Fin 1 → Fin m → ℂ) :=
    { carrier := {z | ∃ T : Matrix (Fin 1) (Fin m) E, (∀ y ∈ Λ', T *ᵥ y ∈ lineLat E I) ∧
        ∀ w, Matrix.of (z w) = (Matrix.of (gS E c w))⁻¹ * T.map w.embedding * Matrix.of (gC E C w)}
      add_mem' := by
        rintro a b ⟨T, hT, h⟩ ⟨T', hT', h'⟩
        refine ⟨T + T', fun y hy => ?_, fun w => ?_⟩
        · rw [Matrix.add_mulVec]
          exact Submodule.add_mem _ (hT y hy) (hT' y hy)
        · have e : (T + T').map w.embedding = T.map w.embedding + T'.map w.embedding := by
            ext i j; simp
          rw [e, Matrix.mul_add, Matrix.add_mul, ← h, ← h']
          rfl
      zero_mem' := ⟨0, fun y _ => by simp [Submodule.zero_mem], fun w => by
        have e : (0 : Matrix (Fin 1) (Fin m) E).map w.embedding = 0 := by
          ext i j; simp
        rw [e, Matrix.mul_zero, Matrix.zero_mul]
        rfl⟩
      smul_mem' := by
        rintro n a ⟨T, hT, h⟩
        refine ⟨n • T, fun y hy => ?_, fun w => ?_⟩
        · rw [Matrix.smul_mulVec]
          exact zsmul_mem (hT y hy) n
        · have e : (n • T).map w.embedding = n • T.map w.embedding := by
            ext i j; simp
          rw [e, Matrix.mul_smul, Matrix.smul_mul, ← h]
          rfl }
  have hg : 0 < detNorm E 1 (gS E c) := by
    rw [detNorm_gS E hc]; positivity
  obtain ⟨hd, hz, hcov⟩ := homCovolume E hE 1 m (lineLat E I) Λ' (isLattice_lineLat E hI) hΛ' (gS E c) (gC E C)
    hg (detNorm_gC E hC) L₃ (fun z => Iff.rfl)
  let e₀ : (InfinitePlace E → Fin m → ℂ) ≃ₗ[ℝ] (InfinitePlace E → Fin 1 → Fin m → ℂ) :=
    { toFun := fun z w _ l => z w l, invFun := fun z w l => z w 0 l, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl, left_inv := fun _ => rfl,
      right_inv := fun z => by
        ext w i l
        rw [Subsingleton.elim i 0] }
  have hmp : MeasurePreserving e₀.toContinuousLinearEquiv volume volume := by
    refine measurePreserving_of_ball _ _ _ (fun x => ?_) ?_
    · simp only [pi_norm_le_iff_of_nonneg zero_le_one]
      exact ⟨fun h w l => h w 0 l, fun h w _ l => h w l⟩
    · simp [volume_pi_closedBall _ zero_le_one, ← pow_mul, mul_comm]
  refine ⟨L₃.comap (e₀.toLinearMap.restrictScalars ℤ), fun z => ?_, ?_⟩
  · have hmem : z ∈ L₃.comap (e₀.toLinearMap.restrictScalars ℤ) ↔
        ∃ T : Matrix (Fin 1) (Fin m) E, (∀ y ∈ Λ', T *ᵥ y ∈ lineLat E I) ∧
        ∀ w, Matrix.of (e₀ z w) = (Matrix.of (gS E c w))⁻¹ * T.map w.embedding * Matrix.of (gC E C w) := Iff.rfl
    rw [hmem]
    refine exists_congr fun T => and_congr Iff.rfl ⟨fun h w l => ?_, fun h w => ?_⟩
    · have h1 := congrFun (congrFun (h w) 0) l
      rw [inv_gS E hc, Matrix.smul_mul, Matrix.one_mul] at h1
      rw [Matrix.smul_mul] at h1
      exact h1
    · rw [inv_gS E hc, Matrix.smul_mul, Matrix.one_mul, Matrix.smul_mul]
      ext i l
      rw [Subsingleton.elim i 0]
      exact h w l
  · have h := HasCov.of_measurePreserving (L := L₃.comap (e₀.toLinearMap.restrictScalars ℤ)) (L' := L₃)
      e₀.toContinuousLinearEquiv hmp (fun _ => Iff.rfl) ⟨hd, hz, hcov⟩
    rw [covAt_line E hE hI hc, pow_one] at h
    exact h

end Core

theorem hasDom_of_hasCov {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] {μ : Measure V} [μ.IsAddHaarMeasure] {L : Submodule ℤ V} {S : Set V}
    (hS : ∀ z, z ∈ L ↔ z ∈ S) {c : ℝ} (hc : HasCov μ L c) : HasDom μ S (ENNReal.ofReal c) := by
  obtain ⟨_, _, h⟩ := hc
  refine ⟨GlobalTheory.latticeDomain L, GlobalTheory.measurableSet_latticeDomain L, fun v => ?_, ?_⟩
  · obtain ⟨z, hz, hu⟩ := GlobalTheory.existsUnique_add_mem_latticeDomain L v
    refine ⟨z, ⟨(hS _).1 z.2, hz⟩, ?_⟩
    rintro l ⟨hl, hlD⟩
    exact congrArg Subtype.val (hu ⟨l, (hS l).2 hl⟩ hlD)
  · rw [GlobalTheory.measure_latticeDomain, h]

section Main

variable {E : Type} [Field E] [NumberField E]

attribute [local instance] haar_two

def signConj (E : Type) [Field E] [NumberField E] (k : ℕ) :
    (InfinitePlace E → Fin (k + 1) → ℂ) ≃L[ℝ] (InfinitePlace E → Fin (k + 1) → ℂ) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun x w l => eps k l * star (x w l)
      invFun := fun x w l => eps k l * star (x w l)
      map_add' := fun x y => by
        ext w l; simp [mul_add]
      map_smul' := fun c x => by
        ext w l; simp; ring
      left_inv := fun x => by
        ext w l
        simp only [star_mul', star_star, star_eps, ← mul_assoc, eps_mul_self, one_mul]
      right_inv := fun x => by
        ext w l
        simp only [star_mul', star_star, star_eps, ← mul_assoc, eps_mul_self, one_mul] }

theorem signConj_apply (k : ℕ) (x : InfinitePlace E → Fin (k + 1) → ℂ) (w : InfinitePlace E) (l : Fin (k + 1)) :
    signConj E k x w l = eps k l * star (x w l) := rfl

theorem signConj_measurePreserving (k : ℕ) : MeasurePreserving (signConj E k) volume volume := by
  refine measurePreserving_of_ball _ _ _ (fun x => ?_) rfl
  simp only [pi_norm_le_iff_of_nonneg zero_le_one, signConj_apply, norm_mul, norm_eps, one_mul, norm_star]

theorem hasDom_homLat (hE : IsTotallyComplex E) (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x)
    (hτ : ∀ (τ : E →+* ℂ) (x : E), τ (σ x) = star (τ x)) {k r : ℕ}
    {J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E} (hJ : ∀ i j, σ (J j i) = J i j) (hdetJ : J.det ≠ 0)
    {Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)} (hSD : GlobalTheory.SgGlob.SelfDual σ J Λ)
    {P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E} {f : Matrix (Fin (2 * r + k + 1)) (Fin r) E} {T : E}
    (hPP : pairM σ J P P = TF r T) (hDu : IsDual σ J P f) (hLat : tupLat (id1 E r) (sideM P f) ≤ Λ)
    {A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hMod : ∀ w, (A w)ᴴ * Hpk k r * A w = J.map w.embedding) {s : Fin r → ℝ} (hs : ∀ a, 0 < s a)
    (hAd : Adapted A P f s) {I : FractionalIdeal (𝓞 E)⁰ E} (hI : I ≠ 0) (hIs : Stab σ I) {c : ℝ} (hc : 0 < c) :
    HasDom volume (homLat σ J Λ P f A I c)
      (ENNReal.ofReal (((FractionalIdeal.absNorm I : ℝ) * Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E *
        c ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1))) := by
  set e : Fin r → Fin (2 * r + k + 1) → E := fun c i => P i c.castSucc with he
  set g : Fin r → Fin (2 * r + k + 1) → E := fun c i => f i c with hg
  have hee : ∀ c d, form σ J (e c) (e d) = 0 := fun c d => by
    have := congrFun (congrFun hPP d.castSucc) c.castSucc
    rw [pairM_apply'] at this
    rw [show form σ J (e c) (e d) = _ from this]
    simp [TF, Matrix.diagonal_apply, (Fin.castSucc_lt_last _).ne]
  have hgg : ∀ c d, form σ J (g c) (g d) = 0 := fun c d => by
    have := congrFun (congrFun hDu.2 d) c
    rw [pairM_apply'] at this
    exact this
  have hge : ∀ c d, form σ J (g c) (e d) = if c = d then 1 else 0 := fun c d => by
    have := congrFun (congrFun hDu.1 d.castSucc) c
    rw [pairM_apply'] at this
    rw [show form σ J (g c) (e d) = _ from this]
    simp [eq_comm]
  have heg : ∀ c d, form σ J (e c) (g d) = if c = d then 1 else 0 := fun c d => by
    rw [← form_conj σ J hσ hJ, hge]
    by_cases h : d = c
    · simp [h]
    · simp [h, Ne.symm h]
  have hle : ∀ c, ∀ x ∈ dInv E (r - c.val), x • e c ∈ Λ := fun c x hx =>
    hLat (Submodule.subset_span ⟨Fin.castAdd r c.castSucc, x, by rwa [FrameDual.frameDualTupleIdeals_castAdd], by
      ext i; simp [sideM, he]⟩)
  have hlg : ∀ c, ∀ x ∈ (dInv E (r - c.val))⁻¹, x • g c ∈ Λ := fun c x hx =>
    hLat (Submodule.subset_span ⟨Fin.natAdd (r + 1) c, x, by rwa [FrameDual.frameDualTupleIdeals_natAdd], by
      ext i; simp [sideM, hg]⟩)
  obtain ⟨Y, Ly, hY, hW⟩ := exists_basis (n := 2 * r + k + 1) (m := k + 1) σ J (by ring) e g hge heg hee hgg
  have hcol : ∀ j b, form σ J (fun i => Y i j) (e b) = 0 ∧ form σ J (fun i => Y i j) (g b) = 0 := fun j =>
    (hW _).2 ⟨Pi.single j 1, by ext i; simp [Matrix.mulVec_single_one]⟩
  have hBu : ∀ w, IsUnit (A w).det := fun w => by
    refine Ne.isUnit fun h0 => hdetJ ?_
    have h1 := congrArg Matrix.det (hMod w)
    rw [Matrix.det_mul, h0, mul_zero] at h1
    have h2 : (J.map w.embedding).det = w.embedding J.det := (RingHom.map_det _ _).symm
    rw [h2] at h1
    exact (map_eq_zero _).1 h1.symm
  have hAe : ∀ (w : InfinitePlace E) a, A w *ᵥ mv w.embedding (e a) = (s a : ℂ) • bvec (eI k r a) :=
    fun w a => (hAd w a).1
  have hAg : ∀ (w : InfinitePlace E) a, A w *ᵥ mv w.embedding (g a) = ((s a)⁻¹ : ℂ) • bvec (esI k r a) :=
    fun w a => (hAd w a).2
  set C : InfinitePlace E → Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ := fun w => Cm w.embedding (A w) Y with hCdef
  have hCu : ∀ w, IsUnit (C w).det := fun w =>
    isUnit_det_Cm σ J w.embedding (A w) (hτ _) (hMod w) (hBu w) hs (hAe w) (hAg w) hY hcol
  have hlat := isLattice_coordLat σ J hSD hY

  have hrow : ∀ (t : Fin (2 * r + k + 1) → E) (w : InfinitePlace E) (l : Fin (k + 1)),
      herm (Hpk k r) (bvec (wI k r l)) (A w *ᵥ mv w.embedding t) =
        (((Matrix.of fun _ j => form σ J (fun i => Y i j) t : Matrix (Fin 1) (Fin (k + 1)) E)).map w.embedding *
          (C w)⁻¹) 0 l := by
    intro t w l
    have h1 : ((Matrix.of fun _ j => form σ J (fun i => Y i j) t : Matrix (Fin 1) (Fin (k + 1)) E)).map w.embedding =
        (Matrix.of fun _ l => herm (Hpk k r) (bvec (wI k r l)) (A w *ᵥ mv w.embedding t) :
          Matrix (Fin 1) (Fin (k + 1)) ℂ) * C w := by
      ext i j
      rw [Matrix.map_apply, Matrix.of_apply,
        pairing_eq σ J w.embedding (A w) (hτ _) (hMod w) hs (hAe w) (hAg w) hcol t j]
      rfl
    rw [h1, Matrix.mul_nonsing_inv_cancel_right _ _ (hCu w)]
    rfl

  have hiff : ∀ (I : FractionalIdeal (𝓞 E)⁰ E), I ≠ 0 → Stab σ I → ∀ (c : ℝ) (z : InfinitePlace E → Fin (k + 1) → ℂ),
      z ∈ homLat σ J Λ P f A I c ↔ ∃ T : Matrix (Fin 1) (Fin (k + 1)) E,
        (∀ y ∈ coordLat Λ Y, (T *ᵥ y) 0 ∈ I) ∧
        ∀ w l, z w l = (c : ℂ) * (T.map w.embedding * (C w)⁻¹) 0 l := by
    intro I hI hIs c z
    have hsm := fun (t : Fin (2 * r + k + 1) → E) (ht : ∀ b, form σ J t (e b) = 0 ∧ form σ J t (g b) = 0) =>
      smul_mem_iff σ J hσ hJ hSD e g hee hgg hge heg (fun c => dInv E (r - c.val))
        (fun c => FrameDual.dInv_ne_zero _) (fun c => FrameDual.stab_dInv hσ _) hle hlg hI hIs ht
    have hTy : ∀ (t : Fin (2 * r + k + 1) → E) (y : Fin (k + 1) → E),
        ((Matrix.of fun _ j => form σ J (fun i => Y i j) t : Matrix (Fin 1) (Fin (k + 1)) E) *ᵥ y) 0 =
          form σ J (Y *ᵥ y) t := by
      intro t y
      rw [form_mulVec_left]
      simp [Matrix.mulVec, dotProduct, mul_comm]
    constructor
    · rintro ⟨t, ⟨htW, htc⟩, hz⟩
      refine ⟨Matrix.of fun _ j => form σ J (fun i => Y i j) t, fun y hy => ?_, fun w l => ?_⟩
      · rw [hTy]
        exact (hsm t htW).1 htc _ hy ((hW _).2 ⟨y, rfl⟩)
      · rw [← hrow]
        exact hz w l
    · rintro ⟨Tm, hT, hz⟩
      obtain ⟨u, hu⟩ := exists_solve σ J hσ hJ hdetJ e g hee hgg hge heg hY hW (Tm 0)
      have hT' : Tm = Matrix.of fun _ j => form σ J (fun i => Y i j) (Y *ᵥ u) := by
        ext i j
        rw [Subsingleton.elim i 0, Matrix.of_apply, hu]
      have htW := (hW (Y *ᵥ u)).2 ⟨u, rfl⟩
      refine ⟨Y *ᵥ u, ⟨htW, (hsm _ htW).2 fun x hx hxW => ?_⟩, fun w l => ?_⟩
      · obtain ⟨y, rfl⟩ := (hW x).1 hxW
        rw [← hTy, ← hT']
        exact hT y hx
      · rw [hz, hT', ← hrow]
        rfl

  have hone : (1 : FractionalIdeal (𝓞 E)⁰ E) ≠ 0 := one_ne_zero
  obtain ⟨L₁, hL₁, hcov₁⟩ := exists_core E hE (coordLat Λ Y) hlat C hCu hone one_pos
  have hmem : ∀ x, x ∈ latAt E (k + 1) (coordLat Λ Y) (gC E C) ↔ signConj E k x ∈ L₁ := by
    intro x
    have hofc : ∀ w, (Matrix.of (gC E C w))⁻¹ = C w := fun w =>
      Matrix.nonsing_inv_nonsing_inv _ (hCu w)
    have hval : ∀ (y : Fin (k + 1) → E) (w : InfinitePlace E) (l : Fin (k + 1)),
        (A w *ᵥ mv w.embedding (Y *ᵥ y)) (wI k r l) = (C w *ᵥ fun a => w.embedding (y a)) l := fun y w l => by
      rw [mv_mulVec]
      exact (Cm_mulVec w.embedding (A w) Y _ l).symm
    rw [hL₁, ← hiff 1 hone (stab_one σ) 1, mem_latAt]
    constructor
    · rintro ⟨y, hy, hx⟩
      refine ⟨Y *ᵥ y, ⟨(hW _).2 ⟨y, rfl⟩, fun c hc => ?_⟩, fun w l => ?_⟩
      · rw [inv_one] at hc
        obtain ⟨d, rfl⟩ := (FractionalIdeal.mem_one_iff _).1 hc
        exact (algebraMap_smul E d (Y *ᵥ y)) ▸ Λ.smul_mem d hy
      · have h1 := herm_bvec_wI k r l (A w *ᵥ mv w.embedding (Y *ᵥ y))
        rw [hval] at h1
        rw [signConj_apply, hx w, hofc]
        change _ = ((1 : ℝ) : ℂ) * herm (Hpk k r) (bvec (wI k r l)) (A w *ᵥ mv w.embedding (Y *ᵥ y))
        rw [h1]
        simp [mul_comm]
    · rintro ⟨t, ⟨htW, htc⟩, hz⟩
      have htΛ : t ∈ Λ := by
        have := htc 1 (by rw [inv_one]; exact (FractionalIdeal.mem_one_iff _).2 ⟨1, by simp⟩)
        simpa using this
      obtain ⟨y, rfl⟩ := (hW t).1 htW
      refine ⟨y, htΛ, fun w => ?_⟩
      ext l
      have h1 := hz w l
      have h2 := herm_bvec_wI k r l (A w *ᵥ mv w.embedding (Y *ᵥ y))
      rw [hval] at h2
      change _ = ((1 : ℝ) : ℂ) * herm (Hpk k r) (bvec (wI k r l)) (A w *ᵥ mv w.embedding (Y *ᵥ y)) at h1
      rw [h2, signConj_apply] at h1
      have h3 : star (x w l) = star ((C w *ᵥ fun a => w.embedding (y a)) l) := by
        have := congrArg (eps k l * ·) h1
        simp only [Complex.ofReal_one, one_mul] at this
        rw [← mul_assoc, eps_mul_self, one_mul, mul_comm (star _), ← mul_assoc, eps_mul_self, one_mul] at this
        exact this
      rw [hofc]
      exact star_injective h3
  obtain ⟨hd, hz, hcv⟩ := HasCov.of_measurePreserving (signConj E k) (signConj_measurePreserving k)
    hmem hcov₁
  have hv : 0 < Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E := by
    rw [vInv_pow E hE]
    have : (discr E : ℝ) ≠ 0 := by exact_mod_cast discr_ne_zero E
    positivity
  have hpos : 0 < covAt E (k + 1) (latAt E (k + 1) (coordLat Λ Y) (gC E C)) := ZLattice.covolume_pos _ _
  have hκ : covAt E (k + 1) (latAt E (k + 1) (coordLat Λ Y) (gC E C)) =
      (Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) ^ (k + 1) := by
    have h1 : covAt E (k + 1) (latAt E (k + 1) (coordLat Λ Y) (gC E C)) = _ := hcv
    simp only [map_one, Rat.cast_one, one_mul, one_pow, mul_one, pow_mul] at h1
    generalize covAt E (k + 1) (latAt E (k + 1) (coordLat Λ Y) (gC E C)) = κ at h1 hpos
    have hvk := pow_pos hv (k + 1)
    generalize (Formalism.HermitianLatticesTheory.vInv E ^ Formalism.HermitianLatticesTheory.fDeg E) ^ (k + 1) = v at h1 hvk ⊢
    have h2 : κ * κ = v * v := by
      calc κ * κ = v * (v / κ) * κ := by rw [← h1]
        _ = v * v := by field_simp
    rcases mul_self_eq_mul_self_iff.1 h2 with h | h
    · exact h
    · linarith
  obtain ⟨L, hL, hcov⟩ := exists_core E hE (coordLat Λ Y) hlat C hCu hI hc
  refine hasDom_of_hasCov (L := L) (fun z => (hL z).trans (hiff I hI hIs c z).symm) ?_
  rw [hκ, ← pow_mul, div_self (by rw [pow_mul]; exact (pow_pos hv _).ne'), mul_one] at hcov
  exact hcov

end Main

theorem covolume_homLat : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (k r : ℕ) (J : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) E) (Λ : Submodule (𝓞 E) (Fin (2 * r + k + 1) → E)) (P : Matrix (Fin (2 * r + k + 1)) (Fin (r + 1)) E) (f : Matrix (Fin (2 * r + k + 1)) (Fin r) E) (T : F) (A : InfinitePlace E → Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (s : Fin r → ℝ), IsVolData σ J Λ P f T A s → ∀ a : Fin r, HasDom volume (homLat (σ : E →+* E) J Λ P f A (dInv E (r - a.val)) (s a)) (ENNReal.ofReal (((2⁻¹ : ℝ) ^ Fintype.card (InfinitePlace E) * |(NumberField.discr F : ℝ)| ^ (1 - 2 * ((r - a.val : ℕ) : ℝ)) * s a ^ (2 * Fintype.card (InfinitePlace E))) ^ (k + 1))) := by
  intro F E _ _ _ _ _ σ k r J Λ P f T A s hV a
  obtain ⟨hCM, hU, hND, hSD, hFr, hDu, hLat, hMod, hs, hAd⟩ := hV
  haveI := hU
  have hτ : ∀ (τ : E →+* ℂ) (x : E), τ ((σ : E →+* E) x) = star (τ x) := hCM.2.2.2
  have hσ : ∀ x, (σ : E →+* E) ((σ : E →+* E) x) = x := fun x => by
    let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
    apply τ.injective
    rw [hτ, hτ, star_star]
  have h := hasDom_homLat hCM.2.1 (σ : E →+* E) hσ hτ hND.1 hND.2 hSD hFr.2 hDu hLat hMod hs hAd
    (FrameDual.dInv_ne_zero (r - a.val)) (FrameDual.stab_dInv hσ _) (hs a)
  have hv := CovMul.value_eq (F := F) (E := E) hCM.2.1 hCM.2.2.1 (r - a.val) 0
  have h0 : dInv E 0 = 1 := pow_zero _
  rw [h0, mul_one] at hv
  simp only [Nat.cast_zero, mul_zero, sub_zero] at hv
  rw [hv] at h
  exact h

end GlobalTheory.SnMass.VolN.CovH
