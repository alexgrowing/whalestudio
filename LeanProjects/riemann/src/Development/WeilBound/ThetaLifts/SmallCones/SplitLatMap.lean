import Development.WeilBound.ThetaLifts.SmallCones.WittOf
import Development.WeilBound.ThetaLifts.TowerModels.PlaneMain

noncomputable section

namespace PositivityTheory.ThKCT

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK Fr PositivityTheory.ThKG.Tow.Pln

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cartan_low {n n₁ : ℕ} {M θ : Matrix (Fin n) (Fin n) ℂ} {θ₁ : Matrix (Fin n₁) (Fin n₁) ℂ}
    {ι : Matrix (Fin n) (Fin n₁) ℂ} {P : Matrix (Fin n₁) (Fin n) ℂ} (hP : P * ι = 1) (h : IsCartan M θ) (e : θ * ι = ι * θ₁) :
    IsCartan (ιᵀ * M * ι.map star) θ₁ := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, fun x hx => ?_⟩
  · rw [← Matrix.one_mul (θ₁ * θ₁), ← hP, Matrix.mul_assoc, ← Matrix.mul_assoc ι, ← e, Matrix.mul_assoc θ, ← e,
      ← Matrix.mul_assoc θ, h1, Matrix.one_mul]
  · have m : ∀ {a b c : ℕ} (A : Matrix (Fin a) (Fin b) ℂ) (C : Matrix (Fin b) (Fin c) ℂ),
        (A * C).map star = A.map star * C.map star := fun A C => Matrix.map_mul (f := starRingEnd ℂ)
    calc _ = (ι * θ₁)ᵀ * M * (ι * θ₁).map star := by simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = ιᵀ * (θᵀ * M * θ.map star) * ι.map star := by rw [← e]; simp only [Matrix.transpose_mul, m, Matrix.mul_assoc]
      _ = _ := by rw [h2]
  · rw [← gram_vec, Matrix.mulVec_mulVec, ← e, ← Matrix.mulVec_mulVec]
    refine h3 _ fun h0 => hx ?_
    rw [← Matrix.one_mulVec x, ← hP, ← Matrix.mulVec_mulVec, h0, Matrix.mulVec_zero]

theorem splitLat_map {v : Pl F} (τ : E →ₐ[F] Fv F v) {n m : ℕ} {L : Submodule (𝓞 E) (Fin n → E)}
    {L' : Submodule (𝓞 E) (Fin m → E)} (A : Matrix (Fin m) (Fin n) E) (h : ∀ z ∈ L, A *ᵥ z ∈ L') {w : Fin n → Fv F v}
    (hw : w ∈ splitLat τ L) : A.map τ *ᵥ w ∈ splitLat τ L' :=
  splitLat_le τ ((splitLat τ L').comap ((A.map τ).mulVecLin.restrictScalars _)) (fun z hz => by
    have e : A.map τ *ᵥ (fun i => τ (z i)) = fun i => τ ((A *ᵥ z) i) :=
      funext fun i => (RingHom.map_mulVec (τ : E →+* Fv F v) A z i).symm
    show A.map τ *ᵥ (fun i => τ (z i)) ∈ splitLat τ L'
    rw [e]
    exact map_mem_splitLat τ (h z hz)) hw

theorem low_eps {B : Base F E} (hB : B.IsGood σ) {ε : E} {κ : ℂ} (hκ1 : κ * star κ = 1)
    (hκ : ∀ e : E →+* ℂ, star κ * e ε = κ) {D : Submodule (𝓞 E) E} {n n₁ : ℕ} {Y : Spc F E n} {Y₁ : Spc F E n₁}
    {H : Plane E n n₁} {i₀ i₁ r s : ℕ} (hY : IsEps σ B ε κ D Y r s) (hH : H.IsAdapted σ B Y Y₁ i₀ i₁) {ε' : E}
    {A' : Matrix (Fin n₁ ⊕ Fin 2) (Fin n) E} (h : IsFr (σ : E →+* E) ε' Y.J Y₁.J H.ι H.x H.y A') :
    1 ≤ r ∧ 1 ≤ s ∧ IsEps σ B ε κ D Y₁ (r - 1) (s - 1) := by
  have hcm := hB.cm
  set P : Matrix (Fin n₁) (Fin n) E := A'.submatrix Sum.inl id with hPd
  have hP : ∀ (u : Fin n₁ → E) (a b : E), P *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = u := fun u a b => funext fun j => by
    have : A' *ᵥ (H.ι *ᵥ u + a • H.x + b • H.y) = Sum.elim u ![a, b] := by
      rw [← fr_mulVec, Matrix.mulVec_mulVec, h.inv2, Matrix.one_mulVec]
    exact congrFun this (Sum.inl j)
  have hPι : P * H.ι = 1 := Matrix.ext fun i j => by
    exact (congrFun (congrFun h.inv2 (Sum.inl i)) (Sum.inl j)).trans (by simp [Matrix.one_apply])
  have hform : ∀ u u', form σ Y₁.J u u' = form σ Y.J (H.ι *ᵥ u) (H.ι *ᵥ u') := hH.gram ▸ form_gram Y.J H.ι
  have hL : Y₁.L = Y.L.comap ((Matrix.mulVecLin H.ι).restrictScalars (𝓞 E)) := Submodule.ext hH.low
  have cg : ∀ e : E →+* ℂ, (H.ι.map e)ᵀ * (κ • Y.J.map e) * (H.ι.map e).map star = κ • Y₁.J.map e := fun e => by
    rw [Matrix.mul_smul, Matrix.smul_mul, map_gram hcm, hH.gram]
  have hPe : ∀ {S : Type} [CommRing S] (e : E →+* S), P.map e * H.ι.map e = 1 := fun e => by
    rw [← Matrix.map_mul, hPι, Matrix.map_one _ (map_zero _) (map_one _)]
  have hXX : ∀ e : E →+* ℂ, (fun i => e (H.x i)) ⬝ᵥ (κ • Y.J.map e) *ᵥ star (fun i => e (H.x i)) = 0 := fun e => by
    rw [Matrix.smul_mulVec, dotProduct_smul, ← map_form hcm, hH.xx, map_zero, smul_zero]
  have hmin : min r s ≠ 0 := fun h0 => by
    obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
    have h1 := aniso (hY.sig w) h0 (hXX _)
    have h2 : H.x = 0 := funext fun i => (B.emb w).1.injective ((congrFun h1 i).trans (map_zero _).symm)
    have e := hH.xy
    rw [h2, form, zero_dotProduct] at e
    exact zero_ne_one e
  refine ⟨by omega, by omega, fun i j => ?_, fun w => ?_, hL ▸ isLattice_comap n n₁ Y.L H.ι P hPι hY.lat, fun u => ?_,
    fun w => ?_, fun v u => ?_⟩
  · rw [← form_single (σ := σ) Y₁.J j i, ← form_single (σ := σ) Y₁.J i j, hform, hform, form_swap hcm hY.herm]
  · rw [← cg]
    refine (real_plane _ (fun i => (B.emb w).1 (H.x i)) (κ • fun i => (B.emb w).1 (H.y i)) _ (P.map (B.emb w).1) hH.rank
      (map_herm hcm _ (hκ _) hY.herm) (hXX _) ?_ ?_ ?_ ?_ (hPe _) (hY.sig w)).1
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, smul_dotProduct, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.yy, map_zero, smul_zero, smul_zero, smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, dotProduct_smul, dotProduct_smul,
        ← map_form hcm, hH.xy, map_one, smul_eq_mul, smul_eq_mul, mul_one, mul_comm, hκ1]
    · rw [Matrix.smul_mulVec, Matrix.mulVec_smul, map_orth hcm _ Y.J H.ι H.x (fun u => (hH.orth u).1), smul_zero]
    · rw [star_smul, Matrix.mulVec_smul, Matrix.smul_mulVec, Matrix.mulVec_smul, Matrix.mulVec_smul,
        map_orth hcm _ Y.J H.ι H.y (fun u => (hH.orth u).2), smul_zero, smul_zero]
  · refine ⟨fun hu u' hu' => ?_, fun G => (hH.low u).2 ((hY.dual _).2 fun z hz => ?_)⟩
    · rw [hform]; exact (hY.dual _).1 ((hH.low u).1 hu) _ ((hH.low u').1 hu')
    · obtain ⟨_, _, u', -, -, hu', hz'⟩ := hH.split z hz
      rw [hz', form_add_right, form_add_right, form_smul_right, form_smul_right, (hH.orth u).1,
        (hH.orth u).2, mul_zero, mul_zero, zero_add, add_zero, ← hform]
      exact G u' hu'
  · rw [← cg]
    exact cartan_low (hPe _) (hY.cartan w) (hH.cartan w).1
  · have hn := hH.rank
    let f : Fin n₁ → Fin n := fun j => ⟨skip i₀ i₁ j, by have := j.2; unfold skip; split_ifs <;> omega⟩
    have hf : Function.Injective f := fun a b e => Fin.ext (by
      have := congrArg Fin.val e
      simp only [f, skip] at this
      split_ifs at this <;> omega)
    let T : Matrix (Fin n) (Fin n₁) (Fv F v.1) := (1 : Matrix (Fin n) (Fin n) _).submatrix id f
    have e1 : (Y.bas v).1 * T = H.ι.map (B.τ v) * (Y₁.bas v).1 := Matrix.ext fun a j => by
      rw [← (hH.bas v (f j)).2.2 j rfl a]
      simp [T, Matrix.mul_apply, Matrix.one_apply]
    have e2 : (∀ i, u i ∈ v.1.adicCompletionIntegers F) ↔ ∀ i, (T *ᵥ u) i ∈ v.1.adicCompletionIntegers F := by
      refine ⟨fun G i => sum_mem fun j _ => mul_mem ?_ (G j), fun G j => ?_⟩
      · simp only [T, Matrix.submatrix_apply, Matrix.one_apply]
        split_ifs
        exacts [one_mem _, zero_mem _]
      · simpa [T, Matrix.mulVec, dotProduct, Matrix.one_apply, hf.eq_iff] using G (f j)
    rw [e2, hY.bas v, Matrix.mulVec_mulVec, e1, ← Matrix.mulVec_mulVec]
    refine ⟨fun G => ?_, splitLat_map _ _ fun z hz => (hH.low z).1 hz⟩
    have := splitLat_map (L' := Y₁.L) _ P (fun z hz => by
      obtain ⟨a, b, u', -, -, hu', rfl⟩ := hH.split z hz
      rwa [add_comm (a • H.x), hP]) G
    rwa [Matrix.mulVec_mulVec, show P.map (B.τ v) * H.ι.map (B.τ v) = 1 from hPe (B.τ v : E →+* Fv F v.1),
      Matrix.one_mulVec] at this

theorem low_of : Low := by
  intro F E _ _ _ _ _ σ B n n₁ Y Y₁ H i₀ i₁ r s hB hH
  refine ⟨fun hY => ?_, fun hY => ?_⟩
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inl hY) hH
    simp only [isHerm_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h
  · obtain ⟨ε, A', h⟩ := isFr hB (Or.inr hY) hH
    simp only [isSkew_iff] at hY ⊢
    exact low_eps hB (by simp) (fun e => by simp) hY hH h

end PositivityTheory.ThKCT

end
