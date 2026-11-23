import Development.WeilBound.ThetaLifts.SmallCones.SoKill
import Development.WeilBound.ThetaLifts.SmallCones.ExpAlg

noncomputable section

namespace PositivityTheory.ThKCT.So

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

theorem two_rows {k : Type} [Field k] {n d : ℕ} (C : Matrix (Fin n) (Fin d) k) (x y : Fin n → k) (w : Fin d → k)
    (hx : x ≠ 0) (hi : ∀ a b : k, a • x + b • y = 0 → b = 0)
    (hs : ∀ j, ∃ (b : k) (z : Fin d → k), x ⬝ᵥ C *ᵥ z = 0 ∧ y ⬝ᵥ C *ᵥ z = 0 ∧ Pi.single j 1 = z + b • w) :
    ∃ p, p ≠ 0 ∧ p ᵥ* C = 0 := by
  have key : ∀ a b : k, a * (x ⬝ᵥ C *ᵥ w) + b * (y ⬝ᵥ C *ᵥ w) = 0 → (a • x + b • y) ᵥ* C = 0 := fun a b h => funext fun j => by
    obtain ⟨c, z, h1, h2, e⟩ := hs j
    have : ((a • x + b • y) ᵥ* C) j = (a • x + b • y) ⬝ᵥ C *ᵥ Pi.single j 1 := by
      rw [dotProduct_mulVec, dotProduct_single, mul_one]
    rw [this, e]
    simp only [mulVec_add, mulVec_smul, add_dotProduct, smul_dotProduct, dotProduct_add, dotProduct_smul, h1, h2, smul_eq_mul,
      Pi.zero_apply]
    linear_combination c * h
  by_cases h : x ⬝ᵥ C *ᵥ w = 0
  · exact ⟨_, by simpa using hx, key 1 0 (by simp [h])⟩
  · exact ⟨_, fun e => h (neg_eq_zero.1 (hi _ _ e)), key (y ⬝ᵥ C *ᵥ w) (-(x ⬝ᵥ C *ᵥ w)) (by ring)⟩

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {v : Pl F}
  {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁} {B : Base F E}

theorem sig_sig (h : IsCMExt F E σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  exact τ.injective (by rw [h.2.2.2, h.2.2.2, star_star])

theorem form_swap (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (ε : E) (h : ∀ i j, σ (J j i) = ε * J i j) (x y : Fin n → E) :
    σ (form σ J x y) = ε * form σ J y x := by
  simp only [form, dotProduct, mulVec, map_sum, map_mul, hσ, h, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem form_swap_zero (hσ : ∀ x, σ (σ x) = x) {J : Matrix (Fin n) (Fin n) E} (ε : E) (h : ∀ i j, σ (J j i) = ε * J i j)
    {x y : Fin n → E} (h0 : form σ J x y = 0) : form σ J y x = 0 := by
  have := form_swap hσ ε h y x
  rw [h0, mul_zero] at this
  exact (map_eq_zero σ).1 this

theorem hTens_vec (a c : AE F E) (x p : Fin n → E) (y q : Fin d → E) :
    hTens (cA σ) (incM F X.J) (incM F W.J) (a • incM F (vecMulVec x y)) (c • incM F (vecMulVec p q)) =
      a * cA σ c * inclR (F := F) (AF F) (form σ X.J x p * form σ W.J y q) := by
  have hc : ∀ z : E, cA σ (inclR (F := F) (AF F) z) = inclR (F := F) (AF F) (σ z) := fun z => rfl
  simp only [hTens, form, dotProduct, mulVec, incM, Matrix.smul_apply, map_apply, vecMulVec_apply, smul_eq_mul, map_mul, hc, map_sum,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_comm, Finset.sum_comm]
  exact Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring

theorem plane_span {H : Plane E n n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B X X₁ i₀ i₁) (hL : X.L.IsLattice E) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  have hz : z ∈ Submodule.span E (X.L : Set (Fin n → E)) := by rw [hL.span_eq_top]; trivial
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨s, t, u, -, -, -, e⟩ := h.split z hz
    exact ⟨s, t, u, e⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add a b _ _ ha hb =>
    obtain ⟨s, t, u, rfl⟩ := ha
    obtain ⟨s', t', u', rfl⟩ := hb
    exact ⟨s + s', t + t', u + u', by rw [add_smul, add_smul, mulVec_add]; abel⟩
  | smul c a _ ha =>
    obtain ⟨s, t, u, rfl⟩ := ha
    exact ⟨c * s, c * t, c • u, by rw [mulVec_smul, mul_smul, mul_smul, smul_add, smul_add]⟩

theorem vec_left (a : AF F) (ε : AE F E) (p : Fin n → E) (q : Fin d → E) :
    a • ε • incM F (vecMulVec p q) = vecMulVec (incV F p) (a • ε • incV F q) := by
  ext i j
  simp only [incM, incV, Matrix.smul_apply, map_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, mul_smul_comm]
  congr 1
  ring

theorem incV_mulVec (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) : incV F (ι *ᵥ p) = incM F ι *ᵥ incV F p := by
  funext i
  simp [incV, incM, mulVec, dotProduct]

theorem vec_right (a : AF F) (ε : AE F E) (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) (q : Fin d → E) :
    a • ε • incM F (vecMulVec (ι *ᵥ p) q) = vecMulVec (incM F ι *ᵥ (a • ε • incV F p)) (incV F q) := by
  rw [mulVec_smul, mulVec_smul, ← incV_mulVec]
  ext i j
  simp only [incM, incV, Matrix.smul_apply, map_apply, vecMulVec_apply, Pi.smul_apply, smul_eq_mul, map_mul, smul_mul_assoc,
    mul_assoc]

theorem vec_mid (a : AF F) (ε : AE F E) (ι : Matrix (Fin n) (Fin n₁) E) (ι' : Matrix (Fin d) (Fin d₁) E) (p : Fin n₁ → E)
    (q : Fin d₁ → E) : a • ε • incM F (vecMulVec (ι *ᵥ p) (ι' *ᵥ q)) =
      incM F ι * (a • ε • incM F (vecMulVec p q)) * (incM F ι')ᵀ := by
  have e : ∀ {a b : ℕ} (p : Fin a → E) (q : Fin b → E), incM F (vecMulVec p q) = vecMulVec (incV F p) (incV F q) := fun p q => by
    ext i j
    simp [incM, incV, vecMulVec_apply]
  rw [Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.smul_mul, e, e, incV_mulVec, incV_mulVec, mul_vecMulVec,
    vecMulVec_mul, vecMul_transpose]

theorem map_mulVec' (t : E →ₐ[F] Fv F v) (ι : Matrix (Fin n) (Fin n₁) E) (p : Fin n₁ → E) :
    (fun i => t ((ι *ᵥ p) i)) = ι.map t *ᵥ fun i => t (p i) := by
  funext i
  simp [mulVec, dotProduct]

theorem map_sgl (t : E →ₐ[F] Fv F v) (j : Fin n) : (fun i => t ((Pi.single j 1 : Fin n → E) i)) = Pi.single j 1 := by
  funext i
  by_cases h : i = j
  · subst h; simp
  · simp [h]

theorem ev_zero (hL : LinEx) {r s r' s' : ℕ} (hB : B.IsGood σ) (hX : X.IsHerm σ B r s) (hW : W.IsSkew σ B r' s') {M : Model σ X W}
    (hM : M.IsGood B.ψ) (t : E →ₐ[F] Fv F v) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) {x : Fin n → E} (hx : x ≠ 0)
    (he : ∀ z, ∀ Φ ∈ schA F _, e (M.co.rho B.ψ (vecMulVec (incV F x) z) Φ) = e Φ) : ∀ Φ ∈ M.So B.ψ t, e Φ = 0 := by
  intro Φ hΦ
  funext y
  refine so_kill M hL hB hX hW hM t (LinearMap.proj y ∘ₗ e) {a | a.1 = x ∧ a.2.2 = 0} ?_ (fun C hC => ⟨fun i => t (x i), ?_, ?_⟩) Φ hΦ
  · rintro ⟨_, q, _⟩ ⟨rfl, rfl⟩ ε - - - c Ψ hΨ
    simp only [LinearMap.comp_apply, vec_left, he _ _ hΨ, zero_mul, map_zero, AddChar.map_zero_eq_one, one_mul]
  · exact fun h0 => hx (funext fun i => (map_eq_zero t).1 (congrFun h0 i))
  · funext j
    have := hC (x, Pi.single j 1, 0) ⟨rfl, rfl⟩
    simp only [map_sgl] at this
    rwa [dotProduct_mulVec, dotProduct_single, mul_one] at this

theorem x_ne {H : Plane E n n₁} {i₀ i₁ : ℕ} (h : H.IsAdapted σ B X X₁ i₀ i₁) : H.x ≠ 0 := fun e => by
  have := h.xy
  rw [e, form, zero_dotProduct] at this
  exact zero_ne_one this

end PositivityTheory.ThKCT.So

namespace PositivityTheory.ThKCT

open Filter Topology NumberField IsDedekindDomain Matrix GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
  GlobalTheory.CompanionTheory.Ar.RT.Move GlobalTheory.LatVac PositivityTheory.KCo GlobalTheory.ThK So

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField Classical.propDecidable

set_option maxHeartbeats 400000 in
theorem soEv_of (hL : LinEx) (hLow : Low) : SoEv := by
  intro F E _ _ _ _ _ σ B n d n₁ d₁ X W X₁ W₁ H H' j₀ j₁ i₀ i₁ r s r' s' M M₀ hH hH' hB hX hW hM hM₀ e he Ψ hΨ
  refine ⟨ev_zero hL hB hX hW hM _ e (x_ne hH) (fun z => he.inv _ (Or.inl ⟨z, rfl⟩)) Ψ hΨ, fun a => ?_⟩
  have hX₁ := ((hLow F E σ B n n₁ X X₁ H j₀ j₁ r s hB hH).1 hX).2.2
  have hW₁ := ((hLow F E σ B d d₁ W W₁ H' i₀ i₁ r' s' hB hH').2 hW).2.2
  have hσ : ∀ x, σ (σ x) = x := sig_sig hB.cm
  set t := B.τ₁
  set s₀ := a • incM F (vecMulVec H.y H'.x)
  have hsch : ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ s₀ Φ) ∈ schA F (Fin n₁ × Fin d₁) :=
    fun Φ hΦ => he.maps _ (rho_mem M hB.std _ hΦ)
  have hΨs : Ψ ∈ schA F (Fin n × Fin d) := so_le M hM _ hΨ
  obtain ⟨⟨ι₀, hι₀⟩, hf⟩ := hL F E σ B n₁ d₁ X₁ W₁ M₀ _ _ _ _ hB hX₁ hW₁ _ t
  refine mem_so M₀ hM₀ t (hsch _ hΨs) fun z => ⟨slice_mem' (hsch _ hΨs) z, ι₀, hι₀, fun Y hY => ?_⟩
  obtain ⟨x₀, hx, h0, rfl⟩ := exists_coB (X := X₁) (W := W₁) hB.cm t (det_herm hX₁) (det_skew hW₁) Y
  obtain ⟨c, hc, hc0⟩ := (rank_ne_iff _).1 hY
  set C₀ := X₁.J.map t * x₀.map (piW (t.comp σ)) * (W₁.J.map t)ᵀ with hC₀
  have hc1 : c ᵥ* C₀ = 0 := by rwa [coB_eq, Matrix.neg_mul, Matrix.neg_mul, Matrix.vecMul_neg, neg_eq_zero] at hc0
  let L : Fn F n d →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => ι₀ (fun y => e (M.co.rho B.ψ s₀ Φ) (repl B.v₁ z y)) (coB σ X₁ W₁ t x₀)
      map_add' := fun a b => by
        rw [rho_add, map_add]
        exact congrFun (map_add ι₀ _ _) _
      map_smul' := fun c a => by
        rw [rho_smul, map_smul]
        exact congrFun (map_smul ι₀ c _) _ }
  have hww : ∀ q, form σ W.J H'.x (H'.ι *ᵥ q) = 0 := fun q =>
    form_swap_zero hσ (-1) (fun i j => by rw [hW.skew, neg_one_mul]) (hH'.orth q).1
  have hxx : ∀ q, form σ X.J H.x (H.ι *ᵥ q) = 0 := fun q =>
    form_swap_zero hσ 1 (fun i j => by rw [hX.herm, one_mul]) (hH.orth q).1
  have hcomm : ∀ (b : AF F) (ε : AE F E) p q, form σ W.J H'.x q = 0 → ∀ Φ,
      M.co.rho B.ψ s₀ (M.co.rho B.ψ (b • ε • incM F (vecMulVec p q)) Φ) =
        M.co.rho B.ψ (b • ε • incM F (vecMulVec p q)) (M.co.rho B.ψ s₀ Φ) := fun b ε p q hq Φ => by
    rw [rho_comm, ← smul_assoc, symp, hTens_vec, hq]
    simp
  refine so_kill M hL hB hX hW hM t L {b | (b.1 = H.x ∧ (b.2.1 = H'.x ∨ ∃ q, b.2.1 = H'.ι *ᵥ q) ∧ b.2.2 = 0) ∨
    (∃ p, b = (H.ι *ᵥ p, H'.x, 0)) ∨ ∃ p q, b = (H.ι *ᵥ p, H'.ι *ᵥ q, (fun i => t (p i)) ⬝ᵥ C₀ *ᵥ fun j => t (q j))} ?_
    (fun C hC => ?_) Ψ hΨ
  · rintro ⟨p, q, β⟩ hb ε e0 e1 e2 b Φ hΦ
    change ι₀ (fun y => e (M.co.rho B.ψ s₀ (M.co.rho B.ψ _ Φ)) (repl B.v₁ z y)) _ = _ * ι₀ _ _
    have hs := rho_mem M hB.std s₀ hΦ
    rcases hb with ⟨rfl, hq, rfl⟩ | ⟨p, h⟩ | ⟨p, q, h⟩
    · rw [hcomm _ _ _ _ (by rcases hq with rfl | ⟨q, rfl⟩; exacts [hH'.xx, hww q]), he.inv _ (Or.inl ⟨_, vec_left _ _ _ _⟩) _ hs]
      simp
    · cases h
      rw [hcomm _ _ _ _ hH'.xx, he.inv _ (Or.inr ⟨_, vec_right _ _ _ _ _⟩) _ hs]
      simp
    · cases h
      have hu : At (evFin F B.v₁) (liftV B.v₁ b • ε • incM F (vecMulVec p q)) := at_lift _ _
      rw [hcomm _ _ _ _ (hww q), vec_mid, he.Heisenberg₂ _ _ hs, slice_rho M₀ B.ψ hu, mult' M₀ hB.std hι₀ hu
        (by rw [← smul_assoc, map_vec _ _ (piW_inc _), Algebra.smul_def, map_mul, e2, mul_zero, zero_smul]) hx h0
        (slice_mem' (hsch Φ hΦ) z)]
      have k1 := hf x₀ (ε • incM F (vecMulVec p q)) hx h0
      rw [map_vec _ _ (piW_inc _), e1, one_smul, trace_vec] at k1
      rw [show symp _ _ _ _ _ _ = _ from sy_smul M₀ _ _ _, mul_comm (liftV _ _), mul_liftV, k1]
  · have hrow : ∀ (w : Fin d → Fv F B.v₁) (w₁ : Fin d₁ → Fv F B.v₁), (∀ p : Fin n₁ → E, (H.ι.map t *ᵥ fun i => t (p i)) ⬝ᵥ C *ᵥ w =
        (fun i => t (p i)) ⬝ᵥ C₀ *ᵥ w₁) → (H.ι.map t *ᵥ c) ⬝ᵥ C *ᵥ w = 0 := fun w w₁ h => by
      have : (H.ι.map t)ᵀ *ᵥ C *ᵥ w = C₀ *ᵥ w₁ := funext fun i => by
        have := h (Pi.single i 1)
        rwa [map_sgl, dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, dotProduct_single, single_dotProduct, mul_one,
          one_mul] at this
      rw [dotProduct_comm, dotProduct_mulVec, ← mulVec_transpose, this, dotProduct_comm, dotProduct_mulVec, hc1, zero_dotProduct]
    refine two_rows C (fun i => t (H.x i)) (H.ι.map t *ᵥ c) (fun j => t (H'.y j))
      (fun h0 => x_ne hH (funext fun i => (map_eq_zero t).1 (congrFun h0 i))) (fun α β h => ?_) fun j => ?_
    · have g1 : (fun i => t (H.x i)) ᵥ* (X.J * H.ι.map σ).map t = 0 := funext fun j => by
        have := congrArg t (hxx (Pi.single j 1))
        simpa [form, vecMul, mulVec, dotProduct, Matrix.mul_apply, Pi.single_apply] using this
      have g2 : (H.ι.map t)ᵀ * (X.J * H.ι.map σ).map t = X₁.J.map t := by
        rw [← hH.gram, Matrix.mul_assoc, Matrix.map_mul (L := H.ιᵀ), transpose_map]
      have g3 := congrArg (· ᵥ* (X.J * H.ι.map σ).map t) h
      simp only [add_vecMul, smul_vecMul, g1, smul_zero, zero_add, zero_vecMul] at g3
      rw [← vecMul_transpose, vecMul_vecMul, g2] at g3
      by_contra hβ
      exact hc (eq_zero_of_vecMul_eq_zero (unit_map t (det_herm hX₁)).ne_zero ((smul_eq_zero.1 g3).resolve_left hβ))
    · obtain ⟨α, β, u, ej⟩ := plane_span hH' hW.lat (Pi.single j 1)
      refine ⟨t β, t α • (fun j => t (H'.x j)) + fun j => t ((H'.ι *ᵥ u) j), ?_, ?_, ?_⟩
      · rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, hC (H.x, H'.x, 0) (Or.inl ⟨rfl, Or.inl rfl, rfl⟩),
          hC (H.x, H'.ι *ᵥ u, 0) (Or.inl ⟨rfl, Or.inr ⟨u, rfl⟩, rfl⟩), smul_zero, add_zero]
      · have q1 := hrow (fun j => t (H'.x j)) 0 fun p => by
          rw [← map_mulVec', mulVec_zero, dotProduct_zero]
          exact hC (H.ι *ᵥ p, H'.x, 0) (Or.inr (Or.inl ⟨p, rfl⟩))
        have q2 := hrow (fun j => t ((H'.ι *ᵥ u) j)) (fun j => t (u j)) fun p => by
          rw [← map_mulVec' t H.ι]
          exact hC (H.ι *ᵥ p, H'.ι *ᵥ u, _) (Or.inr (Or.inr ⟨p, u, rfl⟩))
        rw [mulVec_add, mulVec_smul, dotProduct_add, dotProduct_smul, q1, q2, smul_zero, add_zero]
      · rw [← map_sgl t j, ej]
        funext i
        simp

end PositivityTheory.ThKCT

end
