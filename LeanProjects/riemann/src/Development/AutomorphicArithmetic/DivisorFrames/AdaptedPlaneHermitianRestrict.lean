import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocOpInfMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionMapsSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegrableIdelesPowerDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinPartNeZero
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.LemF
open scoped Classical

section SlopeTestRemainingChoices

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

private theorem schr_schr' {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (h : w.1 ⬝ᵥ w'.2 = w'.1 ⬝ᵥ w.2) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = schr ψ (w + w') φ := by
  funext x
  simp only [schr, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self 2
  simp only [dotProduct_add, add_dotProduct]
  linear_combination (⅟(2 : R)) * h - (w.1 ⬝ᵥ w'.2) * h2

private theorem rho_rho' {R : Type} [CommRing R] [Invertible (2 : R)] {V : Type} [AddCommGroup V] [Module R V]
    {Bf : V → V → R} {κ : Type} [Fintype κ] (d : Darboux Bf κ) (ψ : AddChar R ℂ) (w w' : V) (h : Bf w w' = 0)
    (φ : (κ → R) → ℂ) : d.rho ψ w (d.rho ψ w' φ) = d.rho ψ (w + w') φ := by
  simp only [Darboux.rho]
  rw [schr_schr', map_add]
  have := d.form w w'
  rw [h] at this
  exact sub_eq_zero.mp this.symm

private theorem om_rho {n d : ℕ} {X : Spc F E n} {W : Spc F E d} {M : Model σ X W} {ψ : AddChar (AF F) ℂ}
    (hψ : IsStd ψ) {χX χW : Chr F E} {om : Rep σ X W} (hW : M.IsWeil ψ χX χW om) {g : UA σ X.J}
    (hex : ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (g, 1)) f f₁)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho ψ (partInf F (mat g * u))) (locOpInf (om (g, 1)) f) =
      locOpInf (om (g, 1)) (locOpInf (M.co.rho ψ (partInf F u)) f) := by
  have hS := IsUWeilPair.isUSplitting hW
  have hact : actAB (cA σ) ((g, 1) : UA σ X.J × UA σ W.J) (partInf F u) = partInf F (mat g * u) := by
    change mat g * (partInf F u) * (mat (1 : UA σ W.J))ᵀ = _
    have h1 : mat (1 : UA σ W.J) = 1 := rfl
    rw [h1, Matrix.transpose_one, Matrix.mul_one, partInf, partInf, Matrix.mul_smul]
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  have h2 := hS.impl (g, 1) (partInf F u) _ (hr f).2
  rw [hact, (locOpInf_rho M.co hψ u f).1 r (hr _), acts_locOpInf (hex _) r (hr _), acts_locOpInf (hex _) r (hr _),
    (locOpInf_rho M.co hψ _ _).1 r (hr _)] at h2
  exact h2.symm

private theorem partInf_vec {n d : ℕ} (a : Fin n → AE F E) (w : Fin d → AE F E) :
    partInf F (Matrix.vecMulVec a w) = Matrix.vecMulVec (realAd F 1 • a) w := by
  rw [partInf, Matrix.smul_vecMulVec]

private theorem rho_add {B : Base F E} {n d d₁ j₀ j₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}
    (M : Model σ X W) {H' : Plane E d d₁} (hH' : H'.IsAdapted σ B W W₁ j₀ j₁) (hψ : IsStd B.ψ)
    (a b : Fin n → AE F E) (f : SInf F (Fin n × Fin d)) :
    locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec a (incV F H'.x))))
      (locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec b (incV F H'.x)))) f) =
    locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec (a + b) (incV F H'.x)))) f := by
  obtain ⟨r, h0, hr⟩ := exists_rest_inf F (Fin n × Fin d)
  refine DFunLike.coe_injective (eq_of_tens_inf h0 (hr f).1 ?_)
  rw [← (locOpInf_rho M.co hψ _ _).1 r (hr _), ← (locOpInf_rho M.co hψ _ _).1 r (hr _),
    ← (locOpInf_rho M.co hψ _ _).1 r (hr _), rho_rho']
  · rw [Matrix.add_vecMulVec, partInf, partInf, partInf, smul_add]
  · rw [partInf_vec, partInf_vec, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul, GlobalTheory.ArchUniq.Coord.vecMulVec_eq_mul]
    exact GlobalTheory.ArchUniq.Coord.sympM_eq_zero _ _ (GlobalTheory.ArchUniq.Coord.gram_xx hH') _ _

private theorem ei_inv {B : Base F E} {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {X₁ : Spc F E n₁} {W₁ : Spc F E d₁}
    {M : Model σ X W} {M₁ : Model σ X₁ W₁} (hψ : IsStd B.ψ) (hM : M.IsGood B.ψ) (hM₁ : M₁.IsGood B.ψ)
    {ι : Matrix (Fin n) (Fin n₁) E} {ι' : Matrix (Fin d) (Fin d₁) E} {I : Set (Matrix (Fin n) (Fin d) (AE F E))}
    {e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁} (he : IsEv B M M₁ ι ι' I e) {ei} {ev} (hL : IsLocPart M M₁ e ei ev)
    (u : Matrix (Fin n) (Fin d) (AE F E)) (hu : partInf F u ∈ I) (f : SInf F (Fin n × Fin d)) :
    ei (locOpInf (M.co.rho B.ψ (partInf F u)) f) = ei f := by
  have hSB : ∀ v, M.vac v ∈ SB _ := fun v => (hM.vac v).1
  have hei : ∀ f, e (pure f M.vac) = pure (ei f) M₁.vac := fun f => by
    rw [hL.2.2 f _ hSB (Eventually.of_forall fun _ => rfl)]
    exact congrArg _ (funext fun v => (hL.2.1 v).1)
  have hp := GlobalTheory.TensUniq.pure_mem_schA f _ hSB hM.std
  have h1 : M.co.rho B.ψ (partInf F u) (pure f M.vac) = pure (locOpInf (M.co.rho B.ψ (partInf F u)) f) M.vac :=
    (locOpInf_rho M.co hψ u f).1 _ ⟨fun x z hz => GlobalTheory.EvZeroInf.finPart_add _ x z hz, hp⟩
  refine GlobalTheory.EvZeroInf.eq_of_pure_eq _ (fun v => (hM₁.vac v).2.1) hM₁.std _ _ ?_
  rw [← hei, ← hei, ← h1]
  exact he.inv _ hu _ hp

private theorem span_herm {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (z : Fin n → E) :
    ∃ (s t : E) (u : Fin n₁ → E), z = s • H.x + H.ι *ᵥ u + t • H.y := by
  haveI := hS.lat
  let S : Submodule E (Fin n → E) :=
    Submodule.span E {H.x} ⊔ LinearMap.range (Matrix.mulVecLin H.ι) ⊔ Submodule.span E {H.y}
  have hle : Submodule.span E (X.L : Set (Fin n → E)) ≤ S := by
    rw [Submodule.span_le]
    intro z hz
    obtain ⟨s, t, u, -, -, -, rfl⟩ := hA.split z hz
    refine S.add_mem (S.add_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right ⟨u, rfl⟩)
    · exact Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _))
  have hz : z ∈ S := hle (by rw [Submodule.IsLattice.span_eq_top (A := E)]; trivial)
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hz
  obtain ⟨a₁, ha₁, a₂, ⟨u, rfl⟩, rfl⟩ := Submodule.mem_sup.1 ha
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.1 ha₁
  obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hb
  exact ⟨s, t, u, rfl⟩

private theorem span_ad {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (z : Fin n → AE F E) :
    ∃ (s t : AE F E) (u : Fin n₁ → AE F E), z = s • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y := by
  choose s t U hU using fun j : Fin n => span_herm hS hA (Pi.single j 1)
  refine ⟨∑ j, z j * inclR (F := F) (AF F) (s j), ∑ j, z j * inclR (F := F) (AF F) (t j),
    ∑ j, z j • incV F (U j), ?_⟩
  have h : ∀ j, (Pi.single j 1 : Fin n → AE F E) = inclR (F := F) (AF F) (s j) • incV F H.x +
      incM F H.ι *ᵥ incV F (U j) + inclR (F := F) (AF F) (t j) • incV F H.y := fun j => by
    funext a
    have := congrArg (inclR (F := F) (AF F)) (congrFun (hU j) a)
    rw [Pi.apply_single (fun _ => inclR (F := F) (E := E) (AF F)) (fun _ => map_zero _), map_one] at this
    rw [this]
    simp [incV, incM, Matrix.mulVec, dotProduct]
  rw [Matrix.mulVec_sum, Finset.sum_smul, Finset.sum_smul, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  conv_lhs => rw [pi_eq_sum_univ' z]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h j, Matrix.mulVec_smul, smul_add, smul_add, smul_smul, smul_smul]

omit [NumberField E] in
private theorem formA_inc {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E) :
    incV F x ⬝ᵥ (incM F J *ᵥ fun i => cA σ (incV F y i)) = inclR (F := F) (AF F) (form σ J x y) := by
  have h : ∀ a : E, cA σ (inclR (F := F) (AF F) a) = inclR (F := F) (AF F) (σ a) := fun a => rfl
  simp [incV, incM, form, Matrix.mulVec, dotProduct, h]

private theorem coef_eq {B : Base F E} {n n₁ r s i₀ i₁ : ℕ} {X : Spc F E n} {X₁ : Spc F E n₁} {H : Plane E n n₁}
    (hB : B.IsGood σ) (hS : X.IsHerm σ B r s) (hA : H.IsAdapted σ B X X₁ i₀ i₁) (a t : AE F E) (u : Fin n₁ → AE F E) :
    cA σ (incV F H.x ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i))) = t := by
  have hσ : ∀ z, σ (σ z) = z := fun z => by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact τ.injective (by rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star])
  have hc : ∀ z : AE F E, cA σ (cA σ z) = z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [cA, hσ]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hsym : ∀ x y : Fin n → E, form σ X.J y x = σ (form σ X.J x y) := fun x y => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hS.herm, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hu : incM F H.ι *ᵥ u = ∑ j, u j • incV F (H.ι *ᵥ Pi.single j 1) := by
    funext i
    simp [incV, incM, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
  have e : (fun i => cA σ ((a • incV F H.x + incM F H.ι *ᵥ u + t • incV F H.y) i)) =
      cA σ a • (fun i => cA σ (incV F H.x i)) + ∑ j, cA σ (u j) • (fun i => cA σ (incV F (H.ι *ᵥ Pi.single j 1) i)) +
        cA σ t • fun i => cA σ (incV F H.y i) := by
    funext i
    simp only [hu, Pi.add_apply, Pi.smul_apply, Finset.sum_apply, smul_eq_mul, map_add, map_mul, map_sum]
  have h0 : ∀ v, form σ X.J H.x (H.ι *ᵥ v) = 0 := fun v => by rw [hsym, (hA.orth v).1, map_zero]
  rw [e]
  simp only [Matrix.mulVec_add, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_add, dotProduct_sum, dotProduct_smul,
    formA_inc, hA.xx, hA.xy, h0, map_zero, map_one, smul_zero, Finset.sum_const_zero, zero_add, smul_eq_mul, mul_one, mul_zero, hc]

omit [NumberField E] in
private theorem unit_move {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (k : UA σ J) (x u : Fin n → AE F E) :
    (mat k⁻¹ *ᵥ x) ⬝ᵥ (incM F J *ᵥ fun i => cA σ (u i)) = x ⬝ᵥ (incM F J *ᵥ fun i => cA σ ((mat k *ᵥ u) i)) := by
  have hk : (mat k)ᵀ * incM F J * (mat k).map (cA σ) = incM F J := k.2
  have h1 : mat k * mat k⁻¹ = 1 := k.1.mul_inv
  have h2 : (fun i => cA σ ((mat k *ᵥ u) i)) = (mat k).map (cA σ) *ᵥ fun i => cA σ (u i) := by
    funext i
    simp [Matrix.mulVec, dotProduct]
  conv_lhs => arg 2; rw [← hk]
  rw [h2, Matrix.mul_assoc, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_mulVec]

end SlopeTestRemainingChoices

theorem UpperTheory.adapted_plane_hermitian_restrict :
    GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d n₁ d₁ r s i₀ i₁ j₀ j₁ : ℕ) (X : Spc F E n) (W : Spc F E d) (X₁ : Spc F E n₁) (W₁ : Spc F E d₁)
                 (M : Model σ X W) (M₁ : Model σ X₁ W₁) (H : Plane E n n₁) (H' : Plane E d d₁) (χX χW : Chr F E) (om : Rep σ X W),
                 B.IsGood σ → X.IsHerm σ B r s → H.IsAdapted σ B X X₁ i₀ i₁ → H'.IsAdapted σ B W W₁ j₀ j₁ → M.IsGood B.ψ → M₁.IsGood B.ψ →
                 M.IsWeil B.ψ χX χW om → ∀ e, IsEv B M M₁ H.ι H'.ι (isoB H H') e → ∀ ei ev, IsLocPart M M₁ e ei ev →
                 ∀ k ∈ UAt σ X (evI F), ∀ (u : Fin n → AE F E) (z : AE F E) (f : SInf F (Fin n × Fin d)),
                   ei (locOpInf (M.co.rho B.ψ (partInf F (cA σ z • Matrix.vecMulVec (incV F H.y) (incV F H'.x))))
                     (locOpInf (om (k, 1)) (locOpInf (M.co.rho B.ψ (partInf F (Matrix.vecMulVec u (incV F H'.x)))) f))) =
                   ei (locOpInf (M.co.rho B.ψ (partInf F (cA σ (z + (mat k⁻¹ *ᵥ incV F H.x) ⬝ᵥ (incM F X.J *ᵥ fun i => cA σ (u i))) •
                     Matrix.vecMulVec (incV F H.y) (incV F H'.x)))) (locOpInf (om (k, 1)) f)) := by
  intro hP F E _ _ _ _ _ σ B n d n₁ d₁ r s i₀ i₁ j₀ j₁ X W X₁ W₁ M M₁ H H' χX χW om hB hX hH hH' hM hM₁ hW e he ei ev hL
    k hk u z f
  have hex := GlobalTheory.ArchLocalityX.acts_arch_left hP F E σ _ _ _ _ M B.ψ _ _ om hB.cm hB.std hW k hk
  obtain ⟨a, t, v, hv⟩ := span_ad hX hH (mat k *ᵥ u)
  rw [← om_rho hB.std hW hex, Matrix.mul_vecMulVec, unit_move, map_add, hv, coef_eq hB hX hH, ← Matrix.smul_vecMulVec,
    ← Matrix.smul_vecMulVec, rho_add M hH' hB.std,
    show cA σ z • incV F H.y + (a • incV F H.x + incM F H.ι *ᵥ v + t • incV F H.y) =
      a • incV F H.x + (incM F H.ι *ᵥ v + (cA σ z + t) • incV F H.y) by rw [add_smul]; abel,
    ← rho_add M hH' hB.std, ei_inv hB.std hM hM₁ he hL, ← rho_add M hH' hB.std, ei_inv hB.std hM hM₁ he hL]
  · exact Or.inr ⟨realAd F 1 • v, by rw [partInf_vec, Matrix.mulVec_smul]⟩
  · exact Or.inl ⟨realAd F 1 • a • incV F H'.x, by
      rw [partInf, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, Matrix.vecMulVec_smul]⟩
