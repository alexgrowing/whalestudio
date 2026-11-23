import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRationalDarbouxHermitianTensorAdeles
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDotProductRepresentationCompactCharacterLo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGoodSchrodingerModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdaptedBasisHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRestrictionExtendByZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroSchwartzBruhatMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalLatticeImageOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeInvariantVectorLocalSupport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacuumVectorIffLatticeEigen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeCoordinateInjectionDarboux

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.PlaneEvX

theorem exists_extend_ne_zero {F : Type} [Field F] [NumberField F] (v : Pl F) {κ₁ κ G : Type} [Fintype κ₁] [Fintype κ]
    [AddCommGroup G] (ψ₀ : AddChar (Fv F v) ℂ) (hc : Continuous ψ₀) (hne : ψ₀ ≠ 1)
    (ℓ : G →+ (κ → Fv F v) × (κ → Fv F v)) (Γ : AddSubgroup G)
    (hopen : IsOpen ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))))
    (hcpt : IsCompact ((Γ.map ℓ : AddSubgroup ((κ → Fv F v) × (κ → Fv F v))) : Set ((κ → Fv F v) × (κ → Fv F v))))
    (hdual : ∀ w : (κ → Fv F v) × (κ → Fv F v), (∀ γ ∈ Γ, ψ₀ ((ℓ γ).1 ⬝ᵥ w.2 - w.1 ⬝ᵥ (ℓ γ).2) = 1) → w ∈ Γ.map ℓ)
    (j : κ₁ → κ) (hj : Function.Injective j) (χ : G → ℂ) (φ : (κ → Fv F v) → ℂ) (hφ : φ ≠ 0)
    (hE : ∀ γ ∈ Γ, schr ψ₀ (ℓ γ) φ = χ γ • φ)
    (hχ : ∀ γ ∈ Γ, (ℓ γ).1 = 0 → (∀ k, (ℓ γ).2 (j k) = 0) → χ γ = 1) :
    ∃ y, φ (Function.extend j y 0) ≠ 0 := by
  classical
  set Λ := Γ.map ℓ with hΛ
  have hψne : ∀ z, ψ₀ z ≠ 0 := fun z h => by
    have h0 := AddChar.map_zero_eq_one ψ₀
    rw [← add_neg_cancel z, AddChar.map_add_eq_mul, h, zero_mul] at h0
    exact zero_ne_one h0
  have hpt : ∀ γ ∈ Γ, ∀ x, ψ₀ (x ⬝ᵥ (ℓ γ).2 + ⅟(2 : Fv F v) * ((ℓ γ).1 ⬝ᵥ (ℓ γ).2)) * φ (x + (ℓ γ).1)
        = χ γ * φ x := fun γ hγ x => congrFun (hE γ hγ) x
  obtain ⟨x, hx⟩ := Function.ne_iff.1 hφ
  replace hx : φ x ≠ 0 := hx
  set t : κ → Fv F v := x - Function.extend j (x ∘ j) 0 with ht
  have hdot : ∀ (c : κ₁ → Fv F v) (b : κ → Fv F v), Function.extend j c 0 ⬝ᵥ b = c ⬝ᵥ (b ∘ j) := fun c b => by
    simp only [dotProduct]
    refine (Fintype.sum_of_injective j hj _ _ (fun k hk => ?_) (fun i => ?_)).symm
    · have h : ¬ ∃ x, j x = k := fun ⟨x, hx⟩ => hk ⟨x, hx⟩
      simp [Function.extend_apply' _ _ _ h]
    · simp [hj.extend_apply]
  have htj : t ∘ j = 0 := funext fun k => by simp [ht, hj.extend_apply]
  have h0 : ∀ b : κ → Fv F v, ((0 : κ → Fv F v), b) ∈ Λ → b ∘ j = 0 → ψ₀ (t ⬝ᵥ b) = 1 := by
    intro b hb hbj
    obtain ⟨γ, hγ, hℓ⟩ := AddSubgroup.mem_map.1 hb
    have e := hpt γ hγ x
    rw [hχ γ hγ (by rw [hℓ]) (fun k => by rw [hℓ]; exact congrFun hbj k), hℓ] at e
    simp only [zero_dotProduct, mul_zero, add_zero] at e
    rw [ht, sub_dotProduct, hdot, hbj, dotProduct_zero, sub_zero]
    exact mul_right_cancel₀ hx e
  let p : (κ → Fv F v) × (κ → Fv F v) →+ (κ ⊕ κ₁ → Fv F v) :=
    { toFun := fun a => Sum.elim a.1 (a.2 ∘ j)
      map_zero' := by funext k; rcases k with k | k <;> rfl
      map_add' := fun a b => by funext k; rcases k with k | k <;> rfl }
  have hp1 : ∀ a, p a ∘ Sum.inl = a.1 := fun _ => rfl
  have hp2 : ∀ a, p a ∘ Sum.inr = a.2 ∘ j := fun _ => rfl
  have hwd : ∀ a ∈ Λ, ∀ b ∈ Λ, p a = p b → ψ₀ (t ⬝ᵥ a.2) = ψ₀ (t ⬝ᵥ b.2) := by
    intro a ha b hb hab
    have h1 : a.1 = b.1 := by rw [← hp1, hab, hp1]
    have h2 : a.2 ∘ j = b.2 ∘ j := by rw [← hp2, hab, hp2]
    have hd : ((0 : κ → Fv F v), a.2 - b.2) ∈ Λ := by
      have hs := Λ.sub_mem ha hb
      convert hs using 1
      ext <;> simp [h1]
    have e := h0 _ hd (by funext k; simpa [sub_eq_zero] using congrFun h2 k)
    rw [dotProduct_sub, AddChar.map_sub_eq_div, div_eq_one_iff_eq (hψne _)] at e
    exact e
  let q : (κ ⊕ κ₁ → Fv F v) →+ (κ → Fv F v) × (κ → Fv F v) :=
    { toFun := fun y => (y ∘ Sum.inl, Function.extend j (y ∘ Sum.inr) 0)
      map_zero' := by
        refine Prod.ext rfl ?_
        funext k
        by_cases h : ∃ a, j a = k
        · obtain ⟨a, rfl⟩ := h
          simp [hj.extend_apply]
        · simp [Function.extend_apply' _ _ _ h]
      map_add' := fun a b => Prod.ext rfl (GlobalTheory.VacRestr.ext_add hj (a ∘ Sum.inr) (b ∘ Sum.inr)).symm }
  have hq : ∀ y, q y = (y ∘ Sum.inl, Function.extend j (y ∘ Sum.inr) 0) := fun _ => rfl
  let c' : (κ ⊕ κ₁ → Fv F v) → ℂ := fun y =>
    if h : ∃ a ∈ Λ, p a = y then ψ₀ (t ⬝ᵥ (Classical.choose h).2) else 1
  have hc' : ∀ a ∈ Λ, c' (p a) = ψ₀ (t ⬝ᵥ a.2) := by
    intro a ha
    have h : ∃ b ∈ Λ, p b = p a := ⟨a, ha, rfl⟩
    simp only [c', dif_pos h]
    obtain ⟨hb, hb1⟩ := Classical.choose_spec h
    exact hwd _ hb _ ha hb1
  have hpc : Continuous p := by
    refine continuous_pi fun k => ?_
    rcases k with k | k
    · exact (continuous_apply k).comp continuous_fst
    · exact (continuous_apply (j k)).comp continuous_snd
  have hqc : Continuous q := by
    refine Continuous.prodMk (continuous_pi fun k => continuous_apply _) (continuous_pi fun k => ?_)
    by_cases h : ∃ a, j a = k
    · obtain ⟨a, rfl⟩ := h
      simp only [hj.extend_apply]
      exact continuous_apply _
    · simp only [Function.extend_apply' _ _ _ h]
      exact continuous_const
  obtain ⟨u, hu⟩ := GlobalTheory.CompactCharDual.exists_dotProduct_eq_local v ψ₀ hc hne (Λ.map p)
    (by rw [AddSubgroup.coe_map]; exact hcpt.image hpc) (Λ.comap q)
    (by rw [AddSubgroup.coe_comap]; exact hopen.preimage hqc) c'
    (by
      intro y hy y' hy'
      obtain ⟨a, ha, rfl⟩ := AddSubgroup.mem_map.1 hy
      obtain ⟨b, hb, rfl⟩ := AddSubgroup.mem_map.1 hy'
      rw [← map_add, hc' _ (Λ.add_mem ha hb), hc' a ha, hc' b hb, Prod.snd_add, dotProduct_add, AddChar.map_add_eq_mul])
    (by
      intro y _ hy'
      have hy'' : q y ∈ Λ := hy'
      have hpq : p (q y) = y := by
        funext k
        rcases k with k | k
        · rfl
        · exact hj.extend_apply _ _ k
      have e := hc' _ hy''
      rw [hpq, hq, dotProduct_comm, hdot, htj, dotProduct_zero, AddChar.map_zero_eq_one] at e
      exact e)
  have hw : (t - Function.extend j (u ∘ Sum.inr) 0, u ∘ Sum.inl) ∈ Λ := by
    refine hdual _ fun γ hγ => ?_
    have hlam : ℓ γ ∈ Λ := AddSubgroup.mem_map_of_mem ℓ hγ
    have h1 := hu _ (AddSubgroup.mem_map_of_mem p hlam)
    rw [hc' _ hlam] at h1
    have h2 : u ⬝ᵥ p (ℓ γ) = (ℓ γ).1 ⬝ᵥ (u ∘ Sum.inl) + (u ∘ Sum.inr) ⬝ᵥ ((ℓ γ).2 ∘ j) := by
      rw [dotProduct_comm (ℓ γ).1]
      simp only [dotProduct, Fintype.sum_sum_type]
      rfl
    show ψ₀ ((ℓ γ).1 ⬝ᵥ (u ∘ Sum.inl) - (t - Function.extend j (u ∘ Sum.inr) 0) ⬝ᵥ (ℓ γ).2) = 1
    rw [sub_dotProduct, hdot, show ∀ a b c : Fv F v, a - (b - c) = (a + c) - b from fun a b c => by ring, ← h2,
      AddChar.map_sub_eq_div, h1, div_self (hψne _)]
  obtain ⟨γ, hγ, hℓ⟩ := AddSubgroup.mem_map.1 hw
  refine ⟨x ∘ j + u ∘ Sum.inr, fun h => ?_⟩
  have e := hpt γ hγ (Function.extend j (x ∘ j + u ∘ Sum.inr) 0)
  rw [h, mul_zero, hℓ, ← GlobalTheory.VacRestr.ext_add hj, ht] at e
  simp only [add_add_sub_cancel, add_sub_cancel] at e
  exact mul_ne_zero (hψne _) hx e

theorem det_compl_ne_zero {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (n₁ : ℕ)
    (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hσ : ∀ a, σ (σ a) = a) (hJ : ∀ i j, σ (J j i) = J i j) (hdet : J.det ≠ 0) (hxx : form σ J x x = 0)
    (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hι : Function.Injective ι.mulVec) :
    (ιᵀ * J * ι.map σ).det ≠ 0 := by
  have hsym : ∀ a b, form σ J b a = σ (form σ J a b) := fun a b => by
    simp only [form, dotProduct, Matrix.mulVec, map_sum, map_mul, hσ, hJ, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
  have hyx : form σ J y x = 1 := by rw [hsym, hxy, map_one]
  have hlin : ∀ (a b c d : Fin (n₁ + 2) → E) (s t : E),
      form σ J (a + s • b + t • c) d = form σ J a d + s * form σ J b d + t * form σ J c d := fun a b c d s t => by
    simp only [form, add_dotProduct, smul_dotProduct, smul_eq_mul]
  let P : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E := Matrix.of fun r c =>
    Fin.addCases (motive := fun _ => E) (fun i => ι r i) (fun t => ![x r, y r] t) c
  have hP : ∀ c : Fin (n₁ + 2) → E, P *ᵥ c =
      ι *ᵥ (fun i => c (Fin.castAdd 2 i)) + c (Fin.natAdd n₁ 0) • x + c (Fin.natAdd n₁ 1) • y := fun c => by
    funext r
    simp [P, Matrix.mulVec, dotProduct, Fin.sum_univ_add]
    ring
  have hPinj : Function.Injective P.mulVec := by
    refine (injective_iff_map_eq_zero P.mulVecLin).2 fun c hc => ?_
    rw [Matrix.mulVecLin_apply, hP] at hc
    have h0 : ∀ d, form σ J 0 d = 0 := fun d => by simp [form]
    have h1 := hlin (ι *ᵥ (fun i => c (Fin.castAdd 2 i))) x y y (c (Fin.natAdd n₁ 0)) (c (Fin.natAdd n₁ 1))
    have h2 := hlin (ι *ᵥ (fun i => c (Fin.castAdd 2 i))) x y x (c (Fin.natAdd n₁ 0)) (c (Fin.natAdd n₁ 1))
    rw [hc, h0, (horth _).2, hxy, hyy, zero_add, mul_one, mul_zero, add_zero] at h1
    rw [hc, h0, (horth _).1, hxx, hyx, zero_add, mul_one, mul_zero, zero_add] at h2
    rw [← h1, ← h2, zero_smul, zero_smul, add_zero, add_zero] at hc
    have h3 : (fun i => c (Fin.castAdd 2 i)) = 0 := hι (by rw [hc, Matrix.mulVec_zero])
    funext k
    refine Fin.addCases (fun i => congrFun h3 i) (fun t => ?_) k
    fin_cases t
    · exact h1.symm
    · exact h2.symm
  have hPsurj : Function.Surjective P.mulVec :=
    (LinearMap.injective_iff_surjective (f := P.mulVecLin)).1 hPinj
  intro h0
  obtain ⟨u, hu0, hu⟩ := Matrix.exists_vecMul_eq_zero_iff.2 h0
  have hall : ∀ w, form σ J (ι *ᵥ u) w = 0 := fun w => by
    obtain ⟨c, rfl⟩ := hPsurj w
    rw [hsym, hP, hlin, (hsym (ι *ᵥ u) x), hsym (ι *ᵥ u) y, (horth u).1, (horth u).2, hsym (ι *ᵥ u)]
    have : form σ J (ι *ᵥ u) (ι *ᵥ fun i => c (Fin.castAdd 2 i)) =
        (u ᵥ* (ιᵀ * J * ι.map σ)) ⬝ᵥ fun i => σ (c (Fin.castAdd 2 i)) := by
      have e : (fun i => σ ((ι *ᵥ fun i => c (Fin.castAdd 2 i)) i)) = ι.map σ *ᵥ fun i => σ (c (Fin.castAdd 2 i)) := by
        funext i
        simp [Matrix.mulVec, dotProduct]
      rw [form, e, ← Matrix.dotProduct_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
        Matrix.dotProduct_mulVec u, Matrix.vecMul_transpose]
    rw [this, hu]
    simp
  have hz : (ι *ᵥ u) ᵥ* J = 0 := by
    funext k
    have := hall (Pi.single k 1)
    rw [form, Matrix.dotProduct_mulVec] at this
    have e : (fun i => σ ((Pi.single k 1 : Fin (n₁ + 2) → E) i)) = Pi.single k 1 := by
      funext i
      by_cases h : i = k
      · subst h; simp
      · simp [Pi.single_eq_of_ne h]
    rw [e, dotProduct_single, mul_one] at this
    exact this
  exact hu0 (hι (by rw [Matrix.eq_zero_of_vecMul_eq_zero hdet hz, Matrix.mulVec_zero]))

open GlobalTheory.AdaptedDarboux in

theorem exists_plane_darboux {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (n₁ d : ℕ) (J : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) (J₁ : Matrix (Fin n₁) (Fin n₁) E) (K : Matrix (Fin d) (Fin d) E)
    (x y : Fin (n₁ + 2) → E) (ι : Matrix (Fin (n₁ + 2)) (Fin n₁) E)
    (hσ : ∀ a, σ (σ a) = a) (h2' : Module.finrank F E = 2) (hJ : ∀ i j, σ (J j i) = J i j) (hK : ∀ i j, σ (K j i) = -K i j)
    (hJ₁ : J₁.det ≠ 0) (hK' : K.det ≠ 0) (hxx : form σ J x x = 0) (hyy : form σ J y y = 0) (hxy : form σ J x y = 1)
    (horth : ∀ u, form σ J (ι *ᵥ u) x = 0 ∧ form σ J (ι *ᵥ u) y = 0) (hgram : ιᵀ * J * ι.map σ = J₁)
    (co₁ : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J₁) (incM F K)) (Fin n₁ × Fin d))
    (hrat : ∀ m : Matrix (Fin n₁) (Fin d) E, ∃ a b : Fin n₁ × Fin d → F,
      co₁.e (incM F m) = (fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i))) :
    ∃ (j : Fin n₁ × Fin d → Fin (n₁ + 2) × Fin d)
      (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K)) (Fin (n₁ + 2) × Fin d)),
      Function.Injective j ∧
      (∀ m : Matrix (Fin (n₁ + 2)) (Fin d) E, ∃ a b : Fin (n₁ + 2) × Fin d → F,
        co.e (incM F m) = (fun i => algebraMap F (AF F) (a i), fun i => algebraMap F (AF F) (b i))) ∧
      (∀ z, co.e (incM F ι * z) = (Function.extend j (co₁.e z).1 0, Function.extend j (co₁.e z).2 0)) ∧
      (∀ z, (co.e (Matrix.vecMulVec (incV F x) z)).1 = 0 ∧ ∀ k, (co.e (Matrix.vecMulVec (incV F x) z)).2 (j k) = 0) ∧
      (∀ w, (co.e w).1 = 0 → (∀ k, (co.e w).2 (j k) = 0) → ∃ z, w = Matrix.vecMulVec (incV F x) z) := by
  obtain ⟨p, q, hpq, hpq', hpr, hqr⟩ := GlobalTheory.T.quadratic_extension_symplectic_coordinates σ d K hσ h2' hK hK'
  let P : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E := Matrix.of fun r c =>
    Fin.addCases (motive := fun _ => E) (fun i => ι r i) (fun t => ![x r, y r] t) c
  have hPι : ∀ r i, P r (Fin.castAdd 2 i) = ι r i := fun r i => by simp [P]
  have hPx : ∀ r, P r (Fin.natAdd n₁ 0) = x r := fun r => by simp [P]
  have hPy : ∀ r, P r (Fin.natAdd n₁ 1) = y r := fun r => by simp [P]
  obtain ⟨hPdet, hG1, hG2, hG3, hG00, hG11, hG01, hG10⟩ :=
    GlobalTheory.T.hyperbolic_pair_splitting_matrix σ n₁ J J₁ x y ι P hσ hJ hJ₁ hxx hyy hxy horth hgram hPι hPx hPy
  have hPQ : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P (Ne.isUnit hPdet)
  have hQP : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P (Ne.isUnit hPdet)
  have hinc : ∀ {a b c : ℕ} (U : Matrix (Fin a) (Fin b) E) (V : Matrix (Fin b) (Fin c) E),
      incM F (U * V) = incM F U * incM F V := fun U V => Matrix.map_mul
  have hinc1 : incM F (1 : Matrix (Fin (n₁ + 2)) (Fin (n₁ + 2)) E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h1 : incM F P * incM F P⁻¹ = 1 := by rw [← hinc, hPQ, hinc1]
  have h2 : incM F P⁻¹ * incM F P = 1 := by rw [← hinc, hQP, hinc1]
  let e := (mulLeft (R := AF F) (d := d) (incM F P⁻¹) (incM F P) h1 h2).trans (glue co₁.e p q)
  have he : ∀ w', e w' = glue co₁.e p q (incM F P⁻¹ * w') := fun _ => rfl
  have hrow : ∀ (Z : Matrix (Fin (n₁ + 2)) (Fin d) E) r, incM F Z r = incV F (Z r) := fun _ _ => rfl
  have hembι : ∀ z : Matrix (Fin n₁) (Fin d) (AE F E), incM F ι * z = incM F P * AdaptedDarboux.emb z 0 0 := fun z => by
    ext r l
    simp [Matrix.mul_apply, Fin.sum_univ_add, AdaptedDarboux.emb, incM, hPι]
  have hembx : ∀ z : Fin d → AE F E,
      Matrix.vecMulVec (incV F x) z = incM F P * AdaptedDarboux.emb (0 : Matrix (Fin n₁) (Fin d) (AE F E)) z 0 := fun z => by
    ext r l
    simp [Matrix.mul_apply, Fin.sum_univ_add, AdaptedDarboux.emb, incM, incV, hPx, Matrix.vecMulVec_apply]
  have hback : ∀ Z : Matrix (Fin (n₁ + 2)) (Fin d) (AE F E), incM F P⁻¹ * (incM F P * Z) = Z := fun Z => by
    rw [← Matrix.mul_assoc, h2, Matrix.one_mul]
  have hG : (incM F P)ᵀ * incM F J * (incM F P).map (cA σ) = incM F (Pᵀ * J * P.map σ) := by
    rw [hinc, hinc]; rfl
  have key : ∀ z z' : Matrix (Fin (n₁ + 2)) (Fin d) (AE F E),
      symp (R := AF F) (cA σ) (-1) (incM F J) (incM F K) (incM F P * z) (incM F P * z') =
        (e (incM F P * z)).1 ⬝ᵥ (e (incM F P * z')).2 - (e (incM F P * z')).1 ⬝ᵥ (e (incM F P * z)).2 := fun z z' => by
    rw [he, he, hback, hback, glue_form co₁.e p q _ co₁.form, GlobalTheory.T.symplectic_form_base_change_matrix, hG,
      GlobalTheory.T.hermitian_block_decomposition_hyperbolic σ n₁ d _ J₁ K hG1 hG2 hG3 hG00 hG11 hG01 hG10 z z', hpq (z' (Fin.natAdd n₁ 0)) (z (Fin.natAdd n₁ 1)),
      hpq' (z (Fin.natAdd n₁ 0)) (z' (Fin.natAdd n₁ 1)), map_neg]
    simp only [top]
    ring
  have hnot : ∀ (t : Fin 2) (l : Fin d), ¬∃ k : Fin n₁ × Fin d, (Fin.castAdd 2 k.1, k.2) = (Fin.natAdd n₁ t, l) := by
    rintro t l ⟨k, hk⟩
    have := congrArg (fun x => x.1.val) hk
    simp at this
    omega
  have hinj : Function.Injective (fun k : Fin n₁ × Fin d => (Fin.castAdd 2 k.1, k.2)) := fun k k' h => by
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (Fin.castAdd_injective _ _ h.1) h.2
  have hext : ∀ f : Fin n₁ × Fin d → AF F,
      comb f 0 = Function.extend (fun k : Fin n₁ × Fin d => (Fin.castAdd 2 k.1, k.2)) f 0 := fun f => by
    refine comb_ext (fun i l => ?_) (fun t l => ?_)
    · rw [comb_castAdd]; exact (hinj.extend_apply f 0 (i, l)).symm
    · rw [comb_natAdd, Function.extend_apply' _ _ _ (hnot t l)]; rfl
  refine ⟨fun k => (Fin.castAdd 2 k.1, k.2), ⟨e, fun w₁ w₂ => ?_⟩, hinj, fun m => ?_, fun z => ?_, fun z => ?_, fun w hw1 hw2 => ?_⟩
  · have := key (incM F P⁻¹ * w₁) (incM F P⁻¹ * w₂)
    rwa [← Matrix.mul_assoc, h1, Matrix.one_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul] at this
  · rw [he, ← hinc, glue_apply]
    obtain ⟨y₁, z₁, hM⟩ := hrat (top (P⁻¹ * m))
    obtain ⟨a, ha⟩ := hqr ((P⁻¹ * m) (Fin.natAdd n₁ 1))
    obtain ⟨b, hb⟩ := hpr ((P⁻¹ * m) (Fin.natAdd n₁ 0))
    refine ⟨comb y₁ a, comb z₁ b, ?_⟩
    rw [show top (incM F (P⁻¹ * m)) = incM F (top (P⁻¹ * m)) from rfl, hM, hrow, hrow, ha, hb]
    ext k <;> rcases k with ⟨i, l⟩ <;> refine Fin.addCases (fun i => ?_) (fun t => ?_) i <;> simp
  · rw [he, hembι, hback, glue_apply, top_emb, emb_zero, emb_one, map_zero, map_zero, hext, hext]
  · rw [he, hembx, hback, glue_apply, top_emb, emb_zero, emb_one, map_zero, map_zero]
    refine ⟨?_, fun k => ?_⟩
    · exact comb_ext (fun i l => by simp) (fun t l => by simp)
    · simp
  · change (e w).1 = 0 at hw1
    change ∀ k : Fin n₁ × Fin d, (e w).2 (Fin.castAdd 2 k.1, k.2) = 0 at hw2
    rw [he, glue_apply] at hw1 hw2
    have a1 : (co₁.e (top (incM F P⁻¹ * w))).1 = 0 := funext fun k => by
      simpa using congrFun hw1 (Fin.castAdd 2 k.1, k.2)
    have a2 : (co₁.e (top (incM F P⁻¹ * w))).2 = 0 := funext fun k => by simpa using hw2 k
    have a3 : q ((incM F P⁻¹ * w) (Fin.natAdd n₁ 1)) = 0 := funext fun k => by
      simpa using congrFun hw1 (Fin.natAdd n₁ k.1, k.2)
    have b1 : top (incM F P⁻¹ * w) = 0 := co₁.e.map_eq_zero_iff.1 (Prod.ext a1 a2)
    have b3 : (incM F P⁻¹ * w) (Fin.natAdd n₁ 1) = 0 := q.map_eq_zero_iff.1 a3
    refine ⟨(incM F P⁻¹ * w) (Fin.natAdd n₁ 0), ?_⟩
    rw [hembx]
    have : AdaptedDarboux.emb (0 : Matrix (Fin n₁) (Fin d) (AE F E)) ((incM F P⁻¹ * w) (Fin.natAdd n₁ 0)) 0 = incM F P⁻¹ * w := by
      ext r l
      refine Fin.addCases (fun i => ?_) (fun t => ?_) r
      · have := congrFun (congrFun b1 i) l
        simp only [top, Matrix.of_apply, Matrix.zero_apply] at this
        simp [AdaptedDarboux.emb, this]
      · fin_cases t
        · simp [AdaptedDarboux.emb]
        · have := congrFun b3 l
          simp only [Pi.zero_apply] at this
          simp [AdaptedDarboux.emb, this]
    rw [this, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem eq_zero_of_at {F : Type} [Field F] [NumberField F] (v : Pl F) (a : AF F) (h : At (evFin F v) a)
    (h0 : evFin F v a = 0) : a = 0 := by
  have h1 := h (1 - GlobalTheory.LatVac.liftV v 1) (by rw [map_sub, map_one, GlobalTheory.LatVac.evFin_liftV, sub_self])
  have h2 := GlobalTheory.LatVac.at_liftV v 1 a h0
  rw [smul_eq_mul] at h1 h2
  linear_combination h1 + h2

theorem isVac_restrict {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (B : Base F E) {n d n₁ : ℕ} (X : Spc F E n) (W : Spc F E d) (r s r' s' : ℕ) (hB : B.IsGood σ) (hX : X.IsHerm σ B r s)
    (hW : W.IsSkew σ B r' s') (X₁ : Spc F E n₁) (x : Fin n → E) (ι : Matrix (Fin n) (Fin n₁) E) (hxx : form σ X.J x x = 0)
    (hgram : ιᵀ * X.J * ι.map σ = X₁.J) (hlow : ∀ u, u ∈ X₁.L ↔ ι *ᵥ u ∈ X.L) (M₁ : Model σ X₁ W)
    (j : Fin n₁ × Fin d → Fin n × Fin d)
    (co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d)) (hj : Function.Injective j)
    (hco : ∀ z, co.e (incM F ι * z) = (Function.extend j (M₁.co.e z).1 0, Function.extend j (M₁.co.e z).2 0))
    (hI : ∀ w, (co.e w).1 = 0 → (∀ k, (co.e w).2 (j k) = 0) → ∃ z, w = Matrix.vecMulVec (incV F x) z)
    (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (hφ : (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v φ) :
    M₁.IsVac B.ψ v (fun y => φ (Function.extend j y 0)) := by
  obtain ⟨hsb, hφ0, θ, hθ, heig⟩ := (GlobalTheory.VacLocEig.isVac_iff_loc _ B.ψ v φ).1 hφ
  refine (GlobalTheory.VacLocEig.isVac_iff_loc M₁ B.ψ v _).2 ⟨?_, ?_, θ, hθ, fun z hz => ?_⟩
  · rw [← GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero F j hj v]
    exact Submodule.mem_map_of_mem hsb
  · obtain ⟨oc, ooc⟩ := GlobalTheory.LatOpenCptAny.main σ B X W r s r' s' hX hW co v
    obtain ⟨y, hy⟩ := exists_extend_ne_zero v (GlobalTheory.LatVac.psiAt B.ψ v) (GlobalTheory.VacAny.continuous_psiV hB.std.1 v)
      (GlobalTheory.PsiNontriv.psiAt_ne_one B.ψ hB.std v) (GlobalTheory.LatVac.locCo co v) (latAtV X W v) oc ooc
      (fun w hw => GlobalTheory.LatSelfDualCo.latAtV_selfDual_locCo F E σ B n d X W r s r' s' hB hX hW co v w hw) j hj _ φ hφ0 heig
      (fun γ hγ h1 h2 => by
        have hat := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγ
        have hat' : ∀ u, evFin F v u = 0 → u • co.e γ = 0 := fun u hu => by rw [← map_smul, hat u hu, map_zero]
        obtain ⟨z, rfl⟩ := hI γ
          (funext fun k => eq_zero_of_at v _ (fun u hu => congrFun (congrArg Prod.fst (hat' u hu)) k) (congrFun h1 k))
          (fun k => eq_zero_of_at v _ (fun u hu => congrFun (congrArg Prod.snd (hat' u hu)) (j k)) (h2 k))
        rw [GlobalTheory.VacResNonvan.symp_vecMulVec_self_eq_zero F E σ X.J W.J _ x hxx, mul_zero, AddChar.map_zero_eq_one])
    exact fun h => hy (congrFun h y)
  · have hγ := GlobalTheory.VacRestr.mul_mem_latAtV X W X₁ ι hlow v z hz
    have hloc : GlobalTheory.LatVac.locCo co v (incM F ι * z) =
        (Function.extend j (GlobalTheory.LatVac.locCo M₁.co v z).1 0, Function.extend j (GlobalTheory.LatVac.locCo M₁.co v z).2 0) := by
      simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, hco]
      exact Prod.ext (GlobalTheory.VacRestr.ext_map hj _ (map_zero _) _) (GlobalTheory.VacRestr.ext_map hj _ (map_zero _) _)
    have htw : symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X.J) (incM F W.J) (incM F ι * z) (incM F ι * z) =
        symp (R := AF F) (cA σ) (inclR (F := F) (AF F) (θ : E)) (incM F X₁.J) (incM F W.J) z z := by
      rw [GlobalTheory.symp_mul_left, GlobalTheory.VacRestr.cA_incM, ← hgram]
      congr 1
      simp only [incM]
      rw [← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul]
    funext y
    have h := congrFun (heig _ hγ) (Function.extend j y 0)
    rw [hloc, htw] at h
    simp only [schr, Pi.smul_apply, smul_eq_mul] at h ⊢
    rwa [GlobalTheory.VacRestr.ext_dot hj, GlobalTheory.VacRestr.ext_dot hj, GlobalTheory.VacRestr.ext_add hj] at h

theorem std_extend {F : Type} [Field F] [NumberField F] {κ₁ κ : Type} {j : κ₁ → κ} (hj : Function.Injective j) (v : Pl F) :
    (fun y : κ₁ → Fv F v => Set.indicator {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ → Fv F v) → ℂ)
      (Function.extend j y 0)) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} (1 : (κ₁ → Fv F v) → ℂ) := by
  funext y
  have key : (∀ i, Function.extend j y 0 i ∈ v.adicCompletionIntegers F) ↔ ∀ i, y i ∈ v.adicCompletionIntegers F := by
    constructor
    · intro h i
      simpa [hj.extend_apply] using h (j i)
    · intro h k
      by_cases hk : ∃ a, j a = k
      · obtain ⟨a, rfl⟩ := hk
        simpa [hj.extend_apply] using h a
      · simp [Function.extend_apply' _ _ _ hk]
  by_cases hy : ∀ i, y i ∈ v.adicCompletionIntegers F
  · rw [Set.indicator_of_mem (show y ∈ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_mem (show Function.extend j y 0 ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from key.2 hy)]
    rfl
  · rw [Set.indicator_of_notMem (show y ∉ {x : κ₁ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hy),
      Set.indicator_of_notMem (show Function.extend j y 0 ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from
        fun h => hy (key.1 h))]

theorem extend_dot_zero {α β R : Type} [Fintype α] [Fintype β] {j : α → β} [CommRing R] (y : α → R) (q : β → R)
    (hq : ∀ k, q (j k) = 0) : Function.extend j y 0 ⬝ᵥ q = 0 := by
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases h : ∃ x, j x = k
  · obtain ⟨x, rfl⟩ := h
    simp [hq]
  · simp [Function.extend_apply' _ _ _ h]

theorem exists_model_isEv : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E)
    (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (d₂ : ℕ) (H : Plane E a d₂), (d₂ + 2 = a ∧ form σ G.V.J H.x H.x = 0 ∧ form σ G.V.J H.y H.y = 0 ∧ form σ G.V.J H.x H.y = 1 ∧
          (∀ u, form σ G.V.J (H.ι *ᵥ u) H.x = 0 ∧ form σ G.V.J (H.ι *ᵥ u) H.y = 0) ∧ Function.Injective H.ι.mulVec) →
      ∃ (V₁ : Spc F E d₂) (M₁ : Model σ V₁ G.W) (e : Fn F a (a + a') →ₗ[ℂ] Fn F d₂ (a + a')),
        V₁.J = H.ιᵀ * G.V.J * H.ι.map σ ∧ M₁.IsGood B.ψ ∧ IsEv B G.M M₁ H.ι 1 {u | ∃ z, u = Matrix.vecMulVec (incV F H.x) z} e := by
  intro _ F E _ _ _ _ _ σ B a a' G X om om' hT d₂ H ⟨hrk, hxx, hyy, hxy, horth, hιinj⟩
  classical
  subst hrk
  have hB := hT.base
  have hV := hT.geo.hV
  have hW := hT.geo.hW
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hσ : ∀ x, σ (σ x) = x := fun x => by
    apply ((B.emb w).1 : E →+* ℂ).injective
    rw [hB.cm.2.2.2, hB.cm.2.2.2, star_star]
  have hV' : G.V.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hV.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det G.V.J
    rw [h0, map_zero] at this
    exact this.symm
  have hW' : G.W.J.det ≠ 0 := fun h0 => by
    apply GlobalTheory.RatDarboux.det_ne_zero_of_isCartan (hW.cartan w)
    have := ((B.emb w).1 : E →+* ℂ).map_det G.W.J
    rw [h0, map_zero] at this
    rw [Matrix.det_smul]
    exact mul_eq_zero_of_right _ this.symm
  have hJ₁ := det_compl_ne_zero σ d₂ G.V.J H.x H.y H.ι hσ hV.herm hV' hxx hyy hxy horth hιinj
  have hherm : ∀ i k, σ ((H.ιᵀ * G.V.J * H.ι.map σ) k i) = (H.ιᵀ * G.V.J * H.ι.map σ) i k := fun i k => by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum, map_mul, hσ, hV.herm, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  let V₁ : Spc F E d₂ := ⟨H.ιᵀ * G.V.J * H.ι.map σ, G.V.L.comap (H.ι.mulVecLin.restrictScalars (𝓞 E)), fun _ => 1, fun _ => 1⟩
  obtain ⟨co₁, hrat₁⟩ := GlobalTheory.RatDarboux.exists_darboux (AF F) hB.cm.2.2.1 σ hσ hherm hW.skew hJ₁ hW'
  obtain ⟨j, co, hj, hrat, hι, hx, hI⟩ := exists_plane_darboux σ d₂ _ G.V.J _ G.W.J H.x H.y H.ι hσ hB.cm.2.2.1 hV.herm hW.skew
    hJ₁ hW' hxx hyy hxy horth rfl co₁ hrat₁
  obtain ⟨e₁, ei₁, ev₁, hsurj, hmaps, hheis, hSB, hvac, hstd, hpure⟩ :=
    GlobalTheory.T.darboux_coordinates_good_model F E σ B _ _ G.V G.W G.M _ _ _ _ hB hV hW hT.geo.hM co hrat
  obtain ⟨μ, 𝓕, hμ, h𝓕⟩ := GlobalTheory.ModelEx.exists_haar_fundDom F E σ d₂ V₁.J
  let M₁ : Model σ V₁ G.W := ⟨co₁, fun v y => ev₁ v (G.M.vac v) (Function.extend j y 0), μ, 𝓕⟩
  obtain ⟨R, hR⟩ := GlobalTheory.RestrS.exists_restr F j hj
  refine ⟨V₁, M₁, LinearMap.funLeft ℂ ℂ (fun y : Fin d₂ × Fin (d₂ + 2 + a') → AF F => Function.extend j y 0) ∘ₗ e₁, rfl,
    ⟨hrat₁, fun v => ?_, ?_, hμ, h𝓕⟩, ⟨?_, ?_, ?_, ?_⟩⟩
  · exact isVac_restrict σ B G.V G.W _ _ _ _ hB hV hW V₁ H.x H.ι hxx rfl (fun u => Iff.rfl) M₁ j co hj hι hI v _ (hvac v)
  · filter_upwards [hstd] with v h1
    show (fun y => ev₁ v (G.M.vac v) (Function.extend j y 0)) = _
    rw [h1]
    exact std_extend hj v
  · intro Φ hΦ
    exact GlobalTheory.RestrSchA.mem_schA_comp_extend F j hj _ (hmaps Φ hΦ)
  · intro z Φ hΦ
    have h1 : incM F H.ι * z * (incM F (1 : Matrix (Fin (d₂ + 2 + a')) (Fin (d₂ + 2 + a')) E))ᵀ = incM F H.ι * z := by
      rw [show incM F (1 : Matrix (Fin (d₂ + 2 + a')) (Fin (d₂ + 2 + a')) E) = 1 from
        Matrix.map_one _ (map_zero _) (map_one _)]
      simp
    rw [h1]
    funext y
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hheis _ Φ hΦ]
    simp only [Darboux.rho, schr, hι, GlobalTheory.VacRestr.ext_dot hj, GlobalTheory.VacRestr.ext_add hj, LinearMap.funLeft_apply]
    rfl
  · intro u hu Φ hΦ
    obtain ⟨z, rfl⟩ := hu
    funext y
    simp only [LinearMap.comp_apply, LinearMap.funLeft_apply]
    rw [hheis _ Φ hΦ]
    obtain ⟨h1, h2⟩ := hx z
    simp only [Darboux.rho, schr, h1, extend_dot_zero _ _ h2, zero_dotProduct, mul_zero, add_zero,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨b, hb0⟩ : ∃ b : SInf F (Fin (d₂ + 2) × Fin (d₂ + 2 + a')), b 0 ≠ 0 := by
      let bb : ContDiffBump (0 : Fin (d₂ + 2) × Fin (d₂ + 2 + a') → mixedEmbedding.mixedSpace F) := ⟨1, 2, one_pos, one_lt_two⟩
      have hs : HasCompactSupport (fun x => ((bb x : ℝ) : ℂ)) :=
        bb.hasCompactSupport.comp_left (g := fun t : ℝ => (t : ℂ)) (by simp)
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (fun x => ((bb x : ℝ) : ℂ)) := Complex.ofRealCLM.contDiff.comp bb.contDiff
      refine ⟨hs.toSchwartzMap hcd, ?_⟩
      have h2 : bb 0 = 1 := bb.one_of_mem_closedBall (by simp [bb])
      simp [h2]
    obtain ⟨f₀, hf₀⟩ := hsurj b
    refine ⟨R.comp ei₁, fun v =>
      LinearMap.funLeft ℂ ℂ (fun y : Fin d₂ × Fin (d₂ + 2 + a') → Fv F v => Function.extend j y 0) ∘ₗ ev₁ v, ?_, ?_, ?_⟩
    · intro h
      have := congrArg (fun T : SInf F (Fin (d₂ + 2) × Fin (d₂ + 2 + a')) →L[ℂ] SInf F (Fin d₂ × Fin (d₂ + 2 + a')) =>
        T f₀ 0) h
      have hz : Function.extend j (0 : Fin d₂ × Fin (d₂ + 2 + a') → mixedEmbedding.mixedSpace F) 0 = 0 := by
        funext k
        by_cases h : ∃ a, j a = k
        · obtain ⟨a, rfl⟩ := h
          simp [hj.extend_apply]
        · simp [Function.extend_apply' _ _ _ h]
      simp only [ContinuousLinearMap.comp_apply, hR, hf₀, hz, ContinuousLinearMap.zero_apply,
        SchwartzMap.zero_apply] at this
      exact hb0 this
    · intro v
      refine ⟨rfl, ?_⟩
      rw [Submodule.map_comp, hSB v, GlobalTheory.SchwartzBruhatRestrict.map_funLeft_extendZero F j hj v]
    · intro f φ hφ hφv
      funext y
      rw [LinearMap.comp_apply, hpure f φ hφ hφv]
      simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, ContinuousLinearMap.comp_apply, hR, LinearMap.comp_apply]
      have hI' : (fun i => evI F (Function.extend j y 0 i)) = Function.extend j (fun i => evI F (y i)) 0 :=
        GlobalTheory.VacRestr.ext_map hj (evI F) (by unfold evI; exact map_zero _) y
      have hF : ∀ v : Pl F, (fun i => evFin F v (Function.extend j y 0 i)) =
          Function.extend j (fun i => evFin F v (y i)) 0 := fun v => GlobalTheory.VacRestr.ext_map hj _ (map_zero _) y
      simp only [hI', hF]

end GlobalTheory.PlaneEvX
