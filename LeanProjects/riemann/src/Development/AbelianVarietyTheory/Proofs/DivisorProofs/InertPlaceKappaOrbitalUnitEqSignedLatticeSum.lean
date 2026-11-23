import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnramifiedQuadraticDatumAtInertPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitLemmaUnramifiedProductUnitaryGroupsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLocalRingOfIdem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeCountAndGramDetSignNormClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsModelOfUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelCharpolyEqAndUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNormMulOfHermitianModelUnitaryConjStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianModelsConjUnitaryOfNormClassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHermitianModelOfNormNeZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertOrbitalIntegralUnitEqLatticeCountStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianLatticeLocalUnitaryTwistStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem finsum_match {α β : Type*} (F : α → ℂ) (G : β → ℚ) (Φ : α → β) (P : α → Prop)
    (hF0 : ∀ a, ¬ P a → F a = 0) (hF : ∀ a, P a → F a = G (Φ a))
    (hinj : ∀ a a', P a → P a' → Φ a = Φ a' → a = a') (hsurj : ∀ b, G b ≠ 0 → ∃ a, P a ∧ Φ a = b) :
    ∑ᶠ a, F a = ((∑ᶠ b, G b : ℚ) : ℂ) := by
  have hcast : ((∑ᶠ b, G b : ℚ) : ℂ) = ∑ᶠ b, (G b : ℂ) := by
    by_cases hfin : (Function.support G).Finite
    · simpa using (Rat.castHom ℂ).toAddMonoidHom.map_finsum hfin
    · rw [finsum_of_infinite_support hfin, finsum_of_infinite_support]
      · simp
      · have : Function.support (fun b => (G b : ℂ)) = Function.support G := by
          ext b; simp
        rwa [this]
  have hP : ∀ a, F a ≠ 0 → P a := fun a ha => by by_contra h; exact ha (hF0 a h)
  rw [hcast, ← finsum_mem_support F, ← finsum_mem_support (fun b => (G b : ℂ))]
  apply finsum_mem_eq_of_bijOn Φ
  · refine ⟨?_, ?_, ?_⟩
    · intro a ha
      simp only [Function.mem_support] at ha ⊢
      rwa [hF a (hP a ha)] at ha
    · intro a ha a' ha' h
      exact hinj a a' (hP a ha) (hP a' ha') h
    · intro b hb
      simp only [Function.mem_support, ne_eq, Rat.cast_eq_zero] at hb
      obtain ⟨a, ha, rfl⟩ := hsurj b hb
      refine ⟨a, ?_, rfl⟩
      simp only [Function.mem_support, hF a ha]
      exact_mod_cast hb
  · intro a ha
    exact hF a (hP a ha)

end GlobalTheory.InertUnitOrb

namespace GlobalTheory.InertUnitOrb
open GlobalTheory.UnitLemma

theorem ul_mem_iff {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ} {w : Pl E} (hw : ¬ IsSplitAt w)
    (g : GLw n w) : g ∈ UL n w ↔ (g.val.map (cj w))ᵀ * g.val = 1 := by
  unfold UL
  rw [if_neg hw]
  change cT (cj w) g.val * 1 * g.val = 1 ↔ _
  rw [Matrix.mul_one]
  rfl

theorem kapOrb_unit_eq_kapSum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (w : Pl E), ¬ IsSplitAt w → ∀ (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → (∀ x, x ∈ (algebraMap K.O K.E).range ↔ Valued.v (e x) ≤ 1) → (∀ x, GlobalTheory.UnitLemma.val K.O x = ordL (e x)) → qV E w = K.q ^ 2 → ∀ (n : ℕ) (Q₁ Q₂ : (w.adicCompletion E)[X]), Q₁.Monic → Q₂.Monic → Q₁.natDegree + Q₂.natDegree = n → (Q₁ * Q₂).Separable → IsCsr w Q₁ → IsCsr w Q₂ → ∀ B₁ B₂ : GlobalTheory.UnitLemma.InvAlg K, B₁.g * B₁.σ B₁.g = 1 → B₂.g * B₂.σ B₂.g = 1 → B₁.P = Q₁.map e.symm.toRingHom → B₂.P = Q₂.map e.symm.toRingHom → kapOrb n w Q₁ Q₂ ((KL n w : Set (UL n w)).indicator 1) = (B₁.kapSum B₂ : ℂ) := by
  intro E _ _ _ hU w hw K e he hint hval hq n Q₁ Q₂ hm₁ hm₂ hdeg hsep hc₁ hc₂ B₁ B₂ hu₁ hu₂ hP₁ hP₂
  have hBP : (B₁.prod B₂).P = (Q₁ * Q₂).map e.symm.toRingHom := by
    rw [GlobalTheory.UnitLemma.Orbit.prod_P, hP₁, hP₂, Polynomial.map_mul]
  have hBsep : (B₁.prod B₂).P.Separable := by rw [hBP]; exact hsep.map
  have hBsep' : (B₁.P * B₂.P).Separable := by rw [← GlobalTheory.UnitLemma.Orbit.prod_P]; exact hBsep
  have hBu : (B₁.prod B₂).g * (B₁.prod B₂).σ (B₁.prod B₂).g = 1 := Prod.ext hu₁ hu₂
  have hdim : Module.finrank K.E (B₁.prod B₂).A = n := by
    rw [← LinearMap.charpoly_natDegree (LinearMap.mulLeft K.E (B₁.prod B₂).g)]
    change (B₁.prod B₂).P.natDegree = n
    rw [hBP, natDegree_map_eq_of_injective e.symm.injective, hm₁.natDegree_mul hm₂, hdeg]
  set B := B₁.prod B₂ with hB
  have hcK : ∀ y, K.c (e.symm y) = e.symm (cj w y) := fun y => by
    apply e.injective
    rw [he, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  let tr : GLw n w → Matrix (Fin n) (Fin n) K.E := fun γ => γ.val.map e.symm
  have trmul : ∀ a b : GLw n w, tr (a * b) = tr a * tr b := fun a b => by
    ext i j; simp [tr, Matrix.mul_apply, map_sum]
  have trinj : ∀ a b : GLw n w, tr a = tr b → a = b := fun a b h =>
    Units.ext (Matrix.map_injective e.symm.injective h)
  have trU : ∀ γ : UL n w, ((tr γ.1).map K.c)ᵀ * tr γ.1 = 1 := fun γ => by
    have h := (ul_mem_iff hw γ.1).1 γ.2
    have h2 : ((tr γ.1).map K.c)ᵀ = ((γ.1.val.map (cj w))ᵀ).map e.symm := by
      ext i j; simp [tr, hcK]
    rw [h2]
    calc _ = (((γ.1.val.map (cj w))ᵀ * γ.1.val).map e.symm) := by
            ext i j; simp [tr, Matrix.mul_apply, map_sum]
      _ = 1 := by rw [h]; exact Matrix.map_one _ (map_zero _) (map_one _)
  have trcp : ∀ γ : GLw n w, (tr γ).charpoly = γ.val.charpoly.map e.symm.toRingHom := fun γ =>
    Matrix.charpoly_map γ.val e.symm.toRingHom
  have pull : ∀ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 → ∃ g : UL n w, tr g.1 = u := by
    intro u hu
    have h1 : ((u.map e).map (cj w))ᵀ * u.map e = 1 := by
      have h2 : ((u.map e).map (cj w))ᵀ = ((u.map K.c)ᵀ).map e := by
        ext i j; simp [he]
      have h3 := congrArg (fun M => M.map e) hu
      simp only [Matrix.map_one _ (map_zero e) (map_one e)] at h3
      rw [h2, ← h3]
      ext i j; simp [Matrix.mul_apply, map_sum]
    let g : GLw n w := ⟨u.map e, ((u.map e).map (cj w))ᵀ, mul_eq_one_comm.1 h1, h1⟩
    refine ⟨⟨g, (ul_mem_iff hw g).2 h1⟩, ?_⟩
    ext i j; simp [tr, g]
  have hmod : ∀ γ : UL n w, γ.1.val.charpoly = Q₁ * Q₂ →
      ∃ (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), IsModel B (tr γ.1) x ψ :=
    fun γ h => GlobalTheory.T.exists_isModel_of_unitary_charpoly_eq K B n (tr γ.1) (trU γ) hBu hBsep (by rw [trcp, h, hBP])
  have clEq : Equivalence (fun x y : {x : B.Aˣ // B.σ (x : B.A) = x} =>
      ∃ u : B.Aˣ, (y.1 : B.A) = x.1 * (u * B.σ (u : B.A))) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨u, hu⟩
      refine ⟨u⁻¹, ?_⟩
      have h1 : ((u⁻¹ : B.Aˣ) : B.A) * (u : B.A) = 1 := Units.inv_mul u
      have h2 : B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) = 1 := by rw [← map_mul, h1, map_one]
      rw [hu]
      linear_combination (-(x.1 : B.A)) * B.σ ((u⁻¹ : B.Aˣ) : B.A) * B.σ (u : B.A) * h1 + (-(x.1 : B.A)) * h2
    · rintro x y z ⟨u, hu⟩ ⟨v, hv⟩
      refine ⟨u * v, ?_⟩
      rw [hv, hu, Units.val_mul, map_mul]; ring
  have twEq : Equivalence (fun x y : UL n w => ∃ g, y = g⁻¹ * x * (MonoidHom.id (UL n w)) g) := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨g, rfl⟩
      exact ⟨g⁻¹, by simp [mul_assoc]⟩
    · rintro x y z ⟨g, rfl⟩ ⟨h, rfl⟩
      exact ⟨g * h, by simp [mul_assoc]⟩
  let Fv : {x : B.Aˣ // B.σ (x : B.A) = x} → ℚ := fun x => K.eta (B₁.gramDet (x.1 : B.A).1) * B.N (x.1 : B.A)
  have Fv_resp : ∀ a b : {x : B.Aˣ // B.σ (x : B.A) = x},
      (∃ u : B.Aˣ, (b.1 : B.A) = a.1 * (u * B.σ (u : B.A))) → Fv a = Fv b := by
    rintro a b ⟨u, hu⟩
    have e1 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B (a.1 : B.A) u).1
    have e2 := (GlobalTheory.T.latticeCount_and_gramDetSign_norm_class K B₁ (a.1 : B.A).1 (Units.map (MonoidHom.fst B₁.A B₂.A) u)).2
    simp only [Fv, hu]
    exact (congrArg₂ (· * ·) e2 e1).symm
  have Fv_out : ∀ a, Fv (Quot.out (Quot.mk _ a : B.Cl)) = Fv a := fun a =>
    Fv_resp _ _ (clEq.eqvGen_iff.1 (Quot.eqvGen_exact (Quot.out_eq (Quot.mk _ a : B.Cl))))
  let P : TwCl (MonoidHom.id (UL n w)) → Prop := fun c => c.rep.1.val.charpoly = Q₁ * Q₂
  let Φ : TwCl (MonoidHom.id (UL n w)) → B.Cl := fun c =>
    if h : P c then Quot.mk _ ⟨(hmod c.rep h).choose, (hmod c.rep h).choose_spec.choose_spec.1⟩
    else Quot.mk _ ⟨1, by simp⟩
  unfold kapOrb clSum InvAlg.kapSum
  refine finsum_match _ _ Φ P ?_ ?_ ?_ ?_
  · intro c hc
    exact if_neg hc
  · intro c hc
    have hc' : c.rep ∈ {γ : UL n w | γ.1.val.charpoly = Q₁ * Q₂} := hc
    rw [if_pos hc']
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    rw [hΦ]
    change _ = ((Fv (Quot.out (Quot.mk _ _ : B.Cl)) : ℚ) : ℂ)
    rw [Fv_out]
    beta_reduce
    rw [GlobalTheory.T.hermitian_lattice_local_unitary_twist E hU w hw K e he hval n Q₁ B₁ B₂ hBsep' hP₁ c.rep.1 _ ψ hψ,
      GlobalTheory.T.inert_orbitalIntegral_unit_eq_lattice_count E hU w hw K e he hint n B hBsep c.rep _ ψ hψ]
    simp only [Fv]
    push_cast
    rfl
  · intro c c' hc hc' h
    obtain ⟨ψ, hψ⟩ := (hmod c.rep hc).choose_spec
    obtain ⟨ψ', hψ'⟩ := (hmod c'.rep hc').choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hc).choose, hψ.1⟩ := dif_pos hc
    have hΦ' : Φ c' = Quot.mk _ ⟨(hmod c'.rep hc').choose, hψ'.1⟩ := dif_pos hc'
    rw [hΦ, hΦ'] at h
    obtain ⟨v, hv⟩ := clEq.eqvGen_iff.1 (Quot.eqvGen_exact h)
    obtain ⟨u, hu, hγu⟩ := GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class K B n _ _ _ _ v ψ ψ' hψ hψ' hv
    obtain ⟨g, rfl⟩ := pull u hu
    have hcomm : c.rep * g = g * c'.rep := by
      apply Subtype.ext
      apply trinj
      rw [Subgroup.coe_mul, Subgroup.coe_mul, trmul, trmul]
      exact hγu
    rw [← Quot.out_eq c, ← Quot.out_eq c']
    refine Quot.sound ⟨g, ?_⟩
    change c'.rep = g⁻¹ * c.rep * g
    rw [mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  · intro k hk
    set a := Quot.out k with ha
    have hk' : Fv a ≠ 0 := hk
    have hN : B.N (a.1 : B.A) ≠ 0 := (mul_ne_zero_iff.1 hk').2
    obtain ⟨γm, ψ, hψ⟩ := GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero K B n a.1 hdim a.2 hN
    obtain ⟨hcpm, hunm⟩ := GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary K B n γm a.1 ψ hψ
    obtain ⟨γ, hγ⟩ := pull γm (hunm hBu)
    have hcpγ : γ.1.val.charpoly = Q₁ * Q₂ := by
      apply Polynomial.map_injective e.symm.toRingHom e.symm.injective
      rw [← trcp, hγ, hcpm, hBP]
    let c : TwCl (MonoidHom.id (UL n w)) := Quot.mk _ γ
    obtain ⟨g, hg⟩ := twEq.eqvGen_iff.1
      (Quot.eqvGen_exact (Quot.out_eq c : Quot.mk _ (Quot.out c) = Quot.mk _ γ))
    simp only [MonoidHom.id_apply] at hg
    have hcr : c.rep = g * γ * g⁻¹ := by
      change Quot.out c = g * γ * g⁻¹
      rw [hg]; group
    have hPc : P c := by
      change c.rep.1.val.charpoly = Q₁ * Q₂
      rw [hcr]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul, Matrix.coe_units_inv]
      rw [← hcpγ]
      exact Matrix.charpoly_units_conj (g.1) γ.1.val
    refine ⟨c, hPc, ?_⟩
    obtain ⟨ψc, hψc⟩ := (hmod c.rep hPc).choose_spec
    have hΦ : Φ c = Quot.mk _ ⟨(hmod c.rep hPc).choose, hψc.1⟩ := dif_pos hPc
    rw [hΦ]
    have hgu : γ * g⁻¹ = g⁻¹ * c.rep := by rw [hcr]; group
    obtain ⟨v, hv⟩ := GlobalTheory.T.exists_norm_mul_of_hermitianModel_unitary_conj K B n γm (tr c.rep.1) (tr (g⁻¹).1) a.1 _ ψ ψc hψ hψc (trU g⁻¹)
      (by rw [← hγ, ← trmul, ← trmul, ← Subgroup.coe_mul, ← Subgroup.coe_mul, hgu]) hBsep
    rw [← Quot.out_eq k]
    exact (Quot.sound ⟨v, hv⟩).symm

end GlobalTheory.InertUnitOrb
