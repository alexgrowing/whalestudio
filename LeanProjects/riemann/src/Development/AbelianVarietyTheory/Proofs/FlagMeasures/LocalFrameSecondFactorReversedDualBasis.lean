import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponents
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicProperties
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIffStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvUpperUnitriangularSuperdiagNegStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

namespace SecondFactor

theorem reversed_unitriangular : ∀ (k : Type) [Field k] (n : ℕ) (A M : Matrix (Fin n) (Fin n) k), (∀ x y : Fin n, ∑ l : Fin n, A (Fin.rev l) x * M l y = if x = Fin.rev y then 1 else 0) → ((((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) ↔ ((∀ x y : Fin n, y < x → M x y = 0) ∧ ∀ x, M x x = 1)) ∧ (((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) → ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then M x y else 0) = - ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then A x y else 0))) := by
  intro k _ n A M h
  let Ad : Matrix (Fin n) (Fin n) k := fun x y => A (Fin.rev y) (Fin.rev x)
  have hAM : Ad * M = 1 := by
    refine Matrix.ext fun x y => ?_
    rw [Matrix.mul_apply]
    have := h (Fin.rev x) y
    simp only [Ad]
    rw [this, Matrix.one_apply]
    simp only [Fin.rev_inj]
  have hMA : M * Ad = 1 := mul_eq_one_comm.1 hAM
  have hinvM : Ad⁻¹ = M := Matrix.inv_eq_right_inv hAM
  have hinvA : M⁻¹ = Ad := Matrix.inv_eq_right_inv hMA
  have hrevlt : ∀ x y : Fin n, y < x → Fin.rev x < Fin.rev y := fun x y hxy => Fin.rev_lt_rev.2 hxy
  have hAtoAd : ((∀ x y : Fin n, y < x → A x y = 0) ∧ ∀ x, A x x = 1) →
      ((∀ x y : Fin n, y < x → Ad x y = 0) ∧ ∀ x, Ad x x = 1) := fun ⟨a1, a2⟩ =>
    ⟨fun x y hxy => a1 _ _ (hrevlt x y hxy), fun x => a2 _⟩
  refine ⟨⟨fun hA => ?_, fun hM => ?_⟩, fun hA => ?_⟩
  · obtain ⟨d1, d2⟩ := hAtoAd hA
    obtain ⟨i1, i2, -⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n Ad d1 d2
    rw [hinvM] at i1 i2
    exact ⟨i1, i2⟩
  · obtain ⟨i1, i2, -⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n M hM.1 hM.2
    rw [hinvA] at i1 i2
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have := i1 (Fin.rev y) (Fin.rev x) (hrevlt x y hxy)
      simpa [Ad] using this
    · have := i2 (Fin.rev x)
      simpa [Ad] using this
  · obtain ⟨d1, d2⟩ := hAtoAd hA
    obtain ⟨-, -, i3⟩ := GlobalTheory.T.inv_upperUnitriangular_superdiag_neg k n Ad d1 d2
    rw [hinvM] at i3
    have e1 : ∀ x y : Fin n, (if (x : ℕ) + 1 = y then M x y else 0) =
        - (fun p q : Fin n => if (p : ℕ) + 1 = q then A p q else 0) (Fin.rev y) (Fin.rev x) := by
      intro x y
      have hy := y.2
      have hx := x.2
      by_cases hxy : (x : ℕ) + 1 = y
      · have hc : ((Fin.rev y : Fin n) : ℕ) + 1 = (Fin.rev x : Fin n) := by
          simp only [Fin.val_rev]; omega
        simp only [if_pos hxy, if_pos hc, i3 x y hxy, Ad]
      · have hc : ¬ ((Fin.rev y : Fin n) : ℕ) + 1 = (Fin.rev x : Fin n) := by
          simp only [Fin.val_rev]; omega
        simp only [if_neg hxy, if_neg hc, neg_zero]
    simp only [e1, Finset.sum_neg_distrib]
    congr 1
    have key : ∀ f : Fin n → Fin n → k, ∑ x : Fin n, ∑ y : Fin n, f (Fin.rev y) (Fin.rev x) = ∑ x : Fin n, ∑ y : Fin n, f x y := by
      intro f
      rw [Finset.sum_comm]
      calc ∑ y : Fin n, ∑ x : Fin n, f (Fin.rev y) (Fin.rev x)
          = ∑ y : Fin n, ∑ x : Fin n, f (Fin.rev y) x :=
            Finset.sum_congr rfl fun y _ => Equiv.sum_comp Fin.revPerm (fun x => f (Fin.rev y) x)
        _ = ∑ x : Fin n, ∑ y : Fin n, f x y :=
            Equiv.sum_comp Fin.revPerm (fun y => ∑ x : Fin n, f y x)
    exact key (fun p q : Fin n => if (p : ℕ) + 1 = q then A p q else 0)

theorem reversed_relation_mod : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (n g : ℕ) (A M R : Matrix (Fin n) (Fin n) (v.adicCompletion F)), (∀ a b, A a b ∈ v.adicCompletionIntegers F) → (∀ a b, M a b ∈ v.adicCompletionIntegers F) → Aᵀ * R * M = R → (∀ i j, ∃ s ∈ v.adicCompletionIntegers F, R i j - (if i = Fin.rev j then 1 else 0) = (g : v.adicCompletion F) * s) → IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ x y : Fin n, ∑ l : Fin n, redM F v A (Fin.rev l) x * redM F v M l y = if x = Fin.rev y then 1 else 0 := by
  intro F _ _ v n g A M R hA hM hrel hRent hg x y
  choose s hs hs2 using hRent
  let φ : v.adicCompletionIntegers F →+* v.adicCompletion F := algebraMap _ _
  let ρ : v.adicCompletionIntegers F →+* kv F v := IsLocalRing.residue _
  let Ao : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨A a c, hA a c⟩
  let Mo : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨M a c, hM a c⟩
  let So : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨s a c, hs a c⟩
  let Ro : Fin n → Fin n → v.adicCompletionIntegers F := fun i j => (if i = Fin.rev j then 1 else 0) + (g : v.adicCompletionIntegers F) * So i j
  have hφA : ∀ a c, φ (Ao a c) = A a c := fun _ _ => rfl
  have hφM : ∀ a c, φ (Mo a c) = M a c := fun _ _ => rfl
  have hφS : ∀ a c, φ (So a c) = s a c := fun _ _ => rfl
  have hφR : ∀ i j, φ (Ro i j) = R i j := by
    intro i j
    have := hs2 i j
    have e : R i j = (if i = Fin.rev j then 1 else 0) + (g : v.adicCompletion F) * s i j := by
      rw [← this]; ring
    rw [e]
    simp only [Ro, map_add, map_mul, map_natCast, hφS]
    congr 1
    split_ifs <;> simp
  have hinj : Function.Injective φ := Subtype.val_injective
  have hE : ∑ l, (∑ p, Ao p x * Ro p l) * Mo l y = Ro x y := by
    apply hinj
    have := congrFun (congrFun hrel x) y
    simp only [Matrix.mul_apply, Matrix.transpose_apply] at this
    simp only [map_sum, map_mul, hφA, hφM, hφR]
    exact this
  have hg0 : ρ (g : v.adicCompletionIntegers F) = 0 := by
    refine (IsLocalRing.residue_eq_zero_iff _).2 ?_
    rw [hg]
    exact Ideal.mem_span_singleton_self _
  have hρR : ∀ i j, ρ (Ro i j) = if i = Fin.rev j then 1 else 0 := by
    intro i j
    simp only [Ro, map_add, map_mul, hg0, zero_mul, add_zero]
    split_ifs <;> simp
  have hρA : ∀ a c, ρ (Ao a c) = redM F v A a c := fun a c => (show redM F v A a c = ρ (Ao a c) from dif_pos (hA a c)).symm
  have hρM : ∀ a c, ρ (Mo a c) = redM F v M a c := fun a c => (show redM F v M a c = ρ (Mo a c) from dif_pos (hM a c)).symm
  have h := congrArg ρ hE
  simp only [map_sum, map_mul, hρR, hρA, hρM] at h
  rw [← h]
  refine Finset.sum_congr rfl fun l _ => ?_
  simp

theorem residue_character : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ ψ : AddChar (kv F v) ℂ, ψ ≠ 1 ∧ ∀ (s r : v.adicCompletionIntegers F) (x : E ⊗[F] v.adicCompletion F), sp x = (0, (s : v.adicCompletion F) + (g : v.adicCompletion F) * (r : v.adicCompletion F)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * x)) = ψ (IsLocalRing.residue (v.adicCompletionIntegers F) (-s)) := by
  intro F E _ _ _ _ _ v sp halg hint g hg e he psi hadd hpsiO hne
  have hOA : ∀ x ∈ intV E v, Formalism.UG.P.afsplitIE v x ∈ OAd F E := by
    intro x hx
    refine ((GlobalTheory.St.G.IntAd.integral_adeles_properties F E).1 _).2 fun w => ?_
    by_cases hw : w = v
    · subst hw
      rw [Formalism.UG.P.afsplit_prV_IE]; exact hx
    · rw [Formalism.UG.P.afsplit_prV_IE_ne v w hw]; exact zero_mem _
  have hpsi0 : psi 0 = 1 := hpsiO 0 (zero_mem _)
  have hgF : (g : F) ≠ 0 := by
    intro h0
    obtain ⟨a, -, ha⟩ := hne
    apply ha
    rw [h0, _root_.inv_zero, map_zero, zero_mul, map_zero, hpsi0]
  have hspA : ∀ a : F, sp (algebraMap F (E ⊗[F] v.adicCompletion F) a) =
      (algebraMap F (v.adicCompletion F) a, algebraMap F (v.adicCompletion F) a) := by
    intro a
    have : algebraMap F (E ⊗[F] v.adicCompletion F) a = (1 : E) ⊗ₜ[F] algebraMap F (v.adicCompletion F) a := by
      rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one,
        TensorProduct.smul_tmul]
    rw [this, halg]
  set c : v.adicCompletion F := algebraMap F (v.adicCompletion F) ((g : F)⁻¹) with hc
  have hcg : c * (g : v.adicCompletion F) = 1 := by
    rw [hc, ← map_natCast (algebraMap F (v.adicCompletion F)) g, ← map_mul, inv_mul_cancel₀ hgF, map_one]
  let P : v.adicCompletion F → ℂ := fun r =>
    psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * sp.symm (0, r)))
  have hPadd : ∀ r r', P (r + r') = P r * P r' := by
    intro r r'
    have : ((0 : v.adicCompletion F), r + r') = (0, r) + (0, r') := by simp
    simp only [P]
    rw [this, map_add, mul_add, map_add, hadd]
  have hP1 : ∀ r : v.adicCompletionIntegers F, P ((g : v.adicCompletion F) * r) = 1 := by
    intro r
    have : algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * sp.symm (0, (g : v.adicCompletion F) * r) =
        sp.symm (0, (r : v.adicCompletion F)) := by
      apply sp.injective
      rw [map_mul, hspA, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
      refine Prod.ext (by simp) ?_
      show c * ((g : v.adicCompletion F) * r) = r
      rw [← mul_assoc, hcg, one_mul]
    simp only [P]
    rw [this]
    refine hpsiO _ (hOA _ ((hint _).2 ?_))
    rw [RingEquiv.apply_symm_apply]
    exact ⟨zero_mem _, r.2⟩
  let Q : v.adicCompletionIntegers F → ℂ := fun u => P (-(u : v.adicCompletion F))
  have hQadd : ∀ u u', Q (u + u') = Q u * Q u' := by
    intro u u'
    simp only [Q]
    rw [← hPadd]
    congr 1
    push_cast
    ring
  have hQ1 : ∀ u ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), Q u = 1 := by
    intro u hu
    rw [hg, Ideal.mem_span_singleton'] at hu
    obtain ⟨w, rfl⟩ := hu
    have := hP1 (-w)
    simp only [Q]
    rw [← this]
    congr 1
    push_cast
    ring
  have hsurj := IsLocalRing.residue_surjective (R := v.adicCompletionIntegers F)
  let lift : kv F v → v.adicCompletionIntegers F := Function.surjInv hsurj
  have hlift : ∀ z, IsLocalRing.residue _ (lift z) = z := Function.surjInv_eq hsurj
  have hQres : ∀ u u', IsLocalRing.residue (v.adicCompletionIntegers F) u = IsLocalRing.residue _ u' → Q u = Q u' := by
    intro u u' h
    have hm : u - u' ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := by
      rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
    have h2 : Q u = Q (u' + (u - u')) := by rw [add_sub_cancel]
    rw [h2, hQadd, hQ1 _ hm, mul_one]
  let ψ : AddChar (kv F v) ℂ :=
    { toFun := fun z => Q (lift z)
      map_zero_eq_one' := hQ1 _ ((IsLocalRing.residue_eq_zero_iff _).1 (hlift 0))
      map_add_eq_mul' := fun a b => by
        rw [← hQadd]
        apply hQres
        rw [map_add, hlift, hlift, hlift] }
  have hψ : ∀ u, ψ (IsLocalRing.residue _ u) = Q u := fun u => hQres _ _ (hlift _)
  refine ⟨ψ, ?_, ?_⟩
  · intro h1
    obtain ⟨a, ha, hne'⟩ := hne
    have hr := ((hint a).1 ha).2
    have he' : e * a = sp.symm (0, (sp a).2) := by
      apply sp.injective
      rw [map_mul, he, RingEquiv.apply_symm_apply]
      refine Prod.ext (by simp) (by simp)
    apply hne'
    rw [he']
    have := hψ (-⟨(sp a).2, hr⟩)
    rw [h1, AddChar.one_apply] at this
    simp only [Q] at this
    have e2 : -(((-⟨(sp a).2, hr⟩ : v.adicCompletionIntegers F)) : v.adicCompletion F) = (sp a).2 := by
      push_cast; ring
    rw [e2] at this
    exact this.symm
  · intro s r x hx
    have hxs : x = sp.symm (0, (s : v.adicCompletion F) + (g : v.adicCompletion F) * r) := by
      rw [← hx, RingEquiv.symm_apply_apply]
    rw [hψ]
    show _ = P (-((-s : v.adicCompletionIntegers F) : v.adicCompletion F))
    have e1 : -((-s : v.adicCompletionIntegers F) : v.adicCompletion F) = s := by push_cast; ring
    rw [e1, hxs]
    show P _ = _
    rw [hPadd, hP1, mul_one]

theorem inJ_full_iff {k : Type} [Field k] {n : ℕ} (t : ℕ) (X : Matrix (Fin n) (Fin n) k) :
    InJ n t n false X ↔ ((∀ x y : Fin n, y < x → X x y = 0) ∧ ∀ x, X x x = 1) := by
  have hb : ∀ x : Fin n, blkOf n t x = x := fun x => by simp [blkOf, x.2]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨fun x y h => h1 x y (by rw [hb, hb]; exact h), fun x => h2 x x.2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨fun x y h => h1 x y (by rw [hb, hb] at h; exact h), fun x _ => h2 x, fun x y h => ?_, fun h => ?_⟩
    · exact absurd h (by have := y.2; omega)
    · simp at h

theorem sum_super_eq {A : Type} [AddCommMonoid A] {n : ℕ} (f : Fin n → Fin n → A) :
    (∑ i : Fin n, if hi : i.1 + 1 < n then f i ⟨i.1 + 1, hi⟩ else 0) =
      ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then f x y else 0) := by
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases hi : i.1 + 1 < n
  · rw [dif_pos hi, Finset.sum_eq_single ⟨i.1 + 1, hi⟩]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h
      exact hb (Fin.ext h.symm)
    · simp
  · rw [dif_neg hi]
    symm
    refine Finset.sum_eq_zero fun y _ => ?_
    rw [if_neg]
    have := y.2
    omega

end SecondFactor

open SecondFactor in

theorem local_frame_second_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (0, 1) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet t v sp hsig halg hint g hg L hL e he b bd hb hbd hbe hbde hdual hspan psi hadd hpsiO hne
  obtain ⟨sp', h1, h2⟩ : ∃ sp' : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F,
      (∀ x, (sp' x).1 = (sp x).2) ∧ (∀ x, (sp' x).2 = (sp x).1) :=
    ⟨sp.trans RingEquiv.prodComm, fun _ => rfl, fun _ => rfl⟩
  have hsig' : ∀ x, sp' (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp' x) := by
    intro x
    refine Prod.ext ?_ ?_
    · rw [h1, hsig]; exact (h2 x).symm
    · rw [h2, hsig]; exact (h1 x).symm
  have halg' : ∀ a : v.adicCompletion F, sp' ((1 : E) ⊗ₜ[F] a) = (a, a) := by
    intro a
    refine Prod.ext ?_ ?_
    · rw [h1, halg]
    · rw [h2, halg]
  have hint' : ∀ x, x ∈ intV E v ↔ (sp' x).1 ∈ v.adicCompletionIntegers F ∧ (sp' x).2 ∈ v.adicCompletionIntegers F := by
    intro x
    rw [h1, h2, hint, and_comm]

  have hb1 : ∀ i a, (sp (b i a)).1 = 0 := by
    intro i a
    have := congrArg sp (congrFun (hbe i) a)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, he] at this
    rw [this]; simp
  have hse : sp (sigR cm.sig (v.adicCompletion F) e) = (1, 0) := by
    rw [hsig, he]; rfl
  have hbd2 : ∀ i a, (sp (bd i a)).2 = 0 := by
    intro i a
    have := congrArg sp (congrFun (hbde i) a)
    rw [Pi.smul_apply, smul_eq_mul, map_mul, hse] at this
    rw [this]; simp
  have hrange : Set.range (fun j : Fin n => bd (Fin.rev j)) = Set.range bd :=
    (Fin.revPerm.surjective.range_comp bd)
  obtain ⟨fr, hfr, hlat⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp hsig halg hint g hg L hL
    (fun j => bd (Fin.rev j)) (Set.range b) (fun j => hbd _)
    (by rintro _ ⟨i, rfl⟩ a; exact hb1 i a)
    (by intro y hy; rw [hrange, Set.union_comm]; exact hspan y hy)
  obtain ⟨frB, hfrB, hlatB⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp' hsig' halg' hint' g hg L hL
    b (Set.range bd) hb
    (by rintro _ ⟨i, rfl⟩ a; rw [h1]; exact hbd2 i a)
    (by intro y hy; exact hspan y hy)
  obtain ⟨ψ, hψ1, hψ⟩ := residue_character F E v sp halg hint g hg e he psi hadd hpsiO hne
  refine ⟨fr, ψ, hψ1, hlat, ?_⟩
  intro y hy
  have hA := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp' hsig' halg' hint' g hg L hL b frB hb
    (fun j a => by rw [h2]; exact hb1 j a) hfrB hlatB t y hy
  have hM := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp hsig halg hint g hg L hL
    (fun j => bd (Fin.rev j)) fr (fun j => hbd _) (fun j a => hbd2 _ a) hfr hlat t y hy
  obtain ⟨hAint, hAiff⟩ := hA
  obtain ⟨hMint, -⟩ := hM
  set Y1 : GL (Fin n) (v.adicCompletion F) := bc ((RingHom.fst _ _).comp sp.toRingHom) y with hY1
  set Y2 : GL (Fin n) (v.adicCompletion F) := bc ((RingHom.fst _ _).comp sp'.toRingHom) y with hY2
  set M : Matrix (Fin n) (Fin n) (v.adicCompletion F) := ((fr⁻¹ * Y1 * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hMdef
  set A : Matrix (Fin n) (Fin n) (v.adicCompletion F) := ((frB⁻¹ * Y2 * frB : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hAdef
  have hfM : fr.1 * M = Y1.1 * fr.1 := by
    have : fr * (fr⁻¹ * Y1 * fr) = Y1 * fr := by group
    exact congrArg Units.val this
  have hfA : frB.1 * A = Y2.1 * frB.1 := by
    have : frB * (frB⁻¹ * Y2 * frB) = Y2 * frB := by group
    exact congrArg Units.val this
  set J1 : Matrix (Fin n) (Fin n) (v.adicCompletion F) := Matrix.of fun a c => (sp (inclE (F := F) (v.adicCompletion F) (J a c))).1 with hJ1

  have hyU : cT (sigR cm.sig (v.adicCompletion F)) y.1 * J.map (inclE (F := F) (v.adicCompletion F)) * y.1 =
      J.map (inclE (F := F) (v.adicCompletion F)) := hy.1
  have hU : Y2.1ᵀ * J1 * Y1.1 = J1 := by
    have h := congrArg (fun X => X.map ((RingHom.fst _ _).comp sp.toRingHom : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)) hyU
    simp only [Matrix.map_mul] at h
    have e1 : (cT (sigR cm.sig (v.adicCompletion F)) y.1).map ((RingHom.fst _ _).comp sp.toRingHom : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F) = Y2.1ᵀ := by
      refine Matrix.ext fun a c => ?_
      show (sp (sigR cm.sig (v.adicCompletion F) (y.1 c a))).1 = (sp' (y.1 c a)).1
      rw [hsig, h1]; rfl
    rw [e1] at h
    exact h
  set R : Matrix (Fin n) (Fin n) (v.adicCompletion F) := frB.1ᵀ * J1 * fr.1 with hRdef
  have hrel : Aᵀ * R * M = R := by
    calc Aᵀ * R * M = (frB.1 * A)ᵀ * J1 * (fr.1 * M) := by
          rw [hRdef, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = frB.1ᵀ * (Y2.1ᵀ * J1 * Y1.1) * fr.1 := by
          rw [hfA, hfM, Matrix.transpose_mul]; simp only [Matrix.mul_assoc]
      _ = R := by rw [hU]

  have hpair : ∀ x w : Fin n → E ⊗[F] v.adicCompletion F, (sp (hR cm.sig J (v.adicCompletion F) x w)).2 =
      ∑ a, ∑ c, (sp (x a)).1 * J1 c a * (sp (w c)).2 := by
    intro x w
    have h3 := (GlobalTheory.St.G.split_components F E cm n J hJ hdet v sp' hsig' halg').2.2 x w
    simp only [h1, h2] at h3
    rw [h3]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
    have hJac : (sp (inclE (F := F) (v.adicCompletion F) (J a c))).2 = J1 c a := by
      have hh : J a c = (cm.sig : E →+* E) (J c a) := by
        have := congrFun (congrFun hJ a) c
        exact this.symm
      have hs : inclE (F := F) (v.adicCompletion F) ((cm.sig : E →+* E) (J c a)) =
          sigR cm.sig (v.adicCompletion F) (inclE (F := F) (v.adicCompletion F) (J c a)) := rfl
      rw [hh, hs, hsig]; rfl
    rw [hJac]
  have hpair1 : ∀ (i : Fin n) (w : Fin n → E ⊗[F] v.adicCompletion F), (sp (hR cm.sig J (v.adicCompletion F) (bd i) w)).1 = 0 := by
    intro i w
    rw [(GlobalTheory.St.G.split_components F E cm n J hJ hdet v sp hsig halg).2.2 (bd i) w]
    simp [hbd2]
  have hfrE : ∀ a j, fr.1 a j = (sp (bd (Fin.rev j) a)).1 := fun a j => congrFun (congrFun hfr a) j
  have hfrBE : ∀ a j, frB.1 a j = (sp (b j a)).2 := fun a j => by
    rw [← h1]; exact congrFun (congrFun hfrB a) j

  have hRw : ∀ (i : Fin n) (w : Fin n → E ⊗[F] v.adicCompletion F) (C : Fin n → v.adicCompletion F),
      (fun c => (sp (w c)).2) = frB.1 *ᵥ C →
      (sp (hR cm.sig J (v.adicCompletion F) (bd i) w)).2 = ∑ l, R l (Fin.rev i) * C l := by
    intro i w C hC
    rw [hpair]
    have hR' : ∀ l, R l (Fin.rev i) = ∑ a, ∑ c, frB.1 c l * J1 c a * (sp (bd i a)).1 := by
      intro l
      rw [hRdef, Matrix.mul_apply, Finset.sum_congr rfl fun a _ => by
        rw [Matrix.mul_apply, hfrE, Fin.rev_rev, Finset.sum_mul]]
      simp only [Matrix.transpose_apply]
    have hw : ∀ c, (sp (w c)).2 = ∑ l, frB.1 c l * C l := fun c => congrFun hC c
    simp only [hw, hR', Finset.sum_mul, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun l _ => by ring
  have hRi : ∀ i j, R i j = (sp (hR cm.sig J (v.adicCompletion F) (bd (Fin.rev j)) (b i))).2 := by
    intro i j
    have := hRw (Fin.rev j) (b i) (Pi.single i 1) (by
      funext c
      simp [hfrBE])
    rw [this]
    simp [Pi.single_apply, Fin.rev_rev]
  have hg0 : ∀ x : E ⊗[F] v.adicCompletion F, (sp ((g : E ⊗[F] v.adicCompletion F) * x)).2 = (g : v.adicCompletion F) * (sp x).2 := by
    intro x
    rw [map_mul, map_natCast]; simp
  have hRent : ∀ i j, ∃ s ∈ v.adicCompletionIntegers F, R i j - (if i = Fin.rev j then 1 else 0) = (g : v.adicCompletion F) * s := by
    intro i j
    obtain ⟨s, hs, hs2⟩ := hdual (Fin.rev j) i
    refine ⟨(sp s).2, ((hint s).1 hs).2, ?_⟩
    rw [hRi, ← hg0, ← hs2, map_sub, Prod.snd_sub]
    congr 1
    by_cases hij : i = Fin.rev j
    · simp [hij, he]
    · have : ¬ Fin.rev j = i := fun h => hij h.symm
      simp [hij, this]
  have hred := reversed_relation_mod F v n g A M R hAint hMint hrel hRent hg
  obtain ⟨hiff, hsup⟩ := reversed_unitriangular (kv F v) n (redM F v A) (redM F v M) hred
  refine ⟨hAiff.trans ?_, fun hK => ?_⟩
  · rw [inJ_full_iff, inJ_full_iff]; exact hiff
  have hAu := (inJ_full_iff t _).1 (hAiff.1 hK)
  have hsupM := hsup hAu
  choose sR hsR hsR2 using hRent
  let Ao : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨A a c, hAint a c⟩
  let So : Fin n → Fin n → v.adicCompletionIntegers F := fun a c => ⟨sR a c, hsR a c⟩
  let rr : Fin n → Fin n → v.adicCompletionIntegers F := fun i j => ∑ l, So l (Fin.rev i) * Ao l j
  let sO : v.adicCompletionIntegers F := ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then Ao x y else 0)
  let rO : v.adicCompletionIntegers F := ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then rr x y else 0)
  have hcoe : ∀ (f : Fin n → Fin n → v.adicCompletionIntegers F),
      (((∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then f x y else 0)) : v.adicCompletionIntegers F) : v.adicCompletion F) =
        ∑ x : Fin n, ∑ y : Fin n, (if (x : ℕ) + 1 = y then (f x y : v.adicCompletion F) else 0) := by
    intro f
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) _ = _
    simp only [map_sum, apply_ite (algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F)), map_zero]
    rfl
  have hrr : ∀ i j, ((rr i j : v.adicCompletionIntegers F) : v.adicCompletion F) = ∑ l, sR l (Fin.rev i) * A l j := by
    intro i j
    show algebraMap (v.adicCompletionIntegers F) (v.adicCompletion F) _ = _
    simp only [rr, map_sum, map_mul]
    rfl
  have hterm : ∀ i j, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b j))).2 =
      A i j + (g : v.adicCompletion F) * (rr i j : v.adicCompletion F) := by
    intro i j
    have hC : (fun c => (sp ((y.1 *ᵥ b j) c)).2) = frB.1 *ᵥ (fun l => A l j) := by
      funext c
      have e1 : (frB.1 *ᵥ (fun l => A l j)) c = (frB.1 * A) c j := by
        simp [Matrix.mulVec, dotProduct, Matrix.mul_apply]
      rw [e1, hfA, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct]
      rw [map_sum, Prod.snd_sum]
      refine Finset.sum_congr rfl fun d _ => ?_
      rw [map_mul, Prod.snd_mul, hfrBE, ← h1]
      rfl
    rw [hRw i _ _ hC, hrr, Finset.mul_sum]
    have hRl : ∀ l, R l (Fin.rev i) = (if l = i then 1 else 0) + (g : v.adicCompletion F) * sR l (Fin.rev i) := by
      intro l
      have := hsR2 l (Fin.rev i)
      rw [Fin.rev_rev] at this
      rw [← this]; ring
    simp only [hRl, add_mul, Finset.sum_add_distrib, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    congr 1
    exact Finset.sum_congr rfl fun l _ => by ring
  have hss : sp (supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1) =
      (0, (sO : v.adicCompletion F) + (g : v.adicCompletion F) * (rO : v.adicCompletion F)) := by
    unfold supSum
    rw [map_sum]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_sum]
      refine Finset.sum_eq_zero fun i _ => ?_
      split_ifs
      · exact hpair1 i _
      · simp
    · rw [Prod.snd_sum]
      have e1 : ∀ i : Fin n, (sp (if hi : i.1 + 1 < n then hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b ⟨i.1 + 1, hi⟩) else 0)).2 =
          if hi : i.1 + 1 < n then (fun p q => A p q + (g : v.adicCompletion F) * (rr p q : v.adicCompletion F)) i ⟨i.1 + 1, hi⟩ else 0 := by
        intro i
        split_ifs
        · exact hterm i _
        · simp
      simp only [e1]
      refine (sum_super_eq (fun p q => A p q + (g : v.adicCompletion F) * (rr p q : v.adicCompletion F))).trans ?_
      show _ = ((sO : v.adicCompletionIntegers F) : v.adicCompletion F) + (g : v.adicCompletion F) * ((rO : v.adicCompletionIntegers F) : v.adicCompletion F)
      rw [hcoe Ao, hcoe rr, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun q _ => ?_
      split_ifs
      · rfl
      · simp
  rw [hψ sO rO _ hss]
  have hredA : ∀ x q, redM F v A x q = IsLocalRing.residue (v.adicCompletionIntegers F) (Ao x q) := fun x q => dif_pos (hAint x q)
  have hlam : lamJ ψ (fun _ => 1) n t 0 n (redM F v M) = ψ (∑ x : Fin n, ∑ q : Fin n, (if (x : ℕ) + 1 = q then redM F v M x q else 0)) := by
    simp only [lamJ, Finset.range_zero, Finset.prod_empty, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun q _ => ?_
    have hq := q.2
    by_cases h : (x : ℕ) + 1 = q
    · rw [if_pos h, if_pos ⟨h, hq, by omega⟩]
    · rw [if_neg h, if_neg (fun h' => h h'.1)]
  rw [hlam, hsupM, map_neg]
  congr 2
  simp only [sO, map_sum, apply_ite (IsLocalRing.residue (v.adicCompletionIntegers F)), map_zero, hredA]

end GlobalTheory.St.G
