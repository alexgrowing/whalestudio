import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SelfDualAt
import Formalism.LocalToGlobal.HermitianForms.TiedStep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceLatticeComponentsStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralExtensionFiniteAdelesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FirstComponentsBasisLocalLatticeSplitStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianLocalLevelUnitriangularIffStatement
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.St.G.FirstFactorFrame

theorem res_key {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) (a b : R)
    (h : IsLocalRing.residue R a = IsLocalRing.residue R b) : f a = f b := by
  have hm' : a - b ∈ IsLocalRing.maximalIdeal R := by
    rw [← IsLocalRing.residue_eq_zero_iff, map_sub, h, sub_self]
  have := hadd b (a - b)
  rw [show b + (a - b) = a by ring, hm _ hm', mul_one] at this
  exact this

theorem res_surjInv {R : Type} [CommRing R] [IsLocalRing R] (x : IsLocalRing.ResidueField R) :
    IsLocalRing.residue R (Function.surjInv IsLocalRing.residue_surjective x) = x :=
  Function.surjInv_eq (f := IsLocalRing.residue R) IsLocalRing.residue_surjective x

def resChar {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) : AddChar (IsLocalRing.ResidueField R) ℂ where
  toFun x := f (Function.surjInv IsLocalRing.residue_surjective x)
  map_zero_eq_one' := by
    rw [res_key f hadd hm _ 0 (by rw [res_surjInv, map_zero])]
    exact hm 0 (Ideal.zero_mem _)
  map_add_eq_mul' x y := by
    rw [← hadd]
    exact res_key f hadd hm _ _ (by rw [map_add, res_surjInv, res_surjInv, res_surjInv])

theorem resChar_residue {R : Type} [CommRing R] [IsLocalRing R] (f : R → ℂ) (hadd : ∀ a b, f (a + b) = f a * f b)
    (hm : ∀ a ∈ IsLocalRing.maximalIdeal R, f a = 1) (a : R) :
    resChar f hadd hm (IsLocalRing.residue R a) = f a :=
  res_key f hadd hm _ _ (res_surjInv _)

theorem afsplitIE_mem_OAd {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) (x : E ⊗[F] v.adicCompletion F) (hx : x ∈ intV E v) :
    Formalism.UG.P.afsplitIE v x ∈ OAd F E := by
  rw [(GlobalTheory.T.integralExtensionFiniteAdeles_basic_properties F E).1]
  intro w
  by_cases h : w = v
  · subst h; rw [Formalism.UG.P.afsplit_prV_IE]; exact hx
  · rw [Formalism.UG.P.afsplit_prV_IE_ne v w h]; exact zero_mem _

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)} (σ : E →ₐ[F] E)
  (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem fst_of_sig (hsig : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) {n : ℕ}
    (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0)) (x : Fin n → E ⊗[F] v.adicCompletion F)
    (hx : x = sigR σ (v.adicCompletion F) e • x) (a : Fin n) : (sp (x a)).1 = 0 := by
  have h := congrFun hx a
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [h, map_mul, hsig, he]
  simp [swapR]

theorem snd_of_e {n : ℕ} (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0))
    (x : Fin n → E ⊗[F] v.adicCompletion F) (hx : x = e • x) (a : Fin n) : (sp (x a)).2 = 0 := by
  have h := congrFun hx a
  rw [Pi.smul_apply, smul_eq_mul] at h
  rw [h, map_mul, he]
  simp

theorem hR_snd_zero (hsig : ∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E) (x y : Fin n → E ⊗[F] v.adicCompletion F) (hx : ∀ a, (sp (x a)).1 = 0) :
    (sp (hR σ J (v.adicCompletion F) x y)).2 = 0 := by
  unfold hR hform
  simp only [map_sum, map_mul, Prod.snd_sum, Prod.snd_mul, hsig]
  simp [swapR, hx]

theorem fst_mulVec {n : ℕ} (y : GL (Fin n) (E ⊗[F] v.adicCompletion F))
    (c : Fin n → Fin n → E ⊗[F] v.adicCompletion F) (fr : GL (Fin n) (v.adicCompletion F))
    (hfr : (fr : Matrix (Fin n) (Fin n) (v.adicCompletion F)) = Matrix.of (fun a j => (sp (c j a)).1)) (j a : Fin n) :
    (sp ((y.1 *ᵥ c j) a)).1 = ∑ l, (sp (c l a)).1 *
      ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) :
        Matrix (Fin n) (Fin n) (v.adicCompletion F)) l j := by
  have hG : fr * (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr) =
      bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr := by group
  generalize (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) = Mg at hG ⊢
  have hV := congrArg (fun z : GL (Fin n) (v.adicCompletion F) => (z : Matrix (Fin n) (Fin n) (v.adicCompletion F)) a j) hG
  simp only [Units.val_mul] at hV
  rw [Matrix.mul_apply, Matrix.mul_apply] at hV
  simp only [hfr, Matrix.of_apply] at hV
  rw [hV]
  simp only [Matrix.mulVec, dotProduct, map_sum, Prod.fst_sum, map_mul, Prod.fst_mul]
  apply Finset.sum_congr rfl
  intro d _
  simp [bc]

end Split

section Split2

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}
  (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)

theorem fst_dual (e : E ⊗[F] v.adicCompletion F) (he : sp e = (1, 0)) (P : Prop) [Decidable P]
    (x s : E ⊗[F] v.adicCompletion F) (c : ℕ)
    (hx : x - (if P then e else 0) = (c : E ⊗[F] v.adicCompletion F) * s) :
    (sp x).1 = (if P then 1 else 0) + (c : v.adicCompletion F) * (sp s).1 := by
  rw [sub_eq_iff_eq_add] at hx
  rw [hx, map_add, map_mul, map_natCast, Prod.fst_add, Prod.fst_mul, Prod.fst_natCast]
  split_ifs
  · rw [he]; ring
  · rw [map_zero]; simp

theorem fst_pair_sum {n : ℕ} (X : Fin n → v.adicCompletion F) (Jc : Fin n → Fin n → v.adicCompletion F)
    (B : Fin n → Fin n → v.adicCompletion F) (M : Matrix (Fin n) (Fin n) (v.adicCompletion F)) (j : Fin n) :
    ∑ a, ∑ c, X a * Jc a c * (∑ l, B l c * M l j) = ∑ l, M l j * ∑ a, ∑ c, X a * Jc a c * B l c := by
  calc ∑ a, ∑ c, X a * Jc a c * (∑ l, B l c * M l j) = ∑ a, ∑ c, ∑ l, M l j * (X a * Jc a c * B l c) := by
        refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun l _ => by ring
    _ = ∑ a, ∑ l, ∑ c, M l j * (X a * Jc a c * B l c) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ l, ∑ a, ∑ c, M l j * (X a * Jc a c * B l c) := Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum]

end Split2

theorem local_frame_first_factor : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] (cm : CMData F E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHerm (cm.sig : E →+* E) J → J.det ≠ 0 → ∀ (t : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR cm.sig (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → (∀ x, x ∈ intV E v ↔ (sp x).1 ∈ v.adicCompletionIntegers F ∧ (sp x).2 ∈ v.adicCompletionIntegers F) → ∀ (g : ℕ), IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) = Ideal.span {((g : ℕ) : v.adicCompletionIntegers F)} → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → ∀ (e : E ⊗[F] v.adicCompletion F), sp e = (1, 0) → ∀ (b bd : Fin n → Fin n → E ⊗[F] v.adicCompletion F), (∀ i, b i ∈ loc v L) → (∀ i, bd i ∈ loc v L) → (∀ i, b i = e • b i) → (∀ i, bd i = sigR cm.sig (v.adicCompletion F) e • bd i) → (∀ i j, ∃ s ∈ intV E v, hR cm.sig J (v.adicCompletion F) (bd i) (b j) - (if i = j then e else 0) = (g : E ⊗[F] v.adicCompletion F) * s) → (∀ y ∈ loc v L, InModL (loc v L) g (Set.range b ∪ Set.range bd) y) → ∀ (psi : E ⊗[F] Ad F → ℂ), (∀ x y, psi (x + y) = psi x * psi y) → (∀ x ∈ OAd F E, psi x = 1) → (∃ a ∈ intV E v, psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * (e * a))) ≠ 1) → ∃ (fr : GL (Fin n) (v.adicCompletion F)) (ψ : AddChar (kv F v) ℂ), ψ ≠ 1 ∧ (∀ x : Fin n → v.adicCompletion F, (∃ y ∈ loc v L, ∀ c, (sp (y c)).1 = x c) ↔ ∀ c, ((fr⁻¹ : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)).mulVec x c ∈ v.adicCompletionIntegers F) ∧ ∀ y ∈ levelVL cm.sig J v L, ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) ↔ InJ n t n false (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) ∧ ((∀ i : Fin n, InModL (loc v L) g (b '' {j | j.1 < i.1}) ((y.1 - 1) *ᵥ b i)) → psi (Formalism.UG.P.afsplitIE v (algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) * supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1)) = lamJ ψ (fun _ => 1) n t 0 n (redM F v ((fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) : Matrix (Fin n) (Fin n) (v.adicCompletion F)))) := by
  intro F E _ _ _ _ _ _ cm n J hJ hdet t v sp hsig halg hint g hgmax L hL e he b bd hb hbd hbe hbde hdual hspan
    psi hpsi_add hpsi_int hne
  have hbd1 : ∀ i a, (sp (bd i a)).1 = 0 := fun i a => fst_of_sig cm.sig sp hsig e he (bd i) (hbde i) a
  have hb2 : ∀ j a, (sp (b j a)).2 = 0 := fun j a => snd_of_e sp e he (b j) (hbe j) a
  obtain ⟨fr, hfr, hlat⟩ := GlobalTheory.T.first_components_basis_local_lattice_split F E cm n J hJ hdet v sp hsig halg hint g hgmax L hL b (Set.range bd) hb
    (by rintro x ⟨i, rfl⟩ a; exact hbd1 i a) hspan
  have hpsi0 : psi 0 = 1 := hpsi_int 0 (zero_mem _)
  have hgF : (g : F) ≠ 0 := by
    intro h0
    obtain ⟨a, -, ha⟩ := hne
    apply ha
    rw [h0, _root_.inv_zero, map_zero, zero_mul, map_zero, hpsi0]
  set u := algebraMap F (E ⊗[F] v.adicCompletion F) ((g : F)⁻¹) with hu
  have hug : u * (g : E ⊗[F] v.adicCompletion F) = 1 := by
    rw [hu, ← map_natCast (algebraMap F (E ⊗[F] v.adicCompletion F)), ← map_mul, inv_mul_cancel₀ hgF, map_one]
  let Fk : v.adicCompletion F → ℂ := fun x => psi (Formalism.UG.P.afsplitIE v (u * sp.symm (x, 0)))
  have hFadd : ∀ x y, Fk (x + y) = Fk x * Fk y := by
    intro x y
    simp only [Fk]
    rw [← hpsi_add, ← map_add, ← mul_add, ← map_add, Prod.mk_add_mk, add_zero]
  have hFg : ∀ w ∈ v.adicCompletionIntegers F, Fk ((g : v.adicCompletion F) * w) = 1 := by
    intro w hw
    simp only [Fk]
    have h1 : sp.symm ((g : v.adicCompletion F) * w, 0) = (g : E ⊗[F] v.adicCompletion F) * sp.symm (w, 0) := by
      apply sp.injective
      rw [map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, map_natCast]
      ext <;> simp
    rw [h1, ← mul_assoc, hug, one_mul]
    apply hpsi_int
    apply afsplitIE_mem_OAd
    rw [hint, RingEquiv.apply_symm_apply]
    exact ⟨hw, zero_mem _⟩
  let f : v.adicCompletionIntegers F → ℂ := fun r => Fk r
  have hfadd : ∀ a b, f (a + b) = f a * f b := fun a b => by
    simp only [f]
    push_cast
    exact hFadd _ _
  have hfm : ∀ a ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F), f a = 1 := by
    intro a ha
    rw [hgmax, Ideal.mem_span_singleton'] at ha
    obtain ⟨w, rfl⟩ := ha
    simp only [f]
    push_cast
    rw [mul_comm]
    exact hFg _ w.2
  refine ⟨fr, resChar f hfadd hfm, ?_, hlat, ?_⟩
  · obtain ⟨a, ha, hne'⟩ := hne
    have ha1 := ((hint a).1 ha).1
    intro h1
    apply hne'
    have h2 := resChar_residue f hfadd hfm ⟨(sp a).1, ha1⟩
    rw [h1, AddChar.one_apply] at h2
    have hea : e * a = sp.symm ((sp a).1, 0) := by
      apply sp.injective
      rw [map_mul, he, RingEquiv.apply_symm_apply]
      ext <;> simp
    rw [hea]
    exact h2.symm
  · intro y hy
    obtain ⟨hMint, hiff⟩ := GlobalTheory.T.hermitian_local_level_unitriangular_iff F E cm n J hJ hdet v sp hsig halg hint g hgmax L hL b fr hb hb2 hfr hlat t y hy
    refine ⟨hiff, fun _ => ?_⟩

    choose s hs hsd using hdual
    have hs1 : ∀ i l, (sp (s i l)).1 ∈ v.adicCompletionIntegers F := fun i l => ((hint _).1 (hs i l)).1
    have hcol := fst_mulVec sp y b fr hfr
    generalize (fr⁻¹ * bc ((RingHom.fst _ _).comp sp.toRingHom) y * fr : GL (Fin n) (v.adicCompletion F)) = Mg at hMint hcol ⊢
    set M : Matrix (Fin n) (Fin n) (v.adicCompletion F) := (Mg : Matrix (Fin n) (Fin n) (v.adicCompletion F)) with hMdef
    have hform1 := (GlobalTheory.T.split_place_lattice_components F E cm n J hJ hdet v sp hsig halg).2.2
    have hdual1 : ∀ i l, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (b l))).1 =
        (if i = l then 1 else 0) + (g : v.adicCompletion F) * (sp (s i l)).1 :=
      fun i l => fst_dual sp e he (i = l) _ _ g (hsd i l)
    have hfirst : ∀ i j, (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b j))).1 =
        ∑ l, M l j * (sp (hR cm.sig J (v.adicCompletion F) (bd i) (b l))).1 := by
      intro i j
      rw [hform1]
      simp only [hform1, hcol]
      exact fst_pair_sum _ _ _ M j

    have hMj : ∀ i : Fin n, ∀ hi : i.1 + 1 < n,
        (sp (hR cm.sig J (v.adicCompletion F) (bd i) (y.1 *ᵥ b ⟨i.1 + 1, hi⟩))).1 =
        M i ⟨i.1 + 1, hi⟩ + (g : v.adicCompletion F) * ∑ l, M l ⟨i.1 + 1, hi⟩ * (sp (s i l)).1 := by
      intro i hi
      rw [hfirst]
      simp only [hdual1, mul_add, Finset.sum_add_distrib, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun l _ => by ring
    set R0 : v.adicCompletion F := ∑ i : Fin n, if hi : i.1 + 1 < n then M i ⟨i.1 + 1, hi⟩ else 0 with hR0
    set W0 : v.adicCompletion F :=
      ∑ i : Fin n, if hi : i.1 + 1 < n then ∑ l, M l ⟨i.1 + 1, hi⟩ * (sp (s i l)).1 else 0 with hW0
    have hsup : supSum (hR cm.sig J (v.adicCompletion F)) b bd y.1 =
        sp.symm (R0 + (g : v.adicCompletion F) * W0, 0) := by
      apply sp.injective
      rw [RingEquiv.apply_symm_apply]
      unfold supSum
      rw [map_sum]
      refine Prod.ext ?_ ?_
      · rw [Prod.fst_sum, hR0, hW0, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        split_ifs with hi
        · exact hMj i hi
        · simp
      · rw [Prod.snd_sum]
        refine Finset.sum_eq_zero fun i _ => ?_
        split_ifs with hi
        · exact hR_snd_zero cm.sig sp hsig J _ _ (hbd1 i)
        · simp
    have hW0i : W0 ∈ v.adicCompletionIntegers F := by
      rw [hW0]
      refine sum_mem fun i _ => ?_
      split_ifs with hi
      · exact sum_mem fun l _ => mul_mem (hMint l _) (hs1 i l)
      · exact zero_mem _
    have hr : ∀ i : Fin n, (if hi : i.1 + 1 < n then M i ⟨i.1 + 1, hi⟩ else 0) ∈ v.adicCompletionIntegers F := by
      intro i
      split_ifs
      · exact hMint _ _
      · exact zero_mem _
    have hR0i : R0 ∈ v.adicCompletionIntegers F := by
      rw [hR0]; exact sum_mem fun i _ => hr i
    have hsumres : (∑ x : Fin n, ∑ y : Fin n,
        if (x : ℕ) + 1 = y ∧ (y : ℕ) < n ∧ (y : ℕ) ≠ n then redM F v M x y else 0) =
        IsLocalRing.residue _ (⟨R0, hR0i⟩ : v.adicCompletionIntegers F) := by
      have hsub : (⟨R0, hR0i⟩ : v.adicCompletionIntegers F) = ∑ i, ⟨_, hr i⟩ := Subtype.ext (by simp [hR0])
      rw [hsub, map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      by_cases hx : x.1 + 1 < n
      · rw [Finset.sum_eq_single ⟨x.1 + 1, hx⟩]
        · rw [if_pos ⟨rfl, hx, by omega⟩]
          simp only [redM, dif_pos (hMint x _)]
          congr 1
          exact Subtype.ext (by simp [hx])
        · intro y _ hy
          rw [if_neg]
          rintro ⟨h1, -, -⟩
          exact hy (Fin.ext h1.symm)
        · intro h
          exact absurd (Finset.mem_univ _) h
      · rw [Finset.sum_eq_zero]
        · have h0 : (⟨_, hr x⟩ : v.adicCompletionIntegers F) = 0 := Subtype.ext (by simp [hx])
          rw [h0, map_zero]
        · intro y _
          rw [if_neg]
          rintro ⟨h1, h2, -⟩
          omega
    rw [hsup]
    change Fk (R0 + (g : v.adicCompletion F) * W0) = _
    rw [hFadd, hFg _ hW0i, mul_one]
    unfold lamJ
    rw [Finset.prod_range_zero, mul_one, hsumres, resChar_residue]

end GlobalTheory.St.G.FirstFactorFrame
