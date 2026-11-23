import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TopPairDForm
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.Cartier
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW secZ ptF LiesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR levDet secRing move)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.OrbitSep

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogKSDiv.KSBasis

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

abbrev ksbConj (τ : E →+* ℂ) : E →+* ℂ := (starRingEnd ℂ).comp τ

theorem ksbConj_ksbConj (τ : E →+* ℂ) : ksbConj (ksbConj τ) = τ := by
  ext x; simp [ksbConj]

theorem cmHostImaginaryRootValue_ne_zero (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : H.rt0 ≠ 0 := by
  intro h
  have h2 := H.sqrt_neg_disc_sq
  rw [h] at h2
  have hd : (H.d : ℂ) = 0 := by linear_combination h2
  exact H.d_prime.ne_zero (by exact_mod_cast hd)

theorem cmHostImaginaryRootValue_conj_eq_neg (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) : starRingEnd ℂ H.rt0 = -H.rt0 := by
  have h := H.sqrt_neg_disc_sq
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [pow_two] at hre him
  have hd : (0:ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have hx : H.rt0.re = 0 := by
    by_contra hx
    have hy : H.rt0.im = 0 := by
      have h3 : (2 * H.rt0.re) * H.rt0.im = 0 := by linarith
      exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero two_ne_zero hx)
    rw [hy] at hre
    nlinarith [sq_nonneg H.rt0.re]
  apply Complex.ext <;> simp [hx]

theorem ksb_emb_rt (τ : E →+* ℂ) : τ (H.rt : E) = H.rt0 ∨ τ (H.rt : E) = -H.rt0 := by
  have h1 : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (algebraMap (𝓞 E) E) H.rt_sq
    simpa using this
  have h : (τ (H.rt : E)) ^ 2 = H.rt0 ^ 2 := by
    rw [← map_pow, h1, map_neg, map_natCast, H.sqrt_neg_disc_sq]
  exact sq_eq_sq_iff_eq_or_eq_neg.1 h

theorem ksbConj_mem_iff (τ : E →+* ℂ) : ksbConj τ (H.rt : E) = H.rt0 ↔ ¬ τ (H.rt : E) = H.rt0 := by
  have hne : -H.rt0 ≠ H.rt0 := fun h => cmHostImaginaryRootValue_ne_zero H (by linear_combination -h / 2)
  simp only [ksbConj, RingHom.comp_apply]
  rcases ksb_emb_rt (H := H) τ with h | h
  · rw [h, cmHostImaginaryRootValue_conj_eq_neg]; simp [hne]
  · rw [h, map_neg, cmHostImaginaryRootValue_conj_eq_neg, neg_neg]; exact iff_of_true rfl hne

theorem ksb_card_cmType :
    Fintype.card {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} = Module.finrank ℚ E / 2 := by
  classical
  have e1 : {τ : E →+* ℂ // ¬ τ (H.rt : E) = H.rt0} ≃ {τ : E →+* ℂ // τ (H.rt : E) = H.rt0} :=
    { toFun := fun τ => ⟨ksbConj τ.1, (ksbConj_mem_iff τ.1).2 τ.2⟩
      invFun := fun τ => ⟨ksbConj τ.1, by rw [ksbConj_mem_iff, not_not]; exact τ.2⟩
      left_inv := fun τ => Subtype.ext (ksbConj_ksbConj τ.1)
      right_inv := fun τ => Subtype.ext (ksbConj_ksbConj τ.1) }
  have h1 := Fintype.card_congr (Equiv.sumCompl fun τ : E →+* ℂ => τ (H.rt : E) = H.rt0)
  rw [Fintype.card_sum, Fintype.card_congr e1, NumberField.Embeddings.card E ℂ] at h1
  omega

variable (Dw : Datum H)

abbrev FlatIx : Type := Σ τ : E →+* ℂ, Fin (Dw.mult τ)

def ksbFst (P : PairIx H Dw) : FlatIx Dw := ⟨P.1.1, P.2.1⟩

def ksbSnd (P : PairIx H Dw) : FlatIx Dw := ⟨ksbConj P.1.1, P.2.2⟩

theorem ksbFst_ne_ksbSnd (P Q : PairIx H Dw) : ksbFst Dw P ≠ ksbSnd Dw Q := by
  intro h
  have h1 := congrArg Sigma.fst h
  simp only [ksbFst, ksbSnd] at h1
  have h2 := P.1.2
  rw [h1, ksbConj_mem_iff] at h2
  exact h2 Q.1.2

theorem ksb_pair_inj {P Q : PairIx H Dw} (h1 : ksbFst Dw P = ksbFst Dw Q) (h2 : ksbSnd Dw P = ksbSnd Dw Q) :
    P = Q := by
  obtain ⟨⟨τ, hτ⟩, i, k⟩ := P
  obtain ⟨⟨τ', hτ'⟩, i', k'⟩ := Q
  simp only [ksbFst, ksbSnd, Sigma.mk.inj_iff] at h1 h2
  obtain ⟨rfl, hi⟩ := h1
  obtain ⟨-, hk⟩ := h2
  rw [heq_iff_eq] at hi hk
  subst hi hk
  rfl

theorem ksb_exists_pair (s t : FlatIx Dw) (h : t.1 = ksbConj s.1) (hs : s.1 (H.rt : E) = H.rt0) :
    ∃ P, ksbFst Dw P = s ∧ ksbSnd Dw P = t := by
  obtain ⟨τ, i⟩ := s
  obtain ⟨σ, k⟩ := t
  simp only at h hs
  subst h
  exact ⟨⟨⟨τ, hs⟩, i, k⟩, rfl, rfl⟩

theorem ksb_card_pairIx : Nat.card (PairIx H Dw) = Dw.dim := by
  classical
  rw [Nat.card_eq_fintype_card]
  have hm1 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Dw.mult τ.1 = Dw.p := fun τ => if_pos τ.2
  have hm2 : ∀ τ : {τ : E →+* ℂ // τ (H.rt : E) = H.rt0}, Dw.mult (ksbConj τ.1) = Dw.q :=
    fun τ => if_neg (by rw [ksbConj_mem_iff, not_not]; exact τ.2)
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin, hm1, hm2]
  rw [Finset.sum_const, Finset.card_univ, smul_eq_mul, Datum.dim, ksb_card_cmType]
  ring

end GlobalTheory.LogKSDiv.KSBasis

namespace GlobalTheory.LogKSDiv.KSBasis

open scoped Matrix

section Bal

open Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
  {l : Level H} (c : Coeff l) {R : Type} [CommRing R] (φ : c.F →+* R) {n : ℕ} (e : FlatIx Dw ≃ Fin n)

theorem ksb_exists_ne {s t : E →+* ℂ} (h : t ≠ ksbConj s) :
    ∃ a : 𝓞 E, s (a : E) ≠ starRingEnd ℂ (t (a : E)) := by
  by_contra hc
  push_neg at hc
  apply h
  have : s = ksbConj t := IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a => hc a)
  rw [this, ksbConj_ksbConj]

theorem ksb_embK_bar {s t : E →+* ℂ} (h : t = ksbConj s) (a : 𝓞 E) : embK c t (H.bar a) = embK c s a := by
  apply Subtype.ext
  rw [embK_coe, embK_coe, H.bar_eq, h]
  simp [ksbConj]

theorem ksb_embK_sub_ne {s t : E →+* ℂ} (h : t ≠ ksbConj s) :
    ∃ a : 𝓞 E, embK c s a - embK c t (H.bar a) ≠ 0 := by
  obtain ⟨a, ha⟩ := ksb_exists_ne h
  refine ⟨a, fun h0 => ha ?_⟩
  rw [sub_eq_zero] at h0
  have h1 := congrArg ((↑) : c.F → ℂ) h0
  rw [embK_coe, embK_coe, H.bar_eq, IsCMField.complexEmbedding_complexConj] at h1
  exact h1

def ksbA (a : 𝓞 E) : Matrix (Fin n) (Fin n) R := Matrix.diagonal fun x => φ (embK c (e.symm x).1 a)

theorem ksbA_row (a : 𝓞 E) (s : FlatIx Dw) :
    ksbA Dw c φ e a (e s) = Pi.single (e s) (φ (embK c s.1 a)) := by
  funext y
  simp only [ksbA, Matrix.diagonal_apply, Pi.single_apply, Equiv.symm_apply_apply]
  by_cases hy : y = e s
  · subst hy; simp
  · rw [if_neg (Ne.symm hy), if_neg hy]

def ksbEps : Fin Dw.dim ≃ PairIx H Dw :=
  (Fintype.equivFinOfCardEq (by rw [← Nat.card_eq_fintype_card]; exact ksb_card_pairIx Dw)).symm

theorem ksb_mem_balanced_iff (Θ : Matrix (Fin n) (Fin n) R) :
    Θ ∈ LogKS.balanced H.bar (ksbA Dw c φ e) ↔
      Θᵀ = Θ ∧ ∀ s t : FlatIx Dw, t.1 ≠ ksbConj s.1 → Θ (e s) (e t) = 0 := by
  refine (LogKS.mem_balanced_diagonal (fun a => H.bar a) (fun x a => φ (embK c (e.symm x).1 a)) Θ).trans ?_
  refine and_congr_right fun _ => ⟨fun h s t hst => ?_, fun h a x y => ?_⟩
  · obtain ⟨a, ha⟩ := ksb_embK_sub_ne c hst
    have hu : IsUnit (φ (embK c s.1 a - embK c t.1 (H.bar a))) := (IsUnit.mk0 _ ha).map φ
    have h2 := h a (e s) (e t)
    simp only [Equiv.symm_apply_apply] at h2
    rw [← map_sub] at h2
    exact hu.mul_right_eq_zero.1 h2
  · obtain ⟨s, rfl⟩ := e.surjective x
    obtain ⟨t, rfl⟩ := e.surjective y
    simp only [Equiv.symm_apply_apply]
    by_cases hst : t.1 = ksbConj s.1
    · rw [ksb_embK_bar c hst, sub_self, zero_mul]
    · rw [h s t hst, mul_zero]

theorem ksb_symPair_apply (P : PairIx H Dw) (x y : Fin n) :
    (symPair (R := R) e P) x y =
      (if x = e (ksbFst Dw P) ∧ y = e (ksbSnd Dw P) then 1 else 0) +
        (if x = e (ksbSnd Dw P) ∧ y = e (ksbFst Dw P) then 1 else 0) := rfl

theorem ksb_symPair_eq_zero (P : PairIx H Dw) (s t : FlatIx Dw) (h : t.1 ≠ ksbConj s.1) :
    (symPair (R := R) e P) (e s) (e t) = 0 := by
  rw [ksb_symPair_apply, if_neg, if_neg, add_zero]
  · rintro ⟨h1, h2⟩
    rw [e.injective.eq_iff] at h1 h2
    subst h1 h2
    exact h (by simp only [ksbFst, ksbSnd, ksbConj_ksbConj])
  · rintro ⟨h1, h2⟩
    rw [e.injective.eq_iff] at h1 h2
    subst h1 h2
    exact h (by simp only [ksbFst, ksbSnd, ksbConj_ksbConj])

theorem ksb_symPair_transpose (P : PairIx H Dw) : (symPair (R := R) e P)ᵀ = symPair e P := by
  ext x y
  rw [Matrix.transpose_apply, ksb_symPair_apply, ksb_symPair_apply, add_comm]
  congr 1 <;> exact if_congr and_comm rfl rfl

theorem ksb_symPair_mem (P : PairIx H Dw) : symPair e P ∈ LogKS.balanced H.bar (ksbA Dw c φ e) :=
  (ksb_mem_balanced_iff Dw c φ e _).2
    ⟨ksb_symPair_transpose Dw e P, fun s t h => ksb_symPair_eq_zero Dw e P s t h⟩

theorem ksb_sum_apply_fst (f : PairIx H Dw → R) (Q : PairIx H Dw) :
    (∑ P, f P • symPair (R := R) e P) (e (ksbFst Dw Q)) (e (ksbSnd Dw Q)) = f Q := by
  rw [Matrix.sum_apply, Finset.sum_eq_single Q]
  · rw [Matrix.smul_apply, ksb_symPair_apply, if_pos ⟨rfl, rfl⟩, if_neg, add_zero, smul_eq_mul, mul_one]
    rintro ⟨h1, -⟩
    exact ksbFst_ne_ksbSnd Dw Q Q (e.injective h1)
  · intro P _ hP
    rw [Matrix.smul_apply, ksb_symPair_apply, if_neg, if_neg, add_zero, smul_zero]
    · rintro ⟨h1, -⟩
      exact ksbFst_ne_ksbSnd Dw Q P (e.injective h1)
    · rintro ⟨h1, h2⟩
      exact hP (ksb_pair_inj Dw (e.injective h1) (e.injective h2)).symm
  · intro h
    exact absurd (Finset.mem_univ Q) h

theorem ksb_sum_apply_snd (f : PairIx H Dw → R) (Q : PairIx H Dw) :
    (∑ P, f P • symPair (R := R) e P) (e (ksbSnd Dw Q)) (e (ksbFst Dw Q)) = f Q := by
  rw [Matrix.sum_apply, Finset.sum_eq_single Q]
  · rw [Matrix.smul_apply, ksb_symPair_apply, if_neg, if_pos ⟨rfl, rfl⟩, zero_add, smul_eq_mul, mul_one]
    rintro ⟨h1, -⟩
    exact ksbFst_ne_ksbSnd Dw Q Q (e.injective h1).symm
  · intro P _ hP
    rw [Matrix.smul_apply, ksb_symPair_apply, if_neg, if_neg, add_zero, smul_zero]
    · rintro ⟨h1, h2⟩
      exact hP (ksb_pair_inj Dw (e.injective h2) (e.injective h1)).symm
    · rintro ⟨h1, -⟩
      exact ksbFst_ne_ksbSnd Dw P Q (e.injective h1).symm
  · intro h
    exact absurd (Finset.mem_univ Q) h

theorem ksb_decomp (Θ : Matrix (Fin n) (Fin n) R) (hΘ : Θ ∈ LogKS.balanced H.bar (ksbA Dw c φ e)) :
    ∑ P, Θ (e (ksbFst Dw P)) (e (ksbSnd Dw P)) • symPair (R := R) e P = Θ := by
  obtain ⟨hsym, hz⟩ := (ksb_mem_balanced_iff Dw c φ e Θ).1 hΘ
  ext x y
  obtain ⟨s, rfl⟩ := e.surjective x
  obtain ⟨t, rfl⟩ := e.surjective y
  by_cases hst : t.1 = ksbConj s.1
  · by_cases hs : s.1 (H.rt : E) = H.rt0
    · obtain ⟨P, rfl, rfl⟩ := ksb_exists_pair Dw s t hst hs
      exact ksb_sum_apply_fst Dw e _ P
    · have ht : t.1 (H.rt : E) = H.rt0 := by rw [hst, ksbConj_mem_iff]; exact hs
      have hts : s.1 = ksbConj t.1 := by rw [hst, ksbConj_ksbConj]
      obtain ⟨P, rfl, rfl⟩ := ksb_exists_pair Dw t s hts ht
      rw [ksb_sum_apply_snd]
      have h3 := congrFun (congrFun hsym (e (ksbSnd Dw P))) (e (ksbFst Dw P))
      rw [Matrix.transpose_apply] at h3
      exact h3
  · rw [hz s t hst, Matrix.sum_apply]
    exact Finset.sum_eq_zero fun P _ => by rw [Matrix.smul_apply, ksb_symPair_eq_zero Dw e P s t hst, smul_zero]

def ksbEquiv : LogKS.balanced H.bar (ksbA Dw c φ e) ≃ₗ[R] (PairIx H Dw → R) where
  toFun Θ P := Θ.1 (e (ksbFst Dw P)) (e (ksbSnd Dw P))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨∑ P, f P • symPair e P,
    Submodule.sum_mem _ fun P _ => Submodule.smul_mem _ _ (ksb_symPair_mem Dw c φ e P)⟩
  left_inv Θ := Subtype.ext (ksb_decomp Dw c φ e Θ.1 Θ.2)
  right_inv f := funext fun Q => ksb_sum_apply_fst Dw e f Q

def ksbBasis : Module.Basis (PairIx H Dw) R (LogKS.balanced H.bar (ksbA Dw c φ e)) :=
  Module.Basis.ofEquivFun (ksbEquiv Dw c φ e)

theorem ksbBasis_apply (P : PairIx H Dw) : (ksbBasis Dw c φ e P).1 = symPair e P := by
  rw [ksbBasis, Module.Basis.coe_ofEquivFun]
  simp [ksbEquiv, Pi.single_apply]

end Bal

end GlobalTheory.LogKSDiv.KSBasis

namespace GlobalTheory.LogKSDiv

open KSBasis

theorem KSBasis.ksb_map_reindex {R M N ι κ : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
    [Module R N] (b : Module.Basis ι R N) (f : M ≃ₗ[R] N) (ε : κ ≃ ι) (j : κ) :
    f (((b.map f.symm).reindex ε.symm) j) = b (ε j) := by
  simp

theorem exists_logKS_symPair_basis : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c) (U : TF.Y.X.affineOpens) (n : ℕ) (e : (Σ τ : E →+* ℂ, Fin (Dw.mult τ)) ≃ Fin n) (v : Fin n → (Sp (DualNumber Γ(TF.Y.X, U.1)) ⟶ TF.Y.t.G.left)) (φU : c.F →+* Γ(TF.Y.X, U.1)), (∀ i, IsTanAtG TF.Y.t (LogKS.chart U) (v i)) → (∀ w', IsTanAtG TF.Y.t (LogKS.chart U) w' → ∃! cf : Fin n → Γ(TF.Y.X, U.1), IsCombAtG TF.Y.t (LogKS.chart U) v cf w') → (∀ (a : 𝓞 E) (τ : E →+* ℂ) (i : Fin (Dw.mult τ)), IsCombAtG TF.Y.t (LogKS.chart U) v (Pi.single (e ⟨τ, i⟩) (φU (embK c τ a))) (v (e ⟨τ, i⟩) ≫ (TF.Y.t.act.act a).left)) → ∃ (ε : Fin Dw.dim ≃ GlobalTheory.LogKSDiv.PairIx H Dw) (b : Module.Basis (Fin Dw.dim) Γ(TF.Y.X, U.1) (LogKS.logDer TF.Y.s (Scheme.IdealSheafData.vanishingIdeal (LogKS.interior TF.Y).compl) U)), ∀ j, LogKS.IsKS TF.Y.t (LogKS.interior TF.Y) U v (b j).1 (GlobalTheory.LogKSDiv.symPair e (ε j)) := by
  intro E _ _ _ H Dw l Xo c TF U n e v φU hv huniq hact
  have hA : ∀ a i, IsCombAtG TF.Y.t (LogKS.chart U) v (ksbA Dw c φU e a i) (v i ≫ (TF.Y.t.act.act a).left) := by
    intro a i
    obtain ⟨s, rfl⟩ := e.surjective i
    rw [ksbA_row]
    exact hact a s.1 s.2
  obtain ⟨e', he'⟩ := TF.logKS U n v (ksbA Dw c φU e) hv huniq hA
  refine ⟨ksbEps Dw, ((ksbBasis Dw c φU e).map e'.symm).reindex (ksbEps Dw).symm, fun j => (he' _ _).2 ?_⟩
  rw [ksb_map_reindex (ksbBasis Dw c φU e) e' (ksbEps Dw) j, ksbBasis_apply]

end GlobalTheory.LogKSDiv
