import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.IntegralFormsEqSpan

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Up

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ)

def upO (A : Submodule (𝓞 B.KO) X.Forms) : Submodule (Op X la N) (Rp X la N) :=
  Submodule.span (Op X la N) (emb X la N '' (A : Set X.Forms))

variable {X}

theorem emb_mem_upO {A : Submodule (𝓞 B.KO) X.Forms} {F : X.Forms} (h : F ∈ A) : emb X la N F ∈ upO X la N A :=
  Submodule.subset_span ⟨F, h, rfl⟩

theorem upO_mono {A A' : Submodule (𝓞 B.KO) X.Forms} (h : A ≤ A') : upO X la N A ≤ upO X la N A' :=
  Submodule.span_mono (Set.image_mono h)

theorem upO_mul_le (A A' : Submodule (𝓞 B.KO) X.Forms) : upO X la N A * upO X la N A' ≤ upO X la N (A * A') := by
  unfold upO
  rw [Submodule.span_mul_span]
  refine Submodule.span_mono ?_
  rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
  exact ⟨a * b, Submodule.mul_mem_mul ha hb, map_mul _ _ _⟩

theorem upO_pow_le (A : Submodule (𝓞 B.KO) X.Forms) (n : ℕ) : upO X la N A ^ n ≤ upO X la N (A ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, Submodule.one_le]
    exact Submodule.subset_span ⟨1, Submodule.one_le.1 le_rfl, map_one _⟩
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (mul_le_mul' ih le_rfl).trans (upO_mul_le la N _ _)

theorem mem_span_emb_iff {ka : WeightFamilies.Wt D j} {M : Submodule (𝓞 B.KO) X.Forms} (hM : M ≤ X.Msup ka) (f : ↥(Vw X la N ka)) :
    f ∈ Submodule.span (Op X la N) {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} ↔
      (f : Rp X la N) ∈ upO X la N M := by
  rw [mem_span_subtype_iff (R := Op X la N) (Vw X la N ka)]
  have h : ((↑) '' {f : ↥(Vw X la N ka) | ∃ F ∈ M, (f : Rp X la N) = emb X la N F} : Set (Rp X la N)) =
      emb X la N '' (M : Set X.Forms) := by
    ext x
    constructor
    · rintro ⟨f, ⟨F, hF, hf⟩, rfl⟩; exact ⟨F, hF, hf.symm⟩
    · rintro ⟨F, hF, rfl⟩
      obtain ⟨F', _, rfl⟩ := hM hF
      exact ⟨⟨_, emb_mem_Vw X la N ka F'⟩, ⟨_, hF, rfl⟩, rfl⟩
  rw [h]
  rfl

end Up

section Sec

variable {X : PJ D B P j} (la : HeightOneSpectrum (𝓞 B.KO)) {N : ℕ} {wL : WeightFamilies.Wt D j} (w : Fin N → B.Cusp j wL)
  {W : Submodule (𝓞 B.KO) (B.Cusp j wL)}

theorem sec_mem_upO (hw : ∀ k, w k ∈ W) (i : Fin (WeightFamilies.dimY D j + 1)) : sec X la w i ∈ upO X la N (X.emb wL W) := by
  unfold sec
  refine Submodule.sum_mem _ fun k _ => ?_
  rw [algebraMap_smul]
  exact Submodule.smul_mem _ _ (emb_mem_upO la N ⟨w k, hw k, rfl⟩)

theorem secPow_mem_upO (hw : ∀ k, w k ∈ W) (al : Fin (WeightFamilies.dimY D j) → ℕ) :
    secPow X la w al ∈ upO X la N (X.emb wL W) ^ ∑ i, al i := by
  unfold secPow
  have h : ∀ s : Finset (Fin (WeightFamilies.dimY D j)),
      ∏ i ∈ s, sec X la w i.succ ^ al i ∈ upO X la N (X.emb wL W) ^ ∑ i ∈ s, al i := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => simp only [Finset.prod_empty, Finset.sum_empty, pow_zero]; exact Submodule.one_le.1 le_rfl
    | insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha, pow_add]
      exact Submodule.mul_mem_mul (Submodule.pow_mem_pow _ (sec_mem_upO la w hw _) _) ih
  exact h Finset.univ

theorem secPow_mul_mem_upO (hw : ∀ k, w k ∈ W) (al : Fin (WeightFamilies.dimY D j) → ℕ) {n : ℕ} (hn : ∑ i, al i ≤ n)
    {A : Submodule (𝓞 B.KO) X.Forms} {F : X.Forms} (hF : F ∈ A) :
    secPow X la w al * sec X la w 0 ^ (n - ∑ i, al i) * emb X la N F ∈ upO X la N (X.emb wL W ^ n * A) := by
  refine upO_mul_le la N _ _ (Submodule.mul_mem_mul (upO_pow_le la N _ _ ?_) (emb_mem_upO la N hF))
  have h := Submodule.mul_mem_mul (secPow_mem_upO (X := X) la w hw al)
    (Submodule.pow_mem_pow _ (sec_mem_upO (X := X) la w hw 0) (n - ∑ i, al i))
  rwa [← pow_add, Nat.add_sub_cancel' hn] at h

end Sec

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B)

theorem thetaSpan_le_integralForms (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T)) :
    Th1 X la G.N (addL wF wL T) S wL wF T ≤ M1 X la G.N (addL wF wL T) :=
  Submodule.span_mono (Set.image_mono (Submodule.comap_mono (Submodule.span_mono (Set.image_mono hΘ))))

theorem mem_thetaSpan_iff (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (f : ↥(Vw X la G.N (addL wF wL T))) : f ∈ Th1 X la G.N (addL wF wL T) S wL wF T ↔
      (f : Rp X la G.N) ∈ upO X la G.N (X.Theta S (addL wF wL T) wL wF T) := by
  rw [Th1_eq X la G.N _ S wL wF T hΘ]
  exact mem_span_emb_iff la G.N hΘ f

theorem generators_le_thetaSpan (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ i, G.th' i ∈ X.Thc S.sF wF) :
    N1 G la ≤ Th1 X la G.N (addL wF wL T) S wL wF T := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨al, i, hal, hf⟩
  refine (mem_thetaSpan_iff G la S hΘ f).2 ?_
  rw [hf]
  have hle : ∑ i, al i ≤ T := le_trans hal.le (Nat.sub_le _ _)
  exact upO_mono la G.N (le_sup_of_le_left le_sup_left)
    (secPow_mul_mem_upO la G.w hw al hle (A := X.emb wF (X.Thc S.sF wF)) ⟨G.th' i, hth i, rfl⟩)

theorem zeroGenerators_le_thetaSpan (hΘ : X.Theta S (addL wF wL T) wL wF T ≤ X.Msup (addL wF wL T))
    (hw : ∀ k, G.w k ∈ X.WWc S.sW wL) (hth : ∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF))
    (hal : ∀ k, ∑ i, G.alz k i = a0 D j T) :
    Zl G la ≤ Th1 X la G.N (addL wF wL T) S wL wF T := by
  refine Submodule.span_le.2 ?_
  rintro f ⟨k, hf⟩
  refine (mem_thetaSpan_iff G la S hΘ f).2 ?_
  rw [hf]
  have h := secPow_mul_mem_upO la G.w hw (G.alz k) (n := a0 D j T) (hal k).le
    (A := X.emb (X.wF0 wL wF) (X.Thc S.s0 (X.wF0 wL wF))) ⟨G.th0 k, hth k, rfl⟩
  rw [hal k, Nat.sub_self, pow_zero, mul_one] at h
  exact upO_mono la G.N (le_sup_of_le_left le_sup_right) h

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
