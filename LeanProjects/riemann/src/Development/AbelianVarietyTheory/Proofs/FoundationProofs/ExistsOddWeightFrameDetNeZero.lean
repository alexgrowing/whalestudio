import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIndexOfGammaLe

noncomputable section

open UpperHalfPlane Filter GlobalTheory.OddFrame
open ModularForm (E₄ E₆)
open scoped MatrixGroups ModularForm Manifold Topology

namespace GlobalTheory.OddFrame

theorem exists_coset_reps {M : ℕ} (hM : 0 < M) (Γ : Subgroup SL(2, ℤ)) :
    ∃ (Q : Type) (_ : Fintype Q) (_ : Nonempty Q) (t : Q → SL(2, ℤ)), (∀ q, t q ∈ Γ) ∧
      (∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') ∧
      ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).FiniteIndex := finiteIndex_of_Gamma_le hM le_rfl
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M

  let H : Subgroup (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma M) :=
    Γ.map (QuotientGroup.mk' (CongruenceSubgroup.Gamma M))
  have hq : ∀ q : H, ∃ γ ∈ Γ, QuotientGroup.mk' (CongruenceSubgroup.Gamma M) γ = (q : _) :=
    fun q => Subgroup.mem_map.1 q.2
  choose t ht hmk using hq
  refine ⟨H, Fintype.ofFinite H, ⟨1⟩, t, ht, ?_, ?_⟩
  · intro q q' h
    apply Subtype.ext
    rw [← hmk q, ← hmk q', QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]
    exact h
  · intro γ hγ
    let g : H := ⟨QuotientGroup.mk' _ γ, Subgroup.mem_map_of_mem _ hγ⟩
    refine ⟨Equiv.mulRight g, fun q => ⟨t q * γ * (t (Equiv.mulRight g q))⁻¹, ?_, by group⟩⟩
    have h1 : QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t q * γ) =
        QuotientGroup.mk' (CongruenceSubgroup.Gamma M) (t (Equiv.mulRight g q)) := by
      rw [map_mul, hmk, hmk]
      rfl
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem,
      div_eq_mul_inv] at h1
    exact h1

theorem IsMF.sum_slash_reps {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {Q : Type} [Fintype Q] {t : Q → SL(2, ℤ)}
    (ht : ∀ γ ∈ Γ, ∃ π : Equiv.Perm Q, ∀ q, ∃ g ∈ CongruenceSubgroup.Gamma M, t q * γ = g * t (π q))
    {k : ℤ} {f : ℍ → ℂ} (hf : IsMF (CongruenceSubgroup.Gamma M) k f) : IsMF Γ k (∑ q, f ∣[k] t q) := by
  classical
  have : (CongruenceSubgroup.Gamma M).Normal := CongruenceSubgroup.Gamma_normal M
  have hsum : ∀ (A : SL(2, ℤ)) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]

  have hx : ∀ x : SL(2, ℤ), IsMF (CongruenceSubgroup.Gamma M) k (f ∣[k] x) := by
    intro x
    unfold IsMF
    refine ⟨fun g hg => ?_, mdiff_slash hf.2.1 k x, fun y => ?_⟩
    · rw [← SlashAction.slash_mul]
      have e : x * g = (x * g * x⁻¹) * x := by group
      rw [e, IsMF.slash_mul hf ((inferInstance : (CongruenceSubgroup.Gamma M).Normal).conj_mem g hg x) x]
    · rw [← SlashAction.slash_mul]
      exact hf.2.2 (x * y)
  have hS : IsMF (CongruenceSubgroup.Gamma M) k (∑ q, f ∣[k] t q) :=
    IsMF.sum Finset.univ (fun q _ => hx (t q))
  unfold IsMF
  refine ⟨fun γ hγ => ?_, hS.2.1, hS.2.2⟩
  obtain ⟨π, hπ⟩ := ht γ hγ
  rw [hsum]
  calc ∑ q, (f ∣[k] t q) ∣[k] γ = ∑ q, f ∣[k] t (π q) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        obtain ⟨g, hg, he⟩ := hπ q
        rw [← SlashAction.slash_mul, he, IsMF.slash_mul hf hg]
    _ = ∑ q, f ∣[k] t q := Equiv.sum_comp π (fun q => f ∣[k] t q)

theorem IsReps.signed_reps_injective {M : ℕ} {Γ : Subgroup SL(2, ℤ)} {r : ℕ} {s : Fin r → SL(2, ℤ)}
    (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    {Q : Type} {t : Q → SL(2, ℤ)} (ht : ∀ q, t q ∈ Γ)
    (hinj : ∀ q q', t q * (t q')⁻¹ ∈ CongruenceSubgroup.Gamma M → q = q') :
    (∀ i j q q', t q * s i * (t q' * s j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j ∧ q = q') ∧
      ∀ i j q q', -(t q * s i * (t q' * s j)⁻¹) ∉ CongruenceSubgroup.Gamma M := by
  have hA : ∀ i j q q' (γ : SL(2, ℤ)), γ ∈ Γ →
      (s i = (t q)⁻¹ * γ * t q' * s j ∨ s i = -((t q)⁻¹ * γ * t q' * s j)) → i = j := by
    intro i j q q' γ hγ h
    exact hs.2 i j _ (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem (ht q)) hγ) (ht q')) h
  have key : ∀ i j q q', (t q)⁻¹ * (t q * s i * (t q' * s j)⁻¹) * t q' * s j = s i := by
    intro i j q q'; group
  have diag : ∀ i q q', t q * s i * (t q' * s i)⁻¹ = t q * (t q')⁻¹ := by
    intro i q q'; group
  refine ⟨fun i j q q' h => ?_, fun i j q q' h => ?_⟩
  · have hij : i = j := hA i j q q' _ (hle h) (Or.inl (key i j q q').symm)
    subst hij
    refine ⟨rfl, hinj q q' ?_⟩
    rwa [diag] at h
  · have hΓ := hle h
    have hij : i = j := by
      refine hA i j q q' _ hΓ (Or.inr ?_)
      rw [mul_neg, neg_mul, neg_mul, key, neg_neg]
    subst hij
    rw [diag] at hΓ
    apply hneg
    have hY : t q * (t q')⁻¹ ∈ Γ := Γ.mul_mem (ht q) (Γ.inv_mem (ht q'))
    have e : (-1 : SL(2, ℤ)) = -(t q * (t q')⁻¹) * (t q * (t q')⁻¹)⁻¹ := by
      rw [neg_mul, mul_inv_cancel]
    rw [e]
    exact Γ.mul_mem hΓ (Γ.inv_mem hY)

theorem exists_odd_det_evM_ne_zero (M : ℕ) (Γ : Subgroup SL(2, ℤ)) (r : ℕ) (s : Fin r → SL(2, ℤ)) (τ₀ : ℍ)
    (hM : 0 < M) (hle : CongruenceSubgroup.Gamma M ≤ Γ) (hneg : (-1 : SL(2, ℤ)) ∉ Γ) (hs : IsReps Γ s)
    (H : ∀ (ι : Type) [Fintype ι] (x : ι → SL(2, ℤ)) (c : ι → ℂ),
      (∀ i j, x i * (x j)⁻¹ ∈ CongruenceSubgroup.Gamma M → i = j) →
      (∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f → ∑ i, c i * (f ∣[k] x i) τ₀ = 0) →
      c = 0) :
    ∃ (w : Fin r → ℤ) (F : Fin r → ℍ → ℂ), (∀ j, Odd (w j) ∧ IsMF Γ (w j) (F j)) ∧
      (evM s w F τ₀).det ≠ 0 := by
  classical
  obtain ⟨Q, _, ⟨q0⟩, t, ht, hinj, hperm⟩ := exists_coset_reps hM Γ
  have hsum : ∀ (A : SL(2, ℤ)) (k : ℤ) (u : Finset Q) (g : Q → ℍ → ℂ),
      (∑ q ∈ u, g q) ∣[k] A = ∑ q ∈ u, g q ∣[k] A := by
    intro A k u g
    refine Finset.induction_on u (by simp) ?_
    intro a u ha ih
    rw [Finset.sum_insert ha, Finset.sum_insert ha, SlashAction.add_slash, ih]
  obtain ⟨hpos, hneg'⟩ := IsReps.signed_reps_injective hle hneg hs ht hinj

  let vec : ℤ → (ℍ → ℂ) → Fin r → ℂ := fun k f i => ((∑ q, f ∣[k] t q) ∣[k] s i) τ₀
  let V : Set (Fin r → ℂ) :=
    {v | ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧ v = vec k f}
  have hvec : ∀ k f i, vec k f i = ∑ q, (f ∣[k] (t q * s i)) τ₀ := by
    intro k f i
    simp only [vec]
    rw [hsum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun q _ => by rw [SlashAction.slash_mul]

  have hV : Submodule.span ℂ V = ⊤ := by
    by_contra hne
    obtain ⟨φ, hφ, hker⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    let c : Fin r → ℂ := fun i => φ (fun j => if i = j then 1 else 0)
    have hφc : ∀ v, φ v = ∑ i, v i * c i := by
      intro v
      rw [LinearMap.pi_apply_eq_sum_univ φ v]
      simp only [c, smul_eq_mul]
    apply hφ
    have hc0 : c = 0 := by
      let x : Bool × Fin r × Q → SL(2, ℤ) := fun a =>
        if a.1 then t a.2.2 * s a.2.1 else -(t a.2.2 * s a.2.1)
      let c' : Bool × Fin r × Q → ℂ := fun a => if a.1 then c a.2.1 else -c a.2.1
      have ineg : ∀ B : SL(2, ℤ), (-B)⁻¹ = -B⁻¹ := fun B =>
        inv_eq_of_mul_eq_one_right (by rw [neg_mul_neg, mul_inv_cancel])
      have hx : ∀ a b, x a * (x b)⁻¹ ∈ CongruenceSubgroup.Gamma M → a = b := by
        rintro ⟨_ | _, i, q⟩ ⟨_ | _, j, q'⟩ h <;>
          simp only [x, Bool.false_eq_true, ↓reduceIte] at h
        · rw [ineg, neg_mul_neg] at h
          obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
        · rw [neg_mul] at h
          exact absurd h (hneg' i j q q')
        · rw [ineg, mul_neg] at h
          exact absurd h (hneg' i j q q')
        · obtain ⟨rfl, rfl⟩ := hpos i j q q' h
          rfl
      have hrel : ∀ (k : ℤ) (f : ℍ → ℂ), IsMF (CongruenceSubgroup.Gamma M) k f →
          ∑ a, c' a * (f ∣[k] x a) τ₀ = 0 := by
        intro k f hf
        rw [Fintype.sum_prod_type, Fintype.sum_bool]
        simp only [x, c', Bool.false_eq_true, ↓reduceIte]
        rcases Int.even_or_odd k with hk | hk
        · simp only [slash_neg_of_even hk, neg_mul, Finset.sum_neg_distrib, add_neg_cancel]
        · have h0 : φ (vec k f) = 0 := hker (Submodule.subset_span ⟨k, f, hk, hf, rfl⟩)
          rw [hφc] at h0
          simp only [hvec] at h0
          have hS : ∑ i, ∑ q, c i * (f ∣[k] (t q * s i)) τ₀ = 0 := by
            rw [← h0]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Finset.mul_sum, mul_comm]
          simp only [slash_neg_of_odd hk, Pi.neg_apply, neg_mul_neg]
          rw [Fintype.sum_prod_type, hS, add_zero]
      have hc'0 := H _ x c' hx hrel
      funext i
      simpa [c'] using congrFun hc'0 (true, i, q0)
    refine LinearMap.ext fun v => ?_
    rw [hφc v, hc0]
    simp

  obtain ⟨b, hbV, hspan, hli⟩ := exists_linearIndependent ℂ V
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range ((↑) : b → Fin r → ℂ)) := by
    rw [Subtype.range_coe, hspan, hV]
  let e := (Pi.basisFun ℂ (Fin r)).indexEquiv (Module.Basis.mk hli hsp)
  have hmem : ∀ j, ∃ k f, Odd k ∧ IsMF (CongruenceSubgroup.Gamma M) k f ∧
      (e j : Fin r → ℂ) = vec k f := fun j => hbV (e j).2
  choose w f hw hf hv using hmem
  refine ⟨w, fun j => ∑ q, f j ∣[w j] t q, fun j => ⟨hw j, IsMF.sum_slash_reps hperm (hf j)⟩, ?_⟩
  have hcols : (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) =
      fun j => (e j : Fin r → ℂ) := by
    funext j i
    rw [hv j]
    rfl
  have hli' : LinearIndependent ℂ (fun j => Matrix.transpose (evM s w (fun j => ∑ q, f j ∣[w j] t q) τ₀) j) := by
    rw [hcols]
    exact hli.comp e e.injective
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 hli')).ne_zero

end GlobalTheory.OddFrame
