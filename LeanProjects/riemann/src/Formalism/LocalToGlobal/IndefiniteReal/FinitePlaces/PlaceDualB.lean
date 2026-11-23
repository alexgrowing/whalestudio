import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceDualBSt
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsFurtherLast

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 160000

namespace Formalism.IndefR.Fin.PDB

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem exists_nat_eq_mul {K : Type} [Field K] [NumberField K] (b : 𝓞 K) (hb : b ≠ 0) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ c : 𝓞 K, (m : 𝓞 K) = b * c := by
  refine ⟨Ideal.absNorm (Ideal.span {b}), ?_, ?_⟩
  · have : Ideal.absNorm (Ideal.span {b}) ≠ 0 := by
      rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]; exact hb
    omega
  · obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {b}))
    exact ⟨c, by rw [← hc, mul_comm]⟩

theorem exists_nat_mul_mem {K : Type} [Field K] [NumberField K] (e : K) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : K) * e ∈ (algebraMap (𝓞 K) K).range := by
  obtain ⟨⟨a, b⟩, h⟩ := IsLocalization.surj (nonZeroDivisors (𝓞 K)) e
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul (b : 𝓞 K) (nonZeroDivisors.ne_zero b.2)
  refine ⟨m, hm, a * c, ?_⟩
  have h1 : (m : K) = algebraMap (𝓞 K) K b * algebraMap (𝓞 K) K c := by
    rw [← map_mul, ← hc, map_natCast]
  simp only at h
  rw [map_mul, h1, ← h]
  ring

theorem exists_nat_mul_intAf {F : Type} [Field F] [NumberField F] (t : Af F) :
    ∃ m : ℕ, 1 ≤ m ∧ (m : Af F) * t ∈ intAf F := by
  classical
  have hfin : {v : HeightOneSpectrum (𝓞 F) | t v ∉ v.adicCompletionIntegers F}.Finite :=
    Filter.eventually_cofinite.1 t.2
  have hloc : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m : ℕ, 1 ≤ m ∧
      (m : v.adicCompletion F) * t v ∈ v.adicCompletionIntegers F := by
    intro v
    obtain ⟨b, hb, hbt⟩ := HeightOneSpectrum.adicCompletion.mul_nonZeroDivisor_mem_adicCompletionIntegers v (t v)
    obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul b (nonZeroDivisors.ne_zero hb)
    refine ⟨m, hm, ?_⟩
    have h1 : (m : v.adicCompletion F) = algebraMap (𝓞 F) (v.adicCompletion F) b *
        algebraMap (𝓞 F) (v.adicCompletion F) c := by
      rw [← map_mul, ← hc, map_natCast]
    rw [h1, show algebraMap (𝓞 F) (v.adicCompletion F) b * algebraMap (𝓞 F) (v.adicCompletion F) c * t v
      = t v * algebraMap (𝓞 F) (v.adicCompletion F) b * algebraMap (𝓞 F) (v.adicCompletion F) c by ring]
    exact mul_mem hbt ((HeightOneSpectrum.coe_mem_adicCompletionIntegers (v := v) c))
  choose mv hmv hmt using hloc
  refine ⟨∏ v ∈ hfin.toFinset, mv v, Finset.one_le_prod' fun v _ => hmv v, fun v => ?_⟩
  have hev : evalV F v (((∏ w ∈ hfin.toFinset, mv w : ℕ) : Af F) * t) =
      ((∏ w ∈ hfin.toFinset, mv w : ℕ) : v.adicCompletion F) * t v := by
    rw [map_mul, map_natCast]
    rfl
  rw [hev]
  by_cases hv : v ∈ hfin.toFinset
  · rw [← Finset.mul_prod_erase _ _ hv]
    push_cast
    have e1 : ((mv v : v.adicCompletion F) * ∏ i ∈ hfin.toFinset.erase v, (mv i : v.adicCompletion F)) *
        t v = (∏ i ∈ hfin.toFinset.erase v, (mv i : v.adicCompletion F)) *
          ((mv v : v.adicCompletion F) * t v) := by ring
    rw [e1]
    exact mul_mem (prod_mem fun w _ => natCast_mem _ _) (hmt v)
  · have ht : t v ∈ v.adicCompletionIntegers F := by simpa using hv
    exact mul_mem (natCast_mem _ _) ht

lemma exists_nat_mem_AA : ∃ N : ℕ, 0 < N ∧ ((N : D.host.E)) ∈ (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) := by
  have hne : D.host.ccK ≠ ⊥ := D.host.ccK_ne_bot
  refine ⟨Ideal.absNorm D.host.ccK, Nat.pos_of_ne_zero fun h => hne (Ideal.absNorm_eq_zero_iff.1 h), ?_⟩
  have h1 : ((Ideal.absNorm D.host.ccK : 𝓞 D.host.K)) ∈ D.host.ccK := Ideal.absNorm_mem _
  have h2 : ((Ideal.absNorm D.host.ccK : 𝓞 D.host.E)) ∈ D.host.ccE := by
    have := Ideal.mem_map_of_mem (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) h1
    rw [map_natCast] at this
    exact this
  have hb : D.host.𝔟 ≠ ⊥ := by
    intro h
    have h2 := D.host.𝔟_spec.2
    rw [h] at h2
    simp at h2
  have h3 : ((Ideal.absNorm D.host.ccK : D.host.E)) ∈
      ((D.host.ccE : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) *
        ((D.host.𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E))⁻¹) := by
    have hm := FractionalIdeal.mul_mem_mul ((FractionalIdeal.mem_coeIdeal_of_mem (S := nonZeroDivisors (𝓞 D.host.E)) (P := D.host.E) h2))
      (FractionalIdeal.one_mem_inv_coe_ideal (K := D.host.E) hb)
    simpa using hm
  exact h3

lemma exists_nat_smul_mem {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    (hΛ : Submodule.IsLattice D.host.E Λ) (x : Fin n → D.host.E) :
    ∃ N : ℕ, 0 < N ∧ (N : D.host.E) • x ∈ Λ :=
  _root_.UpperTheory.Reformulated.B.Rd4.exists_nat_smul_mem hΛ x

section V

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

lemma one_mem_intAf : (1 : Af D.host.F) ∈ intAf D.host.F := fun v => by
  rw [map_one]; exact one_mem _

lemma gen_single (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (i : Fin T.rank) (j : Fin S.rank) :
    ∃ NT NS : ℕ, 0 < NT ∧ 0 < NS ∧ ∀ α ∈ intAf D.host.F, ∀ a ∈ D.host.AA,
      Matrix.single i j (pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * ((NT * NS : ℕ) : D.host.E))) ∈ latAll S T ΛS ΛT := by
  classical
  obtain ⟨NT, hNT, ht⟩ := exists_nat_smul_mem hT.1 (Pi.single i (1 : D.host.E))
  set w : Fin S.rank → D.host.E := Matrix.vecMul (Pi.single j (1 : D.host.E)) S.gram⁻¹ with hw
  obtain ⟨NS, hNS, hs⟩ := exists_nat_smul_mem hS.1 (star w)
  refine ⟨NT, NS, hNT, hNS, fun α hα a ha => ?_⟩
  have hrow : ∀ j', ∑ k, star (((NS : D.host.E) • star w) k) * S.gram k j' =
      (NS : D.host.E) * (if j = j' then 1 else 0) := by
    intro j'
    have h1 : ∀ k, star (((NS : D.host.E) • star w) k) = (NS : D.host.E) * w k := fun k => by
      simp [Pi.smul_apply, star_smul, star_natCast]
    simp_rw [h1, mul_assoc, ← Finset.mul_sum]
    congr 1
    have h2 : ∑ k, w k * S.gram k j' = (Matrix.vecMul w S.gram) j' := rfl
    rw [h2, hw, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (gram_det_ne S)),
      Matrix.vecMul_one, Pi.single_apply]
    by_cases h : j = j'
    · subst h; simp
    · simp [h, Ne.symm h]
  refine AddSubgroup.subset_closure ⟨α, hα, fun _ h => absurd trivial h, a, ha, _, hs, _, ht, ?_⟩
  ext i' j'
  rw [Matrix.of_apply, hrow j', Matrix.single_apply]
  simp only [Pi.smul_apply, Pi.single_apply, smul_eq_mul]
  by_cases hi : i = i' <;> by_cases hj : j = j'
  · subst hi; subst hj; simp; push_cast; ring_nf
  · simp [hi, hj]
  · simp [hi, Ne.symm hi]
  · simp [hi, Ne.symm hi]

abbrev fI (D : D7) : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)

lemma pairA_mul_one (α : Af D.host.F) : pairA D.host.F 0 α * pairA D.host.F 0 1 = pairA D.host.F 0 α :=
  Prod.ext (by show (0 : Ainf D.host.F) * 0 = 0; rw [mul_zero]) (by show α * 1 = α; rw [mul_one])

lemma splitIdem_mul_fI {e' : AE D} (h : IsSplitIdem D e') : e' * fI D = e' := by
  obtain ⟨h1, h2, v, ε, ⟨α, rfl, -, -⟩, h3⟩ := h
  have he : e' = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) := by
    rw [← h3, mul_add, h1, h2, add_zero]
  calc e' * fI D = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α) * fI D := by rw [← he]
    _ = e' * algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 α * pairA D.host.F 0 1) := by
        rw [map_mul, mul_assoc]
    _ = e' := by rw [pairA_mul_one, ← he]

lemma idemSum_mul_fI {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (he : IsIdemSum e P) :
    e * fI D = e ∧ cA D e * fI D = cA D e := by
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  have h1 : (∑ PP ∈ P, es PP) * fI D = ∑ PP ∈ P, es PP := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun PP hPP => splitIdem_mul_fI (hes PP hPP).1
  refine ⟨h1, ?_⟩
  have hc : cA D (fI D) = fI D := by
    show cA D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)) = _
    rw [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
    show (Algebra.TensorProduct.map (AlgHom.id D.host.F (AF D.host.F)) D.sp.cm.sig)
      (pairA D.host.F 0 1 ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul, map_one]; rfl
  calc cA D (∑ PP ∈ P, es PP) * fI D = cA D (∑ PP ∈ P, es PP) * cA D (fI D) := by rw [hc]
    _ = cA D ((∑ PP ∈ P, es PP) * fI D) := (map_mul _ _ _).symm
    _ = _ := by rw [h1]

end V

section V2

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

lemma tmul_fI (a : AF D.host.F) (z : D.host.E) :
    (a ⊗ₜ[D.host.F] z) * fI D = pairA D.host.F 0 (sndA D.host.F a) ⊗ₜ[D.host.F] z := by
  rw [fI, Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply,
    Algebra.TensorProduct.tmul_mul_tmul, mul_one]
  congr 1
  exact Prod.ext (by show a.1 * 0 = 0; rw [mul_zero]) (by show a.2 * 1 = sndA D.host.F a; rw [mul_one]; rfl)

lemma nsmul_pairA_tmul (m M : ℕ) (β : Af D.host.F) (z : D.host.E) :
    (m * M) • (pairA D.host.F 0 β ⊗ₜ[D.host.F] z) =
      pairA D.host.F 0 ((m : Af D.host.F) * β) ⊗ₜ[D.host.F] ((M : D.host.E) * z) := by
  calc (m * M) • (pairA D.host.F 0 β ⊗ₜ[D.host.F] z) = m • (M • (pairA D.host.F 0 β ⊗ₜ[D.host.F] z)) := by
        rw [mul_smul]
    _ = (m • pairA D.host.F 0 β) ⊗ₜ[D.host.F] (M • z) := by
        rw [← TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    _ = _ := by
        congr 1
        · exact Prod.ext (by show (m • (0 : Ainf D.host.F)) = 0; rw [smul_zero])
            (by show m • β = (m : Af D.host.F) * β; rw [nsmul_eq_mul])
        · rw [nsmul_eq_mul]

lemma natMul_add {A : Type*} [AddCommGroup A] {L : AddSubgroup A} {a b : A}
    (ha : ∃ k : ℕ, 0 < k ∧ k • a ∈ L) (hb : ∃ k : ℕ, 0 < k ∧ k • b ∈ L) : ∃ k : ℕ, 0 < k ∧ k • (a + b) ∈ L := by
  obtain ⟨k₁, hk₁, m₁⟩ := ha
  obtain ⟨k₂, hk₂, m₂⟩ := hb
  refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
  have e : (k₁ * k₂) • (a + b) = k₂ • (k₁ • a) + k₁ • (k₂ • b) := by
    rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k₂ k₁]
  rw [e]
  exact add_mem (L.nsmul_mem m₁ _) (L.nsmul_mem m₂ _)

lemma natMul_sum {A ι : Type*} [AddCommGroup A] {L : AddSubgroup A} (s : Finset ι) (f : ι → A)
    (h : ∀ i ∈ s, ∃ k : ℕ, 0 < k ∧ k • f i ∈ L) : ∃ k : ℕ, 0 < k ∧ k • (∑ i ∈ s, f i) ∈ L :=
  Finset.sum_induction _ (fun m : A => ∃ k : ℕ, 0 < k ∧ k • m ∈ L) (fun _ _ => natMul_add)
    ⟨1, one_pos, by simp⟩ h

lemma single_mul_fI_mem (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) (i : Fin T.rank) (j : Fin S.rank)
    (y : AE D) : ∃ k : ℕ, 0 < k ∧ k • Matrix.single i j (y * fI D) ∈ latAll S T ΛS ΛT := by
  obtain ⟨NT, NS, hNT, hNS, hgen⟩ := gen_single (ΛS := ΛS) (ΛT := ΛT) hS hT i j
  obtain ⟨N₀, hN₀, hAA⟩ := exists_nat_mem_AA (D := D)
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by simp⟩
  | tmul a z =>
    rw [tmul_fI]
    obtain ⟨m, hm, hmβ⟩ := exists_nat_mul_intAf (sndA D.host.F a)
    obtain ⟨M, hM, o, ho⟩ := exists_nat_mul_mem (z / ((NT * NS : ℕ) : D.host.E))
    have hd : ((NT * NS : ℕ) : D.host.E) ≠ 0 := by
      exact_mod_cast (Nat.mul_pos hNT hNS).ne'
    have ha : (o : D.host.E) * (N₀ : D.host.E) ∈ D.host.AA := by
      have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o hAA
      simpa [Algebra.smul_def] using this
    have hmem := hgen _ hmβ _ ha
    refine ⟨m * (N₀ * M), Nat.mul_pos hm (Nat.mul_pos hN₀ (by omega)), ?_⟩
    rw [Matrix.smul_single, nsmul_pairA_tmul m (N₀ * M)]
    convert hmem using 3
    have ho' : (o : D.host.E) = (M : D.host.E) * (z / ((NT * NS : ℕ) : D.host.E)) := ho
    rw [ho']
    field_simp
    push_cast
    ring
  | add y₁ y₂ h₁ h₂ =>
    have := natMul_add h₁ h₂
    rwa [← Matrix.single_add, ← add_mul] at this

theorem placeLatDualV (D : D7) : PlaceLatDualV D := by
  classical
  intro ψ _ S T ΛS ΛT hS hT P e he e₁ he₁ x hx
  have hf : e₁ * fI D = e₁ := by
    rcases he₁ with rfl | rfl
    · exact (idemSum_mul_fI he).1
    · exact (idemSum_mul_fI he).2
  have hxf : ∀ i j, x i j * fI D = x i j := fun i j => by
    calc x i j * fI D = e₁ * x i j * fI D := by rw [hx i j]
      _ = (e₁ * fI D) * x i j := by ring
      _ = x i j := by rw [hf, hx i j]
  have hQ : ∀ i j, ∃ k : ℕ, 0 < k ∧ k • Matrix.single i j (x i j) ∈ latAll S T ΛS ΛT := fun i j => by
    have := single_mul_fI_mem hS hT i j (x i j)
    rwa [hxf] at this
  rw [Matrix.matrix_eq_sum_single x]
  exact natMul_sum _ _ fun i _ => natMul_sum _ _ fun j _ => hQ i j

end V2

section Sandwich

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

lemma intAf_mul' {a a' : Af D.host.F} (ha : a ∈ intAf D.host.F) (ha' : a' ∈ intAf D.host.F) :
    a * a' ∈ intAf D.host.F := fun w => by rw [map_mul]; exact mul_mem (ha w) (ha' w)

lemma intAE_mul' {z z' : Af D.host.F ⊗[D.host.F] D.host.E} (hz : z ∈ intAE D) (hz' : z' ∈ intAE D) :
    z * z' ∈ intAE D := by
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, o, rfl⟩ := hx
    induction hz' using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨a', ha', o', rfl⟩ := hy
      rw [Algebra.TensorProduct.tmul_mul_tmul]
      exact AddSubgroup.subset_closure ⟨a * a', intAf_mul' ha ha', o * o', by push_cast; rfl⟩
    | zero => rw [mul_zero]; exact zero_mem _
    | add y y' _ _ hy hy' => rw [mul_add]; exact add_mem hy hy'
    | neg y _ hy => rw [mul_neg]; exact neg_mem hy
  | zero => rw [zero_mul]; exact zero_mem _
  | add x x' _ _ hx hx' => rw [add_mul]; exact add_mem hx hx'
  | neg x _ hx => rw [neg_mul]; exact neg_mem hx

def IntF (y : AE D) : Prop := y * fI D = y ∧ finPart D y ∈ intAE D

lemma intF_zero : IntF (0 : AE D) := ⟨zero_mul _, by rw [map_zero]; exact zero_mem _⟩

lemma intF_add {y y' : AE D} (h : IntF y) (h' : IntF y') : IntF (y + y') :=
  ⟨by rw [add_mul, h.1, h'.1], by rw [map_add]; exact add_mem h.2 h'.2⟩

lemma intF_neg {y : AE D} (h : IntF y) : IntF (-y) :=
  ⟨by rw [neg_mul, h.1], by rw [map_neg]; exact neg_mem h.2⟩

lemma intF_mul {y y' : AE D} (h : IntF y) (h' : IntF y') : IntF (y * y') :=
  ⟨by rw [mul_assoc, h'.1], by rw [map_mul]; exact intAE_mul' h.2 h'.2⟩

lemma intF_sum {ι : Type*} (s : Finset ι) (f : ι → AE D) (h : ∀ i ∈ s, IntF (f i)) : IntF (∑ i ∈ s, f i) :=
  Finset.sum_induction _ IntF (fun _ _ => intF_add) intF_zero h

lemma intF_nsmul {y : AE D} (h : IntF y) (k : ℕ) : IntF (k • y) :=
  ⟨by rw [smul_mul_assoc, h.1], by rw [map_nsmul]; exact AddSubgroup.nsmul_mem _ h.2 k⟩

def finiteEmbeddingTensor (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →ₗ[D.host.F] AE D :=
  TensorProduct.map (LinearMap.inr D.host.F (Ainf D.host.F) (Af D.host.F)) LinearMap.id

lemma finite_embedding_tensor_tmul (β : Af D.host.F) (y : D.host.E) :
    finiteEmbeddingTensor D (β ⊗ₜ[D.host.F] y) = pairA D.host.F 0 β ⊗ₜ[D.host.F] y := rfl

lemma mul_fI_eq (y : AE D) : y * fI D = finiteEmbeddingTensor D (finPart D y) := by
  induction y using TensorProduct.induction_on with
  | zero => rw [zero_mul, map_zero, map_zero]
  | tmul a z => rw [tmul_fI]; rfl
  | add y y' h h' => rw [add_mul, h, h', map_add, map_add]

lemma exists_nat_mul_intAE (w : Af D.host.F ⊗[D.host.F] D.host.E) : ∃ k : ℕ, 0 < k ∧ k • w ∈ intAE D := by
  induction w using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | tmul β z =>
    obtain ⟨m, hm, hβ⟩ := exists_nat_mul_intAf β
    obtain ⟨M, hM, o, ho⟩ := exists_nat_mul_mem z
    refine ⟨m * M, Nat.mul_pos hm hM, ?_⟩
    have e : (m * M) • (β ⊗ₜ[D.host.F] z) = ((m : Af D.host.F) * β) ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      have ho' : ((o : 𝓞 D.host.E) : D.host.E) = (M : D.host.E) * z := ho
      rw [ho', mul_smul, ← TensorProduct.tmul_smul, TensorProduct.smul_tmul', nsmul_eq_mul, nsmul_eq_mul]
    rw [e]
    exact AddSubgroup.subset_closure ⟨_, hβ, o, rfl⟩
  | add w w' h h' =>
    obtain ⟨k, hk, m⟩ := h
    obtain ⟨k', hk', m'⟩ := h'
    refine ⟨k * k', Nat.mul_pos hk hk', ?_⟩
    have e : (k * k') • (w + w') = k' • (k • w) + k • (k' • w') := by
      rw [smul_add, ← mul_smul, ← mul_smul, mul_comm k' k]
    rw [e]
    exact add_mem (AddSubgroup.nsmul_mem _ m _) (AddSubgroup.nsmul_mem _ m' _)

lemma exists_nat_intF {y : AE D} (hy : y * fI D = y) : ∃ k : ℕ, 0 < k ∧ IntF (k • y) := by
  obtain ⟨k, hk, h⟩ := exists_nat_mul_intAE (finPart D y)
  exact ⟨k, hk, by rw [smul_mul_assoc, hy], by rw [map_nsmul]; exact h⟩

lemma uniform_nat {ι : Type*} [Fintype ι] (P : ι → ℕ → Prop) (hP : ∀ i k m, P i k → P i (m * k))
    (h : ∀ i, ∃ k, 0 < k ∧ P i k) : ∃ k, 0 < k ∧ ∀ i, P i k := by
  classical
  choose k hk hPk using h
  refine ⟨∏ i, k i, Finset.prod_pos fun i _ => hk i, fun i => ?_⟩
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
  exact hP i _ _ (hPk i)

set_option maxHeartbeats 800000 in

lemma lower (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ c : ℕ, 0 < c ∧ ∀ Z : WO S T, (∀ i j, IntF (Z i j)) → c • Z ∈ latAll S T ΛS ΛT := by
  classical
  obtain ⟨N₀, hN₀, hAA⟩ := exists_nat_mem_AA (D := D)
  have hsingle : ∀ ij : Fin T.rank × Fin S.rank, ∃ c, 0 < c ∧
      ∀ y : AE D, IntF y → c • Matrix.single ij.1 ij.2 y ∈ latAll S T ΛS ΛT := by
    rintro ⟨i, j⟩
    obtain ⟨NT, NS, hNT, hNS, hgen⟩ := gen_single (ΛS := ΛS) (ΛT := ΛT) hS hT i j
    refine ⟨N₀ * (NT * NS), Nat.mul_pos hN₀ (Nat.mul_pos hNT hNS), fun y hy => ?_⟩
    have hy' : y = finiteEmbeddingTensor D (finPart D y) := by rw [← mul_fI_eq, hy.1]
    rw [hy']
    have key : ∀ w ∈ intAE D, (N₀ * (NT * NS)) • Matrix.single i j (finiteEmbeddingTensor D w) ∈ latAll S T ΛS ΛT := by
      intro w hw
      induction hw using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨α, hα, o, rfl⟩ := hx
        have ha : (o : D.host.E) * (N₀ : D.host.E) ∈ D.host.AA := by
          have := Submodule.smul_mem (D.host.AA : Submodule (𝓞 D.host.E) D.host.E) o hAA
          simpa [Algebra.smul_def] using this
        have hm := hgen α hα _ ha
        have heq : (N₀ * (NT * NS)) • Matrix.single i j (finiteEmbeddingTensor D (α ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E))) =
            Matrix.single i j (pairA D.host.F 0 α ⊗ₜ[D.host.F]
              ((o : D.host.E) * (N₀ : D.host.E) * ((NT * NS : ℕ) : D.host.E))) := by
          rw [Matrix.smul_single, finite_embedding_tensor_tmul, ← TensorProduct.tmul_smul, nsmul_eq_mul]
          congr 2
          push_cast; ring
        rw [heq]; exact hm
      | zero => rw [map_zero, Matrix.single_zero, smul_zero]; exact zero_mem _
      | add x x' _ _ h h' => rw [map_add, Matrix.single_add, smul_add]; exact add_mem h h'
      | neg x _ h =>
        have e : Matrix.single i j (-(finiteEmbeddingTensor D x)) = -Matrix.single i j (finiteEmbeddingTensor D x) := by
          ext a b; simp only [Matrix.single_apply, Matrix.neg_apply]; split_ifs <;> simp
        rw [map_neg, e, smul_neg]; exact neg_mem h
    exact key _ hy.2
  obtain ⟨c, hc, hcP⟩ := uniform_nat (fun (ij : Fin T.rank × Fin S.rank) c =>
      ∀ y : AE D, IntF y → c • Matrix.single ij.1 ij.2 y ∈ latAll S T ΛS ΛT)
    (fun ij k m h y hy => by rw [mul_smul]; exact AddSubgroup.nsmul_mem _ (h y hy) m) hsingle
  refine ⟨c, hc, fun Z hZ => ?_⟩
  rw [Matrix.matrix_eq_sum_single Z, Finset.smul_sum]
  refine AddSubgroup.sum_mem _ fun i _ => ?_
  rw [Finset.smul_sum]
  exact AddSubgroup.sum_mem _ fun j _ => hcP (i, j) _ (hZ i j)

end Sandwich

section Upper

variable {S T : HSp D} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
  {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}

lemma natCast_mul_range {x : D.host.E} (hx : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) (m : ℕ) :
    (m : D.host.E) * x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  mul_mem (natCast_mem _ m) hx

lemma lattice_denom {n : ℕ} {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)} (hΛ : Submodule.IsLattice D.host.E Λ) :
    ∃ c : ℕ, 0 < c ∧ ∀ t ∈ Λ, ∀ i, (c : D.host.E) * t i ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  classical
  obtain ⟨s, hs⟩ := hΛ.fg
  obtain ⟨c, hc, hcP⟩ := uniform_nat (fun (gi : ↥s × Fin n) c =>
      (c : D.host.E) * (gi.1 : Fin n → D.host.E) gi.2 ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun gi k m h => by push_cast; rw [mul_assoc]; exact natCast_mul_range h m)
    (fun gi => by
      obtain ⟨m, hm, h⟩ := exists_nat_mul_mem ((gi.1 : Fin n → D.host.E) gi.2)
      exact ⟨m, hm, h⟩)
  refine ⟨c, hc, fun t ht => ?_⟩
  rw [← hs] at ht
  induction ht using Submodule.span_induction with
  | mem x hx => exact fun i => hcP (⟨x, hx⟩, i)
  | zero => intro i; simp
  | add x y _ _ hx hy => intro i; rw [Pi.add_apply, mul_add]; exact add_mem (hx i) (hy i)
  | smul o x _ hx =>
    intro i
    rw [Pi.smul_apply, Algebra.smul_def, mul_left_comm]
    exact mul_mem ⟨o, rfl⟩ (hx i)

lemma star_range {x : D.host.E} (hx : x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) :
    star x ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  obtain ⟨o, rfl⟩ := hx
  have hi : IsIntegral ℤ (star ((o : 𝓞 D.host.E) : D.host.E)) := by
    have := (RingOfIntegers.isIntegral_coe o).map (starRingEnd D.host.E).toIntAlgHom
    convert this using 1
    rfl
  exact ⟨⟨_, hi⟩, rfl⟩

lemma AA_denom' : ∃ d : ℕ, 0 < d ∧ ∀ a ∈ D.host.AA, (d : D.host.E) * a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range := by
  obtain ⟨b, hb, hint⟩ := D.host.AA.isFractional
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  obtain ⟨m, hm, c, hc⟩ := exists_nat_eq_mul b hb0
  refine ⟨m, hm, fun a ha => ?_⟩
  obtain ⟨y, hy⟩ := hint a ha
  have hy' : (y : D.host.E) = (b : D.host.E) * a := by rw [← Algebra.smul_def]; exact hy
  refine ⟨c * y, ?_⟩
  have hc' : (m : D.host.E) = (b : D.host.E) * (c : D.host.E) := by
    have := congrArg (fun z : 𝓞 D.host.E => (z : D.host.E)) hc
    simpa using this
  simp only [map_mul]
  show (c : D.host.E) * (y : D.host.E) = _
  rw [hy', hc']; ring

lemma matrix_denom {m n : ℕ} (G : Matrix (Fin m) (Fin n) D.host.E) :
    ∃ d : ℕ, 0 < d ∧ ∀ i j, (d : D.host.E) * G i j ∈ (algebraMap (𝓞 D.host.E) D.host.E).range :=
  have h := uniform_nat (fun (ij : Fin m × Fin n) d =>
      (d : D.host.E) * G ij.1 ij.2 ∈ (algebraMap (𝓞 D.host.E) D.host.E).range)
    (fun ij k d h => by push_cast; rw [mul_assoc]; exact natCast_mul_range h d)
    (fun ij => by obtain ⟨d, hd, h⟩ := exists_nat_mul_mem (G ij.1 ij.2); exact ⟨d, hd, h⟩)
  let ⟨d, hd, hP⟩ := h
  ⟨d, hd, fun i j => hP (i, j)⟩

lemma intF_gen {α : Af D.host.F} (hα : α ∈ intAf D.host.F) (o : 𝓞 D.host.E) :
    IntF (pairA D.host.F 0 α ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E)) :=
  ⟨by rw [tmul_fI]; rfl, AddSubgroup.subset_closure ⟨α, hα, o, rfl⟩⟩

set_option maxHeartbeats 800000 in

lemma upper (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) :
    ∃ c : ℕ, 0 < c ∧ ∀ t ∈ latAll S T ΛS ΛT, ∀ i j, IntF ((c • t) i j) := by
  obtain ⟨d₀, hd₀, hAA⟩ := AA_denom' (D := D)
  obtain ⟨cT, hcT, hT'⟩ := lattice_denom hT.1
  obtain ⟨cS, hcS, hS'⟩ := lattice_denom hS.1
  obtain ⟨dG, hdG, hG⟩ := matrix_denom S.gram
  refine ⟨d₀ * cT * (cS * dG), by positivity, fun t ht => ?_⟩
  induction ht using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨α, hα, -, a, ha, s, hs, t₀, ht₀, rfl⟩ := hx
    intro i j
    have hint : ((d₀ * cT * (cS * dG) : ℕ) : D.host.E) * (a * t₀ i * ∑ k, star (s k) * S.gram k j) ∈
        (algebraMap (𝓞 D.host.E) D.host.E).range := by
      have e : ((d₀ * cT * (cS * dG) : ℕ) : D.host.E) * (a * t₀ i * ∑ k, star (s k) * S.gram k j) =
          ((d₀ : D.host.E) * a) * ((cT : D.host.E) * t₀ i) *
            ∑ k, star ((cS : D.host.E) * s k) * ((dG : D.host.E) * S.gram k j) := by
        simp only [star_mul, star_natCast, Finset.mul_sum]
        push_cast
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
      rw [e]
      refine mul_mem (mul_mem (hAA a ha) (hT' t₀ ht₀ i)) (sum_mem fun k _ => mul_mem ?_ (hG k j))
      exact star_range (hS' s hs k)
    obtain ⟨o, ho⟩ := hint
    have e2 : ((d₀ * cT * (cS * dG)) • (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F]
        (a * t₀ i * ∑ k, star (s k) * S.gram k j) : WO S T)) i j =
        pairA D.host.F 0 α ⊗ₜ[D.host.F] ((o : 𝓞 D.host.E) : D.host.E) := by
      rw [Matrix.smul_apply, Matrix.of_apply, ← TensorProduct.tmul_smul, nsmul_eq_mul]
      congr 1
      exact ho.symm
    rw [e2]
    exact intF_gen hα o
  | zero => intro i j; rw [smul_zero]; exact intF_zero
  | add x y _ _ hx hy =>
    intro i j
    rw [smul_add, Matrix.add_apply]
    exact intF_add (hx i j) (hy i j)
  | neg x _ hx =>
    intro i j
    rw [smul_neg, Matrix.neg_apply]
    exact intF_neg (hx i j)

end Upper

end Formalism.IndefR.Fin.PDB

end
