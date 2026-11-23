import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsOpenCongruenceIdelesAndRealFiniteParts
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSplitIdempotentsOfRelTraceOneModTwo

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.Core.Rk GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDec

open GlobalTheory.IdemSupport

theorem map_mul_apply_mem {A B n : Type} [CommRing A] [CommRing B] [Fintype n] (φ : A →+* B) (S : Subring B)
    {a b : Matrix n n A} (ha : ∀ i j, φ (a i j) ∈ S) (hb : ∀ i j, φ (b i j) ∈ S) (i j : n) : φ ((a * b) i j) ∈ S := by
  rw [Matrix.mul_apply, map_sum]
  exact sum_mem fun l _ => by rw [map_mul]; exact mul_mem (ha i l) (hb l j)

theorem mulVec_mem {B n : Type} [CommRing B] [Fintype n] (S : Subring B) {a : Matrix n n B} {y : n → B}
    (ha : ∀ i j, a i j ∈ S) (hy : ∀ i, y i ∈ S) (i : n) : (a *ᵥ y) i ∈ S :=
  sum_mem fun j _ => mul_mem (ha i j) (hy j)

theorem map_mix_one {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {f : A} (hf : φ f = 1) (a b : A) :
    φ a = φ (f * a + (1 - f) * b) := by
  rw [map_add, map_mul, map_mul, map_sub, map_one, hf, sub_self, zero_mul, one_mul, add_zero]

variable {D : D7}

theorem exists_splitIdem (D : D7) : ∃ e : AE D, IsSplitIdem D e := by
  have h2 : ¬ IsUnit (2 : 𝓞 D.host.F) := by
    intro hu
    have hn := hu.map (Algebra.norm ℤ (S := 𝓞 D.host.F))
    rw [show (2 : 𝓞 D.host.F) = algebraMap ℤ (𝓞 D.host.F) 2 by simp, Algebra.norm_algebraMap,
      isUnit_pow_iff Module.finrank_pos.ne'] at hn
    rcases Int.isUnit_iff.mp hn with h | h <;> omega
  obtain ⟨M, hM, h2M⟩ := Ideal.exists_le_maximal (Ideal.span {(2 : 𝓞 D.host.F)})
    (by rwa [Ne, Ideal.span_singleton_eq_top])
  have hm : (2 : 𝓞 D.host.F) ∈ M := h2M (Ideal.mem_span_singleton_self 2)
  have hM0 : M ≠ ⊥ := by
    rintro rfl
    exact two_ne_zero ((Submodule.mem_bot _).mp hm)
  obtain ⟨e, a, b, c, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D ⟨M, hM.isPrime, hM0⟩ hm
  exact ⟨e, (GlobalTheory.IdemModTwo.isSplitIdem_iff e).2 ⟨_, a, b, c⟩⟩

theorem exists_mt (V : HSp D) (M : Matrix (Fin V.rank) (Fin V.rank) (AE D))
    (hM : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D)) (hd : IsUnit M.det) :
    ∃ g : GA D V, mt V g = M :=
  ⟨(⟨Matrix.nonsingInvUnit M hd, hM⟩ : HR (AF D.host.F) D.sp.cm.sig V.gram), rfl⟩

theorem int_iff (z : AE D) : finPart D z ∈ intAE D ↔ toEAf D z ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  mem_intAE_iff (finPart D z)

def IntM (V : HSp D) (k : GA D V) : Prop := ∀ i j, toEAf D (mt V k i j) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E

theorem IntM.mul {V : HSp D} {k k' : GA D V} (h : IntM V k) (h' : IntM V k') : IntM V (k * k') := by
  intro i j
  rw [mt_mul]
  exact map_mul_apply_mem (toEAf D) _ h h' i j

theorem intM_one (V : HSp D) : IntM V 1 := by
  intro i j
  rw [mt_one, Matrix.one_apply]
  split_ifs
  · rw [map_one]; exact one_mem _
  · rw [map_zero]; exact zero_mem _

theorem gramA_one {V : HSp D} (hV : V.gram = 1) : V.gram.map (incA D) = 1 := by
  rw [hV]; exact Matrix.map_one _ (map_zero _) (map_one _)

theorem mt_inv {V : HSp D} (hV : V.gram = 1) (k : GA D V) : mt V k⁻¹ = ((mt V k).map (cA D))ᵀ := by
  have h : ((mt V k).map (cA D))ᵀ * V.gram.map (incA D) * mt V k = V.gram.map (incA D) := k.2
  rw [gramA_one hV, Matrix.mul_one] at h
  have e : mt V k * mt V k⁻¹ = 1 := by rw [← mt_mul, mul_inv_cancel, mt_one]
  calc mt V k⁻¹ = (((mt V k).map (cA D))ᵀ * mt V k) * mt V k⁻¹ := by rw [h, Matrix.one_mul]
    _ = _ := by rw [Matrix.mul_assoc, e, Matrix.mul_one]

theorem IntM.inv {V : HSp D} (hV : V.gram = 1) {k : GA D V} (h : IntM V k) : IntM V k⁻¹ := by
  intro i j
  rw [mt_inv hV]
  exact (int_iff _).1 (finPart_cA_mem ((int_iff _).2 (h j i)))

theorem isOpen_intM (V : HSp D) : IsOpen {k : GA D V | IntM V k} := by
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, -⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
    have := GlobalTheory.IdeleParts.isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
    rw [← GlobalTheory.IdeleParts.integralFiniteAdeles_eq_adelicCompletion_integers] at this
    convert this using 1
    ext z
    simp
  have e1 : {k : GA D V | IntM V k} = ⋂ i, ⋂ j, (fun k : GA D V => finPart D (mt V k i j)) ⁻¹' {z | z ∈ intAE D} := by
    ext k
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_setOf_eq, int_iff, IntM]
  rw [e1]
  refine isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => h1.preimage (hfc.comp ?_)
  exact (Units.continuous_val.comp continuous_subtype_val).matrix_elem i j

theorem intM_of_finHom {V : HSp D} {k k' : GA D V} (e : finHom V k = finHom V k') (h : IntM V k') : IntM V k := by
  intro i j
  have e1 : finPart D (mt V k i j) = finPart D (mt V k' i j) := congrArg (fun x => x.1 i j) e
  rw [← int_iff, e1, int_iff]
  exact h i j

theorem rat_int_iff (a : D.host.E) :
    eToEAf D a ∈ Formalism.L2.Herm.intAf D.host.F D.host.E ↔ a ∈ (1 : Submodule (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  have e : eToEAf D a = toEAf D (incA D a) := rfl
  rw [e, ← int_iff, hΦ.int, hΦ.inc, Submodule.mem_one]
  have k : ∀ Q : HeightOneSpectrum (𝓞 D.host.E),
      (algebraMap D.host.E (FiniteAdeleRing (𝓞 D.host.E) D.host.E) a) Q ∈ Q.adicCompletionIntegers D.host.E ↔
        Q.valuation D.host.E a ≤ 1 := fun Q => by
    change algebraMap D.host.E (Q.adicCompletion D.host.E) a ∈ _ ↔ _
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, Formalism.UG.P.levelaf_valued_algebraMap]
  simp only [k]
  exact ⟨fun h => HeightOneSpectrum.mem_integers_of_valuation_le_one D.host.E a h,
    fun ⟨r, hr⟩ Q => hr ▸ Q.valuation_le_one r⟩

theorem finM_mulVec_int {V : HSp D} {n : ℕ} (hn : V.rank = n) {k : GA D V} (h : IntM V k) {y : Fin n → EF D}
    (hy : ∀ i, y i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) (i : Fin n) :
    (finM V hn k *ᵥ y) i ∈ Formalism.L2.Herm.intAf D.host.F D.host.E :=
  mulVec_mem _ (a := finM V hn k) (fun _ _ => h _ _) hy i

theorem moves_std {V : HSp D} (hV : V.gram = 1) {n : ℕ} (hn : V.rank = n) {k : GA D V} (h : IntM V k) :
    Moves V hn k (Formalism.L2.Col.stdLat D.host.E n) := by
  intro x
  have e : x ∈ Formalism.L2.Col.stdLat D.host.E n ↔ ∀ i, eToEAf D (x i) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    simp only [rat_int_iff]
    exact ⟨fun h i => h i trivial, fun h i _ => h i⟩
  rw [e]
  refine ⟨fun hx => finM_mulVec_int hn (h.inv hV) hx, fun hx i => ?_⟩
  have h1 := finM_mulVec_int hn h hx i
  have h2 : finM V hn k * finM V hn k⁻¹ = 1 := by
    subst hn
    change (mt V k).map (toEAf D) * (mt V k⁻¹).map (toEAf D) = 1
    rw [← Matrix.map_mul, ← mt_mul, mul_inv_cancel, mt_one]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  rwa [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec] at h1

theorem splitPart_le (V : HSp D) : splitPart V ≤ GfC V := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  refine (Subgroup.closure_le _).2 ?_
  rintro g ⟨e, ⟨-, -, v, ε, hε, hs⟩, hg⟩
  refine mem_GfC_of_suppF V (f := e + cA D e) ?_ hg
  rw [hs]
  exact (place_comp hΦ hε).1

theorem exists_finPart (V : HSp D) (γ : GA D V) : ∃ r ∈ GfC V, finHom V γ = finHom V r := by
  let f : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 1)
  have h1 : f * f = f := by
    have : pairA D.host.F 0 1 * pairA D.host.F 0 1 = pairA D.host.F 0 1 := Prod.ext (mul_zero _) (mul_one _)
    exact ((algebraMap (AF D.host.F) (AE D)).map_mul _ _).symm.trans (congrArg _ this)
  have h2 : infPart D f = 0 := TensorProduct.zero_tmul _ _
  have h3 : finPart D f = 1 := rfl
  obtain ⟨r, hr⟩ := exists_piece V h1 (cA_algebraMap _) γ
  refine ⟨r, mem_GfC_of_suppF V h2 ((suppF_iff V f r).2 (smul_mix h1 hr)), Units.ext (Matrix.ext fun i j => ?_)⟩
  change finPart D (mt V γ i j) = finPart D (mt V r i j)
  rw [hr]
  exact map_mix_one (finPart D) h3 _ _

theorem ev_eq_of_one {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {f a b : AE D}
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hf : Φ f Q = 1) (h : f * a = f * b) : Φ a Q = Φ b Q := by
  have := congrArg (fun z => Φ z Q) h
  simpa only [ev_mul, hf, one_mul] using this

theorem ev_eq_of_zero {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} {f a b : AE D}
    {Q : HeightOneSpectrum (𝓞 D.host.E)} (hf : Φ f Q = 0) (h : (1 - f) * a = (1 - f) * b) : Φ a Q = Φ b Q := by
  refine ev_eq_of_one ?_ h
  rw [Φ.map_sub, Φ.map_one]
  change 1 - Φ f Q = 1
  rw [hf, sub_zero]

section Loc

variable {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E} (hΦ : Comp D Φ)
include hΦ

theorem int_of_norm_one {x : AE D} (hx : cA D x * x = 1) {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : cP P = P) :
    Φ x P ∈ P.adicCompletionIntegers D.host.E := by
  obtain ⟨δ, hδ⟩ := exists_delta hΦ P
  have hc : cA D δ = δ := by
    have := delta_conj hΦ hδ
    rw [hP] at this
    exact delta_unique hΦ this hδ
  have h1 : Φ (cA D x) P * Φ x P = 1 := by
    rw [← ev_mul, hx, map_one]; rfl
  rcases (P.adicCompletionIntegers D.host.E).mem_or_inv_mem (Φ x P) with h | h
  · exact h
  · rw [← eq_inv_of_mul_eq_one_left h1] at h
    have h2 : finPart D (δ * cA D x) ∈ intAE D := (hΦ.int _).2 fun Q => by
      rw [ev_mul]
      by_cases hQ : Q = P
      · subst hQ; rw [hδ.2.1, one_mul]; exact h
      · rw [hδ.2.2 Q hQ, zero_mul]; exact zero_mem _
    have h3 := (hΦ.int _).1 (finPart_cA_mem h2) P
    rwa [map_mul (cA D), hc, cA_cA, ev_mul, hδ.2.1, one_mul] at h3

theorem exists_split_at {P : HeightOneSpectrum (𝓞 D.host.E)} (hP : cP P ≠ P) :
    ∃ e : AE D, IsSplitIdem D e ∧ ∃ ε, IsPlaceIdem D (P.under (𝓞 D.host.F)) ε ∧
      e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, f, h⟩ := exists_isPrimeIdem hΦ P
  obtain ⟨hd, ε, hε, hf⟩ := of_isPrimeIdem hΦ h
  rcases h with ⟨h, rfl⟩ | ⟨rfl, -⟩
  · exact ⟨e, h.1, ε, hε, hf⟩
  · have h1 := (place_comp hΦ hε).2.1 (cP P) (under_cP P)
    rw [← hf, hd.2.2 _ hP] at h1
    exact absurd h1 zero_ne_one

theorem one_apply_int (V : HSp D) (i j : Fin V.rank) (Q : HeightOneSpectrum (𝓞 D.host.E)) :
    Φ ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) Q ∈ Q.adicCompletionIntegers D.host.E := by
  have := (hΦ.int _).1 ((int_iff _).2 (intM_one V i j)) Q
  rwa [mt_one] at this

theorem exists_split_mul (V : HSp D) (T : Finset (HeightOneSpectrum (𝓞 D.host.E))) : ∀ h : GA D V,
    (∀ Q, (cP Q = Q ∨ Q ∉ T) → ∀ i j, Φ (mt V h i j) Q ∈ Q.adicCompletionIntegers D.host.E) →
    ∃ s ∈ splitPart V, ∃ k, IntM V k ∧ h = s * k := by
  induction T using Finset.induction_on with
  | empty =>
    intro h hh
    exact ⟨1, one_mem _, h, fun i j => (int_iff _).1 ((hΦ.int _).2 fun Q => hh Q (Or.inr (Finset.notMem_empty Q)) i j),
      (one_mul h).symm⟩
  | insert P T hPT ih =>
    intro h hh
    by_cases hP : cP P = P
    · refine ih h fun Q hQ => hh Q ?_
      by_cases hQP : Q = P
      · exact Or.inl (hQP ▸ hP)
      · exact hQ.imp_right fun h1 h2 => (Finset.mem_insert.1 h2).elim hQP h1
    · obtain ⟨e, he, ε, hε, hs⟩ := exists_split_at hΦ hP
      obtain ⟨-, p1, p0⟩ := place_comp hΦ hε
      have hf := place_idem hΦ hε
      have hcf := cA_algebraMap (D := D) ε
      generalize algebraMap (AF D.host.F) (AE D) ε = f at hs p1 p0 hf hcf
      obtain ⟨g₁, g₂, s₁, s₂, hg⟩ := exists_split V hf hcf h
      have t₁ := (suppF_iff V f g₁).1 s₁
      have t₂ := (suppF_iff V (1 - f) g₂).1 s₂
      rw [sub_sub_cancel] at t₂
      have t₃ : (1 - f) • mt V g₂ = (1 - f) • mt V h := by
        rw [hg, mt_mul, ← Matrix.smul_mul, t₁, Matrix.smul_mul, Matrix.one_mul]
      obtain ⟨s, hs', k, hk, e2⟩ := ih g₂ fun Q hQ i j => by
        by_cases hu : Q.under (𝓞 D.host.F) = P.under (𝓞 D.host.F)
        · rw [ev_eq_of_one (p1 Q hu) (congrFun (congrFun t₂ i) j)]
          exact one_apply_int hΦ V i j Q
        · rw [ev_eq_of_zero (p0 Q hu) (congrFun (congrFun t₃ i) j)]
          refine hh Q (hQ.imp_right fun h1 h2 => (Finset.mem_insert.1 h2).elim (fun h3 => hu (by rw [h3])) h1) i j
      refine ⟨g₁ * s, mul_mem (Subgroup.subset_closure ⟨e, he, ?_⟩) hs', k, hk, by rw [hg, e2, mul_assoc]⟩
      intro i j
      rw [hs]
      exact s₁ i j

end Loc

theorem exists_det {V : HSp D} (hV : V.gram = 1) (i₀ : Fin V.rank) (g : GA D V) :
    ∃ s ∈ splitPart V, ∃ k, IntM V k ∧ (mt V (g * (s * k)⁻¹)).det = 1 := by
  obtain ⟨Φ, hΦ⟩ := exists_comp D
  obtain ⟨x, hx⟩ : ∃ x, x = (mt V g).det := ⟨_, rfl⟩
  have hx1 : cA D x * x = 1 := hx ▸ Formalism.L2.Theta.det_conj_mul V g
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin V.rank) (Fin V.rank) (AE D),
      M = Matrix.diagonal fun i => if i = i₀ then x else 1 := ⟨_, rfl⟩
  have hdet : M.det = x := by rw [hM, Matrix.det_diagonal]; simp
  have hU : (M.map (cA D))ᵀ * V.gram.map (incA D) * M = V.gram.map (incA D) := by
    rw [gramA_one hV, Matrix.mul_one, hM, Matrix.diagonal_map (map_zero _), Matrix.diagonal_transpose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    split_ifs
    · exact hx1
    · rw [map_one, one_mul]
  have hu : IsUnit M.det := by rw [hdet]; exact IsUnit.of_mul_eq_one _ ((mul_comm _ _).trans hx1)
  have hfin : {Q : HeightOneSpectrum (𝓞 D.host.E) | Φ x Q ∉ Q.adicCompletionIntegers D.host.E}.Finite :=
    Filter.eventually_cofinite.1 (Φ x).2
  obtain ⟨d, hd⟩ := exists_mt V M hU hu
  obtain ⟨s, hs, k, hk, e⟩ := exists_split_mul hΦ V hfin.toFinset d fun Q hQ i j => by
    have hxQ : Φ x Q ∈ Q.adicCompletionIntegers D.host.E :=
      hQ.elim (int_of_norm_one hΦ hx1) fun h => by_contra fun h' => h (hfin.mem_toFinset.2 h')
    have h1 := one_apply_int hΦ V i j Q
    rw [hd, hM, Matrix.diagonal_apply]
    rw [Matrix.one_apply] at h1
    split_ifs at h1 ⊢
    exacts [hxQ, h1, h1]
  refine ⟨s, hs, k, hk, ?_⟩
  have e1 : (mt V (g * (s * k)⁻¹)).det * M.det = 1 * M.det := by
    rw [one_mul, ← e, ← hd, ← Matrix.det_mul, ← mt_mul, inv_mul_cancel_right, hd, hdet, hx]
  exact hu.mul_right_cancel e1

theorem exists_dec (H : GlobalTheory.Published.StrongApproxSU) {V : HSp D} (hV : V.gram = 1) (g : GA D V) :
    ∃ γ ∈ GQ V, ∃ s ∈ splitPart V, ∃ k, IntM V k ∧ g = γ * s * k := by
  rcases Nat.eq_zero_or_pos V.rank with hn | hn
  · have hg : g = 1 := mt_inj V (Matrix.ext fun i => absurd i.2 (by omega))
    exact ⟨1, one_mem _, 1, one_mem _, 1, intM_one V, by rw [hg, mul_one, mul_one]⟩
  obtain ⟨s, hs, k, hk, hd⟩ := exists_det hV ⟨0, hn⟩ g
  obtain ⟨h, hh⟩ : ∃ h, h = g * (s * k)⁻¹ := ⟨_, rfl⟩
  rw [← hh] at hd
  have hg : g = h * s * k := by rw [hh, mul_assoc, inv_mul_cancel_right]
  rcases Nat.lt_or_ge V.rank 2 with h2 | h2
  · have hmt : mt V h = 1 := by
      let _ : Unique (Fin V.rank) := ⟨⟨⟨0, hn⟩⟩, fun i => Fin.ext (by have := i.2; omega)⟩
      have hdu := Matrix.det_unique (mt V h)
      ext i j
      have hi : i = default := Subsingleton.elim _ _
      have hj : j = default := Subsingleton.elim _ _
      rw [hi, hj, Matrix.one_apply_eq, ← hdu, hd]
    exact ⟨1, one_mem _, s, hs, k, hk, by rw [hg, mt_inj V (hmt.trans (mt_one V).symm)]⟩
  · obtain ⟨e, he⟩ := exists_splitIdem D
    have hcl := GlobalTheory.Published.StrongApprox.dense_split H D V h2 e he h hd
    have hc : Continuous fun y : GA D V => (h * s)⁻¹ * (y * s) := by fun_prop
    obtain ⟨y, hy, γ, hγ, -, h', hh', -, rfl⟩ := mem_closure_iff.1 hcl _ ((isOpen_intM V).preimage hc) (by
      change IntM V ((h * s)⁻¹ * (h * s))
      rw [inv_mul_cancel]
      exact intM_one V)
    refine ⟨γ, hγ, h' * s, mul_mem (Subgroup.subset_closure ⟨e, he, hh'⟩) hs, _, (IntM.inv hV hy).mul hk, ?_⟩
    rw [hg]
    group

theorem exists_rat_split_stab : GlobalTheory.Published.StrongApproxSU → ∀ (D : D7) (V : HSp D) (n : ℕ) (hn : V.rank = n), V.gram = 1 → ∀ g ∈ GfC V, ∃ r s k, IsRatFin V r ∧ s ∈ splitPart V ∧ k ∈ GfC V ∧ Moves V hn k (Formalism.L2.Col.stdLat D.host.E n) ∧ g = r * s * k := by
  intro H D V n hn hV g hg
  obtain ⟨γ, hγ, s, hs, k, hk, e⟩ := exists_dec H hV g
  obtain ⟨r, hr, er⟩ := exists_finPart V γ
  refine ⟨r, s, (r * s)⁻¹ * g, ⟨hr, γ, hγ, er⟩, hs, mul_mem (inv_mem (mul_mem hr (splitPart_le V hs))) hg,
    moves_std hV hn (intM_of_finHom ?_ hk), (mul_inv_cancel_left _ _).symm⟩
  rw [e, map_mul, map_inv, map_mul, map_mul, map_mul, er, inv_mul_cancel_left]

end GlobalTheory.SplitDec

end
