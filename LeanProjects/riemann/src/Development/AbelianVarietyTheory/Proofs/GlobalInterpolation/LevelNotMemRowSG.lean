import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ThDistC
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.IndexExponentDegree
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EmbHInjective
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.OrdDetConjFinite
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitOfConjPNe

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.MuOffMove

variable {X : Fields} {Pr : Primes X} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S}

theorem ordDet_congr {E : Type} [Field E] [NumberField E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)}
    {N₁ N₂ : Submodule (𝓞 E) (Sp E n)} (h : localization₂ P.asIdeal N₁ = localization₂ P.asIdeal N₂) : ordDet P N₁ = ordDet P N₂ := by
  unfold ordDet frameAt
  rw [h]

theorem under_conjP (hX : X.Ok) (Q : HeightOneSpectrum (𝓞 X.E)) :
    (conjPrime₂ Q).asIdeal.under (𝓞 X.F) = Q.asIdeal.under (𝓞 X.F) := by
  ext r
  have e : cO X.E (algebraMap (𝓞 X.F) (𝓞 X.E) r) = algebraMap (𝓞 X.F) (𝓞 X.E) r :=
    RingOfIntegers.ext (hX.star_F (r : X.F))
  rw [Ideal.under_def, Ideal.under_def, Ideal.mem_comap, Ideal.mem_comap, mem_conjP, e]

theorem natCast_mem_under (Q : HeightOneSpectrum (𝓞 X.E)) (p : ℕ) :
    ((p : ℕ) : 𝓞 X.F) ∈ Q.asIdeal.under (𝓞 X.F) ↔ ((p : ℕ) : 𝓞 X.E) ∈ Q.asIdeal := by
  rw [Ideal.under_def, Ideal.mem_comap, map_natCast]

theorem good_of_mem_QE {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K)) :
    ∃ v, GoodPl X.E S v ∧ sel v = P := by
  classical
  unfold QE at h
  split_ifs at h with h2
  · obtain ⟨v, hv, e⟩ := Finset.mem_image.1 h
    have hv1 : v ∈ Qprime (mu : Chr X.F X.E X.K) := by simpa using hv
    refine ⟨v, ?_, e⟩
    by_contra hn
    have h4 := (Subgroup.mem_inf.1 mu.2).2
    exact hv1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 h4 v) hn)
  · simp at h

theorem notMem_of_mem_QE (hsel : IsSel X sel) {P : HeightOneSpectrum (𝓞 X.E)} (h : P ∈ QE sel (mu : Chr X.F X.E X.K))
    {l : ℕ} (hl : l.Prime) (hS : l ∈ S) : (l : 𝓞 X.E) ∉ P.asIdeal := by
  intro hm
  obtain ⟨v, hgood, e⟩ := good_of_mem_QE h
  have h5 : (l : 𝓞 X.F) ∈ v.asIdeal := by
    rw [← hsel v, e, Ideal.under_def, Ideal.mem_comap, map_natCast]
    exact hm
  apply hgood.2.2
  have h6 : ringChar (𝓞 X.F ⧸ v.asIdeal) ∣ l := by
    rw [← ringChar.spec, ← map_natCast (Ideal.Quotient.mk v.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact h5
  haveI := v.isPrime
  rcases (Nat.dvd_prime hl).1 h6 with h7 | h7
  · exact absurd h7 CharP.ringChar_ne_one
  · change ringChar (𝓞 X.F ⧸ v.asIdeal) ∈ S
    rw [h7]
    exact hS

theorem level_notMem_rowSG (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ rowSG Pr sel mu) : (Pr.T u : 𝓞 X.E) ∉ P.asIdeal := by
  classical
  rcases Finset.mem_union.1 hP with h | h
  · exact T_notMem_vGs hPr u ⟨P, h⟩
  · exact notMem_of_mem_QE hsel h (hPr.T_prime u) hS

theorem mem_vT (hPr : Pr.Ok) (u : Pr.Word) (P : HeightOneSpectrum (𝓞 X.E)) : P ∈ Pr.vT u ↔ Pr.piT u ∈ P.asIdeal := by
  have h0 : Pr.piT u ≠ 0 := by
    refine left_ne_zero_of_mul (b := X.conjO (Pr.piT u)) ?_
    rw [hPr.piT_norm u]
    exact_mod_cast (hPr.T_prime u).ne_zero
  refine ⟨decoFin_mem_of_mem_divs, fun h => ?_⟩
  unfold Primes.vT divs
  have hf : {P : HeightOneSpectrum (𝓞 X.E) | Pr.piT u ∈ P.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {Pr.piT u}) (by simpa using h0)).subset fun Q hQ => ?_
    exact Ideal.dvd_span_singleton.2 hQ
  rw [dif_pos hf]
  simpa using h

theorem conjP_notMem_vT (hPr : Pr.Ok) {u : Pr.Word} {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vT u) : conjPrime₂ P ∉ Pr.vT u :=
  fun h => conj_piT_notMem hPr u ⟨P, hP⟩ ((mem_conjP _ _).1 ((mem_vT hPr u _).1 h))

open Classical in

def term (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E n)) (v : HeightOneSpectrum (𝓞 X.F)) : X.K :=
  if ∃ P ∈ SB, P.asIdeal.under (𝓞 X.F) = v.asIdeal then 1 else ((mU (sel v) ^ ordDet (sel v) N : X.Kˣ) : X.K)

theorem term_finite (hsel : IsSel X sel) (SB : Finset (HeightOneSpectrum (𝓞 X.E)))
    (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) {n : ℕ} {N : Submodule (𝓞 X.E) (Sp X.E n)} (hN : IsSdLat N) :
    (Function.mulSupport (term sel SB mU N)).Finite := by
  have hinj : Function.Injective sel := fun v w h => HeightOneSpectrum.ext (by rw [← hsel v, h, hsel w])
  refine ((GlobalTheory.OrdDetConj.ordDet_conj_finite X.E n N hN).2.preimage hinj.injOn).subset fun v hv h0 => hv ?_
  unfold term
  split_ifs
  · rfl
  · rw [h0, zpow_zero, Units.val_one]

open Classical in
theorem term_eq (hX : X.Ok) (hPr : Pr.Ok) (hsel : IsSel X sel) {u : Pr.Word} (hS : Pr.T u ∈ S)
    {mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ} (hU : ∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) {n : ℕ}
    {N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)} (h₁ : IsSdLat N₁) (h₂ : IsSdLat N₂) (hA : AgreeOff (Pr.T u) N₁ N₂)
    (v : HeightOneSpectrum (𝓞 X.F)) :
    term sel (rowSG Pr sel mu) mU N₁ v =
      (∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * term sel (rowSG Pr sel mu) mU N₂ v := by
  by_cases hv : ∃ P ∈ Pr.vT u, P.under (𝓞 X.F) = v
  · obtain ⟨P, hP, hPv⟩ := hv
    have hPv' : P.asIdeal.under (𝓞 X.F) = v.asIdeal := congrArg HeightOneSpectrum.asIdeal hPv
    have hc := conjP_notMem_vT hPr hP
    have hsp := (split_of_conj_ne₂ X P v hX (fun e => hc (e.symm ▸ hP)) hPv').2
    have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = {P} := by
      ext Q
      rw [Finset.mem_filter, Finset.mem_singleton]
      refine ⟨fun ⟨hQ, hQv⟩ => ?_, fun e => e ▸ ⟨hP, hPv⟩⟩
      exact ((hsp Q).1 (congrArg HeightOneSpectrum.asIdeal hQv)).resolve_right fun e => hc (e ▸ hQ)
    have hno : ¬ ∃ Q ∈ rowSG Pr sel mu, Q.asIdeal.under (𝓞 X.F) = v.asIdeal := by
      rintro ⟨Q, hQ, hQv⟩
      refine level_notMem_rowSG hPr hsel hS hQ ?_
      rw [← natCast_mem_under, hQv, ← hPv', natCast_mem_under]
      exact T_mem hPr u ⟨P, hP⟩
    unfold term
    rw [hfil, Finset.prod_singleton, if_neg hno, if_neg hno, ← Units.val_mul]
    congr 1
    unfold idxExp
    rcases (hsp (sel v)).1 (hsel v) with e | e
    · rw [e, ← zpow_add]
      congr 1
      ring
    · rw [e, hU P hP, GlobalTheory.OrdDetConj.ordDet_conjP h₁, GlobalTheory.OrdDetConj.ordDet_conjP h₂, inv_zpow', inv_zpow', ← zpow_add]
      congr 1
      ring
  · have hfil : (Pr.vT u).filter (fun Q => Q.under (𝓞 X.F) = v) = ∅ :=
      Finset.filter_eq_empty_iff.2 fun Q hQ e => hv ⟨Q, hQ, e⟩
    have hT : ((Pr.T u : ℕ) : 𝓞 X.E) ∉ (sel v).asIdeal := by
      intro h
      rw [← hPr.piT_norm u] at h
      rcases (sel v).isPrime.mem_or_mem h with h | h
      · exact hv ⟨sel v, (mem_vT hPr u _).2 h, HeightOneSpectrum.ext (hsel v)⟩
      · exact hv ⟨conjPrime₂ (sel v), (mem_vT hPr u _).2 ((mem_conjP _ _).2 h),
          HeightOneSpectrum.ext ((under_conjP hX _).trans (hsel v))⟩
    unfold term
    rw [hfil, Finset.prod_empty, one_mul, ordDet_congr (hA _ hT)]

theorem muOff_move : ∀ (X : Fields) (Pr : Primes X) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (S : Set ℕ) (mu : Tup X.F X.E X.K S) (u : Pr.Word) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (n : ℕ) (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E n)), X.Ok → Pr.Ok → IsSel X sel → Pr.T u ∈ S → (∀ k, Pr.g k ∈ S) → (∀ P ∈ Pr.vT u, mU (conjPrime₂ P) = (mU P)⁻¹) → IsSdLat N₁ → IsSdLat N₂ → AgreeOff (Pr.T u) N₁ N₂ → muOff sel (rowSG Pr sel mu) mU N₁ = (∏ P ∈ Pr.vT u, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) * muOff sel (rowSG Pr sel mu) mU N₂ := by
  intro X Pr sel S mu u mU n N₁ N₂ hX hPr hsel hS _ hU h₁ h₂ hA
  classical
  change ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₁ v = _ * ∏ᶠ v, term sel (rowSG Pr sel mu) mU N₂ v
  have hsub : Function.mulSupport (fun v : HeightOneSpectrum (𝓞 X.F) =>
      ∏ P ∈ Pr.vT u with P.under (𝓞 X.F) = v, ((mU P ^ (-idxExp P N₁ N₂) : X.Kˣ) : X.K)) ⊆
      ((Pr.vT u).image fun P => P.under (𝓞 X.F) : Finset _) := by
    intro v hv
    by_contra hn
    apply hv
    refine Finset.prod_eq_one fun P hP => absurd ?_ hn
    rw [Finset.mem_filter] at hP
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨P, hP.1, hP.2⟩)
  rw [finprod_congr (term_eq (mu := mu) hX hPr hsel hS hU h₁ h₂ hA),
    finprod_mul_distrib ((Finset.finite_toSet _).subset hsub) (term_finite hsel _ mU h₂),
    finprod_eq_prod_of_mulSupport_subset _ hsub,
    Finset.prod_fiberwise_of_maps_to (g := fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F))
      fun P hP => Finset.mem_image_of_mem (fun P : HeightOneSpectrum (𝓞 X.E) => P.under (𝓞 X.F)) hP]

end GlobalTheory.MuOffMove
