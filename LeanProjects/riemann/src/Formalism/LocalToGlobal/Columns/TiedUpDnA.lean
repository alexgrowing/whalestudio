import Formalism.LocalToGlobal.Columns.TiedUpDnLoc

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.UG

section Lat

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem localizationAt_mono (P : HeightOneSpectrum (𝓞 E)) {A B : Submodule (𝓞 E) (Sp E n)} (h : A ≤ B) :
    localization₂ P.asIdeal A ≤ localization₂ P.asIdeal B := by
  rintro x ⟨s, hs, hx⟩
  exact ⟨s, hs, h hx⟩

theorem tud_locP_L {a : 𝓞 E} (ha : SepElt ST a) (d : DecoSet E n ST SG) (P : ST) :
    localization₂ P.1.asIdeal d.1.L = localization₂ P.1.asIdeal (d.1.LshKer P) := by
  rw [d.2.locP_LshKer_self ha P]
  have key : ∀ (L : Submodule (𝓞 E) (Sp E n)) (x : Sp E n),
      x ∈ localization₂ P.1.asIdeal L ↔ ∃ s ∈ P.1.asIdeal.primeCompl, s • x ∈ L := fun _ _ => Iff.rfl
  ext x
  rw [d.2.mem_locP_L P x, key]
  constructor
  · rintro ⟨hx, hf⟩
    obtain ⟨s, hs, hsx⟩ := (key _ x).1 hx
    refine ⟨s, hs, (d.2.mem_kerAt P _).2 ⟨hsx, ?_⟩⟩
    rw [d.2.f_smul P s x hx, hf, mul_zero]
  · rintro ⟨s, hs, hsx⟩
    obtain ⟨hN, hf⟩ := (d.2.mem_kerAt P _).1 hsx
    have hx : x ∈ d.1.at P.1 := (key _ x).2 ⟨s, hs, hN⟩
    refine ⟨hx, ?_⟩
    rw [d.2.f_smul P s x hx] at hf
    rcases mul_eq_zero.1 hf with h0 | h0
    · exact absurd (Ideal.Quotient.eq_zero_iff_mem.1 h0) hs
    · exact h0

theorem localizationAt_upN {N : Submodule (𝓞 E) (Sp E n)} (hlat : Submodule.IsLattice E N) (huni : IsUnimodular (hStd E n) N)
    (P : HeightOneSpectrum (𝓞 E)) (hne : conjPrime₂ P ≠ P) {x : Sp E n} (hx : x ∈ N) :
    localization₂ P.asIdeal (upN P.asIdeal N x) = localization₂ P.asIdeal (upA P.asIdeal N x) := by
  obtain ⟨-, -, -, h4, h5⟩ := upN_spec hlat huni P hne hx
  obtain ⟨e, he, heP⟩ := exists_mem_notMem (P := conjPrime₂ P) (Q := P) hne
  exact le_antisymm (localizationAt_mono P h4) (localization_le_of_smul_mem heP fun y hy => h5 (Submodule.smul_mem_smul he hy))

theorem localizationAt_upA {P : HeightOneSpectrum (𝓞 E)} {q : 𝓞 E} (hq : q ∈ P.asIdeal) (hq2 : q ∉ P.asIdeal ^ 2)
    {N M : Submodule (𝓞 E) (Sp E n)} (hNM : N ≤ M) (hMN : M ≤ localization₂ P.asIdeal N) {x z : Sp E n} (hz : z ∈ M) {u : 𝓞 E}
    (hu : u ∉ P.asIdeal) (hx : x - u • z ∈ P.asIdeal • N) :
    localization₂ P.asIdeal (upA P.asIdeal N x) =
      localization₂ P.asIdeal (M ⊔ Submodule.span (𝓞 E) {(algebraMap (𝓞 E) E q)⁻¹ • z}) := by
  have hq0 : algebraMap (𝓞 E) E q ≠ 0 := by
    rw [Ne, FaithfulSMul.algebraMap_eq_zero_iff]
    rintro rfl
    exact hq2 (Ideal.zero_mem _)
  apply le_antisymm
  · refine localization_le_of_le_localization P (sup_le ((hNM.trans le_sup_left).trans (le_locP _ _)) ?_)
    rw [Submodule.span_le]
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨r', hr'⟩ := neighbourConstruct_mem_inv.1 hb q hq
    have e1 : b • x = b • (x - u • z) + (r' * u) • ((algebraMap (𝓞 E) E q)⁻¹ • z) := by
      have e2 : (r' * u) • ((algebraMap (𝓞 E) E q)⁻¹ • z) = b • (u • z) := by
        rw [← algebraMap_smul E (r' * u), smul_smul, map_mul, hr', ← algebraMap_smul E u z, smul_smul]
        congr 1
        field_simp
      rw [e2, ← smul_add, sub_add_cancel]
    rw [e1]
    refine le_locP _ _ (Submodule.add_mem _ (Submodule.mem_sup_left (hNM (inv_smul_mem hb hx))) ?_)
    exact Submodule.smul_mem _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · have hNA : N ≤ upA P.asIdeal N x := le_sup_left
    refine localization_le_of_le_localization P (sup_le (hMN.trans (localizationAt_mono P hNA)) ?_)
    rw [Submodule.span_le, Set.singleton_subset_iff]
    obtain ⟨a', ha', r0, hr0, har⟩ := exists_inv_unif P hq hq2
    refine (mem_locP P _ _).2 ⟨r0 * u, fun hm => (P.isPrime.mem_or_mem hm).elim hr0 hu, ?_⟩
    have e1 : (r0 * u) • ((algebraMap (𝓞 E) E q)⁻¹ • z) = a' • x - a' • (x - u • z) := by
      rw [← smul_sub, sub_sub_cancel, ← algebraMap_smul E (r0 * u), smul_smul, map_mul, ← har, ← algebraMap_smul E u z,
        smul_smul]
      congr 1
      field_simp
    rw [e1]
    refine Submodule.sub_mem _ ((le_sup_right : _ ≤ upA P.asIdeal N x) (Submodule.subset_span ⟨a', ha', rfl⟩)) ?_
    exact hNA (inv_smul_mem ha' hx)

end Lat

section Same

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
  {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem tud_isOver_conj (hc : Formalism.BasicNotions.CMData F E) {v : HeightOneSpectrum (𝓞 F)} {P : HeightOneSpectrum (𝓞 E)}
    (hov : IsOver v P) : IsOver v (conjPrime₂ P) := by
  unfold IsOver at *
  rw [hov]
  change _ = Ideal.comap _ (Ideal.comap (cO E) P.asIdeal)
  rw [Ideal.comap_comap]
  congr 1
  apply RingHom.ext
  intro x
  symm
  apply RingOfIntegers.ext
  show star ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E) = ((algebraMap (𝓞 F) (𝓞 E) x : 𝓞 E) : E)
  rw [hc.fixed]
  refine ⟨(x : F), ?_⟩
  rfl

theorem tud_sameOff_up (hc : Formalism.BasicNotions.CMData F E) (d : DecoSet E n ST SG) (P : ST) (hP : MoveHyp ST SG P) {q : 𝓞 E}
    (hq : q ∈ P.1.asIdeal) (hq2 : q ∉ P.1.asIdeal ^ 2) {v : HeightOneSpectrum (𝓞 F)} (hov : IsOver v P.1) {r : Sp E n}
    (hr : r ∈ d.1.N) (hfr : d.1.f P r = 1) : Deco.SameOff ST SG v d.1 (d.up P q r).1 := by
  rw [d.up_val P hP hq hq2 hr hfr]
  obtain ⟨-, -, h3, -, -⟩ := upN_spec d.2.lat d.2.uni P.1 hP.ne hr
  have hconj := tud_isOver_conj hc hov
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun w _ => rfl⟩
  · exact (h3 Q (fun e => hQ (e ▸ hov)) (fun e => hQ (e ▸ hconj))).localization_eq.symm
  · exact (Deco.up_f_ne d.1 P q r (fun e => hQ (by rw [e]; exact hov))).symm

theorem tud_sameOff_dn (hc : Formalism.BasicNotions.CMData F E) (d : DecoSet E n ST SG) (P : ST) (hP : MoveHyp ST SG P)
    {g : Module.Dual (𝓞 E ⧸ P.1.asIdeal) (d.lk P)} (hg : g ≠ 0) {v : HeightOneSpectrum (𝓞 F)} (hov : IsOver v P.1) :
    Deco.SameOff ST SG v d.1 (d.dnL P g).1 := by
  classical
  rw [d.dnL_val P hP hg]
  have h3 := (d.2.dnN_spec P hP.ne).2.2.1
  have hconj := tud_isOver_conj hc hov
  refine ⟨fun Q hQ => ?_, fun Q hQ => ?_, fun w _ => rfl⟩
  · exact (h3 Q (fun e => hQ (e ▸ hov)) (fun e => hQ (e ▸ hconj))).localization_eq.symm
  · show d.1.f Q = Function.update d.1.f P _ Q
    rw [Function.update_of_ne (fun e => hQ (by rw [e]; exact hov))]

end Same

end Formalism.L2.Col
