import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GidxFacts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormProdCmEmbeddingsEqOneOfInert
open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.G.KAat Formalism.MainNotions.G.CmpJ Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms Formalism.L2.DIV Formalism.UG Formalism.L2.Ker Formalism.L2.G.Pend Formalism.L2.PairingIndexBounds.F Formalism.L2.KerInert GlobalTheory.TwV GlobalTheory.TwV.Xc TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.Xc.SBad

theorem not_both_mem {R : Type*} [CommRing R] {I : Ideal R} (hI : I ≠ ⊤) {a b : ℕ} (h : Nat.Coprime a b)
    (ha : (a : R) ∈ I) (hb : (b : R) ∈ I) : False := by
  obtain ⟨s, r, hsr⟩ := h.cast (R := R)
  exact hI ((Ideal.eq_top_iff_one _).2 (hsr ▸ I.add_mem (I.mul_mem_left _ ha) (I.mul_mem_left _ hb)))

theorem mem_of_mem_divs {A : Type} [CommRing A] [IsDedekindDomain A] {a : A} {P : HeightOneSpectrum A}
    (h : P ∈ Formalism.L2.Col.divs a) : a ∈ P.asIdeal := by
  unfold Formalism.L2.Col.divs at h
  split_ifs at h with hf
  · simpa using h
  · simp at h

theorem coprime_absNorm_of_notMem {E : Type} [Field E] [NumberField E] (p : ℕ) [Fact p.Prime]
    (P : HeightOneSpectrum (𝓞 E)) (h : ((p : ℕ) : 𝓞 E) ∉ P.asIdeal) : Nat.Coprime (Ideal.absNorm P.asIdeal) p := by
  refine GlobalTheory.NormUnitInert.Arith.coprime_absNorm p P.ne_bot ?_
  refine P.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun he => h ?_)
  rw [he]
  exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Dx : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Dx cX}

theorem notMem_Sall (t : KerEntTied ex) (u : D.what₂.Word) (μ : D.what₂.Tup) (p : ℕ) (hp : p.Prime)
    (hTp : Nat.Coprime (D.mem u).A.T p) (hgp : ∀ i, p ≠ D.host.g i) (hQ : p ∉ Dx.Qp μ)
    (P : HeightOneSpectrum (𝓞 t.X.E)) (hP : P ∈ Formalism.L2.Col.Sall t.sel (t.tup μ) (t.word u)) :
    ((p : ℕ) : 𝓞 t.X.E) ∉ P.asIdeal := by
  intro hpP
  simp only [Formalism.L2.Col.Sall, Formalism.L2.Col.rowSG, Formalism.L2.Col.uSG, Formalism.L2.Col.Primes.vGs, Finset.mem_union] at hP
  have hG : ∀ i, P ∈ t.Pr.vG i → False := fun i hPi => by
    have hc := mem_of_mem_divs hPi
    have hgm : ((D.host.g i : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.g_rec i, ← t.pr_ok.piG_norm]
      exact Ideal.mul_mem_left _ _ hc
    have hgi : (D.host.g i).Prime := t.g_rec i ▸ t.pr_ok.g_prime i
    exact not_both_mem P.isPrime.ne_top ((Nat.coprime_primes hgi hp).2 (hgp i).symm) hgm hpP
  rcases hP with hP | (hP | hP) | hP
  · have hpi := mem_of_mem_divs hP
    have hTm : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.asIdeal := by
      rw [← t.T_rec u, ← t.pr_ok.piT_norm]
      exact Ideal.mul_mem_right _ _ hpi
    exact not_both_mem P.isPrime.ne_top hTp hTm hpP
  · exact hG 0 hP
  · exact hG 1 hP
  · exact hQ ((t.Q_rec μ p).2 ⟨hp, P, hP, hpP⟩)

set_option maxHeartbeats 1000000 in

theorem bad_prime_to_p : Sites (fun {D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X} [Fact (D.what₂.places.resChar w).Prime] {std t J} S => Nat.Coprime (t.rd u μ).lev (D.what₂.places.resChar w) ∧ (∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.E) ∉ Q.asIdeal) ∧ (∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ), (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) ∧ ∀ v, GlobalTheory.TwU.UnderSB t μ v → (((D.what₂.places.resChar w) : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal) := by
  intro D L hT Gi Gl Kc Dx cX ex u μ w hg Lv I H X hF std t J S _ _
  classical
  have hp : (D.what₂.places.resChar w).Prime := hF.out
  obtain ⟨-, -, hTp, hgp⟩ := GlobalTheory.TwU.XdInert.gidx_facts D _ _ hg
  have hSS := (t.rd_chain u μ).1
  have hlev := (t.rd_chain u μ).2.1
  have key := fun P hP => notMem_Sall t u μ _ hp hTp hgp J.away P hP
  have keyE : ∀ Q ∈ GlobalTheory.TwU.ssRec t u μ, (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.E) ∉ Q.asIdeal := by
    intro Q hQ hm
    obtain ⟨P, hP, rfl⟩ := Finset.mem_map.1 hQ
    refine key P (hSS ▸ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm
  have keyF : ∀ v ∈ Formalism.L2.Col.plUnder D.host.F (GlobalTheory.TwU.ssRec t u μ),
      (((D.what₂.places.resChar w : ℕ)) : 𝓞 D.host.F) ∉ v.asIdeal := by
    rintro v ⟨Q, hQ, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    exact keyE Q hQ hm
  refine ⟨?_, keyE, keyF, ?_⟩
  · rw [hlev]
    have hq : ∀ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Nat.Coprime (Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      fun P => coprime_absNorm_of_notMem _ P.1 (key P.1 (Finset.mem_union_right _ P.2))
    have hprod : Nat.Coprime (∏ P : Formalism.L2.Col.rowSG t.Pr t.sel (t.tup μ), Formalism.L2.Col.qOf P.1) (D.what₂.places.resChar w) :=
      Nat.Coprime.prod_left fun P _ => hq P
    have hT' : Nat.Coprime (t.Pr.T (t.word u)) (D.what₂.places.resChar w) := by rw [t.T_rec u]; exact hTp
    simp only [Formalism.L2.Ker.levC, Formalism.L2.Col.cAof, Formalism.L2.Col.cBof]
    exact Nat.Coprime.mul (Nat.Coprime.pow_left _ hprod) (Nat.Coprime.mul hT' (Nat.Coprime.pow_left _ hprod))
  · rintro v ⟨P, hP, hv⟩ hm
    rw [hv, Ideal.mem_comap, map_natCast] at hm
    refine key P (Finset.mem_union_right _ hP) ((GlobalTheory.TwU.mem_seamP t.seam P _).1 ?_)
    rw [map_natCast]
    exact hm

end GlobalTheory.TwV.Xc.SBad

end
