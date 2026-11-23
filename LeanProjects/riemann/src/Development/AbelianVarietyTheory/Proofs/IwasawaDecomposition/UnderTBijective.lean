import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.AtLevel

def underT {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) (P : Pr.vT u) :
    {v : HeightOneSpectrum (𝓞 X.F) // ((Pr.T u : ℕ) : 𝓞 X.F) ∈ v.asIdeal} :=
  ⟨P.1.under (𝓞 X.F), by
    show algebraMap (𝓞 X.F) (𝓞 X.E) _ ∈ P.1.asIdeal
    rw [map_natCast]
    exact T_mem_vT hPr u P⟩

theorem underT_bijective {Z : Dat} (hX : Z.X.Ok) (hPr : Z.Pr.Ok) (u : Z.Pr.Word) : Function.Bijective (underT hPr u) := by
  constructor
  · intro P Q h
    have h1 : P.1.asIdeal.under (𝓞 Z.X.F) = Q.1.asIdeal.under (𝓞 Z.X.F) :=
      congrArg (fun v => v.1.asIdeal) h
    rcases GlobalTheory.CharVal.eq_or_eq_conjP hX (GlobalTheory.CharVal.splitOver_vT hX hPr u Q.2).ne h1 with e | e
    · exact Subtype.ext e
    · refine absurd ?_ (conj_piT_notMem hPr u Q)
      have := decoFin_mem_of_mem_divs P.2
      rw [e, mem_conjP] at this
      exact this
  · rintro ⟨v, hv⟩
    have := v.isMaximal
    obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 Z.X.E) v.asIdeal
    have hT : ((Z.Pr.T u : ℕ) : 𝓞 Z.X.E) ∈ Q := by
      rw [hQv.over, Ideal.under_def, Ideal.mem_comap, map_natCast] at hv
      exact hv
    have hne : Q ≠ ⊥ := fun e => by
      rw [e, Ideal.mem_bot] at hT
      exact (hPr.T_prime u).ne_zero (by exact_mod_cast hT)
    let P : HeightOneSpectrum (𝓞 Z.X.E) := ⟨Q, hQ.isPrime, hne⟩
    rw [← hPr.piT_norm u] at hT
    rcases hQ.isPrime.mem_or_mem hT with h | h
    · exact ⟨⟨P, (mem_divs (hPr.piT_ne_zero u) P).2 h⟩, Subtype.ext (HeightOneSpectrum.ext hQv.over.symm)⟩
    · exact ⟨⟨conjPrime₂ P, (mem_divs (hPr.piT_ne_zero u) _).2 ((mem_conjP P _).2 h)⟩,
        Subtype.ext (HeightOneSpectrum.ext ((GlobalTheory.CharVal.under_conjP hX P).trans hQv.over.symm))⟩

theorem seenBar_of_not {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) {w : HeightOneSpectrum (𝓞 X.K)}
    (hw : ((Pr.T u : ℕ) : 𝓞 X.K) ∈ w.asIdeal) (hs : ¬ seenC Pr u w) (τ : X.Tau) :
    X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal := by
  rw [← map_natCast (X.embO τ), ← hPr.piT_norm u, map_mul] at hw
  refine (w.isPrime.mem_or_mem hw).resolve_left fun h => hs fun τ' => ?_
  rw [show X.embO τ' (Pr.piT u) = X.embO τ (Pr.piT u) from RingOfIntegers.ext (hPr.piT_Kq u _ _)]
  exact h

theorem mk_surj {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) : Function.Surjective (Ideal.Quotient.mk P.asIdeal) :=
  Ideal.Quotient.mk_surjective

theorem mk_zero {X : Fields} (P : HeightOneSpectrum (𝓞 X.E)) (x : 𝓞 X.E) : x ∈ P.asIdeal ↔ Ideal.Quotient.mk P.asIdeal x = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.symm

set_option maxHeartbeats 1000000 in

def atTTied {B : Base} {X : PreX B.toPre} (I : TC B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) :
    AtTTied (D := (I.rec7 l Z)) u where
  eV := Equiv.ofBijective (underT l.pr u)
    (underT_bijective (Z := B.dat X I.Ch) (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u)
  piU := X.piT u
  piU_K := X.piT_K u
  piU_norm := X.piT_norm u
  piU_cong := Ideal.mem_span_singleton.2 (X.piT_cong u)
  res := I.resT l u I.mu0
  res_surj v := mk_surj (X := B.fields) v.1
  res_pi v := (mk_zero (X := B.fields) v.1 _).1 (decoFin_mem_of_mem_divs (A := 𝓞 B.fields.E) v.2)
  res_conj v pb h e := by
    have h1 : pb = B.fields.conjO (X.piT u) := RingOfIntegers.ext (h.trans (B.fields_conjO_coe _).symm)
    exact conj_piT_notMem l.pr u v (h1 ▸ Ideal.Quotient.eq_zero_iff_mem.1 e)
  res_v v x := mk_zero (X := B.fields) v.1 _
  tauOf w hw v x := by
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    exact (tauAt_mem_iff l.pr u (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws B).1 hw' v x).symm.trans
      (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).symm
  seenP w hw τ := by
    classical
    have hval := Formalism.BasicNotions.Examples₂.placesOf_val_eq B.LL
    have hw' : ((B.T u : ℕ) : 𝓞 B.LL) ∈ w.asIdeal :=
      (show B.places.resChar w = B.T u from hw) ▸ resChar_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w
    have hs : (((I.rec7 l Z).fm u).seenP w = true) ↔ seenC (B.primes X) u w := decide_eq_true_iff
    by_cases h : seenC (B.primes X) u w
    · rw [if_pos (hs.2 h)]
      exact (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (h τ)
    · rw [if_neg (mt hs.1 h)]
      have h2 := (val_pos_iff_mem (X := B.fields) (Pl := B.places) (Equiv.refl _) hval w _).2 (seenBar_of_not l.pr u hw' h τ)
      have h3 : ((B.fields.embO τ (B.fields.conjO (X.piT u)) : 𝓞 B.LL) : B.LL) = B.fields.emb τ (B.host.conj (X.piT u : B.host.E)) :=
        congrArg (B.fields.emb τ) (B.fields_conjO_coe _)
      exact h3 ▸ h2

theorem exists_atTTied : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ u : B.Word, ∃ A : AtTTied (D := (I.rec7 l Z)) u, I.IdV l u I.mu0 A.eV ∧ A.piU = X.piT u ∧ A.res = I.resT l u I.mu0 :=
  fun I _ _ l Z u => ⟨atTTied I l Z u, fun _ => rfl, rfl, by unfold atTTied; rfl⟩

end GlobalTheory.Mem.AtLevel

end
