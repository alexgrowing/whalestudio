import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemSmulLk
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBasisAtOfIsLocBasis
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.HAt Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.HAt.Disc

section Gen

variable {R V W : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]

def quotMapEquiv (e : V ≃ₗ[R] W) (A L : Submodule R V) (A' L' : Submodule R W) (hA : A.map (e : V →ₗ[R] W) = A')
    (hL : L.map (e : V →ₗ[R] W) = L') : (A ⧸ L.comap A.subtype) ≃ₗ[R] (A' ⧸ L'.comap A'.subtype) := by
  subst hA hL
  refine Submodule.Quotient.equiv _ _ (e.submoduleMap A) ?_
  ext ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.1 hy
  simp only [Submodule.mem_map, Submodule.mem_comap, Submodule.subtype_apply]
  constructor
  · rintro ⟨z, hz, hze⟩
    have : (z : V) = x := e.injective (congrArg Subtype.val hze)
    exact ⟨x, this ▸ hz, rfl⟩
  · rintro ⟨x', hx', hxe⟩
    have : x' = x := e.injective hxe
    subst this
    exact ⟨⟨x', hx⟩, hx', rfl⟩

end Gen

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {Pr.piT u} = ⨅ P : Pr.vT u, P.1.asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    exact decoFin_mem_of_mem_divs P.2
  · exact Ideal.mem_span_singleton.2 (piT_dvd_of_mem hX hPr u r fun P => Ideal.mem_iInf.1 hr P)

theorem span_conj_pi_eq {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {X.conjO (Pr.piT u)} = ⨅ P : Pr.vT u, (conjPrime₂ P.1).asIdeal := by
  refine le_antisymm ?_ fun r hr => ?_
  · refine le_iInf fun P => ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show cO X.E (X.conjO (Pr.piT u)) ∈ P.1.asIdeal
    rw [show cO X.E (X.conjO (Pr.piT u)) = Pr.piT u from cO_cO _]
    exact decoFin_mem_of_mem_divs P.2
  · obtain ⟨s, hs⟩ := piT_dvd_of_mem hX hPr u (cO X.E r) fun P => Ideal.mem_iInf.1 hr P
    refine Ideal.mem_span_singleton.2 ⟨cO X.E s, ?_⟩
    have := congrArg (cO X.E) hs
    rw [cO_cO, map_mul] at this
    exact this

end GlobalTheory.Mem.Col2.HAt.Disc

namespace GlobalTheory.Mem.Col2.HAt.Disc

theorem span_T_eq {X : Fields} {Pr : Primes X} (hPr : Pr.Ok) (u : Pr.Word) :
    Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)} = Ideal.span {Pr.piT u} ⊓ Ideal.span {X.conjO (Pr.piT u)} := by
  rw [← hPr.piT_norm u, ← Ideal.span_singleton_mul_span_singleton]
  exact Ideal.mul_eq_inf_of_coprime ((Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)).sup_eq

theorem quotT_equiv {X : Fields} {Pr : Primes X} (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) :
    Nonempty ((𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃ₗ[𝓞 X.E]
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal))) := by
  have hco : IsCoprime (Ideal.span {Pr.piT u}) (Ideal.span {X.conjO (Pr.piT u)}) :=
    (Ideal.isCoprime_span_singleton_iff _ _).2 (hPr.piT_cop u)
  have hp1 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => P.1.asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    exact Ideal.IsMaximal.coprime_of_ne P.1.isMaximal Q.1.isMaximal fun h => hne (Subtype.ext (HeightOneSpectrum.ext h))
  have hp2 : Pairwise (Function.onFun IsCoprime fun P : Pr.vT u => (conjPrime₂ P.1).asIdeal) := fun P Q hne => by
    rw [Function.onFun, Ideal.isCoprime_iff_sup_eq]
    refine Ideal.IsMaximal.coprime_of_ne (conjPrime₂ P.1).isMaximal (conjPrime₂ Q.1).isMaximal fun h => hne (Subtype.ext ?_)
    ext x
    have h2 := congrArg (fun J : Ideal (𝓞 X.E) => cO X.E x ∈ J) h
    simp only [conjPrime₂, Ideal.mem_comap, cO_cO] at h2
    exact Iff.of_eq h2
  let φ : (𝓞 X.E ⧸ Ideal.span {((Pr.T u : ℕ) : 𝓞 X.E)}) ≃+*
      ((∀ P : Pr.vT u, 𝓞 X.E ⧸ P.1.asIdeal) × (∀ P : Pr.vT u, 𝓞 X.E ⧸ (conjPrime₂ P.1).asIdeal)) :=
    (Ideal.quotEquivOfEq (span_T_eq hPr u)).trans ((Ideal.quotientInfEquivQuotientProd _ _ hco).trans
      (RingEquiv.prodCongr
        ((Ideal.quotEquivOfEq (span_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp1))
        ((Ideal.quotEquivOfEq (span_conj_pi_eq hX hPr u)).trans (Ideal.quotientInfRingEquivPiQuotient _ hp2))))
  exact ⟨(AlgEquiv.ofRingEquiv (f := φ) fun a => rfl).toLinearEquiv⟩

end GlobalTheory.Mem.Col2.HAt.Disc

open GlobalTheory.Mem.Col2.HAt.Disc in

theorem GlobalTheory.Mem.Col2.TC.disc_cl : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (H : Formalism.L2.Herm.HermColsCh (I.rec7 l Z)) (F : ∀ u, FormsTiedSym (I.rec7 l Z) u (H.Ch u) (H.chOf u)), (∀ u, I.StdF l Z u (F u) ∧ I.StdLvC l Z u (F u)) → CarH H F → ∀ u, DiscCl (D := I.rec7 l Z) (u := u) := by
  intro B X I hI hP l Z H F _ _ u i hi c
  obtain ⟨hG, -, hc⟩ := (spaces_in_coordinates I hI hP l Z).2.2.2 i hi
  have hL : latCrd (I.rec7 l Z) i hi (I.latAt u I.mu0 i c) = ((I.stp u I.mu0 i).rep c).1.1.deco.1.L := (hc u I.mu0).1 c
  have hD : lc ((I.rec7 l Z).sp.X i) (rankN (I.rec7 l Z) i hi) (Formalism.L2.Herm.Ld (I.rec7 l Z) u i c) =
      ((I.stp u I.mu0 i).rep c).1.1.deco.1.Lsh := by
    refine (dual_co (I.rec7 l Z).sp.cm _ (rankN (I.rec7 l Z) i hi) _).trans ?_
    have h1 := BwLat.dualL_std (E := B.host.E) (sigD (I.rec7 l Z)).toRingHom (fun x => rfl) ((I.stp u I.mu0 i).rep c).1.1.deco.1.L
    exact (congrArg₂ (dualL _) hG hL).trans h1
  have hc' : ∀ P Q : (B.primes X).vT u, Q.1 ≠ conjPrime₂ P.1 := fun P Q => (moveHyp_of_ok l.pr u P).st Q
  obtain ⟨e1⟩ := ((I.stp u I.mu0 i).rep c).1.1.deco.2.Lsh_quot_L hc'
  obtain ⟨e2⟩ := quotT_equiv (FieldsLaws.fields_satisfy_definite_laws B).1.ok l.pr u
  exact ⟨(quotMapEquiv ((crdN (I.rec7 l Z) i hi).restrictScalars (𝓞 (I.rec7 l Z).host.E)) _ _ _ _ hD hL) ≪≫ₗ e1 ≪≫ₗ e2.symm⟩
