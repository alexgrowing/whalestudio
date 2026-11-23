import Formalism.LocalToGlobal.Columns.HermitianFormLastCoordinateUniformizerVectorSelf
import Formalism.LocalToGlobal.Columns.TiedLv

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Crt

variable {E : Type} [Field E] [NumberField E] [StarRing E] {ST : Finset (Pl E)} {π : 𝓞 E} {T : ℕ}

def hd_fam (ST : Finset (Pl E)) : ST ⊕ ST → Ideal (𝓞 E) :=
  Sum.elim (fun P => P.1.asIdeal) (fun P => (conjPrime₂ P.1).asIdeal)

theorem hd_fam_coprime (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Pairwise fun i j : ST ⊕ ST => IsCoprime (hd_fam ST i) (hd_fam ST j) := by
  have hmax : ∀ i, (hd_fam ST i).IsMaximal := by
    rintro (P | P)
    · exact P.1.isMaximal
    · exact (conjPrime₂ P.1).isMaximal
  have hinj : ∀ i j, hd_fam ST i = hd_fam ST j → i = j := by
    rintro (P | P) (Q | Q) h
    · exact congrArg Sum.inl (Subtype.ext (HeightOneSpectrum.ext h))
    · exact absurd (HeightOneSpectrum.ext h : P.1 = conjPrime₂ Q.1) (hc Q P)
    · exact absurd (HeightOneSpectrum.ext h : conjPrime₂ P.1 = Q.1).symm (hc P Q)
    · have h1 : conjPrime₂ P.1 = conjPrime₂ Q.1 := HeightOneSpectrum.ext h
      have h2 : P.1 = Q.1 := by rw [← rlh_conjP_conjP P.1, h1, rlh_conjP_conjP]
      exact congrArg Sum.inr (Subtype.ext h2)
  intro i j hij
  rw [Ideal.isCoprime_iff_sup_eq]
  exact Ideal.IsMaximal.coprime_of_ne (hmax i) (hmax j) fun h => hij (hinj i j h)

def hd_red (ST : Finset (Pl E)) :
    𝓞 E →ₗ[𝓞 E] ((∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) × (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal)) :=
  LinearMap.prod (LinearMap.pi fun P : ST => Submodule.mkQ P.1.asIdeal)
    (LinearMap.pi fun P : ST => Submodule.mkQ (conjPrime₂ P.1).asIdeal)

theorem hd_red_surjective (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) : Function.Surjective (hd_red ST) := by
  rintro ⟨c, c'⟩
  choose x hx using fun P : ST => Submodule.mkQ_surjective P.1.asIdeal (c P)
  choose x' hx' using fun P : ST => Submodule.mkQ_surjective (conjPrime₂ P.1).asIdeal (c' P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal (hd_fam_coprime hc) (Sum.elim x x')
  refine ⟨r, Prod.ext (funext fun P => ?_) (funext fun P => ?_)⟩
  · show Submodule.mkQ P.1.asIdeal r = c P
    rw [← hx P]
    exact (Submodule.Quotient.eq _).2 (hr (Sum.inl P))
  · show Submodule.mkQ (conjPrime₂ P.1).asIdeal r = c' P
    rw [← hx' P]
    exact (Submodule.Quotient.eq _).2 (hr (Sum.inr P))

theorem hd_red_ker (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E)) :
    LinearMap.ker (hd_red ST) = Ideal.span {(T : 𝓞 E)} := by
  ext r
  rw [LinearMap.mem_ker, Ideal.mem_span_singleton, ← hT]
  constructor
  · intro h
    have h1 : ∀ P ∈ ST, r ∈ P.asIdeal := fun P hP =>
      (Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.fst h) ⟨P, hP⟩)
    have h2 : ∀ P ∈ ST, cO E r ∈ P.asIdeal := fun P hP =>
      (mem_conjP P r).1 ((Submodule.Quotient.mk_eq_zero _).1 (congrFun (congrArg Prod.snd h) ⟨P, hP⟩))
    have d1 : π ∣ r := (hB.dvd r).1 h1
    have d2 : cO E π ∣ r := by
      obtain ⟨s, hs⟩ := (hB.dvd (cO E r)).1 h2
      refine ⟨cO E s, ?_⟩
      rw [← map_mul, ← hs, cO_cO]
    exact hB.cop.mul_dvd d1 d2
  · rintro ⟨s, rfl⟩
    refine Prod.ext (funext fun P => ?_) (funext fun P => ?_)
    · refine (Submodule.Quotient.mk_eq_zero _).2 ?_
      rw [mul_assoc]
      exact Ideal.mul_mem_right _ _ (hB.mem P.2)
    · refine (Submodule.Quotient.mk_eq_zero _).2 ((mem_conjP P.1 _).2 ?_)
      rw [map_mul, map_mul, cO_cO, mul_comm (cO E π), mul_assoc]
      exact Ideal.mul_mem_right _ _ (hB.mem P.2)

theorem hd_crt (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E)) (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nonempty ((𝓞 E ⧸ Ideal.span {(T : 𝓞 E)}) ≃ₗ[𝓞 E]
      ((∀ P : ST, 𝓞 E ⧸ P.1.asIdeal) × (∀ P : ST, 𝓞 E ⧸ (conjPrime₂ P.1).asIdeal))) :=
  ⟨(Submodule.quotEquivOfEq _ _ (hd_red_ker hB hT).symm).trans ((hd_red ST).quotKerEquivOfSurjective (hd_red_surjective hc))⟩

theorem hd_Lsh_quot {n : ℕ} {SG : Finset (Pl E)} (dd : DecoSet E n ST SG) (hB : BasePi ST π) (hT : π * cO E π = (T : 𝓞 E))
    (hc : ∀ P Q : ST, Q.1 ≠ conjPrime₂ P.1) :
    Nonempty ((dd.1.Lsh ⧸ dd.1.L.submoduleOf dd.1.Lsh) ≃ₗ[𝓞 E] (𝓞 E ⧸ Ideal.span {(T : 𝓞 E)})) := by
  obtain ⟨e1⟩ := dd.2.Lsh_quot_L hc
  obtain ⟨e2⟩ := hd_crt hB hT hc
  exact ⟨e1.trans e2.symm⟩

end Crt

section Tr

variable {R M M' : Type} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']

theorem hd_transport (e : M ≃ₗ[R] M') (A B : Submodule R M) (A' B' : Submodule R M') (hA : ∀ x, e x ∈ A' ↔ x ∈ A)
    (hB : ∀ x, e x ∈ B' ↔ x ∈ B) :
    Nonempty ((A ⧸ B.comap A.subtype) ≃ₗ[R] (A' ⧸ B'.comap A'.subtype)) := by
  let f : A ≃ₗ[R] A' :=
    { toFun := fun x => ⟨e x.1, (hA x.1).2 x.2⟩
      invFun := fun y => ⟨e.symm y.1, (hA _).1 (by rw [e.apply_symm_apply]; exact y.2)⟩
      map_add' := fun x y => Subtype.ext (map_add e x.1 y.1)
      map_smul' := fun r x => Subtype.ext (map_smul e r x.1)
      left_inv := fun x => Subtype.ext (e.symm_apply_apply x.1)
      right_inv := fun y => Subtype.ext (e.apply_symm_apply y.1) }
  refine ⟨Submodule.Quotient.equiv _ _ f ?_⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact (hB x.1).2 hx
  · intro hy
    refine ⟨f.symm y, ?_, f.apply_symm_apply y⟩
    show e.symm y.1 ∈ B
    refine (hB _).1 ?_
    rw [e.apply_symm_apply]
    exact hy

end Tr

section Rec

variable {d : ColDat} (a : ColArgs d)

theorem hd_Ld_eq (hS : SpStd d.toColBase) (u : d.what₂.Word) (i : ℕ) (hi : i ≤ d.R.m) (c : StCl (Pr := d.Pr) d.W d.lev u i) :
    CF.Ld (d.colRec a) u i hi c = (d.repr u i c).1.Lsh := by
  show Formalism.L2.Forms.dualL (d.sp.cm.sig : d.X.E →+* d.X.E) (CF.gramN (d.colRec a) i hi) (CF.clsCrd (d.colRec a) u i hi c) = _
  rw [gramN_eq a hS i hi, clsCrd_eq a u i hi c]
  exact rlc_span_dualSet d.sp.cm (d.R.N i) _

theorem attDisc (hS : SpStd d.toColBase) (u : d.what₂.Word) : AtTDisc (d.colRec a) u := by
  intro i hi c
  obtain ⟨e1⟩ := hd_Lsh_quot (d.repr u i c) (basePi_of_ok d.hX d.hPr u) (d.hPr.piT_norm u)
    (fun P Q => (moveHyp_of_ok d.hPr u P).st Q)
  obtain ⟨e0⟩ := hd_transport ((CF.crdN (d.colRec a) i hi).restrictScalars (𝓞 d.host.E))
    (CH.Ld (d.colRec a) u i c) ((d.colRec a).clsLat u i c) (d.repr u i c).1.Lsh (d.repr u i c).1.L
    (fun x => by
      have h := hx_mem_Ld (D := d.colRec a) u i hi c x
      rw [hd_Ld_eq a hS u i hi c] at h
      exact h)
    (fun x => by
      have h := hx_mem_map (D := d.colRec a) hi ((d.colRec a).clsLat u i c) x
      rw [← hx_clsCrd, clsCrd_eq a u i hi c] at h
      exact h)
  exact ⟨e0.trans e1⟩

end Rec

end Formalism.L2.Col
