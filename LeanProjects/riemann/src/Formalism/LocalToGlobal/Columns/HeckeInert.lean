import Formalism.LocalToGlobal.Columns.HeckeSp

noncomputable section

namespace Formalism.L2.Col

open NumberField IsDedekindDomain Formalism.HermitianLatticesTheory Module

section InertNbr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}

abbrev inType (P : Ideal (𝓞 E)) (s : List ℕ) : Type := ∀ i : Fin s.length, 𝓞 E ⧸ P ^ s.get i

def IsInertNbr (P : Ideal (𝓞 E)) (s : List ℕ) (N N' : Submodule (𝓞 E) (Sp E n)) : Prop :=
  Nonempty ((N ⧸ (N' ⊓ N).comap N.subtype) ≃ₗ[𝓞 E] inType P s) ∧
    Nonempty ((N' ⧸ (N ⊓ N').comap N'.subtype) ≃ₗ[𝓞 E] inType P s)

theorem IsInertNbr.symm {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : IsInertNbr P s N' N := ⟨h.2, h.1⟩

theorem isInertNbr_comm {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)} :
    IsInertNbr P s N N' ↔ IsInertNbr P s N' N := ⟨IsInertNbr.symm, IsInertNbr.symm⟩

theorem IsInertNbr.gmap {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') (g : Sp E n ≃ₗ[E] Sp E n) : IsInertNbr P s (gmap g N) (gmap g N') := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  exact ⟨⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N' N).symm.trans e1⟩,
    ⟨(quotMapEquiv (g.restrictScalars (𝓞 E)) N N').symm.trans e2⟩⟩

theorem inType_smul_eq_zero {P : Ideal (𝓞 E)} {s : List ℕ} {r : 𝓞 E} (hr : r ∈ P ^ s.sum) (x : inType P s) :
    r • x = 0 := by
  funext i
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (x i)
  rw [Pi.smul_apply, ← hy, Pi.zero_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul,
    Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_le_pow_right (List.le_sum_of_mem (List.get_mem s i)) hr)

theorem IsInertNbr.smul_le {P : Ideal (𝓞 E)} {s : List ℕ} {N N' : Submodule (𝓞 E) (Sp E n)}
    (h : IsInertNbr P s N N') : (P ^ s.sum) • N ≤ N' ∧ (P ^ s.sum) • N' ≤ N := by
  obtain ⟨⟨e1⟩, ⟨e2⟩⟩ := h
  constructor
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e1 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1
  · rw [Submodule.smul_le]
    intro r hr x hx
    have h0 : e2 (Submodule.Quotient.mk (r • (⟨x, hx⟩ : N'))) = 0 := by
      rw [Submodule.Quotient.mk_smul, map_smul]
      exact inType_smul_eq_zero hr _
    rw [LinearEquiv.map_eq_zero_iff, Submodule.Quotient.mk_eq_zero] at h0
    exact (Submodule.mem_inf.1 (Submodule.mem_comap.1 h0)).1

variable {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

def DecoSet.inertSet (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet E n ST SG) : Set (DecoSet E n ST SG) :=
  {d' | IsInertNbr P s d.1.N d'.1.N ∧ d'.1.f = d.1.f ∧ d'.1.be = d.1.be}

open Classical in

def DecoSet.inertNb (P : Ideal (𝓞 E)) (s : List ℕ) (d : DecoSet E n ST SG) : Finset (DecoSet E n ST SG) :=
  if h : (d.inertSet P s).Finite then h.toFinset else ∅

theorem DecoSet.inertSet_symm {P : Ideal (𝓞 E)} {s : List ℕ} {d e : DecoSet E n ST SG} :
    e ∈ d.inertSet P s ↔ d ∈ e.inertSet P s := ⟨fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩, fun h => ⟨h.1.symm, h.2.1.symm, h.2.2.symm⟩⟩

theorem DecoSet.smul_mem_inertSet {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} (h : e ∈ d.inertSet P s) : a • e ∈ (a • d).inertSet P s := by
  obtain ⟨h1, h2, h3⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    exact h1.gmap _
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h2]
  · rw [DecoSet.smul_val, DecoSet.smul_val]
    simp only [Deco.act, h3]

theorem DecoSet.smul_mem_inertSet_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} : a • e ∈ (a • d).inertSet P s ↔ e ∈ d.inertSet P s := by
  constructor
  · intro h
    have := DecoSet.smul_mem_inertSet a⁻¹ h
    simpa only [inv_smul_smul] using this
  · exact DecoSet.smul_mem_inertSet a

theorem DecoSet.inertSet_smul (P : Ideal (𝓞 E)) (s : List ℕ) (a : UF E n × GLG E n SG)
    (d : DecoSet E n ST SG) : (a • d).inertSet P s = (fun e => a • e) '' d.inertSet P s := by
  ext e
  constructor
  · intro he
    refine ⟨a⁻¹ • e, ?_, smul_inv_smul a e⟩
    rw [← DecoSet.smul_mem_inertSet_iff a, smul_inv_smul]
    exact he
  · rintro ⟨e', he', rfl⟩
    exact DecoSet.smul_mem_inertSet a he'

theorem DecoSet.smul_mem_inertNb_iff {P : Ideal (𝓞 E)} {s : List ℕ} (a : UF E n × GLG E n SG)
    {d e : DecoSet E n ST SG} : a • e ∈ (a • d).inertNb P s ↔ e ∈ d.inertNb P s := by
  classical
  unfold DecoSet.inertNb
  have hfin : ((a • d).inertSet P s).Finite ↔ (d.inertSet P s).Finite := by
    rw [DecoSet.inertSet_smul]
    exact Set.finite_image_iff (MulAction.injective a).injOn
  by_cases h : (d.inertSet P s).Finite
  · rw [dif_pos (hfin.2 h), dif_pos h, Set.Finite.mem_toFinset, Set.Finite.mem_toFinset]
    exact DecoSet.smul_mem_inertSet_iff a
  · rw [dif_neg (mt hfin.1 h), dif_neg h]
    simp

end InertNbr

section HeckeI

variable {K : Type} [Field K] [NumberField K] [StarRing K]
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ}
  {ST SG : Finset (HeightOneSpectrum (𝓞 E))} {S : GSD K}

def DecoPts.nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d : S.D) : Finset S.D :=
  ((c.pts d).inertNb P s).map c.pts.symm.toEmbedding

theorem DecoPts.mem_nbI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (d e : S.D) :
    e ∈ c.nbI P s d ↔ c.pts e ∈ (c.pts d).inertNb P s := by
  unfold DecoPts.nbI
  rw [Finset.mem_map_equiv, Equiv.symm_symm]

def heckeI (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) : LocOp S S :=
  LocOp.ofNbr (MonoidHom.id S.G) (c.nbI P s) LinearMap.id
    (by
      intro g d' d
      rw [c.mem_nbI, c.mem_nbI, MonoidHom.id_apply, c.pts_smul, c.pts_smul]
      exact DecoSet.smul_mem_inertNb_iff (c.hom g))
    (by intro g x; rfl)

theorem heckeI_op_apply (c : DecoPts S E n ST SG) (P : Ideal (𝓞 E)) (s : List ℕ) (φ : S.EqFun) (d : S.D) :
    (((heckeI c P s).op φ : S.EqFun) : S.D → S.V) d = ∑ e ∈ c.nbI P s d, (φ : S.D → S.V) e := by
  simp only [heckeI, LocOp.ofNbr_op_apply, LinearMap.id_apply]

def InertOff (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  {P : HeightOneSpectrum (𝓞 E) // conjPrime₂ P = P ∧ (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) ∧ P ∉ S0}

def InertOff.q {S0 : Set (HeightOneSpectrum (𝓞 E))} (P : InertOff S0) : ℕ := Nat.card (𝓞 E ⧸ P.1.asIdeal)

abbrev LevOffI (ST SG : Finset (HeightOneSpectrum (𝓞 E))) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  InertOff (S0 ∪ (↑ST : Set (HeightOneSpectrum (𝓞 E))) ∪ (↑SG : Set (HeightOneSpectrum (𝓞 E))))

def heckeFamI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    LevOffI ST SG S0 × List ℕ → End K S.EqFun := fun x => (heckeI c x.1.1.asIdeal x.2).op

variable (ST SG) in

abbrev HeckeIx (S0 : Set (HeightOneSpectrum (𝓞 E))) : Type :=
  (LevOff ST SG S0 × ℕ) ⊕ (LevOffI ST SG S0 × List ℕ)

def heckeFamAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) :
    HeckeIx ST SG S0 → End K S.EqFun :=
  Sum.elim (heckeFam c S0) (heckeFamI c S0)

def heckeAlgAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Subalgebra K (End K S.EqFun) :=
  hAlg K (heckeFamAll c S0)

def HeckeCommAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  PairComm (heckeFamAll c S0)

def HeckeFieldsInI (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamI c S0)

def HeckeFieldsInAll (c : DecoPts S E n ST SG) (S0 : Set (HeightOneSpectrum (𝓞 E))) : Prop :=
  SplitOver (heckeFamAll c S0)

end HeckeI

section Cartan

def CartanInert (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) : Prop :=
  ∀ P : HeightOneSpectrum (𝓞 E), conjPrime₂ P = P → (∃ x : 𝓞 E, cO E x - x ∉ P.asIdeal) →
    ∀ N N' : Submodule (𝓞 E) (Sp E n), Submodule.IsLattice E N → Submodule.IsLattice E N' →
      IsUnimodular (hStd E n) N → IsUnimodular (hStd E n) N' →
      (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → SameAt Q N N') →
      ∃ g ∈ UF E n, SameAt P (gmap g N) N' ∧ SameAt P (gmap g N') N

end Cartan

end Formalism.L2.Col
