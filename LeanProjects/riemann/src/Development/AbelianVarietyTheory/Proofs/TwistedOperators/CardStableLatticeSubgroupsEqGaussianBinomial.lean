import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NonemptyTransferEquiv
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialFormula
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GaussBinomMulProd
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime
open NumberField

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Gen
variable {R : Type} [CommRing R]

theorem card_torsion_eq {A : Type} [AddCommGroup A] [Module R A] [Finite A] {c π : R} {J : Ideal R}
    (hJ : Ideal.span {c} ⊔ Ideal.span {π} = J) (hc : ∀ x : A, c • x = 0) :
    Nat.card (Submodule.torsionBySet R A (J : Set R)) = Nat.card (A ⧸ J • (⊤ : Submodule R A)) := by
  let f : A →ₗ[R] A := DistribMulAction.toLinearMap R A π
  have hmem : ∀ a ∈ J, ∃ r s : R, a = r * c + s * π := by
    intro a ha
    rw [← hJ, Submodule.mem_sup] at ha
    obtain ⟨y, hy, z, hz, rfl⟩ := ha
    obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    obtain ⟨s, rfl⟩ := Ideal.mem_span_singleton'.1 hz
    exact ⟨r, s, rfl⟩
  have hπ : π ∈ J := hJ ▸ Submodule.mem_sup_right (Ideal.mem_span_singleton_self π)
  have h1 : Submodule.torsionBySet R A (J : Set R) = LinearMap.ker f := by
    ext x
    rw [Submodule.mem_torsionBySet_iff, LinearMap.mem_ker]
    constructor
    · intro h; exact h ⟨π, hπ⟩
    · rintro h ⟨a, ha⟩
      obtain ⟨r, s, rfl⟩ := hmem a ha
      have h' : π • x = 0 := h
      simp only [add_smul, mul_smul, hc, h', smul_zero, add_zero]
  have h2 : J • (⊤ : Submodule R A) = LinearMap.range f := by
    apply le_antisymm
    · rw [Submodule.smul_le]
      intro a ha n _
      obtain ⟨r, s, rfl⟩ := hmem a ha
      refine ⟨s • n, ?_⟩
      show π • s • n = _
      rw [add_smul, mul_smul, hc, smul_zero, zero_add, mul_smul, smul_comm]
    · rintro _ ⟨y, rfl⟩
      exact Submodule.smul_mem_smul hπ trivial
  rw [h1, h2]
  have e1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker f)
  have e2 := Submodule.card_eq_card_quotient_mul_card (LinearMap.range f)
  rw [Nat.card_congr (f.quotKerEquivRange).toEquiv] at e1
  have hpos : 0 < Nat.card (LinearMap.range f) := Nat.card_pos
  rw [e1, mul_comm] at e2
  exact Nat.eq_of_mul_eq_mul_left hpos e2

end Gen
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
section Sub
variable {R : Type} [CommRing R] {A : Type} [AddCommGroup A] [Module R A] (J : Ideal R)

def toQ (S : Submodule R (Submodule.torsionBySet R A (J : Set R))) :
    Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) where
  carrier := S
  add_mem' := S.add_mem
  zero_mem' := S.zero_mem
  smul_mem' c x hx := by
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective c
    show (algebraMap R (R ⧸ J) r) • x ∈ S
    rw [algebraMap_smul]
    exact S.smul_mem r hx

theorem card_sub_eq (m : ℕ) :
    Nat.card {T : Submodule R A // T ≤ Submodule.torsionBySet R A (J : Set R) ∧ Nat.card T = m} =
      Nat.card {S : Submodule (R ⧸ J) (Submodule.torsionBySet R A (J : Set R)) // Nat.card S = m} := by
  set V := Submodule.torsionBySet R A (J : Set R)
  have cardT : ∀ T : Submodule R A, T ≤ V → Nat.card (toQ J (T.comap V.subtype)) = Nat.card T := fun T hT =>
    Nat.card_congr
      { toFun := fun x => ⟨x.1.1, x.2⟩
        invFun := fun y => ⟨⟨y.1, hT y.2⟩, y.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have cardS : ∀ S : Submodule (R ⧸ J) V, Nat.card ((S.restrictScalars R).map V.subtype) = Nat.card S := fun S =>
    (Nat.card_congr (Submodule.equivMapOfInjective V.subtype V.injective_subtype (S.restrictScalars R)).toEquiv).symm
  refine Nat.card_congr
    { toFun := fun T => ⟨toQ J (T.1.comap V.subtype), (cardT T.1 T.2.1).trans T.2.2⟩
      invFun := fun S => ⟨(S.1.restrictScalars R).map V.subtype, fun _ ⟨x, _, hx⟩ => hx ▸ x.2,
        (cardS S.1).trans S.2⟩
      left_inv := fun T => ?_
      right_inv := fun S => ?_ }
  · apply Subtype.ext
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩; exact hx
    · intro hy; exact ⟨⟨y, T.2.1 hy⟩, hy, rfl⟩
  · apply Subtype.ext
    ext x
    constructor
    · rintro ⟨x', hx', h⟩
      have : x' = x := Subtype.ext h
      exact this ▸ hx'
    · intro hx; exact ⟨x, hx, rfl⟩

end Sub
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Lat
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def pSub (D : Datum H) (p : ℕ) : Submodule (𝓞 E) D.La := Ideal.span {(p : 𝓞 E)} • ⊤

theorem mem_pSub {D : Datum H} {p : ℕ} {x : D.La} : x ∈ pSub D p ↔ x ∈ pLat D p := by
  rw [pSub, Submodule.ideal_span_singleton_smul, Submodule.mem_smul_pointwise_iff_exists, mem_pLat]
  simp only [Submodule.mem_top, true_and, Nat.cast_smul_eq_nsmul]
  exact ⟨fun ⟨b, hb⟩ => ⟨b, hb.symm⟩, fun ⟨b, hb⟩ => ⟨b, hb.symm⟩⟩

def asSub {D : Datum H} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    Submodule (𝓞 E) D.La where
  toAddSubmonoid := N.toAddSubmonoid
  smul_mem' a x hx := hN a x hx

theorem relIndex_eq_card {D : Datum H} {p : ℕ} (N : AddSubgroup D.La) (hN : ∀ (a : 𝓞 E), ∀ x ∈ N, a • x ∈ N) :
    (pLat D p).relIndex N = Nat.card ((asSub N hN).map (pSub D p).mkQ) := by
  let g : D.La →+ D.La ⧸ pSub D p := (pSub D p).mkQ.toAddMonoidHom
  have hker : g.ker = pLat D p := by
    ext x
    rw [AddMonoidHom.mem_ker, ← mem_pSub]
    exact Submodule.Quotient.mk_eq_zero _
  rw [← hker, AddSubgroup.relIndex, AddSubgroup.addSubgroupOf, AddMonoidHom.comap_ker,
    AddSubgroup.index_ker, AddMonoidHom.range_comp, AddSubgroup.range_subtype]
  rfl

def latEquiv (D : Datum H) (p : ℕ) (J : Ideal (𝓞 E)) (m : ℕ) :
    LatCount D p J m ≃ {T : Submodule (𝓞 E) (D.La ⧸ pSub D p) //
      T ≤ Submodule.torsionBySet (𝓞 E) (D.La ⧸ pSub D p) (J : Set (𝓞 E)) ∧ Nat.card T = m} where
  toFun N := ⟨(asSub N.1 N.2.2.1).map (pSub D p).mkQ, by
      rintro _ ⟨x, hx, rfl⟩
      rw [Submodule.mem_torsionBySet_iff]
      rintro ⟨a, ha⟩
      rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, mem_pSub]
      exact N.2.2.2.1 a ha x hx,
    (relIndex_eq_card N.1 N.2.2.1).symm.trans N.2.2.2.2⟩
  invFun T := ⟨(T.1.comap (pSub D p).mkQ).toAddSubgroup,
    fun x hx => by
      show (pSub D p).mkQ x ∈ T.1
      rw [Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 (mem_pSub.2 hx)]
      exact T.1.zero_mem,
    fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx,
    fun a ha x hx => by
      have h := (Submodule.mem_torsionBySet_iff _ _).1 (T.2.1 hx) ⟨a, ha⟩
      rw [← mem_pSub, ← Submodule.Quotient.mk_eq_zero]
      exact ((pSub D p).mkQ.map_smul a x).trans h,
    by
      refine (relIndex_eq_card _ (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).trans (Eq.trans ?_ T.2.2)
      have e : (asSub (T.1.comap (pSub D p).mkQ).toAddSubgroup
          (fun a x hx => (T.1.comap (pSub D p).mkQ).smul_mem a hx)).map (pSub D p).mkQ = T.1 :=
        Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _
      rw [e]⟩
  left_inv N := by
    apply Subtype.ext
    ext x
    show (pSub D p).mkQ x ∈ (asSub N.1 N.2.2.1).map (pSub D p).mkQ ↔ x ∈ N.1
    constructor
    · rintro ⟨y, hy, h⟩
      have h' : y - x ∈ pSub D p := by
        rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
        exact sub_eq_zero.2 h
      have := N.1.sub_mem hy (N.2.1 (mem_pSub.1 h'))
      simpa using this
    · intro hx; exact ⟨x, hx, rfl⟩
  right_inv T := Subtype.ext (Submodule.map_comap_eq_of_surjective (pSub D p).mkQ_surjective _)

end Lat
end GlobalTheory.LatCountGauss

namespace GlobalTheory.LatCountGauss
open GlobalTheory.HeckeCount ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped TensorProduct

theorem card_latCount : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    (Dw : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Datum H) (p : ℕ) (J : Ideal (𝓞 E)), 0 < p → J.IsMaximal → (p : 𝓞 E) ∈ J → ∀ k : ℕ,
    Nat.card (GlobalTheory.HeckeCount.LatCount Dw p J (Ideal.absNorm J ^ k)) =
      GlobalTheory.IndefiniteRowSideFullHecke.GaussianBinomialFormula.gaussBinom (Ideal.absNorm J) (Module.finrank (𝓞 E) Dw.La) k := by
  intro E _ _ _ H Dw p J hp hJ hpJ k
  haveI := Dw.fin
  haveI := Dw.proj
  letI := Ideal.Quotient.field J
  set R := 𝓞 E
  set L := Dw.La
  have hp0 : (p : R) ≠ 0 := Nat.cast_ne_zero.2 hp.ne'
  have hspan0 : Ideal.span {(p : R)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]; exact hp0
  have hJ0 : J ≠ ⊥ := fun h => hp0 (by rw [h] at hpJ; exact (Submodule.mem_bot R).1 hpJ)
  haveI hfinJ : Finite (R ⧸ J) := (Ideal.absNorm_ne_zero_iff J).1 (fun h => hJ0 (Ideal.absNorm_eq_zero_iff.1 h))
  haveI : Finite (R ⧸ Ideal.span {(p : R)}) :=
    (Ideal.absNorm_ne_zero_iff _).1 (fun h => hspan0 (Ideal.absNorm_eq_zero_iff.1 h))
  have hq : Nat.card (R ⧸ J) = Ideal.absNorm J := by
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]

  haveI hA : Finite (L ⧸ pSub Dw p) := by
    haveI : Finite ((R ⧸ Ideal.span {(p : R)}) ⊗[R] L) := Module.finite_of_finite (R ⧸ Ideal.span {(p : R)})
    exact Finite.of_equiv _ (TensorProduct.quotTensorEquivQuotSMul L (Ideal.span {(p : R)})).toEquiv
  set V := Submodule.torsionBySet R (L ⧸ pSub Dw p) (J : Set R)

  have hc : ∀ x : L ⧸ pSub Dw p, (p : R) • x = 0 := by
    intro x
    obtain ⟨y, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) trivial
  obtain ⟨π, hπ⟩ := IsDedekindDomain.exists_sup_span_eq
    (show Ideal.span {(p : R)} ≤ J from (Ideal.span_singleton_le_iff_mem J).2 hpJ) hspan0
  have hle : pSub Dw p ≤ J • (⊤ : Submodule R L) :=
    Submodule.smul_mono_left ((Ideal.span_singleton_le_iff_mem J).2 hpJ)
  have hmap : J • (⊤ : Submodule R (L ⧸ pSub Dw p)) = (J • (⊤ : Submodule R L)).map (pSub Dw p).mkQ := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]
  have hV : Nat.card V = Ideal.absNorm J ^ Module.finrank R L := by
    rw [card_torsion_eq hπ hc, hmap,
      Nat.card_congr (Submodule.quotientQuotientEquivQuotient _ _ hle).toEquiv,
      ← Nat.card_congr (TensorProduct.quotTensorEquivQuotSMul L J).toEquiv,
      Module.natCard_eq_pow_finrank (K := R ⧸ J), GlobalTheory.SW.Hyper.finrank_fibre R L (R ⧸ J), hq]
  haveI : Finite V := inferInstance
  haveI : Module.Finite (R ⧸ J) V := Module.Finite.of_finite
  have hq2 : 2 ≤ Ideal.absNorm J := by
    rw [← hq]
    haveI : Nontrivial (R ⧸ J) := Ideal.Quotient.nontrivial_iff.2 hJ.ne_top
    exact Finite.one_lt_card
  have hinj := Nat.pow_right_injective hq2
  have hdim : Module.finrank (R ⧸ J) V = Module.finrank R L := by
    apply hinj
    show Ideal.absNorm J ^ _ = Ideal.absNorm J ^ _
    rw [← hV, Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
  rw [Nat.card_congr (latEquiv Dw p J _), card_sub_eq]
  have key : ∀ S : Submodule (R ⧸ J) V, Nat.card S = Ideal.absNorm J ^ k ↔ Module.finrank (R ⧸ J) S = k := by
    intro S
    rw [Module.natCard_eq_pow_finrank (K := R ⧸ J), hq]
    exact hinj.eq_iff
  rw [Nat.card_congr (Equiv.subtypeEquivRight key), GlobalTheory.GaussCount.subspaceCount (R ⧸ J) V k, hq, hdim]

end GlobalTheory.LatCountGauss
