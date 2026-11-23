import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnitaryOnTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryGroupCharacterEqOneOfTrivialIntegralStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertPlaceHeckeDoubleCosetsInverseRepsLabel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedConjugatePlaceUniformiser
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsSplitAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.MemHermitianStandardLatticeIffPairingIntegral

noncomputable section

namespace GlobalTheory.InertChar

section CM

open Formalism.UG Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField GlobalTheory.PlaceComp GlobalTheory.SelfDualGenus
  GlobalTheory.InertDoubleCoset
open scoped TensorProduct Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

theorem core (hc : CMData (maximalRealSubfield E) E) (V : HSpace E)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))} {P : HeightOneSpectrum (𝓞 E)}
    {e : AF (maximalRealSubfield E) ⊗[maximalRealSubfield E] E} (he : IsIdemOf E v e)
    (hin : IsInertAt (maximalRealSubfield E) E v P) (h2 : (2 : 𝓞 E) ∉ P.asIdeal)
    (ν : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* Circle)
    (hν : ∀ k, Supp hc V e k → Stab hc V k → ν k = 1) (g : HA (AF (maximalRealSubfield E)) hc.sig V.gram)
    (hg : Supp hc V e g) : ν g = 1 := by
  have hur := unramified hc
  obtain ⟨σ, π, hσE, hσ⟩ := GlobalTheory.FixedPrime.exists_isUnramInv v P hin
  obtain ⟨ψ, hψE, hψσ, hψO⟩ := GlobalTheory.T.exists_ringEquiv_tensor_inert_adicCompletion E v P hin σ hσE hσ.2.1
  obtain ⟨h, hfr, hon⟩ := exists_orthonormal hc V v
  obtain ⟨s1, s2, s3⟩ := GlobalTheory.T.adelicUnitary_supportedAtFinitePlace_eq_localUnitary _ E hc V v e he
  let ψ' : LocAlg v →+* P.adicCompletion E := ψ
  let φ : HA (AF (maximalRealSubfield E)) hc.sig V.gram →* GL (Fin V.rank) (P.adicCompletion E) :=
    (bc ψ').comp ((MulAut.conj h⁻¹).toMonoidHom.comp (locMat hc V v))
  have hφ : ∀ k, φ k = bc ψ' (h⁻¹ * locMat hc V v k * h) := fun k => rfl
  have hO : ∀ z, z ∈ ordAt E v ↔ ψ' z ∈ intL (P.adicCompletion E) := fun z => (mem_ordAt_iff v z).trans (hψO z)
  have hback : ∀ x : GL (Fin V.rank) (LocAlg v), bc (ψ.symm : P.adicCompletion E →+* LocAlg v) (bc ψ' x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.symm_apply_apply _)
  have hback' : ∀ x : GL (Fin V.rank) (P.adicCompletion E),
      bc ψ' (bc (ψ.symm : P.adicCompletion E →+* LocAlg v) x) = x :=
    fun x => Units.ext (Matrix.ext fun i j => ψ.apply_symm_apply _)
  have hmem : ∀ k, φ k ∈ UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) := fun k =>
    bc_mem_UJ_one (σ := locConj v) ψ' hψσ (conj_mem_UJ _ hon (locMat_mem hc V v k))
  have hinj : ∀ k, Supp hc V e k → ∀ k', Supp hc V e k' → φ k = φ k' → k = k' := fun k hk k' hk' e => by
    refine s2 k k' hk hk' ?_
    have := congrArg (bc (ψ.symm : P.adicCompletion E →+* LocAlg v)) e
    rw [hφ, hφ, hback, hback] at this
    exact mul_left_cancel (mul_right_cancel this)
  have hsurj : ∀ u : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)),
      ∃ k, Supp hc V e k ∧ φ k = u := fun ⟨u, hu⟩ => by
    have h1 := bc_mem_UJ_one (σ' := locConj v) (ψ.symm : P.adicCompletion E →+* LocAlg v)
      (fun z => ψ.injective (by
        rw [hψσ]
        exact (ψ.apply_symm_apply _).trans (congrArg σ (ψ.apply_symm_apply _).symm))) hu
    obtain ⟨k, hk, ek⟩ := s3 _ (conj_mem_UJ _ (inv_frame _ hon) h1)
    refine ⟨k, hk, ?_⟩
    show φ k = u
    rw [hφ, ek, ← hback' u]
    congr 1
    rw [hback']
    group
  have hmul : ∀ k k', Supp hc V e k → Supp hc V e k' → Supp hc V e (k * k') := fun k k' hk hk' => by
    obtain ⟨a1, a2⟩ := (s1 k).1 hk
    obtain ⟨b1, b2⟩ := (s1 k').1 hk'
    refine (s1 _).2 ⟨?_, fun w hw => by rw [map_mul, a2 w hw, b2 w hw, one_mul]⟩
    exact (map_mul (bc (infP (maximalRealSubfield E) E)) (HA.mat _ hc.sig V.gram k)
      (HA.mat _ hc.sig V.gram k')).trans (by rw [a1, b1, one_mul])
  choose l hl1 hl2 using hsurj
  let μ : UJ σ (1 : Matrix (Fin V.rank) (Fin V.rank) (P.adicCompletion E)) →* Circle :=
    MonoidHom.mk' (fun u => ν (l u)) fun a b => by
      rw [← map_mul, hinj _ (hl1 _) _ (hmul _ _ (hl1 a) (hl1 b)) (by rw [map_mul, hl2, hl2, hl2]; rfl)]
  have hv2 : Valued.v (2 : P.adicCompletion E) = 1 := by
    rw [← map_ofNat (algebraMap E (P.adicCompletion E)) 2, GlobalTheory.Idele.valued_algebraMap,
      ← map_ofNat (algebraMap (𝓞 E) E) 2, HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_eq_one_iff).2 h2
  have : CharZero (P.adicCompletion E) := algebraRat.charZero _
  have key := GlobalTheory.T.unitaryGroup_character_eq_one_of_trivial_integral (P.adicCompletion E) π σ _ V.rank 1 hσ hv2 (one_mem _)
    (fun i j => by
      simp only [Units.val_one, Matrix.one_apply, eq_comm (a := j)]
      split_ifs
      · exact map_one σ
      · exact map_zero σ) μ
    (fun k hk => hν _ (hl1 k) ((GlobalTheory.T.stabilises_completedLattice_iff_localMatrix_integral _ E hc V v h hfr _ ((s1 _).1 (hl1 k)).2).2
      ((bc_mem_range_iff ψ' hO _).2 (by rw [← hφ, hl2]; exact hk)))) ⟨φ g, hmem g⟩
  rw [hinj g hg _ (hl1 ⟨φ g, hmem g⟩) (hl2 ⟨φ g, hmem g⟩).symm]
  exact key

end CM

section Lattice

open Formalism.BasicNotions NumberField

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem mem_dual (V : HSpace E) (L : Submodule (𝓞 E) V.V) (z : V.V) :
    z ∈ Formalism.HermitianLatticesTheory.dual V.hT L ↔ ∀ y ∈ L, ∃ o : 𝓞 E, (o : E) = V.hT y z := by
  simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one,
    LinearMap.restrictScalars_apply]

def withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 : Submodule.IsLattice E Λ)
    (h2 : ∀ y : Fin V.rank → E, y ∈ Λ ↔
      ∀ x ∈ Λ, ∃ b : 𝓞 E, (b : E) = ∑ i, ∑ j, star (x i) * V.gram i j * y j) : HSpace E :=
  { V with
    L0 := Λ.map (V.frame.equivFun.symm.toLinearMap.restrictScalars (𝓞 E))
    standardTuple_isLattice := ⟨h1.fg.map _, by
      change Submodule.span _ (V.frame.equivFun.symm.toLinearMap '' (Λ : Set (Fin V.rank → E))) = ⊤
      rw [← Submodule.map_span, h1.span_eq_top, Submodule.map_top, LinearEquiv.range]⟩
    baseLattice_isUnimodular := by
      refine Submodule.ext fun z => (mem_dual V _ z).trans ?_
      obtain ⟨y, rfl⟩ := V.frame.equivFun.symm.surjective z
      constructor
      · intro h
        refine ⟨y, (h2 y).2 fun x hx => ?_, rfl⟩
        rw [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply, ← V.frame.equivFun_symm_apply]
        exact h _ ⟨x, hx, rfl⟩
      · rintro ⟨y', hy, e⟩ _ ⟨x, hx, rfl⟩
        obtain rfl : y' = y := V.frame.equivFun.symm.injective e
        have := (h2 y').1 hy x hx
        rwa [← GlobalTheory.WeilUnramifiedCompare.hT_coord, ← V.frame.equivFun_symm_apply,
          ← V.frame.equivFun_symm_apply] at this }

theorem coord_withLat (V : HSpace E) (Λ : Submodule (𝓞 E) (Fin V.rank → E)) (h1 h2) :
    {x : Fin V.rank → E | ∑ i, x i • V.frame i ∈ (withLat V Λ h1 h2).L0} = Λ := by
  ext x
  rw [Set.mem_ofPred_eq, ← V.frame.equivFun_symm_apply]
  constructor
  · rintro ⟨y, hy, e⟩
    obtain rfl : y = x := V.frame.equivFun.symm.injective e
    exact hy
  · exact fun h => ⟨x, h, rfl⟩

end Lattice

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.WeilParts
open scoped TensorProduct Kronecker ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem char_eq_one_of_nonSplit : ∀ (D : D7) (V : HSp D) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), IsSelfDualC V Λ → ∀ v ε, NonSplitAt D v ε → ∀ ν : GA D V →* Circle, (∀ k, SuppPl ε V k → (∀ y, y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E)) ↔ (finMat D.sp.cm.sig V.gram k).mulVec y ∈ latHat D.host.F D.host.E (Λ : Set (Fin V.rank → D.host.E))) → ν k = 1) → ∀ g, SuppPl ε V g → ν g = 1 := by
  intro D V Λ hΛ v ε hv ν hν g hg
  obtain ⟨⟨α, rfl, a1, a2⟩, hn⟩ := hv
  have hα : α = singleV D.host.F v 1 := GlobalTheory.SplitIdem.af_ext _ fun w => by
    by_cases hw : w = v
    · subst hw; rw [a1, GlobalTheory.SplitIdem.evalV_singleV_same]
    · rw [a2 w hw, GlobalTheory.SplitIdem.evalV_singleV_ne _ _ _ hw]
  have hn' : ∀ e : Formalism.L2.Theta.AE D, e * e = e → e * cA D e = 0 → e + cA D e =
      algebraMap (AF D.host.F) (Formalism.L2.Theta.AE D) (pairA D.host.F 0 (singleV D.host.F v 1)) → False :=
    fun e e1 e2 e3 => by
      rw [← hα] at e3
      exact hn ⟨e, ⟨e1, e2, v, _, ⟨α, rfl, a1, a2⟩, e3⟩, e3⟩
  have h2 : (2 : 𝓞 D.host.F) ∉ v.asIdeal := fun h2 => by
    obtain ⟨e, e1, e2, e3, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
    exact hn' e e1 e2 e3
  have := v.isMaximal
  obtain ⟨Q, hQ, hQv⟩ := Ideal.exists_ideal_over_maximal_of_isIntegral (S := 𝓞 D.host.E) v.asIdeal
    (by
      rw [(RingHom.injective_iff_ker_eq_bot (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))).1
        (FaithfulSMul.algebraMap_injective _ _)]
      exact bot_le)
  have hQ0 : Q ≠ ⊥ := fun h0 => v.ne_bot (by
    rw [← hQv, h0, Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective _ _)])
  let P : HeightOneSpectrum (𝓞 D.host.E) := ⟨Q, hQ.isPrime, hQ0⟩
  have hPv : P.under (𝓞 D.host.F) = v := HeightOneSpectrum.ext hQv
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have := GlobalTheory.PlaceComp.unramified (E := D.host.E) D.sp.cm
  have hin := GlobalTheory.FixedPrime.isInertAt_under P fun x hx => by
    by_contra hx'
    obtain ⟨e, e1, e2, e3⟩ := GlobalTheory.MovedSplit.exists_splitAt D v
      ⟨Q, hQ.isPrime, hQv, _, hx, x, (star_star (x : D.host.E)).symm, hx'⟩
    exact hn' e e1 e2 e3
  have h2' : (2 : 𝓞 D.host.E) ∉ P.asIdeal := fun h => h2 (by
    rw [← hQv, Ideal.mem_comap, map_ofNat]; exact h)
  have he := GlobalTheory.PlaceComp.isIdemOf_algebraMap (E := D.host.E) a1 a2
  subst hPv
  refine core (E := D.host.E) D.sp.cm (withLat V Λ hΛ.1 hΛ.2) he hin h2' ν (fun k hk hs => hν k hk ?_) g hg
  rw [← coord_withLat V Λ hΛ.1 hΛ.2]
  exact hs

end GlobalTheory.InertChar
