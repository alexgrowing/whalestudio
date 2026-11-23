import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.SatSplit
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassType.UnitaryLocalMassIdentity
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.SplitIntLoc

noncomputable section

namespace PI.LocMassTypS

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.LocVol NumberField IsDedekindDomain
open scoped TensorProduct
open PI.LocMassTypW

section Gen

variable {K A : Type} [Field K] [CommRing A] [Algebra K A] {e : A}

theorem idem_mul_compl (he : e * e = e) : e * (1 - e) = 0 := by
  rw [mul_sub, mul_one, he, sub_self]

theorem compl_idem (he : e * e = e) : (1 - e) * (1 - e) = 1 - e := by
  rw [sub_mul, one_mul, idem_mul_compl he, sub_zero]

theorem linInd (he : e * e = e) (h0 : e ≠ 0) (h1 : e ≠ 1) : LinearIndependent K ![e, 1 - e] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h1' : (1 - e) ≠ 0 := sub_ne_zero.2 (Ne.symm h1)
  have hs : s • e = 0 := by
    have := congrArg (· * e) hst
    simp only [add_mul, smul_mul_assoc, he, mul_comm (1 - e) e, idem_mul_compl he, smul_zero,
      add_zero, zero_mul] at this
    exact this
  have ht : t • (1 - e) = 0 := by
    have := congrArg (· * (1 - e)) hst
    simp only [add_mul, smul_mul_assoc, idem_mul_compl he, compl_idem he, smul_zero,
      zero_add, zero_mul] at this
    exact this
  exact ⟨(smul_eq_zero.1 hs).resolve_right h0, (smul_eq_zero.1 ht).resolve_right h1'⟩

variable [FiniteDimensional K A] (h2 : Module.finrank K A = 2) (he : e * e = e) (h0 : e ≠ 0)
  (h1 : e ≠ 1)

def B : Module.Basis (Fin 2) K A :=
  basisOfLinearIndependentOfCardEqFinrank (linInd he h0 h1) (by simp [h2])

theorem B_apply (i : Fin 2) : B h2 he h0 h1 i = ![e, 1 - e] i := by
  simp [B, coe_basisOfLinearIndependentOfCardEqFinrank]

def c1 (x : A) : K := (B h2 he h0 h1).repr x 0

def c2 (x : A) : K := (B h2 he h0 h1).repr x 1

theorem decomp (x : A) : x = c1 h2 he h0 h1 x • e + c2 h2 he h0 h1 x • (1 - e) := by
  have := (B h2 he h0 h1).sum_repr x
  rw [Fin.sum_univ_two, B_apply, B_apply] at this
  simpa [c1, c2] using this.symm

theorem mul_e (x : A) : x * e = c1 h2 he h0 h1 x • e := by
  conv_lhs => rw [decomp h2 he h0 h1 x]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, he, mul_comm (1 - e) e, idem_mul_compl he,
    smul_zero, add_zero]

theorem mul_ce (x : A) : x * (1 - e) = c2 h2 he h0 h1 x • (1 - e) := by
  conv_lhs => rw [decomp h2 he h0 h1 x]
  rw [add_mul, smul_mul_assoc, smul_mul_assoc, idem_mul_compl he, compl_idem he, smul_zero,
    zero_add]

include h0 in
theorem uniq1 {c d : K} (h : c • e = d • e) : c = d := smul_left_injective K h0 h

include h1 in
theorem uniq2 {c d : K} (h : c • (1 - e) = d • (1 - e)) : c = d :=
  smul_left_injective K (sub_ne_zero.2 (Ne.symm h1)) h

def p1 : A →+* K where
  toFun := c1 h2 he h0 h1
  map_one' := uniq1 h0 (by rw [← mul_e h2 he h0 h1, one_mul, one_smul])
  map_mul' x y := uniq1 h0 (by
    rw [← mul_e h2 he h0 h1, mul_assoc, mul_e h2 he h0 h1 y, mul_smul_comm, mul_e h2 he h0 h1 x,
      smul_smul, mul_comm])
  map_zero' := uniq1 h0 (by rw [← mul_e h2 he h0 h1, zero_mul, zero_smul])
  map_add' x y := uniq1 h0 (by
    rw [← mul_e h2 he h0 h1, add_mul, mul_e h2 he h0 h1 x, mul_e h2 he h0 h1 y, add_smul])

def p2 : A →+* K where
  toFun := c2 h2 he h0 h1
  map_one' := uniq2 h1 (by rw [← mul_ce h2 he h0 h1, one_mul, one_smul])
  map_mul' x y := uniq2 h1 (by
    rw [← mul_ce h2 he h0 h1, mul_assoc, mul_ce h2 he h0 h1 y, mul_smul_comm, mul_ce h2 he h0 h1 x,
      smul_smul, mul_comm])
  map_zero' := uniq2 h1 (by rw [← mul_ce h2 he h0 h1, zero_mul, zero_smul])
  map_add' x y := uniq2 h1 (by
    rw [← mul_ce h2 he h0 h1, add_mul, mul_ce h2 he h0 h1 x, mul_ce h2 he h0 h1 y, add_smul])

theorem adeleInfiniteComponent_apply (x : A) : p1 h2 he h0 h1 x = c1 h2 he h0 h1 x := rfl

theorem adele_ext_components (x : A) : p2 h2 he h0 h1 x = c2 h2 he h0 h1 x := rfl

theorem idem_cases {a : K} (h : a * a = a) : a = 0 ∨ a = 1 := by
  have : a * (a - 1) = 0 := by rw [mul_sub, mul_one, h, sub_self]
  rcases mul_eq_zero.1 this with h' | h'
  · exact Or.inl h'
  · exact Or.inr (sub_eq_zero.1 h')

end Gen

section Split

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F))

attribute [local instance] LocMassOrdSF.finDim_FE

theorem finrank_tens (h : Module.finrank F E = 2) :
    Module.finrank (Fv F v) (Fv F v ⊗[F] E) = 2 := by
  rw [Module.finrank_eq_card_basis (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))]
  simp [h]

theorem finDim_tens : FiniteDimensional (Fv F v) (Fv F v ⊗[F] E) :=
  Module.Finite.of_basis (Algebra.TensorProduct.basis (Fv F v) (Module.finBasis F E))

theorem sigR_sc (c : Fv F v) : sigR (Fv F v) σ (sc (E := E) v c) = sc (E := E) v c := by
  simp [sigR, sc]

theorem sigR_inclR (y : E) : sigR (Fv F v) σ (inclR (F := F) (Fv F v) y) = inclR (F := F) (Fv F v) (σ y) := by
  simp [sigR, inclR]

theorem sigR_smul (c : Fv F v) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (c • x) = c • sigR (Fv F v) σ x := by
  rw [← PI.LocMassTypU.sc_mul_eq_smul, map_mul, sigR_sc, PI.LocMassTypU.sc_mul_eq_smul]

theorem sigR_sigR (hσ : ∀ y, σ (σ y) = y) (x : Fv F v ⊗[F] E) :
    sigR (Fv F v) σ (sigR (Fv F v) σ x) = x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul c y => simp [sigR, hσ]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

theorem inclR_injective : Function.Injective (inclR (F := F) (Fv F v) : E → Fv F v ⊗[F] E) :=
  Algebra.TensorProduct.includeRight_injective (algebraMap F (Fv F v)).injective

theorem sigma_invol (hCM : IsCMExt F E σ) (y : E) : σ (σ y) = y := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hCM.2.2.2 τ (σ y), hCM.2.2.2 τ y, star_star]

theorem sigma_ne_id (hCM : IsCMExt F E σ) : ∃ y, σ y ≠ y := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hR : ComplexEmbedding.IsReal τ := by
    rw [ComplexEmbedding.isReal_iff]
    ext x
    rw [ComplexEmbedding.conjugate_coe_eq]
    have := hCM.2.2.2 τ x
    rw [hcon x] at this
    exact this.symm
  have hc := hCM.2.1.isComplex (InfinitePlace.mk τ)
  exact (InfinitePlace.not_isReal_iff_isComplex.2 hc) ⟨τ, hR, rfl⟩

theorem oev_one : (1 : Fv F v ⊗[F] E) ∈ OEv (E := E) v := by
  have := PI.LocMassTypU.inclR_mem (E := E) v 1
  simpa using this

theorem oev_mul {a b : Fv F v ⊗[F] E} (ha : a ∈ OEv (E := E) v) (hb : b ∈ OEv (E := E) v) :
    a * b ∈ OEv (E := E) v := by
  change a ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at ha
  change b ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hb
  change a * b ∈ Submodule.span (v.adicCompletionIntegers F)
    ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ)
  induction ha using Submodule.span_induction with
  | mem a' ha' =>
    obtain ⟨α, -, rfl⟩ := ha'
    induction hb using Submodule.span_induction with
    | mem b' hb' =>
      obtain ⟨β, -, rfl⟩ := hb'
      exact Submodule.subset_span ⟨α * β, trivial, by simp [map_mul]⟩
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

def OEvR : Subring (Fv F v ⊗[F] E) where
  carrier := OEv (E := E) v
  mul_mem' := oev_mul v
  one_mem' := oev_one v
  add_mem' := PI.LocMassTypU.oev_add v
  zero_mem' := PI.LocMassTypU.oev_zero v
  neg_mem' := PI.LocMassTypU.oev_neg v

def cm : E ⊗[F] Fv F v ≃ₐ[F] Fv F v ⊗[F] E := Algebra.TensorProduct.comm F E (Fv F v)

theorem oev_iff_tensInt (x : Fv F v ⊗[F] E) :
    x ∈ OEv (E := E) v ↔ (cm v).symm x ∈
      PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
        (v.adicCompletionIntegers F).toSubring := by
  set T := PI.SplitIntLoc.tensInt (F := F) (Fv F v) (PI.SplitIntLoc.intOE E)
    (v.adicCompletionIntegers F).toSubring with hT
  have hsc : ∀ c ∈ v.adicCompletionIntegers F, (cm v).symm (sc (E := E) v c) ∈ T := by
    intro c hc
    have e : (cm v).symm (sc (E := E) v c) = (1 : E) ⊗ₜ[F] c := by
      simp [cm, sc]
    rw [e]
    exact Subring.subset_closure (Or.inr ⟨⟨c, hc⟩, rfl⟩)
  constructor
  · intro hx
    change x ∈ Submodule.span (v.adicCompletionIntegers F)
      ((fun x : 𝓞 E => inclR (F := F) (Fv F v) (x : E)) '' Set.univ) at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, -, rfl⟩ := hy
      have e : (cm v).symm (inclR (F := F) (Fv F v) (a : E)) = (a : E) ⊗ₜ[F] (1 : Fv F v) := by
        simp [cm, inclR]
      rw [e]
      exact Subring.subset_closure (Or.inl ⟨⟨(a : E), ⟨a, rfl⟩⟩, rfl⟩)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add]; exact T.add_mem hy hz
    | smul c y _ hy =>
      have e : c • y = sc (E := E) v (c : Fv F v) * y := by
        rw [PI.LocMassTypU.sc_mul_eq_smul]
        rfl
      rw [e, map_mul]
      exact T.mul_mem (hsc _ c.2) hy
  · intro hx
    have hle : T ≤ (OEvR v).comap (cm v).toAlgHom.toRingHom := by
      rw [hT]
      unfold PI.SplitIntLoc.tensInt
      rw [Subring.closure_le]
      rintro _ (⟨⟨a, ⟨b, rfl⟩⟩, rfl⟩ | ⟨⟨c, hc⟩, rfl⟩)
      · show (cm v) ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : Fv F v)) ∈ OEv (E := E) v
        have e : (cm v) ((algebraMap (𝓞 E) E b) ⊗ₜ[F] (1 : Fv F v)) =
            inclR (F := F) (Fv F v) (b : E) := by
          simp [cm, inclR]
        rw [e]
        exact PI.LocMassTypU.inclR_mem v b
      · show (cm v) ((1 : E) ⊗ₜ[F] c) ∈ OEv (E := E) v
        have e : (cm v) ((1 : E) ⊗ₜ[F] c) = c • (1 : Fv F v ⊗[F] E) := by
          rw [← PI.LocMassTypU.sc_mul_eq_smul, mul_one]
          simp [cm, sc]
        rw [e]
        exact PI.LocMassTypU.oev_smul v hc (oev_one v)
    have h : x ∈ OEvR v := by simpa using hle hx
    exact h

end Split

end PI.LocMassTypS
