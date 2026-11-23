import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SameForm
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

noncomputable section

namespace GlobalTheory.Mem.Df

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem GlobalTheory.Mem.Col2

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 1000000

theorem inner_eq_of_norm_sq {K V E M : Type} [Field K] [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [AddCommGroup M] [Module K M] (σ : K →+* ℂ) (j : M →ₛₗ[σ] V) (hspan : Submodule.span ℂ (Set.range j) = ⊤) (k : K)
    (hk : (σ k).im ≠ 0) (e : V →ₗ[ℂ] E) (q : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ) (hn : ∀ m, ((‖e (j m)‖ ^ 2 : ℝ) : ℂ) = q (j m) (j m))
    (y y' : V) : inner ℂ (e y) (e y') = q y y' := by
  let D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ := LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ)
    (fun y y' => inner ℂ (e y) (e y') - q y y')
    (fun y z y' => by simp only [map_add, inner_add_left, LinearMap.add_apply]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_left, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]; ring)
    (fun y y' z => by simp only [map_add, inner_add_right]; ring)
    (fun c y y' => by simp only [map_smul, inner_smul_right, smul_eq_mul, RingHom.id_apply]; ring)
  have hDapp : ∀ y y', D y y' = inner ℂ (e y) (e y') - q y y' := fun y y' => rfl
  have h0 : ∀ m, D (j m) (j m) = 0 := by
    intro m
    rw [hDapp, ← hn m, inner_self_eq_norm_sq_to_K]
    simp
  have hsym : ∀ m m', D (j m) (j m') + D (j m') (j m) = 0 := by
    intro m m'
    have h := h0 (m + m')
    simp only [map_add, LinearMap.add_apply, h0 m, h0 m'] at h
    linear_combination h
  have hpair : ∀ m m', D (j m) (j m') = 0 := by
    intro m m'
    have h1 := hsym m (k • m')
    rw [j.map_smulₛₗ, map_smul, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul] at h1
    have h2 := hsym m m'
    have h3 : (σ k - starRingEnd ℂ (σ k)) * D (j m) (j m') = 0 := by linear_combination h1 - starRingEnd ℂ (σ k) * h2
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exfalso
      rw [Complex.sub_conj] at h4
      simp [hk] at h4
    · exact h4
  have h1 : ∀ m, D (j m) = 0 := fun m => LinearMap.ext_on_range hspan fun m' => by rw [hpair m m']; rfl
  have hall : D = 0 := LinearMap.ext_on_range hspan fun m => by rw [h1 m]; rfl
  have h := congrArg (fun D : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ => D y y') hall
  simp only [hDapp, LinearMap.zero_apply] at h
  exact sub_eq_zero.1 h

theorem exists_embLL_im_ne {B : Base} (hX : B.fields.Ok) : ∃ k : B.LL, (B.embLL k).im ≠ 0 := by
  have hc : (InfinitePlace.mk (B.embLL : B.fields.K →+* ℂ)).IsComplex := hX.cplxK.isComplex _
  rw [← InfinitePlace.not_isReal_iff_isComplex, InfinitePlace.isReal_mk_iff] at hc
  by_contra hne
  push_neg at hne
  apply hc
  rw [ComplexEmbedding.isReal_iff]
  ext x
  rw [ComplexEmbedding.conjugate_coe_eq]
  exact Complex.conj_eq_iff_im.2 (hne x)

variable {B : Base} {X : PreX B.toPre} (I : TC B X)

def cjPol (ι : Type) (n : ℕ) : Pol ℂ ι n →ₗ⋆[ℂ] Pol ℂ ι n where
  toFun p := MvPolynomial.map (starRingEnd ℂ) p
  map_add' p q := map_add _ p q
  map_smul' c p := by
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C, RingHom.id_apply]

theorem map_conj_smul {ι : Type} {n : ℕ} (r : ℂ) (p : Pol ℂ ι n) :
    MvPolynomial.map (starRingEnd ℂ) (r • p) = starRingEnd ℂ r • MvPolynomial.map (starRingEnd ℂ) p :=
  (cjPol ι n).map_smulₛₗ r p

abbrev rowS (a : I.ι) : GSD B.fields.K := mtildeGSD (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) I.Ps

theorem rowS_ok (hX : B.fields.Ok) (a : I.ι) : (rowS I a).Ok :=
  mtildeOk (Pr := B.primes X) (R := B.R) B.wts I.Ch I.sel (I.tup a) hX I.Ps

def cTerm (a : I.ι) (c : (rowS I a).Cl) (F G : MtCx I a) : ℂ :=
  ((Nat.card (@MulAction.stabilizer (rowS I a).G (rowS I a).D _ (rowS I a).actD ((rowS I a).outSec.rep c)) : ℕ) : ℂ)⁻¹ *
    pairB B.wts.sgTrue (MvPolynomial.map (starRingEnd ℂ) (F.1 ((rowS I a).outSec.rep c))) (G.1 ((rowS I a).outSec.rep c))

theorem cTerm_add_left (a : I.ι) (c : (rowS I a).Cl) (F F' G : MtCx I a) :
    cTerm I a c (F + F') G = cTerm I a c F G + cTerm I a c F' G := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add, LinearMap.add_apply, mul_add]

theorem cTerm_smul_left (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c (r • F) G = starRingEnd ℂ r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_conj_smul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem cTerm_add_right (a : I.ι) (c : (rowS I a).Cl) (F G G' : MtCx I a) :
    cTerm I a c F (G + G') = cTerm I a c F G + cTerm I a c F G' := by
  simp only [cTerm, Submodule.coe_add, Pi.add_apply, map_add, mul_add]

theorem cTerm_smul_right (a : I.ι) (c : (rowS I a).Cl) (r : ℂ) (F G : MtCx I a) :
    cTerm I a c F (r • G) = r * cTerm I a c F G := by
  simp only [cTerm, SetLike.val_smul, Pi.smul_apply, map_smul, smul_eq_mul]
  ring

def cSum (hX : B.fields.Ok) (a : I.ι) : MtCx I a →ₗ⋆[ℂ] MtCx I a →ₗ[ℂ] ℂ :=
  letI := (rowS_ok I hX a).fintypeCl
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun F G => ∑ c : (rowS I a).Cl, cTerm I a c F G)
    (fun F F' G => by simp only [cTerm_add_left, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_left, Finset.mul_sum, smul_eq_mul])
    (fun F G G' => by simp only [cTerm_add_right, Finset.sum_add_distrib])
    (fun r F G => by simp only [cTerm_smul_right, Finset.mul_sum, smul_eq_mul, RingHom.id_apply])

theorem cSum_apply (hX : B.fields.Ok) (a : I.ι) (F G : MtCx I a) :
    cSum I hX a F G = letI := (rowS_ok I hX a).fintypeCl; ∑ c : (rowS I a).Cl, cTerm I a c F G := rfl

end GlobalTheory.Mem.Df

end
