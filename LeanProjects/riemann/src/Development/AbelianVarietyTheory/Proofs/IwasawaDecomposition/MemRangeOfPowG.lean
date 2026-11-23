import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmbientBaseHeq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NoRamifiedNorm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeUOperatorRationalInvertibleRamifiedFormsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DGamDvdOfMinkMult
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BaseFieldsDefiniteLaws
import Formalism.LocalToGlobal.GroupLattices.Joint0
import Formalism.LocalToGlobal.GroupLattices.TiedFamilies.ChiMemSubfield

noncomputable section

namespace GlobalTheory.Mem.Top.ColOwe

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host Formalism.L2.Forms GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Top NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem natCast_kv_eq_zero (F : Type) [Field F] [NumberField F]
    (v : HeightOneSpectrum (𝓞 F)) (p : ℕ) (h : (p : 𝓞 F) ∈ v.asIdeal) : (p : kv F v) = 0 := by

  have hval : Valued.v ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) :
      v.adicCompletion F)) < 1 := by
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact (v.valuation_lt_one_iff_mem (K := F) _).2 h
  have hmax : algebraMap (𝓞 F) (v.adicCompletionIntegers F) (p : 𝓞 F) ∈
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) :=
    (Valuation.mem_maximalIdeal_iff _ Valued.v).2 hval
  have hres := (IsLocalRing.residue_eq_zero_iff _).2 hmax
  simpa using hres

theorem mem_range_of_pow_g (B : Base) (i : Fin 2) (z : ℂ) (hz : z ^ B.host.g i = 1) : ∃ r : B.LL, B.embLL r = z := by
  have hp : (B.host.g i).Prime := B.host.g_prime i

  have hmem : B.host.g i * (B.host.g i - 1) ∈ [B.toPre.restRowsFiniteGroupCard, B.host.g 0 * (B.host.g 0 - 1),
      B.host.g 1 * (B.host.g 1 - 1), 3 ^ 4, 5 ^ 4] := by
    fin_cases i <;> simp
  obtain ⟨z0, -, hz0⟩ := B.roots_Ks _ hmem
  have hN : B.host.g i * (B.host.g i - 1) ≠ 0 :=
    Nat.mul_ne_zero hp.ne_zero (by have := hp.two_le; omega)
  have hprim : IsPrimitiveRoot (B.embLL z0) (B.host.g i * (B.host.g i - 1)) := by
    rw [hz0]; exact Complex.isPrimitiveRoot_exp _ hN

  have hprim' : IsPrimitiveRoot (B.embLL z0 ^ (B.host.g i - 1)) (B.host.g i) :=
    hprim.pow (Nat.pos_of_ne_zero hN) (mul_comm _ _)
  have : NeZero (B.host.g i) := ⟨hp.ne_zero⟩
  obtain ⟨k, -, hk⟩ := hprim'.eq_pow_of_pow_eq_one hz
  exact ⟨(z0 ^ (B.host.g i - 1)) ^ k, by rw [map_pow, map_pow, hk]⟩

theorem psi0Rat (X : Stages) (T : ∀ u, Forms0 X.toD7 u) (u : X.toD7.what₂.Word) : Formalism.L2.G.LevelZeroCharacterRational T u := by
  intro i v h x

  have hx : ((T u).gl.psi0 i v h x) ^ X.toD7.host.g i = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, natCast_kv_eq_zero _ v _ h, zero_mul,
      AddChar.map_zero_eq_one]
  exact mem_range_of_pow_g X.B i _ hx

variable {D : D7}

def levOf (C : ColsTiedSym D) : LevelData D := C.herm.base.lev0

def formsOf (C : ColsTiedSym D) (u : D.what₂.Word) : Forms0 D u := (C.forms u).to0

def errOf (H : Formalism.L2.Herm.ColsHermS D) : ErrX D := (GlobalTheory.Mem.ErrTies.exists_errX D H).choose

theorem errOf_piG (H : Formalism.L2.Herm.ColsHermS D) : (errOf H).piG = (H.levelZeroCompatibility D.u₀).piG :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.1

theorem errOf_piT (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) : (errOf H).piT u = (H.atT u).piU :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.1 u

theorem errOf_vPl (H : Formalism.L2.Herm.ColsHermS D) (u : D.what₂.Word) (v : (D.mem u).A.vT) :
    (errOf H).vPl u v = (H.base.vT u v).1 :=
  (GlobalTheory.Mem.ErrTies.exists_errX D H).choose_spec.2.2.1 u v

theorem joint0 (C : ColsTiedSym D) (u : D.what₂.Word) : Joint0 (levOf C) u (formsOf C u) := by
  unfold levOf formsOf
  exact C.joint0 u

theorem dGamChoice_of_lcm (X : Stages) (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) :
    DGamChoice_at X.toD7 := by
  intro M hM u

  have hc : (X.toD7.mem u).C = X.C.chTw u X.C.mu0 := (X.C.memberColumns_twistedChain_base u).symm
  rw [hc, hDG u X.C.mu0]
  have hf : X.B.fields.f = X.B.R.f := (GlobalTheory.Mem.FieldsLaws.fields_satisfy_definite_laws X.B).2
  refine GlobalTheory.Mem.Col2.DGam_dvd_of_minkMult X.B.R (GlobalTheory.Mem.FieldsLaws.fields_ok (B := X.B)) M ?_
  rw [hf]
  exact hM

theorem colLay_of_herm (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R)
    (H : Formalism.L2.Herm.ColsHermS X.toD7) (T : ∀ u, Forms0 X.toD7 u) (hJ : ∀ u, Joint0 H.base.lev0 u (T u)) :
    ColLay X.toD7 H.base.lev0 (errOf H) where
  piG_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.1
  piT_lev := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.1
  seen := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.1
  tauOf := (GlobalTheory.Mem.ErrTies.exists_errX X.toD7 H).choose_spec.2.2.2.2.2.2
  one u μ := by
    have h0 : (X.C.chTw X.B.u₀ X.C.mu0).DGam = (X.C.mem X.B.u₀).C.DGam :=
      congrArg (fun c => c.DGam) (X.C.memberColumns_twistedChain_base X.B.u₀)
    exact (hDG u μ).trans ((hDG X.B.u₀ X.C.mu0).symm.trans h0)
  mink := dGamChoice_of_lcm X hDG
  atT := GlobalTheory.T.heckeUOperator_rational_invertible_ramifiedForms X hX H T hJ (fun u => psi0Rat X T u)

theorem colLay_of_tied (X : Stages) (hX : Nonempty (PreX X.B.toPre))
    (hDG : ∀ u μ, (X.C.chTw u μ).DGam = GlobalTheory.Mem.Col2.DGam X.B.fields.E X.B.R) (C : ColsTiedSym X.toD7) :
    ColLay X.toD7 (levOf C) (errOf C.herm) :=
  colLay_of_herm X hX hDG C.herm (formsOf C) (joint0 C)

end GlobalTheory.Mem.Top.ColOwe

end
