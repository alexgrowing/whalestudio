import Formalism.LocalRingCardinality.SpanPowerMembership.EmbeddingBaseFieldMul
import Formalism.LocalRingCardinality.SpanPowerMembership.NZRowD

noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.Inhab
open scoped TensorProduct

section E

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} [NumberField what₂.LL] [StarRing what₂.LL]
  {LL0 : IntermediateField ℚ what₂.LL} {N : NData R H what₂}

set_option synthInstance.maxHeartbeats 400000 in

structure NzE (C : TwCore R H what₂ LL0 N) : Type 1 where
  eA : ∀ i, Bool → MonoidAlgebra (FractionRing (C.O i)) (G0g N)
  eL : G0g N → LL0
  eA_def : ∀ i b (g : G0g N), (eA i b).coeff g =
    IsFractionRing.map (A := C.O0 i) (B := C.O i) (K := FractionRing (C.O0 i))
      (L := FractionRing (C.O i)) (C.O_inj i) ((if b then C.emb0 i else C.emb0b i) (eL g))
  eA_idem : ∀ i b, eA i b * eA i b = eA i b
  eA_central : ∀ i b x, eA i b * x = x * eA i b
  Psi : ∀ i, G0g N →* (FractionRing (C.O i))ˣ
  hPsi : ∀ i b (V : Type) [AddCommGroup V] [Module (FractionRing (C.O i)) V],
    MonoidAlgebra.lift (FractionRing (C.O i)) (Module.End (FractionRing (C.O i)) V) (G0g N)
      (LinearEquiv.automorphismGroup.toLinearMapMonoidHom.comp (scalAct _ V (Psi i))) (eA i b) = 1

abbrev NzE.toIn {C : TwCore R H what₂ LL0 N} (Ed : NzE C) (n : ℕ → ℕ) : NzIn C where
  eA := Ed.eA
  eL := Ed.eL
  eA_def := Ed.eA_def
  eA_idem := Ed.eA_idem
  eA_central := Ed.eA_central
  Psi := Ed.Psi
  hPsi := Ed.hPsi
  ix j := {_a : Fin (n j) // 1 ≤ j ∧ j ≤ R.m}
  ix_out _ := fun ⟨a⟩ => a.2
  ixM j := Fin (n j)
  rM _ := Subtype.val

end E

def nzEL {R : Ranks} (H : Host R) (Lb : Lbl H) (what₂ : Rows.Data R) (h : NHyp H what₂)
    [NumberField what₂.LL] [StarRing what₂.LL] {LL0 : IntermediateField ℚ what₂.LL}
    (C : TwCore R H what₂ LL0 (ndG H Lb what₂ h)) (ht : THyp H) : NzE C :=
  let I := nzInL H Lb what₂ h C ht 0
  ⟨I.eA, I.eL, I.eA_def, I.eA_idem, I.eA_central, I.Psi, I.hPsi⟩

theorem jB_gen_set {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] (b : OrthonormalBasis (Fin n) ℂ V) :
    {x | jB σ b x ∈ genB b} = Set.range (Pi.basisFun K (Fin n)) := by
  classical
  ext x
  constructor
  · intro hx
    obtain ⟨i, -, hi⟩ := Finset.mem_image.mp (show jB σ b x ∈ Finset.univ.image b from hx)
    exact ⟨i, jB_inj σ b ((jB_single σ b i).trans hi)⟩
  · rintro ⟨i, rfl⟩
    exact (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, (jB_single σ b i).symm⟩ :
      jB σ b (Pi.basisFun K (Fin n) i) ∈ Finset.univ.image b)

variable (D : D7) [hL : IsEmpty D.nd.Loc] (C : TwCore D.R D.host D.what₂ D.LL0 D.nd) (Ed : NzE C) (n : ℕ → ℕ)
  (he : ∀ g : G0g D.nd, D.what₂.embLL ((Ed.eL g : ↥D.LL0) : D.what₂.LL) = D.ntypes.e0.coeff g)

structure StdRows where
  bt : ∀ w j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mt (D.what₂.muTw w) j)
  phi : ∀ w j, D.what₂.MtL (D.what₂.muTw w) j ≃ₗ[D.what₂.LL] (Fin (n j) → D.what₂.LL)
  hj : ∀ w j x, D.what₂.jMt (D.what₂.muTw w) j x = jB D.what₂.embLL (bt w j) (phi w j x)
  hgen : ∀ w j, (D.what₂.MtLat (D.what₂.muTw w) j).gen = genB (bt w j)
  bM : ∀ j, OrthonormalBasis (Fin (n j)) ℂ (D.what₂.Mj j)
  hgM : ∀ j, (D.what₂.MjLat j).gen = genB (bM j)
  hth : ∀ w j (x : Fin (n j) → D.what₂.LL),
    D.what₂.thetaP (D.what₂.muTw w) j (jB D.what₂.embLL (bt w j) x) = jB D.what₂.embLL (bM j) x

variable (Z : StdRows D n)

def stdMtOf : StdMt D C (Ed.toIn n) where
  bT := fun w j => (Pi.basisFun D.what₂.LL (Fin (n j))).map (Z.phi w j).symm
  bT_gen := fun w j => by
    ext x
    rw [Set.mem_setOf_eq, Z.hj, Z.hgen]
    have h := Set.ext_iff.mp (jB_gen_set D.what₂.embLL (Z.bt w j)) (Z.phi w j x)
    rw [Set.mem_setOf_eq] at h
    rw [h]
    constructor
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [Module.Basis.map_apply, hi, LinearEquiv.symm_apply_apply]⟩
    · rintro ⟨i, hi⟩
      exact ⟨i, by rw [← hi, Module.Basis.map_apply, LinearEquiv.apply_symm_apply]⟩

def divXOf : DivX (recN D C (Ed.toIn n) he) :=
  divXStd (recN D C (Ed.toIn n) he) n Z.bM Z.hgM 1 one_pos

def stdMjOf : StdMj D C (Ed.toIn n) he (stdMtOf D C Ed n Z) (divXOf D C Ed n he Z) where
  eI := fun _ a => a.1
  eI_bij := fun _ h1 h2 => ⟨fun _ _ h => Subtype.ext h, fun a => ⟨⟨a, h1, h2⟩, rfl⟩⟩
  L_std := fun _ _ _ => rfl
  th_std := fun w j _ _ x y hy a => by
    have h1 : jB D.what₂.embLL (Z.bM j) y = jB D.what₂.embLL (Z.bM j) (Z.phi w j x) := by
      rw [← Z.hth w j, ← Z.hj]; exact hy
    have h2 : y = Z.phi w j x := jB_inj _ _ h1
    show (Pi.basisFun D.what₂.LL (Fin (n j))).repr y a.1 =
      ((Pi.basisFun D.what₂.LL (Fin (n j))).map (Z.phi w j).symm).repr x a.1
    rw [Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_symm, h2]

variable (hLL0 : ∀ x : D.what₂.LL, x ∈ D.LL0)

def nchStd : NChoice (recN D C (Ed.toIn n) he) :=
  nchN D C (Ed.toIn n) he (embCOf D C (Ed.toIn n) he hLL0) (stdMtOf D C Ed n Z)

theorem nchStd_tie : NChTie (recN D C (Ed.toIn n) he) (nchStd D C Ed n he Z hLL0) :=
  nchN_tie D C (Ed.toIn n) he _ _

def nmjStd : NMj (recN D C (Ed.toIn n) he) (divXOf D C Ed n he Z) (nchStd D C Ed n he Z hLL0) :=
  nmjN D C (Ed.toIn n) he _ _ _ (stdMjOf D C Ed n he Z)

end Formalism.BasicNotions.Examples₂.NZ
