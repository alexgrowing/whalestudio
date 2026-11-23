import Formalism.LocalToGlobal.HermitianForms.TiedStep

noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

section Gen

variable {E : Type} [Field E] [NumberField E] {n : ℕ}

def dualL (σ : E →+* E) (J : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) (dualSet σ J L)

def mulLat (γ : Matrix (Fin n) (Fin n) E) (L : Submodule (𝓞 E) (Fin n → E)) : Submodule (𝓞 E) (Fin n → E) :=
  L.map ((Matrix.mulVecLin γ).restrictScalars (𝓞 E))

end Gen

variable {D : D7}

structure AtTTied (u : D.what₂.Word) where

  eV : (D.mem u).A.vT ≃ PlT D u

  piU : 𝓞 D.host.E
  piU_K : (piU : D.host.E) ∈ D.host.K
  piU_norm : (piU : D.host.E) * D.host.conj piU = ((D.mem u).A.T : D.host.E)
  piU_cong : piU - 1 ∈ Ideal.span
    {((D.host.QS * D.host.q * D.host.d * (D.host.g 0 * D.host.g 1) ^ 2 : ℕ) : 𝓞 D.host.E)}

  res : ∀ v, 𝓞 D.host.E →+* (D.mem u).A.Fv v
  res_surj : ∀ v, Function.Surjective (res v)
  res_pi : ∀ v, res v piU = 0

  res_conj : ∀ v (pb : 𝓞 D.host.E), (pb : D.host.E) = D.host.conj piU → res v pb ≠ 0
  res_v : ∀ v (x : 𝓞 D.host.F), x ∈ (eV v).1.asIdeal ↔ res v (algebraMap (𝓞 D.host.F) (𝓞 D.host.E) x) = 0

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v (x : 𝓞 D.host.F),
    x ∈ (eV v).1.asIdeal ↔ (0 : WithTop ℤ) < D.what₂.places.val w
      (D.embE (D.host.sigmaOf (D.eTau ((D.fm u).tauOf w v) : D.R.GG)
        (algebraMap (𝓞 D.host.F) D.host.E x)))

  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ τ : D.what₂.Tau,
    (0 : WithTop ℤ) < D.what₂.places.val w (D.embE (D.host.sigmaOf (D.eTau τ : D.R.GG)
      (if (D.fm u).seenP w = true then (piU : D.host.E) else D.host.conj piU)))

def AtTTied.Pv {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : Ideal (𝓞 D.host.E) := RingHom.ker (A.res v)

instance {u : D.what₂.Word} (A : AtTTied u) (v : (D.mem u).A.vT) : (A.Pv v).IsPrime := RingHom.ker_isPrime _

abbrev Ld (D : D7) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  dualL (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)

abbrev Lk {u : D.what₂.Word} (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (v : (D.mem u).A.vT) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  clsCrd D u i hi c ⊔ A.Pv v • Ld D u i hi c

set_option maxHeartbeats 1000000 in

structure LvTied (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) where

  pr : ∀ v c, ↥(Ld D u i hi c) →+ (D.fm u).lv i v c
  pr_surj : ∀ v c, Function.Surjective (pr v c)
  pr_smul : ∀ v c (a : 𝓞 D.host.E) z, pr v c (a • z) = A.res v a • pr v c z
  pr_ker : ∀ v c z, pr v c z = 0 ↔ z.1 ∈ A.Pv v • Ld D u i hi c

  fv_ker : ∀ v c z, (D.fm u).fv i v c (pr v c z) = 0 ↔ z.1 ∈ Lk A i hi v c

  prk : ∀ v c, ↥(Lk A i hi v c) →+ (D.fm u).lk i v c
  prk_surj : ∀ v c, Function.Surjective (prk v c)
  prk_smul : ∀ v c (a : 𝓞 D.host.E) z, prk v c (a • z) = A.res v a • prk v c z
  prk_ker : ∀ v c z, prk v c z = 0 ↔ z.1 ∈ A.Pv v • Lk A i hi v c

  te : ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (pr v c z) = 1 →
    ∀ h : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • z.1 ∈ Lk A i hi v c, prk v c ⟨_, h⟩ = (D.fm u).te i v c

variable {u : D.what₂.Word} {A : AtTTied u} {i : ℕ} {hi : i ≤ D.R.m}

set_option maxHeartbeats 1000000 in

def FvTie (P : LvTied u A i hi) (K : ClsTied u i hi)
    (fMe : ∀ v, K.lev.fM (A.eV v).1 (A.eV v).2 ≃+ (D.mem u).A.Fv v) : Prop :=
  ∀ v c (z : ↥(Ld D u i hi c))
    (hz : ((bc (prV (E := D.host.E) (A.eV v).1) (K.y c).1)⁻¹).1 *ᵥ
        (fun a => inclE (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (z.1 a)) ∈
      latS (F := D.host.F) ((A.eV v).1.adicCompletion D.host.F) (intV D.host.E (A.eV v).1)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) K.lev.Lb))),
    (D.fm u).fv i v c (P.pr v c z) = fMe v (K.lev.fT (A.eV v).1 (A.eV v).2 ⟨_, hz⟩)

set_option maxHeartbeats 1000000 in

def UpTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (P.pr v c z) = 1 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).up i v c (P.pr v c z))).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c (P.pr v c z))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
        (D.fm u).fv i v _ (P.pr v _ x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) ∧
      ∀ g ∈ AdFun K.lev (embT D),
        (D.fm u).upT i v c (P.pr v c z) (fun s => g (K.y ((D.fm u).up i v c (P.pr v c z))) (W.eY s)) =
          fun s => g (K.y c * η) (W.eY s)

set_option maxHeartbeats 1000000 in

def DnTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).dn i v c g)).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk A i hi v c),
        (D.fm u).fv i v _ (P.pr v _ x) = g (P.prk v c ⟨_, hx⟩)) ∧
      ∀ f ∈ AdFun K.lev (embT D),
        (D.fm u).dnT i v c g (fun s => f (K.y ((D.fm u).dn i v c g)) (W.eY s)) = fun s => f (K.y c * η) (W.eY s)

set_option maxHeartbeats 1000000 in

def UpNatTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (z : ↥(Ld D u i hi c)), (D.fm u).fv i v c (P.pr v c z) = 1 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).up i v c (P.pr v c z))).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (clsCrd D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c) ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).up i v c (P.pr v c z)))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (Ld D u i hi c ⊔
          Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).up i v c (P.pr v c z))))
        (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1.1 *ᵥ x.1) ∈ Ld D u i hi c),
        (D.fm u).fv i v _ (P.pr v _ x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) ∧
      ∀ (h : (D.mem u).C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
        (D.fm u).upT i v c (P.pr v c z) h s = (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

set_option maxHeartbeats 1000000 in

def DnNatTie (P : LvTied u A i hi) (K : ClsTied u i hi) (W : ValTied u A.eV i hi K) : Prop :=
  ∀ v c (g : Module.Dual ((D.mem u).A.Fv v) ((D.fm u).lk i v c)), g ≠ 0 →
    ∃ (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi))
      (η : UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) (κ : K.lev.U),
      (∀ v', v' ≠ (A.eV v).1 → bc (prV (E := D.host.E) v') η.1 = 1) ∧
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 *
        (K.y ((D.fm u).dn i v c g)).1 = (K.y c).1 * η.1 * κ.1 ∧
      Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (mulLat γ.1.1 (Ld D u i hi ((D.fm u).dn i v c g))) =
        Formalism.HermitianLatticesTheory.localization₂ (A.Pv v) (clsCrd D u i hi c) ∧
      (∀ (x : ↥(Ld D u i hi ((D.fm u).dn i v c g))) (hx : γ.1.1 *ᵥ x.1 ∈ Lk A i hi v c),
        (D.fm u).fv i v _ (P.pr v _ x) = g (P.prk v c ⟨_, hx⟩)) ∧
      ∀ (h : (D.mem u).C.Y i → ℂ) s s', IsTr (atInf (embT D) γ.1.1) (W.eY s') (W.eY s) →
        (D.fm u).dnT i v c g h s = (((K.lev.chi κ)⁻¹ : ℂˣ) : ℂ) * h s'

end Formalism.L2.Forms
