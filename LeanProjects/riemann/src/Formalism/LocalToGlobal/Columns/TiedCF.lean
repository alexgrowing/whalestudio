import Formalism.LocalToGlobal.Columns.TiedRec
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Col.CF

open Formalism.L2.Forms

section Step

variable (D : ColRec)

def sigD : D.host.E →ₐ[D.host.F] D.host.E := letI := D.host.cmStar; D.sp.cm.sig

def embT : D.what₂.Tau → D.host.E →+* ℂ := fun τ => D.host.emb (D.eTau τ : D.R.GG)

theorem rankN (i : ℕ) (hi : i ≤ D.R.m) : letI := D.host.cmStar; (D.sp.X i).rank = D.R.N i :=
  letI := D.host.cmStar; D.sp.X_rank i hi

def gramN (i : ℕ) (hi : i ≤ D.R.m) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E :=
  letI := D.host.cmStar
  (D.sp.X i).gram.reindex (finCongr (rankN D i hi)) (finCongr (rankN D i hi))

def clsCrd (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
    Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.clsLat u i c).map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def selfDualLatticeCoords (i : ℕ) (hi : i ≤ D.R.m) : Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E) :=
  letI := D.host.cmStar
  (D.sp.X i).L0.map ((((D.sp.X i).frame.equivFun.trans
    (LinearEquiv.funCongrLeft D.host.E D.host.E (finCongr (rankN D i hi)).symm) :
      (D.sp.X i).V ≃ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)) :
      (D.sp.X i).V →ₗ[D.host.E] (Fin (D.R.N i) → D.host.E)).restrictScalars (𝓞 D.host.E))

def badG : Set (HeightOneSpectrum (𝓞 D.host.F)) :=
  {v | (D.host.g 0 : 𝓞 D.host.F) ∈ v.asIdeal ∨ (D.host.g 1 : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev PlT (u : D.what₂.Word) : Type :=
  {v : HeightOneSpectrum (𝓞 D.host.F) // (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal}

abbrev Fr (i : ℕ) (hi : i ≤ D.R.m) : Type := Frames (gramC (gramN D i hi) (embT D))

def RatSpan {n : ℕ} (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

def IntSpan {n : ℕ} (w : D.what₂.places.Pl) (lam : D.what₂.Tau → DomWeight n) :
    AddSubgroup (MvPolynomial (D.what₂.Tau × Fin n × Fin n) ℂ) :=
  AddSubgroup.closure {p | ∃ (r : D.what₂.LL) (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ),
    r ∈ intW D.what₂.places w ∧ (∀ τ, f τ ∈ delSq ℤ n (lam τ)) ∧
    p = D.what₂.embLL r • ten (fun τ => MvPolynomial.map (Int.castRingHom ℂ) (f τ))}

variable {D}

def lamT (u : D.what₂.Word) (i : ℕ) : D.what₂.Tau → DomWeight (D.R.N i) :=
  fun τ => shW ((D.fm u).lam i τ) ((i * (D.R.t + 1) / 2 : ℕ) : ℤ)

theorem lamT_zero (u : D.what₂.Word) : lamT u 0 = (D.fm u).lam 0 := by
  funext τ
  simp [lamT, shW_zero]

set_option maxHeartbeats 1000000 in

structure ClsTied (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) where

  lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) (D.mem u).A.T D.R.f (badG D)

  y : (D.mem u).C.cls i → UPts (sigD D) (gramN D i hi) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
  y_bij : Function.Bijective (fun c => (Quotient.mk'' (y c) : Cls lev))

  y_lat : ∀ c (x : Fin (D.R.N i) → D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F),
    x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F))
      (clsCrd D u i hi c) ↔
    ((y c).1⁻¹).1 *ᵥ x ∈ latS (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)
      (tensInt (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (intOE D.host.E) (intAd D.host.F)) lev.Lb

  stabI : ∀ c, (D.mem u).C.stab i c →* UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)
  stabI_inj : ∀ c, Function.Injective (stabI c)
  stabI_range : ∀ c (γ : UJ (sigD D : D.host.E →+* D.host.E) (gramN D i hi)),
    γ ∈ (stabI c).range ↔
      bc (inclE (F := D.host.F) (FiniteAdeleRing (𝓞 D.host.F) D.host.F)) γ.1 ∈
        lev.U.map (MulAut.conj (y c).1).toMonoidHom

set_option maxHeartbeats 1000000 in

structure ValTied (u : D.what₂.Word) (eV : (D.mem u).A.vT ≃ PlT D u) (i : ℕ) (hi : i ≤ D.R.m) (K : ClsTied u i hi) where

  eY : (D.mem u).C.Y i ≃ Fr D i hi

  de : ∃ C : GL (Fin (D.R.N i)) D.host.E,
    cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
    (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
    ∀ τ z, (D.mem u).C.de i z τ = embT D τ C.1.det * ((eY z).1 τ).det

  Fi : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, φ ∈ (D.fm u).Fi i ↔
    (fun c z => φ c (eY.symm z)) ∈ FiC K.lev (embT D) (lamT u i) K.y

  ipV : ∀ c (o : Fr D i hi), o.IsON → ∀ P ∈ CSpan ((D.fm u).lam i), ∀ Q ∈ CSpan ((D.fm u).lam i),
    (D.fm u).ipV i c
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) P (eY z))
      (fun z => fnOf _ (shiftOf (lamT u i)) (fun τ => (o.1 τ)⁻¹) Q (eY z)) =
    nfAll ((D.fm u).lam i) Q P

  rat : ∀ φ : (D.mem u).C.cls i → (D.mem u).C.Y i → ℂ, (∃ x, (D.fm u).emb i x = φ) ↔
    φ ∈ (D.fm u).Fi i ∧ ∀ c, ∃ P ∈ RatSpan D ((D.fm u).lam i),
      ∀ z, φ c z = fnOf _ (shiftOf (lamT u i)) 1 P (eY z)

  lat : ∀ x : ((D.fm u).lat i).V, x ∈ ((D.fm u).lat i).L ↔
    ∀ (w : D.what₂.places.Pl) (c : (D.mem u).C.cls i) (B : GL (Fin (D.R.N i)) D.host.E),
      IsLocBasis (D.what₂.places.resChar w)
        (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) (clsCrd D u i hi c)) B →
      ∃ P ∈ IntSpan D w ((D.fm u).lam i),
        ∀ z, (D.fm u).emb i x c z =
          fnOf _ (shiftOf (lamT u i)) (atInf (embT D) (B⁻¹ : GL (Fin (D.R.N i)) D.host.E).1) P (eY z)

  dil : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ →
    (Quotient.mk'' (K.y ((D.fm u).dil i v a c)) : Cls K.lev) = Quotient.mk'' (K.y c * δ)

  dilT : ∀ v (a : ((D.mem u).A.Fv v)ˣ) (k : ℤ), (k : (D.mem u).A.Fv v) = a → ∀ c δ,
    IsDia K.lev (eV v).1 (eV v).2 k δ → ∀ g ∈ AdFun K.lev (embT D),
    (D.fm u).dilT i v a c (fun z => g (K.y ((D.fm u).dil i v a c)) (eY z)) = fun z => g (K.y c * δ) (eY z)

end Step

section AtT

variable {D : ColRec}

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

abbrev Ld (D : ColRec) (u : D.what₂.Word) (i : ℕ) (hi : i ≤ D.R.m) (c : (D.mem u).C.cls i) :
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

end AtT

end Formalism.L2.Col.CF

end
