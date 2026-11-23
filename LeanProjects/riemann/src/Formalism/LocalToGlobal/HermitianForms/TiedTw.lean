import Formalism.LocalToGlobal.HermitianForms.TiedTwGen
import Formalism.LocalToGlobal.HermitianColumns.TiedQCJoint
import Formalism.LocalRingCardinality.DataKerP

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem lam_tw (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) (j : ℕ) (hj : j ≤ D.R.m) :
    (Tw.fm u μ).lam j = (D.fm u).lam j := by
  funext τ
  have h : ((Tw.fm u μ).lam j τ).w = ((D.fm u).lam j τ).w := by
    funext i
    have h1 := (Tw.fm u μ).lam_eq j hj τ i
    have h2 := (D.fm u).lam_eq j hj τ i
    exact_mod_cast h1.trans h2.symm
  cases h1 : (Tw.fm u μ).lam j τ
  cases h2 : (D.fm u).lam j τ
  simp only [h1, h2] at h
  subst h
  rfl

structure TwAtT (Tw : TwForms D) (u : D.what₂.Word) (μ : D.what₂.Tup) where

  eVT : (Tw.A u μ).vT ≃ (D.mem u).A.vT

  eFv : ∀ v, (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)
  psiT : ∀ v x, (Tw.A u μ).psiT v x = (D.mem u).A.psiT (eVT v) (eFv v x)
  rhoT : ∀ v a φ, (Tw.A u μ).rhoT v a (D.e0Tw u μ φ) =
    D.e0Tw u μ ((D.mem u).A.rhoT (eVT v) (Units.map ((eFv v : (Tw.A u μ).Fv v ≃+* (D.mem u).A.Fv (eVT v)) : (Tw.A u μ).Fv v →* (D.mem u).A.Fv (eVT v)) a) φ)
  Mu0 : (Tw.A u μ).Mu0 = (D.mem u).A.Mu0.map (D.e0Tw u μ : _ →ₗ[ℂ] _)
  duStar : (Tw.A u μ).duStar = (D.mem u).A.duStar
  Dstar : (Tw.A u μ).Dstar = (D.mem u).A.Dstar
  GamP : (Tw.A u μ).GamP = (D.mem u).A.GamP

  tauOf : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → ∀ v, (Tw.fm u μ).tauOf w v = (D.fm u).tauOf w (eVT v)
  seenP : ∀ w, D.what₂.places.resChar w = (D.mem u).A.T → (Tw.fm u μ).seenP w = (D.fm u).seenP w

def TwAtT.eV {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) :
    (Tw.A u μ).vT ≃ PlT D u := a.eVT.trans At.eV

def TwAtT.res {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} (a : TwAtT Tw u μ) (At : AtTTied u) (v : (Tw.A u μ).vT) :
    𝓞 D.host.E →+* (Tw.A u μ).Fv v := ((a.eFv v).symm : _ →+* _).comp (At.res (a.eVT v))

variable {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}

def okQ (D : D7) (Q : Finset (HeightOneSpectrum (𝓞 D.host.F))) (w : D.what₂.places.Pl) : Prop :=
  ∀ v ∈ Q, ((D.what₂.places.resChar w : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal

def twY (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    (D.chTw u μ).Y i ≃ Fr D i hi :=
  (T.eY u μ i hi).symm.trans ((F u).val i hi).eY

theorem twY_de (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) (u : D.what₂.Word) (μ : D.what₂.Tup) (i : ℕ) (hi : i ≤ D.R.m) :
    ∃ C : GL (Fin (D.R.N i)) D.host.E,
      cT (sigD D : D.host.E →+* D.host.E) C.1 * C.1 = gramN D i hi ∧
      (∀ x : Fin (D.R.N i) → D.host.E, x ∈ selfDualLatticeCoords D i hi ↔ ∀ a, (C.1 *ᵥ x) a ∈ (algebraMap (𝓞 D.host.E) D.host.E).range) ∧
      ∀ τ z, (D.chTw u μ).de i z τ = embT D τ C.1.det * ((twY T F u μ i hi z).1 τ).det := by
  obtain ⟨C, h1, h2, h3⟩ := ((F u).val i hi).de
  refine ⟨C, h1, h2, fun τ z => ?_⟩
  have := T.de_eq u μ i hi ((T.eY u μ i hi).symm z) τ
  rw [Equiv.apply_symm_apply] at this
  rw [this, h3]
  rfl

set_option maxHeartbeats 4000000 in

structure TwFormsTied (D : D7) (Tw : TwForms D) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (T : Formalism.L2.Herm.TwChTied D inQ) (F : ∀ u, FormsTied D u) where

  atT : ∀ u μ, TwAtT Tw u μ

  ch : ∀ (u : D.what₂.Word) (μ : D.what₂.Tup), μ ≠ D.what₂.mu0 → ∀ (i : ℕ), 1 ≤ i → ∀ (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    LevelChart D (D.mem u).A.T (badQ D (T.Q μ)) i hm
      (fun c : {c // T.chOf u μ i c = β} => (D.chTw u μ).stab i c.1) (fun c => latCrd D i hm (T.lat u μ i c.1))

  car : ∀ u μ (hμ : μ ≠ D.what₂.mu0) i (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i),
    SameCar (rankN D i hm) (T.lev u μ i h1 hm β).Lb (ch u μ hμ i h1 hm β).lev.Lb
      (T.lev u μ i h1 hm β).Uloc (ch u μ hμ i h1 hm β).lev.Uloc (T.lev u μ i h1 hm β).U (ch u μ hμ i h1 hm β).lev.U
      (fun c => ((T.cls u μ hμ i h1 hm β).y c).1) (fun c => ((ch u μ hμ i h1 hm β).y c).1)
      (fun c s => ((T.cls u μ hμ i h1 hm β).stabI c s).1) (fun c s => ((ch u μ hμ i h1 hm β).stabI c s).1)

  chi_fin : ∀ u μ hμ i h1 hm β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (ch u μ hμ i h1 hm β).lev.chi κ ^ n = 1

  chi_off : ∀ u μ hμ i h1 hm β (κ : (ch u μ hμ i h1 hm β).lev.U) (κ' : ((F u).cls i hm).lev.U), κ.1 = κ'.1 →
    (∀ v ∈ T.Q μ, bc (prV (E := D.host.E) v) κ.1 = 1) → (ch u μ hμ i h1 hm β).lev.chi κ = ((F u).cls i hm).lev.chi κ'

  chiJ : ∀ u μ (h : 1 ≤ D.R.m - 1), (T.levJ u μ h).U →* ℂˣ
  chiJ_eq : ∀ u μ hμ (h : 1 ≤ D.R.m - 1) β (κ : (T.levJ u μ h).U)
    (κ' : (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.U), κ'.1 = reGL (rankN D (D.R.m - 1) (Nat.sub_le _ _)) _ κ.1 →
    (ch u μ hμ (D.R.m - 1) h (Nat.sub_le _ _) β).lev.chi κ' = chiJ u μ h κ

  val : ∀ u μ hμ i h1 hm, ValuationCompatibleChart (Tw.fm u μ) (twY T F u μ i hm) (okQ D (T.Q μ)) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  dil : ∀ u μ hμ i h1 hm, DilationCompatibleChart (Tw.fm u μ) (twY T F u μ i hm) ((atT u μ).eV (F u).atT) (T.chOf u μ i)
    (lat := fun c => latCrd D i hm (T.lat u μ i c)) (ch u μ hμ i h1 hm)

  ipV : ∀ u μ i hi, IpVTieG (Tw.fm u μ) (twY T F u μ i hi)

  norm : ∀ u μ i hi, NormTieG (Tw.fm u μ) (twY T F u μ i hi)

  twisted_e0_at_mu0_eq_eMu0 : ∀ u x, Tw.e0 u D.what₂.mu0 x = Tw.eMu0 u 0 (Nat.zero_le _) x

theorem eMu0_emb_apply (Tw : TwForms D) (u : D.what₂.Word) (j : ℕ) (hj : j ≤ D.R.m) (x : ((D.fm u).lat j).V)
    (c : (D.mem u).C.cls j) (y : (D.mem u).C.Y j) :
    (Tw.fm u D.what₂.mu0).emb j (Tw.eMu0 u j hj x) (Formalism.L2.Herm.clsCast D u j c) (Formalism.L2.Herm.yCast D u j y) = (D.fm u).emb j x c y :=
  Formalism.L2.Herm.heq_apply (D.memberColumns_twistedChain_base u) j _ _ (Tw.eMu0_emb u j hj x) c y

end Formalism.L2.Forms

end
