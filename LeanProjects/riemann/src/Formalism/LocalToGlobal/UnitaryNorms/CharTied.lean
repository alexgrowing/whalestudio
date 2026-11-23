import Formalism.LocalRingCardinality.DataTheta
import Formalism.LocalToGlobal.UnitaryNorms.CharUniq

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR

namespace Formalism.L2.Host

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def embTau (D : D7) (τ : D.what₂.Tau) : D.host.E →+* ℂ := D.host.emb ((D.eTau τ : D.R.Psi) : D.R.GG)

def eExp (D : D7) (j : Fin D.R.m) (g : D.R.Psi) : ℚ := (D.hc (D.eTau.symm g)).e j

structure CharFrame (D : D7) where

  P : PiBar D.host

  W : Omg D.host

  mu0 : Fin D.R.m → HChar D.host.E
  eta : HChar D.host.E
  chiPsi : HChar D.host.E
  del : HChar D.host.E
  del' : HChar D.host.E
  isMu0 : ∀ j, IsMu0 P W (eExp D j) j.1 (mu0 j)
  isEta : IsEtaT D.host eta
  isChi : IsChiPsi D.host chiPsi
  isDel : IsDelta D.host.pde del
  isDel' : IsDelta D.host.pde' del'

def embLL0 (D : D7) : ↥D.LL0 →+* ℂ := D.what₂.embLL.comp D.LL0.val.toRingHom

structure ValLL0 (D : D7) (C : CharFrame D) : Prop where
  mu0 : ∀ j, (C.mu0 j).ValuesIn 0 (embLL0 D)
  eta : C.eta.ValuesIn (1 / 2) (embLL0 D)
  chiPsi : C.chiPsi.ValuesIn 0 (embLL0 D)
  del : C.del.ValuesIn 0 (embLL0 D)
  del' : C.del'.ValuesIn 0 (embLL0 D)

structure ValLL (D : D7) (C : CharFrame D) : Prop where
  mu0 : ∀ j, (C.mu0 j).ValuesIn 0 D.what₂.embLL
  eta : C.eta.ValuesIn (1 / 2) D.what₂.embLL
  chiPsi : C.chiPsi.ValuesIn 0 D.what₂.embLL
  del : C.del.ValuesIn 0 D.what₂.embLL
  del' : C.del'.ValuesIn 0 D.what₂.embLL

theorem HChar.ValuesIn.ofLL0 {D : D7} {χ : HChar D.host.E} {s : ℝ} (h : χ.ValuesIn s (embLL0 D)) :
    χ.ValuesIn s D.what₂.embLL := by
  intro v hv
  obtain ⟨y, hy⟩ := h v hv
  exact ⟨D.LL0.val y, hy⟩

theorem ValLL0.toLL {D : D7} {C : CharFrame D} (h : ValLL0 D C) : ValLL D C := by
  exact ⟨fun j => HChar.ValuesIn.ofLL0 (h.mu0 j), HChar.ValuesIn.ofLL0 h.eta,
    HChar.ValuesIn.ofLL0 h.chiPsi, HChar.ValuesIn.ofLL0 h.del, HChar.ValuesIn.ofLL0 h.del'⟩

def CharFrame.delAt {D : D7} (C : CharFrame D) (l : ℕ) : HChar D.host.E := if l = D.host.pde then C.del' else C.del

structure TupTied (D : D7) (C : CharFrame D) (nch : NChoice D) where

  xi : D.what₂.Tup → HChar D.host.E
  xi_inj : Function.Injective xi
  xi_fin : ∀ μ, ∃ n : ℕ, 0 < n ∧ (xi μ).OrderDvd n
  xi_triv : ∀ μ, (xi μ).TrivOn D.host.F
  xi_tame : ∀ μ v, (xi μ).TameAt v

  psi : D.what₂.places.Pl → HChar D.host.E

  trueColumnChoices_heckeChar_reference_eq_one : xi D.what₂.mu0 = 1

  xi_star : xi D.what₂.muStar = C.del
  xi_star' : xi D.what₂.muStar' = C.del'

  xi_tw : ∀ w, xi (D.what₂.muTw w) = C.delAt (D.what₂.places.resChar w) * psi w

  psi_is : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → IsPsi (D.what₂.places.resChar w) (nch.Q w) (psi w)

  psi_un : ∀ w, D.what₂.muAt w = D.what₂.mu0 → psi w = 1

theorem TupTied.psi_gen {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (w : D.what₂.places.Pl) :
    ∃ Q, IsPsi (D.what₂.places.resChar w) Q (Tp.psi w) := by
  by_cases hw : D.what₂.muAt w = D.what₂.mu0
  · rw [Tp.psi_un w hw]
    exact ⟨∅, isPsi_one _⟩
  · exact ⟨_, Tp.psi_is w hw⟩

def TupTied.tup {D : D7} {C : CharFrame D} {nch : NChoice D} (Tp : TupTied D C nch) (μ : D.what₂.Tup) (j : Fin D.R.m) :
    HChar D.host.E := C.mu0 j * Tp.xi μ

def IsFinIdele {L : Type} [Field L] [NumberField L] (a : Ideles L) : Prop :=
  ∀ w : InfinitePlace L, (a : AdeleRing (𝓞 L) L).1 w = 1

structure DtTied (D : D7) (C : CharFrame D) where
  eDt : Ideles D.host.E →* D.Dt
  surj : Function.Surjective eDt

  ker_open : IsOpen ((eDt.ker : Subgroup (Ideles D.host.E)) : Set (Ideles D.host.E))
  inf : ∀ w y, eDt (infIdele D.host.E w y) = 1

  onF : ∀ (v : HeightOneSpectrum (𝓞 D.host.F)) (k : D.host.Fˣ),
    eDt (∏ Q ∈ aboveF (L := D.host.E) D.host.F v, localIdele D.host.E Q (atFin Q (upF D.host.F k))) = 1

  ker_le : ∀ a, eDt a = 1 → ∀ w w', IsConjPl D.host w w' →
    Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w) = Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 w')

  rat : letI := D.host.cmStar; ∀ (k : D.host.Eˣ) (z : unitary D.host.E), (z : D.host.E) * D.host.conj (k : D.host.E) = k →
    eDt (diagUnits D.host.E k) = D.e1Dt z

  UO_eq : ∀ x, x ∈ D.UO ↔ ∃ a : Ideles D.host.E,
    (∀ v, Valued.v ((a : AdeleRing (𝓞 D.host.E) D.host.E).2 v) = 1) ∧ eDt a = x

  muTil_eq : ∀ (j : Fin D.R.m) (a : Ideles D.host.E), IsFinIdele a → D.muTil (j.1 + 1) (eDt a) = (C.mu0 j).1 a

  chiD_eq : ∀ a : Ideles D.host.E, IsFinIdele a → D.chiD (eDt a) = C.chiPsi.1 a

def IsCSD {R : Ranks} (H : Formalism.BasicNotions.Host R) (χ : HChar H.E) : Prop :=
  (∀ w w', IsConjPl H w w' → ∀ k : H.Eˣ, χ.locK w' (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.locK w k)⁻¹) ∧
    ∀ k : H.Eˣ, χ.inf (Units.map (MonoidHomClass.toMonoidHom H.conj) k) = (χ.inf k)⁻¹

structure NCharTied (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) where
  e1 : D.naut.CG 1 ≃ {χ : HChar D.host.E // χ.IsUnitary}
  unr_iff : ∀ π w, D.naut.unr (D.naut.locG π w) ↔ (e1 π).1.UnrAt w

  frob : ∀ π w, (e1 π).1.UnrAt w → D.naut.frobEig (D.naut.locG π w) = {(((e1 π).1.val w)⁻¹ : ℂˣ).1}
  tw : ∀ π χ : D.naut.CG 1, (e1 (D.naut.tw π χ)).1 = (e1 π).1 * (e1 χ).1

  infG : ∀ π (a : D.R.Psi → ℚ), (e1 π).1.HasInfQ (embPsi D.host) a → ∀ g,
    D.naut.infG π (embPsi D.host g) = {(a g : ℂ)} ∧
      D.naut.infG π ((starRingEnd ℂ).comp (embPsi D.host g)) = {-(a g : ℂ)}
  csd : ∀ π : D.naut.CG 1, D.naut.csd π ↔ IsCSD D.host (e1 π).1

  muC : ∀ i (j : Fin D.R.m), j.1 + 1 = D.nd.j i → (e1 (D.naut.muC i)).1 = Tp.tup (D.nd.mu i) j
  etaT : (e1 D.naut.etaT).1 = C.eta
  etaTinv : (e1 D.naut.etaTinv).1 = C.eta⁻¹

  plGw : ∀ k v, C.P.Div k (D.naut.plGw k v)

structure ThetaChrTied (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch) (X : ThetaX D) where
  eChr : X.Chr →* HChar D.host.E
  inj : Function.Injective eChr
  range : ∀ χ : HChar D.host.E, (∃ c, eChr c = χ) ↔ χ.IsUnitary ∧ ∃ a : D.what₂.Tau → ℚ, χ.HasInfQ (embTau D) a
  infTy : ∀ c, (eChr c).HasInfQ (embTau D) (X.infTy c)
  chrOf : ∀ μ (j : Fin D.R.m), eChr (X.chrOf μ (j.1 + 1)) = Tp.tup μ j
  etaT : eChr X.etaT = C.eta

theorem ThetaChrTied.carY {D : D7} {C : CharFrame D} {nch : NChoice D} {Tp : TupTied D C nch} {X : ThetaX D}
    (T : ThetaChrTied D C nch Tp X) (μ : D.what₂.Tup) (j : Fin D.R.m) (i : ℕ) :
    T.eChr (X.carY μ (j.1 + 1) i) = if Even i then Tp.tup μ j * C.eta⁻¹ else Tp.tup μ j := by
  unfold ThetaX.carY
  split_ifs with hi
  · rw [map_mul, map_inv, T.chrOf, T.etaT]
  · rw [T.chrOf]

end Formalism.L2.Host
