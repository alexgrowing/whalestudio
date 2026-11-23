import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WdOfMono0L

noncomputable section

namespace GlobalTheory.HeightCounting

open Formalism.BasicNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Formalism.L2.Host

section
variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}

def ndLab (N : NData R H what₂) (lab : ∀ k, what₂.FT → N.PlG k → Polynomial (ZMod (H.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = R.r) : NData R H what₂ :=
  { N with lab := lab, lab_monic := h }

structure CGK {N : NData R H what₂} (A : NAut N) where
  CG : ℕ → Type
  csd : ∀ {a}, CG a → Prop
  ralg : ∀ {a}, CG a → Prop
  locG : ∀ {a}, CG a → ∀ w, A.LP w
  locG_dim : ∀ {a} (π : CG a) w, A.lpDim (locG π w) = a
  locG_unr_ae : ∀ {a} (π : CG a), ∀ᶠ w in Filter.cofinite, A.unr (locG π w)
  tw : ∀ {a}, CG a → CG 1 → CG a
  locG_tw : ∀ {a} (π : CG a) (χ : CG 1) w, locG (tw π χ) w = A.lpChar (locG π w) (locG χ w)
  infG : ∀ {a}, CG a → (H.E →+* ℂ) → Multiset ℂ
  infG_card : ∀ {a} (π : CG a) τ, Multiset.card (infG π τ) = a
  ralg_def : ∀ {a} (π : CG a), ralg π ↔ ∀ τ, (infG π τ).Nodup ∧
    ∀ z ∈ infG π τ, ∃ n : ℤ, z = (n : ℂ) + ((a : ℂ) - 1) / 2
  infG_tw : ∀ {a} (π : CG a) (χ : CG 1) τ (s : ℂ), infG χ τ = {s} → infG (tw π χ) τ = (infG π τ).map (· + s)
  csd_tw : ∀ {a} (π : CG a) (χ : CG 1), csd χ → csd π → csd (tw π χ)
  csd_unr : ∀ {a} (π : CG a) w w', csd π → IsConjPl H w w' → A.unr (locG π w) →
    A.unr (locG π w') ∧ A.frobEig (locG π w') = (A.frobEig (locG π w)).map (·⁻¹)
  etaT : CG 1
  etaTinv : CG 1
  etaT_unr : ∀ w, A.unr (locG etaT w)
  etaT_inert : ∀ w, ¬ IsSplitPl H w → A.frobEig (locG etaT w) = {-1}
  etaTinv_def : ∀ w, A.unr (locG etaTinv w) ∧ A.frobEig (locG etaTinv w) = (A.frobEig (locG etaT w)).map (·⁻¹)
  etaT_split : ∀ w w', IsSplitPl H w → IsConjPl H w w' → ∀ a b : ℂ, A.frobEig (locG etaT w) = {a} →
    A.frobEig (locG etaT w') = {b} → a * b = 1

def CGK.naut {N : NData R H what₂} {A : NAut N} (K : CGK A) (hE : IsEmpty N.Loc) : NAut N :=
  { A with
    CG := K.CG
    csd := K.csd
    ralg := K.ralg
    locG := K.locG
    locG_dim := K.locG_dim
    locG_unr_ae := K.locG_unr_ae
    tw := K.tw
    locG_tw := K.locG_tw
    infG := K.infG
    infG_card := K.infG_card
    ralg_def := K.ralg_def
    infG_tw := K.infG_tw
    csd_tw := K.csd_tw
    csd_unr := K.csd_unr
    etaT := K.etaT
    etaTinv := K.etaTinv
    etaT_unr := K.etaT_unr
    etaT_inert := K.etaT_inert
    etaTinv_def := K.etaTinv_def
    etaT_split := K.etaT_split
    muC := fun i => hE.elim i
    muC_csd := fun i => hE.elim i
    jumpsInf := fun i => hE.elim i
    jumpsInf_def := fun i => hE.elim i
    chi_mu := fun i => hE.elim i }

end

structure RowWD (D : D7) where
  par : D.what₂.FT → ∀ w : PlE D.host, GlobalTheory.WeilDeligne.WD (E := D.host.E) (A := D.nd.plOm.1 w) (w := w) (D.nd.plOm.2 w)
  sat : D.what₂.FT → PlE D.host → Multiset ℂ
  dim : ∀ σ w, (par σ w).lpDim = D.R.r
  tame : ∀ σ k v, (par σ (D.naut.plGw k v)).tame

set_option maxHeartbeats 2000000 in

def setAut (D : D7) (hE : IsEmpty D.nd.Loc) (lab : ∀ k, D.what₂.FT → D.nd.PlG k → Polynomial (ZMod (D.host.g k)))
    (h : ∀ k σ v, (lab k σ v).Monic ∧ (lab k σ v).natDegree = D.R.r) (A : NAut (ndLab D.nd lab h)) (C : NBC A)
    (tg_mem : ∀ k v, D.ntypes.tg k v ∈ Ine (F := D.host.E) (D.nd.plOm.1 (A.plGw k v)))
    (tg_gen : ∀ k v, TameGenAt (D.nd.plOm.1 (A.plGw k v)) (D.ntypes.tg k v))
    (hl : ∀ k v (L : A.LP (A.plGw k v)), (A.items₂ k (A.plGw k v) L).natDegree = A.lpDim L →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      A.inePol L (D.ntypes.tg k v) =
        ((Formalism.CyclotomicNorms.rootsBar (A.items₂ k (A.plGw k v) L)).map fun x => X - Polynomial.C (D.ntypes.teichC k x)).prod) : D7 :=
  { D with
    nd := ndLab D.nd lab h, ntw := { D.ntw with }, naut := A, nbc := C, nexp := { D.nexp with }, nth := { D.nth with }
    ntypes := { D.ntypes with
      tg_mem := tg_mem, tg_gen := tg_gen, heckeLoc_gamma_places := fun i => hE.elim i, inertiaCharpoly_type := hl, chiT_tg := fun i => hE.elim i
      Par := PEmpty, labPar := fun _ a => a.elim, labPar_monic := fun _ a => a.elim, locPar := fun a => a.elim
      locPar_dim := fun a => a.elim, labPar_def := fun _ a => a.elim, MtPar := fun _ _ a => a.elim
      AmbPar := fun _ a => a.elim }
    nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq, ntwbr := D.ntwbr, ntwbr_ind := D.ntwbr_ind
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i
    etaJ_tie := D.etaJ_tie }

set_option maxHeartbeats 2000000 in

def setCG (D : D7) (hE : IsEmpty D.nd.Loc) (K : CGK D.naut) : D7 :=
  { D with
    naut := K.naut hE, nbc := { D.nbc with }, ntypes := { D.ntypes with }, nStage_trivialCharacter_compat := D.nStage_trivialCharacter_compat, nStage_trivialCharacter_coeff_eq := D.nStage_trivialCharacter_coeff_eq
    nbr := fun i => hE.elim i, nbr_ind := fun i => hE.elim i, self_good := fun i => hE.elim i
    loc_tie := fun i => hE.elim i, bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i
    mtpar_tie := fun i => hE.elim i, Z_tie := fun i => hE.elim i, Zgood_tie := fun i => hE.elim i }

def setBC (D : D7) (C : NBC D.naut) : D7 := { D with nbc := C }

def setTy (D : D7) (hE : IsEmpty D.nd.Loc) (X : NTypes D.naut) (h1 : X.IdempotentMatchesAction)
    (h0 : ∀ g : G0g D.nd, D.what₂.embLL ((D.nexp.eLL0 g : ↥D.LL0) : D.what₂.LL) = X.e0.coeff g) : D7 :=
  { D with
    ntypes := X, nStage_trivialCharacter_compat := h1, nStage_trivialCharacter_coeff_eq := h0
    bc_tie := fun i => hE.elim i, rbar_tie := fun i => hE.elim i, mtpar_tie := fun i => hE.elim i }

def BlocksUnique (D : D7) : Prop :=
  ∀ Sig Sig' : List (Part D.naut.CG), (∀ p ∈ Sig ++ Sig', 1 ≤ p.a ∧ 1 ≤ p.d ∧ D.naut.csd p.π ∧ ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2) →
    rankIso D.nd D.naut Sig = D.R.r → rankIso D.nd D.naut Sig' = D.R.r →
    (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = isoLoc D.nd D.naut Sig' w) →
    Multiset.ofList (Sig.map fun p => (p.a, p.d)) = Multiset.ofList (Sig'.map fun p => (p.a, p.d))

def IsRepOf (D : D7) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {a : ℕ} (π : D.naut.CG a) (s : ℝ)
    (ρ : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) : Prop :=
  Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) ∧ IsSSRep ρ ∧
  ∀ᶠ w in Filter.cofinite, ∀ (B : ValuationSubring D.nd.Om) (σ : G D.host.E D.nd.Om),
    IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ →
    ((ρ σ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).charpoly.map ι.toRingHom =
      galPol D.naut (D.naut.lpTw (D.naut.locG π w) s)

def GalEx (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (a : ℕ), 1 ≤ a → ∀ π : D.naut.CG a, D.naut.csd π → D.naut.ralg π →
    ∃ ρ, IsRepOf D l ι π ((1 - (a : ℝ)) / 2) ρ

def RowCusp (D : D7) (Rw : RowSide D) : Prop :=
  ∀ j, 1 ≤ j → j ≤ D.R.m → ∀ σ, D.what₂.isot j σ ≠ ⊥ → D.nd.goodRow σ → ∃ π : D.naut.CG D.R.r,
    D.naut.csd π ∧ D.naut.ralg π ∧ (∀ w, IsSplitPl D.host w → D.naut.locG π w = Rw.locR σ w) ∧
    ∀ᶠ w in Filter.cofinite, ∃ p : Polynomial ↥D.LL0, p.map (embLL0 D) =
      galPol D.naut (D.naut.lpTw (D.naut.locG (D.naut.tw π D.naut.etaTinv) w) ((1 - (D.R.nV : ℝ)) / 2))

end GlobalTheory.HeightCounting

end
