import Mathlib
import Formalism.LocalToGlobal.Divisibility.HeckeCSDICommTrRep

open Module NumberField IsDedekindDomain Polynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.DIV

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.DivisionValues Formalism.L2.Indef

section Gen

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G] {Pl0 : Type}

namespace DefFam

variable {T T' J : Type} (F : DefFam K G Pl0 T J)

def comap (f : T' → T) (μ0' : T') : DefFam K G Pl0 T' J where
  v0 := F.v0
  μ0 := μ0'
  X := F.X
  R t := F.R (f t)
  L j t := F.L j (f t)
  tr := F.tr

theorem comap_ok [Fintype J] {s : ℕ} (h : F.Ok s) {f : T' → T} (hf : Function.Injective f) (μ0' : T') :
    (F.comap f μ0').Ok s where
  conj := h.conj
  tup_fin := @Finite.of_injective _ _ h.tup_fin f hf
  irr := h.irr
  what₂ t := h.what₂ (f t)
  lifts j t := h.lifts j (f t)

end DefFam

namespace DefFam3

variable {I0 Ty T T' J : Type} (F3 : DefFam3 K G Pl0 I0 Ty T J)

def comap (f : T' → T) (μ0' : T') : DefFam3 K G Pl0 I0 Ty T' J where
  F := F3.F.comap f μ0'
  RI t := F3.RI (f t)
  LI j t := F3.LI j (f t)
  trI := F3.trI

theorem comap_ok_of_injective [Fintype J] {s : ℕ} (h : F3.Ok3 s) {f : T' → T} (hf : Function.Injective f) (μ0' : T') :
    (F3.comap f μ0').Ok3 s where
  ok2 := F3.F.comap_ok h.ok2 hf μ0'
  what₂ t := h.what₂ (f t)
  lifts j t := h.lifts j (f t)

theorem comap_typesSep3_iff [Fintype J] {f : T' → T} {μ0' : T'} (hμ : f μ0' = F3.F.μ0) :
    (F3.comap f μ0').TypesSep3 ↔ F3.TypesSep3 := by
  unfold DefFam3.TypesSep3
  show (∀ p ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, p ≠ p' →
      ∀ j, (F3.LI j (f μ0')).DiffAt (F3.tr3 j p) (F3.tr3 j p')) ↔ _
  rw [hμ]

theorem comap_trISep_iff [Fintype J] {f : T' → T} {μ0' : T'} (hμ : f μ0' = F3.F.μ0) :
    (F3.comap f μ0').TrISep ↔ F3.TrISep := by
  unfold DefFam3.TrISep
  show (∀ j, ∀ p ∈ (F3.RI (f μ0')).ixFin3 F3.F.X, ∀ p' ∈ (F3.RI (f μ0')).ixFin3 F3.F.X,
      (∃ k : (F3.RI (f μ0')).PlI × Ty, p.2 ((F3.RI (f μ0')).plI k.1, k.2) ≠ p'.2 ((F3.RI (f μ0')).plI k.1, k.2)) →
        ∃ k : (F3.LI j (f μ0')).PlI × Ty,
          F3.trI j p.2 ((F3.LI j (f μ0')).plI k.1, k.2) ≠ F3.trI j p'.2 ((F3.LI j (f μ0')).plI k.1, k.2)) ↔ _
  rw [hμ]

end DefFam3

namespace FamIn

variable {T T' : Type} {m : ℕ} (A : FamIn K G Pl0 T m)

def comap (f : T' → T) (μ0' : T') : FamIn K G Pl0 T' m where
  v0 := A.v0
  μ0 := μ0'
  X := A.X
  r := A.r
  t := A.t
  q := A.q
  muVal j τ := A.muVal j (f τ)
  etaVal := A.etaVal
  ok τ := A.ok (f τ)
  MtildeCSD τ := A.MtildeCSD (f τ)
  leftGroupActionRight τ := A.leftGroupActionRight (f τ)
  heckeR τ := A.heckeR (f τ)
  MtCSD j τ := A.MtCSD j (f τ)
  leftGroupActionLift j τ := A.leftGroupActionLift j (f τ)
  heckeL j τ := A.heckeL j (f τ)

theorem fam_comap (f : T' → T) (μ0' : T') : (A.comap f μ0').fam = A.fam.comap f μ0' := rfl

end FamIn

namespace FamIn3

variable {I0 Ty T T' : Type} {m : ℕ} (A3 : FamIn3 K G Pl0 I0 Ty T m)

def comap (f : T' → T) (μ0' : T') : FamIn3 K G Pl0 I0 Ty T' m where
  A := A3.A.comap f μ0'
  okI τ := A3.okI (f τ)
  heckeRI τ := A3.heckeRI (f τ)
  heckeLI j τ := A3.heckeLI j (f τ)
  trI := A3.trI

theorem family_inputs_comap_eq (f : T' → T) (μ0' : T') : (A3.comap f μ0').fam3 = A3.fam3.comap f μ0' := rfl

end FamIn3

end Gen

section Inst

variable {X : Col.Fields} {Pr : Col.Primes X} {R : Ranks} (W : Col.Wts X Pr.Word R) (Ch : Col.Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (hX : X.Ok)

def TupF.incl {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF TU → TupF TC :=
  fun τ => ⟨τ.1, τ.2.imp id fun hm => h hm⟩

theorem TupF.incl_val {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) (τ : TupF TU) : (TupF.incl h τ).1 = τ.1 := rfl

theorem TupF.incl_injective {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : Function.Injective (TupF.incl h) := by
  intro a b hab
  have hv : (TupF.incl h a).1 = (TupF.incl h b).1 := congrArg Subtype.val hab
  exact Subtype.ext hv

theorem TupF.incl_mu0F {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC) : TupF.incl h (mu0F TU) = mu0F TC := rfl

variable (v0 : InfinitePlace X.K) {TU TC : Finset (Tup X.F X.E X.K S)} (h : TU ⊆ TC)
  (Xg : Finset (Col.G0 X.E Pr.vGs R.r → X.K)) (S0 : Set (HeightOneSpectrum (𝓞 X.E)))
  (xiVal : Tup X.F X.E X.K S → HeightOneSpectrum (𝓞 X.E) → X.Kˣ)
  (trIv : Fin R.m → (Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K) → Col.LevOffI ∅ Pr.vGs S0 × List ℕ → X.K)

theorem colIn_comap :
    colIn W Ch sel hX v0 TU Xg S0 xiVal = (colIn W Ch sel hX v0 TC Xg S0 xiVal).comap (TupF.incl h) (mu0F TU) := rfl

theorem colIn3_comap :
    colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).comap (TupF.incl h) (mu0F TU) := rfl

theorem colFam3_comap :
    colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv =
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).comap (TupF.incl h) (mu0F TU) := rfl

theorem column_family_base_tuple_comap :
    TupF.incl h (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.μ0 = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.μ0 := rfl

theorem column_family_place_character_comap :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.v0 = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.v0 ∧
      (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.X = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.X := by
  exact ⟨rfl, rfl⟩

theorem colFam3_R_comap (t : TupF TU) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.R t = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.R (TupF.incl h t) := rfl

theorem colFam3_L_comap (j : Fin R.m) (t : TupF TU) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.L j t =
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.L j (TupF.incl h t) := rfl

theorem colFam3_tr_comap :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.tr = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.tr := rfl

theorem colFam3_lvl_comap (P : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.lvl P ψ = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.lvl P ψ ∧
      (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).F.lvlA P ψ = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).F.lvlA P ψ := by
  exact ⟨rfl, rfl⟩

theorem colIn3_ok_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.ok t = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.ok (TupF.incl h t) := rfl

theorem colIn3_muVal_comap (j : Fin R.m) (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.muVal j t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.muVal j (TupF.incl h t) := rfl

theorem colIn3_forms_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtildeCSD t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.MtildeCSD (TupF.incl h t) ∧
      ∀ j, (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.MtCSD j t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.MtCSD j (TupF.incl h t) := by
  exact ⟨rfl, fun _ => rfl⟩

theorem colIn3_hecke_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.heckeR t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.heckeR (TupF.incl h t) ∧
      ∀ j, (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.heckeL j t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.heckeL j (TupF.incl h t) := by
  exact ⟨rfl, fun _ => rfl⟩

theorem colIn3_g0Act_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.leftGroupActionRight t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.leftGroupActionRight (TupF.incl h t) ∧
      ∀ j, (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).A.leftGroupActionLift j t =
        (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).A.leftGroupActionLift j (TupF.incl h t) := by
  exact ⟨rfl, fun _ => rfl⟩

theorem colIn3_okI_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).okI t = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).okI (TupF.incl h t) := rfl

theorem colIn3_heckeRI_comap (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeRI t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).heckeRI (TupF.incl h t) := rfl

theorem colIn3_heckeLI_comap (j : Fin R.m) (t : TupF TU) :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).heckeLI j t =
      (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).heckeLI j (TupF.incl h t) := rfl

theorem colIn3_trI_comap :
    (colIn3 W Ch sel hX v0 TU Xg S0 xiVal trIv).trI = (colIn3 W Ch sel hX v0 TC Xg S0 xiVal trIv).trI := rfl

theorem colFam3_RI_LI_comap (t : TupF TU) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).RI t = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).RI (TupF.incl h t) ∧
      ∀ j, (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).LI j t =
        (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).LI j (TupF.incl h t) := by
  exact ⟨rfl, fun _ => rfl⟩

include h in

theorem colHyp_restrict (hH : ColHyp W Ch sel v0 TC Xg S0) : ColHyp W Ch sel v0 TU Xg S0 where
  conj := hH.conj
  irr := hH.irr
  commR τ := hH.commR (TupF.incl h τ)
  splitR τ := hH.splitR (TupF.incl h τ)
  commL j τ := hH.commL j (TupF.incl h τ)
  splitL j τ := hH.splitL j (TupF.incl h τ)

include h in

theorem colHyp3_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0) : ColHyp3 W Ch sel v0 TU Xg S0 where
  base := colHyp_restrict W Ch sel v0 h Xg S0 hH.base
  commAllR τ := hH.commAllR (TupF.incl h τ)
  splitIR τ := hH.splitIR (TupF.incl h τ)
  commAllL j τ := hH.commAllL j (TupF.incl h τ)
  splitIL j τ := hH.splitIL j (TupF.incl h τ)

include h in

theorem column_family_ok_restrict_subtype {s : ℕ} (hO : (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).Ok3 s) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).Ok3 s := by
  exact DefFam3.comap_ok_of_injective _ hO (TupF.incl_injective h) (mu0F TU)

include h in

theorem colFam3_ok_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0) : (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).Ok3 1 := by
  exact column_family_ok_restrict_subtype (h := h) (hO := colFam3_ok (hH := hH) ..) ..

include h in

theorem colFam3_typesSep3_restrict_iff :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 ↔ (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TypesSep3 := by
  rw [colFam3_comap W Ch sel hX v0 h Xg S0 xiVal trIv]
  exact DefFam3.comap_typesSep3_iff (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv) (TupF.incl_mu0F h)

include h in

theorem colFam3_trISep_restrict_iff :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TrISep ↔ (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TrISep := by
  rw [colFam3_comap W Ch sel hX v0 h Xg S0 xiVal trIv]
  exact DefFam3.comap_trISep_iff (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv) (TupF.incl_mu0F h)

include h in

theorem colFam3_typesSep_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0)
    (hI : (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TrISep) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).TypesSep3 := by
  exact (colFam3_typesSep3_restrict_iff W Ch sel hX v0 h Xg S0 xiVal trIv).mpr
    (colFam3_typesSep' W Ch sel hX v0 TC Xg S0 xiVal trIv hH hI)

theorem colFam_comap :
    colFam W Ch sel hX v0 TU Xg S0 xiVal = (colFam W Ch sel hX v0 TC Xg S0 xiVal).comap (TupF.incl h) (mu0F TU) := rfl

theorem colFam3_ix_comap :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).base3.Ix = (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).base3.Ix := rfl

def colSubRes3 (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3) :
    DefSub (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).amb3 :=
  ⟨fun t => Zs.Z (TupF.incl h t), fun j t => Zs.Zl j (TupF.incl h t)⟩

variable (Zs : DefSub (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).amb3)

theorem colSubRes3_stable (hst : Zs.Stable) : (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs).Stable := by
  unfold DefSub.Stable at hst ⊢
  exact ⟨fun t i => hst.1 (TupF.incl h t) i, fun j t i => hst.2 j (TupF.incl h t) i⟩

theorem colSubRes3_inBlock (hin : Zs.InBlock) : (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs).InBlock := by
  unfold DefSub.InBlock at hin ⊢
  exact ⟨fun t => hin.1 (TupF.incl h t), fun j t => hin.2 j (TupF.incl h t)⟩

theorem colFam3_sameTypes3_restrict_iff (P : Subgroup (Col.G0 X.E Pr.vGs R.r)) (ψ : P →* X.Kˣ) :
    (colFam3 W Ch sel hX v0 TU Xg S0 xiVal trIv).SameTypes3 P ψ (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs) ↔
      (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).SameTypes3 P ψ Zs := by
  exact Iff.rfl

theorem colSide3_rows_comap (P : Col.LevFam X.E X.K R.r Pr.vGs) (t : TupF TU) :
    (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).nV t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).nV (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).HV t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).HV (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).Mt t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).Mt (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).dQ t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).dQ (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).Pq t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).Pq (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).XQ t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).XQ (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).Qp t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).Qp (TupF.incl h t) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem colSide3_lifts_comap (P : Col.LevFam X.E X.K R.r Pr.vGs) (j : Fin R.m) (t : TupF TU) :
    (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).dZ j t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).dZ j (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).HT j t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).HT j (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).XT j t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).XT j (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).Tl j t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).Tl j (TupF.incl h t) ∧
      (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).Zp j t =
        (colSide3 W Ch sel hX v0 TC Xg S0 xiVal trIv P Zs).Zp j (TupF.incl h t) := by
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem colSide3_WF_restrict (hH : ColHyp3 W Ch sel v0 TC Xg S0)
    (hI : (colFam3 W Ch sel hX v0 TC Xg S0 xiVal trIv).TrISep) (P : Col.LevFam X.E X.K R.r Pr.vGs)
    (hst : Zs.Stable) (hin : Zs.InBlock) :
    (colSide3 W Ch sel hX v0 TU Xg S0 xiVal trIv P (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)).WF := by
  exact colSide3_WF W Ch sel hX v0 TU Xg S0 xiVal trIv (colHyp3_restrict (h := h) (hH := hH) ..)
    ((colFam3_trISep_restrict_iff W Ch sel hX v0 h Xg S0 xiVal trIv).mpr hI) P
    (colSubRes3 W Ch sel hX v0 h Xg S0 xiVal trIv Zs)
    (colSubRes3_stable (h := h) (Zs := Zs) (hst := hst) ..)
    (colSubRes3_inBlock (h := h) (Zs := Zs) (hin := hin) ..)

end Inst

end Formalism.L2.DIV
