import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalToGlobal.Divisibility.DivisionHeightBoundStatement
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ColDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.UnitaryNorms.CharTransport

open Module NumberField IsDedekindDomain
open scoped Matrix InnerProductSpace

noncomputable section

namespace Formalism.IndefR.Cx

open Formalism.DivisionValues Formalism.L2.Indef Formalism.L2.DIV Formalism.BasicNotions Formalism.L2.Col Formalism.IndefR.Links

section Face

variable {Fl : Fields} {Pr : Primes Fl} {Rk : Ranks} (W : Wts Fl Pr.Word Rk) (Ch : Chars Fl Pr Rk.m)
  (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ}
  {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {m : ℕ}

def faceCol (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)) (Am : Formalism.L2.Ker.Amb Fl)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P) :
    ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs) := fun Zs =>
  colFace hX (A.side P1 ψ1 Zs) Xg mu cst L hL hP Mem wd b hY
    (fun t x => Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x)) hF (ev Zs)

def faceColT (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x))
    {D : D7} (sm : Formalism.L2.Ker.Seam D Fl) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Formalism.L2.Ker.Base D cc δ)
    (χ : Formalism.MainNotions.TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) (Formalism.L2.Ker.ambOf sm B χ cD) (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P) :
    ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs) :=
  faceCol W Ch sel hX A P1 ψ1 Xg mu cst L hL hP Mem wd b hY (Formalism.L2.Ker.ambOf sm B χ cD) hK hF ev

theorem faceCol_Pt (hX : Fl.Ok) (A : FamIn Fl.K G Pl0 T m) (P1 : Subgroup G) (ψ1 : P1 →* Fl.Kˣ)
    {P : LevFam Fl.E Fl.K Rk.r Pr.vGs} (Xg : Finset (G0 Fl.E Pr.vGs Rk.r → Fl.K)) {m2 : ℕ} {Gc : ChGlob Fl Rk.m}
    (mu : A.fam.base.Tup → Tup Fl.F Fl.E Fl.K Sg) (cst : ∀ t, LocCst Fl (rowSG Pr sel (mu t)))
    (L : ∀ t, ChIdx Fl Pr Rk (QE sel (mu t : Chr Fl.F Fl.E Fl.K))) (hL : ∀ t, (L t).Ok Ch sel (mu t) (cst t) Gc m2)
    (hP : ∀ t, (mtildeGSD W Ch sel (mu t) P).Ok) (Mem : Type) (wd : Mem → Pr.Word) (b : ∀ t, Mem → (L t).β (m2 + 1))
    (hY : ∀ t x, YbHyp (R := Rk) sel (mu t) (cst t) (L t) (wd x) m2 (b t x)) (Am : Formalism.L2.Ker.Amb Fl)
    (hK : ∀ t x, Formalism.L2.Ker.KerEquivC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P)
    (hF : ∀ t x j, (chF W sel (mu t) (L t) (wd x) j).Ok)
    (ev : ∀ (Zs : DefSub A.fam.amb) t, (Fin ((A.side P1 ψ1 Zs).nV t) → Fl.K) →ₗ[Fl.K] V0X W Ch sel (mu t) Xg P)
    (Zs : DefSub A.fam.amb) (x : Mem) (t : A.fam.base.Tup) :
    (faceCol W Ch sel hX A P1 ψ1 Xg mu cst L hL hP Mem wd b hY Am hK hF ev Zs).Pt x t =
      colPer hX (hP t) Xg (Formalism.L2.Ker.chKerC W Ch sel (mu t) (cst t) (L t) Am (wd x) m2 (b t x) (hY t x) P (hK t x))
        (hF t x) (hL t) (ev Zs t) := rfl

end Face

section Sp

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

structure PerW (hK : X.LevelSubgroupCharacter) (u : D.what₂.Word) where

  Dt : Set X.B.I.GA
  hD : IsReps X u Dt
  hin : InHH X u hK
  hlin : PuLinear X u hK Dt

  F : Formalism.L2.Forms.Forms0 D u

  Tr : Transport X u F
  hI : ColDictInto X Tr hK
  hB : ColDictBij X Tr hK

variable {X}

def PerW.op {hK : X.LevelSubgroupCharacter} {u : D.what₂.Word} (p : PerW X hK u) : (D.mem u).A.Mu0 →ₗ[ℂ] HHX X :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.Pu X u hK p.Dt p.hD p.hin p.hlin ∘ₗ (colDict X p.Tr hK p.hI p.hB).symm.toLinearMap

def ramCrd {u : D.what₂.Word} {n : ℕ} (bR : Fin n → (D.mem u).A.Mram) : (Fin n → ℂ) →ₗ[ℂ] (D.mem u).A.Mu0 :=
  Submodule.inclusion inf_le_left ∘ₗ Fintype.linearCombination ℂ bR

def cjVec (s : Bool) (n : ℕ) : (Fin n → ℂ) →ₛₗ[cj s] (Fin n → ℂ) where
  toFun φ i := cj s (φ i)
  map_add' φ ψ := by funext i; simp
  map_smul' a φ := by funext i; simp

def perTw (s : Bool) {n : ℕ} (f : (Fin n → ℂ) →ₗ[ℂ] HHX X) : (Fin n → ℂ) →ₗ[ℂ] Tw s (HHX X) :=
  Tw.semi (σ := cj s) (σ' := RingHom.id ℂ) s (fun a => (cj_cj s a).symm) (f.comp (cjVec s n))

def spOf (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
    (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram) : SPer Dc where
  HH := Tw s (HHX X)
  nHH := inferInstance
  iHH := inferInstance
  Pu x := perTw s ((pw x).op ∘ₗ ramCrd (bR x))
  Rw := Tw.sub s ((goodSub X G).comap (HHX X).subtype)

section Facts

variable (s : Bool) {Bs : DefBase D.what₂.LL} {Df : DefSide Bs} (Dc : DefCols Df) (hK : X.LevelSubgroupCharacter) (G : GoodOp X)
  (wdD : Dc.Mem → D.what₂.Word) (pw : ∀ x, PerW X hK (wdD x)) (bR : ∀ x, Fin (Dc.a x) → (D.mem (wdD x)).A.Mram)

theorem spOf_Pu (x : Dc.Mem) (φ : Fin (Dc.a x) → ℂ) :
    Tw.out (s := s) ((spOf s Dc hK G wdD pw bR).Pu x φ) = (pw x).op (ramCrd (bR x) (cjVec s _ φ)) := rfl

theorem mem_spOf_Rw (y : Tw s (HHX X)) :
    y ∈ (spOf s Dc hK G wdD pw bR).Rw ↔ ((Tw.out (s := s) y : HHX X) : L2X X) ∈ goodSub X G := Iff.rfl

theorem spOf_Rw_range {ι : D.s.HH ≃ₗᵢ[ℂ] HHX X} (h : RowDictTie X G ι) (y : Tw s (HHX X)) :
    y ∈ (spOf s Dc hK G wdD pw bR).Rw ↔ ∃ F : D.what₂.EE, ι (D.sEE F) = Tw.out (s := s) y := by
  rw [mem_spOf_Rw]
  obtain ⟨j, hj⟩ := h
  have hj' : ∀ F, ι (D.sEE F) = conjHH X G (j F) := hj
  constructor
  · intro hm
    have hF' : star ((Tw.out (s := s) y : HHX X) : L2X X) ∈ EEC X G := by
      rw [mem_EEC, star_star]; exact hm
    refine ⟨j.symm ⟨_, hF'⟩, ?_⟩
    rw [hj', LinearIsometryEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [conjHH_apply]
    exact star_star _
  · rintro ⟨F, hF⟩
    rw [← hF, hj', conjHH_apply]
    have h2 := (j F).2
    rw [mem_EEC] at h2
    exact h2

end Facts

end Sp

section Seam

open Classical in

structure ColSeam {D : D7} {Fl : Fields} {Pr : Primes Fl} (Ch : Chars Fl Pr D.R.m)
    (sel : HeightOneSpectrum (𝓞 Fl.F) → HeightOneSpectrum (𝓞 Fl.E)) {Sg : Set ℕ} (s : Formalism.L2.Ker.Seam D Fl) (σK : Fl.K →+* ℂ)
    (Gc : ChGlob Fl D.R.m) (C : Formalism.L2.Host.CharFrame D) (Pg : Finset (HeightOneSpectrum (𝓞 D.host.E))) {T : Type}
    (mu : T → Tup Fl.F Fl.E Fl.K Sg) (Q : T → Finset (HeightOneSpectrum (𝓞 D.host.E))) (P : LevFam Fl.E Fl.K D.R.r Pr.vGs) : Prop where
  ok : s.Ok
  sig : s.σ₀ = σK
  sigG : Gc.σ₀ = σK
  xi0 : s.iE Gc.xi0 = D.host.xi0
  mu0 : ∀ j, Gc.mu0 j = Formalism.L2.Host.CT.transport s.iE (C.mu0 j)
  vGs : Pr.vGs.image (Formalism.L2.Host.CT.plMap s.iE) = Pg
  twQ : ∀ t, (QE sel (mu t : Chr Fl.F Fl.E Fl.K)).image (Formalism.L2.Host.CT.plMap s.iE) = Q t
  lev : P = rPsymF Ch

end Seam

section FaceSp

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}

def faceSp (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (P1 : Subgroup G) (ψ1 : P1 →* D.what₂.LLˣ)
    (Dc : ∀ Zs : DefSub A.fam.amb, DefCols (A.side P1 ψ1 Zs)) (s : Bool) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (hK : X.LevelSubgroupCharacter)
    (Gd : Formalism.L2.SG.RowDict.GoodOp X) (wdD : ∀ Zs, (Dc Zs).Mem → D.what₂.Word) (pw : ∀ Zs x, PerW X hK (wdD Zs x))
    (bR : ∀ Zs x, Fin ((Dc Zs).a x) → (D.mem (wdD Zs x)).A.Mram) (Zsc : DefSub A.fam.amb → IndefScale A.fam.base) : Face D A where
  P0 := P0
  ψ0 := ψ0
  P1 := P1
  ψ1 := ψ1
  Dc := Dc
  Sp Zs := spOf s (Dc Zs) hK Gd (wdD Zs) (pw Zs) (bR Zs)
  Zsc := Zsc

end FaceSp

end Formalism.IndefR.Cx
