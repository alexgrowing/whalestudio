import Formalism.LocalToGlobal.IndefiniteReal.WeakCharacterisationWithError
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.BaseSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open scoped TensorProduct InnerProductSpace

namespace Formalism.IndefR.Seed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type}

section Pieces

variable (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m)

def TupL (L : LevCh D T) (mu : HeightOneSpectrum (𝓞 D.what₂.LL) → T) (twPl : Finset (HeightOneSpectrum (𝓞 D.what₂.LL))) : Prop :=
  (∀ w, w ∉ twPl → mu w = A3.A.μ0) ∧ (∀ t, t = A3.A.μ0 ∨ ∃ w, mu w = t) ∧ (∀ w ∈ twPl, mu w ≠ A3.A.μ0) ∧
    (∀ w, mu (conjPl w) = mu w) ∧
    ∀ w ∈ twPl, ∃ (ψw : Formalism.L2.Host.HChar D.host.E) (Qw : Finset (Pl D.host.E)),
      Formalism.L2.Host.IsPsi (H := D.host) (Formalism.EigenvalueLevelCeiling.plc w) Qw ψw ∧ L.xiH (mu w) = L.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψw

def TupAt (L : LevCh D T) : Prop := ∃ mu twPl, TupL A3 L mu twPl

def RecL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) : Prop :=
  ∃ (eR : G ≃* G0g D.nd) (plg : (Σ k : Fin 2, D.nd.PlG k) ≃ L.Pg)
      (iso : ∀ kv : (Σ k : Fin 2, D.nd.PlG k), ZMod (D.host.g kv.1) ≃+* kP (plg kv).1),
    (∀ g, D.what₂.embLL ((idemOf A3.A.X).coeff g) = D.ntypes.e0.coeff (eR g)) ∧ (∀ kv, L.C.P.Div kv.1 (plg kv).1) ∧
      ∀ g kv, eG g (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (eR g kv)

def LevelsL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (F : Face D A3.A) : Prop :=
  ∃ ψ0 : ∀ PP : Pl D.host.E, AddChar (kP PP) ℂ, IsGenericPsi L.Pg ψ0 ∧
    levPOf eG D.what₂.embLL (F.lvl false).P (F.lvl false).ψ = P0 L.Pg D.R.r ψ0 ∧
    ∃ π : Equiv.Perm (Fin D.R.r), IsSymOrd D.R.rS D.R.k π ∧
      (∀ g, g ∈ (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).H ↔ reord π g ∈ (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).H) ∧
      ∀ g hg hg', (levPOf eG D.what₂.embLL (F.lvl true).P (F.lvl true).ψ).chi ⟨g, hg⟩ =
        (PsharpSym L.Pg D.R.r D.R.rS D.R.k ψ0).chi ⟨reord π g, hg'⟩

def GrpAt (L : LevCh D T) (F : Face3 D A3) : Prop := ∃ eG : G ≃* G0 L.Pg D.R.r, RecL A3 L eG ∧ LevelsL A3 L eG F.lv2

abbrev BType (L : LevCh D T) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) : Type :=
  Bridge.FamReal D A3.A cX.coef (fun i => (cV i).coef) (fun t => levEnvOf D.sp.X' L.βX (L.datXt t) pl (A3.A.ok t))
    (fun i t => levEnvOf (Vc D i) (L.βV i) (L.datVt i t) pl (A3.A.ok t))

structure BrgL (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E)
    (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) :
    Prop where
  red_R : ∀ t (q : (levEnv D.sp.X' L.βX (L.datXt t)).Q),
    eG ((B.R t).act_tie.red q) = rTup L.βX (L.datXt t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf D.sp.X') : GL _ _))
  red_L : ∀ i t (q : (levEnv (Vc D i) (L.βV i) (L.datVt i t)).Q),
    eG ((B.L i t).act_tie.red q) = rTup (L.βV i) (L.datVt i t) (Formalism.UG.bc (swapAE D) ((q : Bridge.Gf (Vc D i)) : GL _ _))
  tie : ∃ gramR c0R c0L, Bridge.FamTie B pl (Sb : Set (Pl D.host.E)) L.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L
  sb : Sb = L.Pg
  roots : ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))
  pl_onto : ∀ PP, Bridge.SplitOff PP (Sb : Set (Pl D.host.E)) → ∃ P, pl P = PP
  degR : ∀ t P, A3.A.heckeR t (P, 0) = 1 ∧ ∀ k, D.sp.X'.rank < k → A3.A.heckeR t (P, k) = 0
  degL : ∀ i t P, A3.A.heckeL i t (P, 0) = 1 ∧ ∀ k, (Vc D i).rank < k → A3.A.heckeL i t (P, k) = 0
  muVal : ∀ (i : Fin D.R.m) t, ∀ P ∈ A3.A.ok t,
    D.what₂.embLL (A3.A.muVal i t P : D.what₂.LL) = (((L.C.mu0 i * L.xiH t).val (pl P) : ℂˣ) : ℂ)
  etaVal : ∀ P ∈ A3.A.ok A3.A.μ0, D.what₂.embLL (A3.A.etaVal P : D.what₂.LL) = Formalism.L2.Host.etaAlg D.host L.C.eta (pl P)
  in_tie : Bridge.InertTie A3 plI (Sb : Set (Pl D.host.E)) L.Q
  in_onto : ∀ PP, Bridge.InertOff PP (Sb : Set (Pl D.host.E)) → ∃ Q, plI Q = PP
  in_R : ∀ t, Nonempty (Bridge.HeckeTie (Bridge.ratF D.sp.X') (B.R t).pres (A3.heckeRI t)
    (fun i => Formalism.L2.Col.InertTypeOk D.sp.X'.rank i.2) (fun i => IsLabElt D.sp.X' (plI i.1) (labIn D.sp.X'.rank i.2))
    fun i => IsLocElt D.sp.X' (plI i.1))
  in_L : ∀ i t, Nonempty (Bridge.HeckeTie (Bridge.ratF (Vc D i)) (B.L i t).pres (A3.heckeLI i t)
    (fun k => Formalism.L2.Col.InertTypeOk (Vc D i).rank k.2) (fun k => IsLabElt (Vc D i) (plI k.1) (labIn (Vc D i).rank k.2))
    fun k => IsLocElt (Vc D i) (plI k.1))
  in_SF : ∀ v, v ∈ SF ↔ ∃ PP ∈ Sb, PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) = v.asIdeal

def BrgAt (L : LevCh D T) : Prop :=
  ∀ eG : G ≃* G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
    ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl)
      (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ),
      cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ BrgL A3 L eG cX cV pl Sb B plI SF

def RootsAt (L : LevCh D T) : Prop :=
  ∀ t PP, PP ∈ L.Pg ∨ PP ∈ L.Q t → ∃ z : D.what₂.LL, IsPrimitiveRoot z (Nat.card (kP PP))

def QOffAt (L : LevCh D T) : Prop :=
  ∀ t, ∀ PP ∈ L.Q t, ((D.host.condN * D.sp.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal ∧
    ∀ u : D.what₂.Word, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal

def QDeAt (L : LevCh D T) : Prop :=
  ∀ p ∈ ({D.host.pde, D.host.pde'} : Set ℕ), ∃ 𝔭 : HeightOneSpectrum (𝓞 D.host.K),
    ∀ t, ∀ PP ∈ L.Q t, ((p : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal → PP.under (𝓞 D.host.K) = 𝔭

theorem rootsAt_iff (L : LevCh D T) (eG : G ≃* G0 L.Pg D.R.r) (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E)
    (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl) (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F)))
    (h : BrgL A3 L eG cX cV pl Sb B plI SF) : RootsAt L := h.roots

theorem qOff_of (L : LevCh D T) (h : L.Is A3.A.μ0) : QOffAt L := h.Q_off

theorem qDe_of (L : LevCh D T) (h : L.Is A3.A.μ0) : QDeAt L := h.Q_de

def BrgAtX (L : LevCh D T) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∀ eG : G ≃* G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ →
    ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl)
      (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ),
      cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Pr MX cX cV prX ∧ BrgL A3 L eG cX cV pl Sb B plI SF

def BrgAtP (L : LevCh D T)
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∀ eG : G ≃* G0 L.Pg D.R.r, RecL A3 L eG → ∀ θ : InfFam D, IsInfFam θ → ∀ MX : DSModel D.sp.X' (parB (Ptw D) D.R.m),
    ∃ (cX : CoefA D.sp.X') (cV : ∀ i, CoefA (Vc D i)) (pl : Pl0 → Pl D.host.E) (Sb : Finset (Pl D.host.E)) (B : BType A3 L cX cV pl)
      (plI : I0 → Pl D.host.E) (SF : Finset (HeightOneSpectrum (𝓞 D.host.F))) (prX : cX.W →ₗ[ℂ] SmT MX →ₗ[ℂ] ℂ),
      cX.Is ∧ (∀ i, (cV i).Is) ∧ IsDualPair θ MX cX prX ∧ Pr MX cX cV prX ∧ BrgL A3 L eG cX cV pl Sb B plI SF

theorem brgAtX_of_brgAtP {L : LevCh D T}
    {Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop}
    (h : BrgAtP A3 L Pr) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) : BrgAtX A3 L MX Pr :=
  fun eG hrec θ hθ => h eG hrec θ hθ MX

theorem brgAtX_of_brgAt {L : LevCh D T} (h : BrgAt A3 L) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)) :
    BrgAtX A3 L MX (fun _ _ _ _ => True) := fun eG hrec θ hθ => by
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, h1, h2, h3, h4⟩ := h eG hrec θ hθ MX
  exact ⟨cX, cV, pl, Sb, B, plI, SF, prX, h1, h2, h3, trivial, h4⟩

end Pieces

variable (D) in

def ModY : Prop :=
  (∀ j, Nonempty (DSModel (Yc D j) (parB (Ptw D) (min j D.R.m)))) ∧ Nonempty (DSModel D.sp.X' (parB (Ptw D) D.R.m))

def ModWAt (σ0 : D.what₂.LL →+* ℂ) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)) : Prop :=
  ∀ i τ a, (MW i σ0).ε τ a = decide ((a : ℕ) < ((Wc D i).sig (tauE D τ)).1)

def ModW (σ0 : D.what₂.LL →+* ℂ) : Prop :=
  ∃ MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ), ModWAt σ0 MW

variable (D) in

def VPos : Prop := ∀ i, (Vc D i).IsPosDef

section Junk

def hZ (X : Type) [AddCommGroup X] [Module ℂ X] : HMod X where
  H := ℂ
  e := 0

end Junk

variable {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

variable (D A3 Ks) in

def Seed3Psi (F : Face3 D A3) (ψ : AddChar (AF D.host.F) ℂ) : Prop :=
  ∃ R : RealDat3 D A3 Ks, R.toRealDat.ψ = ψ ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces

variable (D A3 Ks) in

def Seed3At (F : Face3 D A3) (ψ : AddChar (AF D.host.F) ℂ) (L : LevCh D T) : Prop :=
  ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.toRealDat.ψ = ψ ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces

variable (D A3 Ks) in

def Seed3AtNT (F : Face3 D A3) (ψ : AddChar (AF D.host.F) ℂ) (L : LevCh D T) : Prop :=
  ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.toRealDat.ψ = ψ ∧ R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.AllPlaces

variable (D A3 Ks) in

def Seed3AtM (F : Face3 D A3) (ψ : AddChar (AF D.host.F) ℂ) (L : LevCh D T) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ))
    (eG : G ≃* G0 L.Pg D.R.r) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.toRealDat.ψ = ψ ∧ R.toRealDat.MW = MW ∧ HEq R.toRealDat.eG eG ∧
    R.toRealDat.MX = MX ∧ Pr R.toRealDat.MX R.toRealDat.cX R.toRealDat.cV R.toRealDat.prX ∧
    R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.IsTup ∧ R.AllPlaces

variable (D A3 Ks) in

def Seed3AtNTM (F : Face3 D A3) (ψ : AddChar (AF D.host.F) ℂ) (L : LevCh D T) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ))
    (eG : G ≃* G0 L.Pg D.R.r) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop) : Prop :=
  ∃ R : RealDat3 D A3 Ks, R.toRealDat.toLevCh = L ∧ R.toRealDat.ψ = ψ ∧ R.toRealDat.MW = MW ∧ HEq R.toRealDat.eG eG ∧
    R.toRealDat.MX = MX ∧ Pr R.toRealDat.MX R.toRealDat.cX R.toRealDat.cV R.toRealDat.prX ∧
    R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.AllPlaces

theorem initial_data_at_of_models {F : Face3 D A3} {ψ : AddChar (AF D.host.F) ℂ} {L : LevCh D T} {MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)}
    {eG : G ≃* G0 L.Pg D.R.r} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)}
    {Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop}
    (h : Seed3AtM D A3 Ks F ψ L MW eG MX Pr) : Seed3At D A3 Ks F ψ L := by
  obtain ⟨R, h1, h2, -, -, -, -, h⟩ := h
  exact ⟨R, h1, h2, h⟩

theorem seed3AtNT_of_M {F : Face3 D A3} {ψ : AddChar (AF D.host.F) ℂ} {L : LevCh D T} {MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)}
    {eG : G ≃* G0 L.Pg D.R.r} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)}
    {Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop}
    (h : Seed3AtNTM D A3 Ks F ψ L MW eG MX Pr) : Seed3AtNT D A3 Ks F ψ L := by
  obtain ⟨R, h1, h2, -, -, -, -, h⟩ := h
  exact ⟨R, h1, h2, h⟩

theorem seed3Psi_of_at {F : Face3 D A3} {ψ : AddChar (AF D.host.F) ℂ} {L : LevCh D T} (h : Seed3At D A3 Ks F ψ L) :
    Seed3Psi D A3 Ks F ψ := by
  obtain ⟨R, -, h⟩ := h
  exact ⟨R, h⟩

theorem seed3Exists_of_psi {F : Face3 D A3} {ψ : AddChar (AF D.host.F) ℂ} (h : Seed3Psi D A3 Ks F ψ) : ThreeFaceBaseDatumExists D A3 Ks F := by
  obtain ⟨R, -, h⟩ := h
  exact ⟨R, h⟩

theorem initial_data_at_of_model_choice (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (hT : TupAt A3 L) (eG : G ≃* G0 L.Pg D.R.r) (hrec : RecL A3 L eG)
    (hlev : LevelsL A3 L eG F.lv2) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop)
    (hB : BrgAtX A3 L MX Pr)
    (hY : ModY D) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)) (hMW : ModWAt (D := D) (sg0 D A3.A) MW) (hθ : Eqv.InfFamExists D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (hV : VPos D) : Seed3AtM D A3 Ks F ψ L MW eG MX Pr := by
  obtain ⟨mu, twPl, hmu⟩ := hT
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨hMY, -⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb⟩ := hB eG hrec θ hθ
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => hZ _
      HV := fun _ _ => hZ _
      HE := hZ _
      HW := fun _ _ => hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := mu
      twPl := twPl
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, hPr, ?_, ?_, ?_, hb.sb⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW, hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩
  · exact ⟨hmu.1, hmu.2.1, hmu.2.2.1, hmu.2.2.2.1, hmu.2.2.2.2⟩

theorem initial_data_at (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (hT : TupAt A3 L) (hG : GrpAt A3 L F) (hB : BrgAt A3 L)
    (hY : ModY D) (hW : ModW (D := D) (sg0 D A3.A)) (hθ : Eqv.InfFamExists D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (hV : VPos D) : Seed3At D A3 Ks F ψ L := by
  obtain ⟨MW, hMW⟩ := hW
  obtain ⟨eG, hrec, hlev⟩ := hG
  obtain ⟨-, ⟨MX⟩⟩ := id hY
  exact initial_data_at_of_models (initial_data_at_of_model_choice L F hL hT eG hrec hlev MX (fun _ _ _ _ => True) (brgAtX_of_brgAt A3 hB MX) hY MW hMW hθ ψ hψ hV)

theorem initial_data_untwisted_of_model_choice (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (eG : G ≃* G0 L.Pg D.R.r) (hrec : RecL A3 L eG)
    (hlev : LevelsL A3 L eG F.lv2) (MX : DSModel D.sp.X' (parB (Ptw D) D.R.m))
    (Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop)
    (hB : BrgAtX A3 L MX Pr)
    (hY : ModY D) (MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)) (hMW : ModWAt (D := D) (sg0 D A3.A) MW) (hθ : Eqv.InfFamExists D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (hV : VPos D) : Seed3AtNTM D A3 Ks F ψ L MW eG MX Pr := by
  obtain ⟨θ, hθ⟩ := hθ
  obtain ⟨hMY, -⟩ := hY
  let MY := fun j => (hMY j).some
  obtain ⟨cX, cV, pl, Sb, B, plI, SF, prX, hcX, hcV, hpr, hPr, hb⟩ := hB eG hrec θ hθ
  obtain ⟨gramR, c0R, c0L, htie⟩ := hb.tie
  let R : RealDat D A3.A Ks :=
    { toLevCh := L
      hv0 := htie.v0
      eG := eG
      pl := pl
      Sb := Sb
      θ := θ
      ψ := ψ
      MY := MY
      MX := MX
      MW := MW
      cX := cX
      cV := cV
      B := B
      prX := prX
      HX := fun _ => hZ _
      HV := fun _ _ => hZ _
      HE := hZ _
      HW := fun _ _ => hZ _
      gE := 1
      gW := fun _ _ => 1
      jX := fun _ => 0
      jV := fun _ _ => 0
      νY := fun _ _ => 0
      fdY := fun _ _ => ∅
      ν0 := 0
      fd0 := ∅
      νX := fun _ => 0
      fdX := fun _ => ∅
      νV := fun _ _ => 0
      fdV := fun _ _ => ∅
      νW := fun _ => 0
      fdW := fun _ => ∅
      ωY := fun _ _ => 1
      ωX := fun _ => 1
      ωP := fun _ _ => 1
      vac := fun _ => 0
      vacX := 0
      vacP := fun _ => 0
      vY := fun _ _ => 0
      vX := fun _ => 0
      vP := fun _ _ => 0
      ItY := fun _ => 0
      ItX := 0
      ioY := fun _ _ => 0
      ioX := fun _ => 0
      Th := fun _ => 0
      BV := fun _ _ => 0
      ioP := fun _ => 0
      thF := fun _ _ => 0
      thG := fun _ _ => 0
      nW := fun _ => 0
      FW := fun _ =>
        { WK := ⊥
          Pt := fun _ => PEmpty
          nrm := fun _ y _ => PEmpty.elim y
          nrm_nonneg := fun _ y _ => PEmpty.elim y
          nrm_zero := fun _ y => PEmpty.elim y
          nrm_add := fun _ y _ _ => PEmpty.elim y
          nrm_smul := fun _ y _ _ => PEmpty.elim y
          towKs := inferInstance
          ρ := 1
          chi := 1
          j := fun _ => 0 }
      mu := fun _ => A3.A.μ0
      twPl := ∅
      kap := 0
      lam := fun _ _ _ _ => 0
      err0 := fun _ _ => 0 }
  refine ⟨{ toRealDat := R, plI := plI, SF := SF, lam3 := fun _ _ _ _ => 0, phs := fun _ => 1 }, rfl, rfl, rfl, HEq.rfl, rfl, hPr, ?_, ?_, hb.sb⟩
  · have hsub : L.Pg ⊆ Sb := by rw [hb.sb]
    exact ⟨hL, hb.red_R, hb.red_L, hlev, hrec, ⟨⟨gramR, c0R, c0L, htie⟩, hsub, hb.roots, hb.pl_onto, hb.degR, hb.degL, hb.muVal,
      hb.etaVal⟩, hθ, hV, hcX, hcV, hpr, hMW, hψ⟩
  · exact ⟨hb.in_tie, hb.in_onto, hb.in_R, hb.in_L, hb.in_SF⟩

theorem initial_data_untwisted_of_models (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (hG : GrpAt A3 L F) (hB : BrgAt A3 L)
    (hY : ModY D) (hW : ModW (D := D) (sg0 D A3.A)) (hθ : Eqv.InfFamExists D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (hV : VPos D) : Seed3AtNT D A3 Ks F ψ L := by
  obtain ⟨MW, hMW⟩ := hW
  obtain ⟨eG, hrec, hlev⟩ := hG
  obtain ⟨-, ⟨MX⟩⟩ := id hY
  exact seed3AtNT_of_M (initial_data_untwisted_of_model_choice L F hL eG hrec hlev MX (fun _ _ _ _ => True) (brgAtX_of_brgAt A3 hB MX) hY MW hMW hθ ψ hψ hV)

theorem initial_data_of_character (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (hT : TupAt A3 L) (hG : GrpAt A3 L F) (hB : BrgAt A3 L)
    (hY : ModY D) (hW : ModW (D := D) (sg0 D A3.A)) (hθ : Eqv.InfFamExists D) (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1))
    (hV : VPos D) : Seed3Psi D A3 Ks F ψ :=
  seed3Psi_of_at (initial_data_at L F hL hT hG hB hY hW hθ ψ hψ hV)

theorem initial_data_exists (L : LevCh D T) (F : Face3 D A3) (hL : L.Is A3.A.μ0) (hT : TupAt A3 L) (hG : GrpAt A3 L F) (hB : BrgAt A3 L)
    (hY : ModY D) (hW : ModW (D := D) (sg0 D A3.A)) (hθ : Eqv.InfFamExists D) (hψ : ∃ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1))
    (hV : VPos D) : ThreeFaceBaseDatumExists D A3 Ks F := by
  obtain ⟨ψ, hψ⟩ := hψ
  exact seed3Exists_of_psi (initial_data_of_character L F hL hT hG hB hY hW hθ ψ hψ hV)

theorem seedQ_of_NTM {F : Face3 D A3} {ψ : AddChar (AF D.host.F) ℂ} {L : LevCh D T} {MW : ∀ i σ, DSModel (Wc D i) (parAt (Wc D i) σ)}
    {eG : G ≃* G0 L.Pg D.R.r} {MX : DSModel D.sp.X' (parB (Ptw D) D.R.m)}
    {Pr : ∀ (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)) (c : CoefA D.sp.X') (cv : ∀ i, CoefA (Vc D i)),
      (c.W →ₗ[ℂ] SmT M →ₗ[ℂ] ℂ) → Prop}
    (h : Seed3AtNTM D A3 Ks F ψ L MW eG MX Pr) :
    ∃ R : RealDat3 D A3 Ks, R.toRealDat.Pre0 F.lv2 ∧ R.IsInert ∧ R.AllPlaces ∧
      (R.toRealDat.toLevCh = L ∧ R.toRealDat.ψ = ψ ∧ R.toRealDat.MW = MW ∧ HEq R.toRealDat.eG eG ∧ R.toRealDat.MX = MX ∧
        Pr R.toRealDat.MX R.toRealDat.cX R.toRealDat.cV R.toRealDat.prX) := by
  obtain ⟨R, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
  exact ⟨R, h7, h8, h9, h1, h2, h3, h4, h5, h6⟩

end Formalism.IndefR.Seed

end
