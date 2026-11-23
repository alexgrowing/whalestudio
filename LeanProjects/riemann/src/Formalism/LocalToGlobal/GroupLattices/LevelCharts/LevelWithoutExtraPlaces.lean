import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LevelsOfChChartsCover
import Formalism.LocalToGlobal.GroupLattices.LevelCharts.LamHLocPrinc
import Formalism.LocalToGlobal.GroupLattices.CloudFilling.CloudBound
import Formalism.LocalToGlobal.HermitianColumns.HermCols
import Formalism.LocalToGlobal.HermitianColumns.TiedQC

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG Formalism.MainNotions.G Formalism.FrobeniusOrbits
open scoped TensorProduct

namespace Formalism.L2.G

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Generic

variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [StarRing E] [Algebra F E] {sp : Spaces R F E} {gp : Fin 2 → ℕ}
    {ι' : Type} [Fintype ι'] {hc : ι' → HCParam R} {C : ColumnChain R ι' hc} {A : ColumnsAtT R C}
    {clsLat : ∀ i, C.cls i → Submodule (𝓞 E) (sp.X i).V}
  {L : ColLevel R F E sp gp C A clsLat} {p nV : ℕ} {W Qq : Type} [CommRing W] [Field Qq] [Algebra W Qq]

def levelWithoutExtraPlaces {S : HSpace E} {T f : ℕ} (X : Formalism.L2.Herm.StepLevel sp.cm S gp T f) :
    Formalism.L2.Herm.StepLevelQ sp.cm S gp T f ∅ where
  Lb := X.Lb
  Lb_fin := X.Lb_fin
  Lb_span := X.Lb_span
  Lb_int := X.Lb_int
  Lb_dual := X.Lb_dual
  Lb_index := X.Lb_index
  Uloc := X.Uloc
  Uloc_lev := X.Uloc_lev
  Uloc_hyp := fun v h0 h1 hT _ => X.Uloc_hyp v h0 h1 hT
  Uloc_g := X.Uloc_g
  UlocAlt := X.UlocAlt
  Uloc_Q := fun v hv => absurd hv (Finset.notMem_empty v)
  U := X.U
  U_eq := X.U_eq

structure StepX (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (T f i : ℕ) where

  Q : Finset (HeightOneSpectrum (𝓞 F))
  Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal
  Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal

  lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q

  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 F)), (gp a : 𝓞 F) ∈ v.asIdeal → Subgroup (GL (Fin (sp.X i).rank) (resV F v))

  atG : LevAtGH sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc HG

  lamG : ∀ a v h, HG a v h →* Z

  typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)

  fr : FrS I lev.Lb

  fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))

def StepX.type {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ} (Sx : StepX I Z T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) :
    awayG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p →* Z :=
  Sx.atG.typeX hg Sx.lamG p hp * lamQG sp.cm.sig (sp.X i).gram Sx.lev.Uloc Sx.Q Sx.typQ p Sx.Q_p

def StepX.toStepAt {I : LocId L p nV W Qq} {O : Type} [CommRing O] {T f i : ℕ} (Sx : StepX I Oˣ T f i)
    (hg : ∀ a, gp a ≠ 0) (hp : ∀ a, Nat.Coprime p (gp a)) : StepAt I O (sp.X i).rank where
  J := (sp.X i).gram
  Lb := Sx.lev.Lb
  Uloc := Sx.lev.Uloc
  fr := Sx.fr
  ψ := (Sx.type hg hp)⁻¹
  eps := 1
  fin := finite_compG sp.cm.sig (sp.X i).gram Sx.lev.Uloc p Sx.lev.U (fun x hx => (Sx.lev.U_eq x).1 hx) Sx.fin

def StepX.ofFlag {I : LocId L p nV W Qq} {Z : Type} [CommGroup Z] {T f i : ℕ}
    (Q : Finset (HeightOneSpectrum (𝓞 F))) (Q_p : ∀ v ∈ Q, ((p : ℕ) : 𝓞 F) ∉ v.asIdeal)
    (Q_g : ∀ v ∈ Q, ∀ a, (gp a : 𝓞 F) ∉ v.asIdeal) (prime_not_mem_places : ∀ v ∈ Q, (T : 𝓞 F) ∉ v.asIdeal)
    (lev : Formalism.L2.Herm.StepLevelQ sp.cm (sp.X i) gp T f Q)
    (atG : LevAtG sp.cm.sig (sp.X i).gram gp L.splitG lev.Lb lev.Uloc R.k R.m R.t i) (ch : CharsG F gp Z)
    (typQ : ∀ v, v ∈ Q → (lev.Uloc v →* Z)) (fr : FrS I lev.Lb)
    (fin : Finite (ClassSet (Formalism.L2.Herm.UFin sp.cm (sp.X i)) (lev.U.subgroupOf (Formalism.L2.Herm.UAf sp.cm (sp.X i))))) :
    StepX I Z T f i where
  Q := Q
  Q_p := Q_p
  Q_g := Q_g
  prime_not_mem_places := prime_not_mem_places
  lev := lev
  HG := fun _ v _ => JXbar (resV F v) (sp.X i).rank R.k R.m R.t i
  atG := atG.toH
  lamG := ch.lamX (sp.X i).rank R.k R.m R.t i
  typQ := typQ
  fr := fr
  fin := fin

end Generic

section Record

variable {p : ℕ} {W Qq O Kf : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [Field Qq]
  [Algebra W Qq] [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field Kf] [Algebra O Kf]
  {ι : Qq →+* Kf} {σ : Qq ≃+* Qq} {j : W →+* O} {w : O}

theorem rank_step (D : D7) (i : ℕ) (hi : i < D.R.m) :
    D.R.k - 1 + (i + 1) * (D.R.t + 1) + 1 = (D.sp.X (i + 1)).rank := by
  rw [D.sp.X_rank (i + 1) hi]
  have := k_pred D.R
  simp only [Ranks.N]
  omega

abbrev levelsRec (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
    (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I Oˣ (D.mem u).A.T D.R.f (i + 1)) :
    Levels (fillsRec D u h hS r L I ψ y e c hc) :=
  levelsOfCh hS r (fun v s => lamRec D u (posG (zPsi D.R.toFrame h) ⟨v, s⟩)) (fun _ _ => lamRec_anti D u _) (k_pred D.R) I ψ y e
    (fillsRec D u h hS r L I ψ y e c hc) D.R.m (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_step D i hi) Cb
    (fun i hi β => (Sx i hi β).toStepAt hg hp)

def levelsRec_tie (D : D7) (u : D.what₂.Word) (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (Cb : ∀ i, i < D.R.m → Type) [∀ i hi, Finite (Cb i hi)]
    (Sx : ∀ i (hi : i < D.R.m), Cb i hi → StepX I Oˣ (D.mem u).A.T D.R.f (i + 1))
    (hy : ∀ i, (Quotient.mk'' (y i) : compL L p) = i)
    (hyp : ∀ i (w' : HeightOneSpectrum (𝓞 D.host.F)), ((p : ℕ) : 𝓞 D.host.F) ∈ w'.asIdeal →
      bc (prV (E := D.host.E) w') (y i : GL (Fin D.R.k) (D.host.E ⊗[D.host.F] Formalism.L2.Herm.Af D.host.F)) = 1)
    (i : ℕ) (hi : i < D.R.m) (β : Cb i hi) :
    GChartTie (gatRec_lev D u h hS r L I ψ y e hy hyp) (levelsRec D u h hS r L I ψ y e c hc hg hp Cb Sx) i
      (fun a : ((Sx i hi β).toStepAt hg hp).comp => ⟨hi, β, a⟩)
      (D.sp.X (i + 1)).gram (Sx i hi β).lev.Lb (Sx i hi β).lev.Uloc ((Sx i hi β).type hg hp)⁻¹ 1 :=
  levelsOfCh_tie hS r _ _ (k_pred D.R) I ψ y e hy hyp (fillsRec D u h hS r L I ψ y e c hc) D.R.m
    (fun i => (D.sp.X (i + 1)).rank) (fun i hi => rank_step D i hi) Cb (fun i hi β => (Sx i hi β).toStepAt hg hp) i hi β

structure StepMore (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i) where
  Q_p : ∀ v ∈ T.Q μ, ((p : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  Q_g : ∀ v ∈ T.Q μ, ∀ a, (D.host.g a : 𝓞 D.host.F) ∉ v.asIdeal
  prime_not_mem_places : ∀ v ∈ T.Q μ, (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ v.asIdeal
  HG : ∀ (a : Fin 2) (v : HeightOneSpectrum (𝓞 D.host.F)), (D.host.g a : 𝓞 D.host.F) ∈ v.asIdeal →
    Subgroup (GL (Fin (D.sp.X i).rank) (resV D.host.F v))
  atG : LevAtGH D.sp.cm.sig (D.sp.X i).gram D.host.g L.splitG (T.lev u μ i h1 hm β).Lb (T.lev u μ i h1 hm β).Uloc HG
  lamG : ∀ a v h, HG a v h →* Z
  typQ : ∀ v, v ∈ T.Q μ → ((T.lev u μ i h1 hm β).Uloc v →* Z)
  fr : FrS I (T.lev u μ i h1 hm β).Lb

def stepXTw (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    {L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u)} {nV : ℕ}
    (I : LocId L p nV W Qq) (Z : Type) [CommGroup Z] (i : ℕ) (h1 : 1 ≤ i) (hm : i ≤ D.R.m) (β : T.Ch u μ i)
    (M : StepMore D T u μ I Z i h1 hm β) : StepX I Z (D.mem u).A.T D.R.f i where
  Q := T.Q μ
  Q_p := M.Q_p
  Q_g := M.Q_g
  prime_not_mem_places := M.prime_not_mem_places
  lev := T.lev u μ i h1 hm β
  HG := M.HG
  atG := M.atG
  lamG := M.lamG
  typQ := M.typQ
  fr := M.fr
  fin := T.finite_cls u μ hμ i h1 hm β

abbrev levelsTw (D : D7) {inQ : D.what₂.Tup → HeightOneSpectrum (𝓞 D.host.F) → Prop} (T : Formalism.L2.Herm.TwChTied D inQ)
    (u : D.what₂.Word) (μ : D.what₂.Tup) (hμ : μ ≠ D.what₂.mu0)
    (h : D.R.MA)
    (hS : HidaSetting p (orderOf (zPsi D.R.toFrame h)) W Qq O Kf ι σ j w) (r : ℕ)
    (L : ColLevel D.R D.host.F D.host.E D.sp D.host.g (D.mem u).C (D.mem u).A (D.clsLat u))
    (I : LocId L p (nOrb (zPsi D.R.toFrame h)) W Qq) (ψ : Formalism.L2.Herm.awayFrom₂ L p →* Oˣ)
    (y : compL L p → UPts D.sp.cm.sig D.sp.gram0 (Formalism.L2.Herm.Af D.host.F)) (e : ℕ) (c : ℕ) (hc : CloudBound D u c)
    (hg : ∀ a, D.host.g a ≠ 0) (hp : ∀ a, Nat.Coprime p (D.host.g a))
    (M : ∀ i (hi : i < D.R.m) (β : T.Ch u μ (i + 1)),
      StepMore D T u μ I Oˣ (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi β) :
    Levels (fillsRec D u h hS r L I ψ y e c hc) :=
  levelsRec D u h hS r L I ψ y e c hc hg hp (fun i _ => T.Ch u μ (i + 1))
    (fun i hi β => stepXTw D T u μ hμ I Oˣ (i + 1) (Nat.succ_le_succ (Nat.zero_le i)) hi β (M i hi β))

end Record

end Formalism.L2.G
