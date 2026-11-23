import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.MassDataInst

open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.HidaSetting Formalism.L2.SG.AdBridge
  Formalism.L2.SG.TypedSets
open scoped TensorProduct

namespace MassDataMassesW

variable {D : D7} (X : HidaSetting D)

noncomputable abbrev KX : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J) :=
  Kf X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E))

def MassAt (u : D.what₂.Word) : Prop :=
  massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u) =
    covol (X.measW u).μH / ((X.muH u Set.univ).toReal *
      ((X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal)

def NVolAt (u : D.what₂.Word) (FdN : Set X.B.I.Ginf) : Prop :=
  covol (X.measW u).μN = (X.muN u FdN).toReal *
    ((X.measW u).μNf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)))).toReal

def MassAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word), X.MeasTie hb → MassAt X u

def NVolAll : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (_hK : X.LevelSubgroupCharacter) (u : D.what₂.Word)
    (FdN : Set X.B.I.Ginf), X.MeasTie hb → X.LevelSubgroupNormalized →
    IsSFund X.B.I (Formalism.L2.SG.PoincareInHH.PoincareSetting.NOinf X u) FdN → NVolAt X u FdN

def HinfCompact : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))

def KCompactOpen : Prop :=
  ∀ {D : D7} (X : HidaSetting D),
    IsCompact (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      IsOpen (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))

noncomputable abbrev GamH (u : D.what₂.Word) : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (HFinIn (Af X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)).subgroupOf
    (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))

noncomputable abbrev KH (u : D.what₂.Word) : Subgroup ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) :=
  (KX X).subgroupOf (Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))

def ClassFinite : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    Finite (DoubleCoset.Quotient (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (GamH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)))
      (KH X u : Set ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))))

def StrongApproxN : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J),
    x ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) →
    ∃ γ : HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J,
      γ ∈ (HFinIn (AF X.B.I.F) X.B.I.cm.sig X.B.I.J : Subgroup (HA (AF X.B.I.F) X.B.I.cm.sig X.B.I.J)) ∧
      γ ∈ Nsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u) ∧
      (splitA X.B.I.cm.sig X.B.I.J (γ * x)).2 ∈ KX X

def SplitIso : Prop :=
  ∀ {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {n : ℕ}
    (J : Matrix (Fin n) (Fin n) E),
    ∃ e : HA (AF F) σ J ≃ₜ* HA (Ainf F) σ J × HA (Af F) σ J, ⇑e = ⇑(splitA σ J)

def VolHTie : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (u : D.what₂.Word), X.MeasTie hb →
    X.muH u Set.univ = (X.measW u).μHinf Set.univ

def StabFinite : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (x : ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))),
    Finite ↥(GamH X u ⊓ (KH X u).map (MulAut.conj x).toMonoidHom)

def FDExistsH : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    ∃ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μH

def MassUnfold : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word),
    (X.measW u).IsTextNorm →
    CompactSpace (Hsub (Ainf X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)) →
    IsCompact (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) →
    IsOpen (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J)) →
    MassFinite (G := ↥(Hsub (Af X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) (GamH X u) (KH X u) →
    ∀ 𝓕 : Set ↥(Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u)),
      IsFundamentalDomain (ratOf (K := Hsub (AF X.B.I.F) X.B.I.cm.sig X.B.I.J (frameOf X u))) 𝓕 (X.measW u).μH →
      (X.measW u).μH 𝓕 = (X.measW u).μHinf Set.univ *
        (X.measW u).μHf (Subtype.val ⁻¹' (KX X : Set (HA (Af X.B.I.F) X.B.I.cm.sig X.B.I.J))) *
        ENNReal.ofReal (massH X.B.I.cm.sig X.B.I.J (X.B.I.L : Set (Fin X.B.I.n → X.B.I.E)) (frameOf X u))

def NLevel : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (u : D.what₂.Word) (y : X.B.I.Gf),
    y ∈ X.NfinU u → y ∈ X.B.I.Kset → (X.xu u)⁻¹ * y * X.xu u ∈ X.K2

def BridgeK : Prop :=
  ∀ {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I) (x : X.B.I.Gf),
    x ∈ X.B.I.Kset ↔ finHA X hb x ∈ KX X

end MassDataMassesW
