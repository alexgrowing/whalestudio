import Mathlib
import ReciprocityTheory.NeutralLocalFields.Reciprocity
import Formalism.LocalToGlobal.UnitaryNorms.IsUnitaryNormOf
import Formalism.UnipotentAdelicQuotients.FinOrdValGen

noncomputable section

namespace GlobalTheory.HeckeSplit

open NumberField IsDedekindDomain HeckeValGen

variable (L : Type) [Field L] [NumberField L]

def IsHeckeChar (χ : Ideles L →* ℂˣ) : Prop := Continuous χ ∧ ∀ k : Lˣ, χ (diagUnits L k) = 1

def infIdele : (InfiniteAdeleRing L)ˣ →* Ideles L :=
  Units.map (MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def infPart : Ideles L →* (InfiniteAdeleRing L)ˣ :=
  Units.map (MonoidHom.fst (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def finPart (v : HeightOneSpectrum (𝓞 L)) : Ideles L →* (v.adicCompletion L)ˣ :=
  Units.map
    { toFun := fun x : AdeleRing (𝓞 L) L => (x.2 : FiniteAdeleRing (𝓞 L) L) v
      map_one' := rfl
      map_mul' := fun _ _ => rfl }

variable {L}

def TrivAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, χ (localIdele L v x) = 1

def UnrAt (χ : Ideles L →* ℂˣ) (v : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ x : (v.adicCompletion L)ˣ, Valued.v (x : v.adicCompletion L) = 1 → χ (localIdele L v x) = 1

def DegOne (F : Type) [Field F] [NumberField F] [Algebra F L] (w : HeightOneSpectrum (𝓞 L)) : Prop :=
  ∀ y : 𝓞 L, ∃ u : 𝓞 F, y - algebraMap (𝓞 F) (𝓞 L) u ∈ w.asIdeal

variable (L)

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.unrAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.UnrAt χ.1 v ↔ χ.UnrAt v := by
  unfold _root_.GlobalTheory.HeckeSplit.UnrAt _root_.Formalism.L2.Host.HChar.UnrAt _root_.Formalism.L2.Host.IsUnitAt _root_.Formalism.L2.Host.HChar.loc
  rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.trivAt_iff (χ : _root_.Formalism.L2.Host.HChar L) (v : HeightOneSpectrum (𝓞 L)) :
    _root_.GlobalTheory.HeckeSplit.TrivAt χ.1 v ↔ χ.loc v = 1 := by
  unfold _root_.GlobalTheory.HeckeSplit.TrivAt
  rw [DFunLike.ext_iff]
  unfold _root_.Formalism.L2.Host.HChar.loc
  rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_infIdele (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.GlobalTheory.HeckeSplit.infIdele L x) = x :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_infIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (InfiniteAdeleRing L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.GlobalTheory.HeckeSplit.infIdele L x) = 1 :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.finPart L v (_root_.HeckeValGen.localIdele L v x) = x :=
  Units.ext (_root_.Neutral.B1.localIdele_snd_self L v x)

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

@[simp] theorem _root_.GlobalTheory.HeckeSplit.infPart_localIdele (v : HeightOneSpectrum (𝓞 L))
    (x : (v.adicCompletion L)ˣ) :
    _root_.GlobalTheory.HeckeSplit.infPart L (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext rfl

open NumberField IsDedekindDomain in
variable (L : Type) [Field L] [NumberField L] in
variable {L} in
variable (L) in

theorem _root_.GlobalTheory.HeckeSplit.finPart_localIdele_ne {v w : HeightOneSpectrum (𝓞 L)} (h : w ≠ v)
    (x : (v.adicCompletion L)ˣ) : _root_.GlobalTheory.HeckeSplit.finPart L w (_root_.HeckeValGen.localIdele L v x) = 1 :=
  Units.ext ((_root_.Neutral.B1.localIdele_isSupportedAt L v x).2 w h)

variable {L}

theorem IsHeckeChar.mul {χ ψ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) (hψ : IsHeckeChar L ψ) :
    IsHeckeChar L (χ * ψ) := (Formalism.L2.Host.hcharSub L).mul_mem hχ hψ

theorem IsHeckeChar.inv {χ : Ideles L →* ℂˣ} (hχ : IsHeckeChar L χ) :
    IsHeckeChar L χ⁻¹ := (Formalism.L2.Host.hcharSub L).inv_mem hχ

theorem TrivAt.unrAt {χ : Ideles L →* ℂˣ} {v : HeightOneSpectrum (𝓞 L)} (h : TrivAt χ v) :
    UnrAt χ v := fun x _ => h x

end GlobalTheory.HeckeSplit
