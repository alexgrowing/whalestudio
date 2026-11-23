import Mathlib

noncomputable section

open NumberField IsDedekindDomain

namespace GlobalTheory.Mem.Chr

variable (L : Type) [Field L] [NumberField L]

abbrev Ideles : Type := (AdeleRing (𝓞 L) L)ˣ

def diagUnits : Lˣ →* Ideles L := Units.map (algebraMap L (AdeleRing (𝓞 L) L)).toMonoidHom

open Classical in

def finSingle (v : HeightOneSpectrum (𝓞 L)) : v.adicCompletion L →* FiniteAdeleRing (𝓞 L) L where
  toFun x := ⟨Pi.mulSingle v x, by
    refine Filter.eventually_cofinite.mpr ((Set.finite_singleton v).subset ?_)
    intro w hw
    by_contra h
    apply hw
    have h' : w ≠ v := h
    rw [Pi.mulSingle_eq_of_ne h']
    exact one_mem _⟩
  map_one' := by
    apply Subtype.ext
    exact Pi.mulSingle_one v
  map_mul' x y := by
    apply Subtype.ext
    exact Pi.mulSingle_mul v x y

def localIdele (v : HeightOneSpectrum (𝓞 L)) : (v.adicCompletion L)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inr (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp (finSingle L v))

open Classical in

def infIdele (w : InfinitePlace L) : (w.Completion)ˣ →* Ideles L :=
  Units.map ((MonoidHom.inl (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L)).comp
    (MonoidHom.mulSingle (fun w : InfinitePlace L => w.Completion) w))

theorem valued_algebraMap_eq_one (v : HeightOneSpectrum (𝓞 L)) (x : 𝓞 L) (hx : x ∉ v.asIdeal) :
    Valued.v (algebraMap L (v.adicCompletion L) (algebraMap (𝓞 L) L x)) = 1 := by
  show Valued.v ((algebraMap (𝓞 L) L x : L) : v.adicCompletion L) = _
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_eq_one_iff).mpr hx

end GlobalTheory.Mem.Chr
