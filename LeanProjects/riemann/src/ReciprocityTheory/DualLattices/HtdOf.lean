import ReciprocityTheory.DualLattices.EvLatStatement
import ReciprocityTheory.DualLattices.EvHopfStatement
import ReciprocityTheory.DualLattices.EvActStatement
import ReciprocityTheory.DualLattices.EvHtStatement
import ReciprocityTheory.DualLattices.PSerFrobStatement
import ReciprocityTheory.DualLattices.WFrobStatement
import ReciprocityTheory.DualLattices.EvBtStatement
import ReciprocityTheory.DualLattices.EvenTwoEvaluationSign
import ReciprocityTheory.DualLattices.EvCotStatement

noncomputable section

open TensorProduct IsLocalRing Matrix

namespace ReciprocityTheory.PGsh.Be2

open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.L2

variable {R₀ : Type} [CommRing R₀]
variable {p : ℕ} [Fact p.Prime] {g : ℕ} {B : BX R₀} {Tw : ATowerL R₀ p} {Dt : DualTower Tw}
  [Algebra ℤ_[p] (Tw.O : Type)] {Oe : Type} [CommRing Oe] [Algebra ℤ_[p] Oe] {σ : Oe ≃ₐ[ℤ_[p]] Oe}
  {cp : (Tw.O : Type)}

def Dat.hopf (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] [Algebra (Tw.O : Type) C]
    (hdom : IsDomain (Tw.O : Type)) (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) : HopfOrder (C := C) (Tw.O : Type) (Nb p g) where
  carrier := D.evImg C
  lat := (hLat C hdom hinj).1
  le_int := (hLat C hdom hinj).2.1
  one_mem := (hLat C hdom hinj).2.2.1
  mul_mem := (hLat C hdom hinj).2.2.2
  comul := (hHopf C hinj).1
  antipode := (hHopf C hinj).2

def htd_of (D : Dat p g B Tw Dt Oe σ cp) (C : Type) [Field C] (v : Valuation C NNReal)
    [Algebra (Tw.O : Type) C] (hdom : IsDomain (Tw.O : Type))
    (hinj : Function.Injective (algebraMap (Tw.O : Type) C))
    (hLat : EvLatStatement D) (hHopf : EvHopfStatement D) (hAct : EvActStatement D)
    (hHt : EvHtStatement D) (hBt : EvBtStatement D) (hH5 : EvenTwoEvaluationSign D) (hCot : EvCotStatement D) :
    HodgeTateDatum p g v (Tw.O : Type) Oe σ cp where
  ρ := D.H.ρ
  ρL := D.H.ρL
  P := D.H.P
  PL := D.H.PL
  E := D.H.E
  E_alternating := D.H.E_alternating
  isUnit_det_E := D.H.isUnit_det_E
  E_equivariant := D.H.E_equivariant
  projectors := D.H.projectors
  Ht := D.H.Ht
  Bt := D.H.Bt
  Ht_equivariant := D.H.Ht_equivariant
  form_eq_alt := D.H.form_eq_alt
  AA := D.hopf C hdom hinj hLat hHopf
  h3 := fun a f hf => hAct C a f hf
  h4 := fun k => ⟨hHt C k, hBt C k⟩
  h5 := fun hp2 s => hH5 C hdom hinj hp2 s
  φ := Classical.choose (hCot C hinj)
  cotangent_surjective := (Classical.choose_spec (hCot C hinj)).1
  cotangent_ker_eq := (Classical.choose_spec (hCot C hinj)).2.1
  cotangent_linear := (Classical.choose_spec (hCot C hinj)).2.2

end ReciprocityTheory.PGsh.Be2
