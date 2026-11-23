import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.PatchedSupportCompletions
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.InvAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs

noncomputable section

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.AlgebraTools

namespace UpperTheory.V.Pa

def oB (n a : ℕ) (i : Fin n) : Fin n := if (i : ℕ) < a then ⟨0, i.pos⟩ else ⟨n - 1, by have := i.pos; omega⟩

structure GrAlg {B E F : Type} [CommRing B] [IsLocalRing B] [Ring E] [Algebra B E] [CommRing F] [Algebra B F]
    (T : TrInv B E) (n a : ℕ) (r : E →ₐ[B] Matrix (Fin n) (Fin n) F) (ep : Fin n → E) : Type 1 where
  AA : Type
  [ring : CommRing AA]
  [alg : Algebra B AA]
  fin : Module.Finite B AA
  inj : Function.Injective (algebraMap B AA)
  N : Submodule B AA
  compl : _root_.IsCompl (1 : Submodule B AA) N
  mul_mem : ∀ y ∈ N, ∀ z ∈ N, ∃ c ∈ maximalIdeal B, y * z = algebraMap B AA c
  typeI : a = n → N = ⊥
  φ : E →ₐ[B] Matrix (Fin n) (Fin n) AA
  φ_inj : Function.Injective φ
  range : ∀ Y, Y ∈ Set.range φ ↔ Y ∈ blkMat n a (1 : Submodule B AA) N
  st : ∀ y, φ (T.st y) = (φ y)ᵀ
  φ_ep : ∀ i, φ (ep i) = single i i 1
  red : ∀ y i j (b : B), φ y i j - algebraMap B AA b ∈ N → algebraMap B F b = r y i j

attribute [instance] GrAlg.ring GrAlg.alg

variable {l : ℕ} [Fact l.Prime] {L : Loc} {G G0 : Glob l L} (h : G.Hom G0) {n : ℕ} (x : NP G0.frame n)
  {B : Type} [CommRing B] [IsLocalRing B] (D : GDet n B G.G₀) (I : Set (MonoidAlgebra B G.G₀))
  (Bh : Type) [CommRing Bh] [Algebra B Bh] [Algebra Bh (FractionRing x.A)] (e : G.G₀ →* Bˣ)

structure Hat : Type 1 where
  E : Type
  [ring : Ring E]
  [alg : Algebra Bh E]
  [algB : Algebra B E]
  [tower : IsScalarTower B Bh E]
  fin : Module.Finite Bh E
  ι : MonoidAlgebra Bh G.G₀ →ₐ[Bh] E
  surj : Function.Surjective ι
  ker : ∀ y, ι y = 0 ↔ y ∈ TwoSidedIdeal.span (MonoidAlgebra.mapRingHom G.G₀ (algebraMap B Bh) '' I)
  DE : Det n Bh E
  ch : DE.IsCH
  pull : DE.pull ι = (D.map (algebraMap B Bh)).toDet
  T : TrInv Bh E
  tr : ∀ y, T.tr y = DE.tr y
  st : ∀ g, T.st (ι (MonoidAlgebra.single g 1)) =
    algebraMap B Bh (e g ^ (1 - (n : ℤ)) : Bˣ) • ι (MonoidAlgebra.single (G.frame.conj g)⁻¹ 1)
  r : E →ₐ[Bh] Matrix (Fin n) (Fin n) (FractionRing x.A)
  r_ι : ∀ g, r (ι (MonoidAlgebra.single g 1)) = (mat x.ρ (h.p₀ g)).map (algebraMap x.A (FractionRing x.A))
  P : Submodule B E
  ker_le_span_sub_sup_map : P.FG
  mem : ∀ g, ι (MonoidAlgebra.single g 1) ∈ P
  cont : ∀ j : ℕ, ∃ V : OpenNormalSubgroup G.G₀, ∀ g, ∀ v ∈ V,
    ι (MonoidAlgebra.single (g * v) 1) - ι (MonoidAlgebra.single g 1) ∈ maximalIdeal B ^ j • P

attribute [instance] Hat.ring Hat.alg Hat.algB Hat.tower

variable {h x} {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] [Algebra O x.K] {r : Resid G.frame O n}
  {R : Type} [CommRing R] [Algebra O R] [IsCO O R] {u : Pair r R}

def OoPt.gens (P : OoPt h x u) : Set (MonoidAlgebra R G.G₀) :=
  pairGens u ∪ qGens (O := O) (F := G.frame) P.ph P.ta P.U P.y

def OoPt.rep (P : OoPt h x u) : MonoidAlgebra R G.G₀ →+* Matrix (Fin n) (Fin n) x.A :=
  (GDet.repAlg (mat (x.ρ.comp h.p₀)) x.A).toRingHom.comp (MonoidAlgebra.mapRingHom G.G₀ P.f.toRingHom)

end UpperTheory.V.Pa
