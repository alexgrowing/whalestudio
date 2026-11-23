import Mathlib
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.InnerEuclideanEmbeddingEqAverage
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps Formalism.MainNotions.Gaps.NetNorms Formalism.L2.Pj

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.NetWire

def NormLaws {D : D7} (B : WeightFamilies.Prov D) (N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ) : Prop :=
  (∀ j ka σ F, 0 ≤ N j ka σ F) ∧ (∀ j ka σ F, N j ka σ F = 0 ↔ F = 0) ∧
  (∀ j ka σ (a : B.KO) F, N j ka σ (a • F) = ‖σ a‖ * N j ka σ F) ∧
  (∀ j ka σ F G, N j ka σ (F + G) ≤ N j ka σ F + N j ka σ G) ∧
  (∀ j ka σ F, N j ka σ F ≤ B.supN j ka σ F)

section Defs

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ} (n : NormLaws B N)

abbrev base : WeightFamilies.Prov D := withNorm B N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2

def pj (X : PJ D B P j) : PJ D (base n) P j := PJ.tol2NormAlt N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 X

def sc (S : Scal B) : Scal (base n) := scalarsWithNorm N n.1 n.2.1 n.2.2.1 n.2.2.2.1 n.2.2.2.2 S

def gd {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) : GlobalFamilyData (pj n X) ka wL wF :=
  ⟨G.N, G.w, G.del, G.th', G.rz, G.alz, G.th0, G.zc, G.rq, G.th, G.iet, G.et, G.mx⟩

end Defs

section Wrappers

def FinalTheorems (α : Sort 1) : Sort 1 := α

def Tgt (α : Sort 1) : Sort 1 := α

def SrcP (p : Prop) : Prop := p

def TgtP (p : Prop) : Prop := p

def move {α β : Type} (f : FinalTheorems α → Tgt β) : α → β := f

end Wrappers

local unif_hint (α β : Type) where
  ⊢ FinalTheorems α =?= Tgt β

local unif_hint (p q : Prop) where
  ⊢ SrcP p =?= TgtP q

attribute [local irreducible] FinalTheorems Tgt SrcP TgtP

def pd {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {N : ∀ j ka, (B.KO →+* ℂ) → B.Cusp j ka → ℝ} (n : NormLaws B N) {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) : LocalPointData (gd n G) la :=
  ⟨fun ζ => Q.y (move (α := PtsG (gd n G) la) (β := PtsG G la) (fun x => x) ζ), Q.g0,
   fun ζ => Q.c (move (α := PtsG (gd n G) la) (β := PtsG G la) (fun x => x) ζ)⟩

end GlobalTheory.NetWire
