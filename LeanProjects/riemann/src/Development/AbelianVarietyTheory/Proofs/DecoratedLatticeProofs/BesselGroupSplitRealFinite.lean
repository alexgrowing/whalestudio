import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValLastX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FlagUnipotentAnisotropicProjectionEqOne
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BesSplit

theorem tens_ext {F E A B : Type} [Field F] [Field E] [Algebra F E] [CommRing A] [CommRing B] [Algebra F A]
    [Algebra F B] (z w : (A × B) ⊗[F] E)
    (h1 : Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) w)
    (h2 : Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z =
      Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) w) : z = w := by
  have hz : ∀ z : (A × B) ⊗[F] E, z = LinearMap.rTensor E (LinearMap.inl F A B)
        (Algebra.TensorProduct.map (AlgHom.fst F A B) (AlgHom.id F E) z) +
      LinearMap.rTensor E (LinearMap.inr F A B)
        (Algebra.TensorProduct.map (AlgHom.snd F A B) (AlgHom.id F E) z) := by
    intro z
    induction z with
    | zero => simp
    | tmul x y => simp [← TensorProduct.add_tmul]
    | add x y hx hy =>
      simp only [map_add]
      rw [add_add_add_comm, ← hx, ← hy]
  rw [hz z, hz w, h1, h2]

theorem entry_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    (i : Fin k) (j : Fin m) {c : R} (hN : (P * (N * Q)) i j = c) (hK : (P * (K * Q)) i j = c) :
    (P * (M * Q)) i j = c := by
  refine hinj _ _ ?_ ?_
  · have e : (P * (M * Q)).map φ = (P * (N * Q)).map φ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hi]
    exact (congrFun (congrFun e i) j).trans (congrArg φ hN)
  · have e : (P * (M * Q)).map ψ = (P * (K * Q)).map ψ := by
      rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, hf]
    exact (congrFun (congrFun e i) j).trans (congrArg ψ hK)

theorem mat_eq {R R₁ R₂ : Type} [CommRing R] [CommRing R₁] [CommRing R₂] (φ : R →+* R₁) (ψ : R →+* R₂)
    (hinj : ∀ z w, φ z = φ w → ψ z = ψ w → z = w) {n k m : ℕ} {M N K : Matrix (Fin n) (Fin n) R}
    (hi : M.map φ = N.map φ) (hf : M.map ψ = K.map ψ) (P : Matrix (Fin k) (Fin n) R) (Q : Matrix (Fin n) (Fin m) R)
    {C : Matrix (Fin k) (Fin m) R} (hN : P * (N * Q) = C) (hK : P * (K * Q) = C) : P * (M * Q) = C :=
  Matrix.ext fun i j => entry_eq φ ψ hinj hi hf P Q i j (congrFun (congrFun hN i) j) (congrFun (congrFun hK i) j)

variable {D : D7}

def realPart (D : D7) : AE D →+* Ainf D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (fstA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

def finitePart (D : D7) : AE D →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id D.host.F D.host.E)).toRingHom

theorem ext_parts (z w : AE D) (h1 : realPart D z = realPart D w) (h2 : finitePart D z = finitePart D w) : z = w :=
  tens_ext (A := Ainf D.host.F) (B := Af D.host.F) z w h1 h2

theorem map_real_eq {S : HSp D} {x y : GA D S} (h : infHom S x = infHom S y) :
    (Formalism.L2.Theta.mt S x).map (realPart D) = (Formalism.L2.Theta.mt S y).map (realPart D) := congrArg Units.val h

theorem map_finite_eq {S : HSp D} {x y : GA D S} (h : finHom S x = finHom S y) :
    (Formalism.L2.Theta.mt S x).map (finitePart D) = (Formalism.L2.Theta.mt S y).map (finitePart D) := congrArg Units.val h

set_option maxHeartbeats 2000000 in

theorem mem_besGrp_of_parts {S S₀ A L : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (o : OrthDec S₀ A L) {x y z : GA D S}
    (hi : infHom S x = infHom S y) (hf : finHom S x = finHom S z) (hy : y ∈ besGrp d o) (hz : z ∈ besGrp d o) :
    x ∈ besGrp d o := by
  have key : ∀ g : GA D S, g ∈ besGrp d o ↔ g ∈ jacGrp d ∧
      d.p0 ⬝ (Formalism.L2.Theta.mt S g ⬝ (d.j0 ⬝ o.jB)) = o.jB := fun g => by
    have e := Set.ext_iff.1 (GlobalTheory.BesClosed.besGrp_eq_inter d o) g
    rw [← Matrix.mul_assoc (Formalism.L2.Theta.mt S g), ← Matrix.mul_assoc]
    exact e
  have hi' := map_real_eq hi
  have hf' := map_finite_eq hf
  obtain ⟨hy1, hy2⟩ := (key y).1 hy
  obtain ⟨hz1, hz2⟩ := (key z).1 hz
  obtain ⟨hy3, hy4, hy5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d y).1 hy1
  obtain ⟨hz3, hz4, hz5⟩ := (GlobalTheory.BesClosed.mem_jacGrp_iff_mat d z).1 hz1
  refine (key x).2 ⟨(GlobalTheory.BesClosed.mem_jacGrp_iff_mat d x).2 ⟨?_, ?_, fun i j => ⟨fun hji => ?_, ?_⟩⟩, ?_⟩
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy3 hz3
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy4 hz4
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i j ((hy5 i j).1 hji) ((hz5 i j).1 hji)
  · exact entry_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ i i (hy5 i j).2 (hz5 i j).2
  · exact mat_eq (realPart D) (finitePart D) ext_parts hi' hf' _ _ hy2 hz2

theorem besGrp_split : ∀ (D : D7) (V V₀ A L : HSp D) (ρ : ℕ) (d : HypDec V V₀ ρ) (o : OrthDec V₀ A L),
    ∀ a ∈ GinfC V, ∀ b ∈ GfC V, a * b ∈ besGrp d o → a ∈ besGrp d o ∧ b ∈ besGrp d o := by
  intro D V V₀ A L ρ d o a ha b hb hab
  have ha' : finHom V a = 1 := MonoidHom.mem_ker.1 ha
  have hb' : infHom V b = 1 := MonoidHom.mem_ker.1 hb
  exact ⟨mem_besGrp_of_parts d o (by rw [map_mul, hb', mul_one]) (by rw [ha', map_one]) hab (one_mem _),
    mem_besGrp_of_parts d o (by rw [hb', map_one]) (by rw [map_mul, ha', one_mul]) (one_mem _) hab⟩

end GlobalTheory.BesSplit
