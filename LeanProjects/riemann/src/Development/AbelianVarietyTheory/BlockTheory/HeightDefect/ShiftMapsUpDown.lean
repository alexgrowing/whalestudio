import Mathlib
import Formalism.LocalToGlobal.BesselHermitianTheta.TiedWeil

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct

namespace GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

abbrev AEf (D : D7) : Type := Af D.host.F ⊗[D.host.F] D.host.E

def locPart (D : D7) (v : HeightOneSpectrum (𝓞 D.host.F)) : AE D →+* Fv D.host.F v ⊗[D.host.F] D.host.E :=
  (Algebra.TensorProduct.map (evalV D.host.F v) (AlgHom.id D.host.F D.host.E)).toRingHom.comp (finPart D)

def gramFin (V : HSp D) : Matrix (Fin V.rank) (Fin V.rank) (AEf D) :=
  V.gram.map (inclR (F := D.host.F) (Af D.host.F))

def latFin (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) := latHat D.host.F D.host.E (L0c D V)

def latFinAA (V : HSp D) : AddSubgroup (Fin V.rank → AEf D) :=
  latHat D.host.F D.host.E {y | ∃ a ∈ D.host.AA, ∃ x ∈ L0c D V, y = a • x}

def offS (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) where
  carrier := {x | (∀ i j, infPart D (x i j) = 0) ∧ ∀ v ∈ S, ∀ i j, locPart D v (x i j) = 0}
  zero_mem' := ⟨fun i j => by simp, fun v _ i j => by simp⟩
  add_mem' := by
    rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.add_apply, RingHom.map_add, hx i j, hy i j, add_zero]
    · rw [Matrix.add_apply, RingHom.map_add, hx' v hv i j, hy' v hv i j, add_zero]
  neg_mem' := by
    rintro x ⟨hx, hx'⟩
    refine ⟨fun i j => ?_, fun v hv i j => ?_⟩
    · rw [Matrix.neg_apply, RingHom.map_neg, hx i j, neg_zero]
    · rw [Matrix.neg_apply, RingHom.map_neg, hx' v hv i j, neg_zero]

def mapUp (V W : HSp D) (x : WA V W) : Matrix (Fin W.rank) (Fin V.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)).transpose (gramFin V)

def mapDown (V W : HSp D) (x : WA V W) : Matrix (Fin V.rank) (Fin W.rank) (AEf D) :=
  HMul.hMul (x.map (finPart D)) (gramFin W)

theorem mapUp_add (V W : HSp D) (x y : WA V W) : mapUp V W (x + y) = mapUp V W x + mapUp V W y := by
  ext i j
  simp [mapUp, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapDown_add (V W : HSp D) (x y : WA V W) : mapDown V W (x + y) = mapDown V W x + mapDown V W y := by
  ext i j
  simp [mapDown, Matrix.mul_apply, add_mul, Finset.sum_add_distrib]

theorem mapUp_neg (V W : HSp D) (x : WA V W) : mapUp V W (-x) = -mapUp V W x := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_neg (V W : HSp D) (x : WA V W) : mapDown V W (-x) = -mapDown V W x := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

theorem mapUp_zero (V W : HSp D) : mapUp V W 0 = 0 := by
  ext i j
  simp [mapUp, Matrix.mul_apply]

theorem mapDown_zero (V W : HSp D) : mapDown V W 0 = 0 := by
  ext i j
  simp [mapDown, Matrix.mul_apply]

def homInt (V W : HSp D) : AddSubgroup (WA V W) where
  carrier := {x | if V.rank ≤ W.rank then ∀ y ∈ latFin V, (mapUp V W x).mulVec y ∈ latFinAA W
    else ∀ y ∈ latFin W, (mapDown V W x).mulVec y ∈ latFinAA V}
  zero_mem' := by
    simp only [Set.mem_setOf_eq, mapUp_zero, mapDown_zero, Matrix.zero_mulVec]
    split_ifs
    · exact fun _ _ => zero_mem _
    · exact fun _ _ => zero_mem _
  add_mem' := by
    intro x y hx hy
    simp only [Set.mem_setOf_eq, mapUp_add, mapDown_add, Matrix.add_mulVec] at hx hy ⊢
    split_ifs at hx hy ⊢
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
    · exact fun z hz => add_mem (hx z hz) (hy z hz)
  neg_mem' := by
    intro x hx
    simp only [Set.mem_setOf_eq, mapUp_neg, mapDown_neg, Matrix.neg_mulVec] at hx ⊢
    split_ifs at hx ⊢
    · exact fun z hz => neg_mem (hx z hz)
    · exact fun z hz => neg_mem (hx z hz)

def homLat (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) : AddSubgroup (WA V W) :=
  offS V W S ⊓ homInt V W

def UnramOutside (D : D7) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (∀ v ∈ S, locPart D v (x : AE D) = 1) → χ x = 1

def vacSignOf (ψ : AddChar (AF D.host.F) ℂ) (θ : D.host.E) (V W : HSp D) (l : WA V W) : ℂ :=
  ψ (algebraMap D.host.F (AF D.host.F) (1 / 2) *
    Algebra.trace (AF D.host.F) (AE D) (incA D (θ * D.host.xi0) * hHom V W l l))

def theta0 (D : D7) : D.host.E := (1 + D.host.sqrtMinusD) / 2

def vacSign (ψ : AddChar (AF D.host.F) ℂ) (V W : HSp D) (l : WA V W) : ℂ := vacSignOf ψ (theta0 D) V W l

variable {X : ThetaX D} {T : ThetaTied D X}

def IsVacuum (Wl : WeilTied D X T) (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))) (Φ : X.Sch V W) : Prop :=
  ∀ l ∈ homLat V W S, Heisenberg₂ Wl.ψ V W l (Wl.evS V W Φ) = vacSign Wl.ψ V W l • Wl.evS V W Φ

def HomLatSelfDual (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
    ∀ x ∈ offS V W S, x ∈ homLat V W S ↔ ∀ l ∈ homLat V W S, ψ (sympl V W x l) = 1

def VacSignIndep (D : D7) : Prop :=
  ∀ ψ : AddChar (AF D.host.F) ℂ, IsStdChar D ψ (-1) → ∀ θ : 𝓞 D.host.E, (θ : D.host.E) + star (θ : D.host.E) = 1 →
    ∀ (V W : HSp D) (S : Finset (HeightOneSpectrum (𝓞 D.host.F))),
      ∀ l ∈ homLat V W S, vacSignOf ψ (θ : D.host.E) V W l = vacSign ψ V W l

def VacuumExists (Wl : WeilTied D X T) : Prop :=
  ∀ V W : HSp D, V.rank ≠ W.rank → ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), ∃ Φ : X.Sch V W, Φ ≠ 0 ∧ IsVacuum Wl V W S Φ

def HyperspecialFixesVacuum (Wl : WeilTied D X T) : Prop :=
  ∀ (V W : HSp D) (χ χ' : X.Chr), V.rank ≠ W.rank → ResEta D (T.eChr χ) V.rank → ResEta D (T.eChr χ') W.rank →
    ∀ S : Finset (HeightOneSpectrum (𝓞 D.host.F)), UnramOutside D S (T.eChr χ) → UnramOutside D S (T.eChr χ') →
      ∀ g ∈ KsphC V S, ∀ h ∈ KsphC W S, ∀ Φ : X.Sch V W, IsVacuum Wl V W S Φ → Wl.om V W χ χ' (g, h) Φ = Φ

theorem IsVacuum.mono (Wl : WeilTied D X T) (V W : HSp D) {S S' : Finset (HeightOneSpectrum (𝓞 D.host.F))} (hS : S ⊆ S')
    {Φ : X.Sch V W} (h : IsVacuum Wl V W S Φ) : IsVacuum Wl V W S' Φ :=
  fun l hl => h l ⟨⟨hl.1.1, fun v hv => hl.1.2 v (hS hv)⟩, hl.2⟩

end GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown

end
