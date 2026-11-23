import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemConeOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsOfInduces
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam.Pad

namespace GlobalTheory.TrivFlag

def FlagOfTriv {Z : Scheme.{0}} [IsIntegral Z] {N : ℕ} (g : Fin N → Pic Z) : Prop :=
  ∃ (G : Fin N → LB Z) (hG : ∀ i, (G i).IsLB) (r : ∀ i, (G i).ι → Z.functionFieldˣ)
    (A : Matrix (Fin N) (Fin N) Z.functionField), (∀ i, cls (G i) (hG i) = g i) ∧ (∀ i, IsRatSec (G i) (r i)) ∧
    ∀ z : Z, ∃ B : Matrix (Fin N) (Fin N) Z.functionField, B.BlockTriangular id ∧ (∀ a b, RegAt z ((A * B) a b)) ∧
      UnitAt z (A * B).det ∧ ∀ i c, z ∈ (G i).U c → UnitAt z (B i i * r i c)

theorem flagOfTriv_zero (Z : Scheme.{0}) [IsIntegral Z] (N : ℕ) : FlagOfTriv (0 : Fin N → Pic Z) := by
  refine ⟨fun _ => LB.triv Z, fun _ => LB.isLB_triv Z, fun _ _ => 1, 1, fun _ => rfl, fun _ a b h => ?_, fun z =>
    ⟨1, Matrix.blockTriangular_one, fun a b => ?_, by simpa using unitAt_one z, fun i c _ => by simpa using unitAt_one z⟩⟩
  · exact (map_one _).symm.trans (mul_one _).symm
  · rw [mul_one, Matrix.one_apply]
    split_ifs
    · exact (unitAt_one z).regAt
    · exact ⟨0, map_zero _⟩

variable {F : Type} [Field F] [NumberField F] {Y : Var F}

def NormsAt (V : Cover Y) (L : LB V.X) (p : ℕ) (W : Y.X.Opens) (f : Y.X → Y.Fn)
    (l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ) : Prop :=
  ∃ r : (L.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.pull V.j).U i, UnitAt x (V.φ (f (V.π x)) * r i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G)
      (yt : Sp e.O ⟶ V.X) (i : (L.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ⊤ ≤ yt ⁻¹ᵁ L.U (i PUnit.unit) →
      l v e y = Real.log (e.w (valAt z (V.φ (f (below y.1)) * (r i : V.G.functionField))))

theorem normsAt_of_norms {V : Cover Y} {L : HermLB V.p} {f : Y.X → Y.Fn} {a : ∀ σ : F →+* ℂ, Pts Y σ → ℝ}
    {l : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : Norms V L f a l) (p : ℕ) (W : Y.X.Opens) :
    NormsAt V L.B p W f l :=
  have ⟨r, h₁, h₂, _, h₄⟩ := h
  ⟨r, h₁, h₂, fun v _ e y _ => h₄ v e y⟩

theorem NormsAt.congr {V : Cover Y} {L : LB V.X} {p : ℕ} {W : Y.X.Opens} {f f' : Y.X → Y.Fn}
    {l l' : ∀ v : HeightOneSpectrum (𝓞 F), Ext v → AlgPt Y → ℝ} (h : NormsAt V L p W f l) (hf : ∀ x, f x = f' x)
    (hl : ∀ v, resP v = p → ∀ e y, l v e y = l' v e y) : NormsAt V L p W f' l' := by
  obtain rfl : f = f' := funext hf
  obtain ⟨r, h₁, h₂, h₃⟩ := h
  exact ⟨r, h₁, h₂, fun v hv e y hy z yt i a b c => (hl v hv e y).symm.trans (h₃ v hv e y hy z yt i a b c)⟩

def FlagAt {C : CxSt F} {N : ℕ} (A : Fin N → Adl C Y) (p : ℕ) : Prop :=
  ∃ V : Cover Y, ∀ (V' : Cover Y) (π : V'.X ⟶ V.X), π ≫ V.p = V'.p → VertForm.Lies V' V π →
    ∀ (L : Fin N → LB V'.X) (hL : ∀ i, (L i).IsLB) (m : ℕ),
      (∀ i, NormsAt V' (L i) p ⊤ (fun x => genAt (A i).D x ^ m) fun v e y => m * (A i).lg v e y) →
      ∀ (Z : Scheme.{0}) [IsIntegral Z] (ι : Z ⟶ V'.X), (p : Γ(Z, ⊤)) = 0 →
        ∃ g : Fin N → Pic Z, FlagOfTriv g ∧ ∀ i, CechPic.pull ι (cls (L i) (hL i)) = m • g i

def LocFlag {C : CxSt F} {N : ℕ} (A : Fin N → Adl C Y) (p : ℕ) : Prop :=
  ∃ (V : Cover Y) (W : Y.X.Opens) (ι : Type) (U : ι → V.X.Opens) (M : ι → Matrix (Fin N) (Fin N) V.X.functionField)
    (c : ι → Fin N → V.G.functionFieldˣ), genericPoint Y.X ∈ W ∧
    (∀ x : V.X, ¬ IsUnit (p : V.X.presheaf.stalk x) → ∃ a, x ∈ U a) ∧
    (∀ a, ∀ x ∈ U a, ¬ IsUnit (p : V.X.presheaf.stalk x) → (∀ i k, RegAt x (M a i k)) ∧ UnitAt x (M a).det) ∧
    (∀ a i (z : V.G), V.j z ∈ U a → UnitAt z (V.φ (genAt (A i).D (V.π z)) * c a i)) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)), resP v = p → ∀ (e : Ext v) (y : AlgPt Y), below y.1 ∈ W →
      ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j →
      ∀ a, ⊤ ≤ yt ⁻¹ᵁ U a →
        (∀ i, (A i).lg v e y =
          Real.log (e.w (valAt z (V.φ (genAt (A i).D (below y.1)) * (c a i : V.G.functionField))))) ∧
        ∀ b, ⊤ ≤ yt ⁻¹ᵁ U b → ∀ i, (∀ k, k < i → e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i k)) < 1) ∧
          e.w (valAt (z ≫ V.j) (((M a)⁻¹ * M b) i i) - valAt z ((c a i / c b i : V.G.functionFieldˣ) : V.G.functionField)) < 1

end GlobalTheory.TrivFlag

end
