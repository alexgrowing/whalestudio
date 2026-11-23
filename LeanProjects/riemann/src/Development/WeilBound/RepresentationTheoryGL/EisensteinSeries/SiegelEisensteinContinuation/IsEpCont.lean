import Development.WeilBound.RepresentationTheoryGL.EisensteinSeries.SiegelEisensteinContinuation.ConvGrOf
import GroundTheory.AutomorphicForms.GL2.GJMatrixAdelic
import GroundTheory.AutomorphicForms.GL2.GodementSection

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing

namespace PositivityTheory.RgEis

open GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.GodementSection GroundTheory.Automorphic.Reduction

variable (k : Type) [Field k] [NumberField k] {ι : Type} [Fintype ι] [DecidableEq ι]

def intAd : Subring 𝔸[k] := ⨅ v : HeightOneSpectrum (𝓞 k), (v.adicCompletionIntegers k).toSubring.comap (finEval v)

def adStd : Ad k 𝔸[k] where
  i := algebraMap k 𝔸[k]
  σ := RingHom.id _
  O := intAd k
  W := InfinitePlace k
  φ w := (InfinitePlace.Completion.extensionEmbedding w).comp (infEval w)
  lg x := Real.log (IdeleGroup.ideleModule k x : ℝ)
  χ := 1

variable {k}

def lineZeta (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) (x : ι → 𝔸[k]) : ℂ :=
  globalZeta (fun t => Ψ (t • x)) ω z

def ratV (ξ : ι → k) : ι → 𝔸[k] := fun i => algebraMap k 𝔸[k] (ξ i)

def epstein (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (z : ℂ) (m : GL ι 𝔸[k]) : ℂ :=
  ∑' l : Projectivization k (ι → k), lineZeta Ψ ω z (((m⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ ratV l.rep)

def tInv {R : Type} [CommRing R] : GL ι R →* GL ι R where
  toFun g := ⟨((g⁻¹ : GL ι R) : Matrix ι ι R)ᵀ, (g : Matrix ι ι R)ᵀ,
    by rw [← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one],
    by rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]⟩
  map_one' := by ext1; simp
  map_mul' a b := by ext1; simp [Matrix.transpose_mul]

structure IsEpCont (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k) (F : ℂ → GL ι 𝔸[k] → ℂ) : Prop where
  entire : ∀ m, Differentiable ℂ (F · m)
  cont : Continuous fun y : ℂ × GL ι 𝔸[k] => F y.1 y.2
  eq : ∀ z : ℂ, (Fintype.card ι : ℝ) < z.re → ∀ m, F z m = z * (z - Fintype.card ι) * epstein Ψ ω z m
  strip : ∀ (a b : ℝ) (C : Set (GL ι 𝔸[k])), IsCompact C → ∃ M : ℝ, ∀ z : ℂ, a ≤ z.re → z.re ≤ b → ∀ m ∈ C,
    ‖F z m‖ ≤ M * (1 + ‖z‖) ^ 2

def StdGood : Prop := ∀ (k : Type) [Field k] [NumberField k], (adStd k).GoodL

def EpConv : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (Ψ : (ι → 𝔸[k]) → ℂ),
    Ψ ∈ GJMatrix.schwartzBruhatPi k ι →
    (∀ (i₀ : ι) (a b : ℝ) (C : Set (GL ι 𝔸[k])), 1 < a → IsCompact C → ∃ f : IdeleGroup k → ℝ,
      Integrable f (ideleMeasure k) ∧ ∀ x : ℝ, a ≤ x → x ≤ b → ∀ m ∈ C, ∀ t : IdeleGroup k,
        ‖Ψ ((t : 𝔸[k]) • ((m : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1))‖ * (IdeleGroup.ideleModule k t : ℝ) ^ x ≤ f t) ∧
    ∀ (x : ℝ) (C : Set (GL ι 𝔸[k])), max 1 (Fintype.card ι : ℝ) < x → IsCompact C →
      ∃ u : Projectivization k (ι → k) → ℝ, Summable u ∧ ∀ m ∈ C, ∀ l,
        ∫ t : IdeleGroup k, ‖Ψ ((t : 𝔸[k]) • ((m : Matrix ι ι 𝔸[k]) *ᵥ ratV l.rep))‖ *
          (IdeleGroup.ideleModule k t : ℝ) ^ x ∂ideleMeasure k ≤ u l

def EpMain : Prop :=
  ∀ (k : Type) [Field k] [NumberField k], ∃ V : ℝ, 0 < V ∧ ∀ (ι : Type) [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (Ψ : (ι → 𝔸[k]) → ℂ) (ω : HeckeCharacter k), Ψ ∈ GJMatrix.schwartzBruhatPi k ι → ω * ω = 1 →
    ∃ F F' : ℂ → GL ι 𝔸[k] → ℂ, IsEpCont Ψ ω F ∧ IsEpCont (GJMatrix.adelicFourierPi k Ψ) ω F' ∧
      (∀ z m, F z m = modPow (Matrix.GeneralLinearGroup.det m) 1 * F' (Fintype.card ι - z) (tInv m)) ∧
      (ω = 1 → ∀ m, F 0 m = Fintype.card ι * V * Ψ 0 ∧ F (Fintype.card ι) m =
        Fintype.card ι * V * modPow (Matrix.GeneralLinearGroup.det m) 1 * GJMatrix.adelicFourierPi k Ψ 0)

def TestFun : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι) (ω : HeckeCharacter k), ω * ω = 1 →
    ∀ U ∈ 𝓝 (1 : (adStd k).kGL ι), ∃ (Ψ : (ι → 𝔸[k]) → ℂ) (Ψ₁ : (Unit → 𝔸[k]) → ℂ) (ψ : (adStd k).kGL ι → ℂ),
      Ψ ∈ GJMatrix.schwartzBruhatPi k ι ∧ Ψ₁ ∈ GJMatrix.schwartzBruhatPi k Unit ∧ Continuous ψ ∧ ψ 1 = 1 ∧
      (∀ (t : 𝔸[k]) (κ : (adStd k).kGL ι),
        Ψ (t • (((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1)) = Ψ₁ (fun _ => t) * ψ κ) ∧
      (∀ κ, ψ κ ≠ 0 → ∃ p : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} ∧ ∃ u ∈ U, κ = p * u ∧
        ψ κ = ω.toIdele (bdet {i₀} p.1) * (‖ψ κ‖ : ℂ)) ∧
      (∀ p κ : (adStd k).kGL ι, p.1 ∈ stab 𝔸[k] {i₀} → ψ (p * κ) = ω.toIdele (bdet {i₀} p.1) * ψ κ) ∧
      (∃ z : ℂ, (Fintype.card ι : ℝ) + 1 < z.re ∧ globalZeta (fun t => Ψ₁ fun _ => t) ω z ≠ 0) ∧
      (ω = 1 → ∀ x : ℝ, 1 < x → globalZeta (fun t => Ψ₁ fun _ => t) ω x ≠ 0)

def TestSph : Prop :=
  ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι] [DecidableEq ι] (i₀ : ι),
    ∃ (Ψ : (ι → 𝔸[k]) → ℂ) (Ψ₁ : (Unit → 𝔸[k]) → ℂ), Ψ ∈ GJMatrix.schwartzBruhatPi k ι ∧
      Ψ₁ ∈ GJMatrix.schwartzBruhatPi k Unit ∧ Ψ 0 = 1 ∧
      (∀ (t : 𝔸[k]) (κ : (adStd k).kGL ι),
        Ψ (t • (((κ.1⁻¹ : GL ι 𝔸[k]) : Matrix ι ι 𝔸[k]) *ᵥ Pi.single i₀ 1)) = Ψ₁ fun _ => t) ∧
      ∀ x : ℝ, 1 < x → globalZeta (fun t => Ψ₁ fun _ => t) 1 x ≠ 0

structure MirData {G : Type} [Group G] [TopologicalSpace G] (π : G →* GL ι 𝔸[k]) (Γ K : Subgroup G) (i₀ i₁ : ι)
    (ω : HeckeCharacter k) (d : ι → IdeleGroup k) (c : G → ℂ) (η η' l : G → ℝ) : Prop where
  two : 2 ≤ Fintype.card ι
  sq : ω * ω = 1
  cont : Continuous π
  cpt : IsCompact (K : Set G)
  piK : ∀ κ ∈ K, ∃ κ' ∈ (adStd k).kGL ι, (π κ : Matrix ι ι 𝔸[k]) * Matrix.diagonal (fun i => (d i : 𝔸[k])) =
    Matrix.diagonal (fun i => (d i : 𝔸[k])) * (κ' : Matrix ι ι 𝔸[k])
  piΓ : ∀ γ ∈ Γ, π γ ∈ (adStd k).ratGL ι
  trans : ∀ (s : Set ι), s = {i₀} ∨ s = {i₁}ᶜ → ∀ g ∈ (adStd k).ratGL ι, ∃ γ ∈ Γ, g * (π γ)⁻¹ ∈ stab 𝔸[k] s
  par : IsPar Γ K ((stab 𝔸[k] {i₀}).comap π) c
  par' : IsPar Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) c
  ht : IsHt Γ K ((stab 𝔸[k] {i₀}).comap π) η
  ht' : IsHt Γ K ((stab 𝔸[k] {i₁}ᶜ).comap π) η'
  htl : IsHt Γ K ⊤ l
  val : ∀ p, π p ∈ stab 𝔸[k] {i₀} → c p = ω.toIdele (bdet {i₀} (π p)) ∧ η p = (adStd k).lg (bdet {i₀} (π p))
  val' : ∀ p, π p ∈ stab 𝔸[k] {i₁}ᶜ → c p = ω.toIdele (bdet {i₁} (π p)) ∧ η' p = -(adStd k).lg (bdet {i₁} (π p))
  vall : ∀ g, l g = (adStd k).lg (Matrix.GeneralLinearGroup.det (π g))

def MirGen : Prop := ForRep fun {G} _ _ {_W} _ _ K ρ => ∀ (k : Type) [Field k] [NumberField k] (ι : Type) [Fintype ι]
  [DecidableEq ι] (π : G →* GL ι 𝔸[k]) (Γ : Subgroup G) (i₀ i₁ : ι) (ω : HeckeCharacter k) (d : ι → IdeleGroup k)
  (c : G → ℂ) (η η' l : G → ℝ), SecondCountableTopology G → MirData π Γ K i₀ i₁ ω d c η η' l →
  HasWall Γ K ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η' (fun g => l g + (Fintype.card ι : ℝ) * η' g) ρ ∧
  (ω = 1 → c = 1 →
    HasFirst Γ K ⊤ ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η'
      (fun g => l g + (Fintype.card ι : ℝ) * η' g) ρ ∧
    HasLast Γ K ⊤ ((stab 𝔸[k] {i₀}).comap π) ((stab 𝔸[k] {i₁}ᶜ).comap π) c η η'
      (fun g => l g + (Fintype.card ι : ℝ) * η' g) l (Fintype.card ι) ρ)

end PositivityTheory.RgEis
