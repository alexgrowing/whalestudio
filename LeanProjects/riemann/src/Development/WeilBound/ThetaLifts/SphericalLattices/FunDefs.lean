import Development.WeilBound.ThetaLifts.SphericalLattices.HoweInert
import Development.WeilBound.CoreStatements.CompactAveragingSplitting.EigenvectorLifting.ExistsEigenLift
import Development.WeilBound.CoreStatements.LocalThetaKernels.IwasMain

noncomputable section

namespace PositivityTheory.Sph

open scoped Matrix
open NumberField IsDedekindDomain Topology GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PositivityTheory.ThK

section Abs

variable {G : Type} [Group G]

def conjInf (K : Subgroup G) (h : G) : Subgroup G := K ⊓ K.map (MulAut.conj h).toMonoidHom

def avgK (K : Subgroup G) (f : G → ℂ) (h : G) : ℂ :=
  ((conjInf K h).relIndex K : ℂ)⁻¹ * ∑ᶠ q : K ⧸ (conjInf K h).subgroupOf K, f ((Quotient.out q : K) * h)

end Abs

def CountSt : Prop :=
  ∀ (G : Type) [Group G] (U K P : Subgroup G) (f f' : G → ℂ), K ≤ U → P ≤ U →
    (∀ g ∈ U, ∃ p ∈ P, ∃ k ∈ K, g = p * k) →
    (∀ h ∈ U, ∃ k₁ ∈ K, ∃ k₂ ∈ K, h⁻¹ = k₁ * h * k₂) →
    (∀ h ∈ U, (conjInf K h).relIndex K ≠ 0) → f 1 = 1 → f' 1 = 1 →
    (∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f (p * g * k) = f p * f g) →
    (∀ p ∈ P, ∀ g ∈ U, ∀ k ∈ K, f' (p * g * k) = f' p * f' g) →
    (∀ p ∈ P, f p * f' p * (((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) : ℂ) =
      (((P ⊓ K).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (P ⊓ K) : ℂ)) →
    ∀ h ∈ U, avgK K f h = avgK K f' h

def AvgSt : Prop :=
  ∀ (G S : Type) [Group G] [AddCommGroup S] [Module ℂ S] (K : Subgroup G) (V : Submodule ℂ S)
    (ω : G → Module.End ℂ S) (l₀ : S →ₗ[ℂ] ℂ), (∀ k ∈ K, ∀ φ ∈ V, ω k φ ∈ V) → (∀ φ ∈ V, ω 1 φ = φ) →
    (∀ k ∈ K, ∀ k' ∈ K, ∀ φ ∈ V, ω (k * k') φ = ω k (ω k' φ)) →
    (∀ φ ∈ V, ∃ H : Subgroup G, H ≤ K ∧ H.relIndex K ≠ 0 ∧ ∀ k ∈ H, ω k φ = φ) →
    ∃ lam : S →ₗ[ℂ] ℂ, (∀ k ∈ K, ∀ φ ∈ V, lam (ω k φ) = lam φ) ∧
      ∀ φ ∈ V, ∀ H : Subgroup G, H ≤ K → H.relIndex K ≠ 0 → (∀ k ∈ H, ω k φ = φ) →
        lam φ = (H.relIndex K : ℂ)⁻¹ * ∑ᶠ q : K ⧸ H.subgroupOf K, l₀ (ω (Quotient.out q : K) φ)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {d : ℕ}

variable (σ) in

def PSub (W : Spc F E d) (v : Pl F) {m : ℕ} (Cy : Matrix (Fin d) (Fin m) (AE F E)) : Subgroup (UA σ W.J) where
  carrier := {p | p ∈ PAt σ W v Cy ∧ p⁻¹ ∈ PAt σ W v Cy}
  one_mem' := by
    have e : mat (1 : UA σ W.J) = 1 := rfl
    exact ⟨⟨one_mem_UAt W v, 1, by rw [e, Matrix.one_mul, Matrix.mul_one]⟩,
      ⟨by rw [inv_one]; exact one_mem_UAt W v, 1, by rw [inv_one, e, Matrix.one_mul, Matrix.mul_one]⟩⟩
  mul_mem' := fun {p q} hp hq => by
    have mm : ∀ a b : UA σ W.J, a ∈ PAt σ W v Cy → b ∈ PAt σ W v Cy → a * b ∈ PAt σ W v Cy := fun a b ha hb => by
      obtain ⟨ha, t, ht⟩ := ha
      obtain ⟨hb, t', ht'⟩ := hb
      refine ⟨mul_mem_UAt ha hb, t * t', ?_⟩
      have e : mat (a * b) = mat a * mat b := rfl
      rw [e, Matrix.mul_assoc, ht', ← Matrix.mul_assoc, ht, Matrix.mul_assoc]
    exact ⟨mm p q hp.1 hq.1, by rw [mul_inv_rev]; exact mm _ _ hq.2 hp.2⟩
  inv_mem' := fun {p} hp => ⟨hp.2, by rw [inv_inv]; exact hp.1⟩

def PInvSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (W : Spc F E d)
    (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)),
    IsLagAt σ W v Cy → ∀ p ∈ PAt σ W v Cy, p⁻¹ ∈ PAt σ W v Cy ∧
      ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t → IsUnit (t.map (compFin F E v)).det

def UnitLiftSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (v : Pl F) (y : (Ev E v)ˣ),
    ∃ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) ∧ compFin F E v (z : AE F E) = y

def CharSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ)
    (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ v w, Formalism.UG.IsInertAt F E v w → v ∉ X.T → ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) →
      X.α z * X.β z = 1 ∧ X.β z = X.α z

def EvInvSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), PairOK B X W M om →
    M.IsWeil B.ψ χX χW om → ∀ v w, Formalism.UG.IsInertAt F E v w → (∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → χW z = 1) →
    ∀ ω ρ, IsLocRep M B.ψ om v ω ρ → ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy → IsAdaptedAt σ W v Cy →
    ∀ l : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l → (∃ φ ∈ SB _, l φ ≠ 0) →
      ∀ g ∈ UAt σ X (evFin F v), ∀ φ ∈ SB _, l (ω (g, 1) φ) = l φ

def SiegSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d : ℕ) (B : Base F E)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (om : Rep σ X W) (χX χW : Chr F E), PairOK B X W M om →
    M.IsWeil B.ψ χX χW om → ∀ v w, Formalism.UG.IsInertAt F E v w → ∀ [LocallyCompactSpace (Fv F v)],
    ∀ ω ρ, IsLocRep M B.ψ om v ω ρ → ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy → IsAdaptedAt σ W v Cy →
    ∀ l : Fn F n d v →ₗ[ℂ] ℂ, IsEvAt M B.ψ v Cy l →
    ∀ p ∈ UAt σ W (evFin F v), ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t →
    ∀ z : (AE F E)ˣ, At (evFin F v) ((z : AE F E) - 1) → compFin F E v (z : AE F E) = (t.map (compFin F E v)).det →
    ∀ u : (Fv F v)ˣ, (u : Fv F v) = Algebra.norm (Fv F v) (compFin F E v (z : AE F E)) →
      ∀ φ ∈ SB _, l (ω (1, p) φ) = (χX z : ℂ) * ((((sbClass (Fv F v)).modu u : ℝ) ^ ((n : ℝ) / 2) : ℝ) : ℂ) * l φ

def ModSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (B : Base F E)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ v w, Formalism.UG.IsInertAt F E v w → ∀ [LocallyCompactSpace (Fv F v)],
    ∀ (m : ℕ) (Cy : Matrix (Fin d) (Fin m) (AE F E)), IsLagAt σ W v Cy → IsAdaptedAt σ W v Cy →
    ∀ p ∈ PSub σ W v Cy, ∀ t : Matrix (Fin m) (Fin m) (AE F E), mat p * Cy = Cy * t →
    ∀ u : (Fv F v)ˣ, (u : Fv F v) = Algebra.norm (Fv F v) (t.map (compFin F E v)).det →
      ((((PSub σ W v Cy ⊓ KSub σ W v).map (MulAut.conj p⁻¹).toMonoidHom).relIndex (PSub σ W v Cy ⊓ KSub σ W v) : ℕ) : ℝ) =
        ((sbClass (Fv F v)).modu u : ℝ) ^ m *
          ((((PSub σ W v Cy ⊓ KSub σ W v).map (MulAut.conj p).toMonoidHom).relIndex (PSub σ W v Cy ⊓ KSub σ W v) : ℕ) : ℝ)

def CartanSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (B : Base F E)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → Even d → ∀ v w, Formalism.UG.IsInertAt F E v w →
    ∀ h ∈ UAt σ W (evFin F v), ∃ k₁ ∈ KAt σ W v, ∃ k₂ ∈ KAt σ W v, h⁻¹ = k₁ * h * k₂

def FinSt : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (d : ℕ) (B : Base F E)
    (W : Spc F E d) (r s : ℕ), B.IsGood σ → W.IsSkew σ B r s → ∀ v w, Formalism.UG.IsInertAt F E v w →
    ∀ h ∈ UAt σ W (evFin F v), (conjInf (KSub σ W v) h).relIndex (KSub σ W v) ≠ 0

end PositivityTheory.Sph

end
