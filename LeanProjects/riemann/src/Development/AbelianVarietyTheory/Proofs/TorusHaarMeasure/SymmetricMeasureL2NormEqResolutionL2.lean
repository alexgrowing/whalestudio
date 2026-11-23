import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.TorusAtDataPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.SupRatioLeOfPhaseZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.Taylor
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.SumCMulImHermCEqSignMulTrace
import Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsTorusCoordinates
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.PointwiseNormCanonicalThetaEqSqThetaConstant
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusMarkingPhase
import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.TorusThetaNorms

namespace GlobalTheory.TorusMirror

open NumberField Complex ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.I2 GlobalTheory.ThetaHol
open scoped ComplexConjugate ContDiff

noncomputable section

section Deriv

variable {W W' : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] [NormedAddCommGroup W']
  [NormedSpace ℂ W']

variable (J : W →L[ℝ] W') {F : W → ℂ} {G : W' → ℂ} (hF : ContDiff ℂ ω F) (hG : ContDiff ℂ ω G)
  (h : ∀ w, G (J w) = conj (F w))
include hF hG h

end Deriv

section Torus

variable {E : Type} [Field E] [NumberField E]

theorem act_cj (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim)
    (hσ : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1) (α : 𝓞 E) (y : Vsp X.dim) :
    act α (cj X σ y) = cj X σ (act α y) := by
  ext i
  simp [act, cj_apply, hσ]

def conjBasis (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim) :
    Module.Basis (Fin (2 * Fintype.card (Idx dim))) ℝ (Vsp dim) :=
  (X.b.map (cj X σ)).reindex (finCongr (by rw [Fintype.card_congr σ]))

theorem mem_conjBasis (X : PT E) {dim : (E →+* ℂ) → ℕ} (σ : Idx dim ≃ Idx X.dim) (y : Vsp X.dim) :
    cj X σ y ∈ lat (conjBasis X σ) ↔ y ∈ lat X.b := by
  simp only [lat, Module.Basis.mem_span_iff_repr_mem, conjBasis, Module.Basis.repr_reindex_apply,
    Module.Basis.map_repr, LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]
  exact ⟨fun h i => h (finCongr (by rw [Fintype.card_congr σ]) i), fun h i => h _⟩

def conjPT (X : PT E) (σ : Idx (fun τ => X.dim (ComplexEmbedding.conjugate τ)) ≃ Idx X.dim)
    (hσ : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1) : PT E :=
  let b := conjBasis X σ
  have hb : ∀ y, cj X σ y ∈ lat b ↔ y ∈ lat X.b := mem_conjBasis X σ
  { dim := fun τ => X.dim (ComplexEmbedding.conjugate τ)
    r := X.r
    dim_conj := fun τ => X.dim_conj _
    b := b
    stable := fun α y hy => by
      obtain ⟨y, rfl⟩ := (cj X σ).surjective y
      rw [act_cj X σ hσ, hb]
      exact X.stable α y ((hb y).1 hy)
    integral := fun y z hy hz => by
      obtain ⟨y, rfl⟩ := (cj X σ).surjective y
      obtain ⟨z, rfl⟩ := (cj X σ).surjective z
      obtain ⟨k, hk⟩ := X.integral y z ((hb y).1 hy) ((hb z).1 hz)
      exact ⟨-k, by rw [Hf_cj, conj_im, hk, Int.cast_neg]⟩
    perfect := fun ψ => by
      let j : lat X.b →+ lat b :=
        { toFun := fun v => ⟨cj X σ v, (hb _).2 v.2⟩
          map_zero' := by ext1; simp
          map_add' := fun u v => by ext1; simp }
      obtain ⟨y, hy, h⟩ := X.perfect (ψ.comp j)
      refine ⟨cj X σ (-y), (hb _).2 (neg_mem hy), ?_⟩
      rintro ⟨z, hz⟩
      obtain ⟨z, rfl⟩ := (cj X σ).surjective z
      have := h ⟨z, (hb z).1 hz⟩
      rw [Hf_cj, conj_im]
      refine this.trans ?_
      simp [Hf]
    eps := fun y => X.eps ((cj X σ).symm y)
    eps_pm := fun y hy => by
      obtain ⟨y, rfl⟩ := (cj X σ).surjective y
      simpa using X.eps_pm y ((hb y).1 hy)
    eps_add := fun y hy z hz => by
      obtain ⟨y, rfl⟩ := (cj X σ).surjective y
      obtain ⟨z, rfl⟩ := (cj X σ).surjective z
      rw [Hf_cj, conj_im, mul_neg, Real.cos_neg]
      simpa using X.eps_add y ((hb y).1 hy) z ((hb z).1 hz)
    eps_iso := fun y hy h => by
      obtain ⟨y, rfl⟩ := (cj X σ).surjective y
      rw [LinearEquiv.symm_apply_apply]
      refine X.eps_iso y ((hb y).1 hy) fun α => ?_
      have := h α
      rwa [act_cj X σ hσ, Hf_cj, conj_im, neg_eq_zero] at this }

section

variable (X : PT E) (σ : Idx (fun τ => X.dim (ComplexEmbedding.conjugate τ)) ≃ Idx X.dim)
  (hσ : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1)

end

def swapIdx (dim : (E →+* ℂ) → ℕ) (p : (E →+* ℂ) → Prop) :
    Idx (fun τ => dim (ComplexEmbedding.conjugate τ)) ≃ Idx dim := by
  classical
  exact Equiv.sigmaCongr (ComplexEmbedding.involutive_conjugate E).toPerm
    fun τ => if p τ then Fin.revPerm else Equiv.refl (Fin (dim (ComplexEmbedding.conjugate τ)))

end Torus

section Coord

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}
  {x : Frame D.Ψ r} {w0 : 𝓞 E}

def IsCoord (D : Data E r) (e : D.Ψ → Fin r → Fin r → ℂ) {dim : (E →+* ℂ) → ℕ}
    (w : D.Ψ → Fin r → ℂ) (y : Vsp dim) : Prop :=
  ∀ (j : Idx dim) (τ : D.Ψ) (a : Fin r), (j.1 = τ.1 → (a : ℕ) = j.2 → y j = pr D e w τ a) ∧
    (j.1 = ComplexEmbedding.conjugate τ.1 → (a : ℕ) = D.p0 + j.2 → y j = -conj (pr D e w τ a))

def fr (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x) (τ : D.Ψ) (a : Fin r) : Fin r → ℂ :=
  (√(D.c τ) : ℂ) • FD.col (mat T.e τ) a

variable (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x)

end Coord

section Mirror

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}
  {x : Frame D.Ψ r} {w0 : 𝓞 E}

structure Mirror (A : I2.TorusAt D x) (T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x)
    (σ : Idx T.X.dim ≃ Idx A.T.dim) : Prop where
  rankOne_base_weight_eq_cmTheta : A.w0 = w0
  frame : ∀ τ a, A.e τ a = (√(D.c τ) : ℂ) • FD.col (mat T.e τ) a
  swap : ∀ i, (σ i).1 = ComplexEmbedding.conjugate i.1
  order_neg : ∀ i, i.1 ∈ D.Ψ → ((σ i).2 : ℕ) = i.2
  order_pos : ∀ i, i.1 ∉ D.Ψ → ((σ i).2 : ℕ) + i.2 + 1 = D.p0
  gen : ∀ y, T.s (fun _ => cj A.T σ y) = conj (A.s fun _ => y)

open Classical in

def realExt (A : I2.TorusAt D x) (w : D.Ψ → Fin r → ℂ) : Vsp A.T.dim :=
  WithLp.toLp 2 fun j =>
    if h : j.1 ∈ D.Ψ then pr D A.e w ⟨j.1, h⟩
      ⟨j.2, (j.2.2.trans_eq (A.dim_pos ⟨_, h⟩)).trans_le D.p0_le⟩
    else -conj (pr D A.e w ⟨_, conj_mem D h⟩ ⟨D.p0 + j.2, by
      have h1 := j.2.2.trans_eq ((congrArg A.T.dim (conj_conj_X j.1).symm).trans
        (A.dim_neg ⟨_, conj_mem D h⟩))
      omega⟩)

namespace Mirror

variable {A : I2.TorusAt D x} {T : IndefiniteRowSideFullHecke.TorusThetaNorms.TorusAt D w0 x} {σ : Idx T.X.dim ≃ Idx A.T.dim}
  (h : Mirror A T σ)
include h

end Mirror

end Mirror

section Exist

open TorusCoord TorusAtDataPf IndefiniteRowSideFullHecke.TorusThetaNorms SemicharIndep

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {D : Data E r}

def Perfect (D : Data E r) : Prop :=
  ∀ φ : D.Λ →+ ℤ, ∃ u ∈ D.Λ, ∀ v : D.Λ, (φ v : ℚ) = B D u (v : Fin r → E)

end Exist

end

end GlobalTheory.TorusMirror
