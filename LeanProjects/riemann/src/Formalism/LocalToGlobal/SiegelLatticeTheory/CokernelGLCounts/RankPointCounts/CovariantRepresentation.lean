import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.KppOffCOfSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish

noncomputable section

open scoped Classical ComplexConjugate
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.KappaOffDiagonal

open Matrix

namespace Formalism.L2.SG.CovariantRepresentation

open Formalism.L2.SG.TermOp.Vanish in

def ShiftCore : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [SigmaFinite μ] [μ.IsMulLeftInvariant]
    (R Γ : Subgroup G) [Countable Γ] (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : G → V) (Ω : Set G) (h : G) (ν : Measure G),
    IsClosed (R : Set G) → Γ ≤ R → (∃ K : Set G, IsCompact K ∧ ∀ r ∈ R, ∃ s ∈ Γ, s * r ∈ K) →
    (∀ r, r ∈ R ↔ h⁻¹ * r * h ∈ R) →
    SigmaFinite ν → ν ≠ 0 → ν (R : Set G)ᶜ = 0 → (∀ K : Set G, IsCompact K → ν K < ⊤) →
    (∀ r ∈ R, ν.map (fun x => r * x) = ν) → ν.map (fun x => x⁻¹) = ν → ν.map (fun x => h⁻¹ * x * h) = ν →
    (∀ r ∈ R, ∀ x, f (r * x) = f x) → IsSF (Γ : Set G) Ω → IntegrableOn f Ω μ →
    ∫ x in Ω, f x ∂μ = ∫ x in (fun x => h⁻¹ * x) '' Ω, f x ∂μ

open Formalism.L2.SG.TermOp.Vanish in

def FixNormC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∀ r, r ∈ Rset t ↔ h⁻¹ * r * h ∈ Rset t

open Formalism.L2.SG.TermOp.Vanish in

def RHaarC : Prop :=
  ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word)
    (t : GTerm X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u')),
    ∀ h ∈ pointwiseStabilizerInfinite X t.rep, ∃ ν : Measure X.B.I.Ginf, SigmaFinite ν ∧ ν ≠ 0 ∧ ν (Rset t)ᶜ = 0 ∧
      (∀ K : Set X.B.I.Ginf, IsCompact K → ν K < ⊤) ∧ (∀ r ∈ Rset t, ν.map (fun x => r * x) = ν) ∧
      ν.map (fun x => x⁻¹) = ν ∧ ν.map (fun x => h⁻¹ * x * h) = ν

section Plumb

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {u u' : D.what₂.Word} {Λ Λ' : Submodule (𝓞 D.host.E) (VS D).V}

theorem rv_ratLink {x : X.B.I.GA} {γ : (VS D).V ≃ₗ[D.host.E] (VS D).V} (hl : RatLink X x γ)
    (v : InfinitePlace X.B.I.F) (y : (VS D).V) :
    uMat (x.1 v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd (γ y)) := by
  obtain ⟨M, -, hx, -, hc⟩ := hl
  rw [hc, hx v]
  unfold rv
  have hw : (fun i => X.B.I.φ v (((M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) *ᵥ X.crd y) i)) =
      (M : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E).map (X.B.I.φ v) *ᵥ
        fun i => X.B.I.φ v (X.crd y i) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [hw, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  congr 1
  by_cases hP : IsUnit (X.B.I.P v).det
  · rw [Matrix.mul_assoc _ (X.B.I.P v), Matrix.mul_nonsing_inv _ hP, Matrix.mul_one]
  · rw [Matrix.nonsing_inv_apply_not_isUnit _ hP]
    simp

theorem basis_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : X.eX a ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.mem_sup_left ?_)
  refine Submodule.subset_span ⟨a, ?_⟩
  show (X.Fu u).e a = X.eX a
  rw [X.Fu_e u]

theorem zu_mem_fixedSubspaceOfRepresentative (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : X.zu u ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative FlagG.Xplus
  refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
  show X.zu u ∈ Submodule.span D.host.E {(X.Fu u).z}
  rw [X.flagZVector u]
  exact Submodule.mem_span_singleton_self _

theorem frq_fl (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') :
    (frq X q).fl = mapFlag q.1.2 q.2.2.1 (X.Fu u') := by
  unfold frq mapLF
  split
  · rfl
  · exact absurd q.2.2.1 ‹_›

theorem ge_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') (a : Fin D.R.rS) : q.1.2 (X.eX a) ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus FlagG.X
  refine Submodule.mem_sup_left (Submodule.subset_span ⟨a, ?_⟩)
  show q.1.2 ((X.Fu u').e a) = q.1.2 (X.eX a)
  rw [X.Fu_e u']

theorem gz_mem_fixedSubspace (q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ') : q.1.2 (X.zu u') ∈ fixedSubspaceOfRepresentative X q := by
  unfold fixedSubspaceOfRepresentative
  refine Submodule.mem_sup_right ?_
  rw [frq_fl]
  unfold FlagG.Xplus
  refine Submodule.mem_sup_right ?_
  show q.1.2 (X.zu u') ∈ Submodule.span D.host.E {q.1.2 (X.Fu u').z}
  rw [X.flagZVector u']
  exact Submodule.mem_span_singleton_self _

theorem fix_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat (h v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  dsimp [pointwiseStabilizerInfinite, Hset] at hh
  first
  | exact hh _ ⟨y, hy, rfl⟩ v
  | exact hh v _ ⟨y, hy, rfl⟩
  | exact hh.2 _ ⟨y, hy, rfl⟩ v
  | exact hh.2 v _ ⟨y, hy, rfl⟩
  | (clear hy; done)

theorem uMat_inv_mul {n : ℕ} {ε : Fin n → Bool} (a : Formalism.REAL.UJ ε) : uMat a⁻¹ * uMat a = 1 := by
  delta uMat
  simp

theorem fix'_rv {q : GCar X u u' (X.Fu u) (X.Fu u') Λ Λ'} {h : X.B.I.Ginf} (hh : h ∈ pointwiseStabilizerInfinite X q)
    {y : (VS D).V} (hy : q.1.2 y ∈ fixedSubspaceOfRepresentative X q) (v : InfinitePlace X.B.I.F) :
    uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) *ᵥ rv X.B.I v (X.crd y) = rv X.B.I v (X.crd y) := by
  have h1 := rv_ratLink q.2.1 v y
  have h2 := fix_rv hh hy v
  have hm : uMat ((q.1.1.1⁻¹ * h * q.1.1.1) v) =
      uMat ((q.1.1.1 v)⁻¹) * uMat (h v) * uMat (q.1.1.1 v) := by
    delta uMat
    simp
  rw [hm, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, h1, h2, ← h1, Matrix.mulVec_mulVec,
    uMat_inv_mul, Matrix.one_mulVec]

theorem inS_of_fix {n r : ℕ} (e : Fin r → Fin n → ℂ) (z : Fin n → ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) : InS e z g := by
  delta InS
  exact ⟨fun a => by simp [Matrix.sub_mulVec, he], by simp [Matrix.sub_mulVec, hz]⟩

theorem rootCoord_fix {n r : ℕ} (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) (a : Fin r) :
    rootCoord ε e f z g a = rootCoord ε e f z 1 a := by
  delta rootCoord
  have hn : g *ᵥ nxt e z a = nxt e z a := by
    delta nxt
    split <;> simp [he, hz]
  rw [hn, Matrix.one_mulVec]

theorem psiR_fix {n r : ℕ} (ε : Fin n → Bool) (gg : ℕ) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ)
    (g : Matrix (Fin n) (Fin n) ℂ) (he : ∀ a, g *ᵥ e a = e a) (hz : g *ᵥ z = z) :
    psiR ε gg e f z g = psiR ε gg e f z 1 := by
  delta psiR
  simp only [rootCoord_fix ε e f z g he hz]

theorem psiInfU_fix (X : HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf)
    (he : ∀ v a, uMat (s v) *ᵥ rv X.B.I v (X.eR a) = rv X.B.I v (X.eR a))
    (hz : ∀ v, uMat (s v) *ᵥ rv X.B.I v (X.zR u) = rv X.B.I v (X.zR u)) :
    X.psiInfU u s = X.psiInfU u 1 := by
  dsimp [HidaSetting.psiInfU]
  delta psiInf
  refine Finset.prod_congr rfl (fun v _ => ?_)
  rw [psiR_fix _ _ _ _ _ _ (he v) (hz v)]
  congr 1

theorem one_mem_SinfU (X : HidaSetting D) (u : D.what₂.Word) : (1 : X.B.I.Ginf) ∈ X.SinfU u := by
  dsimp [HidaSetting.SinfU, Sinf]
  intro v
  exact inS_of_fix _ _ _ (fun a => by delta uMat; simp) (by delta uMat; simp)

theorem psiInfU_one (X : HidaSetting D) (u : D.what₂.Word) : X.psiInfU u 1 = 1 := by
  have h1 : ∀ x, X.Wu u x = X.psiInfU u 1 • X.Wu u x := fun x => by
    have e : X.Wu u (1 * x) = X.psiInfU u 1 • X.piU u 1 (X.Wu u x) := (X.Wu_spec u).1 1 (one_mem_SinfU X u) x
    rwa [one_mul, (X.piU_rep u).1, ContinuousLinearMap.one_apply] at e
  by_contra hne
  have h0 : ∀ x, X.Wu u x = 0 := fun x => by
    have h2 : (1 - X.psiInfU u 1) • X.Wu u x = 0 := by rw [sub_smul, one_smul, ← h1 x, sub_self]
    exact (smul_eq_zero.1 h2).resolve_left (sub_ne_zero.2 (Ne.symm hne))
  have := (X.Wu_spec u).2.2.2.2
  simp [h0] at this

end Plumb

section Main

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.TermOp.Vanish

section Gen

variable {V V' : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [NormedAddCommGroup V']
  [InnerProductSpace ℂ V']

theorem comp_rk1 (A : V →L[ℂ] V) (v : V) (w : V') : A.comp (rk1 v w) = rk1 (A v) w := by
  ext x
  simp [rk1, map_smul]

theorem rankOne_map_left_eq_comp (B : V' ≃ₗᵢ[ℂ] V') (v : V) (w : V') :
    (rk1 v w).comp (B.toContinuousLinearEquiv : V' →L[ℂ] V') = rk1 v (B.symm w) := by
  ext x
  simp only [rk1, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply]
  congr 1
  simp
  rw [← B.inner_map_map (B.symm w) x, LinearIsometryEquiv.apply_symm_apply]

end Gen

variable {D : D7} (X : HidaSetting D)

def piIsoT (u : D.what₂.Word) (s : X.B.I.Ginf) (hs : s ∈ X.SinfU u) : X.Vpi u ≃ₗᵢ[ℂ] X.Vpi u :=
  ((X.piU u s).toLinearMap.isometryOfInner (fun x y => (X.piU_rep u).2.2.1 s hs x y)).toLinearIsometryEquiv rfl

variable {X}

end Main

end Formalism.L2.SG.CovariantRepresentation
