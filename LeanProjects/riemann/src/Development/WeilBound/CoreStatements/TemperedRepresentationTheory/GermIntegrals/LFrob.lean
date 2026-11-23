import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped TensorProduct

noncomputable section

namespace PositivityTheory.Tls2.Ming3.FrobX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {μ : kˣ →* ℂˣ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ : Representation ℂ (GL (Fin r) k) V} {π : Representation ℂ (GL (Fin (r + t)) k) W}

abbrev lrep (t : ℕ) (μ : kˣ →* ℂˣ) (σ : Representation ℂ (GL (Fin r) k) V) :
    Representation ℂ (Levi k (Two (Fin r) (Fin t))) (V ⊗[ℂ] ℂ) :=
  (extTensor σ (detRep (Fin t) μ)).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem lrep_tmul (g : Levi k (Two (Fin r) (Fin t))) (v : V) :
    lrep t μ σ g (v ⊗ₜ[ℂ] (1 : ℂ)) =
      (μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) •
        (σ (g false : GL (Fin r) k) v ⊗ₜ[ℂ] (1 : ℂ)) := by
  change σ (g false) v ⊗ₜ[ℂ] ((μ (Matrix.GeneralLinearGroup.det (g true : GL (Fin t) k)) : ℂ) • (1 : ℂ)) = _
  rw [TensorProduct.tmul_smul]

def fn (π : Representation ℂ (GL (Fin (r + t)) k) W) (ev : W →ₗ[ℂ] V) (w : W) :
    GL (Fin (r + t)) k → V ⊗[ℂ] ℂ :=
  fun h => ev (π h w) ⊗ₜ[ℂ] (1 : ℂ)

theorem fn_law {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W)
    (p : parab k (two (stdSum (rfl : r + t = r + t)))) (g : GL (Fin (r + t)) k) :
    fn π ev w (p * g) =
      ((twist (lrep t μ σ) (deltaHalf k (Two (Fin r) (Fin t)))).comp
        (leviProj k (two (stdSum (rfl : r + t = r + t))))) p (fn π ev w g) := by
  rw [MonoidHom.comp_apply, GlobalTheory.SmGL.twist_apply]
  simp only [PositivityTheory.Tls2.Ming3.FrobX.fn]
  rw [PositivityTheory.Tls2.Ming3.FrobX.lrep_tmul, smul_smul, TensorProduct.smul_tmul', map_mul,
    Module.End.mul_apply, hl p (π g w)]

def elt (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) (w : W) :
    IndSp (two (stdSum (rfl : r + t = r + t))) (lrep t μ σ) :=
  ⟨⟨fn π ev w, fun p g => fn_law hl w p g⟩,
    mem_smoothPart_of_nhds (Filter.mem_of_superset ((hπ w).mem_nhds (by simp)) (by
      intro g hg
      have hg' : π g w = w := hg
      refine Subtype.ext (funext fun x => ?_)
      show fn π ev w (x * g) = fn π ev w x
      simp only [fn, map_mul, Module.End.mul_apply, hg']))⟩

def frobMap (hπ : IsSmooth π) {ev : W →ₗ[ℂ] V} (hl : ParLaw μ σ π ev) :
    π.IntertwiningMap (prod₂ σ (detRep (Fin t) μ)) where
  toFun w := elt hπ hl w
  map_add' w w' := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (w + w')) ⊗ₜ[ℂ] (1 : ℂ) = ev (π h w) ⊗ₜ[ℂ] (1 : ℂ) + ev (π h w') ⊗ₜ[ℂ] (1 : ℂ)
    simp [TensorProduct.add_tmul]))
  map_smul' c w := Subtype.ext (Subtype.ext (funext fun h => by
    show ev (π h (c • w)) ⊗ₜ[ℂ] (1 : ℂ) = c • (ev (π h w) ⊗ₜ[ℂ] (1 : ℂ))
    simp [TensorProduct.smul_tmul']))
  isIntertwining' g := by
    refine LinearMap.ext fun w => Subtype.ext (Subtype.ext (funext fun x => ?_))
    show ev (π x (π g w)) ⊗ₜ[ℂ] (1 : ℂ) = ev (π (x * g) w) ⊗ₜ[ℂ] (1 : ℂ)
    rw [map_mul, Module.End.mul_apply]

end PositivityTheory.Tls2.Ming3.FrobX

namespace PositivityTheory.Tls2.Ming3

theorem frob : FrobSt := by
  intro k _ _ _ _ r t μ V _ _ W _ _ σ π ev hπ hev hl
  refine ⟨PositivityTheory.Tls2.Ming3.FrobX.frobMap hπ hl, fun h => hev ?_⟩
  refine LinearMap.ext fun w => ?_
  have h1 : ev (π 1 w) ⊗ₜ[ℂ] (1 : ℂ) = 0 :=
    congrArg (fun x => x.1.1 (1 : GL (Fin (r + t)) k)) (LinearMap.congr_fun h w)
  rw [map_one, Module.End.one_apply] at h1
  have h2 := congrArg (TensorProduct.rid ℂ V) h1
  rw [TensorProduct.rid_tmul, one_smul, map_zero] at h2
  rw [LinearMap.zero_apply]
  exact h2

end PositivityTheory.Tls2.Ming3
