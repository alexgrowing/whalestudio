import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.CentralProd2
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StdQuotGenericOfStdSubGeneric
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralCharacterEqProdSupercuspidalSupport

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL

namespace PositivityTheory.RgUd.Exp.Facts

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem isGeneric_comp_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (h : IsGeneric π) : IsGeneric (π.comp (Zc.Cos.thetaW k N)) := by
  obtain ⟨ψ, hc, h1, hg⟩ := h
  refine ⟨ψ⁻¹, ?_, inv_ne_one.mpr h1, ?_⟩
  · have e : (⇑(ψ⁻¹) : k → Circle) = fun x => ψ (-x) := by
      funext x
      exact AddChar.inv_apply ψ x
    rw [e]
    exact hc.comp continuous_neg
  · unfold IsGenericFor TwJacquet at hg ⊢
    rw [Submodule.Quotient.nontrivial_iff] at hg ⊢
    intro htop
    apply hg
    rw [eq_top_iff] at htop ⊢
    refine htop.trans ?_
    unfold twKer
    refine Submodule.span_le.mpr ?_
    rintro w ⟨n, v, rfl⟩
    apply Submodule.subset_span
    refine ⟨⟨Zc.Cos.thetaW k N n, GlobalTheory.CompanionTheory.StdQuot.thetaW_mem_unipB n.2⟩, v, ?_⟩
    rw [GlobalTheory.CompanionTheory.StdQuot.whitChar_thetaW, ← GlobalTheory.CompanionTheory.StdQuot.whitChar_inv]
    rfl

theorem thetaW_scalar (N : ℕ) (z : kˣ) :
    Zc.Cos.thetaW k N (GeneralLinearGroup.scalar (Fin N) z) = GeneralLinearGroup.scalar (Fin N) z⁻¹ := by
  ext i j
  rw [GlobalTheory.CompanionTheory.StdQuot.thetaW_apply, ← map_inv]
  simp [GeneralLinearGroup.scalar]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [Matrix.diagonal_apply, hij, Ne.symm hij]

theorem hasCentralChar_comp_thetaW {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (ω : kˣ →* ℂˣ) (h : HasCentralChar π ω) :
    HasCentralChar (π.comp (Zc.Cos.thetaW k N)) ω⁻¹ := by
  intro z v
  rw [MonoidHom.comp_apply, thetaW_scalar, h z⁻¹ v, MonoidHom.inv_apply, map_inv]

theorem hasCentralChar_prodIrr_two (x y : IrrGL k) (N : ℕ) (hd : ∑ a, (![x, y] a).1 = N) (ω ω' : kˣ →* ℂˣ)
    (hx : HasCentralChar x.rep ω) (hy : HasCentralChar y.rep ω') :
    HasCentralChar (prodIrr ![x, y] hd) (ω * ω') := by
  have key := GlobalTheory.CentralSupport.hasCentralChar_multiProd_prod
    (stdBlocks (fun a : Fin 2 => (![x, y] a).fst) hd) (fun a : Fin 2 => (![x, y] a).rep) ![ω, ω']
    (by
      intro a
      fin_cases a
      · exact hx
      · exact hy)
  rw [Fin.prod_univ_two] at key
  exact key

end PositivityTheory.RgUd.Exp.Facts

namespace PositivityTheory.RgUd.Exp

theorem thetaFacts (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    ThetaFacts k :=
  ⟨fun _ _ _ _ π h => Facts.isGeneric_comp_thetaW π h,
    fun _ _ _ _ π ω h => Facts.hasCentralChar_comp_thetaW π ω h⟩

theorem centralProd2 (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    CentralProd2 k :=
  fun x y N hd ω ω' hx hy => Facts.hasCentralChar_prodIrr_two x y N hd ω ω' hx hy

end PositivityTheory.RgUd.Exp

end
