import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.ComplementarySeries.Complementary
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductTransposeInverseDualReverseStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsSocleOfOrderFree
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalLanglandsOfIrreducibleAdmissibleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualClassTwistNegStatement
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import CompanionTheory.AutomorphicTheory.HeckeStandardModules.EqZeroOfCompAt

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.SplitWeil Zc Zc.Cos

namespace PositivityTheory.RgGu.NR

namespace HermB

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem nontriv {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V)
    (h : ρ.IsIrreducible) : Nontrivial V := by
  by_contra hV
  rw [not_nontrivial_iff_subsingleton] at hV
  have hne : (⊥ : Subrepresentation ρ) ≠ ⊤ := bot_ne_top
  exact hne (Subrepresentation.toSubmodule_injective (Subsingleton.elim _ _))

theorem congrProd {h N : ℕ} {x y : Fin h → IrrGL k} (e : x = y) (hx : ∑ a, (x a).1 = N) (hy : ∑ a, (y a).1 = N) :
    Nonempty ((prodIrr x hx).Equiv (prodIrr y hy)) := by
  subst e
  exact ⟨Representation.Equiv.refl _⟩

def yy (x : IrrGL k) (s : ℝ) : Fin 2 → IrrGL k := ![x.nu (-(s : ℂ)), x.nu (s : ℂ)]

theorem eqv {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
    {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (e : ρ.Equiv σ) (g : G) (v : V) :
    e (ρ g v) = σ g (e v) :=
  Representation.IntertwiningMap.isIntertwining ρ σ e.toIntertwiningMap g v

theorem theta_contra (hGK : GKLocal k) {N : ℕ} {W : Type} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (GL (Fin N) k) W) (hs : IsSmooth π) (hi : π.IsIrreducible) :
    Nonempty (Representation.Equiv (π.comp (thetaW k N)) (contra π)) := by
  have E := GlobalTheory.CompanionTheory.LSocle.equiv_contra_comp_thetaW hGK (π.comp (thetaW k N))
    (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hs) (by rw [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π]; exact hi)
  rwa [GlobalTheory.CompanionTheory.LSocle.comp_thetaW_thetaW π] at E

theorem hasSesq_of {G V V₁ V₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V]
    [Module ℂ V] [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂] (π : Representation ℂ G V)
    (π₁ : Representation ℂ G V₁) (π₂ : Representation ℂ G V₂) (hi : π.IsIrreducible) (e₁ : π.Equiv π₁)
    (hc : ConjEquiv π₁ π₂) (e₂ : π₂.Equiv (contra π)) : HasSesq π := by
  obtain ⟨φ0, hφb, hφi⟩ := hc
  let Φ : V →ₛₗ[starRingEnd ℂ] smoothPart π.dual :=
    (e₂.toLinearEquiv.toLinearMap.comp φ0).comp e₁.toLinearEquiv.toLinearMap
  have hΦ : ∀ v, Φ v = e₂ (φ0 (e₁ v)) := fun _ => rfl
  have hΦb : Function.Injective Φ := (e₂.toLinearEquiv.injective.comp hφb.1).comp e₁.toLinearEquiv.injective
  have hΦi : ∀ g v, Φ (π g v) = contra π g (Φ v) := fun g v => by rw [hΦ, hΦ, eqv e₁, hφi, eqv e₂]
  haveI := nontriv _ hi
  refine ⟨LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun v w => (Φ w : Module.Dual ℂ V) v)
    (fun v v' w => map_add _ v v') (fun c v w => map_smul _ c v)
    (fun v w w' => by rw [map_add]; rfl) (fun c v w => by rw [map_smulₛₗ]; rfl), ?_, ?_⟩
  · intro hB
    obtain ⟨w, hw⟩ := exists_ne (0 : V)
    refine hw (hΦb ((Subtype.ext (LinearMap.ext fun v => ?_)).trans (map_zero Φ).symm))
    exact LinearMap.congr_fun₂ hB v w
  · intro g v w
    show (Φ (π g w) : Module.Dual ℂ V) (π g v) = (Φ w : Module.Dual ℂ V) v
    rw [hΦi, contra_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]

end HermB

set_option maxHeartbeats 2000000 in
open HermB in
theorem herm_ofB (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (h1 : ConjProd k) (h2 : ConjDual k) : Herm k := by
  intro x hxu s N hd hirr
  have hA := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hGK : GKLocal k := GlobalTheory.T.local_langlands_of_irreducible_admissible hA
  change HasSesq (prodIrr (yy x s) hd)
  change (prodIrr (yy x s) hd).IsIrreducible at hirr

  obtain ⟨E5⟩ := theta_contra hGK (prodIrr (yy x s) hd) (isSmooth_prodIrr _ _) hirr
  obtain ⟨hd', ⟨E4⟩⟩ := GlobalTheory.T.product_transpose_inverse_dual_reverse hA hGK (yy x s) hd

  let c : Fin 2 → ℝ := ![-s, s]
  have hM : ∑ _a : Fin 2, x.1 = N := by
    rw [← hd, Fin.sum_univ_two, Fin.sum_univ_two]; rfl
  let χ : Fin 2 → kˣ →* ℂˣ := fun a => absPow k ((c a : ℝ) : ℂ)
  have hχ : ∀ a, IsSmoothChar (χ a) := fun a => isSmoothChar_absPow _
  let πs : Fin 2 → Representation ℂ (GL (Fin x.1) k) x.2.rep.V := fun a => twist x.rep (detChar (Fin x.1) (χ a))
  let σs : Fin 2 → Representation ℂ (GL (Fin x.1) k) (smoothPart x.rep.dual) :=
    fun a => twist (contra x.rep) (detChar (Fin x.1) (χ a))
  have hsπ : ∀ a, IsSmooth (πs a) := fun a => isSmooth_twist x.2.rep.smooth (hχ a).detChar
  have hiπ : ∀ a, (πs a).IsIrreducible := fun a => isIrreducible_twist x.2.rep.irr _
  have hic : (contra x.rep).IsIrreducible :=
    GlobalTheory.CompanionTheory.ZcDual.isIrreducible_contra hA _ x.2.rep.smooth x.2.rep.irr
  have hsσ : ∀ a, IsSmooth (σs a) := fun a => isSmooth_twist (isSmooth_contra _) (hχ a).detChar
  have hiσ : ∀ a, (σs a).IsIrreducible := fun a => isIrreducible_twist hic _
  have hcj := h1 2 N (fun _ => x.1) hM (fun _ => x.2.rep.V) (fun _ => smoothPart x.rep.dual) πs σs
    (fun a => h2 x.1 x.2.rep.V x.rep x.2.rep.smooth x.2.rep.irr hxu (c a))
  have E1 := prodIrrEquiv hM πs hsπ hiπ
  have E2 := prodIrrEquiv hM σs hsσ hiσ
  have e0 : ((-s : ℝ) : ℂ) = -(s : ℂ) := by push_cast; ring
  have keyπ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist x.rep (detChar (Fin x.1) t)) (isSmooth_twist x.2.rep.smooth ht.detChar)
        (isIrreducible_twist x.2.rep.irr _) = x.tw t ht := by
    intro t ht
    have := IrrGL.tw_of x.rep x.2.rep.smooth x.2.rep.irr t ht
    rw [IrrGL.of_rep] at this
    exact this.symm
  have keyσ : ∀ (t : kˣ →* ℂˣ) (ht : IsSmoothChar t),
      IrrGL.of (twist (contra x.rep) (detChar (Fin x.1) t)) (isSmooth_twist (isSmooth_contra _) ht.detChar)
        (isIrreducible_twist hic _) = (dualCl x).tw t ht := by
    intro t ht
    have := IrrGL.tw_of (contra x.rep) (isSmooth_contra _) hic t ht
    rw [← GlobalTheory.CompanionTheory.ZcDual.dualCl_eq hA x] at this
    exact this.symm
  have fπ : (fun a => IrrGL.of (πs a) (hsπ a) (hiπ a)) = yy x s := by
    funext a
    rw [keyπ _ (hχ a)]
    fin_cases a
    · show x.tw (absPow k ((-s : ℝ) : ℂ)) _ = x.nu (-(s : ℂ))
      simp only [IrrGL.nu, e0]
    · rfl
  have fσ : (fun a => IrrGL.of (σs a) (hsσ a) (hiσ a)) = fun a => dualCl (yy x s (Fin.rev a)) := by
    funext a
    rw [keyσ _ (hχ a)]
    fin_cases a
    · show (dualCl x).tw (absPow k ((-s : ℝ) : ℂ)) _ = dualCl (x.nu (s : ℂ))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (s : ℂ)]
      simp only [IrrGL.nu, e0]
    · show (dualCl x).tw (absPow k ((s : ℝ) : ℂ)) _ = dualCl (x.nu (-(s : ℂ)))
      rw [GlobalTheory.T.dual_class_twist_neg hA x (-(s : ℂ)), neg_neg]
      rfl
  obtain ⟨E0⟩ := congrProd fπ.symm hd hM
  obtain ⟨E3⟩ := congrProd fσ hM hd'
  exact hasSesq_of _ _ _ hirr (E0.trans E1.symm) hcj ((E2.trans E3).trans (E4.symm.trans E5))

end PositivityTheory.RgGu.NR

end
