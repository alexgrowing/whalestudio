import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FromBlocksMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StarMemAdelicSchwartzSpaceNumberField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilRepresentationLocalityFinitePlaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLatticStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumConditionStableLatticeStabilizerIneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceDoubledVacuumConditionUniqueStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.InertDblLine

theorem line : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w →
    ∀ (dd : Darboux (symp (cA σ) (-1) (incM F G.V'.J) (dbl (incM F G.W.J))) (Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')))
      (omd : UG (cA σ) (dbl (incM F G.W.J)) →* Module.End ℂ ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a') → AF F) → ℂ)),
      IsDblCoord (cA σ) (-1) (incM F G.V'.J) (incM F G.W.J) G.M'.co dd →
      IsUWeilSplit (cA σ) (adeleClass F) B.ψ (-1) (incM F G.V'.J) (dbl (incM F G.W.J)) dd X.α (diagCols (Fin (a + a'))) omd →
    ∀ R : (Fin a' × Fin (a + a') → AF F) → ℂ, Rest (evFin F v) (G.M'.vac v) R →
    ∀ g ∈ GlobalTheory.InertDbl.KAtD σ G.W v, ∃ c : ℂ, omd g (GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R)) =
      c • GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w hw dd omd hdd hsp R hR g hg
  obtain ⟨hvSB, hv0, θ, hθ, hvac⟩ := hTr.geo.hM'.vac v
  set φ₀ := boxFun (G.M'.vac v) (fun x => star (G.M'.vac v x)) with hφ₀
  set r₀ : ((Fin a' × Fin (a + a') ⊕ Fin a' × Fin (a + a')) → AF F) → ℂ := boxFun R (fun x => star (R x)) with hr₀
  have hΦ : GlobalTheory.InertDbl.dblFun (tens (evFin F v) (G.M'.vac v) R) = tens (evFin F v) φ₀ r₀ := by
    funext x
    show (_ * _) * star (_ * _) = (_ * _) * (_ * _)
    rw [star_mul']
    exact mul_mul_mul_comm _ _ _ _
  have hstar : (fun x => star (G.M'.vac v x)) ∈ SB (Fin a' × Fin (a + a') → Fv F v) :=
    ⟨hvSB.1.comp star, hvSB.2.comp_left (g := star) (star_zero ℂ)⟩
  have hφ₀SB : φ₀ ∈ SB _ := GlobalTheory.BoxSpan.boxFun_mem_SB' hvSB hstar
  have hRest : Rest (evFin F v) φ₀ r₀ := by
    refine ⟨fun x z hz => ?_, ?_⟩
    · have hl : At (evFin F v) (z ∘ Sum.inl) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inl i)
      have hr : At (evFin F v) (z ∘ Sum.inr) := fun u hu => by
        funext i; exact congrFun (hz u hu) (Sum.inr i)
      simp only [hr₀, boxFun]
      rw [show (x + z) ∘ Sum.inl = x ∘ Sum.inl + z ∘ Sum.inl from rfl,
        show (x + z) ∘ Sum.inr = x ∘ Sum.inr + z ∘ Sum.inr from rfl, hR.1 _ _ hl, hR.1 _ _ hr]
    · rw [← hΦ]
      exact GlobalTheory.SchwartzBox.boxFun_mem_schA F _ _ _ hR.2 _ (GlobalTheory.SchAConj.star_mem_schA F _ _ hR.2)
  obtain ⟨φ₁, hφ₁, hact⟩ := GlobalTheory.T.doubledWeilRepresentation_locality_finitePlace F E σ B a a' G X om om' hTr v dd omd hsp g hg.1 φ₀ hφ₀SB
  have h₀ := GlobalTheory.T.doubledVacuum_twistedVacuumCondition_doubledLattice F E σ B a a' G X om om' hTr v dd hdd θ hθ hvac
  have h₁ := GlobalTheory.T.doubledVacuumCondition_stable_latticeStabilizer_inert F E σ B a a' G X om om' hTr v dd omd hsp θ hθ g hg φ₀ hφ₀SB φ₁ hφ₁ h₀ hact
  obtain ⟨c, hc⟩ := GlobalTheory.T.inertPlace_doubledVacuumCondition_unique F E σ B a a' G X om om' hTr v w hw dd hdd θ hθ hvac φ₁ hφ₁ h₁
  refine ⟨c, ?_⟩
  rw [hΦ, hact r₀ hRest, hc]
  funext x
  simp only [tens, Pi.smul_apply, smul_eq_mul]
  ring

end GlobalTheory.InertDblLine
