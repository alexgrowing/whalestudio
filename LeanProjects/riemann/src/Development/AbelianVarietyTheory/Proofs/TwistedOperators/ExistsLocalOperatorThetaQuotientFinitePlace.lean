import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRtensOp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.LocalDescent

theorem descend {A A' P : Type*} [AddCommGroup A] [Module ℂ A] [AddCommGroup A'] [Module ℂ A'] [AddCommGroup P]
    [Module ℂ P] (S : Submodule ℂ A) (S' : Submodule ℂ A') (p : A →ₗ[ℂ] P) (p' : A' →ₗ[ℂ] P)
    (hp : S.map p = ⊤) (hp' : S'.map p' = ⊤) (r : A → A → Prop) (r' : A' → A' → Prop)
    (hex : ∀ x ∈ S, ∃ y ∈ S, r x y) (hex' : ∀ x ∈ S', ∃ y ∈ S', r' x y)
    (hlin : ∀ x ∈ S, ∀ z ∈ S, ∀ y w, r x y → r z w → ∀ s t : ℂ, r (s • x + t • z) (s • y + t • w))
    (heq : ∀ x ∈ S, ∀ x' ∈ S', ∀ y ∈ S, ∀ y' ∈ S', r x y → r' x' y' → p x = p' x' → p y = p' y') :
    ∃ T : Module.End ℂ P, (∀ x ∈ S, ∀ y ∈ S, r x y → p y = T (p x)) ∧
      ∀ x ∈ S', ∀ y ∈ S', r' x y → p' y = T (p' x) := by
  have hwd : ∀ x ∈ S, ∀ z ∈ S, ∀ y ∈ S, ∀ w ∈ S, r x y → r z w → p x = p z → p y = p w := by
    intro x hx z hz y hy w hw h1 h2 h3
    obtain ⟨x', hx', e⟩ : p x ∈ S'.map p' := hp' ▸ Submodule.mem_top
    obtain ⟨y', hy', h'⟩ := hex' x' hx'
    rw [heq x hx x' hx' y hy y' hy' h1 h' e.symm, heq z hz x' hx' w hw y' hy' h2 h' (h3.symm.trans e.symm)]
  have hsec : ∀ ξ : P, ∃ x ∈ S, ∃ y ∈ S, p x = ξ ∧ r x y := by
    intro ξ
    obtain ⟨x, hx, e⟩ : ξ ∈ S.map p := hp ▸ Submodule.mem_top
    obtain ⟨y, hy, h⟩ := hex x hx
    exact ⟨x, hx, y, hy, e, h⟩
  choose f hf g hg hfp hfg using hsec
  have hcomb : ∀ (ξ η : P) (s t : ℂ), p (g (s • ξ + t • η)) = s • p (g ξ) + t • p (g η) := by
    intro ξ η s t
    have := hwd _ (hf (s • ξ + t • η)) _ (add_mem (S.smul_mem s (hf ξ)) (S.smul_mem t (hf η))) _ (hg _) _
      (add_mem (S.smul_mem s (hg ξ)) (S.smul_mem t (hg η))) (hfg _)
      (hlin _ (hf ξ) _ (hf η) _ _ (hfg ξ) (hfg η) s t) (by rw [hfp, map_add, map_smul, map_smul, hfp, hfp])
    rw [this, map_add, map_smul, map_smul]
  let T : Module.End ℂ P :=
    { toFun := fun ξ => p (g ξ)
      map_add' := fun ξ η => by simpa using hcomb ξ η 1 1
      map_smul' := fun s ξ => by simpa using hcomb ξ ξ s 0 }
  refine ⟨T, fun x hx y hy h => ?_, fun x hx y hy h => ?_⟩
  · exact hwd x hx _ (hf (p x)) y hy _ (hg _) h (hfg _) (hfp _).symm
  · exact (heq _ (hf (p' x)) x hx _ (hg _) y hy (hfg _) h (hfp _)).symm

theorem acts_comb {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hex : ∀ φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (κ → Fv F v),
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    {φ ψ φ₁ ψ₁ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v)) (hψ : ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    (h₁ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T φ φ₁)
    (h₂ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T ψ ψ₁) (s t : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) T (s • φ + t • ψ) (s • φ₁ + t • ψ₁) := by
  have hs : s • φ + t • ψ ∈ GlobalTheory.WeilM.SB (κ → Fv F v) :=
    add_mem ((GlobalTheory.WeilM.SB _).smul_mem s hφ) ((GlobalTheory.WeilM.SB _).smul_mem t hψ)
  obtain ⟨χ, -, hχ⟩ := hex _ hs
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest κ v
  have e : ∀ α β : (κ → Fv F v) → ℂ, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • α + t • β) R =
      s • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) α R + t • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) β R := by
    intro α β
    funext x
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have key : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) χ R =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (GlobalTheory.AdelicU.evFin F v) (s • φ₁ + t • ψ₁) R := by
    rw [← hχ R (hR _ hs), e, map_add, map_smul, map_smul, h₁ R (hR φ hφ), h₂ R (hR ψ hψ), e]
  have hχe : χ = s • φ₁ + t • ψ₁ := by
    funext y
    have hz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (GlobalTheory.AdelicU.evFin F v) (fun i => GlobalTheory.LatVac.liftV v (y i)) := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    have hRz : R (fun i => GlobalTheory.LatVac.liftV v (y i)) = R 0 := by
      simpa using (hR φ hφ).1 0 _ hz
    have := congrFun key (fun i => GlobalTheory.LatVac.liftV v (y i))
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, GlobalTheory.LatVac.evFin_liftV, hRz] at this
    exact mul_right_cancel₀ hR0 this
  rw [← hχe]
  exact hχ

theorem exists_localOp : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  intro F E _ _ _ _ _ σ a a' Bs Γ Xc om om' R Rf hM v h hh
  have hex := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  have hex' := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ Bs a a' Γ Xc om om' hM.triple v h hh
  exact descend _ _ (Rf.p v) (Rf.p' v) (hM.fin.onto v) (hM.fin.onto' v)
    (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, h))) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, h)))
    hex hex' (fun x hx z hz y w h1 h2 s t => acts_comb v (om (1, h)) hex hx hz h1 h2 s t) (hM.fin.equiv v h hh)

end GlobalTheory.LocalDescent
