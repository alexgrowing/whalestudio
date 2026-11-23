import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalDarbouxCoordinatesCompareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardCharacterAlmostUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticGroupGeneratedByElementaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrixStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElementStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChange

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem spAct_one {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)) :
    spAct (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F) w = w := by
  have h1 : (1 : Matrix (κ ⊕ κ) (κ ⊕ κ) F).map (algebraMap F R) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  simp only [spAct, h1, Matrix.one_mulVec]
  rfl

theorem spAct_mul {R : Type} [CommRing R] [Algebra F R] (G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (w : (κ → R) × (κ → R)) :
    spAct (G * G') w = spAct G (spAct G' w) := by
  have h : Sum.elim (spAct G' w).1 (spAct G' w).2 = G'.map (algebraMap F R) *ᵥ Sum.elim w.1 w.2 := by
    funext i; cases i <;> rfl
  conv_rhs => rw [spAct, h]
  simp only [spAct, Matrix.map_mul (f := algebraMap F R), Matrix.mulVec_mulVec]

variable [NumberField F]

theorem hasOp_one (ψ : AddChar (AF F) ℂ) : HasOp (κ := κ) ψ 1 := by
  refine ⟨LinearMap.id, ContinuousLinearMap.id ℂ _, fun _ => LinearMap.id, Function.surjective_id, fun Φ h => h,
    fun w Φ _ => by simp [spAct_one], fun v => Submodule.map_id _, fun v φ _ h => h, fun v w φ _ => by simp [spAct_one],
    Filter.Eventually.of_forall fun v => rfl, fun f φ _ _ => rfl⟩

theorem hasOp_mul {ψ : AddChar (AF F) ℂ} {G G' : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hG : HasOp ψ G) (hG' : HasOp ψ G') :
    HasOp ψ (G * G') := by
  obtain ⟨e, ei, ev, hs, hm, hh, hSB, hi, hl, hind, hp⟩ := hG
  obtain ⟨e', ei', ev', hs', hm', hh', hSB', hi', hl', hind', hp'⟩ := hG'
  have hmem : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev' v φ ∈ SB (κ → Fv F v) := fun v φ hφ => by
    rw [← hSB' v]; exact Submodule.mem_map_of_mem hφ
  refine ⟨e ∘ₗ e', ei.comp ei', fun v => ev v ∘ₗ ev' v, hs.comp hs', fun Φ h => hm _ (hm' _ h), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro w Φ hΦ
    simp only [LinearMap.comp_apply]
    rw [hh' w Φ hΦ, hh _ _ (hm' _ hΦ), spAct_mul]
  · intro v
    rw [Submodule.map_comp, hSB', hSB]
  · intro v φ hφ h0
    exact hi' v φ hφ (hi v _ (hmem v φ hφ) h0)
  · intro v w φ hφ
    simp only [LinearMap.comp_apply]
    rw [hl' v w φ hφ, hl v _ _ (hmem v φ hφ), spAct_mul]
  · filter_upwards [hind, hind'] with v h1 h2
    simp only [LinearMap.comp_apply, h2, h1]
  · intro f φ hφ hφv
    simp only [LinearMap.comp_apply, ContinuousLinearMap.comp_apply]
    rw [hp' f φ hφ hφv, hp _ _ (fun v => hmem v _ (hφ v))]
    filter_upwards [hφv, hind'] with v h1 h2
    rw [h1, h2]

theorem hasOp_of_mem_closure {ψ : AddChar (AF F) ℂ} (hgen : ∀ G ∈ gens (F := F) (κ := κ), HasOp ψ G) :
    ∀ G ∈ Submonoid.closure (gens (F := F) (κ := κ)), HasOp ψ G := fun G hG =>
  Submonoid.closure_induction (fun x hx => hgen x hx) (hasOp_one ψ) (fun _ _ _ _ hx hy => hasOp_mul hx hy) hG

theorem locCo_eq {W : Type} [AddCommGroup W] [Module (AF F) W] {B : W → W → AF F} (c₁ c₂ : Darboux B κ)
    (G : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (h : ∀ w, c₂.e w = spAct G (c₁.e w)) (v : Pl F) (γ : W) :
    GlobalTheory.LatVac.locCo c₂ v γ = spAct G (GlobalTheory.LatVac.locCo c₁ v γ) := by
  have key : ∀ (x : κ ⊕ κ → AF F) (i : κ ⊕ κ), evFin F v ((G.map (algebraMap F (AF F)) *ᵥ x) i) =
      (G.map (algebraMap F (Fv F v)) *ᵥ fun j => evFin F v (x j)) i := by
    intro x i
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, AlgHom.commutes]
  have hs : ∀ a b : κ → AF F, (fun j => evFin F v (Sum.elim a b j)) =
      Sum.elim (fun k => evFin F v (a k)) (fun k => evFin F v (b k)) := by
    intro a b; funext j; cases j <;> rfl
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, h, spAct, key, hs]

theorem acts_unique' (v : Pl F) {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} {R : (κ → AF F) → ℂ} (hR0 : R 0 ≠ 0)
    (hR : Rest (evFin F v) φ R) {T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ}
    (h₁ : Acts (evFin F v) T φ φ₁) (h₂ : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  have e := (h₁ R hR).symm.trans (h₂ R hR)
  funext t
  have h := congrFun e (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hx : R (fun i => GlobalTheory.LatVac.liftV v (t i)) = R 0 := by
    have := hR.1 0 (fun i => GlobalTheory.LatVac.liftV v (t i))
      (fun u hu => by funext i; exact GlobalTheory.LatVac.at_liftV v _ u hu)
    simpa using this
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hx] at h
  exact mul_right_cancel₀ hR0 h

end GlobalTheory.SympChange

open GlobalTheory.SympChange in
theorem GlobalTheory.SympChange.change_of_coordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        ∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOp B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact GlobalTheory.T.weil_operator_for_levi_matrix F B.ψ hB.std hunr hnt _ A hA
    · exact GlobalTheory.T.weil_operator_for_unipotent_matrix F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weil_operator_for_weyl_element F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure⟩ :=
    hasOp_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    rw [locCo_eq M.co co G hGe v γ, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
