import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinMapsOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupWPairVWStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section
namespace GlobalTheory.LocalWeilOps

theorem comm_off_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl F) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ u : AF F, evFin F v u = 0 → ∀ p q : Fin a × Fin (a + a') → AF F,
    ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')),
      om (x, 1) (GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) Φ) = GlobalTheory.WeilM.schr Bs.ψ (u • p, u • q) (om (x, 1) Φ) := by
  intro u hu p q Φ hΦ
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set w := Γ.M.co.e.symm (p, q) with hw
  have he : Γ.M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1) = 0 := hx u hu
  have hact : GlobalTheory.WeilM.actAB (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) ((x, 1) : UA σ Γ.V.J × UA σ Γ.W.J) (u • w) = u • w := by
    have h1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x * (u • w) - u • w = (u • (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat x - 1)) * w := by
      rw [Matrix.smul_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_smul, smul_sub]
    rw [h0, Matrix.zero_mul, sub_eq_zero] at h1
    simp only [GlobalTheory.WeilM.actAB]
    simpa [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.mat] using h1
  have h2 := hW.impl (x, 1) (u • w) Φ hΦ
  simp only [GlobalTheory.WeilM.Darboux.rho, he, hact] at h2
  exact h2

theorem locality_V {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {a a' : ℕ} (Bs : Base F E) (Γ : Geo σ a a') (X : Chars F E) (om : Rep σ Γ.V Γ.W) (om' : Rep σ Γ.V' Γ.W)
    (hTr : IsTriple Bs Γ X om om') (v : Pl F) (x : UA σ Γ.V.J) (hx : x ∈ UAt σ Γ.V (evFin F v)) :
    ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∃ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (x, 1)) φ φ₁ := by
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  set T := om (x, 1) with hTdef
  have hkeep : ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun Φ hΦ => hW.pres (x, 1) Φ hΦ
  have hcomm := comm_off_V Bs Γ X om om' hTr v x hx
  have hfib := GlobalTheory.T.isometry_commuting_heisenberg_acts_fibrewise v Bs.ψ T hTr.base.std (GlobalTheory.T.standardAdelicAddChar_nontrivial_finitePlace Bs.ψ hTr.base.std) hkeep
    (fun μ hμ Φ hΦ => hW.unit μ hμ (x, 1) Φ hΦ) hcomm
  have htr : ∀ u : AF F, evFin F v u = 0 → ∀ p : Fin a × Fin (a + a') → AF F,
      ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), T (fun y => Φ (y + u • p)) = fun y => T Φ (y + u • p) := by
    intro u hu p Φ hΦ
    have h := hcomm u hu p 0 Φ hΦ
    rw [smul_zero, GlobalTheory.WeilLocality.schr_trans, GlobalTheory.WeilLocality.schr_trans] at h
    exact h
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  intro φ hφ
  refine ⟨fun t => (R 0)⁻¹ * T (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R) (fun i => GlobalTheory.LatVac.liftV v (t i)), ?_, ?_⟩
  · have h4 := GlobalTheory.T.adelicSchwartz_restrict_finitePlace_mem_schwartzBruhat v _ (hkeep _ (hR φ hφ).2)
    exact (GlobalTheory.WeilM.SB _).smul_mem (R 0)⁻¹ h4
  · intro r hr
    funext y
    set u : AF F := 1 - GlobalTheory.LatVac.liftV v 1 with hudef
    have hu : evFin F v u = 0 := by simp [hudef, GlobalTheory.LatVac.evFin_liftV]
    set p : Fin a × Fin (a + a') → AF F := fun i => GlobalTheory.LatVac.liftV v (evFin F v (y i)) with hpdef
    have hyp : y + u • (-y) = p := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, Pi.neg_apply, smul_eq_mul, hudef, hpdef]
      rw [← GlobalTheory.WeilLocality.liftV_one_mul]
      ring
    have hpat : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) p := by
      intro u' hu'
      funext i
      exact GlobalTheory.LatVac.at_liftV v _ u' hu'
    set Φ₀ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ R with hΦ₀
    set Φ₁ := GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens (evFin F v) φ r with hΦ₁
    set Φ₂ : (Fin a × Fin (a + a') → AF F) → ℂ := (r y / R 0) • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
    have hm₀ : Φ₀ ∈ GlobalTheory.WeilM.schA F _ := (hR φ hφ).2
    have hm₂ : Φ₂ ∈ GlobalTheory.WeilM.schA F _ := Submodule.smul_mem _ _ (GlobalTheory.T.adelicSchwartzSpace_translate_mem_of_mem _ _ hm₀)
    have hfz : ∀ z, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) z → (Φ₁ - Φ₂) (y + z) = 0 := by
      intro z hz
      have e1 : r (y + z) = r y := hr.1 y z hz
      have e2 : y + z + u • (-y) = p + z := by rw [← hyp]; abel
      have hpz : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (evFin F v) (p + z) := fun u' hu' => by
        rw [smul_add, hpat u' hu', hz u' hu', add_zero]
      have e3 : R (p + z) = R 0 := by simpa using (hR φ hφ).1 0 (p + z) hpz
      have e4 : (fun i => evFin F v ((y + z + u • (-y)) i)) = fun i => evFin F v ((y + z) i) := by
        funext i
        simp [hu]
      simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens]
      rw [e4, e2, e3, e1]
      field_simp
      ring
    have h0 := hfib (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hfz
    rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
    have h2 : T Φ₂ y = (r y / R 0) * T Φ₀ p := by
      rw [hΦ₂, map_smul, htr u hu (-y) Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hyp]
    rw [h0, h2]
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.tens, hpdef]
    field_simp

theorem read_off {F : Type} [Field F] [NumberField F] {κ : Type} (v : Pl F) (R : (κ → AF F) → ℂ) (hR0 : R 0 ≠ 0)
    (hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x) (φ₁ φ₂ : (κ → Fv F v) → ℂ)
    (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext t
  have hz : At (evFin F v) (fun i => GlobalTheory.LatVac.liftV v (t i) : κ → AF F) := by
    intro u' hu'
    funext i
    exact GlobalTheory.LatVac.at_liftV v _ u' hu'
  have e := congrFun h (fun i => GlobalTheory.LatVac.liftV v (t i))
  have hR := hRi 0 _ hz
  rw [zero_add] at hR
  simp only [tens, GlobalTheory.LatVac.evFin_liftV, hR] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_unique {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) {φ : (κ → Fv F v) → ℂ} (hφ : φ ∈ GlobalTheory.WeilM.SB (κ → Fv F v))
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T φ φ₁) (h2 : Acts (evFin F v) T φ φ₂) : φ₁ = φ₂ := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction κ v
  exact read_off v R hR0 (hR φ hφ).1 φ₁ φ₂ ((h1 R (hR φ hφ)).symm.trans (h2 R (hR φ hφ)))

theorem acts_comp {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (v : Pl F)
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₁ : ∀ Φ ∈ GlobalTheory.WeilM.schA F κ, T₁ Φ ∈ GlobalTheory.WeilM.schA F κ)
    {φ φ₁ φ₂ : (κ → Fv F v) → ℂ} (h1 : Acts (evFin F v) T₁ φ φ₁) (h2 : Acts (evFin F v) T₂ φ₁ φ₂) :
    Acts (evFin F v) (T₂ * T₁) φ φ₂ := by
  intro r hr
  have e1 := h1 r hr
  have hr1 : Rest (evFin F v) φ₁ r := ⟨hr.1, e1 ▸ hT₁ _ hr.2⟩
  rw [Module.End.mul_apply, e1, h2 r hr1]

theorem local_ops : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (Γ : Type) [Group Γ] (j : Γ →* UA σ G.V.J × UA σ G.W.J),
      (∀ g, (j g).1 ∈ UAt σ G.V (evFin F v) ∧ (j g).2 ∈ UAt σ G.W (evFin F v)) →
      ∃ ω : Γ →* Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)), ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v))
        (φ₁ : (Fin a × Fin (a + a') → Fv F v) → ℂ),
        Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          φ₁ = ((ω g φ : SB (Fin a × Fin (a + a') → Fv F v)) : (Fin a × Fin (a + a') → Fv F v) → ℂ) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v Γ _ j hj
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil
  have hkeep : ∀ g, ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin a × Fin (a + a')), om g Φ ∈ GlobalTheory.WeilM.schA F _ :=
    fun g Φ hΦ => hW.pres g Φ hΦ
  have hsplit : ∀ g, om (j g) = om ((j g).1, 1) * om (1, (j g).2) := by
    intro g
    rw [← map_mul]
    congr 1
    simp [Prod.mk_mul_mk]
  have hex : ∀ g (φ : SB (Fin a × Fin (a + a') → Fv F v)), ∃ φ₁ ∈ SB (Fin a × Fin (a + a') → Fv F v),
      Acts (evFin F v) (om (j g)) (φ : (Fin a × Fin (a + a') → Fv F v) → ℂ) φ₁ := by
    intro g φ
    obtain ⟨φ₁, h₁, a₁⟩ := GlobalTheory.T.weilRepresentationLocality_unitaryGroupW_pairVW F E σ B a a' G X om om' hTr v (j g).2 (hj g).2 φ φ.2
    obtain ⟨φ₂, h₂, a₂⟩ := locality_V B G X om om' hTr v (j g).1 (hj g).1 φ₁ h₁
    refine ⟨φ₂, h₂, ?_⟩
    rw [hsplit g]
    exact acts_comp v _ _ (hkeep _) a₁ a₂
  choose S hS hA using hex
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (Fin a × Fin (a + a')) v
  have hRi := (hR 0 (Submodule.zero_mem _)).1
  have hadd : ∀ g (φ φ' : SB (Fin a × Fin (a + a') → Fv F v)), S g (φ + φ') = S g φ + S g φ' := by
    intro g φ φ'
    apply read_off v R hR0 hRi
    have e1 := hA g (φ + φ') R (hR _ (φ + φ').2)
    have e2 := hA g φ R (hR _ φ.2)
    have e3 := hA g φ' R (hR _ φ'.2)
    have t1 : ∀ ψ₁ ψ₂ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (ψ₁ + ψ₂) R = tens (evFin F v) ψ₁ R + tens (evFin F v) ψ₂ R := by
      intro ψ₁ ψ₂; funext x; simp [tens, add_mul]
    rw [← e1, Submodule.coe_add, t1, map_add, e2, e3, ← t1]
  have hsmul : ∀ g (c : ℂ) (φ : SB (Fin a × Fin (a + a') → Fv F v)), S g (c • φ) = c • S g φ := by
    intro g c φ
    apply read_off v R hR0 hRi
    have e1 := hA g (c • φ) R (hR _ (c • φ).2)
    have e2 := hA g φ R (hR _ φ.2)
    have t2 : ∀ ψ : (Fin a × Fin (a + a') → Fv F v) → ℂ,
        tens (evFin F v) (c • ψ) R = c • tens (evFin F v) ψ R := by
      intro ψ; funext x; simp [tens, mul_assoc]
    rw [← e1, Submodule.coe_smul, t2, map_smul, e2, ← t2]
  let ωl : Γ → Module.End ℂ (SB (Fin a × Fin (a + a') → Fv F v)) := fun g =>
    { toFun := fun φ => ⟨S g φ, hS g φ⟩
      map_add' := fun φ φ' => Subtype.ext (hadd g φ φ')
      map_smul' := fun c φ => Subtype.ext (hsmul g c φ) }
  have hone : ∀ φ : SB (Fin a × Fin (a + a') → Fv F v), S 1 φ = φ := by
    intro φ
    refine acts_unique v _ φ.2 (hA 1 φ) ?_
    intro r hr
    rw [map_one, map_one]
    rfl
  have hmul : ∀ g h (φ : SB (Fin a × Fin (a + a') → Fv F v)), S (g * h) φ = S g ⟨S h φ, hS h φ⟩ := by
    intro g h φ
    refine acts_unique v _ φ.2 (hA (g * h) φ) ?_
    rw [map_mul, map_mul]
    exact acts_comp v _ _ (hkeep _) (hA h φ) (hA g ⟨S h φ, hS h φ⟩)
  refine ⟨{ toFun := ωl, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · exact LinearMap.ext fun φ => Subtype.ext (hone φ)
  · intro g h
    exact LinearMap.ext fun φ => Subtype.ext (hmul g h φ)
  · intro g φ φ₁
    constructor
    · intro hφ₁
      exact acts_unique v _ φ.2 hφ₁ (hA g φ)
    · rintro rfl
      exact hA g φ

end GlobalTheory.LocalWeilOps
