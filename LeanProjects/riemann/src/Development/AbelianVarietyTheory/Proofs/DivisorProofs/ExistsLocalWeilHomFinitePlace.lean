import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInertLocalUniformizerImports
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroupStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.KFinLoc
open scoped TensorProduct Matrix

noncomputable section

namespace GlobalTheory.LocalWeilHom

theorem tens_cancel {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ]
    {R : (κ → AF F) → ℂ} (hR : ∀ x z, At (evFin F v) z → R (x + z) = R x) (hR0 : R 0 ≠ 0)
    {φ₁ φ₂ : (κ → Fv F v) → ℂ} (h : tens (evFin F v) φ₁ R = tens (evFin F v) φ₂ R) : φ₁ = φ₂ := by
  funext y
  set z : κ → AF F := fun i => GlobalTheory.LatVac.liftV v (y i) with hz
  have hza : At (evFin F v) z := GlobalTheory.VacAny.at_pi fun i => GlobalTheory.LatVac.at_liftV v _
  have hrx : R (0 + z) = R 0 := hR 0 z hza
  have hy : (fun i => evFin F v ((0 + z) i)) = y := by
    funext i
    simp only [hz, zero_add, GlobalTheory.LatVac.evFin_liftV]
  have e := congrFun h (0 + z)
  simp only [tens] at e
  rw [hrx, hy] at e
  exact mul_right_cancel₀ hR0 e

theorem acts_mul {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ]
    (T₁ T₂ : Module.End ℂ ((κ → AF F) → ℂ)) (hT₂ : ∀ Φ ∈ schA F κ, T₂ Φ ∈ schA F κ)
    {φ φ' φ'' : (κ → Fv F v) → ℂ} (h₂ : Acts (evFin F v) T₂ φ φ') (h₁ : Acts (evFin F v) T₁ φ' φ'') :
    Acts (evFin F v) (T₁ * T₂) φ φ'' := by
  intro r hr
  have e₂ := h₂ r hr
  have hr' : Rest (evFin F v) φ' r := ⟨hr.1, by rw [← e₂]; exact hT₂ _ hr.2⟩
  show T₁ (T₂ (tens (evFin F v) φ r)) = _
  rw [e₂]
  exact h₁ r hr'

theorem exists_hom {F : Type} [Field F] [NumberField F] (v : Pl F) {κ : Type} [Fintype κ] {Γ : Type} [Monoid Γ]
    (ρ : Γ →* Module.End ℂ ((κ → AF F) → ℂ)) (hpres : ∀ γ, ∀ Φ ∈ schA F κ, ρ γ Φ ∈ schA F κ)
    (hex : ∀ γ, ∀ m ∈ SB (κ → Fv F v), ∃ φ₁ ∈ SB (κ → Fv F v), Acts (evFin F v) (ρ γ) m φ₁) :
    ∃ ω : Γ →* Module.End ℂ (SB (κ → Fv F v)), ∀ γ (m : SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      φ₁ ∈ SB (κ → Fv F v) → (Acts (evFin F v) (ρ γ) (m : (κ → Fv F v) → ℂ) φ₁ ↔ ((ω γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = φ₁) := by
  obtain ⟨R, hR0, hR⟩ := GlobalTheory.RestWitness.exists_rest (F := F) κ v
  have hRi : ∀ x z, At (evFin F v) z → R (x + z) = R x := (hR 0 (SB _).zero_mem).1
  choose f hfSB hfA using hex

  have hread : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      Acts (evFin F v) (ρ γ) m φ₁ → ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R :=
    fun γ m hm φ₁ h => h R (hR m hm)
  have huniq : ∀ γ (m : (κ → Fv F v) → ℂ) (hm : m ∈ SB (κ → Fv F v)) (φ₁ : (κ → Fv F v) → ℂ),
      ρ γ (tens (evFin F v) m R) = tens (evFin F v) φ₁ R → f γ m hm = φ₁ := by
    intro γ m hm φ₁ h
    exact tens_cancel v hRi hR0 ((hread γ m hm _ (hfA γ m hm)).symm.trans h)
  have htadd : ∀ φ φ' : (κ → Fv F v) → ℂ, tens (evFin F v) (φ + φ') R =
      tens (evFin F v) φ R + tens (evFin F v) φ' R := by
    intro φ φ'; funext x; simp only [tens, Pi.add_apply, add_mul]
  have htsmul : ∀ (c : ℂ) (φ : (κ → Fv F v) → ℂ), tens (evFin F v) (c • φ) R = c • tens (evFin F v) φ R := by
    intro c φ; funext x; simp only [tens, Pi.smul_apply, smul_eq_mul, mul_assoc]
  let L : Γ → Module.End ℂ (SB (κ → Fv F v)) := fun γ =>
    { toFun := fun m => ⟨f γ m m.2, hfSB γ m m.2⟩
      map_add' := fun m m' => by
        apply Subtype.ext
        show f γ _ _ = f γ m m.2 + f γ m' m'.2
        apply huniq
        rw [Submodule.coe_add, htadd, map_add, hread γ m m.2 _ (hfA γ m m.2),
          hread γ m' m'.2 _ (hfA γ m' m'.2), htadd]
      map_smul' := fun c m => by
        apply Subtype.ext
        show f γ _ _ = c • f γ m m.2
        apply huniq
        rw [Submodule.coe_smul, htsmul, map_smul, hread γ m m.2 _ (hfA γ m m.2), htsmul] }
  have hL : ∀ γ (m : SB (κ → Fv F v)), ((L γ m : SB (κ → Fv F v)) : (κ → Fv F v) → ℂ) = f γ m m.2 := fun _ _ => rfl
  refine ⟨{ toFun := L, map_one' := ?_, map_mul' := ?_ }, ?_⟩
  · apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    apply huniq
    rw [map_one]; rfl
  · intro γ γ'
    apply LinearMap.ext; intro m
    apply Subtype.ext
    rw [hL]
    show f (γ * γ') m m.2 = f γ (f γ' m m.2) (hfSB γ' m m.2)
    apply huniq
    rw [map_mul]
    exact acts_mul v (ρ γ) (ρ γ') (hpres γ') (hfA γ' m m.2) (hfA γ _ (hfSB γ' m m.2)) R (hR m m.2)
  · intro γ m φ₁ _
    show _ ↔ f γ m m.2 = φ₁
    constructor
    · intro h; exact huniq γ m m.2 φ₁ (hread γ m m.2 φ₁ h)
    · intro h; rw [← h]; exact hfA γ m m.2

end GlobalTheory.LocalWeilHom

namespace GlobalTheory.LocalWeilHom

theorem local_weil_hom : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ (v : Pl F) (w : HeightOneSpectrum (𝓞 E)), Formalism.UG.IsInertAt F E v w → v ∉ X.T →
    ∀ {L : Type} [Field L] (σL : L →+* L) (JS : GL (Fin a') L) (JT : GL (Fin (a + a')) L)
      (ιS : Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) →* UA σ G.V'.J)
      (ιT : Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →* UA σ G.W.J),
      (∀ g, ιS g ∈ UAt σ G.V' (evFin F v)) → (∀ h, ιT h ∈ UAt σ G.W (evFin F v)) →
    ∃ ω : (Formalism.UG.UJ σL (JS : Matrix (Fin a') (Fin a') L) × Formalism.UG.UJ σL (JT : Matrix (Fin (a + a')) (Fin (a + a')) L) →*
        Module.End ℂ (SB (Fin a' × Fin (a + a') → Fv F v))),
      (∀ g h (m : SB (Fin a' × Fin (a + a') → Fv F v)) (φ₁ : (Fin a' × Fin (a + a') → Fv F v) → ℂ),
        φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v) →
        (Acts (evFin F v) (om' (ιS g, ιT h)) (m : (Fin a' × Fin (a + a') → Fv F v) → ℂ) φ₁ ↔
          ((ω (g, h) m : SB (Fin a' × Fin (a + a') → Fv F v)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) = φ₁)) := by
  intro F E _ _ _ _ _ σ B a a' G X om om' hTr v w _ _ L _ σL JS JT ιS ιT hιS hιT
  have hW := GlobalTheory.WeilM.IsUWeilPair.isUSplitting hTr.weil'
  let ρ := om'.comp (MonoidHom.prodMap ιS ιT)
  have hρ : ∀ g h, ρ (g, h) = om' (ιS g, ιT h) := fun _ _ => rfl
  have hpres : ∀ γ, ∀ Φ ∈ schA F (Fin a' × Fin (a + a')), ρ γ Φ ∈ schA F (Fin a' × Fin (a + a')) :=
    fun γ Φ hΦ => hW.pres _ Φ hΦ
  have hex : ∀ γ, ∀ m ∈ SB (Fin a' × Fin (a + a') → Fv F v),
      ∃ φ₁ ∈ SB (Fin a' × Fin (a + a') → Fv F v), Acts (evFin F v) (ρ γ) m φ₁ := by
    rintro ⟨g, h⟩ m hm
    obtain ⟨φ₁, hφ₁, hA₁⟩ := GlobalTheory.T.weilRepresentation_localAtFinitePlace_unitaryGroupW F E σ B a a' G X om om' hTr v (ιT h) (hιT h) m hm
    obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hTr v (ιS g) (hιS g)
    refine ⟨S φ₁, (hS φ₁ hφ₁).1, ?_⟩
    have hsplit : ρ (g, h) = om' (ιS g, 1) * om' (1, ιT h) := by
      rw [hρ, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    rw [hsplit]
    exact acts_mul v _ _ (fun Φ hΦ => hW.pres _ Φ hΦ) hA₁ (hS φ₁ hφ₁).2
  obtain ⟨ω, hω⟩ := exists_hom v ρ hpres hex
  exact ⟨ω, fun g h m φ₁ hφ₁ => hω (g, h) m φ₁ hφ₁⟩

end GlobalTheory.LocalWeilHom

end
