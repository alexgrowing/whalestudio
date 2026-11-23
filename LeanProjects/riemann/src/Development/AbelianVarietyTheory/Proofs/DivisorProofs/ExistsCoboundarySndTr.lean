import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DerivativeCechCocycleInvariantVectorFieldIsCobouStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionOfNaturalOnAlgebraPointsOfCoverStatement
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.CechKS
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CocInv

variable {K : Type} [Field K] {A : Over (Sp K)} [GrpObj A]

def affVal (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).Hom P where
  ρ := { (GlobalTheory.Points.valMap P.x V.1 (show ⊤ ≤ P.x ⁻¹ᵁ V.1 from h)).hom with
    commutes' := fun r ↦
      (GlobalTheory.Points.valR_eq P.x V.1 h (constFn (A.hom ≫ 𝟙 (Sp K)) V.1 r)).symm.trans
        (GlobalTheory.Points.valR_constFn_of_over _ (algebraMap K P.B) P.x P.w V.1 h r) }
  pt := GlobalTheory.Points.specMap_valMap_fromSpec V.2 P.x h

theorem affVal_ρ (V : A.left.affineOpens) (P : GPt A) (h : P.In V.1) (f : CechDR.Sec (A.hom ≫ 𝟙 (Sp K)) V.1) :
    (affVal V P h).ρ f = valR P.x V.1 f :=
  (GlobalTheory.Points.valR_eq P.x V.1 h f).symm

theorem affVal_comp (V : A.left.affineOpens) {P Q : GPt A} (h : P.In V.1) (φ : P.Hom Q) :
    (affVal V P h).comp φ = affVal V Q (h.map φ) := by
  have e : ((affVal V P h).comp φ).ρ = (affVal V Q (h.map φ)).ρ := by
    ext f
    change φ.ρ ((affVal V P h).ρ f) = _
    rw [affVal_ρ, affVal_ρ, ← φ.pt]
    exact (GlobalTheory.Points.valR_spMap_comp (φ.ρ : P.B →+* Q.B) P.x V.1 h f).symm
  cases h1 : (affVal V P h).comp φ
  cases h2 : affVal V Q (h.map φ)
  rw [h1, h2] at e
  cases e
  rfl

theorem aff_in (V : A.left.affineOpens) : (Pt.aff (A.hom ≫ 𝟙 (Sp K)) V).In V.1 :=
  V.2.fromSpec_preimage_self.ge

def Idx {I : Type} (U : I → A.left.Opens) : Type := {p : I × A.left.affineOpens // p.2.1 ≤ U p.1}

omit [GrpObj A] in

theorem iSup_idx {I : Type} (U : I → A.left.Opens) (hU : ⨆ i, U i = ⊤) : ⨆ a : Idx U, a.1.2.1 = ⊤ := by
  rw [eq_top_iff]
  intro x _
  have hx : x ∈ ⨆ i, U i := hU.ge trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ :=
    A.left.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(i, ⟨V, hV⟩), hVU⟩, hxV⟩

open Classical in

def βa {I : Type} {U : I → A.left.Opens} (β : ∀ P Q : GPt A, P.Hom Q → Q.B) (a : Idx U) :
    PtFn (A.hom ≫ 𝟙 (Sp K)) :=
  fun P ↦ if h : P.In a.1.2.1 then β _ P (affVal a.1.2 P h) else 0

theorem βa_step {I : Type} {U : I → A.left.Opens} {β : ∀ P Q : GPt A, P.Hom Q → Q.B}
    (hβ : ∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) →
      β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) (a : Idx U) {P Q : GPt A} (h : P.In a.1.2.1)
    (φ : P.Hom Q) : βa β a Q = φ.ρ (βa β a P) + β P Q φ := by
  have hQ : Q.In a.1.2.1 := h.map φ
  simp only [βa, dif_pos h, dif_pos hQ]
  rw [← affVal_comp a.1.2 h φ]
  exact hβ _ P Q _ φ ⟨a.1.1, (aff_in a.1.2).mono a.2⟩

open Classical in

theorem exists_coboundary_snd_tr : ∀ (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A], IsAbelianScheme A → ∀ (I : Type) (U : I → A.left.Opens), ⨆ i, U i = ⊤ → ∀ β : ∀ P Q : GPt A, P.Hom Q → Q.B, (∀ (P Q T : GPt A) (φ : P.Hom Q) (ψ : Q.Hom T), (∃ i, P.In (U i)) → β P T (φ.comp ψ) = ψ.ρ (β P Q φ) + β Q T ψ) → ∀ v : epsR K ⟶ A, IsTangent v → ∃ G : PtFn (A.hom ≫ 𝟙 (Sp K)), ∀ (i : I) (V : A.left.affineOpens), V.1 ≤ U i → ∀ (P Q : GPt A) (φ : P.Hom Q), P.In V.1 → TrivSqZeroExt.snd (R := Q.B) (β (P.tr v) (Q.tr v) (φ.tr v)) = G Q - φ.ρ (G P) := by
  intro K _ A _ hA I U hU β hβ v hv
  let W : Idx U → A.left.Opens := fun a ↦ a.1.2.1

  have hsec : ∀ a b : Idx U, ∃ f : Γ(A.left, W a ⊓ W b), ∀ P : GPt A, P.In (W a ⊓ W b) →
      βa β a P - βa β b P = valR P.x (W a ⊓ W b) f := by
    intro a b
    obtain ⟨f, hf⟩ := GlobalTheory.T.exists_section_of_natural_on_algebraPoints_of_cover K A.left (A.hom ≫ 𝟙 (Sp K)) Unit (fun _ ↦ W a ⊓ W b) (W a ⊓ W b)
      (fun _ ↦ le_rfl) (le_iSup (fun _ : Unit ↦ W a ⊓ W b) ()) (fun P ↦ βa β a P - βa β b P) (fun _ P Q φ hP ↦ by
        change βa β a Q - βa β b Q = φ.ρ (βa β a P - βa β b P)
        rw [βa_step hβ a (hP.mono inf_le_left) φ, βa_step hβ b (hP.mono inf_le_right) φ, map_sub]
        ring)
    exact ⟨f, fun P hP ↦ hf () P hP⟩
  choose φab hφab using hsec
  have hcoc : ∀ (a b c : Idx U) (P : GPt A), P.In (W a) → P.In (W b) → P.In (W c) →
      valR P.x _ (φab a b) + valR P.x _ (φab b c) = valR P.x _ (φab a c) := by
    intro a b c P ha hb hc
    rw [← hφab a b P (ha.inf hb), ← hφab b c P (hb.inf hc), ← hφab a c P (ha.inf hc)]
    ring
  obtain ⟨ψ, hψn, hψ⟩ := GlobalTheory.T.derivative_cechCocycle_invariantVectorField_isCoboundary K A hA (Idx U) W (iSup_idx U hU) φab hcoc v hv
  let G : PtFn (A.hom ≫ 𝟙 (Sp K)) := fun P ↦
    if h : ∃ a, P.In (W a) then TrivSqZeroExt.snd (R := P.B) (βa β h.choose (P.tr v)) - ψ h.choose P else 0
  have hG : ∀ (a : Idx U) (P : GPt A), P.In (W a) →
      G P = TrivSqZeroExt.snd (R := P.B) (βa β a (P.tr v)) - ψ a P := by
    intro a P ha
    have h : ∃ a, P.In (W a) := ⟨a, ha⟩
    have hb : P.In (W h.choose) := h.choose_spec
    have e1 := hφab h.choose a (P.tr v) ((hb.inf ha).tr hv)
    have e2 := hψ h.choose a P hb ha
    change βa β h.choose (P.tr v) - βa β a (P.tr v) = valR (P.trx v) _ (φab h.choose a) at e1
    rw [← e1, TrivSqZeroExt.snd_sub] at e2
    simp only [G, dif_pos h]
    linear_combination e2
  refine ⟨G, fun i V hVU P Q φ hP ↦ ?_⟩
  let a : Idx U := ⟨(i, V), hVU⟩
  have hPa : P.In (W a) := hP
  have hQa : Q.In (W a) := hP.map φ
  rw [hG a P hPa, hG a Q hQa, hψn a P Q φ hPa]
  have e := βa_step hβ a (hPa.tr hv) (φ.tr v)
  have e' := congrArg (TrivSqZeroExt.snd (R := Q.B)) e
  change TrivSqZeroExt.snd (R := Q.B) (βa β a (Q.tr v)) =
    TrivSqZeroExt.snd (R := Q.B) (dualAlg φ.ρ (βa β a (P.tr v)) + β (P.tr v) (Q.tr v) (φ.tr v)) at e'
  rw [TrivSqZeroExt.snd_add, snd_dualAlg] at e'
  rw [map_sub]
  linear_combination -e'

end GlobalTheory.CocInv
