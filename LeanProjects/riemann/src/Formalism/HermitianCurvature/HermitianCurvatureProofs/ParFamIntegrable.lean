import Formalism.HermitianCurvature.HermitianCurvatureProofs.FrameTransport

open MeasureTheory Filter Topology Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
open scoped ContDiff

noncomputable section

namespace Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra

section Fam

variable {k ρ : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {Par : Type} [NormedAddCommGroup Par]
  [NormedSpace ℝ Par] {U₀ : Set (Par × Mt k ρ)}

theorem parFam_add {f g : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) (hg : PBI.ParFam k ρ U₀ g) :
    PBI.ParFam k ρ U₀ (fun q => f q + g q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  obtain ⟨U', F', hU', hqU', hF', hgF⟩ := hg q₀ hq hG
  exact ⟨U ∩ U', fun q => F q + F' q, hU.inter hU', ⟨hqU, hqU'⟩,
    (hF.mono Set.inter_subset_left).add (hF'.mono Set.inter_subset_right),
    fun q hq hG => by show f q + g q = F q + F' q; rw [hfF q hq.1 hG, hgF q hq.2 hG]⟩

theorem parFam_smul (a : ℂ) {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) :
    PBI.ParFam k ρ U₀ (fun q => a • f q) := by
  intro q₀ hq hG
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf q₀ hq hG
  exact ⟨U, fun q => a • F q, hU, hqU, hF.const_smul a, fun q hq hG => by show a • f q = a • F q; rw [hfF q hq hG]⟩

theorem parFam_zero : PBI.ParFam k ρ U₀ (fun _ => (0 : E)) := fun q₀ _ _ =>
  ⟨Set.univ, fun _ => 0, isOpen_univ, Set.mem_univ _, contDiffOn_const, fun _ _ _ => rfl⟩

theorem parFam_sum {ι : Type} (s : Finset ι) {f : ι → Par × Mt k ρ → E}
    (hf : ∀ i ∈ s, PBI.ParFam k ρ U₀ (f i)) : PBI.ParFam k ρ U₀ (fun q => ∑ i ∈ s, f i q) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (parFam_zero (E := E) (U₀ := U₀))
  | insert a s ha ih =>
    have h1 := hf a (Finset.mem_insert_self a s)
    have h2 := ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))
    have := parFam_add h1 h2
    simpa [Finset.sum_insert ha] using this

theorem parFam_contAt {f : Par × Mt k ρ → E} (hf : PBI.ParFam k ρ U₀ f) {Z : Par} {y : Mt k ρ} (hq : (Z, y) ∈ U₀)
    (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) : ContinuousAt (fun Z' => f (Z', y)) Z := by
  obtain ⟨U, F, hU, hqU, hF, hfF⟩ := hf (Z, y) hq hy
  have hci : Continuous fun Z' : Par => ((Z', y) : Par × Mt k ρ) := continuous_id.prodMk continuous_const
  have hm : {Z' | (Z', y) ∈ U} ∈ 𝓝 Z := hci.continuousAt.preimage_mem_nhds (hU.mem_nhds hqU)
  have hcF : ContinuousAt (fun Z' => F (Z', y)) Z :=
    ContinuousAt.comp (g := F) (f := fun Z' : Par => ((Z', y) : Par × Mt k ρ)) (x := Z)
      (hF.continuousOn.continuousAt (hU.mem_nhds hqU)) hci.continuousAt
  refine hcF.congr ?_
  filter_upwards [hm] with Z' hZ'
  exact (hfF (Z', y) hZ' hy).symm

theorem parFam_integrable [MeasurableSpace Par] [BorelSpace Par] {f : Par × Mt k ρ → E}
    (hf : PBI.ParFam k ρ U₀ f) {ν : Measure Par} [IsFiniteMeasure ν] {Kp : Set Par} (hK : IsCompact Kp)
    (hν : ν Kpᶜ = 0) {y : Mt k ρ} (hy : Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ)) (hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀) :
    Integrable (fun Z => f (Z, y)) ν := by
  have hc : ContinuousOn (fun Z => f (Z, y)) Kp := fun Z hZ =>
    (parFam_contAt hf (hKU Z hZ) hy).continuousWithinAt
  have hI : IntegrableOn (fun Z => f (Z, y)) Kp ν := hc.integrableOn_compact hK
  have hae : ∀ᵐ Z ∂ν, Z ∈ Kp := by
    rw [ae_iff]
    simpa [Set.compl_def] using hν
  rwa [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hae] at hI

end Fam

section Cls

variable {k ρ : ℕ} {z z' : Fin (2 * ρ + k + 1) → ℂ} {Wp Wq : Type} [NormedAddCommGroup Wp]
  [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] {π : Q.Mx k ρ → (Wp →L[ℂ] Wp)}
  {π' : Q.Mx k ρ → (Wq →L[ℂ] Wq)}

def Rep {Par : Type} (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)) : Prop :=
  ∀ Z c y, Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → (Ψ Z : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = Ψf Z y

def GGpos (k ρ : ℕ) (z z' : Fin (2 * ρ + k + 1) → ℂ) : Set (Mt k ρ) := {y | 0 < Q.GGl k ρ z z' (Matrix.of y)}

variable (z z' π π') in

def Good (A : Module.End ℂ (Q.RadSp k ρ z z' π π')) : Prop :=
  ∀ (Par : Type) [NormedAddCommGroup Par] [NormedSpace ℝ Par] [FiniteDimensional ℝ Par] [MeasurableSpace Par]
    [BorelSpace Par] (U₀ : Set (Par × Mt k ρ)), IsOpen U₀ → U₀ ⊆ Set.univ ×ˢ GGpos k ρ z z' →
  ∀ (Ψ : Par → Q.RadSp k ρ z z' π π') (Ψf : Par → Mt k ρ → (Wq →L[ℂ] Wp)), Rep Ψ Ψf →
    PBI.ParFam k ρ U₀ (fun q => Ψf q.1 q.2) →
  ∃ Φf : Par → Mt k ρ → (Wq →L[ℂ] Wp), Rep (fun Z => A (Ψ Z)) Φf ∧ PBI.ParFam k ρ U₀ (fun q => Φf q.1 q.2) ∧
    (∀ K : Set (Par × Mt k ρ), (∀ q, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ K → Ψf q.1 q.2 = 0) →
      ∀ q ∈ U₀, Matrix.of q.2 ∈ Q.Glev k ρ (Fin.last ρ) → q ∉ closure K → Φf q.1 q.2 = 0) ∧
    ∀ (ν : Measure Par) [IsFiniteMeasure ν] (Kp : Set Par), IsCompact Kp → ν Kpᶜ = 0 →
    ∀ (Ψi : Q.RadSp k ρ z z' π π') (y : Mt k ρ) (V : Set (Mt k ρ)), IsOpen V → y ∈ V →
      Matrix.of y ∈ Q.Glev k ρ (Fin.last ρ) → Kp ×ˢ V ⊆ U₀ →
      (∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Ψf Z y' ∂ν) →
      ∀ c, (A Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y) = ∫ Z, Φf Z y ∂ν

theorem good_id : Good z z' π π' (LinearMap.id : Module.End ℂ (Q.RadSp k ρ z z' π π')) := by
  intro Par _ _ _ _ _ U₀ _ _ Ψ Ψf hR hF
  refine ⟨Ψf, fun Z c y hy => hR Z c y hy, hF, fun K hK q _ hG hq => hK q hG (fun h => hq (subset_closure h)),
    fun ν _ Kp _ _ Ψi y V _ hyV hyG _ hi c => hi c y hyV hyG⟩

theorem good_comp {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A * B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hA Par U₀ hU₀ hUpos (fun Z => B (Ψ Z)) Φ₁ hR₁ hF₁
  refine ⟨Φ₂, fun Z c y hy => hR₂ Z c y hy, hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · have hK' : ∀ q', Matrix.of q'.2 ∈ Q.Glev k ρ (Fin.last ρ) → q' ∉ closure K ∪ U₀ᶜ → Φ₁ q'.1 q'.2 = 0 := by
      intro q' hG' hq'
      simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not] at hq'
      exact hS₁ K hK q' hq'.2 hG' hq'.1
    refine hS₂ _ hK' q hq hG ?_
    rw [closure_union, hU₀.isClosed_compl.closure_eq, closure_closure]
    simp only [Set.mem_union, Set.mem_compl_iff, not_or, not_not]
    exact ⟨hqK, hq⟩
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hi' : ∀ c y', y' ∈ V → Matrix.of y' ∈ Q.Glev k ρ (Fin.last ρ) →
        (B Ψi : Q.Fn k ρ (Wq →L[ℂ] Wp)) c (Matrix.of y') = ∫ Z, Φ₁ Z y' ∂ν :=
      fun c y' hy' hG' => hW₁ ν Kp hKp hν Ψi y' V hV hy' hG' hKV hi c
    exact hW₂ ν Kp hKp hν (B Ψi) y V hV hyV hyG hKV hi' c

theorem good_add {A B : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) (hB : Good z z' π π' B) :
    Good z z' π π' (A + B) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₂, hR₂, hF₂, hS₂, hW₂⟩ := hB Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => Φ₁ Z y + Φ₂ Z y, fun Z c y hy => ?_, parFam_add hF₁ hF₂, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hR₁ Z c y hy, hR₂ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, hS₂ K hK q hq hG hqK, add_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    have hKU : ∀ Z ∈ Kp, (Z, y) ∈ U₀ := fun Z hZ => hKV ⟨hZ, hyV⟩
    simp only [LinearMap.add_apply, Submodule.coe_add, Pi.add_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, hW₂ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c,
      ← integral_add (parFam_integrable hF₁ hKp hν hyG hKU) (parFam_integrable hF₂ hKp hν hyG hKU)]

theorem good_smul (a : ℂ) {A : Module.End ℂ (Q.RadSp k ρ z z' π π')} (hA : Good z z' π π' A) :
    Good z z' π π' (a • A) := by
  intro Par _ _ _ _ _ U₀ hU₀ hUpos Ψ Ψf hR hF
  obtain ⟨Φ₁, hR₁, hF₁, hS₁, hW₁⟩ := hA Par U₀ hU₀ hUpos Ψ Ψf hR hF
  refine ⟨fun Z y => a • Φ₁ Z y, fun Z c y hy => ?_, parFam_smul a hF₁, fun K hK q hq hG hqK => ?_, ?_⟩
  · simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hR₁ Z c y hy]
  · simp only [hS₁ K hK q hq hG hqK, smul_zero]
  · intro ν _ Kp hKp hν Ψi y V hV hyV hyG hKV hi c
    simp only [LinearMap.smul_apply, Submodule.coe_smul, Pi.smul_apply]
    rw [hW₁ ν Kp hKp hν Ψi y V hV hyV hyG hKV hi c, integral_smul]

variable (z z' π π') in

def PGood (x : Q.Pr (Q.RadSp k ρ z z' π π')) : Prop := Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop

variable (z z' π π') in

def goodAlg : StarSubalgebra ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) where
  carrier := {x | PGood z z' π π' x}
  mul_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_comp hx1 hy1, good_comp hy2 hx2⟩
  add_mem' := by
    rintro x y ⟨hx1, hx2⟩ ⟨hy1, hy2⟩
    exact ⟨good_add hx1 hy1, good_add hx2 hy2⟩
  algebraMap_mem' := by
    intro a
    have e1 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1 = a • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) a = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ a
    have e2 : (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop = (starRingEnd ℂ a) • LinearMap.id := by
      show algebraMap ℂ (Module.End ℂ (Q.RadSp k ρ z z' π π')) (starRingEnd ℂ a) = _
      exact Module.algebraMap_end_eq_smul_id _ _ _ _
    refine ⟨?_, ?_⟩
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).1
      rw [e1]; exact good_smul a good_id
    · show Good z z' π π' (algebraMap ℂ (Q.Pr (Q.RadSp k ρ z z' π π')) a).2.unop
      rw [e2]; exact good_smul _ good_id
  star_mem' := by
    rintro x ⟨hx1, hx2⟩
    exact ⟨hx2, hx1⟩

theorem mem_goodAlg {x : Q.Pr (Q.RadSp k ρ z z' π π')} :
    x ∈ goodAlg z z' π π' ↔ Good z z' π π' x.1 ∧ Good z z' π π' x.2.unop := Iff.rfl

theorem good_mkP {X Xs : Module.End ℂ (Q.RadSp k ρ z z' π π')} (h1 : Good z z' π π' X) (h2 : Good z z' π π' Xs) :
    Q.mkP X Xs ∈ goodAlg z z' π π' := ⟨h1, h2⟩

end Cls

end Formalism.FourierDecayAlt.P.ParameterFamilyAlgebra
