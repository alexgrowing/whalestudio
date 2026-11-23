import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsTrigPolynomialAnnihilatingAdelicSchwartzStatement
import GroundTheory.GlobalFields.Adele.Compact
import GroundTheory.GlobalFields.Adele.Approximation

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix

noncomputable section
namespace GlobalTheory.ArchLocality

theorem evI_add {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_mul {F : Type} [Field F] [NumberField F] (a b : AF F) : evI F (a * b) = evI F a * evI F b :=
  map_mul (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

theorem fst_eq_zero {F : Type} [Field F] [NumberField F] {a : AF F} (h : evI F a = 0) : a.1 = 0 :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).map_eq_zero_iff.mp h

theorem loc_chars : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ Φ ∈ schA F κ, ∀ y : κ → AF F, (∀ z, At (evI F) z → Φ (y + z) = 0) →
    ∃ (s : Finset (κ → AF F)) (c : (κ → AF F) → ℂ), (∀ q ∈ s, ∀ i, evI F (q i) = 0) ∧
      ∑ q ∈ s, c q * ψ (y ⬝ᵥ q) = 1 ∧ ∀ x, (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x = 0 := GlobalTheory.T.exists_trigPolynomial_annihilating_adelicSchwartz

theorem snd_eq_zero_of_at {F : Type} [Field F] [NumberField F] {κ : Type} {z : κ → AF F} (hz : At (evI F) z) (i : κ) :
    (z i).2 = 0 := by
  have := congrArg Prod.snd (congrFun (hz (0, 1) evI_fin) i)
  change (((0, 1) : InfiniteAdeleRing F × FiniteAdeleRing (𝓞 F) F).2 * (z i).2) = (0 : AF F).2 at this
  rw [one_mul] at this
  exact this

def intInd {F : Type} [Field F] [NumberField F] (κ : Type) : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ :=
  (Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F))).indicator 1

theorem intInd_mem {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    intInd (F := F) κ ∈ SB (κ → FiniteAdeleRing (𝓞 F) F) := by
  set B := Set.pi Set.univ fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) with hB
  have hO : IsOpen B := isOpen_set_pi Set.finite_univ fun _ _ => GroundTheory.Global.isOpen_integralFiniteAdeles
  have hK : IsCompact B := isCompact_univ_pi fun _ => GroundTheory.Global.isCompact_integralFiniteAdeles F
  have hC : IsClosed B := hK.isClosed
  refine ⟨?_, HasCompactSupport.intro hK fun x hx => Set.indicator_of_notMem hx _⟩
  rw [IsLocallyConstant.iff_exists_open]
  intro x
  by_cases hx : x ∈ B
  · refine ⟨_, hO, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_mem hy, Set.indicator_of_mem hx, Pi.one_apply]
  · refine ⟨_, hC.isOpen_compl, hx, fun y hy => ?_⟩
    simp only [intInd, ← hB, Set.indicator_of_notMem hy, Set.indicator_of_notMem hx]

theorem ref_fun : ∀ {F : Type} [Field F] [NumberField F] (κ : Type) [Fintype κ],
    ∃ r₀ : (κ → AF F) → ℂ, (∀ x : κ → AF F, (∀ i, (x i).2 = 0) → r₀ x = 1) ∧
      ∀ f : SInf F κ, Rest (evI F) (f : (κ → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
  intro F _ _ κ _
  refine ⟨fun x => intInd κ (fun i => (x i).2), fun x hx => ?_, fun f => ⟨fun x z hz => ?_, ?_⟩⟩
  · have : (fun i => (x i).2) = 0 := funext hx
    simp only [this, intInd]
    rw [Set.indicator_of_mem (show (0 : κ → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : κ => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  · have : (fun i => ((x + z) i).2) = fun i => (x i).2 := by
      funext i
      change (x i).2 + (z i).2 = (x i).2
      rw [snd_eq_zero_of_at hz i, add_zero]
    simp only [this]
  · exact Submodule.subset_span ⟨f, intInd κ, intInd_mem κ, rfl⟩

theorem res_arch : ∀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ], ∀ Φ ∈ schA F κ,
    ∃ f : SInf F κ, ∀ t : κ → mixedEmbedding.mixedSpace F,
      Φ (fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (t i), 0) : AF F)) = f t := by
  intro F _ _ κ _ Φ hΦ
  induction hΦ using Submodule.span_induction with
  | mem Φ h =>
    obtain ⟨f, g, _, rfl⟩ := h
    refine ⟨g 0 • f, fun t => ?_⟩
    simp only [pureA, RingEquiv.apply_symm_apply, SchwartzMap.smul_apply, smul_eq_mul]
    rw [mul_comm]
    rfl
  | zero => exact ⟨0, fun t => rfl⟩
  | add Φ₁ Φ₂ _ _ h1 h2 =>
    obtain ⟨f₁, hf₁⟩ := h1
    obtain ⟨f₂, hf₂⟩ := h2
    exact ⟨f₁ + f₂, fun t => by
      show Φ₁ _ + Φ₂ _ = _
      rw [hf₁, hf₂, SchwartzMap.add_apply]⟩
  | smul a Φ _ h =>
    obtain ⟨f, hf⟩ := h
    exact ⟨a • f, fun t => by
      show a • Φ _ = _
      rw [hf, SchwartzMap.smul_apply]⟩

theorem comm_fin {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W)
    (hW : M.IsWeil ψ χX χW om) (h : UA σ W.J) (hh : h ∈ UAt σ W (evI F))
    (u : AF F) (hu : evI F u = 0) (p q : Fin n × Fin d → AF F)
    (Φ : (Fin n × Fin d → AF F) → ℂ) (hΦ : Φ ∈ schA F (Fin n × Fin d)) :
      om (1, h) (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (om (1, h) Φ) := by
  have hS := IsUWeilPair.isUSplitting hW
  set w := M.co.e.symm (p, q) with hw
  have he : M.co.e (u • w) = (u • p, u • q) := by
    rw [LinearEquiv.map_smul, hw, LinearEquiv.apply_symm_apply, Prod.smul_mk]
  have h0 : u • (mat h - 1) = 0 := hh u hu
  have hact : actAB (cA σ) ((1, h) : UA σ X.J × UA σ W.J) (u • w) = u • w := by
    have h1 : (u • w) * (mat h)ᵀ - u • w = w * (u • (mat h - 1))ᵀ := by
      rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, Matrix.transpose_sub, Matrix.transpose_one,
        Matrix.mul_sub, Matrix.mul_one, smul_sub]
    rw [h0, Matrix.transpose_zero, Matrix.mul_zero, sub_eq_zero] at h1
    simp only [actAB]
    simpa [mat] using h1
  have h2 := hS.impl (1, h) (u • w) Φ hΦ
  simp only [Darboux.rho, he, hact] at h2
  exact h2

theorem fibre {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ)
    (T : Module.End ℂ ((κ → AF F) → ℂ))
    (hcomm : ∀ u : AF F, evI F u = 0 → ∀ p q : κ → AF F, ∀ Φ ∈ schA F κ,
      T (schr ψ (u • p, u • q) Φ) = schr ψ (u • p, u • q) (T Φ))
    (Φ : (κ → AF F) → ℂ) (hΦ : Φ ∈ schA F κ) (y : κ → AF F) (hy : ∀ z, At (evI F) z → Φ (y + z) = 0) :
    T Φ y = 0 := by
  obtain ⟨s, c, hs, h1, h0⟩ := loc_chars ψ hψ Φ hΦ y hy
  have hch : ∀ q ∈ s, T (fun x => ψ (x ⬝ᵥ q) * Φ x) = fun x => ψ (x ⬝ᵥ q) * T Φ x := by
    intro q hq
    set u : AF F := (0, 1) with hu
    have hu0 : evI F u = 0 := evI_fin
    have huq : u • q = q := by
      funext i
      have hi := hs q hq i
      have hq1 : (q i).1 = 0 := fst_eq_zero hi
      refine Prod.ext ?_ ?_
      · show (0 : InfiniteAdeleRing F) * (q i).1 = (q i).1
        rw [hq1, zero_mul]
      · show (1 : FiniteAdeleRing (𝓞 F) F) * (q i).2 = (q i).2
        rw [one_mul]
    have e := hcomm u hu0 0 q Φ hΦ
    have hs0 : ∀ G : (κ → AF F) → ℂ, schr ψ (u • (0 : κ → AF F), u • q) G = fun x => ψ (x ⬝ᵥ q) * G x := by
      intro G; funext x; simp [schr, huq]
    rw [hs0, hs0] at e
    exact e
  have hsum : ∀ G : (κ → AF F) → ℂ, (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * G x) =
      ∑ q ∈ s, c q • (fun x => ψ (x ⬝ᵥ q) * G x) := by
    intro G; funext x; simp [Finset.sum_mul, mul_assoc]
  have hT : T (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * T Φ x := by
    rw [hsum, hsum, map_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    rw [map_smul, hch q hq]
  have hz : (fun x => (∑ q ∈ s, c q * ψ (x ⬝ᵥ q)) * Φ x) = 0 := funext h0
  rw [hz, map_zero] at hT
  have := congrFun hT y
  simp only [Pi.zero_apply, h1, one_mul] at this
  exact this.symm

theorem acts_arch : GlobalTheory.FunPr.Hypotheses₂ → ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    IsCMExt F E σ → IsStd ψ → M.IsWeil ψ χX χW om →
    ∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, h)) f f₁ := by
  intro _ F E _ _ _ _ _ σ n d X W M ψ χX χW om _ hψ hW h hh f
  have hS := IsUWeilPair.isUSplitting hW
  set T := om (1, h) with hTdef
  have hpres : ∀ Φ ∈ schA F (Fin n × Fin d), T Φ ∈ schA F (Fin n × Fin d) := fun Φ hΦ => hS.pres (1, h) Φ hΦ
  have hcomm := comm_fin M ψ χX χW om hW h hh
  obtain ⟨r₀, hr₀1, hr₀⟩ := ref_fun (F := F) (Fin n × Fin d)
  set Φ₀ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ with hΦ₀
  have hm₀ : Φ₀ ∈ schA F _ := (hr₀ f).2
  obtain ⟨f₁, hf₁⟩ := res_arch (T Φ₀) (hpres Φ₀ hm₀)
  refine ⟨f₁, fun r hr => ?_⟩
  funext y
  set u : AF F := (0, 1) with hu
  have hu0 : evI F u = 0 := evI_fin
  have htr : ∀ Ψ ∈ schA F (Fin n × Fin d), T (fun w => Ψ (w + u • (-y))) = fun w => T Ψ (w + u • (-y)) := by
    intro Ψ hΨ
    have e := hcomm u hu0 (-y) 0 Ψ hΨ
    have hs0 : ∀ G : (Fin n × Fin d → AF F) → ℂ, schr ψ (u • (-y), u • (0 : Fin n × Fin d → AF F)) G =
        fun w => G (w + u • (-y)) := by
      intro G; funext w; simp [schr]
    rw [hs0, hs0] at e
    exact e
  set Φ₁ := tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r with hΦ₁
  set Φ₂ : (Fin n × Fin d → AF F) → ℂ := r y • (fun w => Φ₀ (w + u • (-y))) with hΦ₂
  have hm₂ : Φ₂ ∈ schA F _ := Submodule.smul_mem _ _ (GlobalTheory.SchwartzTranslation.schA_add_const _ _ hm₀)
  have hz2 : ∀ z : Fin n × Fin d → AF F, At (evI F) z → ∀ i, (z i).2 = 0 := by
    intro z hz i
    have := congrArg Prod.snd (congrFun (hz u hu0) i)
    change (u * z i).2 = (0 : AF F).2 at this
    have e : (u * z i).2 = (z i).2 := one_mul _
    rw [e] at this
    exact this
  have hvan : ∀ z, At (evI F) z → (Φ₁ - Φ₂) (y + z) = 0 := by
    intro z hz
    have e1 : r (y + z) = r y := hr.1 y z hz
    have e2 : (fun i => evI F ((y + z + u • (-y)) i)) = fun i => evI F ((y + z) i) := by
      funext i
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, evI_add, evI_mul, hu0, zero_mul, add_zero]
    have e3 : r₀ (y + z + u • (-y)) = 1 := by
      refine hr₀1 _ fun i => ?_
      change ((y i + z i) + u * -(y i)).2 = 0
      change (y i).2 + (z i).2 + 1 * -(y i).2 = 0
      rw [hz2 z hz i]
      ring
    simp only [Pi.sub_apply, hΦ₂, hΦ₁, hΦ₀, Pi.smul_apply, smul_eq_mul, tens]
    rw [e2, e3, e1]
    ring
  have h0 := fibre ψ hψ T hcomm (Φ₁ - Φ₂) (sub_mem hr.2 hm₂) y hvan
  rw [map_sub, Pi.sub_apply, sub_eq_zero] at h0
  have hy0 : y + u • (-y) = fun i => (((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (evI F (y i)), 0) : AF F) := by
    funext i
    refine Prod.ext ?_ ?_
    · change (y i).1 + 0 * -(y i).1 = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace F (y i).1)
      rw [RingEquiv.symm_apply_apply]
      ring
    · change (y i).2 + 1 * -(y i).2 = 0
      ring
  have h2 : T Φ₂ y = r y * f₁ (fun i => evI F (y i)) := by
    rw [hΦ₂, map_smul, htr Φ₀ hm₀, Pi.smul_apply, smul_eq_mul, hy0, hf₁]
  rw [h0, h2]
  simp only [tens]
  ring

end GlobalTheory.ArchLocality
