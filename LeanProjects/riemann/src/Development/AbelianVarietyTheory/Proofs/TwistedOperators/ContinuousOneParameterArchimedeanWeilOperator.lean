import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchActOne
import GroundTheory.GlobalFields.Adele.Compact

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.ArchUniq GlobalTheory.ArchUniq.Coord GlobalTheory.ArchLine
open scoped Matrix Classical SchwartzMap

noncomputable section

namespace GlobalTheory.ArchLine.OpCont

theorem evI_fin {F : Type} [Field F] [NumberField F] : evI F ((0, 1) : AF F) = 0 :=
  map_zero (InfiniteAdeleRing.ringEquiv_mixedSpace F)

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

end GlobalTheory.ArchLine.OpCont

namespace GlobalTheory.ArchLine

theorem archOp_apply_continuous : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (χX χW : Chr F E) (om : Rep σ X W),
    M.IsWeil ψ χX χW om → (∀ h ∈ UAt σ W (evI F), ∀ f : SInf F (Fin n × Fin d), ∃ f₁ : SInf F (Fin n × Fin d),
      Acts (evI F) (om (1, h)) ⇑f ⇑f₁) → ∀ γ ∈ Lines σ W,
    ∀ (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d → mixedEmbedding.mixedSpace F),
      Continuous fun t : ℝ => archOp om (γ (Multiplicative.ofAdd t)) f x := by
  intro F E _ _ _ _ _ σ n d X W M ψ χX χW om hW hex γ hγ f x
  have hC := hW.2.2

  set r₀ : (Fin n × Fin d → AF F) → ℂ := fun y => GlobalTheory.ArchLine.OpCont.intInd (F := F) (Fin n × Fin d) (fun i => (y i).2)
    with hr₀
  have hr₀1 : ∀ y : Fin n × Fin d → AF F, (∀ i, (y i).2 = 0) → r₀ y = 1 := by
    intro y hy
    have : (fun i => (y i).2) = 0 := funext hy
    simp only [hr₀, this, GlobalTheory.ArchLine.OpCont.intInd]
    rw [Set.indicator_of_mem (show (0 : Fin n × Fin d → FiniteAdeleRing (𝓞 F) F) ∈ Set.pi Set.univ
      fun _ : Fin n × Fin d => (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F : Set (FiniteAdeleRing (𝓞 F) F)) from
        fun i _ => zero_mem (GroundTheory.Global.integralFiniteAdeles (𝓞 F) F))]
    rfl
  have hrest : ∀ g : SInf F (Fin n × Fin d), Rest (evI F) (g : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ := by
    intro g
    refine ⟨fun y z hz => ?_, ?_⟩
    · have : (fun i => ((y + z) i).2) = fun i => (y i).2 := by
        funext i
        change (y i).2 + (z i).2 = (y i).2
        rw [GlobalTheory.ArchLine.OpCont.snd_eq_zero_of_at hz i, add_zero]
      simp only [hr₀, this]
    · exact Submodule.subset_span ⟨g, GlobalTheory.ArchLine.OpCont.intInd _, GlobalTheory.ArchLine.OpCont.intInd_mem _, rfl⟩

  let l : ((Fin n × Fin d → AF F) → ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun Φ => Φ (liftV x), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hl : l ∈ (adeleClass F).adm (Fin n × Fin d) := by
    intro g _
    refine ⟨g 0 • ((BoundedContinuousFunction.evalCLM ℂ x).comp
      (SchwartzMap.toBoundedContinuousFunctionCLM ℂ (Fin n × Fin d → mixedEmbedding.mixedSpace F) ℂ)), fun f' => ?_⟩
    rw [ContinuousLinearMap.smul_apply, smul_eq_mul]
    show pureA F f' g (liftV x) = _
    simp only [pureA, liftV, RingEquiv.apply_symm_apply]
    change f' x * g 0 = g 0 * f' x
    ring
  have hφ : tens (evI F) (f : (Fin n × Fin d → mixedEmbedding.mixedSpace F) → ℂ) r₀ ∈ (adeleClass F).sp (Fin n × Fin d) :=
    (hrest f).2
  have hcont := hC l hl _ hφ
  have hpath : Continuous fun t : ℝ => (((1 : UA σ X.J), γ (Multiplicative.ofAdd t)) : UA σ X.J × UA σ W.J) :=
    continuous_const.prodMk (hγ.1.comp continuous_ofAdd)
  have key := hcont.comp hpath
  convert key using 1
  funext t
  have hh : γ (Multiplicative.ofAdd t) ∈ UAt σ W (evI F) := hγ.2 _
  have ha := acts_archOp om (γ (Multiplicative.ofAdd t)) f (hex _ hh f) r₀ (hrest f)
  simp only [Function.comp_apply]
  show _ = om _ _ (liftV x)
  change _ = om (1, γ (Multiplicative.ofAdd t)) (tens (evI F) (⇑f) r₀) (liftV x)
  rw [ha]
  have h1 : r₀ (liftV x) = 1 := hr₀1 _ fun i => rfl
  have h2 : (fun i => evI F (liftV x i)) = x := by
    funext i; simp [evI, liftV]
  simp only [tens, h1, h2, mul_one]

end GlobalTheory.ArchLine
