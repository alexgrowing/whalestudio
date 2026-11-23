import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsTerRest
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.ImportsRestFurther
import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.PCutRegular
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (mIdealOver)

section

variable {k : Type} [Field k] {N m : ℕ}

theorem weight_mapDomain_base (e : Fin (N + 1) →₀ ℕ) :
    Finsupp.weight (NumbersDVR.blockWeight (graphIdx N m))
        (Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e) =
      Sum.elim (fun _ => e.degree) (fun _ => 0) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  funext c
  rw [← sum_block_eq_blockWeight]
  rcases c with ⟨⟩ | ⟨⟩
  · simp only [Sum.elim_inl]
    rw [Finsupp.degree_eq_sum]
    exact Finset.sum_congr rfl fun a _ => Finsupp.mapDomain_apply hinj e a
  · simp only [Sum.elim_inr]
    refine Finset.sum_eq_zero fun b _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨a, ha⟩
    cases (Sigma.mk.inj ha).1

theorem rename_base_homogeneousComponent (d : ℕ) (f : Kleiman.Poly k N) :
    rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (homogeneousComponent d f) =
      weightedHomogeneousComponent (NumbersDVR.blockWeight (graphIdx N m)) (Sum.elim (fun _ => d) (fun _ => 0))
        (rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) f) := by
  classical
  have hinj : Function.Injective (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) :=
    fun a b h => eq_of_heq (Sigma.mk.inj h).2
  ext e'
  rw [coeff_weightedHomogeneousComponent]
  by_cases he : ∃ e, Finsupp.mapDomain (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) e = e'
  · obtain ⟨e, rfl⟩ := he
    rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj, coeff_homogeneousComponent,
      weight_mapDomain_base]
    by_cases hd : e.degree = d
    · rw [if_pos hd, if_pos (by rw [hd])]
    · rw [if_neg hd, if_neg fun h => hd (congrFun h (Sum.inl ()))]
  · push Not at he
    rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    split_ifs
    · rw [coeff_rename_eq_zero _ _ _ fun u hu => absurd hu (he u)]
    · rfl

end

theorem CurveComap.proof (hR : SectionRatio.Statement) (hD : RatioDim.Statement) : CurveComap.Statement := by
  intro k _ N Ω _ _ x Q n m s hx hgen W hW hle e
  have := hW.isPrime
  obtain ⟨j, hj⟩ := hW.relevant (Sum.inr ())
  have hdim := hD k N m W hW.isPrime hW.multiHomog j hj fun b => by
    obtain ⟨d, f, g, -, -, h1, h2⟩ := hR k N Ω x Q n m s hx hgen W hW hle j b hj
    exact ⟨f, g, h1, h2⟩
  have hsub : Kleiman.IsSubvar x (W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) e ↔
      ringKrullDim (Kleiman.Poly k N ⧸
          W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) =
        ((e + 1 : ℕ) : WithBot ℕ∞) := by
    refine ⟨fun h => h.dim, fun h => ⟨Ideal.comap_isPrime _ _, fun f hf d => ?_, ?_, ?_, h⟩⟩
    · rw [Ideal.mem_comap] at hf ⊢
      rw [rename_base_homogeneousComponent]
      exact hW.multiHomog _ hf _
    · rw [← comap_mIdealOver_graph (S := k) x s]
      exact Ideal.comap_mono hle
    · obtain ⟨i, hi⟩ := hW.relevant (Sum.inl ())
      have hXi : rename (fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c)) (X i : Kleiman.Poly k N) =
          X ⟨baseBlock, i⟩ := rename_X _ _
      exact ⟨i, by rw [Ideal.mem_comap, hXi]; exact hi⟩
  rw [hsub, FieldNumbers.CutRegular.relDim_eq_natCast_iff, hdim, Fintype.card_sum, Fintype.card_unit]
  generalize ringKrullDim (Kleiman.Poly k N ⧸
    W.comap (rename fun a : Fin (N + 1) => (⟨baseBlock, a⟩ : Σ c, graphIdx N m c))) = D
  induction D using WithBot.recBotCoe with
  | bot =>
    rw [WithBot.bot_add]
    exact iff_of_false (WithBot.bot_ne_natCast _) (WithBot.bot_ne_natCast _)
  | coe t =>
    rw [← WithBot.coe_one, ← WithBot.coe_add, ← WithBot.coe_natCast, ← WithBot.coe_natCast, WithBot.coe_inj,
      WithBot.coe_inj]
    induction t using ENat.recTopCoe with
    | top => exact iff_of_false (by rw [top_add]; exact ENat.top_ne_natCast _) (ENat.top_ne_natCast _)
    | coe t =>
      norm_cast
      omega

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
