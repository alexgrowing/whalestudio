import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.WeilM

noncomputable section

namespace GlobalTheory.AlgCountDim

open GlobalTheory.AdelicU

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d}

theorem eventually_evFin_integral (x : AF F) :
    ∀ᶠ v in Filter.cofinite, GlobalTheory.AdelicU.evFin F v x ∈ v.adicCompletionIntegers F := x.2.2

theorem eventually_vac_eq_one (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (hM : M.IsGood ψ)
    (x : Fin n × Fin d → AF F) :
    ∀ᶠ v in Filter.cofinite, M.vac v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 1 := by
  have hint : ∀ᶠ v in Filter.cofinite, ∀ i, GlobalTheory.AdelicU.evFin F v (x i) ∈ v.adicCompletionIntegers F :=
    Filter.eventually_all.2 fun i => eventually_evFin_integral (x i)
  filter_upwards [hM.std, hint] with v hv hi
  rw [hv]
  simp [Set.indicator, hi]

open Classical in

theorem pure_update_eq (f : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ) (a : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)
    (x : Fin n × Fin d → AF F)
    (hx : {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite) :
    ∃ c : ℂ, ∀ ζ : (Fin n × Fin d → Fv F a) → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f (Function.update φ a ζ) x =
        f (fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI F (x i)) * (ζ (fun i => GlobalTheory.AdelicU.evFin F a (x i)) * c) := by
  classical
  set s := hx.toFinset with hs
  have ha : a ∉ s := by simp [hs]
  refine ⟨∏ v ∈ s, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)), fun ζ => ?_⟩
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  congr 1
  rw [finprod_eq_prod_of_mulSupport_subset (s := insert a s)]
  · rw [Finset.prod_insert ha, Function.update_self]
    congr 1
    refine Finset.prod_congr rfl fun v hv => ?_
    have : v ≠ a := fun h => ha (h ▸ hv)
    rw [Function.update_of_ne this]
  · intro v hv
    simp only [Function.mem_mulSupport] at hv
    by_cases h : v = a
    · simp [h]
    · rw [Function.update_of_ne h] at hv
      simp [hs, h, hv]

section Main

variable (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ) (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w)

open Classical in

def gens : Set ((Fin n × Fin d → AF F) → ℂ) :=
  Set.range fun p : Σ S : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F), Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb) ×
      (∀ v : S, Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v.1))) =>
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) p.2.1 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
      (fun v => if h : v ∈ p.1 then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (p.2.2 ⟨v, h⟩) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v)

open Classical in

theorem pure_mem_span_gens (hM : M.IsGood ψ) (i : Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) :
    ∀ (S T : Finset (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F)) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (Fin n × Fin d → Fv F v) → ℂ),
      (∀ v, φ v ∈ GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) → (∀ v, v ∉ S → v ∉ T → φ v = M.vac v) →
      (∀ v ∈ T, ∃ j, φ v = ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ)) →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈
        Submodule.span ℂ (gens M ψ emb) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
    intro T φ _ hoff hT
    choose j hj using hT
    have hfun : (fun v => if h : v ∈ T then
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) (j v h) :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) : (Fin n × Fin d → Fv F v) → ℂ) else M.vac v) = φ := by
      funext v
      by_cases h : v ∈ T
      · rw [dif_pos h]
        exact (hj v h).symm
      · rw [dif_neg h]
        exact (hoff v (Finset.notMem_empty v) h).symm
    exact Submodule.subset_span ⟨⟨T, i, fun v => j v.1 v.2⟩, congrArg (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
      ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) hfun⟩
  | insert a S ha ih =>
    intro T φ hSB hoff hT
    set g := ((Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb) i : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))
    have hfin : ∀ x : Fin n × Fin d → AF F,
        {v | v ≠ a ∧ φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 1}.Finite := by
      intro x
      have h2 := Filter.eventually_cofinite.1 (eventually_vac_eq_one M ψ hM x)
      refine ((insert a S ∪ T : Finset _).finite_toSet.union h2).subset ?_
      rintro v ⟨_, hv⟩
      by_cases h : v ∈ insert a S ∪ T
      · exact Or.inl h
      · right
        simp only [Finset.mem_union, not_or] at h
        rw [hoff v h.1 h.2] at hv
        exact hv
    have key : ∀ ζ ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro ζ hζ
      induction hζ using Submodule.span_induction with
      | mem ζ hζ =>
        obtain ⟨j, rfl⟩ := hζ
        apply ih (insert a T)
        · intro v
          by_cases h : v = a
          · subst h
            rw [Function.update_self]
            exact (Module.Basis.ofVectorSpace ℂ _ j).2
          · rw [Function.update_of_ne h]
            exact hSB v
        · intro v hvS hvT
          have hva : v ≠ a := fun h => hvT (h ▸ Finset.mem_insert_self _ _)
          rw [Function.update_of_ne hva]
          exact hoff v (by simp [hva, hvS]) (fun h => hvT (Finset.mem_insert_of_mem h))
        · intro v hv
          by_cases h : v = a
          · subst h
            exact ⟨j, by rw [Function.update_self]⟩
          · rw [Function.update_of_ne h]
            exact hT v ((Finset.mem_insert.1 hv).resolve_left h)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a 0) = 0 := funext fun x => by
          obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
          rw [hc]
          simp
        rw [this]
        exact zero_mem _
      | add ζ₁ ζ₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (ζ₁ + ζ₂)) =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₁) + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ₂) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.add_apply, hc]
            ring
        rw [this]
        exact add_mem h₁ h₂
      | smul r ζ _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a (r • ζ)) = r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g (Function.update φ a ζ) :=
          funext fun x => by
            obtain ⟨c, hc⟩ := pure_update_eq g φ a x (hfin x)
            simp only [Pi.smul_apply, smul_eq_mul, hc]
            ring
        rw [this]
        exact Submodule.smul_mem _ r h
    have hmem : φ a ∈ Submodule.span ℂ (Set.range fun j =>
        ((Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) j :
          GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) : (Fin n × Fin d → Fv F a) → ℂ)) := by
      have h1 : (⟨φ a, hSB a⟩ : GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)) ∈
          Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)))) := by
        rw [Module.Basis.span_eq]
        trivial
      have := Submodule.apply_mem_span_image_of_mem_span (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F a)).subtype h1
      rw [← Set.range_comp] at this
      exact this
    simpa using key _ hmem

end Main

theorem rank_algD_le_aleph0 : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {n d : ℕ} {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {W : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X W) (ψ : AddChar (AF F) ℂ)
    (emb : ∀ w : InfinitePlace F, GlobalTheory.AdelicU.EmbOver E w), M.IsGood ψ →
    Module.rank ℂ (M.Pol ψ emb) ≤ Cardinal.aleph0 →
    (∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, Module.rank ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v)) ≤ Cardinal.aleph0) →
    Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Cardinal.aleph0 := by
  intro F E _ _ _ _ _ σ n d X W M ψ emb hM hPol hSB
  classical
  haveI := GlobalTheory.AdelicUnitaryTop.countable_heightOneSpectrum F
  haveI : Countable (Module.Basis.ofVectorSpaceIndex ℂ (M.Pol ψ emb)) := by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hPol
  haveI : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
      Countable (Module.Basis.ofVectorSpaceIndex ℂ (GlobalTheory.WeilM.SB (Fin n × Fin d → Fv F v))) := fun v => by
    rw [← Cardinal.mk_le_aleph0_iff, (Module.Basis.ofVectorSpace ℂ _).mk_eq_rank'']
    exact hSB v
  have hle : GlobalTheory.SquareAgree.algD M ψ emb ≤ Submodule.span ℂ (gens M ψ emb) := by
    rw [GlobalTheory.SquareAgree.algD, Submodule.span_le]
    rintro _ ⟨f, φ, hf, hφ, hcof, rfl⟩
    have hfin := Filter.eventually_cofinite.1 hcof
    have key : ∀ g ∈ Submodule.span ℂ (Set.range (Module.Basis.ofVectorSpace ℂ (M.Pol ψ emb))),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ ∈ Submodule.span ℂ (gens M ψ emb) := by
      intro g hg
      induction hg using Submodule.span_induction with
      | mem g hg =>
        obtain ⟨i, rfl⟩ := hg
        exact pure_mem_span_gens M ψ emb hM i hfin.toFinset ∅ φ hφ (fun v hv _ => by simpa using hv) (by simp)
      | zero =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((0 : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ = 0 :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
        rw [this]
        exact zero_mem _
      | add g₁ g₂ _ _ h₁ h₂ =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((g₁ + g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₁ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ +
              GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g₂ : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]
        rw [this]
        exact add_mem h₁ h₂
      | smul r g _ h =>
        have : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (((r • g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d))) φ =
            r • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure ((g : M.Pol ψ emb) : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin n × Fin d)) φ :=
          funext fun x => by simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]
        rw [this]
        exact Submodule.smul_mem _ r h
    exact key ⟨f, hf⟩ (by rw [Module.Basis.span_eq]; trivial)
  calc Module.rank ℂ (GlobalTheory.SquareAgree.algD M ψ emb) ≤ Module.rank ℂ (Submodule.span ℂ (gens M ψ emb)) :=
        Submodule.rank_mono hle
    _ ≤ Cardinal.mk (gens M ψ emb) := rank_span_le _
    _ ≤ Cardinal.aleph0 := by
        rw [Cardinal.mk_le_aleph0_iff]
        exact (Set.countable_range _).to_subtype

end GlobalTheory.AlgCountDim

end
