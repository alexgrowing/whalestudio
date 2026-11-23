import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PureTensorMemSchwartzAdelicStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical

noncomputable section

namespace GlobalTheory.FinComm.VacLaw

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

theorem eq_atPlace_of_at (v : Pl F) {z : κ → AF F} (hz : At (evFin F v) z) (i : κ) :
    z i = GlobalTheory.EmbChart.atPlace v (evFin F v (z i)) := by
  have h0 : evFin F v (1 - GlobalTheory.EmbChart.atPlace v 1) = 0 := by
    rw [map_sub, map_one, GlobalTheory.EmbChart.evFin_atPlace, sub_self]
  have h := congrFun (hz _ h0) i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply, sub_mul, one_mul, sub_eq_zero] at h
  rw [GlobalTheory.EmbChart.atPlace_mul_right, one_mul] at h
  exact h

theorem evI_add (a b : AF F) : evI F (a + b) = evI F a + evI F b :=
  map_add (InfiniteAdeleRing.ringEquiv_mixedSpace F) a.1 b.1

theorem evI_atPlace (v : Pl F) (a : Fv F v) : evI F (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact map_zero _

theorem evFin_atPlace_ne {v u : Pl F} (h : u ≠ v) (a : Fv F v) : evFin F u (GlobalTheory.EmbChart.atPlace v a) = 0 := by
  rw [GlobalTheory.EmbChart.atPlace_apply]
  exact evalV_singleFin_ne h a

theorem eventually_int (x : κ → AF F) :
    ∀ᶠ u in cofinite, ∀ i, evFin F u (x i) ∈ u.adicCompletionIntegers F :=
  Filter.eventually_all.mpr fun i => (x i).2.2

theorem finite_mulSupport (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (x : κ → AF F) : (Function.mulSupport fun u => φ u (fun i => evFin F u (x i))).Finite := by
  have h : ∀ᶠ u in cofinite, φ u (fun i => evFin F u (x i)) = 1 := by
    filter_upwards [hφ, eventually_int x] with u hu hx
    rw [hu]
    simp [indO, Set.indicator, hx]
  exact (Filter.eventually_cofinite.mp h).subset fun u hu hp => hu hp

theorem tens_update (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (hφ : ∀ᶠ u in cofinite, φ u = indO u)
    (v : Pl F) : tens (evFin F v) (φ v) (pure f (Function.update φ v fun _ => 1)) = pure f φ := by
  funext x
  have hfin := finite_mulSupport φ hφ x
  unfold tens GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [← mul_finprod_cond_ne v hfin]
  have : (∏ᶠ u, Function.update φ v (fun _ => 1) u (fun i => evFin F u (x i))) =
      ∏ᶠ (u) (_ : u ≠ v), φ u (fun i => evFin F u (x i)) := by
    have hfin' : (Function.mulSupport fun u =>
        Function.update φ v (fun _ => (1 : ℂ)) u (fun i => evFin F u (x i))).Finite := by
      refine hfin.subset fun u hu => ?_
      by_cases e : u = v
      · subst e; simp at hu
      · simpa [Function.update_of_ne e] using hu
    rw [← mul_finprod_cond_ne v hfin', Function.update_self, one_mul]
    exact finprod_congr fun u => finprod_congr fun hu => by rw [Function.update_of_ne hu]
  rw [this]
  ring

theorem pure_update_add_at (f : SInf F κ) (φ : ∀ u : Pl F, (κ → Fv F u) → ℂ) (v : Pl F) (x z : κ → AF F)
    (hz : At (evFin F v) z) :
    pure f (Function.update φ v fun _ => 1) (x + z) = pure f (Function.update φ v fun _ => 1) x := by
  have hI : (fun i => evI F ((x + z) i)) = fun i => evI F (x i) := by
    funext i
    rw [Pi.add_apply, evI_add, eq_atPlace_of_at v hz i, evI_atPlace, add_zero]
  unfold GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure
  rw [hI]
  congr 1
  refine finprod_congr fun u => ?_
  by_cases e : u = v
  · subst e; simp
  · rw [Function.update_of_ne e]
    congr 1
    funext i
    rw [Pi.add_apply, map_add, eq_atPlace_of_at v hz i, evFin_atPlace_ne e, add_zero]

end GlobalTheory.FinComm.VacLaw

namespace GlobalTheory.FinComm

open GlobalTheory.FinComm.VacLaw

theorem vac_law : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : Spc F E n} {W : Spc F E d} (M : Model σ X W) (ψ : AddChar (AF F) ℂ), M.IsGood ψ →
    ∃ c : Pl F → Matrix (Fin n) (Fin d) (AE F E) → ℂ, ∀ v, ∀ γ ∈ latAtV X W v, ∀ f : SInf F (Fin n × Fin d),
      M.co.rho ψ γ (pure f M.vac) = c v γ • pure f M.vac := by
  intro F E _ _ _ _ _ σ n d X W M ψ hM
  have hvacO : ∀ᶠ u in cofinite, M.vac u = indO u := by
    filter_upwards [hM.std] with u hu
    rw [hu]
    rfl
  have hvacSB : ∀ u, M.vac u ∈ SB _ := fun u => (hM.vac u).1
  refine ⟨fun v γ => ψ (⅟(2 : AF F) * symp (cA σ) (inclR (F := F) (AF F) (((hM.vac v).2.2.choose : 𝓞 E) : E))
    (incM F X.J) (incM F W.J) γ γ), fun v γ hγ f => ?_⟩
  have hact := ((hM.vac v).2.2.choose_spec.2) γ hγ
  have hpv : pure f M.vac ∈ schA F _ := GlobalTheory.T.pure_tensor_mem_schwartz_adelic f M.vac hvacSB hvacO
  have hten := tens_update f M.vac hvacO v
  have hrest : Rest (evFin F v) (M.vac v) (pure f (Function.update M.vac v fun _ => 1)) :=
    ⟨fun x z hz => pure_update_add_at f M.vac v x z hz, hten ▸ hpv⟩
  have h := hact _ hrest
  rw [hten] at h
  rw [h, ← hten]
  funext x
  simp [tens, mul_assoc]

end GlobalTheory.FinComm
