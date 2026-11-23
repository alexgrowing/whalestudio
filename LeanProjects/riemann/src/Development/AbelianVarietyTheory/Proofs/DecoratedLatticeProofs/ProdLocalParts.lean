import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LocMod GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain ValuativeRel

noncomputable section

namespace GlobalTheory.LevelCut

open GlobalTheory.SplitCut

variable {D : D7}

theorem entry_idAt (V : HSp D) (P : Pl D → Prop) (g : GA D V) (hg : g ∈ grpAt V P) (i j : Fin V.rank) :
    (mt V g - 1) i j ∈ idAt D P := by
  have h := congrArg (fun x : GL (Fin V.rank) (AE D ⧸ idAt D P) => x.1 i j) (show _ = (1 : GL _ _) from hg)
  change Ideal.Quotient.mk (idAt D P) (mt V g i j) = _ at h
  have h2 : Ideal.Quotient.mk (idAt D P) (mt V g i j) =
      Ideal.Quotient.mk (idAt D P) ((1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) i j) := by
    rw [h, Units.val_one]; by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [Matrix.sub_apply]; exact Ideal.Quotient.eq.mp h2

open GlobalTheory.LocWeil.PlaceIdem in

theorem sum_act {W : Type} [Fintype W] (v : W → Pl D) (hv : Function.Injective v)
    (y : AE D) (hy : y ∈ idAt D (fun u => u ∈ Set.range v)) :
    (1 - ∑ w, algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w))) * y = 0 := by
  unfold idAt at hy
  obtain ⟨h1, h2⟩ := hy
  have h1' : infPart D y = 0 := h1
  have h2' : ∀ u, u ∉ Set.range v → compAt D u y = 0 := fun u hu => by
    have := (Ideal.mem_iInf.1 h2) ⟨u, hu⟩
    exact (RingHom.mem_ker).mp this
  have h3 := key v hv y h2'
  have h0 : finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)) = 0 := by
    rw [finPart_algebraMap]
    exact TensorProduct.zero_tmul _ _
  have h4 : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0) * y = 0 :=
    GlobalTheory.SplitScalar.adele_ext (by rw [RingHom.map_mul, h1', mul_zero, RingHom.map_zero])
      (by rw [RingHom.map_mul, h0, zero_mul, RingHom.map_zero])
  rw [map_sub, map_sub, map_one, map_sum] at h3
  linear_combination h3 + h4

theorem pr_sum {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : SplitPt D k) :
    q.pr (q.e + cA D q.e) = 1 := by
  have h2 := q.split.2.1
  have ho : q.sec 1 = q.e := by rw [← q.pr.map_one, q.sec_pr, mul_one]
  have p1 : q.pr q.e = 1 := by rw [← ho, q.pr_sec]
  have p2 : q.pr (cA D q.e) = 0 := by rw [← one_mul (q.pr _), ← p1, ← RingHom.map_mul, h2, RingHom.map_zero]
  rw [RingHom.map_add, p1, p2, add_zero]

theorem exists_coord {k : Type} [Field k] {N : ℕ} {Y : Type} [Fintype Y] [DecidableEq Y] (F : GlobalTheory.LocMod.Frame k N Y)
    (A B : Matrix (Fin N) (Fin N) k) (h1 : A * B = 1) (h2 : B * A = 1) : ∃ x : GL Y k, A = F.β * x.val * F.γ := by
  have key : ∀ A B : Matrix (Fin N) (Fin N) k, A * B = 1 → (F.γ * A * F.β) * (F.γ * B * F.β) = 1 := fun A B h => by
    calc (F.γ * A * F.β) * (F.γ * B * F.β) = F.γ * (A * (F.β * F.γ) * B) * F.β := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [F.βγ, Matrix.mul_one, h, Matrix.mul_one, F.γβ]
  refine ⟨⟨F.γ * A * F.β, F.γ * B * F.β, key A B h1, key B A h2⟩, ?_⟩
  calc A = (F.β * F.γ) * A * (F.β * F.γ) := by rw [F.βγ, Matrix.mul_one, Matrix.one_mul]
    _ = F.β * (F.γ * A * F.β) * F.γ := by simp only [Matrix.mul_assoc]

open GlobalTheory.LocWeil.PlaceIdem in

theorem exists_parts (V : HSp D) {n : ℕ} (v : Fin n → Pl D) (e : Fin n → AE D) (hv : Function.Injective v)
    (he : ∀ w, ∃ ε, IsPlaceIdem D (v w) ε ∧ e w + cA D (e w) = algebraMap (AF D.host.F) (AE D) ε)
    (g : GA D V) (hg : g ∈ grpAt V (fun u => u ∈ Set.range v)) :
    ∃ h : Fin n → GA D V, (∀ w, SuppAt (e w) V (h w)) ∧
      (∀ w, mt V (h w) = (e w + cA D (e w)) • mt V g + (1 - (e w + cA D (e w))) • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D))) ∧
      g = ((List.finRange n).map h).prod := by
  set E : Fin n → AE D := fun w => algebraMap (AF D.host.F) (AE D) (eFin D.host.F (v w)) with hEdef
  have hE : ∀ w, e w + cA D (e w) = E w := fun w => by
    obtain ⟨ε, hε, h⟩ := he w
    rw [h, eFin_of_placeIdem hε]
  have hEE : ∀ w, E w * E w = E w := fun w => by
    simp only [hEdef, ← map_mul, eFin_idem]
  have hEc : ∀ w, cA D (E w) = E w := fun w => cA_algebraMap _
  have hEo : ∀ w w', w ≠ w' → E w * E w' = 0 := fun w w' hww => by
    simp only [hEdef, ← map_mul]
    rw [eFin_mul_eFin _ (fun h => hww (hv h)), map_zero]
  choose h hh using fun w => cut_exists V g (E w) (hEE w) (hEc w)
  refine ⟨h, fun w i j => ?_, fun w => ?_, ?_⟩
  · rw [hE w, hh w]
    exact idempotent_mul_cut_sub_one_entry _ (hEE w) _ i j
  · rw [hE w, hh w]
  · apply GlobalTheory.SplitCut.mt_injective
    rw [mt_list_prod V h E _ hh hEo _ (List.nodup_finRange n), ← Fin.sum_univ_def]
    exact exists_widePullback_of_iteratedLine _ _ fun i j => sum_act v hv _ (entry_idAt V _ g hg i j)

theorem prod_local_parts : ∀ (D : D7) (c : Comm D) (v : VCom c) (n : ℕ) (G : Fin n → GLoc v), GPin G →
    ∀ (j : ℕ) (k : GA D (c.V j)), k ∈ grpAt (c.V j) (· ∈ v.gP) → ∃ h : Fin n → GA D (c.V j),
      (∀ i b hb, ∃ x, (G i).Mat j b hb k x ∧ (ofSplit (G i).q).IsLoc ((G i).FY j b hb) (h i) x) ∧
        k = ((List.finRange n).map h).prod := by
  intro D c v n G hG j g hg
  have hP : (fun u => u ∈ v.gP) = fun u => u ∈ Set.range (fun i => (G i).q.v) := by
    funext u
    rw [hG.places u]
    exact propext ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩
  rw [hP] at hg
  obtain ⟨h, h1, h2, h3⟩ := exists_parts (c.V j) (fun i => (G i).q.v) (fun i => (G i).q.e) hG.inj
    (fun i => (G i).q.above) g hg
  refine ⟨h, fun i b hb => ?_, h3⟩
  have hm : ∀ a a' : GA D (c.V j), a * a' = 1 →
      (mt (c.V j) a).map (G i).q.pr * (mt (c.V j) a').map (G i).q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  obtain ⟨x, hx⟩ := exists_coord ((G i).FY j b hb) _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))
  refine ⟨x, hx, h1 i, ?_⟩
  change (mt (c.V j) (h i)).map (G i).q.pr = _
  rw [h2 i, GlobalTheory.GfCut.map_idem, pr_sum, one_smul, sub_self, zero_smul, add_zero]
  exact hx

end GlobalTheory.LevelCut
