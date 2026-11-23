import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGram
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupProjections
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LatticeStableAlmostEverywhere

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PureH

theorem map_consTup {K L : Type} [Zero K] [One K] [Zero L] [One L] (f : K → L) (h0 : f 0 = 0)
    (h1 : f 1 = 1) {M n : ℕ} (X : Fin n → Fin M → K) :
    (fun a i => f (consTup X a i)) = consTup (fun a i => f (X a i)) := by
  funext a i
  induction a using Fin.cases with
  | zero =>
    induction i using Fin.cases with
    | zero => simp [consTup, h1]
    | succ i => simp [consTup, h0]
  | succ a =>
    induction i using Fin.cases with
    | zero => simp [consTup, h0]
    | succ i => simp [consTup]

theorem consTup_empty {K : Type} [Zero K] [One K] {M : ℕ} (X : Fin 0 → Fin M → K) :
    (consTup X : Fin (0 + 1) → Fin (M + 1) → K) = fun _ : Fin 1 => Fin.cons 1 (fun _ => 0) := by
  funext a
  induction a using Fin.cases with
  | zero => simp [consTup]
  | succ a => exact a.elim0

section Glob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem projInf_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projInf (consTup X) = consTup (projInf X) :=
  map_consTup (Algebra.TensorProduct.map (fstA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projFin_consTup {M n : ℕ} (X : Fin n → Fin M → AF F ⊗[F] E) :
    projFin (consTup X) = consTup (projFin X) :=
  map_consTup (Algebra.TensorProduct.map (sndA F) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem projV_consTup (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ} (X : Fin n → Fin M → Af F ⊗[F] E) :
    projV v (consTup X) = consTup (projV v X) :=
  map_consTup (Algebra.TensorProduct.map (evalV F v) (AlgHom.id F E)) (map_zero _) (map_one _) X

theorem consTup_mem_latV {d : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) {M n : ℕ}
    (h0 : ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (X : Fin n → Fin M → Fv F v ⊗[F] E) : consTup X ∈ latV b v ↔ X ∈ latV b v := by
  constructor
  · intro h a i k
    simpa [consTup] using h a.succ i.succ k
  · intro h a i k
    induction a using Fin.cases with
    | zero => simpa [consTup] using h0 (fun a => a.elim0) 0 i k
    | succ a =>
      induction i using Fin.cases with
      | zero => simp [consTup, zero_mem]
      | succ i => simpa [consTup] using h a i k

end Glob

end GlobalTheory.CompanionTheory.SW.PureH

namespace GlobalTheory.CompanionTheory.SW.PureH

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  [DecidableEq (HeightOneSpectrum (𝓞 F))]

theorem prod_union_split {ι : Type} [DecidableEq ι] (S Sh : Finset ι) (A B : ι → ℝ≥0∞) (P : ι → Prop)
    [DecidablePred P] (hS : ∀ v, P v ↔ v ∈ S) :
    ∏ v ∈ S ∪ Sh, (if P v then A v else B v) = (∏ v ∈ S, A v) * ∏ v ∈ Sh \ S, B v := by
  rw [← Finset.union_sdiff_self_eq_union, Finset.prod_union Finset.disjoint_sdiff]
  congr 1
  · exact Finset.prod_congr rfl fun v hv => if_pos ((hS v).2 hv)
  · exact Finset.prod_congr rfl fun v hv => if_neg fun h => (Finset.mem_sdiff.1 hv).2 ((hS v).1 h)

variable {d M : ℕ} (b : Module.Basis (Fin d) F E) (σ : E →ₐ[F] E)
  (Jp : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (AF F) σ Jp) (ginf : HA (Ainf F) σ Jp)
  (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ Jp) (S Sh : Finset (HeightOneSpectrum (𝓞 F)))

include b in

theorem pureL_act
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    {n : ℕ} (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞)
    (X : Fin n → Fin M → AF F ⊗[F] E) :
    pureL b S φinf φ (actW (AF F) σ Jp h (consTup X)) =
      pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ Jp ginf (consTup Y)))
        (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ Jp (g v) (consTup Y))
          else (latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup Y))) X := by
  have hP : projInf (actW (AF F) σ Jp h (consTup X)) =
      actW (Ainf F) σ Jp ginf (consTup (projInf X)) := by
    rw [hinf, projInf_consTup]
  have hV : ∀ v, projV v (projFin (actW (AF F) σ Jp h (consTup X))) =
      actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) := fun v => by
    rw [hfin, projFin_consTup, projV_consTup]
  have key : ∀ v, v ∉ S → v ∉ Sh →
      (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v ↔
        projV v (projFin X) ∈ latV b v) := fun v h1 h2 =>
    (hSh v h2 _ _).trans (consTup_mem_latV b v (hS v h1) _)
  have hprod := prod_union_split S Sh
    (fun v => φ v (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))))
    (fun v => ((latV b v).indicator 1 (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
    (fun v => v ∈ S) (fun _ => Iff.rfl)
  unfold pureL
  by_cases hX : X ∈ intOff b (S ∪ Sh)
  · rw [Set.indicator_of_mem hX, hprod]
    by_cases hA : ∀ v ∈ Sh \ S, actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X))) ∈ latV b v
    · have hY : actW (AF F) σ Jp h (consTup X) ∈ intOff b S := by
        intro v hv
        rw [hV]
        by_cases hvh : v ∈ Sh
        · exact hA v (Finset.mem_sdiff.2 ⟨hvh, hv⟩)
        · exact (key v hv hvh).2 (hX v (by simp [hv, hvh]))
      rw [Set.indicator_of_mem hY, hP, Finset.prod_eq_one
        (f := fun v => ((latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (consTup (projV v (projFin X)))) : ℝ≥0∞))
        (fun v hv => by simp [Set.indicator_of_mem (hA v hv)])]
      simp only [mul_one, hV]
    · push Not at hA
      obtain ⟨v, hv, hvl⟩ := hA
      have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
        intro hm
        have := hm v (Finset.mem_sdiff.1 hv).2
        rw [hV] at this
        exact hvl this
      rw [Set.indicator_of_notMem hY, Finset.prod_eq_zero hv (by simp [Set.indicator_of_notMem hvl])]
      simp
  · have hY : actW (AF F) σ Jp h (consTup X) ∉ intOff b S := by
      intro hm
      apply hX
      intro v hv
      have hv' : v ∉ S ∧ v ∉ Sh := by simpa using hv
      have := hm v hv'.1
      rw [hV] at this
      exact (key v hv'.1 hv'.2).1 this
    rw [Set.indicator_of_notMem hX, Set.indicator_of_notMem hY]

include b in

theorem pureL_act_vec
    (hinf : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E),
      projInf (actW (AF F) σ Jp h X) = actW (Ainf F) σ Jp ginf (projInf X))
    (hfin : ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)),
      projV v (projFin (actW (AF F) σ Jp h X)) = actW (Fv F v) σ Jp (g v) (projV v (projFin X)))
    (hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ Jp (g v) X ∈ latV b v ↔ X ∈ latV b v)
    (hS : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v)
    (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞)
    (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) :
    pureL b S Ψinf Ψ (actW (AF F) σ Jp h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) =
      (Ψinf (actW (Ainf F) σ Jp ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) *
        ∏ v ∈ S, Ψ v (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) *
        ∏ v ∈ Sh \ S, (latV b v).indicator 1
          (actW (Fv F v) σ Jp (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  let X₀ : Fin 0 → Fin M → AF F ⊗[F] E := fun a => a.elim0
  have h1 := pureL_act (n := 0) b σ Jp h ginf g S Sh hinf hfin hSh hS Ψinf Ψ X₀
  have hmem : X₀ ∈ intOff b (S ∪ Sh) := fun v _ a => a.elim0
  unfold pureL at h1
  rw [Set.indicator_of_mem hmem] at h1
  rw [consTup_empty] at h1
  simp only [consTup_empty] at h1
  rw [prod_union_split S Sh _ _ (fun v => v ∈ S) (fun _ => Iff.rfl)] at h1
  rw [mul_assoc]
  unfold pureL
  exact h1

end Core

theorem pure_h : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [DecidableEq (HeightOneSpectrum (𝓞 F))] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∃ S₁ : Finset (HeightOneSpectrum (𝓞 F)), ∀ h : HA (AF F) σ (blockOne (algebraMap F E t) J), ∃ (ginf : HA (Ainf F) σ (blockOne (algebraMap F E t) J)) (g : ∀ v : HeightOneSpectrum (𝓞 F), HA (Fv F v) σ (blockOne (algebraMap F E t) J)) (Sh : Finset (HeightOneSpectrum (𝓞 F))), ∀ S, S₁ ⊆ S → (∀ (n : ℕ) (φinf : (Fin (n + 1) → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (φ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin (n + 1) → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞) (X : Fin n → Fin M → AF F ⊗[F] E), pureL b S φinf φ (actW (AF F) σ _ h (consTup X)) = pureL b (S ∪ Sh) (fun Y => φinf (actW (Ainf F) σ _ ginf (consTup Y))) (fun v Y => if v ∈ S then φ v (actW (Fv F v) σ _ (g v) (consTup Y)) else (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (consTup Y))) X) ∧ ∀ (Ψinf : (Fin 1 → Fin (M + 1) → Ainf F ⊗[F] E) → ℝ≥0∞) (Ψ : ∀ v : HeightOneSpectrum (𝓞 F), (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E) → ℝ≥0∞), pureL b S Ψinf Ψ (actW (AF F) σ _ h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) = (Ψinf (actW (Ainf F) σ _ ginf (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) * ∏ v ∈ S, Ψ v (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)))) * ∏ v ∈ Sh \ S, (latV b v).indicator 1 (actW (Fv F v) σ _ (g v) (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0))) := by
  intro F E _ _ _ _ _ _ σ hCM M J hJ t ht d b
  have hba := GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M J t
  have hJ' : IsHermND σ (blockOne (algebraMap F E t) J) :=
    ⟨hba.2.1 hJ.1, by
      rw [hba.1]
      exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2⟩
  obtain ⟨pinf, p, hcomp, hlat, -⟩ := GlobalTheory.CompanionTheory.SW.HProj.components F E σ hCM (M + 1) _ hJ'
  have hcons := (GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b 0 M).2.2
  let S₁ : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hcons).toFinset
  refine ⟨S₁, fun h => ?_⟩
  have hlat' := hlat d b h
  let Sh : Finset (HeightOneSpectrum (𝓞 F)) := (Filter.eventually_cofinite.1 hlat').toFinset
  have hSh : ∀ v, v ∉ Sh → ∀ (n : ℕ) (X : Fin n → Fin (M + 1) → Fv F v ⊗[F] E),
      actW (Fv F v) σ _ (p v h) X ∈ latV b v ↔ X ∈ latV b v := fun v hv => by
    simpa [Sh] using hv
  refine ⟨pinf h, fun v => p v h, Sh, fun S hS => ?_⟩
  have hS' : ∀ v, v ∉ S → ∀ X₀ : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X₀ ∈ latV b v := by
    intro v hv X₀
    have hv₁ : v ∉ S₁ := fun hm => hv (hS hm)
    have : ∀ X : Fin 0 → Fin M → Fv F v ⊗[F] E, consTup X ∈ latV b v ↔ X ∈ latV b v := by
      simpa [S₁] using hv₁
    exact (this X₀).2 fun a => a.elim0
  have hinf := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) => (hcomp n h X).1
  have hfin := fun (n : ℕ) (X : Fin n → Fin (M + 1) → AF F ⊗[F] E) (v : HeightOneSpectrum (𝓞 F)) =>
    (hcomp n h X).2 v
  exact ⟨fun n φinf φ X => pureL_act b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' φinf φ X,
    fun Ψinf Ψ => pureL_act_vec b σ _ h (pinf h) (fun v => p v h) S Sh hinf hfin hSh hS' Ψinf Ψ⟩

end GlobalTheory.CompanionTheory.SW.PureH
