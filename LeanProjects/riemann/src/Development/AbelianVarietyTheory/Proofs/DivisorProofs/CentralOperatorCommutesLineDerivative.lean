import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompFinEqZeroOfAt

open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open scoped ContDiff

noncomputable section
namespace GlobalTheory.UAut.CentralComm

theorem hasDerivAt_snd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : X × ℝ → ℂ}
    (hH : Differentiable ℝ H) (x : X) : HasDerivAt (fun t => H (x, t)) (fderiv ℝ H (x, 0) (0, 1)) 0 :=
  (hH (x, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) x).prodMk (hasDerivAt_id (0 : ℝ)))

theorem hasDerivAt_fst {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : ℝ × X → ℂ}
    (hH : Differentiable ℝ H) (x : X) : HasDerivAt (fun t => H (t, x)) (fderiv ℝ H (0, x) (1, 0)) 0 :=
  (hH (0, x)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) x))

theorem contDiff_deriv_snd {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {H : X × ℝ → ℂ}
    (hH : ContDiff ℝ ∞ H) : ContDiff ℝ ∞ fun x => deriv (fun t => H (x, t)) 0 := by
  simp only [fun x => (hasDerivAt_snd (hH.differentiable (by simp)) x).deriv]
  exact ((hH.fderiv_right (m := ∞) (by simp)).comp (contDiff_id.prodMk contDiff_const)).clm_apply contDiff_const

theorem deriv_deriv_comm {H : ℝ × ℝ → ℂ} (hH : ContDiff ℝ ∞ H) :
    deriv (fun s => deriv (fun t => H (s, t)) 0) 0 = deriv (fun t => deriv (fun s => H (s, t)) 0) 0 := by
  have hd := hH.differentiable (by simp)
  have h2 : Differentiable ℝ (fderiv ℝ H) := (hH.fderiv_right (m := ∞) (by simp)).differentiable (by simp)
  simp only [fun x => (hasDerivAt_snd hd x).deriv, fun x => (hasDerivAt_fst hd x).deriv]
  have e1 : HasDerivAt (fun s : ℝ => fderiv ℝ H (s, 0)) (fderiv ℝ (fderiv ℝ H) (0, 0) (1, 0)) 0 :=
    (h2 (0, 0)).hasFDerivAt.comp_hasDerivAt (f := fun s : ℝ => (s, (0 : ℝ))) (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) (0 : ℝ)))
  have e2 : HasDerivAt (fun t : ℝ => fderiv ℝ H (0, t)) (fderiv ℝ (fderiv ℝ H) (0, 0) (0, 1)) 0 :=
    (h2 (0, 0)).hasFDerivAt.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).prodMk (hasDerivAt_id (0 : ℝ)))
  have e3 := (e1.clm_apply (hasDerivAt_const (0 : ℝ) ((0, 1) : ℝ × ℝ))).deriv
  have e4 := (e2.clm_apply (hasDerivAt_const (0 : ℝ) ((1, 0) : ℝ × ℝ))).deriv
  rw [e3, e4]
  simp only [map_zero, add_zero]
  exact (hH.contDiffAt.isSymmSndFDerivAt (by simpa using ENat.LEInfty.out)) _ _

theorem prod_snoc {G : Type} [Monoid G] {m : ℕ} (δ : Fin m → ℝ → G) (γ : ℝ → G) (s : Fin m → ℝ) (t : ℝ) :
    (List.ofFn fun i : Fin (m + 1) => (Fin.snoc (α := fun _ => ℝ → G) δ γ i) (Fin.snoc (α := fun _ => ℝ) s t i)).prod =
      (List.ofFn fun i => δ i (s i)).prod * γ t := by
  rw [List.ofFn_succ', List.concat_eq_append, List.prod_append]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

theorem contDiff_snoc {k : ℕ} :
    ContDiff ℝ ∞ fun p : (Fin k → ℝ) × ℝ => (Fin.snoc (α := fun _ => ℝ) p.1 p.2 : Fin (k + 1) → ℝ) := by
  refine contDiff_pi.2 fun i => ?_
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using contDiff_snd
  · simp only [Fin.snoc_castSucc]
    exact (contDiff_apply ℝ ℝ j).comp contDiff_fst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

variable (σ J) in

def IsSmFamily (u : ℝ → GAd σ J → ℂ) : Prop :=
  ∀ (k : ℕ) (δ : Fin k → ℝ → GAd σ J), (∀ i, IsRealLine σ J (δ i)) → ∀ g,
    ContDiff ℝ ∞ fun p : ℝ × (Fin k → ℝ) => u p.1 (g * (List.ofFn fun i => δ i (p.2 i)).prod)

omit [NumberField E] in
theorem isRealLine_snoc {k : ℕ} {δ : Fin k → ℝ → GAd σ J} (hδ : ∀ i, IsRealLine σ J (δ i)) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (i : Fin (k + 1)) : IsRealLine σ J (Fin.snoc (α := fun _ => ℝ → GAd σ J) δ γ i) :=
  Fin.lastCases (by simpa using hγ) (fun j => by simpa using hδ j) i

omit [NumberField E] in

theorem isSmFamily_translate {f : GAd σ J → ℂ} (hf : IsSm σ J f) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSmFamily σ J fun s x => f (x * γ s) := fun k δ hδ g => by
  have h := (hf (k + 1) _ (isRealLine_snoc hδ hγ) g).comp (contDiff_snoc.comp (contDiff_snd.prodMk contDiff_fst))
  simpa only [Function.comp_def, prod_snoc, ← mul_assoc] using h

omit [NumberField E] in

theorem IsSmFamily.lineDer {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) :
    IsSmFamily σ J fun s => lineDer γ (u s) := fun k δ hδ g => by
  have h := (hu (k + 1) _ (isRealLine_snoc hδ hγ) g).comp
    (((contDiff_fst.comp contDiff_fst).prodMk
      (contDiff_snoc.comp ((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd))) :
      ContDiff ℝ ∞ fun q : (ℝ × (Fin k → ℝ)) × ℝ => (q.1.1, (Fin.snoc (α := fun _ => ℝ) q.1.2 q.2 : Fin (k + 1) → ℝ)))
  simpa only [Function.comp_def, prod_snoc, ← mul_assoc, SiegelSet.lineDer] using contDiff_deriv_snd h

omit [NumberField E] in

theorem IsSmFamily.differentiable {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) (g : GAd σ J) :
    Differentiable ℝ fun s => u s g := by
  have h := (hu 0 Fin.elim0 (fun i => i.elim0) g).comp
    (contDiff_id.prodMk contDiff_const : ContDiff ℝ ∞ fun s : ℝ => (s, (0 : Fin 0 → ℝ)))
  simpa [Function.comp_def] using h.differentiable (by simp)

omit [NumberField E] in

theorem IsSmFamily.deriv_lineDer {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) {γ : ℝ → GAd σ J}
    (hγ : IsRealLine σ J γ) (g : GAd σ J) :
    deriv (fun s => SiegelSet.lineDer γ (u s) g) 0 = SiegelSet.lineDer γ (fun x => deriv (fun s => u s x) 0) g := by
  have h := (hu 1 (fun _ => γ) (fun _ => hγ) g).comp
    (contDiff_fst.prodMk (contDiff_pi.2 fun _ => contDiff_snd) :
      ContDiff ℝ ∞ fun q : ℝ × ℝ => (q.1, fun _ : Fin 1 => q.2))
  have h' : ContDiff ℝ ∞ fun q : ℝ × ℝ => u q.1 (g * γ q.2) := by simpa [Function.comp_def] using h
  exact deriv_deriv_comm h'

omit [NumberField E] in

theorem IsSmFamily.foldr {u : ℝ → GAd σ J → ℂ} (hu : IsSmFamily σ J u) :
    ∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
      IsSmFamily σ J (fun s => l.foldr SiegelSet.lineDer (u s)) ∧
      (fun x => deriv (fun s => l.foldr SiegelSet.lineDer (u s) x) 0) =
        l.foldr SiegelSet.lineDer fun x => deriv (fun s => u s x) 0
  | [], _ => ⟨hu, rfl⟩
  | γ :: l, hl => by
    obtain ⟨h1, h2⟩ := hu.foldr l fun γ' h => hl γ' (List.mem_cons_of_mem _ h)
    have hγ := hl γ List.mem_cons_self
    refine ⟨h1.lineDer hγ, funext fun x => ?_⟩
    simp only [List.foldr_cons]
    rw [← h2]
    exact h1.deriv_lineDer hγ x

theorem lineDer_dop_comm : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (z : List (ℝ → GAd σ J) →₀ ℂ), IsCentral σ J z →
    ∀ f : GAd σ J → ℂ, IsSm σ J f → ∀ γ : ℝ → GAd σ J, IsRealLine σ J γ →
      lineDer γ (dop z f) = dop z (lineDer γ f) := by
  intro F E _ _ _ _ _ σ n J z hz f hf γ hγ
  have hinf : ∀ s, γ s ∈ infPts σ J := fun s => by
    obtain ⟨w, τ, Z, -, h⟩ := hγ
    obtain ⟨y, e, -⟩ := h s
    exact e ▸ mem_infPts.2 (projFin_embArch _ _ _ _)
  have hu := isSmFamily_translate hf hγ
  funext g
  have e : (fun s => dop z f (g * γ s)) =
      fun s => ∑ l ∈ z.support, z l * l.foldr lineDer (fun x => f (x * γ s)) g :=
    funext fun s => (hz.2 f hf _ (hinf s) g).symm
  change deriv (fun s => dop z f (g * γ s)) 0 = ∑ l ∈ z.support, z l * l.foldr lineDer (lineDer γ f) g
  rw [e]
  refine (HasDerivAt.fun_sum fun l hl => HasDerivAt.const_mul (z l) ?_).deriv
  obtain ⟨h1, h2⟩ := hu.foldr l (hz.1 l hl)
  have h3 := (h1.differentiable g 0).hasDerivAt
  rw [congrFun h2 g] at h3
  exact h3

end GlobalTheory.UAut.CentralComm

end
