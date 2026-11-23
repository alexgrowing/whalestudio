import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceUnitaryLocalPointsEquivGL

noncomputable section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.LocGlue

theorem entry_mem {E : Type} [Field E] [NumberField E] {n : ℕ} {v : HeightOneSpectrum (𝓞 E)}
    {g : GL (Fin n) (v.adicCompletion E)} (hg : g ∈ GlobalTheory.LFun.KGL v n) (i j : Fin n) :
    g.val i j ∈ v.adicCompletionIntegers E ∧ (g⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E := by
  obtain ⟨g0, rfl⟩ := hg
  refine ⟨(g0.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((g0⁻¹).val i j).2

theorem glue : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (g : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)), (∀ᶠ v in cofinite, g v ∈ GlobalTheory.LFun.KGL v n) → ∃ k : GL (Fin n) (Af E), ∀ v, GeneralLinearGroup.map (pLoc E v) k = g v := by
  intro E _ _ n g hg
  have hent : ∀ i j, ∀ᶠ v in cofinite, (g v).val i j ∈ v.adicCompletionIntegers E ∧
      ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j ∈ v.adicCompletionIntegers E :=
    fun i j => hg.mono fun v hv => entry_mem hv i j
  let M : Matrix (Fin n) (Fin n) (Af E) := fun i j => ⟨fun v => (g v).val i j, (hent i j).mono fun v h => h.1⟩
  let N : Matrix (Fin n) (Fin n) (Af E) := fun i j =>
    ⟨fun v => ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val i j, (hent i j).mono fun v h => h.2⟩
  have hM : ∀ v, RingHom.mapMatrix (pLoc E v) M = (g v).val := fun v => rfl
  have hN : ∀ v, RingHom.mapMatrix (pLoc E v) N = ((g v)⁻¹ : GL (Fin n) (v.adicCompletion E)).val := fun v => rfl
  have hMN : M * N = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.mul_inv]
  have hNM : N * M = 1 := GlobalTheory.SplitPts.matAf_ext fun v => by
    rw [map_mul, map_one, hM, hN, Units.inv_mul]
  exact ⟨⟨M, N, hMN, hNM⟩, fun v => Units.ext (hM v)⟩

theorem intst : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (v u : HeightOneSpectrum (𝓞 E)) (f : v.adicCompletion E →+* u.adicCompletion E), (∀ x, Valued.v (f x) = Valued.v x) → ∀ g ∈ GlobalTheory.LFun.KGL v n, invT n _ (GeneralLinearGroup.map f g) ∈ GlobalTheory.LFun.KGL u n := by
  intro E _ _ n v u f hf g hg
  obtain ⟨g0, rfl⟩ := hg
  let r : Formalism.UG.Ov E v →+* Formalism.UG.Ov E u := f.restrict _ _ fun x hx => by
    change _ ∈ u.adicCompletionIntegers E
    change x ∈ v.adicCompletionIntegers E at hx
    rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
    rw [hf]
    exact hx
  refine ⟨invT n _ (GeneralLinearGroup.map r g0), ?_⟩
  apply Units.ext
  ext i j
  rfl

theorem ns : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), ¬ IsSplitAt u → GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) u)) = GeneralLinearGroup.map (cj u) (Y u) := by
  intro E _ _ _ n Y u hu
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ (IsCMField.complexConj E k)) →
      GeneralLinearGroup.map f (Y v) = GeneralLinearGroup.map (cj u) (Y u) := by
    rintro v rfl f hf hext
    have hex : ∃ s : v.adicCompletion E →+* v.adicCompletion E, Continuous s ∧
        ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x) := ⟨f, hf, hext⟩
    have hcj : cj v = hex.choose := by unfold cj; rw [dif_pos hex]
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = hex.choose :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf hex.choose_spec.1
        (funext fun k => (hext k).trans (hex.choose_spec.2 k).symm)
    rw [hcj]
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have hcu : conjSrc (GlobalTheory.SplitPts.conjE E) u = u := by
    by_contra h
    exact hu ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
      (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
      (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
  exact key _ hcu _ (conjLoc_spec _ u).1 (conjLoc_spec _ u).2.1

theorem twice : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (Y : ∀ v : HeightOneSpectrum (𝓞 E), GL (Fin n) (v.adicCompletion E)) (u : HeightOneSpectrum (𝓞 E)), GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) u) (GeneralLinearGroup.map (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)) (Y (conjSrc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))) = Y u := by
  intro E _ _ _ n Y u
  have key : ∀ (v : HeightOneSpectrum (𝓞 E)) (_ : v = u) (f : v.adicCompletion E →+* u.adicCompletion E), Continuous f →
      (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → GeneralLinearGroup.map f (Y v) = Y u := by
    rintro v rfl f hf hext
    have hfs : (f : v.adicCompletion E → v.adicCompletion E) = id :=
      (HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext fun k => hext k)
    refine Units.ext (Matrix.ext fun i j => ?_)
    exact congrFun hfs ((Y v).val i j)
  have h := key _ (GlobalTheory.SplitPts.conjSrc_conjSrc_cm u)
    ((conjLoc (GlobalTheory.SplitPts.conjE E) u).comp (conjLoc (GlobalTheory.SplitPts.conjE E) (conjSrc (GlobalTheory.SplitPts.conjE E) u)))
    ((conjLoc_spec _ u).1.comp (conjLoc_spec _ _).1) fun k => by
      rw [RingHom.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
      exact congrArg _ (IsCMField.complexConj_apply_apply E k)
  rw [← h]
  rfl

end GlobalTheory.BCT.LocGlue

theorem GlobalTheory.BCT.exists_finU_of_loc : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, ∀ S : Set (Pl E), IsSection S → ∀ y : ∀ w : Pl E, UL n w, (∀ᶠ w in cofinite, y w ∈ KL n w) → ∃ x : finU E n, ∀ w ∈ S, toSub (UL n w) (cLoc w (x : UA E n)) = y w := by
  intro E _ _ _ _ n S hS y hy
  set c := GlobalTheory.SplitPts.conjE E with hc
  have hnotS : ∀ v, v ∉ S → conjSrc c v ∈ S := by
    intro v hv
    obtain ⟨s, ⟨hsS, hsv⟩, -⟩ := hS v
    have hne : v ≠ s := fun e => hv (e ▸ hsS)
    have hsp : IsSplitAt s := ⟨v, hne, hsv.symm⟩
    obtain ⟨-, -, hover⟩ := GlobalTheory.SplitPts.over_split hsp
    rcases hover v hsv.symm with h | h
    · exact absurd h hne
    · rw [h, GlobalTheory.SplitPts.conjSrc_conjSrc_cm]; exact hsS
  have hSsplit : ∀ v ∈ S, IsSplitAt v → conjSrc c v ∉ S := by
    intro v hv hsp h
    obtain ⟨hne, hund, -⟩ := GlobalTheory.SplitPts.over_split hsp
    exact hne ((hS v).unique ⟨h, hund⟩ ⟨hv, rfl⟩)
  let z : ∀ v : Pl E, GLw n v := fun v => if v ∈ S then (y v).1 else
    invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1)
  have hz_in : ∀ v ∈ S, z v = (y v).1 := fun v hv => if_pos hv
  have hz_out : ∀ v, v ∉ S → z v = invT n _ (GeneralLinearGroup.map (conjLoc c v) (y (conjSrc c v)).1) :=
    fun v hv => if_neg hv
  have hint : ∀ᶠ v in cofinite, z v ∈ GlobalTheory.LFun.KGL v n := by
    have h1 : ∀ᶠ v in cofinite, (y v).1 ∈ GlobalTheory.LFun.KGL v n := hy.mono fun v hv => Subgroup.mem_subgroupOf.1 hv
    have h2 := (conjSrc_injective c).tendsto_cofinite.eventually h1
    filter_upwards [h1, h2] with v a1 a2
    by_cases hv : v ∈ S
    · rw [hz_in v hv]; exact a1
    · rw [hz_out v hv]; exact GlobalTheory.BCT.LocGlue.intst E n _ v (conjLoc c v) (conjLoc_spec c v).2.2 _ a2
  obtain ⟨k, hk⟩ := GlobalTheory.BCT.LocGlue.glue E n z hint
  have hk' : ∀ u, ((GeneralLinearGroup.map (pLoc E (conjSrc c u)) k).val.map (conjLoc c u))ᵀ *
      (GeneralLinearGroup.map (pLoc E u) k).val = 1 := by
    intro u
    rw [hk, hk]
    show ((GeneralLinearGroup.map (conjLoc c u) (z (conjSrc c u))).val)ᵀ * (z u).val = 1
    by_cases hu : u ∈ S
    · by_cases hsp : IsSplitAt u
      · rw [hz_out _ (hSsplit u hu hsp), hz_in u hu, GlobalTheory.SplitPts.invT_map,
          GlobalTheory.BCT.LocGlue.twice E n (fun v => (y v).1) u]
        change ((((y u).1)⁻¹ : GLw n u).val)ᵀᵀ * (y u).1.val = 1
        rw [Matrix.transpose_transpose, Units.inv_mul]
      · have hcu : conjSrc c u = u := by
          by_contra h
          exact hsp ⟨_, h, (GlobalTheory.Mem.Chr.under_eq_iff_conjPl (IsCMField.complexConj E)
            (Algebra.IsQuadraticExtension.finrank_eq_two _ _) (IsCMField.complexConj_ne_one E) u _).2
            (Or.inr (GlobalTheory.SplitPts.conjPl_self_conjSrc u))⟩
        rw [hz_in _ (by rw [hcu]; exact hu), hz_in u hu, GlobalTheory.BCT.LocGlue.ns E n (fun v => (y v).1) u hsp]
        have key : ∀ g : GLw n u, g ∈ UL n u → g ∈ UJ (cj u) 1 := by
          intro g hg
          unfold UL at hg
          rwa [if_neg hsp] at hg
        have hUL : (y u).1 ∈ UJ (cj u) 1 := key _ (y u).2
        have h3 : cT (cj u) (y u).1.val * 1 * (y u).1.val = 1 := hUL
        rw [Matrix.mul_one] at h3
        exact h3
    · rw [hz_out u hu, hz_in _ (hnotS u hu)]
      change ((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1).val)ᵀ *
        (((GeneralLinearGroup.map (conjLoc c u) (y (conjSrc c u)).1)⁻¹ : GLw n u).val)ᵀ = 1
      rw [← Matrix.transpose_mul, Units.inv_mul, Matrix.transpose_one]
  let x : finU E n := ⟨⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩, MonoidHom.mem_ker.2 (pInf_finGL k)⟩
  refine ⟨x, fun w hw => ?_⟩
  show toSub (UL n w) (cLoc w ⟨finGL E n k, GlobalTheory.SplitPts.finGL_mem_UA k hk'⟩) = y w
  rw [GlobalTheory.SplitPts.cLoc_finGL, hk, hz_in w hw]
  unfold toSub
  rw [dif_pos (y w).2]
