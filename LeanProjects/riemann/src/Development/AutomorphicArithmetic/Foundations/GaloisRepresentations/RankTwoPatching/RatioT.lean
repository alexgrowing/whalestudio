import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RankTwoPatching.PsForm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.RealOld
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PAdicTorsionHoms.PlainOf
import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.GenericIrreducibility.GenericUnitary.NormEqOneOfValuationEqOne

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published
open UpperTheory.Zero.LLC UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter ValuativeRel

namespace UpperTheory.Gal.SV.GlobalSectionsBijection

section Loc

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem ord_unif : GlobalTheory.SmGL.ord k (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 1 := by
  have hs := (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.polFacts k).1
  obtain ⟨p, hp⟩ := valuation_surjective (uniformizer k : ValueGroupWithZero k)
  exact ord_eq_one (le_antisymm (le_uniformizer_iff.2 hs.1) (hp ▸ hs.2 p (hp ▸ uniformizer_lt_one)))

private theorem norm_neg_one (ξ : kˣ →* ℂˣ) (hξ : IsSmoothChar ξ) {x : kˣ} (hx : GlobalTheory.SmGL.ord k x = -1) :
    ‖((ξ x : ℂˣ) : ℂ)‖ = ‖((ξ (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) : ℂˣ) : ℂ)‖⁻¹ := by
  have hu : GlobalTheory.SmGL.ord k (x * UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif k) = 0 := by
    rw [ord_mul, hx, ord_unif]
    simp
  have h1 := PositivityTheory.RgUd.Exp.Rpow.norm_eq_one_of_valuation_eq_one ξ hξ (ord_eq_zero_iff.1 hu)
  rw [map_mul, Units.val_mul, norm_mul] at h1
  exact eq_inv_of_mul_eq_one_left h1

end Loc

section WD

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

private theorem eig_sum {n : ℕ} (c : Fin n → Weil h →* ℂˣ) (hc : ∀ i, GlobalTheory.WeilDeligne.IsSmooth (c i)) (s : ℝ)
    {φ : ↥(Weil h)} (hφ : deg φ = 1) {α : ℂ}
    (hα : α ∈ ((sumList (List.ofFn fun i => WD.lpOfChar h (c i) (hc i))).lpTw s).eig φ) :
    ∃ i, α = ((c i φ : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ ((s : ℝ) : ℂ) := by
  rw [GlobalTheory.RowTie.EigTwist.eig_lpTw _ hφ s, Multiset.mem_map] at hα
  obtain ⟨y, hy, rfl⟩ := hα
  have h1 : ∀ i, (WD.lpOfChar h (c i) (hc i)).charPol φ = X - C ((c i φ : ℂˣ) : ℂ) := fun i => by
    rw [WD.lpOfChar, WD.charPol_mk, WDRep.ofChars_ρ, charpoly_diagEnd]
    simp
  have h2 := Polynomial.isRoot_of_mem_roots hy
  rw [GlobalTheory.LocLanglands.CuspExt.charPol_sumList, List.map_ofFn] at h2
  have h3 : (List.ofFn ((fun y : WD h => y.charPol φ) ∘ fun i => WD.lpOfChar h (c i) (hc i))).prod =
      ∏ i, (X - C ((c i φ : ℂˣ) : ℂ)) := by
    rw [List.prod_ofFn]
    exact Finset.prod_congr rfl fun i _ => h1 i
  rw [h3, Polynomial.IsRoot.def, Polynomial.eval_prod, Finset.prod_eq_zero_iff] at h2
  obtain ⟨i, -, hi⟩ := h2
  refine ⟨i, ?_⟩
  simp only [eval_sub, eval_X, eval_C] at hi
  rw [sub_eq_zero.1 hi]

end WD

end UpperTheory.Gal.SV.GlobalSectionsBijection

open UpperTheory.Gal.SV.GlobalSectionsBijection in
theorem UpperTheory.Gal.SV.ratioT :
    UpperTheory.Gal.SV.RatioT := by
  intro K Ω _ _ _ _ _ _ A w h rc ⟨a, ha, L⟩ n π t hw σ hσ φ hφ α hα β hβ
  have hP := (UpperTheory.V.Z.Win.plainRec K Ω A w h rc ⟨a, ha, L⟩ n π t hw σ hσ).1
  obtain ⟨ξ, hξ, hs, hu⟩ := GlobalTheory.RoadU.plainTor_exists_chars _ _ hP
  have hs' : HasSupport σ.ρ (GlobalTheory.RoadU.chars ξ hξ) := hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm
  have hA := psForm L σ ξ hξ hs' hu
  rw [hA] at hα hβ
  obtain ⟨i, rfl⟩ := eig_sum _ _ _ hφ hα
  obtain ⟨j, rfl⟩ := eig_sum _ _ _ hφ hβ
  have hq : ((normV w : ℕ) : ℝ) = (Ideal.absNorm w.asIdeal : ℝ) := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hq1 : (1 : ℝ) < ((normV w : ℕ) : ℝ) := by exact_mod_cast GlobalTheory.WeilDeligne.one_lt_normV w
  have hord : GlobalTheory.SmGL.ord (w.adicCompletion K) (a φ) = -1 := by rw [ha.ord_eq φ, hφ]
  have hwin : ∀ m, ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) < ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ ∧
      ‖((ξ m (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ < ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) := fun m => by
    rw [hq]
    exact hw.2 _ ⟨σ, hσ, hs'⟩ (ξ m) ⟨hξ m, Multiset.mem_map_of_mem _ (Finset.mem_univ_val m)⟩
  have hbi := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin i).1
  have hbj := (Real.rpow_pos_of_pos (by linarith) _).trans (hwin j).1
  have hlt : ‖((ξ j (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ <
      ‖((ξ i (UpperTheory.V.Z.ImaginaryQuadraticEtaCharacter.unif (w.adicCompletion K)) : ℂˣ) : ℂ)‖ * ((normV w : ℕ) : ℝ) := by
    have e : ((normV w : ℕ) : ℝ) ^ (t + 1 / 2) = ((normV w : ℕ) : ℝ) ^ (t - 1 / 2) * ((normV w : ℕ) : ℝ) := by
      rw [← Real.rpow_add_one (by linarith)]
      congr 1
      ring
    calc _ < _ := (hwin j).2
      _ = _ := e
      _ < _ := mul_lt_mul_of_pos_right (hwin i).1 (by linarith)
  have hc : 0 < ‖((normV w : ℕ) : ℂ) ^ ((((1 - (n : ℝ)) / 2 : ℝ)) : ℂ)‖ := by
    refine norm_pos_iff.2 ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    intro e
    have : ((normV w : ℕ) : ℝ) = 0 := by exact_mod_cast e.1
    linarith
  simp only [MonoidHom.comp_apply]
  rw [norm_mul, norm_mul, norm_neg_one _ (hξ i) hord, norm_neg_one _ (hξ j) hord, ← mul_assoc]
  refine mul_lt_mul_of_pos_right ?_ hc
  rw [← div_eq_mul_inv, lt_div_iff₀ hbj, inv_mul_lt_iff₀ hbi]
  exact hlt
