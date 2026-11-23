import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.PlaneSupports.PlaneSupp
import GroundTheory.GlobalFields.Adele.WeakApprox
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousSingleV

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Sa2 GlobalTheory.CompanionTheory.SaGen
open scoped TensorProduct Topology

namespace GlobalTheory.CompanionTheory.SaGen.DensePair

variable {F : Type} [Field F] [NumberField F]

theorem idem_mul_of_subset {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) :
    b * a = a := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul]
    funext w
    change fstA F b w * fstA F a w = fstA F a w
    by_cases hw : w ∈ A₁
    · rw [hb.1 w (h₁ hw), one_mul]
    · rw [ha.2.1 w hw, mul_zero]
  · rw [map_mul, map_mul]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.1 v (h₂ hv), one_mul]
    · rw [ha.2.2.2 v hv, mul_zero]

theorem idem_mul_of_disjoint {A₁ B₁ : Finset (InfinitePlace F)} {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))}
    {a b : AF F} (ha : IsPlacesIdem A₁ A₂ a) (hb : IsPlacesIdem B₁ B₂ b) (h₁ : Disjoint A₁ B₁)
    (h₂ : Disjoint A₂ B₂) : a * b = 0 := by
  refine adele_ext ?_ (finAdele_ext fun v => ?_)
  · rw [map_mul, map_zero]
    funext w
    change fstA F a w * fstA F b w = 0
    by_cases hw : w ∈ A₁
    · rw [hb.2.1 w (Finset.disjoint_left.1 h₁ hw), mul_zero]
    · rw [ha.2.1 w hw, zero_mul]
  · rw [map_mul, map_mul, map_zero, map_zero]
    by_cases hv : v ∈ A₂
    · rw [hb.2.2.2 v (Finset.disjoint_left.1 h₂ hv), mul_zero]
    · rw [ha.2.2.2 v hv, zero_mul]

def sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj 1 + ∑ v : S₂, (placeMapFin v.1).inj 1

def glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F)))
    (p : (∀ v : S₂, v.1.adicCompletion F) × (∀ w : S₁, w.1.Completion)) : AF F :=
  ∑ w : S₁, (placeMapInf w.1).inj (p.2 w) + ∑ v : S₂, (placeMapFin v.1).inj (p.1 v)

theorem continuous_glue (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    Continuous (glue S₁ S₂) := by
  unfold glue
  refine Continuous.add ?_ ?_
  · exact continuous_finset_sum _ fun w _ =>
      (placeMapInf w.1).cont_inj.comp ((continuous_apply w).comp continuous_snd)
  · exact continuous_finset_sum _ fun v _ =>
      (placeMapFin v.1).cont_inj.comp ((continuous_apply v).comp continuous_fst)

theorem glue_proj (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) (a : AF F) :
    glue S₁ S₂ (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) = sumIdem S₁ S₂ * a := by
  simp only [glue, sumIdem, PlaceMap.inj_proj, add_mul, Finset.sum_mul]

theorem inf_proj_inf_ne {w u : InfinitePlace F} (h : w ≠ u) (y : u.Completion) :
    (placeMapInf w).proj ((placeMapInf u).inj y) = 0 :=
  singleI_ne h y

theorem inf_proj_fin (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (y : v.adicCompletion F) :
    (placeMapInf w).proj ((placeMapFin v).inj y) = 0 := rfl

theorem fin_proj_inf (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (y : w.Completion) :
    (placeMapFin v).proj ((placeMapInf w).inj y) = 0 :=
  map_zero (evalV F v)

theorem fin_proj_fin_ne {v u : HeightOneSpectrum (𝓞 F)} (h : v ≠ u) (y : u.adicCompletion F) :
    (placeMapFin v).proj ((placeMapFin u).inj y) = 0 :=
  StrongApprox.evalV_single_ne h y

theorem isPlacesIdem_sumIdem (S₁ : Finset (InfinitePlace F)) (S₂ : Finset (HeightOneSpectrum (𝓞 F))) :
    IsPlacesIdem S₁ S₂ (sumIdem S₁ S₂) := by
  classical
  have hI : ∀ w, (placeMapInf w).proj (sumIdem S₁ S₂) =
      ∑ u : S₁, (placeMapInf w).proj ((placeMapInf u.1).inj 1) := by
    intro w
    simp only [sumIdem, map_add, map_sum, inf_proj_fin, Finset.sum_const_zero, add_zero]
  have hF : ∀ v, (placeMapFin v).proj (sumIdem S₁ S₂) =
      ∑ u : S₂, (placeMapFin v).proj ((placeMapFin u.1).inj 1) := by
    intro v
    simp only [sumIdem, map_add, map_sum, fin_proj_inf, Finset.sum_const_zero, zero_add]
  refine ⟨fun w hw => ?_, fun w hw => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · refine (hI w).trans ?_
    rw [Finset.sum_eq_single (⟨w, hw⟩ : S₁)]
    · exact (placeMapInf w).proj_inj 1
    · intro u _ hu
      exact inf_proj_inf_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hI w).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact inf_proj_inf_ne (fun h : w = u.1 => hw (by rw [h]; exact u.2)) 1
  · refine (hF v).trans ?_
    rw [Finset.sum_eq_single (⟨v, hv⟩ : S₂)]
    · exact (placeMapFin v).proj_inj 1
    · intro u _ hu
      exact fin_proj_fin_ne (fun h => hu (Subtype.ext h.symm)) 1
    · intro h
      exact absurd (Finset.mem_univ _) h
  · refine (hF v).trans (Finset.sum_eq_zero fun u _ => ?_)
    exact fin_proj_fin_ne (fun h : v = u.1 => hv (by rw [h]; exact u.2)) 1

section Two

variable {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
  [TopologicalSpace K₂]

theorem proj_idem_one (P : PlaceMap F K₁) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} {d : AF F} (hP : IsPlacesIdem A₁ A₂ (P.inj 1))
    (hd : IsPlacesIdem B₁ B₂ d) (h₁ : A₁ ⊆ B₁) (h₂ : A₂ ⊆ B₂) : P.proj d = 1 := by
  have h := congrArg P.proj (idem_mul_of_subset hP hd h₁ h₂)
  rwa [map_mul, P.proj_inj, mul_one] at h

theorem proj_inj_other (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) (h : P₁.inj 1 * P₂.inj 1 = 0) (x : K₂) :
    P₁.proj (P₂.inj x) = 0 := by
  have e : P₂.inj x = P₂.inj 1 * P₂.inj x := by
    have := P₂.inj_proj (P₂.inj x)
    rwa [P₂.proj_inj] at this
  have h0 : P₁.proj (P₂.inj 1) = 0 := by
    have := congrArg P₁.proj h
    rwa [map_mul, P₁.proj_inj, one_mul, map_zero] at this
  rw [e, map_mul, h0, zero_mul]

end Two

theorem denseRange_pair {K₁ K₂ : Type} [Field K₁] [Algebra F K₁] [TopologicalSpace K₁] [Field K₂] [Algebra F K₂]
    [TopologicalSpace K₂] (P₁ : PlaceMap F K₁) (P₂ : PlaceMap F K₂) {A₁ B₁ : Finset (InfinitePlace F)}
    {A₂ B₂ : Finset (HeightOneSpectrum (𝓞 F))} (h₁ : IsPlacesIdem A₁ A₂ (P₁.inj 1))
    (h₂ : IsPlacesIdem B₁ B₂ (P₂.inj 1)) (d₁ : Disjoint A₁ B₁) (d₂ : Disjoint A₂ B₂) :
    DenseRange (fun f : F => (algebraMap F K₁ f, algebraMap F K₂ f)) := by
  classical
  have hD := isPlacesIdem_sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)
  have p₁ : P₁.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₁ h₁ hD Finset.subset_union_left Finset.subset_union_left
  have p₂ : P₂.proj (sumIdem (A₁ ∪ B₁) (A₂ ∪ B₂)) = 1 :=
    proj_idem_one P₂ h₂ hD Finset.subset_union_right Finset.subset_union_right
  have z₁ : P₁.inj 1 * P₂.inj 1 = 0 := idem_mul_of_disjoint h₁ h₂ d₁ d₂
  have z₂ : P₂.inj 1 * P₁.inj 1 = 0 := by rw [mul_comm]; exact z₁
  let G := fun p => (P₁.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p), P₂.proj (glue (A₁ ∪ B₁) (A₂ ∪ B₂) p))
  have hG : Continuous G :=
    (P₁.cont_proj.comp (continuous_glue _ _)).prodMk (P₂.cont_proj.comp (continuous_glue _ _))
  have hval : ∀ a : AF F, G (fun v => (placeMapFin v.1).proj a, fun w => (placeMapInf w.1).proj a) =
      (P₁.proj a, P₂.proj a) := by
    intro a
    simp only [G, glue_proj, map_mul, p₁, p₂, one_mul]
  have hsurj : Function.Surjective G := by
    rintro ⟨x₁, x₂⟩
    refine ⟨_, (hval (P₁.inj x₁ + P₂.inj x₂)).trans ?_⟩
    rw [map_add, map_add, P₁.proj_inj, P₂.proj_inj, proj_inj_other P₁ P₂ z₁, proj_inj_other P₂ P₁ z₂, add_zero,
      zero_add]
  have hdense := hsurj.denseRange.comp (GroundTheory.Global.denseRange_algebraMap_prod_pi (A₂ ∪ B₂) (A₁ ∪ B₁)) hG
  convert hdense using 1
  funext f
  have := hval (algebraMap F (AF F) f)
  simp only [AlgHom.commutes] at this
  exact this.symm

end GlobalTheory.CompanionTheory.SaGen.DensePair
