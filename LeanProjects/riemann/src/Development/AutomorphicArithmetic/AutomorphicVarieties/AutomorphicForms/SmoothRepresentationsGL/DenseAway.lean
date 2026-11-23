import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb
import GroundTheory.GlobalFields.Adele.WeakApprox

open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

noncomputable section

namespace UpperTheory.V.Af.Smo.DenseAwayFromPlace

open GlobalTheory.CuspRep (cornerGL matN map_cornerGL_of_hom map_cornerGL_of_zero pFin_finGL)

private theorem dense_gl {K R : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] (n : ℕ)
    (q : K →+* R) (hq : DenseRange q) : DenseRange (GeneralLinearGroup.map (n := Fin n) q) := by
  have ho : Topology.IsOpenEmbedding (Units.val : GL (Fin n) R → Matrix (Fin n) (Fin n) R) := by
    have h : ∀ (M : Type) [NormedRing M], CompleteSpace M → Topology.IsOpenEmbedding (Units.val : Mˣ → M) :=
      fun _ _ _ => Units.isOpenEmbedding_val
    exact @h _ Matrix.linftyOpNormedRing (inferInstanceAs (CompleteSpace (Fin n → Fin n → R)))
  have hd : DenseRange fun x : Matrix (Fin n) (Fin n) K => x.map q :=
    DenseRange.piMap fun _ : Fin n => DenseRange.piMap fun _ : Fin n => hq
  refine dense_iff_inter_open.2 fun U hU hne => ?_
  obtain ⟨x, u, hu, e⟩ := hd.exists_mem_open (ho.isOpenMap U hU) (hne.image _)
  have h1 : IsUnit (q x.det) := by
    rw [RingHom.map_det, RingHom.mapMatrix_apply, ← e]
    exact (Matrix.isUnit_iff_isUnit_det _).1 u.isUnit
  have h2 : x.det ≠ 0 := fun h => by
    rw [h, map_zero] at h1
    exact not_isUnit_zero h1
  exact ⟨u, hu, GeneralLinearGroup.mkOfDetNeZero x h2, Units.ext e.symm⟩

private theorem dense_abs {K R A : Type} [Field K] [NormedCommRing R] [CompleteSpace R] [Nontrivial R] [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] (n : ℕ) (a : K →+* A) (p : A →+* R) (s : R →ₙ+* A) (hs : Continuous s)
    (hp : ∀ x, p (s x) = x) (hq : DenseRange (p.comp a)) :
    Dense {x : GL (Fin n) A | ∃ γ k, GeneralLinearGroup.map p k = 1 ∧ x = GeneralLinearGroup.map a γ * k} := by
  have hc : Continuous (cornerGL n s) := by
    refine Continuous.units_map _ ?_
    change Continuous fun x : Matrix (Fin n) (Fin n) R => 1 - matN n s 1 + matN n s x
    exact continuous_const.add (continuous_id.matrix_map hs)
  have hps : ∀ y, GeneralLinearGroup.map p (cornerGL n s y) = y := fun y => by
    rw [map_cornerGL_of_hom s p (RingHom.id _) hp]
    rfl
  refine dense_iff_inter_open.2 fun U hU ⟨g, hg⟩ => ?_
  let Φ : GL (Fin n) R → GL (Fin n) A := fun y => cornerGL n s y * ((cornerGL n s (GeneralLinearGroup.map p g))⁻¹ * g)
  have hΦ : Continuous Φ := hc.mul continuous_const
  obtain ⟨γ, hγ⟩ := (dense_gl n _ hq).exists_mem_open (hU.preimage hΦ)
    ⟨GeneralLinearGroup.map p g, by simpa [Φ] using hg⟩
  refine ⟨_, hγ, γ, (GeneralLinearGroup.map a γ)⁻¹ * Φ (GeneralLinearGroup.map (p.comp a) γ), ?_, by simp⟩
  have e : GeneralLinearGroup.map p (GeneralLinearGroup.map a γ) = GeneralLinearGroup.map (p.comp a) γ := rfl
  simp only [Φ, map_mul, map_inv, hps, e, inv_mul_cancel, mul_one]

variable {E : Type} [Field E] [NumberField E]

private theorem cont_sLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (sLoc E w) := by
  classical
  have hle : (Filter.cofinite : Filter (HeightOneSpectrum (𝓞 E))) ≤ Filter.principal {w}ᶜ :=
    Filter.le_principal_iff.2 (Set.finite_singleton w).compl_mem_cofinite
  let f : w.adicCompletion E → RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) (Filter.principal {w}ᶜ) :=
    fun x => ⟨Pi.single w x, Filter.eventually_principal.2 fun v hv => by
      rw [Pi.single_eq_of_ne hv]
      exact zero_mem _⟩
  have hf : Continuous f := RestrictedProduct.continuous_rng_of_principal.2
    (continuous_single (A := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w)
  exact (RestrictedProduct.continuous_inclusion hle).comp hf

variable (S : Finset (HeightOneSpectrum (𝓞 E)))

private theorem sum_mem (x : ∀ v : S, v.1.adicCompletion E) (w : S) : pLoc E w.1 (∑ v : S, sLoc E v.1 (x v)) = x w := by
  classical
  rw [map_sum, Finset.sum_eq_single w]
  · exact Pi.single_eq_same (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E) w.1 _
  · exact fun v _ h => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun e => h (Subtype.ext e.symm)) _
  · simp

private theorem sum_notMem (x : ∀ v : S, v.1.adicCompletion E) {w : HeightOneSpectrum (𝓞 E)} (hw : w ∉ S) :
    pLoc E w (∑ v : S, sLoc E v.1 (x v)) = 0 := by
  classical
  rw [map_sum]
  exact Finset.sum_eq_zero fun v _ => Pi.single_eq_of_ne (M := fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
    (fun e : w = v.1 => hw (e ▸ v.2)) _

private abbrev RS : Type :=
  (∀ v : S, v.1.adicCompletion E) × (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion)

private def pS : Ad E →+* RS S :=
  (RingHom.pi fun v : S => (pLoc E v.1).comp (pFin E)).prod
    (RingHom.pi fun w => (Pi.evalRingHom (fun w : InfinitePlace E => w.Completion) w.1).comp
      (RingHom.fst (InfiniteAdeleRing E) (Af E)))

private def sS : RS S →ₙ+* Ad E where
  toFun x := ((fun w => x.2 ⟨w, Finset.mem_univ w⟩, ∑ v : S, sLoc E v.1 (x.1 v)) : InfiniteAdeleRing E × Af E)
  map_mul' x y := Prod.ext rfl (FiniteAdeleRing.ext _ fun w => by
    change pLoc E w (∑ v : S, sLoc E v.1 ((x.1 * y.1) v)) =
      pLoc E w ((∑ v : S, sLoc E v.1 (x.1 v)) * ∑ v : S, sLoc E v.1 (y.1 v))
    rw [map_mul]
    by_cases hw : w ∈ S
    · rw [sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩, sum_mem S _ ⟨w, hw⟩]
      rfl
    · rw [sum_notMem S _ hw, sum_notMem S _ hw, zero_mul])
  map_zero' := Prod.ext rfl (Finset.sum_eq_zero fun v _ => map_zero _)
  map_add' x y := Prod.ext rfl ((Finset.sum_congr rfl fun v _ => map_add _ _ _).trans Finset.sum_add_distrib)

private theorem cont_sS : Continuous (sS S) :=
  Continuous.prodMk (continuous_pi fun w => (continuous_apply _).comp continuous_snd)
    (continuous_finset_sum _ fun v _ => (cont_sLoc v.1).comp ((continuous_apply v).comp continuous_fst))

private theorem pS_sS (x : RS S) : pS S (sS S x) = x :=
  Prod.ext (funext fun v => sum_mem S x.1 v) rfl

end UpperTheory.V.Af.Smo.DenseAwayFromPlace

end

open UpperTheory.V.Af.Smo.DenseAwayFromPlace in
theorem UpperTheory.V.Af.Smo.denseAway :
    UpperTheory.V.Af.Smo.DenseAway := by
  intro E _ _ n S
  haveI : Inhabited (Finset.univ : Finset (InfinitePlace E)) := ⟨⟨Classical.arbitrary _, Finset.mem_univ _⟩⟩
  haveI : Nontrivial (∀ w : (Finset.univ : Finset (InfinitePlace E)), w.1.Completion) := Pi.nontrivial
  haveI : Nontrivial (RS S) := nontrivial_prod_right
  refine (dense_abs n (algebraMap E (Ad E)) (pS S) (sS S) (cont_sS S) (pS_sS S)
    (GroundTheory.Global.denseRange_algebraMap_prod_pi S Finset.univ)).mono ?_
  rintro _ ⟨γ, k, hk, rfl⟩
  have h : ∀ i j, pS S (k i j) = (1 : Matrix (Fin n) (Fin n) (RS S)) i j := fun i j =>
    congrArg (fun x : GL (Fin n) (RS S) => x i j) hk
  refine ⟨γ, GeneralLinearGroup.map (pFin E) k, fun w hw => ?_, congrArg _ ?_⟩
  · refine Units.ext (Matrix.ext fun i j => ?_)
    refine (congrFun (congrArg Prod.fst (h i j)) ⟨w, hw⟩).trans ?_
    by_cases e : i = j <;> simp [Matrix.one_apply, e]
  · refine Units.ext (Matrix.ext fun i j => Prod.ext (funext fun w => ?_) ?_)
    · refine (congrFun (congrArg Prod.snd (h i j)) ⟨w, Finset.mem_univ w⟩).trans ?_
      change _ = (((1 : Matrix (Fin n) (Fin n) (Ad E)) i j).1 - 0 + 0) w
      rw [add_zero, sub_zero]
      by_cases e : i = j <;> simp only [Matrix.one_apply, e, if_true, if_false] <;> rfl
    · exact (congrArg (fun x : GL (Fin n) (Af E) => x i j)
        (GlobalTheory.CuspRep.pFin_finGL (GeneralLinearGroup.map (pFin E) k))).symm
