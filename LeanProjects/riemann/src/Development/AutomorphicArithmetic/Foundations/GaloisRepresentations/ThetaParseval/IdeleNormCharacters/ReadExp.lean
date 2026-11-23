import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.IdeleNormCharacters.AbsFactsAlt
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenEmbeddingVal
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Host Formalism.ConjugateSelfDual Neutral.B1 ReciprocityTheory.Gal
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.HeckeGal GlobalTheory.CuspRep UpperTheory.Gal.TP.Chr
open scoped TensorProduct

noncomputable section

namespace UpperTheory.Gal.TP.Chr

private theorem exists_read {E : Type} [Field E] [NumberField E] (φ : E →+* ℂ) :
    ∃ ρ : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous ρ ∧
      ∀ x : E, ρ (algebraMap E (InfinitePlace.mk φ).Completion x) = φ x := by
  have hc := (InfinitePlace.Completion.isometry_extensionEmbedding (InfinitePlace.mk φ)).continuous
  have he : ∀ x : E, InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)
      (algebraMap E (InfinitePlace.mk φ).Completion x) = (InfinitePlace.mk φ).embedding x := fun x =>
    InfinitePlace.Completion.extensionEmbedding_coe (InfinitePlace.mk φ) (WithAbs.toAbs _ x)
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · exact ⟨_, hc, fun x => (he x).trans (by rw [h])⟩
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding (InfinitePlace.mk φ)),
      Complex.continuous_conj.comp hc, fun x => ?_⟩
    rw [RingHom.comp_apply, he, h, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

private theorem inf_formula {E ι : Type} [Field E] [NumberField E] [Fintype ι] (μ : HChar E) (φ : ι → E →+* ℂ)
    (m : ι → ℤ) (ρ : ∀ i, (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hc : ∀ i, Continuous (ρ i))
    (hρ : ∀ i x, ρ i (algebraMap E _ x) = φ i x)
    (h : ∀ k : Eˣ, ((μ.inf k : ℂˣ) : ℂ) = ∏ i, (φ i (k : E) / ‖φ i (k : E)‖) ^ m i)
    (y : (InfiniteAdeleRing E)ˣ) :
    ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E y) : ℂˣ) : ℂ) =
      ∏ i, (ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
        ‖ρ i ((y : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
  have hne : ∀ (i) (u : (InfiniteAdeleRing E)ˣ), ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) ≠ 0 := by
    intro i u e
    have h1 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) *
        ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)) = 1 :=
      congrFun u.mul_inv (InfinitePlace.mk (φ i))
    have h2 := congrArg (ρ i) h1
    rw [map_mul, map_one, e, zero_mul] at h2
    exact zero_ne_one h2
  have hci : ∀ i, Continuous fun u : (InfiniteAdeleRing E)ˣ => ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) :=
    fun i => (hc i).comp ((continuous_apply _).comp Units.continuous_val)
  have hL : Continuous fun u : (InfiniteAdeleRing E)ˣ => ((μ.1 (GlobalTheory.CompanionTheory.HeckeFin.infIdele E u) : ℂˣ) : ℂ) :=
    Units.continuous_val.comp (μ.2.1.comp (GlobalTheory.CompanionTheory.HeckeFin.continuous_infIdele E))
  have hR : Continuous fun u : (InfiniteAdeleRing E)ˣ => ∏ i, (ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i))) /
      ‖ρ i ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ i)))‖) ^ m i := by
    refine continuous_finset_prod _ fun i _ => ?_
    refine Continuous.zpow₀ ((hci i).div (Complex.continuous_ofReal.comp (hci i).norm) fun u => ?_) _ fun u => Or.inl ?_
    · exact Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u))
    · exact div_ne_zero (hne i u) (Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne i u)))
  refine congrFun ((GlobalTheory.CompanionTheory.HeckeFin.denseRange_units E).equalizer hL hR (funext fun k => ?_)) y
  have e1 : GlobalTheory.CompanionTheory.HeckeFin.infIdele E (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) = infDiag k := by
    classical
    refine Units.ext ?_
    rw [infDiag, MonoidHom.finsetProd_apply, Units.coe_prod]
    let p1 : AdeleRing (𝓞 E) E →+* InfiniteAdeleRing E := RingHom.fst _ _
    let p2 : AdeleRing (𝓞 E) E →+* FiniteAdeleRing (𝓞 E) E := RingHom.snd _ _
    refine Prod.ext ?_ ?_
    · change _ = p1 _
      rw [map_prod]
      change _ = ∏ w : InfinitePlace E, Pi.mulSingle w (algebraMap E w.Completion (k : E))
      exact (Finset.univ_prod_mulSingle _).symm
    · change _ = p2 _
      rw [map_prod]
      exact (Finset.prod_eq_one fun _ _ => rfl).symm
  simp only [Function.comp_apply]
  rw [e1]
  refine (h k).trans (Finset.prod_congr rfl fun i _ => ?_)
  have e2 : ρ i (((Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E)
      (InfinitePlace.mk (φ i))) = φ i (k : E) := hρ i k
  rw [e2]

private theorem piInf_read {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {w : InfinitePlace F} (τ : EmbOver E w) (ρ : (InfinitePlace.mk τ.1).Completion →+* ℂ) (hc : Continuous ρ)
    (hρ : ∀ x, ρ (algebraMap E _ x) = τ.1 x) (z : AE F E) :
    piInf τ z = ρ ((GlobalTheory.UnitaryHeckeBaseChange.toAdele F E z).1 (InfinitePlace.mk τ.1)) := by
  have key : (fun b : InfiniteAdeleRing F => InfinitePlace.Completion.extensionEmbedding w (b w)) =
      fun b => ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E b (InfinitePlace.mk τ.1)) := by
    refine (InfiniteAdeleRing.denseRange_algebraMap F).equalizer
      ((InfinitePlace.Completion.isometry_extensionEmbedding w).continuous.comp (continuous_apply _))
      (hc.comp ((continuous_apply _).comp (GlobalTheory.UnitaryHeckeBaseChange.continuous_infiniteAdeleMap F E))) (funext fun x => ?_)
    have h1 : InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = w.embedding x :=
      InfinitePlace.Completion.extensionEmbedding_coe w (WithAbs.toAbs _ x)
    have h2 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E (algebraMap F _ x) (InfinitePlace.mk τ.1) =
        algebraMap E (InfinitePlace.mk τ.1).Completion (algebraMap F E x) :=
      congrFun (congrArg Prod.fst (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x)) _
    simp only [Function.comp_apply]
    change InfinitePlace.Completion.extensionEmbedding w (algebraMap F w.Completion x) = ρ _
    rw [h1, h2, hρ]
    exact (RingHom.congr_fun τ.2 x).symm
  induction z using TensorProduct.induction_on with
  | zero =>
    rw [map_zero, map_zero]
    exact (map_zero ρ).symm
  | add x y hx hy =>
    rw [map_add, hx, hy, map_add, ← map_add]
    rfl
  | tmul a e =>
    rw [GlobalTheory.UnitaryHeckeBaseChange.toAdele_tmul]
    have h3 : InfinitePlace.Completion.extensionEmbedding w (a.1 w) =
        ρ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1)) := congrFun key a.1
    have h4 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E (AdeleRing (𝓞 E) E) e).1 (InfinitePlace.mk τ.1) =
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap F E a.1 (InfinitePlace.mk τ.1) *
          algebraMap E (InfinitePlace.mk τ.1).Completion e := rfl
    rw [h4, map_mul, ← h3, hρ]
    rfl

theorem readExp : ReadExp := by
  intro E _ _ _ emb μ χ m hR hI z hz
  have hcm := GlobalTheory.GalOfCusp.isCMExt_real E
  set x : Ideles E := Units.map (GlobalTheory.UnitaryHeckeBaseChange.adeleEquiv hcm).toRingHom.toMonoidHom z with hx
  have hx1 : (x : AdeleRing (𝓞 E) E) = GlobalTheory.UnitaryHeckeBaseChange.toAdele _ E (z : AE (maximalRealSubfield E) E) := rfl
  have hfin : (x : AdeleRing (𝓞 E) E).2 = 1 := by
    let u : AF (maximalRealSubfield E) := (0, 1)
    have h0 : u • ((z : AE (maximalRealSubfield E) E) - 1) = 0 := hz u (map_zero _)
    have h1 := congrArg (GlobalTheory.UnitaryHeckeBaseChange.toAdele (maximalRealSubfield E) E) h0
    rw [Algebra.smul_def, map_mul, GlobalTheory.UnitaryHeckeBaseChange.toAdele_algebraMap, map_sub, map_one, map_zero, ← hx1] at h1
    have h2 := congrArg Prod.snd h1
    have h3 : (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 = 1 := map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteAdeleMap (maximalRealSubfield E) E)
    change (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap (maximalRealSubfield E) E u).2 * ((x : AdeleRing (𝓞 E) E).2 - 1) = 0 at h2
    rw [h3, one_mul] at h2
    exact sub_eq_zero.1 h2
  let y : (InfiniteAdeleRing E)ˣ := Units.map (RingHom.fst (InfiniteAdeleRing E) (FiniteAdeleRing (𝓞 E) E)).toMonoidHom x
  have hxy : x = GlobalTheory.CompanionTheory.HeckeFin.infIdele E y := Units.ext (Prod.ext rfl hfin)
  choose ρ hc hρ using fun w => exists_read (emb w).1
  have hf := inf_formula μ (fun w => (emb w).1) m ρ hc hρ hI y
  rw [hR z]
  change ((μ.1 x : ℂˣ) : ℂ) = _
  rw [hxy, hf]
  refine Finset.prod_congr rfl fun w _ => ?_
  rw [piInf_read (emb w) (ρ w) (hc w) (hρ w) z]
  rfl

end UpperTheory.Gal.TP.Chr

end
