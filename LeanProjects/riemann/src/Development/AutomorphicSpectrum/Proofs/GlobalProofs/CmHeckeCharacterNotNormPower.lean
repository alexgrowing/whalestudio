import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeTateFunctionalEquationCM
import GroundTheory.GlobalFields.TateThesis.RootNumberLocalFinite
import GroundTheory.GlobalFields.AnalyticClassNumber.HeckeContinued
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousIdeleCircle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EtaTildeIsUnitArgAtCmTypePlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCMTypeOfEmbeddingsCardEqFinrank
open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds GlobalTheory.HeckeEps GlobalTheory.CompanionTheory.HeckeBridge GroundTheory.Global GroundTheory.LocalField GroundTheory.Global.IdeleGroup
open GroundTheory.Automorphic.GodementSection (localChar)
open Formalism.L2.Host (unif atFin unif_spec)

noncomputable section
namespace GlobalTheory.CompanionTheory.HeckeBridge.NotPow

open ReciprocityTheory.Neutral.Bridge.HCFR Neutral.B1
open Formalism.L2.Host (atInf)

theorem exists_ext_surj {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) (hw : (InfinitePlace.mk φ).IsComplex) :
    ∃ e : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous e ∧ (∀ k : L, e (algebraMap L _ k) = φ k) ∧
      Function.Surjective e ∧ ∀ x, ‖e x‖ = ‖x‖ := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_,
      InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw, fun x => ?_⟩
    · rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
      rfl
    · exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_, fun y => ?_, fun x => ?_⟩
    · rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
        InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
      exact Complex.conj_conj _
    · obtain ⟨x, hx⟩ := InfinitePlace.Completion.surjective_extensionEmbedding_of_isComplex hw
        ((starRingEnd ℂ) y)
      exact ⟨x, by rw [RingHom.comp_apply, hx, Complex.conj_conj]⟩
    · rw [RingHom.comp_apply, Complex.norm_conj]
      exact (InfinitePlace.Completion.isometry_extensionEmbedding _).norm_map_of_map_zero (map_zero _) x

theorem exists_norm_one_zpow_ne (m : ℤ) (hm : m ≠ 0) : ∃ ζ : ℂ, ‖ζ‖ = 1 ∧ ζ ^ m ≠ 1 := by
  refine ⟨Complex.exp (((Real.pi / m : ℝ) : ℂ) * Complex.I), Complex.norm_exp_ofReal_mul_I _, ?_⟩
  rw [← Complex.exp_int_mul]
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  have hx : (m : ℂ) * (((Real.pi / m : ℝ) : ℂ) * Complex.I) = (Real.pi : ℂ) * Complex.I := by
    push_cast
    field_simp
  rw [hx, Complex.exp_pi_mul_I]
  norm_num

private theorem exists_inclusion_mul_eq_mul_inclusion_of_normal {L : Type} [Field L] [NumberField L] (φ : L →+* ℂ) :
    ∃ c : (InfinitePlace.mk φ).Completion →+* ℂ, Continuous c ∧ ∀ k : L, c (algebraMap L _ k) = φ k := by
  rcases InfinitePlace.embedding_mk_eq φ with h | h
  · refine ⟨InfinitePlace.Completion.extensionEmbedding _,
      (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous, fun k => ?_⟩
    rw [InfinitePlace.Completion.algebraMap_apply, InfinitePlace.Completion.extensionEmbedding_coe, h]
    rfl
  · refine ⟨(starRingEnd ℂ).comp (InfinitePlace.Completion.extensionEmbedding _),
      Complex.continuous_conj.comp (InfinitePlace.Completion.isometry_extensionEmbedding _).continuous,
      fun k => ?_⟩
    rw [RingHom.comp_apply, InfinitePlace.Completion.algebraMap_apply,
      InfinitePlace.Completion.extensionEmbedding_coe, h, ComplexEmbedding.conjugate_coe_eq]
    exact Complex.conj_conj _

private theorem denseRange_units_map_infiniteAdeleRing (E : Type) [Field E] [NumberField E] :
    DenseRange (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom) := by
  have hopen : IsOpenMap (Units.val : (InfiniteAdeleRing E)ˣ → InfiniteAdeleRing E) :=
    Units.isOpenMap_val (R := (w : InfinitePlace E) → w.Completion)
  have hd := InfiniteAdeleRing.denseRange_algebraMap E
  rw [DenseRange, dense_iff_inter_open]
  rintro V hV ⟨u, hu⟩
  obtain ⟨_, ⟨u', hu', rfl⟩, k, hk⟩ := hd.inter_open_nonempty _ (hopen V hV) ⟨u, u, hu, rfl⟩
  by_cases hk0 : k = 0
  · have h0 : (u' : InfiniteAdeleRing E) = 0 := by rw [← hk, hk0, map_zero]
    have h01 : (0 : InfiniteAdeleRing E) = 1 := by rw [← u'.mul_inv, h0, zero_mul]
    haveI := subsingleton_of_zero_eq_one h01
    exact ⟨u', hu', 1, Units.ext (Subsingleton.elim _ _)⟩
  · exact ⟨u', hu', Units.mk0 k hk0, Units.ext (by simpa using hk)⟩

theorem comp_eq {E : Type} [Field E] [NumberField E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hb : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar E) {n : I → ℤ}
    (hn : Formalism.L2.Host.HChar.HasInf χ φ n) (i : I)
    (e : (InfinitePlace.mk (φ i)).Completion →+* ℂ) (hec : Continuous e)
    (he : ∀ k : E, e (algebraMap E _ k) = φ i k) (z : ((InfinitePlace.mk (φ i)).Completion)ˣ) :
    ((χ.1 (infIdele E _ z) : ℂˣ) : ℂ) =
      (e (z : (InfinitePlace.mk (φ i)).Completion) /
        ((‖e (z : (InfinitePlace.mk (φ i)).Completion)‖ : ℝ) : ℂ)) ^ n i := by
  classical
  choose c₀ hc₀ hc₀' using fun j => exists_inclusion_mul_eq_mul_inclusion_of_normal (φ j)
  let c : ∀ j, (InfinitePlace.mk (φ j)).Completion →+* ℂ := Function.update c₀ i e
  have hc : ∀ j, Continuous (c j) := by
    intro j
    by_cases hj : j = i
    · subst hj
      simpa [c] using hec
    · simpa [c, hj] using hc₀ j
  have hc' : ∀ j (k : E), c j (algebraMap E _ k) = φ j k := by
    intro j k
    by_cases hj : j = i
    · subst hj
      simpa [c] using he k
    · simpa [c, hj] using hc₀' j k
  let ι0 : InfiniteAdeleRing E →* NumberField.AdeleRing (NumberField.RingOfIntegers E) E :=
    MonoidHom.inl (InfiniteAdeleRing E) (IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E)
  have hι0 : Continuous ι0 := continuous_id.prodMk continuous_const
  obtain ⟨hχc, -⟩ := χ.2
  let Ψ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ((χ.1 (Units.map ι0 u) : ℂˣ) : ℂ)
  let Θ : (InfiniteAdeleRing E)ˣ → ℂ := fun u => ∏ j, (c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) /
      ((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ^ n j
  have hne : ∀ (j : I) (u : (InfiniteAdeleRing E)ˣ),
      c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) ≠ 0 := by
    intro j u h0
    have h1 := congrArg (fun x : InfiniteAdeleRing E => x (InfinitePlace.mk (φ j))) u.mul_inv
    have h2 : (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 0 := (map_eq_zero (c j)).1 h0
    change (u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) *
      ((u⁻¹ : (InfiniteAdeleRing E)ˣ) : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)) = 1 at h1
    rw [h2, zero_mul] at h1
    exact zero_ne_one h1
  have hΨ : Continuous Ψ := Units.continuous_val.comp (hχc.comp (Continuous.units_map ι0 hι0))
  have hΘ : Continuous Θ := by
    refine continuous_finsetProd _ fun j _ => ?_
    have hcont : Continuous fun u : (InfiniteAdeleRing E)ˣ =>
        c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j))) :=
      (hc j).comp ((continuous_apply (InfinitePlace.mk (φ j))).comp Units.continuous_val)
    have hn0 : ∀ u : (InfiniteAdeleRing E)ˣ,
        (((‖c j ((u : InfiniteAdeleRing E) (InfinitePlace.mk (φ j)))‖ : ℝ) : ℂ)) ≠ 0 :=
      fun u => Complex.ofReal_ne_zero.2 (norm_ne_zero_iff.2 (hne j u))
    exact (hcont.div (Complex.continuous_ofReal.comp (continuous_norm.comp hcont)) hn0).zpow₀ (n j)
      fun u => Or.inl (div_ne_zero (hne j u) (hn0 u))
  have hkey : Ψ = Θ := by
    refine Continuous.ext_on (denseRange_units_map_infiniteAdeleRing E) hΨ hΘ ?_
    rintro _ ⟨k, rfl⟩
    have hdiag : Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k) =
        Formalism.L2.Host.infDiag k := by
      apply Units.ext
      simp only [Formalism.L2.Host.infDiag, MonoidHom.coe_finsetProd, Finset.prod_apply, MonoidHom.coe_comp,
        Function.comp_apply, Units.coe_prod, Units.coe_map]
      have hprod : (∏ w, (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w
          (algebraMap E w.Completion (k : E)) : InfiniteAdeleRing E)) = algebraMap E (InfiniteAdeleRing E) (k : E) :=
        Finset.univ_prod_mulSingle (fun w : InfinitePlace E => algebraMap E w.Completion (k : E))
      rw [Finset.prod_congr rfl fun w _ => (show ((infIdele E w (Formalism.L2.Host.atInf w k) : Neutral.B1.Ideles E) :
          NumberField.AdeleRing (NumberField.RingOfIntegers E) E) =
          ι0 (Pi.mulSingle (M := fun w : InfinitePlace E => w.Completion) w (algebraMap E w.Completion (k : E))) from rfl),
]
      exact (congrArg ι0 hprod.symm).trans (map_prod ι0 _ _)
    have hinf := hn k
    simp only [Formalism.L2.Host.HChar.inf, MonoidHom.coe_comp, Function.comp_apply] at hinf
    show ((χ.1 (Units.map ι0 (Units.map (algebraMap E (InfiniteAdeleRing E)).toMonoidHom k)) : ℂˣ) : ℂ) = _
    rw [hdiag]
    refine hinf.trans (Finset.prod_congr rfl fun j _ => ?_)
    show _ = (c j (algebraMap E _ (k : E)) / ((‖c j (algebraMap E _ (k : E))‖ : ℝ) : ℂ)) ^ n j
    rw [hc' j]
  have hz := congrFun hkey
    (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z)
  have hι : Units.map ι0
      (Units.map (MonoidHom.mulSingle (fun w : InfinitePlace E => w.Completion) (InfinitePlace.mk (φ i))) z) =
      infIdele E _ z := by
    apply Units.ext
    rfl
  simp only [Ψ, Θ] at hz
  rw [hι] at hz
  rw [hz, Finset.prod_eq_single i]
  · simp [c]
  · intro j _ hj
    have hw : InfinitePlace.mk (φ j) ≠ InfinitePlace.mk (φ i) := fun h => hj (hb.1 h)
    simp only [Units.coe_map, MonoidHom.coe_mulSingle, MonoidHom.mulSingle_apply]
    rw [Pi.mulSingle_eq_of_ne hw]
    simp
  · intro h
    exact absurd (Finset.mem_univ i) h

theorem ideleModule_infIdele {E : Type} [Field E] [NumberField E] (w : InfinitePlace E)
    (z : (w.Completion)ˣ) :
    (ideleModule E (infIdele E w z) : ℝ) = ‖(z : w.Completion)‖ ^ w.mult := by
  classical
  show (IdeleGroup.infiniteModule (infIdele E w z) * IdeleGroup.finiteModule (infIdele E w z) : ℝ) = _
  have hinf : IdeleGroup.infiniteModule (infIdele E w z : IdeleGroup E) = ‖(z : w.Completion)‖ ^ w.mult := by
    unfold IdeleGroup.infiniteModule
    rw [Fintype.prod_eq_single w]
    · show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w‖ ^ w.mult = _
      rw [Pi.mulSingle_eq_same]
    · intro w' hw'
      show ‖(Pi.mulSingle w (z : w.Completion) : ∀ w', w'.Completion) w'‖ ^ w'.mult = 1
      rw [Pi.mulSingle_eq_of_ne hw', norm_one, one_pow]
  have hfin : IdeleGroup.finiteModule (infIdele E w z : IdeleGroup E) = 1 := by
    unfold IdeleGroup.finiteModule
    refine finprod_eq_one_of_forall_eq_one fun v => ?_
    show ‖(1 : IsDedekindDomain.FiniteAdeleRing (NumberField.RingOfIntegers E) E) v‖ = 1
    simp
  rw [hinf, hfin, mul_one]

theorem not_modulePow : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (I : Type) [Fintype I] (φ : I → E →+* ℂ), IsCMType φ → ∀ (χ : HChar E) (hu : IsUnitary χ) (n : I → ℤ), Formalism.L2.Host.HChar.HasInf χ φ n → (∃ i, n i ≠ 0) → ¬ ∃ τ : ℝ, ∀ x : IdeleGroup E, ((toHecke χ hu).toIdele x : ℂ) = ((ideleModule E x : ℝ) : ℂ) ^ ((τ : ℂ) * Complex.I) := by
  intro E _ _ _ I _ φ hcm χ hu n hn hex hτex
  obtain ⟨i, hi⟩ := hex
  obtain ⟨τ, hτ⟩ := hτex
  have hb := GlobalTheory.CMTypeCard.bijective_mk_of_isCMType hcm
  have hw : (InfinitePlace.mk (φ i)).IsComplex := IsTotallyComplex.isComplex _
  obtain ⟨e, hec, he, hes, hen⟩ := exists_ext_surj (φ i) hw
  obtain ⟨ζ, hζ1, hζm⟩ := exists_norm_one_zpow_ne (n i) hi
  obtain ⟨y, rfl⟩ := hes ζ
  have hy0 : y ≠ 0 := by
    rintro rfl
    simp at hζ1
  have hy1 : ‖y‖ = 1 := by rw [← hen]; exact hζ1
  have h3 := comp_eq hb χ hn i e hec he (Units.mk0 y hy0)
  have h4 := ideleModule_infIdele (InfinitePlace.mk (φ i)) (Units.mk0 y hy0)
  have h5 := hτ (infIdele E _ (Units.mk0 y hy0))
  rw [GlobalTheory.CompanionTheory.HeckeBridge.coe_toIdele] at h5
  apply hζm
  simp only [Units.val_mk0] at h3 h4
  rw [hζ1, Complex.ofReal_one, div_one] at h3
  rw [← h3]
  refine h5.trans ?_
  rw [h4, hy1, one_pow, Complex.ofReal_one, Complex.one_cpow]

end GlobalTheory.CompanionTheory.HeckeBridge.NotPow
