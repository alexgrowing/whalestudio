import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodicEqZeroOfFourierCoefficientsZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageTranslateInvariantStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.QuotientAverageAddOfPeriodicStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped InnerProductSpace

namespace PositivityTheory.AdelicQuotientData

namespace tableDegreeThreeBase

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem ratV_eq : ratV E ι = vecLattice E ι := rfl

instance haar : (vecMeasure E ι).IsAddHaarMeasure := inferInstance

theorem borel_ok : BorelSpace (ι → Ad E) := inferInstance

theorem avg_eq_integral (f : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f) :
    avg (ratV E ι) f = ∫ x in vecDomain E ι, f x ∂vecMeasure E ι := by
  have h := GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι) (vecMeasure E ι) (vecDomain E ι) inferInstance
    isAddFundamentalDomain_vecDomain f hf
  rw [h.2.2.2, vecMeasure_vecDomain]
  simp

theorem integrableOn (f : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f) :
    IntegrableOn f (vecDomain E ι) (vecMeasure E ι) :=
  (GlobalTheory.T.setIntegral_fundamentalDomain_eq_mass_mul_average (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι) (vecMeasure E ι) (vecDomain E ι) inferInstance
    isAddFundamentalDomain_vecDomain f hf).2.2.1

theorem exists_ne_one {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) : ∃ a, ψ a ≠ 1 := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  have hne : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨y, hy⟩ := hψ.loc ⟨M, hM.isPrime, hne⟩
  exact ⟨_, hy⟩

theorem per_char {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (ζ : ι → E) :
    Per (ratV E ι) (fun x => ψ (dot ζ x)) := by
  refine ⟨hψ.cont.comp (continuous_dot ζ), ?_⟩
  rintro _ ⟨c, rfl⟩ x
  exact hψ.map_dot ζ c x

theorem dot_single' [DecidableEq ι] (ζ : ι → E) (t : ι) (a : Ad E) :
    dot ζ (Pi.single t a) = algebraMap E (Ad E) (ζ t) * a := by
  rw [dot, Finset.sum_eq_single t]
  · simp
  · intro s _ hs
    simp [Pi.single_eq_of_ne hs]
  · simp

open Classical in
theorem avg_char {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (ζ : ι → E) :
    avg (ratV E ι) (fun x => ψ (dot ζ x)) = if ζ = 0 then 1 else 0 := by
  classical
  split_ifs with h
  · subst h
    rw [avg_eq_integral _ (per_char hψ 0)]
    simp only [dot_zero_left, AddChar.map_zero_eq_one]
    rw [setIntegral_const]
    simp [Measure.real, vecMeasure_vecDomain]
  · obtain ⟨t, ht⟩ : ∃ t, ζ t ≠ 0 := by
      by_contra hc
      push_neg at hc
      exact h (funext hc)
    obtain ⟨a, ha⟩ := exists_ne_one hψ
    set y : ι → Ad E := Pi.single t (algebraMap E (Ad E) (ζ t)⁻¹ * a)
    have hy : dot ζ y = a := by
      rw [dot_single', ← mul_assoc, ← map_mul, mul_inv_cancel₀ ht, map_one, one_mul]
    have h1 := GlobalTheory.T.quotientAverage_translate_invariant (ι → Ad E) (ratV E ι) (isCoLat_ratV E ι) _ (per_char hψ ζ) y
    have h2 : (fun x => ψ (dot ζ (x + y))) = fun x => ψ a * ψ (dot ζ x) := by
      funext x
      rw [dot_add_right, hy, AddChar.map_add_eq_mul, mul_comm]
    rw [h2, avg_const_mul] at h1
    have h3 : (ψ a - 1) * avg (ratV E ι) (fun x => ψ (dot ζ x)) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)

variable (E ι) in

abbrev Q : Type := (ι → Ad E) ⧸ ratV E ι

theorem isClosed_ratV : IsClosed (ratV E ι : Set (ι → Ad E)) := by
  haveI := (isCoLat_ratV E ι).1
  exact AddSubgroup.isClosed_of_discrete

instance quotient_t3_space : T3Space (Q E ι) := by
  haveI : IsClosed (ratV E ι : Set (ι → Ad E)) := isClosed_ratV
  infer_instance

instance instCpt : CompactSpace (Q E ι) := by
  obtain ⟨_, K, hK, hcov⟩ := isCoLat_ratV E ι
  have hπ : Continuous (QuotientAddGroup.mk : (ι → Ad E) → Q E ι) := QuotientAddGroup.continuous_mk
  refine ⟨(hK.image hπ).of_isClosed_subset isClosed_univ fun q _ => ?_⟩
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  obtain ⟨γ, hγ, hk⟩ := hcov x
  refine ⟨γ + x, hk, QuotientAddGroup.eq.2 ?_⟩
  simpa using hγ

instance instSC : SecondCountableTopology (Q E ι) := inferInstance

instance instMet : TopologicalSpace.MetrizableSpace (Q E ι) :=
  TopologicalSpace.metrizableSpace_of_t3_secondCountable _

instance instMS : MeasurableSpace (Q E ι) := borel _

instance instBS : BorelSpace (Q E ι) := ⟨rfl⟩

variable (E ι) in

def nu : Measure (Q E ι) :=
  Measure.map (QuotientAddGroup.mk : (ι → Ad E) → Q E ι) ((vecMeasure E ι).restrict (vecDomain E ι))

theorem measurable_mk : Measurable (QuotientAddGroup.mk : (ι → Ad E) → Q E ι) :=
  QuotientAddGroup.continuous_mk.measurable

instance instFin : IsFiniteMeasure (nu E ι) := by
  haveI : IsFiniteMeasure ((vecMeasure E ι).restrict (vecDomain E ι)) :=
    ⟨by rw [Measure.restrict_apply_univ, vecMeasure_vecDomain]; exact ENNReal.one_lt_top⟩
  unfold nu
  infer_instance

theorem integral_nu (F : Q E ι → ℂ) (hF : Continuous F) :
    ∫ q, F q ∂nu E ι = ∫ x in vecDomain E ι, F (x : Q E ι) ∂vecMeasure E ι :=
  integral_map measurable_mk.aemeasurable hF.aestronglyMeasurable

def lift (f : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f) : C(Q E ι, ℂ) :=
  ⟨Quotient.lift f (fun x y hxy => by
      have h : -x + y ∈ ratV E ι := QuotientAddGroup.leftRel_apply.1 hxy
      rw [← hf.2 _ h x]
      congr 1
      abel), hf.1.quotient_lift _⟩

@[simp] theorem lift_mk (f : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f) (x : ι → Ad E) :
    lift f hf (x : Q E ι) = f x := rfl

theorem per_mul {f g : (ι → Ad E) → ℂ} (hf : Per (ratV E ι) f) (hg : Per (ratV E ι) g) :
    Per (ratV E ι) (fun x => f x * g x) :=
  ⟨hf.1.mul hg.1, fun γ hγ x => by simp only; rw [hf.2 γ hγ x, hg.2 γ hγ x]⟩

theorem per_conj {f : (ι → Ad E) → ℂ} (hf : Per (ratV E ι) f) :
    Per (ratV E ι) (fun x => conj (f x)) :=
  ⟨Complex.continuous_conj.comp hf.1, fun γ hγ x => by simp only; rw [hf.2 γ hγ x]⟩

theorem inner_lift {f g : (ι → Ad E) → ℂ} (hf : Per (ratV E ι) f) (hg : Per (ratV E ι) g) :
    ⟪ContinuousMap.toLp 2 (nu E ι) ℂ (lift g hg), ContinuousMap.toLp 2 (nu E ι) ℂ (lift f hf)⟫_ℂ =
      avg (ratV E ι) (fun x => f x * conj (g x)) := by
  rw [ContinuousMap.inner_toLp]
  rw [integral_nu (fun q => lift f hf q * conj (lift g hg q))
      ((lift f hf).continuous.mul (Complex.continuous_conj.comp (lift g hg).continuous)),
    avg_eq_integral _ (per_mul hf (per_conj hg))]
  rfl

theorem conj_psi {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (a : Ad E) : conj (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv, Complex.inv_def, Complex.normSq_eq_norm_sq, hψ.norm, one_pow, inv_one, Complex.ofReal_one, mul_one]

theorem dot_neg (ξ : ι → E) (x : ι → Ad E) : dot (-ξ) x = -dot ξ x := by
  simp [dot, Finset.sum_neg_distrib]

theorem char_mul {ψ : AddChar (Ad E) ℂ} (ξ η : ι → E) (x : ι → Ad E) :
    ψ (dot ξ x) * ψ (dot η x) = ψ (dot (ξ + η) x) := by
  rw [dot_add_left, AddChar.map_add_eq_mul]

variable (ψ : AddChar (Ad E) ℂ) (hψ : StdPsi ψ)

def ch (ξ : ι → E) : C(Q E ι, ℂ) := lift _ (per_char hψ ξ)

theorem ch_add (ξ η : ι → E) : ch ψ hψ (ξ + η) = ch ψ hψ ξ * ch ψ hψ η := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ch, lift_mk, ContinuousMap.mul_apply]
  rw [char_mul]

theorem ch_zero : ch ψ hψ (0 : ι → E) = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp [ch, dot_zero_left]

theorem ch_neg (ξ : ι → E) : ch ψ hψ (-ξ) = star (ch ψ hψ ξ) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective q
  simp only [ch, lift_mk, ContinuousMap.star_apply]
  rw [dot_neg, ← conj_psi hψ]
  rfl

theorem ch_sep {p q : Q E ι} (h : p ≠ q) : ∃ ξ, ch ψ hψ ξ p ≠ ch ψ hψ ξ q := by
  obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective p
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective q
  by_contra hc
  push Not at hc
  refine h (QuotientAddGroup.eq.2 ((hψ.forall_dot_eq_one_iff _).1 fun ξ => ?_))
  have h1 := hc ξ
  simp only [ch, lift_mk] at h1
  have e : -dot ξ (-x + y) = dot ξ x + -dot ξ y := by
    have h2 : dot ξ (-x) = -dot ξ x := by simp [dot, Finset.sum_neg_distrib]
    rw [dot_add_right, h2]
    ring
  rw [e, AddChar.map_add_eq_mul, h1, ← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]

theorem span_dense : (Submodule.span ℂ (Set.range (ch ψ hψ (ι := ι)))).topologicalClosure = ⊤ := by
  let V : Submodule ℂ C(Q E ι, ℂ) := Submodule.span ℂ (Set.range (ch ψ hψ (ι := ι)))
  have hV1 : (1 : C(Q E ι, ℂ)) ∈ V := Submodule.subset_span ⟨0, ch_zero ψ hψ⟩
  have hVmul : ∀ p ∈ V, ∀ q ∈ V, p * q ∈ V := by
    intro p hp q hq
    have : V * V ≤ V := by
      rw [Submodule.span_mul_span]
      refine Submodule.span_mono ?_
      rintro _ ⟨_, ⟨a, rfl⟩, _, ⟨b, rfl⟩, rfl⟩
      exact ⟨a + b, ch_add ψ hψ a b⟩
    exact this (Submodule.mul_mem_mul hp hq)
  have hVstar : ∀ p ∈ V, star p ∈ V := by
    intro p hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      exact Submodule.subset_span ⟨-a, ch_neg ψ hψ a⟩
    | zero => rw [star_zero]; exact V.zero_mem
    | add x y _ _ hx hy => rw [star_add]; exact V.add_mem hx hy
    | smul c x _ hx => rw [star_smul]; exact V.smul_mem _ hx
  let S : StarSubalgebra ℂ C(Q E ι, ℂ) :=
    { toSubalgebra := V.toSubalgebra hV1 (fun p q hp hq => hVmul p hp q hq)
      star_mem' := fun {p} hp => hVstar p hp }
  have hS : S.topologicalClosure = ⊤ := by
    refine ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ ?_
    intro x y hxy
    obtain ⟨a, ha⟩ := ch_sep ψ hψ hxy
    exact ⟨ch ψ hψ a, ⟨ch ψ hψ a, Submodule.subset_span ⟨a, rfl⟩, rfl⟩, ha⟩
  rw [eq_top_iff]
  intro f _
  have hf : f ∈ S.topologicalClosure := by rw [hS]; trivial
  exact hf

def chL (ξ : ι → E) : Lp ℂ 2 (nu E ι) := ContinuousMap.toLp 2 (nu E ι) ℂ (ch ψ hψ ξ)

theorem orth : Orthonormal ℂ (chL ψ hψ (ι := ι)) := by
  classical
  rw [orthonormal_iff_ite]
  intro ξ η
  simp only [chL, ch]
  rw [inner_lift]
  have e : (fun x => ψ (dot η x) * conj (ψ (dot ξ x))) = fun x => ψ (dot (η + -ξ) x) := by
    funext x
    rw [conj_psi hψ, ← dot_neg, char_mul]
  rw [e, avg_char hψ]
  by_cases h : ξ = η
  · subst h
    simp
  · rw [if_neg h, if_neg]
    intro h'
    rw [← sub_eq_add_neg, sub_eq_zero] at h'
    exact h h'.symm

theorem dense : ⊤ ≤ (Submodule.span ℂ (Set.range (chL ψ hψ (ι := ι)))).topologicalClosure := by
  intro f _
  have hd := ContinuousMap.toLp_denseRange ℂ (nu E ι) ℂ (p := 2) ENNReal.ofNat_ne_top
  have hmaps : Set.MapsTo (ContinuousMap.toLp 2 (nu E ι) ℂ : C(Q E ι, ℂ) →L[ℂ] Lp ℂ 2 (nu E ι))
      (Submodule.span ℂ (Set.range (ch ψ hψ (ι := ι))))
      (Submodule.span ℂ (Set.range (chL ψ hψ (ι := ι)))) := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨ξ, rfl⟩ := hy
      exact Submodule.subset_span ⟨ξ, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ c hy
  have h1 : Set.range (ContinuousMap.toLp 2 (nu E ι) ℂ : C(Q E ι, ℂ) →L[ℂ] Lp ℂ 2 (nu E ι)) ⊆
      ((Submodule.span ℂ (Set.range (chL ψ hψ (ι := ι)))).topologicalClosure : Set (Lp ℂ 2 (nu E ι))) := by
    rintro _ ⟨g, rfl⟩
    have hg : g ∈ closure (Submodule.span ℂ (Set.range (ch ψ hψ (ι := ι))) : Set C(Q E ι, ℂ)) := by
      rw [← Submodule.topologicalClosure_coe, span_dense]
      trivial
    rw [Submodule.topologicalClosure_coe]
    exact map_mem_closure (ContinuousMap.toLp 2 (nu E ι) ℂ).continuous hg hmaps
  exact closure_minimal h1 (Submodule.isClosed_topologicalClosure _) (hd f)

def basis : HilbertBasis (ι → E) ℂ (Lp ℂ 2 (nu E ι)) := HilbertBasis.mk (orth ψ hψ) (dense ψ hψ)

theorem coe_basis : ⇑(basis ψ hψ (ι := ι)) = chL ψ hψ := HilbertBasis.coe_mk _ _

theorem inner_chL (u : (ι → Ad E) → ℂ) (hu : Per (ratV E ι) u) (ξ : ι → E) :
    ⟪chL ψ hψ ξ, ContinuousMap.toLp 2 (nu E ι) ℂ (lift u hu)⟫_ℂ = avg (ratV E ι) (fun x => ψ (-dot ξ x) * u x) := by
  rw [chL, ch, inner_lift]
  congr 1
  funext x
  rw [conj_psi hψ, mul_comm]

include hψ in
theorem parseval (f g : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f) (hg : Per (ratV E ι) g) :
    HasSum (fun ξ : ι → E => avg (ratV E ι) (fun x => ψ (-dot ξ x) * f x) *
      conj (avg (ratV E ι) fun x => ψ (-dot ξ x) * g x)) (avg (ratV E ι) fun x => f x * conj (g x)) := by
  have h := (basis ψ hψ).hasSum_inner_mul_inner (ContinuousMap.toLp 2 (nu E ι) ℂ (lift g hg))
    (ContinuousMap.toLp 2 (nu E ι) ℂ (lift f hf))
  rw [inner_lift] at h
  have key : ∀ ξ, ⟪ContinuousMap.toLp 2 (nu E ι) ℂ (lift g hg), basis ψ hψ ξ⟫_ℂ *
      ⟪basis ψ hψ ξ, ContinuousMap.toLp 2 (nu E ι) ℂ (lift f hf)⟫_ℂ =
      avg (ratV E ι) (fun x => ψ (-dot ξ x) * f x) * conj (avg (ratV E ι) fun x => ψ (-dot ξ x) * g x) := by
    intro ξ
    have e1 : ⟪ContinuousMap.toLp 2 (nu E ι) ℂ (lift g hg), basis ψ hψ ξ⟫_ℂ =
        conj (avg (ratV E ι) fun x => ψ (-dot ξ x) * g x) := by
      rw [← inner_conj_symm, coe_basis, inner_chL]
    have e2 : ⟪basis ψ hψ ξ, ContinuousMap.toLp 2 (nu E ι) ℂ (lift f hf)⟫_ℂ =
        avg (ratV E ι) fun x => ψ (-dot ξ x) * f x := by
      rw [coe_basis, inner_chL]
    rw [e1, e2, mul_comm]
  simp only [key] at h
  exact h

end tableDegreeThreeBase

namespace tableDegreeThreeBase

variable {E : Type} [Field E] [NumberField E] {ι : Type} [Fintype ι]

theorem per_cmul {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (c : ℂ) (ζ : ι → E) :
    Per (ratV E ι) (fun x => c * ψ (dot ζ x)) :=
  ⟨continuous_const.mul (per_char hψ ζ).1, fun γ hγ x => by
    have h := (per_char hψ ζ).2 γ hγ x
    simp only at h ⊢
    rw [h]⟩

theorem twist_char {ψ : AddChar (Ad E) ℂ} (ξ η : ι → E) (x : ι → Ad E) :
    ψ (-dot ξ x) * ψ (dot η x) = ψ (dot (η - ξ) x) := by
  rw [sub_eq_add_neg, dot_add_left, dot_neg, AddChar.map_add_eq_mul, mul_comm]

theorem fin_case {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (f : (ι → Ad E) → ℂ) (hf : Per (ratV E ι) f)
    (hfin : {ξ : ι → E | avg (ratV E ι) (fun x => ψ (-dot ξ x) * f x) ≠ 0}.Finite) :
    HasSum (fun ξ : ι → E => avg (ratV E ι) fun x => ψ (-dot ξ x) * f x) (f 0) := by
  classical
  set c : (ι → E) → ℂ := fun ξ => avg (ratV E ι) fun x => ψ (-dot ξ x) * f x with hc
  set S := hfin.toFinset
  have hS : ∀ ξ, ξ ∉ S → c ξ = 0 := fun ξ h => by simpa [S, c] using h
  set h : (ι → Ad E) → ℂ := fun x => f x - ∑ η ∈ S, c η * ψ (dot η x) with hh_def
  have hh : Per (ratV E ι) h := by
    refine ⟨hf.1.sub (continuous_finsetSum _ fun η _ => (per_cmul hψ (c η) η).1), fun γ hγ x => ?_⟩
    simp only [h]
    rw [hf.2 γ hγ x]
    congr 1
    refine Finset.sum_congr rfl fun η _ => ?_
    exact (per_cmul hψ (c η) η).2 γ hγ x
  have hcoef : ∀ ξ, avg (ratV E ι) (fun x => ψ (-dot ξ x) * h x) = 0 := by
    intro ξ
    rw [avg_eq_integral _ (hψ.per_twist hh ξ)]
    have e : (fun x => ψ (-dot ξ x) * h x) =
        fun x => ψ (-dot ξ x) * f x - ∑ η ∈ S, c η * ψ (dot (η - ξ) x) := by
      funext x
      simp only [h, mul_sub, Finset.mul_sum]
      congr 1
      refine Finset.sum_congr rfl fun η _ => ?_
      rw [← twist_char]
      ring
    rw [e, integral_sub (integrableOn _ (hψ.per_twist hf ξ))
      (integrable_finsetSum _ fun η _ => integrableOn _ (per_cmul hψ (c η) (η - ξ))),
      integral_finsetSum _ fun η _ => integrableOn _ (per_cmul hψ (c η) (η - ξ))]
    rw [← avg_eq_integral _ (hψ.per_twist hf ξ)]
    have h3 : ∀ η ∈ S, ∫ x in vecDomain E ι, c η * ψ (dot (η - ξ) x) ∂vecMeasure E ι =
        if ξ = η then c η else 0 := by
      intro η _
      rw [integral_const_mul, ← avg_eq_integral _ (per_char hψ _), avg_char hψ]
      by_cases hξ : ξ = η
      · subst hξ
        simp
      · rw [if_neg, if_neg hξ, mul_zero]
        intro h'
        exact hξ (sub_eq_zero.1 h').symm
    rw [Finset.sum_congr rfl h3, Finset.sum_ite_eq]
    split_ifs with hm
    · exact sub_self _
    · rw [sub_zero]
      exact hS ξ hm
  have h0 := congrFun (eq_zero_of_avg_character_eq_zero E ι ψ hψ h hh hcoef) 0
  simp only [h, Pi.zero_apply] at h0
  have hd : ∀ η : ι → E, dot η (0 : ι → Ad E) = 0 := fun η => by simp [dot]
  simp only [hd, AddChar.map_zero_eq_one, mul_one] at h0
  rw [sub_eq_zero.1 h0]
  exact hasSum_sum_of_ne_finset_zero hS

end tableDegreeThreeBase

theorem poisson_base_holds : P0 := by
  intro E _ _ ψ hψ ι _
  exact ⟨fun f hf => tableDegreeThreeBase.avg_eq_integral f hf, fun f g hf hg => tableDegreeThreeBase.parseval ψ hψ f g hf hg,
    fun f hf hfin => tableDegreeThreeBase.fin_case hψ f hf hfin⟩

end PositivityTheory.AdelicQuotientData

end
