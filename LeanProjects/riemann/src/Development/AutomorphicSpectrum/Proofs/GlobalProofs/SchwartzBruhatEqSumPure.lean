import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CoefS
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.AdmCpt

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published.SiegelOneVector GlobalTheory.CompanionTheory.Hypotheses₂.OneV
open scoped TensorProduct ENNReal Topology

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

open PI.VolStabS.PositiveNearLattice PI.VolStabS.AdmissibleCompactSupport

section Group

variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem invariant_mem_nhds {f : V → ℂ} (h1 : IsLocallyConstant f) (h2 : HasCompactSupport f) :
    {u : V | ∀ x, f (x + u) = f x} ∈ 𝓝 (0 : V) := by
  have hg : IsLocallyConstant fun p : V × V => f (p.1 + p.2) - f p.1 :=
    (h1.comp_continuous (f := fun p : V × V => p.1 + p.2) (by fun_prop)).sub
      (h1.comp_continuous (f := fun p : V × V => p.1) (by fun_prop))
  have hn := hg.isOpen_fiber 0
  obtain ⟨u, v, _, hv, hCu, h0, huv⟩ := generalized_tube_lemma h2.isCompact
    (isCompact_singleton (x := (0 : V))) hn (by
      rintro ⟨c, x⟩ ⟨_, hx⟩
      have hx' : x = 0 := hx
      subst hx'
      simp)
  have hv0 : v ∈ 𝓝 (0 : V) := hv.mem_nhds (h0 rfl)
  have hv1 : (fun x : V => -x) ⁻¹' v ∈ 𝓝 (0 : V) := by
    have hc : ContinuousAt (fun x : V => -x) 0 := by fun_prop
    exact hc.preimage_mem_nhds (by simpa using hv0)
  refine Filter.mem_of_superset (Filter.inter_mem hv0 hv1) fun w hw x => ?_
  by_cases hx : x ∈ tsupport f
  · have := huv (Set.mk_mem_prod (hCu hx) hw.1)
    simpa [sub_eq_zero] using this
  · by_cases hx' : x + w ∈ tsupport f
    · have h : f (x + w + -w) - f (x + w) = 0 := huv (Set.mk_mem_prod (hCu hx') hw.2)
      rw [add_neg_cancel_right, sub_eq_zero] at h
      exact h.symm
    · rw [image_eq_zero_of_notMem_tsupport hx, image_eq_zero_of_notMem_tsupport hx']

theorem eq_sum_cosets {φ : V → ℂ} (hφ : HasCompactSupport φ) (L : AddSubgroup V) (hL : IsOpen (L : Set V))
    (hinv : ∀ x, ∀ l ∈ L, φ (x + l) = φ x) :
    ∃ s : Finset V, ∀ x, φ x = ∑ a ∈ s, φ a * Set.indicator {y | y - a ∈ L} (fun _ => (1 : ℂ)) x := by
  classical
  obtain ⟨t, ht⟩ := hφ.isCompact.elim_finite_subcover (fun a : V => {y | y - a ∈ L})
    (fun a => hL.preimage (continuous_id.sub continuous_const))
    (fun x _ => Set.mem_iUnion.2 ⟨x, by simp [L.zero_mem]⟩)
  let T : Finset (V ⧸ L) := t.image (QuotientAddGroup.mk : V → V ⧸ L)
  refine ⟨T.image Quotient.out, fun x => ?_⟩
  rw [Finset.sum_image (fun a _ b _ hab => Quotient.out_injective hab)]
  have key : ∀ q : V ⧸ L, x - q.out ∈ L ↔ q = (x : V ⧸ L) := by
    intro q
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
  have hval : φ ((x : V ⧸ L).out) = φ x := by
    have hm : x - ((x : V ⧸ L)).out ∈ L := (key _).2 rfl
    have := hinv ((x : V ⧸ L)).out _ hm
    rw [← this]
    congr 1
    abel
  have hterm : ∀ q : V ⧸ L, φ q.out * Set.indicator {y | y - q.out ∈ L} (fun _ => (1 : ℂ)) x
      = if q = (x : V ⧸ L) then φ x else 0 := by
    intro q
    by_cases hq : q = (x : V ⧸ L)
    · subst hq
      rw [if_pos rfl, Set.indicator_of_mem (show x ∈ {y | y - ((x : V ⧸ L)).out ∈ L} from (key _).2 rfl),
        hval, mul_one]
    · rw [if_neg hq, Set.indicator_of_notMem (show x ∉ {y | y - q.out ∈ L} from fun hx => hq ((key _).1 hx)),
        mul_zero]
  simp only [hterm, Finset.sum_ite_eq']
  split_ifs with hx
  · rfl
  · by_contra hne
    have hmem : x ∈ tsupport φ := subset_tsupport φ hne
    obtain ⟨a, ha, hxa⟩ := Set.mem_iUnion₂.1 (ht hmem)
    apply hx
    refine Finset.mem_image.2 ⟨a, ha, ?_⟩
    rw [QuotientAddGroup.eq, neg_add_eq_sub]
    exact hxa

end Group

theorem exists_nhds_of_pi {ι X : Type} [Finite ι] [TopologicalSpace X] {x : X} {U : Set (ι → X)}
    (hU : U ∈ 𝓝 (fun _ => x)) : ∃ W ∈ 𝓝 x, ∀ c : ι → X, (∀ i, c i ∈ W) → c ∈ U := by
  rw [nhds_pi, Filter.mem_pi] at hU
  obtain ⟨I, hI, t, ht, hsub⟩ := hU
  exact ⟨⋂ i ∈ I, t i, (Filter.biInter_mem hI).2 fun i _ => ht i, fun c hc =>
    hsub fun i hi => Set.mem_iInter₂.1 (hc i) i hi⟩

variable {F : Type} [Field F] [NumberField F]

def intSub (v : HeightOneSpectrum (𝓞 F)) : OpenAddSubgroup (Fv F v) :=
  ⟨(v.adicCompletionIntegers F).toSubring.toAddSubgroup, ReciprocityTheory.GeneralLinearIntegers.GeneralLinearIntegersOpenCompact.isOpen_integers v⟩

theorem mem_intSub (v : HeightOneSpectrum (𝓞 F)) (x : Fv F v) :
    x ∈ intSub v ↔ x ∈ v.adicCompletionIntegers F := Iff.rfl

theorem exists_box_subset {W : Set (Af F)} (hW : W ∈ 𝓝 (0 : Af F)) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 F))) (P : ∀ v : HeightOneSpectrum (𝓞 F), OpenAddSubgroup (Fv F v)),
      (∀ v, P v ≤ intSub v) ∧ (∀ v, v ∉ T → P v = intSub v) ∧ {y : Af F | ∀ v, y v ∈ P v} ⊆ W := by
  classical
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) => (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  have hc : Continuous (RestrictedProduct.structureMap R A Filter.cofinite) :=
    RestrictedProduct.isEmbedding_structureMap.continuous
  have hp : (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W ∈ 𝓝 (fun v => (0 : A v)) :=
    hc.continuousAt.preimage_mem_nhds hW
  rw [nhds_pi, Filter.mem_pi] at hp
  obtain ⟨I, hI, t, ht, hsub⟩ := hp
  have hQ : ∀ v : HeightOneSpectrum (𝓞 F), ∃ Q : OpenAddSubgroup (Fv F v), Q ≤ intSub v ∧
      ∀ x : A v, (x : Fv F v) ∈ Q → x ∈ t v := by
    intro v
    obtain ⟨u, hu, hut⟩ := mem_nhds_subtype _ _ _ |>.1 (ht v)
    have h0 : u ∩ (intSub v : Set (Fv F v)) ∈ 𝓝 (0 : Fv F v) :=
      Filter.inter_mem hu ((intSub v).isOpen.mem_nhds (intSub v).zero_mem)
    obtain ⟨Q, hQ⟩ := NonarchimedeanAddGroup.is_nonarchimedean _ h0
    exact ⟨Q, fun x hx => (hQ hx).2, fun x hx => hut (hQ hx).1⟩
  choose Q hQ1 hQ2 using hQ
  refine ⟨hI.toFinset, fun v => if v ∈ I then Q v else intSub v, ?_, ?_, ?_⟩
  · intro v
    by_cases hv : v ∈ I
    · simpa [hv] using hQ1 v
    · simp [hv]
  · intro v hv
    have : v ∉ I := by simpa using hv
    simp [this]
  · intro y hy
    have hint : ∀ v, y v ∈ A v := by
      intro v
      by_cases hv : v ∈ I
      · have := hy v
        simp only [hv, if_true] at this
        exact hQ1 v this
      · have := hy v
        simp only [hv, if_false] at this
        exact this
    have : (fun v => (⟨y v, hint v⟩ : A v)) ∈ (RestrictedProduct.structureMap R A Filter.cofinite) ⁻¹' W := by
      refine hsub fun v hv => hQ2 v _ ?_
      have := hy v
      simp only [hv, if_true] at this
      exact this
    exact this

variable {E : Type} [Field E] [Algebra F E] [FiniteDimensional F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_add {R : Type} [CommRing R] [Algebra F R] (x y : R ⊗[F] E) (k : Fin d) :
    crd b R (x + y) k = crd b R x k + crd b R y k := by
  simp [crd]

theorem crd_neg {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) (k : Fin d) :
    crd b R (-x) k = - crd b R x k := by
  simp [crd]

theorem crd_zero {R : Type} [CommRing R] [Algebra F R] (k : Fin d) :
    crd b R (0 : R ⊗[F] E) k = 0 := by
  simp [crd]

def lv (v : HeightOneSpectrum (𝓞 F)) (P : AddSubgroup (Fv F v)) (M : ℕ) :
    AddSubgroup (Fin 1 → Fin M → Fv F v ⊗[F] E) where
  carrier := {Z | ∀ a i k, crd b (Fv F v) (Z a i) k ∈ P}
  add_mem' hx hy a i k := by
    rw [Pi.add_apply, Pi.add_apply, crd_add]
    exact add_mem (hx a i k) (hy a i k)
  zero_mem' a i k := by
    rw [Pi.zero_apply, Pi.zero_apply, crd_zero]
    exact zero_mem P
  neg_mem' hx a i k := by
    rw [Pi.neg_apply, Pi.neg_apply, crd_neg]
    exact neg_mem (hx a i k)

def cosV (v : HeightOneSpectrum (𝓞 F)) (P : OpenAddSubgroup (Fv F v)) {M : ℕ}
    (a : Fin 1 → Fin M → Fv F v ⊗[F] E) : Set (Fin 1 → Fin M → Fv F v ⊗[F] E) :=
  {Z | Z - a ∈ lv b v (P : AddSubgroup (Fv F v)) M}

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef.Dec

namespace GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef

open Dec

end GlobalTheory.CompanionTheory.Hypotheses₂.OneV.Coef
