import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrdQ
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsFinsetEqSumIndicatorOfPeriodic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerMemSchwartzBruhatFinitePlace
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv

namespace GlobalTheory.SBHaarDelta

open scoped Topology

theorem indicator_mem {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) {φ : X → ℂ} (hφ : φ ∈ SB X) :
    U.indicator φ ∈ SB X := by
  have : U.indicator φ = U.indicator 1 * φ := by
    funext x; by_cases hx : x ∈ U <;> simp [hx]
  rw [this]
  exact ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant.mul hφ.1, hφ.2.mul_left⟩

theorem indicator_one_mem {X : Type} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) (hK : IsCompact U) :
    U.indicator (fun _ => (1 : ℂ)) ∈ SB X :=
  ⟨(LocallyConstant.indicator (1 : LocallyConstant X ℂ) hU).isLocallyConstant,
    HasCompactSupport.intro' hK hU.1 fun _ hx => Set.indicator_of_notMem hx _⟩

theorem eq_zero_of_local {X : Type} [TopologicalSpace X] (Λ : (X → ℂ) → ℂ)
    (hadd : ∀ f ∈ SB X, ∀ g ∈ SB X, Λ (f + g) = Λ f + Λ g) {f : X → ℂ} (hf : f ∈ SB X)
    (h : ∀ x, f x ≠ 0 → ∃ N : Set X, IsClopen N ∧ x ∈ N ∧ ∀ g ∈ SB X, Function.support g ⊆ N → Λ g = 0) :
    Λ f = 0 := by
  have h0 : Λ 0 = 0 := by
    have := hadd 0 (zero_mem _) 0 (zero_mem _)
    simpa using this
  have hc : IsCompact (Function.support f) :=
    hf.2.of_isClosed_subset (hf.1.isClopen_fiber 0).2.isClosed_compl (subset_tsupport f)
  have key : ∃ N : Set X, IsClopen N ∧ Function.support f ⊆ N ∧ ∀ g ∈ SB X, Function.support g ⊆ N → Λ g = 0 := by
    refine hc.induction_on (p := fun s => ∃ N : Set X, IsClopen N ∧ s ⊆ N ∧
      ∀ g ∈ SB X, Function.support g ⊆ N → Λ g = 0) ?_ ?_ ?_ ?_
    · refine ⟨∅, isClopen_empty, le_rfl, fun g _ hg => ?_⟩
      rw [Function.support_eq_empty_iff.1 (Set.subset_empty_iff.1 hg), h0]
    · rintro s t hst ⟨N, h1, h2, h3⟩
      exact ⟨N, h1, hst.trans h2, h3⟩
    · rintro s t ⟨N, h1, h2, h3⟩ ⟨M, k1, k2, k3⟩
      refine ⟨N ∪ M, h1.union k1, Set.union_subset_union h2 k2, fun g hg hs => ?_⟩
      have e : g = N.indicator g + Nᶜ.indicator g := (Set.indicator_self_add_compl N g).symm
      rw [e, hadd _ (indicator_mem h1 hg) _ (indicator_mem h1.compl hg), h3 _ (indicator_mem h1 hg),
        k3 _ (indicator_mem h1.compl hg), add_zero]
      · rw [Set.support_indicator]
        exact fun x hx => (hs hx.2).resolve_left hx.1
      · exact Set.support_indicator_subset
    · intro x hx
      obtain ⟨N, h1, h2, h3⟩ := h x hx
      exact ⟨N, mem_nhdsWithin_of_mem_nhds (h1.2.mem_nhds h2), N, h1, le_rfl, h3⟩
  obtain ⟨N, -, h2, h3⟩ := key
  exact h3 f hf h2

section Group

variable {G : Type} [AddCommGroup G] [TopologicalSpace G]

theorem translate_mem [IsTopologicalAddGroup G] {f : G → ℂ} (hf : f ∈ SB G) (a : G) : (fun x => f (x + a)) ∈ SB G :=
  ⟨hf.1.comp_continuous (continuous_add_const a), hf.2.comp_homeomorph (Homeomorph.addRight a)⟩

theorem eventually_periodic [IsTopologicalAddGroup G] {f : G → ℂ} (hf : f ∈ SB G) :
    ∀ᶠ y in 𝓝 (0 : G), ∀ x, f (x + y) = f x := by
  have key : ∀ x ∈ tsupport f, ∀ᶠ z : G × G in 𝓝 ((0 : G), x), f (z.2 + z.1) = f z.2 ∧ f (z.2 - z.1) = f z.2 := by
    intro x _
    have e3 := (hf.1.comp_continuous (f := fun z : G × G => z.2 + z.1) (by fun_prop)).eventually_eq ((0 : G), x)
    have e4 := (hf.1.comp_continuous (f := fun z : G × G => z.2 - z.1) (by fun_prop)).eventually_eq ((0 : G), x)
    have e5 := (hf.1.comp_continuous (f := fun z : G × G => z.2) (by fun_prop)).eventually_eq ((0 : G), x)
    filter_upwards [e3, e4, e5] with z h3 h4 h5
    simp only [Function.comp_apply, add_zero, sub_zero] at h3 h4 h5
    exact ⟨h3.trans h5.symm, h4.trans h5.symm⟩
  have h := hf.2.eventually_forall_of_forall_eventually (x₀ := (0 : G))
    (P := fun (w : G) (y : G) => f (y + w) = f y ∧ f (y - w) = f y) key
  filter_upwards [h] with w hw x
  by_cases hx : x ∈ tsupport f
  · exact (hw x hx).1
  by_cases hx' : x + w ∈ tsupport f
  · have := (hw _ hx').2
    rw [add_sub_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hx', image_eq_zero_of_notMem_tsupport hx]

def IsInvForm (L : (G → ℂ) → ℂ) : Prop :=
  (∀ f ∈ SB G, ∀ g ∈ SB G, L (f + g) = L f + L g) ∧ (∀ z : ℂ, ∀ f ∈ SB G, L (z • f) = z * L f) ∧
    ∀ f ∈ SB G, ∀ a : G, L (fun x => f (x + a)) = L f

theorem IsInvForm.sum [IsTopologicalAddGroup G] {L : (G → ℂ) → ℂ} (hL : IsInvForm L) {e : G → ℂ} (he : e ∈ SB G)
    (c : G → ℂ) (s : Finset G) :
    (fun t => ∑ a ∈ s, c a * e (t - a)) ∈ SB G ∧ L (fun t => ∑ a ∈ s, c a * e (t - a)) = (∑ a ∈ s, c a) * L e := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := hL.1 0 (zero_mem _) 0 (zero_mem _)
    refine ⟨zero_mem _, ?_⟩
    simp only [Finset.sum_empty, zero_mul]
    exact (by simpa using this : L 0 = 0)
  | insert a s ha ih =>
    have e1 : (fun t => ∑ b ∈ insert a s, c b * e (t - b)) =
        c a • (fun t => e (t + -a)) + fun t => ∑ b ∈ s, c b * e (t - b) := by
      funext t; simp [Finset.sum_insert ha, sub_eq_add_neg]
    have h1 := translate_mem he (-a)
    rw [e1]
    refine ⟨add_mem (Submodule.smul_mem _ _ h1) ih.1, ?_⟩
    rw [hL.1 _ (Submodule.smul_mem _ _ h1) _ ih.1, hL.2.1 _ _ h1, hL.2.2 _ he, ih.2, Finset.sum_insert ha, add_mul]

theorem exists_compact_open [NonarchimedeanAddGroup G] [LocallyCompactSpace G] {U : Set G} (hU : U ∈ 𝓝 (0 : G)) :
    ∃ V : AddSubgroup G, IsClopen (V : Set G) ∧ IsCompact (V : Set G) ∧ (V : Set G) ⊆ U := by
  obtain ⟨K, hK, hKU, hKc⟩ := local_compact_nhds hU
  obtain ⟨V, hV⟩ := NonarchimedeanAddGroup.is_nonarchimedean K hK
  exact ⟨V, V.isClopen, hKc.of_isClosed_subset V.isClosed hV, hV.trans hKU⟩

theorem IsInvForm.mul_comm [NonarchimedeanAddGroup G] [LocallyCompactSpace G] {L I : (G → ℂ) → ℂ}
    (hL : IsInvForm L) (hI : IsInvForm I) {f g : G → ℂ} (hf : f ∈ SB G) (hg : g ∈ SB G) :
    L f * I g = L g * I f := by
  obtain ⟨V, hV, hVc, hVU⟩ := exists_compact_open ((eventually_periodic hf).and (eventually_periodic hg))
  obtain ⟨s, hs⟩ := GlobalTheory.RootEx.exists_finset_eq_sum_indicator_of_periodic hf.2 V hV.2 fun x y hy => (hVU hy).1 x
  obtain ⟨u, hu⟩ := GlobalTheory.RootEx.exists_finset_eq_sum_indicator_of_periodic hg.2 V hV.2 fun x y hy => (hVU hy).2 x
  have he := indicator_one_mem hV hVc
  have a1 := (hL.sum he f s).2
  have a2 := (hI.sum he f s).2
  have a3 := (hL.sum he g u).2
  have a4 := (hI.sum he g u).2
  rw [← funext hs] at a1 a2
  rw [← funext hu] at a3 a4
  rw [a1, a2, a3, a4]; ring

theorem IsInvForm.eq_integral [NonarchimedeanAddGroup G] [LocallyCompactSpace G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsAddHaarMeasure] {L : (G → ℂ) → ℂ} (hL : IsInvForm L) :
    ∃ κ : ℂ, ∀ f ∈ SB G, L f = κ * ∫ x, f x ∂μ := by
  have hint : ∀ f ∈ SB G, Integrable f μ := fun f hf => hf.1.continuous.integrable_of_hasCompactSupport hf.2
  have hI : IsInvForm (fun f : G → ℂ => ∫ x, f x ∂μ) :=
    ⟨fun f hf g hg => integral_add (hint f hf) (hint g hg), fun z f _ => integral_const_mul z f,
      fun f _ a => integral_add_right_eq_self f a⟩
  obtain ⟨V, hV, hVc, -⟩ := exists_compact_open (G := G) Filter.univ_mem
  have he := indicator_one_mem hV hVc
  have hne : (∫ x, (V : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ) ≠ 0 := by
    rw [integral_indicator_const _ hV.2.measurableSet]
    have h1 : μ V ≠ 0 := (hV.2.measure_pos μ ⟨0, V.zero_mem⟩).ne'
    have h2 : μ V ≠ ⊤ := hVc.measure_lt_top.ne
    simp [Measure.real, ENNReal.toReal_eq_zero_iff, h1, h2]
  refine ⟨L ((V : Set G).indicator fun _ => 1) / ∫ x, (V : Set G).indicator (fun _ => (1 : ℂ)) x ∂μ, fun f hf => ?_⟩
  have := hL.mul_comm hI hf he
  field_simp
  linear_combination this

theorem eq_integral_of_retract [NonarchimedeanAddGroup G] [LocallyCompactSpace G] [T2Space G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsAddHaarMeasure] {X : Type} [AddCommGroup X] [TopologicalSpace X]
    [NonarchimedeanAddGroup X] [LocallyCompactSpace X] [T2Space X] (ι : G → X) (π : X → G) (hι : Continuous ι)
    (hπ : Continuous π) (hιa : ∀ g h, ι (g + h) = ι g + ι h) (hπa : ∀ x y, π (x + y) = π x + π y)
    (hπι : ∀ g, π (ι g) = g) (Λ : (X → ℂ) → ℂ) (hadd : ∀ f ∈ SB X, ∀ g ∈ SB X, Λ (f + g) = Λ f + Λ g)
    (hsmul : ∀ z : ℂ, ∀ f ∈ SB X, Λ (z • f) = z * Λ f)
    (hinv : ∀ f ∈ SB X, ∀ g : G, Λ (fun x => f (x + ι g)) = Λ f)
    (hvan : ∀ f ∈ SB X, (∀ g, f (ι g) = 0) → Λ f = 0) :
    ∃ κ : ℂ, ∀ f ∈ SB X, (fun g => f (ι g)) ∈ SB G ∧ Λ f = κ * ∫ g, f (ι g) ∂μ := by
  obtain ⟨V, hV, hVc, -⟩ := exists_compact_open (G := X) Filter.univ_mem
  have he := indicator_one_mem hV hVc
  set e : X → ℂ := (V : Set X).indicator (fun _ => (1 : ℂ)) with hedef
  let E : (G → ℂ) → X → ℂ := fun h x => h (π x) * e (x - ι (π x))
  have hE : ∀ h ∈ SB G, E h ∈ SB X := by
    intro h hh
    refine ⟨(hh.1.comp_continuous hπ).mul (he.1.comp_continuous (continuous_id.sub (hι.comp hπ))), ?_⟩
    have hK : IsCompact ((fun p : G × X => ι p.1 + p.2) '' (tsupport h ×ˢ (V : Set X))) :=
      (hh.2.isCompact.prod hVc).image (by fun_prop)
    refine HasCompactSupport.intro hK fun x hx => ?_
    by_contra hne
    refine hx ⟨(π x, x - ι (π x)), ⟨subset_tsupport _ (left_ne_zero_of_mul hne), ?_⟩, by simp⟩
    exact Set.support_indicator_subset (right_ne_zero_of_mul hne)
  have hL : IsInvForm (fun h => Λ (E h)) := by
    refine ⟨fun f hf g hg => ?_, fun z f hf => ?_, fun f hf a => ?_⟩
    · beta_reduce
      rw [← hadd _ (hE f hf) _ (hE g hg)]
      congr 1; funext x; simp [E, add_mul]
    · beta_reduce
      rw [← hsmul z _ (hE f hf)]
      congr 1; funext x; simp [E, mul_assoc]
    · beta_reduce
      rw [← hinv _ (hE f hf) a]
      congr 1; funext x; simp [E, hπa, hιa, hπι]
  obtain ⟨κ, hκ⟩ := hL.eq_integral μ
  refine ⟨κ, fun f hf => ?_⟩
  have hce : Topology.IsClosedEmbedding ι := Function.LeftInverse.isClosedEmbedding (f := π) hπι hπ hι
  have hr : (fun g => f (ι g)) ∈ SB G := ⟨hf.1.comp_continuous hι, hf.2.comp_isClosedEmbedding hce⟩
  refine ⟨hr, ?_⟩
  rw [← hκ _ hr]
  have hd := sub_mem hf (hE _ hr)
  have h0 := hvan _ hd fun g => by simp [E, hπι, hedef]
  have := hadd _ hd _ (hE _ hr)
  rw [sub_add_cancel, h0, zero_add] at this
  exact this

end Group

theorem nonarch_pi {ι : Type} [Finite ι] (G : ι → Type) [∀ i, AddCommGroup (G i)] [∀ i, TopologicalSpace (G i)]
    [∀ i, NonarchimedeanAddGroup (G i)] : NonarchimedeanAddGroup (∀ i, G i) where
  is_nonarchimedean U hU := by
    rw [nhds_pi, Filter.mem_pi] at hU
    obtain ⟨I, -, t, ht, hs⟩ := hU
    choose K hK using fun i => NonarchimedeanAddGroup.is_nonarchimedean (G := G i) (t i) (ht i)
    exact ⟨⟨AddSubgroup.pi Set.univ fun i => (K i : AddSubgroup (G i)),
      isOpen_set_pi Set.finite_univ fun i _ => (K i).isOpen⟩, fun x hx => hs fun i _ => hK i (hx i trivial)⟩

section Coord

variable {R : Type} {a b : ℕ}

def coords (Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) R) : (Fin (a + (b + 2)) → R) × (Fin b → R) :=
  (fun j => Z ⟨b + 1, by omega⟩ j, fun i => Z ⟨i.1 + 1, by omega⟩ ⟨a + b + 1, by omega⟩)

theorem insS_apply [Zero R] (r : Fin (a + (b + 2)) → R) (c : Fin b → R) (i : Fin (b + 2)) (j : Fin (a + (b + 2))) :
    insS (0 : Matrix (Fin b) (Fin (a + b)) R) r c 0 i j =
      if i.1 = b + 1 then r j else if h : i.1 ≠ 0 ∧ i.1 ≠ b + 1 ∧ j.1 = a + b + 1 then
        c ⟨i.1 - 1, by have := i.2; omega⟩ else 0 := by
  unfold insS
  split_ifs <;> first | rfl | omega

theorem coords_insS [Zero R] (r : Fin (a + (b + 2)) → R) (c : Fin b → R) :
    coords (insS (0 : Matrix (Fin b) (Fin (a + b)) R) r c 0) = (r, c) := by
  refine Prod.ext (funext fun j => ?_) (funext fun i => ?_)
  · simp [coords, insS_apply]
  · have := i.2
    simp [coords, insS_apply, this.ne]

theorem insS_add [AddMonoid R] (r r' : Fin (a + (b + 2)) → R) (c c' : Fin b → R) :
    insS (0 : Matrix (Fin b) (Fin (a + b)) R) (r + r') (c + c') 0 =
      insS (0 : Matrix (Fin b) (Fin (a + b)) R) r c 0 + insS (0 : Matrix (Fin b) (Fin (a + b)) R) r' c' 0 := by
  ext i j
  simp only [Matrix.add_apply, insS_apply]
  split_ifs <;> simp

theorem continuous_insS [Zero R] [TopologicalSpace R] :
    Continuous fun p : (Fin (a + (b + 2)) → R) × (Fin b → R) => insS (0 : Matrix (Fin b) (Fin (a + b)) R) p.1 p.2 0 := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [insS_apply]
  split_ifs <;> fun_prop

theorem exists_entry [Zero R] (Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) R)
    (h : Z ≠ insS (0 : Matrix (Fin b) (Fin (a + b)) R) (coords Z).1 (coords Z).2 0) :
    ∃ i j, Z i j ≠ 0 ∧ ∀ r c, insS (0 : Matrix (Fin b) (Fin (a + b)) R) r c 0 i j = 0 := by
  by_contra hn
  push_neg at hn
  apply h
  ext i j
  rw [insS_apply]
  split_ifs with h1 h2
  · simp only [coords]; congr 1; exact Fin.ext h1
  · simp only [coords]; congr 1
    · exact Fin.ext (by simp only; omega)
    · exact Fin.ext h2.2.2
  · by_contra hz
    obtain ⟨r, c, hrc⟩ := hn i j hz
    rw [insS_apply, if_neg h1, dif_neg h2] at hrc
    exact hrc rfl

end Coord

theorem main : ∀ {F : Type} [Field F] [NumberField F] (v : Pl F) {a b : ℕ} (ψ : AddChar (Fv F v) ℂ), Continuous ψ → ψ ≠ 1 →
    ∀ (P : Matrix (Fin (b + 2)) (Fin (b + 2)) (Fv F v)) (Q : Matrix (Fin (a + (b + 2))) (Fin (a + (b + 2))) (Fv F v)),
    IsUnit P.det → IsUnit Q.det →
    ∀ Λ : (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v) → ℂ) → ℂ,
    (∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ g ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
      Λ (f + g) = Λ f + Λ g) →
    (∀ z : ℂ, ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), Λ (z • f) = z * Λ f) →
    (∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ (r : Fin (a + (b + 2)) → Fv F v) (c : Fin b → Fv F v),
      Λ (fun Z => f (Z + P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 * Q)) = Λ f) →
    (∀ U : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v),
      (∀ (r : Fin (a + (b + 2)) → Fv F v) (c : Fin b → Fv F v),
        ∑ i, ∑ j, U i j * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 i j = 0) →
      ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)), ∀ f₁ ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
        (∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v), f₁ (P * Z * Q) = ψ (∑ i, ∑ j, U i j * Z i j) * f (P * Z * Q)) → Λ f₁ = Λ f) →
    ∃ κ : ℂ, ∀ f ∈ SB (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)),
      Λ f = κ * ∫ r, ∫ c, f (P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) r c 0 * Q) ∂(haarVec v b) ∂(haarVec v (a + (b + 2))) := by
  intro F _ _ v a b ψ hψ hψ1 P Q hP hQ Λ hadd hsmul hinv hchar
  haveI := haarO_isAddHaar v
  haveI : LocallyCompactSpace (Fv F v) := (intPC v).locallyCompactSpace_of_addGroup
  haveI : SecondCountableTopology (Fv F v) := by
    have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
    have : TopologicalSpace.SeparableSpace (Fv F v) :=
      ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
        IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
    exact UniformSpace.secondCountable_of_separable (Fv F v)
  haveI : ∀ p : ℕ, NonarchimedeanAddGroup (Fin p → Fv F v) := fun p => nonarch_pi (fun _ : Fin p => Fv F v)
  haveI : NonarchimedeanAddGroup (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)) :=
    nonarch_pi (fun _ : Fin (b + 2) => Fin (a + (b + 2)) → Fv F v)
  haveI : LocallyCompactSpace (Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v)) :=
    inferInstanceAs (LocallyCompactSpace (Fin (b + 2) → Fin (a + (b + 2)) → Fv F v))
  haveI : ∀ p : ℕ, (haarVec v p).IsAddHaarMeasure := fun p => by unfold haarVec; infer_instance
  have hψl : IsLocallyConstant ψ := GlobalTheory.SchrSB.isLocallyConstant_addChar ψ hψ
  have hc1 : ∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v), P⁻¹ * (P * Z * Q) * Q⁻¹ = Z := fun Z => by
    rw [Matrix.mul_assoc P, Matrix.nonsing_inv_mul_cancel_left _ _ hP, Matrix.mul_nonsing_inv_cancel_right _ _ hQ]
  have hc2 : ∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v), P * (P⁻¹ * Z * Q⁻¹) * Q = Z := fun Z => by
    rw [Matrix.mul_assoc P⁻¹, Matrix.mul_nonsing_inv_cancel_left _ _ hP, Matrix.nonsing_inv_mul_cancel_right _ _ hQ]
  have hT : Continuous fun Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v) => P⁻¹ * Z * Q⁻¹ :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
  obtain ⟨κ, hκ⟩ := eq_integral_of_retract ((haarVec v (a + (b + 2))).prod (haarVec v b))
    (fun p => P * insS (0 : Matrix (Fin b) (Fin (a + b)) (Fv F v)) p.1 p.2 0 * Q) (fun Z => coords (P⁻¹ * Z * Q⁻¹))
    ((continuous_const.matrix_mul continuous_insS).matrix_mul continuous_const)
    ((show Continuous (coords (R := Fv F v) (a := a) (b := b)) by unfold coords; fun_prop).comp hT)
    (fun g h => by simp only [Prod.fst_add, Prod.snd_add, insS_add, Matrix.mul_add, Matrix.add_mul])
    (fun x y => by simp only [Matrix.mul_add, Matrix.add_mul]; rfl)
    (fun g => by simp only [hc1, coords_insS]) Λ hadd hsmul (fun f hf g => hinv f hf g.1 g.2) (by
      intro f hf hf0
      refine eq_zero_of_local Λ hadd hf fun x hx => ?_
      obtain ⟨i, j, hij, hz⟩ := exists_entry (P⁻¹ * x * Q⁻¹) fun h => hx (by
        have := hf0 (coords (P⁻¹ * x * Q⁻¹))
        rwa [← h, hc2] at this)
      obtain ⟨t, ht⟩ : ∃ t, ψ t ≠ 1 := by
        by_contra h
        push_neg at h
        exact hψ1 (AddChar.ext _ _ h)
      set s := t / (P⁻¹ * x * Q⁻¹) i j with hs
      have hsum : ∀ Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v),
          ∑ k, ∑ l, Matrix.single i j s k l * Z k l = s * Z i j := fun Z => by
        simp [Matrix.single_apply, ite_and, Finset.sum_ite_eq]
      have hχ : IsLocallyConstant fun Z : Matrix (Fin (b + 2)) (Fin (a + (b + 2))) (Fv F v) =>
          ψ (s * (P⁻¹ * Z * Q⁻¹) i j) := hψl.comp_continuous (continuous_const.mul (hT.matrix_elem i j))
      refine ⟨_, hχ.isClopen_fiber (ψ t), ?_, fun g hg hs => ?_⟩
      · simp only [Set.mem_setOf_eq, hs, div_mul_cancel₀ t hij]
      · have h1 := hchar (Matrix.single i j s) (fun r c => by rw [hsum, hz, mul_zero]) g hg (ψ t • g)
          (Submodule.smul_mem _ _ hg) fun Z => by
            by_cases hZ : g (P * Z * Q) = 0
            · simp [hZ]
            · have := hs hZ
              simp only [Set.mem_setOf_eq, hc1] at this
              rw [hsum, this]; rfl
        rw [hsmul _ _ hg] at h1
        have : (ψ t - 1) * Λ g = 0 := by rw [sub_mul, h1, one_mul, sub_self]
        exact (mul_eq_zero.1 this).resolve_left (sub_ne_zero.2 ht))
  refine ⟨κ, fun f hf => ?_⟩
  obtain ⟨h1, h2⟩ := hκ f hf
  rw [h2, integral_prod _ (h1.1.continuous.integrable_of_hasCompactSupport h1.2)]

end GlobalTheory.SBHaarDelta
