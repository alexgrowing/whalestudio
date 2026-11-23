import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedLem
import Formalism.LocalToGlobal.IndefiniteReal.PHeisFC

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField Formalism.IndefR.PHeisFC

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def PhiM (m n : ℕ) (x : Mx D m n) : Fin m → Fin n → Fin (nE D) → AF D.host.F :=
  fun i j => cE D.host.F D.host.E (x i j)

theorem PhiM_add (m n : ℕ) (x y : Mx D m n) (i j k) : PhiM m n (x + y) i j k = PhiM m n x i j k + PhiM m n y i j k := by
  simp [PhiM]

theorem PhiM_rat (m n : ℕ) (e : Matrix (Fin m) (Fin n) D.host.E) (i j k) :
    PhiM m n (e.map (incA D)) i j k =
      algebraMap D.host.F (AF D.host.F) ((Module.finBasis D.host.F D.host.E).repr (e i j) k) := by
  show cE D.host.F D.host.E (incA D (e i j)) k = _
  exact cE_tmul (e i j) k

theorem cont_PhiM (m n : ℕ) (i j k) : Continuous fun x : Mx D m n => PhiM m n x i j k :=
  (continuous_apply k).comp ((cE D.host.F D.host.E).continuous.comp (continuous_id.matrix_elem i j))

def FDM (D : D7) (m n : ℕ) : Set (Mx D m n) := {x | ∀ i j k, PhiM m n x i j k ∈ F0 D.host.F}

theorem exUM (m n : ℕ) (x : Mx D m n) : ∃! g : ratMx D m n, g +ᵥ x ∈ FDM D m n := by
  classical
  choose q hq using fun i j k => (ad_exU D.host.F (PhiM m n x i j k)).exists
  let b := Module.finBasis D.host.F D.host.E
  let e : Matrix (Fin m) (Fin n) D.host.E := fun i j => b.equivFun.symm (q i j)
  have hr : ∀ v k, b.repr (b.equivFun.symm v) k = v k := fun v k => by
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  refine ⟨⟨_, ⟨e, rfl⟩⟩, ?_, ?_⟩
  · intro i j k
    show PhiM m n (e.map (incA D) + x) i j k ∈ F0 D.host.F
    rw [PhiM_add, PhiM_rat, show e i j = b.equivFun.symm (q i j) from rfl, hr]
    exact hq i j k
  · rintro ⟨g, e', rfl⟩ hg
    apply Subtype.ext
    show e'.map (incA D) = e.map (incA D)
    congr 1
    funext i j
    refine b.ext_elem fun k => ?_
    have h1 : algebraMap D.host.F (AF D.host.F) (b.repr (e' i j) k) + PhiM m n x i j k ∈ F0 D.host.F := by
      have := hg i j k
      have e2 : PhiM m n (e'.map (incA D) + x) i j k =
          algebraMap D.host.F (AF D.host.F) (b.repr (e' i j) k) + PhiM m n x i j k := by
        rw [PhiM_add, PhiM_rat]
      rw [← e2]; exact this
    have h2 := (ad_exU D.host.F (PhiM m n x i j k)).unique h1 (hq i j k)
    rw [h2, show e i j = b.equivFun.symm (q i j) from rfl, hr]

open scoped Classical in
theorem meas_FDM (m n : ℕ) : MeasurableSet (FDM D m n) := by
  have h : FDM D m n = ⋂ i, ⋂ j, ⋂ k,
      ((fun x => eM D.host.F (PhiM m n x i j k).1) ⁻¹' ZSpan.fundamentalDomain (mixedEmbedding.latticeBasis D.host.F) ∩
        (fun x => (PhiM m n x i j k).2) ⁻¹' Ohat D.host.F) := by
    ext x; simp [FDM, F0, Pinf]
  rw [h]
  refine MeasurableSet.iInter fun i => MeasurableSet.iInter fun j => MeasurableSet.iInter fun k => ?_
  refine MeasurableSet.inter ?_ ?_
  · exact ((continuous_eM _).comp (continuous_fst.comp (cont_PhiM m n i j k))).measurable (measurableSet_Pinf _)
  · exact ((isOpen_Ohat _).preimage (continuous_snd.comp (cont_PhiM m n i j k))).measurableSet

theorem FDM_sub_compact (m n : ℕ) : ∃ K : Set (Mx D m n), IsCompact K ∧ FDM D m n ⊆ K := by
  obtain ⟨K0, hK0, hsub⟩ := fundamental_set_subset_compact D.host.F
  let Ps : (Fin m → Fin n → Fin (nE D) → AF D.host.F) → Mx D m n :=
    fun y => Matrix.of fun i j => (cE D.host.F D.host.E).symm (y i j)
  have hc : Continuous Ps := continuous_matrix fun i j =>
    (cE D.host.F D.host.E).symm.continuous.comp ((continuous_apply j).comp (continuous_apply i))
  refine ⟨Ps '' Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => K0),
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hK0).image hc,
    fun x hx => ⟨PhiM m n x, fun i _ j _ k _ => hsub (hx i j k), ?_⟩⟩
  ext i j
  simp [Ps, PhiM]

instance lcMx (m n : ℕ) : LocallyCompactSpace (Mx D m n) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin n → AE D))

theorem isAddFD_FDM (m n : ℕ) (μ : Measure (Mx D m n)) : IsAddFundamentalDomain (ratMx D m n) (FDM D m n) μ :=
  IsAddFundamentalDomain.mk' (meas_FDM m n).nullMeasurableSet (exUM m n)

theorem covolM (m n : ℕ) (μ : Measure (Mx D m n)) [hμ : μ.IsAddHaarMeasure] (𝓕 : Set (Mx D m n))
    (h𝓕 : IsAddFundamentalDomain (ratMx D m n) 𝓕 μ) : μ 𝓕 < ⊤ ∧ μ 𝓕 ≠ 0 := by
  have := countable_ratMx (D := D) m n
  have : MeasurableConstVAdd (ratMx D m n) (Mx D m n) :=
    ⟨fun c => (continuous_const.add continuous_id).measurable⟩
  have : VAddInvariantMeasure (ratMx D m n) (Mx D m n) μ :=
    ⟨fun c s _ => measure_preimage_add μ (c : Mx D m n) s⟩
  obtain ⟨K, hK, hsub⟩ := FDM_sub_compact (D := D) m n
  refine ⟨?_, h𝓕.measure_ne_zero (NeZero.ne μ)⟩
  rw [h𝓕.measure_eq (isAddFD_FDM m n μ)]
  exact lt_of_le_of_lt (measure_mono hsub) hK.measure_lt_top

end Formalism.IndefR.Eqv

end
