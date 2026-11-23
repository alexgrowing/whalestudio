import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonalBis
import Formalism.LocalToGlobal.ProjectiveLattices.FamilyUniformisationBasePointOrthogonal
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsOpenNsmulAdelicCompletionOfVectorSet
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite

noncomputable section

namespace GlobalTheory.IdeleParts

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj
open scoped TensorProduct Matrix Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem isOpen_nsmul_adelicCompletion_integers (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (N : ℕ) (hN : 0 < N) :
    letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
    IsOpen {z : GlobalTheory.AdLat.RA F E | ∃ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)), z = N • y} := by
  letI : TopologicalSpace (FiniteAdeleRing (𝓞 F) F ⊗[F] E) :=
      moduleTopology (FiniteAdeleRing (𝓞 F) F) (FiniteAdeleRing (𝓞 F) F ⊗[F] E)
  let L : Submodule (𝓞 E) (Fin 1 → E) :=
    (1 : Submodule (𝓞 E) E).comap (LinearMap.proj (R := 𝓞 E) (φ := fun _ : Fin 1 => E) 0)
  have hL : ∀ x : Fin 1 → E, x ∈ L ↔ x 0 ∈ Set.range (algebraMap (𝓞 E) E) := by
    intro x
    simp only [L, Submodule.mem_comap, Submodule.mem_one, LinearMap.proj_apply, Set.mem_range]
  have hspan : Submodule.span E (L : Set (Fin 1 → E)) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have h1 : (fun _ => (1 : E)) ∈ L := (hL _).2 ⟨1, map_one _⟩
    have : x = x 0 • (fun _ : Fin 1 => (1 : E)) := by
      funext i
      rw [Subsingleton.elim i 0]
      simp
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span h1)
  have ho := (GlobalTheory.AdLat.OpenLat.isOpen_nsmul_hat F E 1 L hspan).1 N hN
  have hc : Continuous (fun z : GlobalTheory.AdLat.RA F E => fun _ : Fin 1 => z) := continuous_pi fun _ => continuous_id
  have h1 : ∀ y ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)),
      y 0 ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, x 0, (hL x).1 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  have h2 : ∀ y ∈ GlobalTheory.AdLat.hat1 F (Set.range (algebraMap (𝓞 E) E)),
      (fun _ : Fin 1 => y) ∈ GlobalTheory.AdLat.hat F (L : Set (Fin 1 → E)) := by
    intro y hy
    induction hy using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨a, ha, x, hx, rfl⟩ := hz
      exact AddSubgroup.subset_closure ⟨a, ha, fun _ => x, (hL _).2 hx, rfl⟩
    | zero => exact zero_mem _
    | add u v _ _ hu hv => exact add_mem hu hv
    | neg u _ hu => exact neg_mem hu
  convert ho.preimage hc using 1
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨_, h2 y hy, rfl⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y 0, h1 y hy, congrFun h 0⟩

theorem integralFiniteAdeles_eq_adelicCompletion_integers (D : D7) :
    intAE D = GlobalTheory.AdLat.hat1 D.host.F (Set.range (algebraMap (𝓞 D.host.E) D.host.E)) := by
  unfold intAE GlobalTheory.AdLat.hat1
  congr 1
  ext z
  constructor
  · rintro ⟨a, ha, x, rfl⟩
    exact ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨a, ha, _, ⟨x, rfl⟩, rfl⟩
    exact ⟨a, ha, x, rfl⟩

theorem exists_units_parts {R A B : Type} [Ring R] [Ring A] [Ring B] [TopologicalSpace R] [TopologicalSpace A]
    [TopologicalSpace B] (e : R ≃+* A × B) (hec : Continuous e) (hes : Continuous e.symm)
    (f : R → A) (g : R → B) (he : ∀ z, (e z).1 = f z ∧ (e z).2 = g z) :
    ∃ a b : Rˣ →* Rˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧
      (∀ x, f (a x : R) = f (x : R) ∧ g (a x : R) = 1) ∧ ∀ x, f (b x : R) = 1 ∧ g (b x : R) = g (x : R) := by
  let a0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inl _ _).comp ((MonoidHom.fst _ _).comp e.toRingHom.toMonoidHom))
  let b0 : R →* R := e.symm.toRingHom.toMonoidHom.comp
    ((MonoidHom.inr _ _).comp ((MonoidHom.snd _ _).comp e.toRingHom.toMonoidHom))
  have ha0 : ∀ z, a0 z = e.symm ((e z).1, 1) := fun z => rfl
  have hb0 : ∀ z, b0 z = e.symm (1, (e z).2) := fun z => rfl
  have hac : Continuous a0 := by
    rw [show (a0 : R → R) = fun z => e.symm ((e z).1, 1) from funext ha0]
    exact hes.comp ((continuous_fst.comp hec).prodMk continuous_const)
  have hbc : Continuous b0 := by
    rw [show (b0 : R → R) = fun z => e.symm (1, (e z).2) from funext hb0]
    exact hes.comp (continuous_const.prodMk (continuous_snd.comp hec))
  refine ⟨Units.map a0, Units.map b0, Continuous.units_map a0 hac, Continuous.units_map b0 hbc,
    fun x => ?_, fun x => ?_, fun x => ?_⟩
  · apply Units.ext
    rw [Units.val_mul, Units.coe_map, Units.coe_map, ha0, hb0, ← map_mul, Prod.mk_mul_mk, mul_one, one_mul]
    exact (e.symm_apply_apply _).symm
  · rw [Units.coe_map, ha0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨(he _).1, rfl⟩
  · rw [Units.coe_map, hb0, ← (he _).1, ← (he _).2, e.apply_symm_apply]
    exact ⟨rfl, (he _).2⟩

theorem congr_open_and_parts : ∀ (D : D7), (∀ N : ℕ, 0 < N → IsOpen {x : (AE D)ˣ | finPart D (x : AE D) ∈ intAE D ∧ finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D ∧ ∃ y ∈ intAE D, finPart D (x : AE D) - 1 = N • y}) ∧ ∃ a b : (AE D)ˣ →* (AE D)ˣ, Continuous a ∧ Continuous b ∧ (∀ x, x = a x * b x) ∧ (∀ x, infPart D (a x : AE D) = infPart D (x : AE D) ∧ finPart D (a x : AE D) = 1) ∧ ∀ x, infPart D (b x : AE D) = 1 ∧ finPart D (b x : AE D) = finPart D (x : AE D) := by
  intro D
  letI tf : TopologicalSpace (Af D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E)
  letI ti : TopologicalSpace (Ainf D.host.F ⊗[D.host.F] D.host.E) :=
    moduleTopology (Ainf D.host.F) (Ainf D.host.F ⊗[D.host.F] D.host.E)
  obtain ⟨e, he, hec, hes⟩ : ∃ e : AE D ≃+* (Ainf D.host.F ⊗[D.host.F] D.host.E) × (Af D.host.F ⊗[D.host.F] D.host.E),
      (∀ z, (e z).1 = infPart D z ∧ (e z).2 = finPart D z) ∧ Continuous e ∧ Continuous e.symm :=
    GlobalTheory.AdSplit.exists_adele_equiv D.host.F D.host.E
  have hfc : Continuous (finPart D) := by
    have : (finPart D : AE D → _) = fun z => (e z).2 := funext fun z => (he z).2.symm
    rw [this]
    exact continuous_snd.comp hec
  refine ⟨fun N hN => ?_, ?_⟩
  · haveI : IsModuleTopology (Af D.host.F) (Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
    haveI : ContinuousAdd (Af D.host.F ⊗[D.host.F] D.host.E) :=
      IsModuleTopology.toContinuousAdd (Af D.host.F) _
    have hN' : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | ∃ y ∈ intAE D, z = N • y} := by
      rw [integralFiniteAdeles_eq_adelicCompletion_integers]
      exact isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E N hN
    have h1 : IsOpen {z : Af D.host.F ⊗[D.host.F] D.host.E | z ∈ intAE D} := by
      have := isOpen_nsmul_adelicCompletion_integers D.host.F D.host.E 1 one_pos
      rw [← integralFiniteAdeles_eq_adelicCompletion_integers] at this
      convert this using 1
      ext z
      simp
    have c1 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) := hfc.comp Units.continuous_val
    have c2 : Continuous fun x : (AE D)ˣ => finPart D ((x⁻¹ : (AE D)ˣ) : AE D) :=
      hfc.comp Units.continuous_coe_inv
    have c3 : Continuous fun x : (AE D)ˣ => finPart D (x : AE D) - 1 := by
      simp only [sub_eq_add_neg]
      exact c1.add continuous_const
    exact (h1.preimage c1).inter ((h1.preimage c2).inter (hN'.preimage c3))
  · exact exists_units_parts e hec hes (infPart D) (finPart D) he

end GlobalTheory.IdeleParts
