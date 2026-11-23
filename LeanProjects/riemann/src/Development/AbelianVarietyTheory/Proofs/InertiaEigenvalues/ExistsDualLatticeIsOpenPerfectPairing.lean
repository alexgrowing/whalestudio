import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSummandTw
open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass Formalism.MainNotions.PairedCharacterCondition GlobalTheory.Pass.LocDual

noncomputable section

namespace GlobalTheory.Pass.LocDual

set_option maxHeartbeats 1000000 in
set_option synthInstance.maxHeartbeats 400000 in

theorem exists_dualLat_isOpen : ∀ {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR] [TopologicalSpace Qp]
    (PD : PeriodData G Qp K₀ K B BdR) {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL], GoodO (Qp := Qp) LL O →
    (∀ g, ∃ u : Oˣ, ((cycLL PD LL g : LLˣ) : LL) = algebraMap O LL (u : O)) →
    ∀ (U U' : GRep G Qp LL O) (P : U.V →ₗ[LL] U'.V →ₗ[LL] LL), IsDual1 PD U.ρ U'.ρ P →
    ∀ LT : Lattice (O := O) U.ρ, ∃ LT' : Lattice (O := O) U'.ρ, IsDualLat1 PD LT LT' P ∧ IsOpen (LT'.T : Set U'.V) := by
  intro G _ _ Qp K₀ K _ _ _ _ _ _ _ B BdR _ _ _ _ _ _ _ _ _ _ _ _ PD LL O _ _ _ _ _ hO hcyc U U' P hP LT

  obtain ⟨⟨hdom, hdvr, hfr⟩, hfd, hmt, htr, hopen⟩ := hO
  haveI := hfr
  haveI : Module.Finite O LT.T := Module.Finite.iff_fg.mpr LT.fg
  haveI : Module.Free O LT.T := LT.free
  let b := Module.Free.chooseBasis O LT.T
  let e : Module.Free.ChooseBasisIndex O LT.T → U.V := fun i => (b i : U.V)
  have he_O : LinearIndependent O e := b.linearIndependent.map' LT.T.subtype (Submodule.ker_subtype _)
  have he_L : LinearIndependent LL e := (LinearIndependent.iff_fractionRing O LL).mp he_O
  have hspanO : Submodule.span O (Set.range e) = LT.T := by
    have h1 : Set.range e = LT.T.subtype '' Set.range b := (Set.range_comp _ _)
    rw [h1, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_subtype]
  have hspanL : Submodule.span LL (Set.range e) = ⊤ := by
    rw [← Submodule.span_span_of_tower O LL (Set.range e), hspanO]; exact LT.span
  let bL := Basis.mk he_L (le_of_eq hspanL.symm)
  have hbL : ∀ i, bL i = e i := fun i => Basis.mk_apply _ _ _
  let φ : U'.V →ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearMap.pi (fun i => P (e i))
  have hφ : ∀ y i, φ y i = P (e i) y := fun _ _ => rfl
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hP.2.2.1 y
    intro x
    have h1 : P.flip y = 0 := bL.ext (fun i => by
      rw [hbL]; simpa [hφ] using congrFun hy i)
    simpa using LinearMap.congr_fun h1 x
  have hdim : finrank LL U'.V = finrank LL (Module.Free.ChooseBasisIndex O LT.T → LL) := by
    rw [← hP.2.2.2, Module.finrank_fintype_fun_eq_card, Module.finrank_eq_card_basis bL]
  have hφsurj : Function.Surjective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mp hφinj
  let φe : U'.V ≃ₗ[LL] (Module.Free.ChooseBasisIndex O LT.T → LL) := LinearEquiv.ofBijective φ ⟨hφinj, hφsurj⟩
  let bf := (Pi.basisFun LL (Module.Free.ChooseBasisIndex O LT.T)).map φe.symm
  have hφf : ∀ i j, P (e j) (bf i) = (Pi.single i (1 : LL) : Module.Free.ChooseBasisIndex O LT.T → LL) j := fun i j => by
    have : φ (bf i) = Pi.single i 1 := by
      simp only [bf, Basis.map_apply, Pi.basisFun_apply]
      exact φe.apply_symm_apply _
    exact congrFun this j
  let T' : Submodule O U'.V :=
    { carrier := {y | ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a}
      add_mem' := by
        intro y z hy hz x hx
        obtain ⟨a, ha⟩ := hy x hx
        obtain ⟨c, hc⟩ := hz x hx
        exact ⟨a + c, by simp [ha, hc]⟩
      zero_mem' := fun x _ => ⟨0, by simp⟩
      smul_mem' := by
        intro c y hy x hx
        obtain ⟨a, ha⟩ := hy x hx
        refine ⟨c * a, ?_⟩
        show P x (c • y) = _
        rw [← algebraMap_smul LL c y, map_smul, ha, smul_eq_mul, map_mul] }
  have hmem : ∀ y, y ∈ T' ↔ ∀ x ∈ LT.T, ∃ a : O, P x y = algebraMap O LL a := fun y => Iff.rfl
  have hmem' : ∀ y, y ∈ T' ↔ ∀ i, P (e i) y ∈ Set.range (algebraMap O LL) := by
    intro y; constructor
    · intro hy i; obtain ⟨a, ha⟩ := hy (e i) (b i).2; exact ⟨a, ha.symm⟩
    · intro hy x hx
      choose a ha using hy
      have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • e i := by
        have h2 := congrArg Subtype.val (b.sum_repr ⟨x, hx⟩)
        rw [Submodule.coe_sum] at h2
        exact h2.symm
      obtain ⟨c, hcx⟩ : ∃ c : Module.Free.ChooseBasisIndex O LT.T → O, x = ∑ i, c i • e i := ⟨_, hx'⟩
      refine ⟨∑ i, c i * a i, ?_⟩
      rw [hcx, map_sum, LinearMap.sum_apply, map_sum (algebraMap O LL)]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [← algebraMap_smul LL (c i) (e i), map_smul, LinearMap.smul_apply, ← ha i,
        smul_eq_mul, map_mul]
  have hf_mem : ∀ i, bf i ∈ T' := fun i => (hmem' _).mpr fun j => by
    rw [hφf]
    refine ⟨(Pi.single i (1 : O) : Module.Free.ChooseBasisIndex O LT.T → O) j, ?_⟩
    rcases eq_or_ne j i with rfl | h
    · simp
    · simp [Pi.single_apply, h]
  have hT'eq : T' = Submodule.span O (Set.range bf) := by
    apply le_antisymm
    · intro y hy
      choose a ha using (hmem' y).mp hy
      have hy' : y = ∑ i, a i • bf i := by
        apply hφinj
        funext j
        rw [hφ, hφ, map_sum, ← ha j]
        simp_rw [← algebraMap_smul LL (a _) (bf _), map_smul, hφf, Pi.single_apply, smul_eq_mul,
          mul_ite, mul_one, mul_zero]
        simp
      rw [hy']
      exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact hf_mem i
  have hfO : LinearIndependent O bf := (LinearIndependent.iff_fractionRing O LL).mpr bf.linearIndependent
  have hstab : ∀ g, ∀ y ∈ T', U'.ρ g y ∈ T' := by
    intro g y hy x hx
    obtain ⟨u, hu⟩ := hcyc g
    obtain ⟨a, ha⟩ := hy (U.ρ g⁻¹ x) (LT.stable g⁻¹ x hx)
    refine ⟨u * a, ?_⟩
    have hx' : U.ρ g (U.ρ g⁻¹ x) = x := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    have h3 := hP.1 g (U.ρ g⁻¹ x) y
    rw [hx'] at h3
    rw [h3, hu, ha, map_mul]
  have hopenT : IsOpen (T' : Set U'.V) := by
    have h4 : (T' : Set U'.V) = ⋂ i, (fun y => P (e i) y) ⁻¹' Set.range (algebraMap O LL) := by
      ext y; simp only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe]; exact hmem' y
    rw [h4]
    exact isOpen_iInter_of_finite
      (fun i => hopen.preimage (IsModuleTopology.continuous_of_linearMap (R := LL) (P (e i))))
  refine ⟨⟨T', hstab, ?_, ?_, ?_⟩, ⟨hP, hmem⟩, hopenT⟩
  · rw [hT'eq]; exact Submodule.fg_span (Set.finite_range _)
  · rw [hT'eq]; exact Module.Free.of_basis (Basis.span hfO)
  · rw [hT'eq, Submodule.span_span_of_tower O LL]; exact bf.span_eq

end GlobalTheory.Pass.LocDual

end
