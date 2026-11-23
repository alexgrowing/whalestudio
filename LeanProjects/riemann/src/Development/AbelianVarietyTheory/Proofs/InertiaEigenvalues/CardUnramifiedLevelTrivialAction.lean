import Mathlib
import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteCardTorsionLevelFractionRingQuot
import ReciprocityTheory.ClassFieldTheory.LocalClassField.ExistsDvdQKPowSubOne
import ReciprocityTheory.ClassFieldTheory.LocalClassField.UnramA
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.ShapeNeg

def LCHomLev {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G] (M : Type)
    [AddCommGroup M] [Module O M] (c : O) (I : Subgroup G) : Type :=
  {f : G → Lev M c // IsLocallyConstant f ∧ (∀ a b, f (a * b) = f a + f b) ∧ ∀ g ∈ I, f g = 0}

section Triv

variable {O : Type} [CommRing O] {G : Type} [Group G] {M : Type} [AddCommGroup M] [Module O M]

theorem mem_coboundaries_of_trivial {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m) (x : G → M) :
    x ∈ Formalism.NG.coB1 ρ ↔ x = 0 := by
  constructor
  · rintro ⟨v, rfl⟩
    funext g
    show ρ g v - v = 0
    rw [hρ, sub_self]
  · rintro rfl
    exact zero_mem _

theorem mk_eq_zero_of_triv {ρ : Representation O G M} (hρ : ∀ g m, ρ g m = m)
    (z : Formalism.NG.coZ1s ρ) : (Submodule.Quotient.mk z : Formalism.NG.H1z ρ) = 0 ↔ (z : G → M) = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype,
    mem_coboundaries_of_trivial hρ]

variable [TopologicalSpace G]

theorem card_torsion_eq_locConstHom_trivial_action (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m)
    (I : Subgroup G) (c : O) :
    Nat.card (LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (LCHomLev M c I) := by
  have hres : ∀ (g : I) (m : M), Formalism.NG.resRep ρ I g m = m := fun g m => hρ g m
  let coc : LCHomLev M c I → Formalism.NG.coZ1s ρ := fun f =>
    ⟨fun g => (f.1 g).val, fun a b => by
      show (f.1 (a * b)).val = (f.1 a).val + ρ a (f.1 b).val
      rw [hρ, f.2.2.1, Lev.val_add]⟩
  let F : LCHomLev M c I → LinearMap.ker (c • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype)) := fun f =>
    ⟨⟨⟨Submodule.Quotient.mk (coc f),
        Submodule.mem_map.2 ⟨coc f, f.2.1.comp Lev.val, rfl⟩⟩,
      by
        change (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I (coc f)) :
          Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0
        rw [mk_eq_zero_of_triv hres]
        funext g
        show (f.1 g.1).val = 0
        rw [f.2.2.2 g.1 g.2]
        rfl⟩,
      by
        rw [LinearMap.mem_ker, LinearMap.smul_apply, LinearMap.id_apply]
        apply Subtype.ext
        apply Subtype.ext
        show c • (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) = 0
        rw [← Submodule.Quotient.mk_smul, mk_eq_zero_of_triv hρ]
        funext g
        exact Lev.smul_val (f.1 g)⟩
  have hinj : ∀ f f' : LCHomLev M c I, (Submodule.Quotient.mk (coc f) : Formalism.NG.H1z ρ) =
      Submodule.Quotient.mk (coc f') → f = f' := by
    intro f f' h
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, mk_eq_zero_of_triv hρ] at h
    apply Subtype.ext
    funext g
    apply Lev.ext
    have h1 : (f.1 g).val - (f'.1 g).val = 0 := congrFun h g
    exact sub_eq_zero.1 h1
  refine (Nat.card_eq_of_bijective F ⟨fun f f' h => hinj f f' ?_, fun y => ?_⟩).symm
  · exact congrArg (fun y => y.1.1.1) h
  · obtain ⟨z, hz, hzy⟩ := Submodule.mem_map.1 y.1.1.2
    have hk : (Submodule.Quotient.mk (c • z) : Formalism.NG.H1z ρ) = 0 := by
      rw [Submodule.Quotient.mk_smul]
      change c • Submodule.mkQ _ z = 0
      rw [hzy]
      exact congrArg (fun w => w.1.1) (LinearMap.mem_ker.1 y.2)
    rw [mk_eq_zero_of_triv hρ] at hk
    have hz0 : ∀ g, c • (z : G → M) g = 0 := fun g => congrFun hk g
    have hu : Formalism.NG.resH1 ρ I (Submodule.mkQ _ z) = 0 := by
      rw [hzy]
      exact y.1.2
    have hu' : (Submodule.Quotient.mk (Formalism.NG.restrictCocycles1 ρ I z) :
        Formalism.NG.H1z (Formalism.NG.resRep ρ I)) = 0 := hu
    rw [mk_eq_zero_of_triv hres] at hu'
    have hI0 : ∀ g ∈ I, (z : G → M) g = 0 := fun g hg => congrFun hu' ⟨g, hg⟩
    let f : LCHomLev M c I := ⟨fun g => Lev.mk ((z : G → M) g) (hz0 g),
      IsLocallyConstant.desc _ Lev.val hz (fun a b h => Lev.ext h),
      fun a b => Lev.ext (by rw [Lev.val_add, Lev.val_mk, Lev.val_mk, Lev.val_mk, z.2 a b, hρ]),
      fun g hg => Lev.ext (by rw [Lev.val_mk, hI0 g hg]; rfl)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change Submodule.Quotient.mk (coc f) = y.1.1.1
    rw [← hzy]
    rfl

end Triv

section H1Triv

variable {R : Type} [CommRing R] {Γ : Type} [Group Γ] [TopologicalSpace Γ] {N : Type}
  [AddCommGroup N] [Module R N] [TopologicalSpace N] [IsTopologicalAddGroup N]
  [ContinuousConstSMul R N]

theorem H1_mk_eq_zero_iff_of_trivial {rho : Representation R Γ N} (hrho : ∀ g m, rho g m = m)
    (z : Z1 rho) : (Submodule.Quotient.mk z : H1 rho) = 0 ↔ z = 0 := by
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype, mem_coboundaries1]
  constructor
  · rintro ⟨m, hm⟩
    apply Subtype.ext
    funext g
    rw [hm g, hrho, sub_self]
    rfl
  · rintro rfl
    exact ⟨0, fun g => by rw [map_zero, sub_zero]; rfl⟩

theorem mk_mem_H1ur_of_vanish (rho : Representation R Γ N) (J : Subgroup Γ) (z : Z1 rho)
    (hz : ∀ g ∈ J, z.1 g = 0) : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J := by
  change (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
    H1 (rho.comp J.subtype)) = 0
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype]
  exact (mem_coboundaries1 _ _).2 ⟨0, fun g => by rw [map_zero, sub_zero]; exact hz g.1 g.2⟩

theorem vanish_of_mk_mem_H1ur (rho : Representation R Γ N) (J : Subgroup Γ)
    (hJ : ∀ g ∈ J, ∀ m, rho g m = m) (z : Z1 rho)
    (hz : (Submodule.Quotient.mk z : H1 rho) ∈ H1ur rho J) (g : Γ) (hg : g ∈ J) : z.1 g = 0 := by
  have h1 : (Submodule.Quotient.mk (restrictCocycles1 rho J.subtype continuous_subtype_val z) :
      H1 (rho.comp J.subtype)) = 0 := hz
  rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.coe_subtype] at h1
  obtain ⟨m, hm⟩ := (mem_coboundaries1 _ _).1 h1
  have h3 : z.1 g = rho g m - m := hm ⟨g, hg⟩
  rw [h3, hJ g hg, sub_self]

end H1Triv

theorem card_LCHomLev_eq_unrK {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    {O : Type} [CommRing O] {G : Type} [Group G] [TopologicalSpace G]
    (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M]
    (ρ : Representation O G M) (hρ : ∀ g m, ρ g m = m) (I : Subgroup G)
    (hI : ∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) (r : ℕ) [NeZero (p ^ r)] (c : O)
    (h : ((p : O) ^ r) ∈ Ideal.span {c}) :
    letI := levZ (M := M) p r h
    Nat.card (LCHomLev M c I) =
      Nat.card (Formalism.GaloisCohomology.unrK (levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom))) := by
  letI := levZ (M := M) p r h
  let ρ' := levRepZ p r h (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  let F : LCHomLev M c I → Formalism.GaloisCohomology.unrK ρ' := fun f =>
    ⟨Submodule.Quotient.mk ⟨f.1 ∘ i.symm, (f.2.1.comp_continuous i.symm.continuous).continuous,
        fun a b => by
          show f.1 (i.symm (a * b)) = f.1 (i.symm a) + ρ' a (f.1 (i.symm b))
          rw [hρ', map_mul, f.2.2.1]⟩,
      mk_mem_H1ur_of_vanish ρ' _ _ fun g hg => by
        show f.1 (i.symm g) = 0
        exact f.2.2.2 _ ((hI _).2 (by rw [ContinuousMulEquiv.apply_symm_apply]; exact hg))⟩
  refine Nat.card_eq_of_bijective F ⟨fun f f' hff => ?_, fun x => ?_⟩
  · have h1 := congrArg Subtype.val hff
    rw [← sub_eq_zero, ← Submodule.Quotient.mk_sub, H1_mk_eq_zero_iff_of_trivial hρ', sub_eq_zero] at h1
    have h2 := congrArg Subtype.val h1
    apply Subtype.ext
    funext g
    have h3 := congrFun h2 (i g)
    simpa only [Function.comp_apply, ContinuousMulEquiv.symm_apply_apply] using h3
  · obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ x.1
    have hx : (Submodule.Quotient.mk z : H1 ρ') ∈ H1ur ρ' (Formalism.GaloisCohomology.inertiaK p K) := by
      rw [hz]; exact x.2
    let f : LCHomLev M c I := ⟨fun g => z.1 (i g),
      ((IsLocallyConstant.iff_continuous _).2 z.2.1).comp_continuous i.continuous,
      fun a b => by
        show z.1 (i (a * b)) = z.1 (i a) + z.1 (i b)
        rw [map_mul, z.2.2, hρ'],
      fun g hg => vanish_of_mk_mem_H1ur ρ' _ (fun σ _ m => hρ' σ m) z hx (i g) ((hI g).1 hg)⟩
    refine ⟨f, ?_⟩
    apply Subtype.ext
    change Submodule.Quotient.mk _ = x.1
    rw [← hz]
    congr 1
    apply Subtype.ext
    funext g
    show z.1 (i (i.symm g)) = z.1 g
    rw [ContinuousMulEquiv.apply_symm_apply]

open scoped ReciprocityTheory.DiscreteGroups.LocalClassField in

theorem card_unramifiedClasses_eq_card_invariants_localGalois {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}
    (hK : FiniteDimensional ℚ_[p] K) {R : Type} [CommRing R] {N : Type} [AddCommGroup N] [Module R N]
    [Finite N] [TopologicalSpace N] [DiscreteTopology N]
    (rho : Representation R (Formalism.GaloisCohomology.GK p K) N) (hrho : ReciprocityTheory.Gal.ContAction rho)
    (hI : ∀ σ ∈ Formalism.GaloisCohomology.inertiaK p K, ∀ m, rho σ m = m) :
    Nat.card (Formalism.GaloisCohomology.unrK rho) = Nat.card (H0 rho) := by
  change Nat.card (Neutral.B1.H1ur rho (Neutral.B1.inertiaK p K)) = Nat.card (Neutral.B1.H0 rho)
  replace hI : ∀ σ ∈ Neutral.B1.inertiaK p K, ∀ m, rho σ m = m := hI
  rw [← ReciprocityTheory.DiscreteGroups.LocalClassField.subG_Kur_eq_inertiaK hK] at hI ⊢
  exact ReciprocityTheory.DiscreteGroups.LocalClassField.InflationOneCocycles.card_H1ur hrho hI (s := ReciprocityTheory.DiscreteGroups.LocalClassField.frobK p K)
    (ReciprocityTheory.DiscreteGroups.LocalClassField.isZHat_GalKur hK)

theorem card_unr_lev_of_triv : ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K →
    ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Finite (IsLocalRing.ResidueField O)] {ϖ : O},
    Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} →
    ∀ {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) {M : Type} [AddCommGroup M] [Module O M],
    (M ≃ₗ[O] Formalism.NG.KO O) → ∀ (ρ : Representation O G M), (∀ g m, ρ g m = m) →
    ∀ I : Subgroup G, (∀ g, g ∈ I ↔ i g ∈ Formalism.GaloisCohomology.inertiaK p K) → ∀ n : ℕ,
    Nat.card (LinearMap.ker (ϖ ^ n • LinearMap.id :
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype) →ₗ[O]
      ↥((Formalism.RepresentationBoundsCohomology.BR.unrH1 ρ I).comap (ReciprocityTheory.ChartRestriction.T2.HcLC ρ).subtype))) =
      Nat.card (IsLocalRing.ResidueField O) ^ n := by
  intro p _ K hK O _ _ _ _ ϖ hϖ hp G _ _ i M _ _ e ρ hρ I hI n
  have hpn : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n} :=
    Ideal.mem_span_singleton.2 (pow_dvd_pow_of_dvd (Ideal.mem_span_singleton.1 hp) n)
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩
  letI := levZ (M := M) p n hpn
  obtain ⟨hfin, hcard⟩ := levKO_card hϖ e n
  haveI := hfin
  let ρ' := levRepZ p n hpn (ρ.comp i.symm.toMulEquiv.toMonoidHom)
  have hρ' : ∀ g x, ρ' g x = x := fun g x => Lev.ext (hρ _ _)
  have hcont : ReciprocityTheory.Gal.ContAction ρ' := by
    unfold ReciprocityTheory.Gal.ContAction
    simp only [hρ']
    exact continuous_snd
  calc _ = Nat.card (LCHomLev M (ϖ ^ n) I) := card_torsion_eq_locConstHom_trivial_action ρ hρ I (ϖ ^ n)
    _ = Nat.card (Formalism.GaloisCohomology.unrK ρ') := card_LCHomLev_eq_unrK i ρ hρ I hI n (ϖ ^ n) hpn
    _ = Nat.card (H0 ρ') :=
        card_unramifiedClasses_eq_card_invariants_localGalois hK ρ' hcont (fun σ _ m => hρ' σ m)
    _ = Nat.card (Lev M (ϖ ^ n)) := Nat.card_congr (Equiv.subtypeUnivEquiv fun x g => hρ' g x)
    _ = _ := hcard

end GlobalTheory.ShapeNeg
