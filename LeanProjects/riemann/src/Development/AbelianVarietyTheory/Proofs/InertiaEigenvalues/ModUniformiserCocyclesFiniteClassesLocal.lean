import Mathlib
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteH1H2Local
open ReciprocityTheory.Gal

namespace GlobalTheory

theorem modpi_cocycles_finite_classes : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)}, FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] {M : Type} [AddCommGroup M] [Module O M] [TopologicalSpace M] [IsTopologicalAddGroup M] [ContinuousConstSMul O M] [CompactSpace M] {G : Type} [Group G] [TopologicalSpace G] (i : G ≃ₜ* Formalism.GaloisCohomology.GK p K) (ρ : Representation O G M), ContAction ρ → ∀ (ϖ : O), (p : O) ∈ Ideal.span {ϖ} → IsOpen (LinearMap.range (LinearMap.lsmul O M ϖ) : Set M) → ∃ s : Finset (Z1 ρ), ∀ c : Z1 ρ, ∃ i ∈ s, ∃ x : M, ∀ g, (c : G → M) g - (i : G → M) g - (ρ g x - x) ∈ LinearMap.range (LinearMap.lsmul O M ϖ) := by
  classical
  intro hT p _ K hK O _ M _ _ _ _ _ _ G _ _ e ρ hρ ϖ hp hN
  set N : Submodule O M := LinearMap.range (LinearMap.lsmul O M ϖ) with hNdef
  have hmemN : ∀ m : M, ϖ • m ∈ N := fun m => ⟨m, rfl⟩
  have hstab : ∀ g : G, N ≤ N.comap (ρ g) := by
    rintro g _ ⟨m, rfl⟩
    show ρ g (ϖ • m) ∈ N
    rw [map_smul]; exact hmemN _
  haveI hdisc : DiscreteTopology (M ⧸ N) :=
    QuotientAddGroup.discreteTopology (N := N.toAddSubgroup) hN
  haveI : CompactSpace (M ⧸ N) :=
    (Submodule.Quotient.mk_surjective N).compactSpace (Submodule.isOpenQuotientMap_mkQ N).continuous
  haveI : Finite (M ⧸ N) := finite_of_compact_of_discrete
  obtain ⟨r, hr⟩ := Ideal.mem_span_singleton'.mp hp
  obtain ⟨k, hk1⟩ : ∃ k : ℕ, k = 1 := ⟨1, rfl⟩
  have hkill : ∀ q : M ⧸ N, (p ^ k : ℕ) • q = 0 := by
    intro q
    subst hk1
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    rw [pow_one, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    have : (p • m : M) = ϖ • (r • m) := by
      rw [← Nat.cast_smul_eq_nsmul O, ← hr, smul_smul, mul_comm]
    rw [this]; exact hmemN _
  haveI : Module (ZMod (p ^ k)) (M ⧸ N) := AddCommGroup.zmodModule (n := p ^ k) hkill
  haveI : ContinuousConstSMul (ZMod (p ^ k)) (M ⧸ N) := ⟨fun _ => continuous_of_discreteTopology⟩
  let f : Formalism.GaloisCohomology.GK p K → Module.End (ZMod (p ^ k)) (M ⧸ N) := fun h =>
    (N.mapQ N (ρ (e.symm h)) (hstab _)).toAddMonoidHom.toZModLinearMap (p ^ k)
  have hf1 : f 1 = 1 := by
    refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  have hfm : ∀ a b, f (a * b) = f a * f b := by
    intro a b; refine LinearMap.ext fun q => ?_
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective N q
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    simp
  let ρ' : Representation (ZMod (p ^ k)) (Formalism.GaloisCohomology.GK p K) (M ⧸ N) := MonoidHom.mk (OneHom.mk f hf1) hfm
  have hρ'mk : ∀ h m, ρ' h (Submodule.Quotient.mk m) = Submodule.Quotient.mk (ρ (e.symm h) m) := fun h m => rfl
  have hρ' : ContAction ρ' := by
    have hq : Topology.IsQuotientMap (Prod.map (id : Formalism.GaloisCohomology.GK p K → Formalism.GaloisCohomology.GK p K) (N.mkQ)) :=
      (IsOpenQuotientMap.id.prodMap (Submodule.isOpenQuotientMap_mkQ N)).isQuotientMap
    show Continuous _
    rw [hq.continuous_iff]
    have : ((fun x : Formalism.GaloisCohomology.GK p K × (M ⧸ N) => ρ' x.1 x.2) ∘ Prod.map id N.mkQ)
        = fun x => Submodule.Quotient.mk (p := N) (ρ (e.symm x.1) x.2) := by
      funext x; rfl
    rw [this]
    exact (Submodule.isOpenQuotientMap_mkQ N).continuous.comp
      (hρ.comp ((e.symm.continuous.comp continuous_fst).prodMk continuous_snd))
  have hfin := (GlobalTheory.finite_H1_H2_of_localTateDuality hT p K hK k (M ⧸ N) ρ' (by omega) hρ').1
  let cb : Z1 ρ → (Formalism.GaloisCohomology.GK p K → M ⧸ N) := fun c h => Submodule.Quotient.mk ((c : G → M) (e.symm h))
  have hcb : ∀ c, cb c ∈ Z1 ρ' := by
    intro c
    refine ⟨(Submodule.isOpenQuotientMap_mkQ N).continuous.comp (c.2.1.comp e.symm.continuous), ?_⟩
    intro a b
    simp only [cb, map_mul, c.2.2, Submodule.Quotient.mk_add, hρ'mk]
  let κ : Z1 ρ → H1 ρ' := fun c => Submodule.Quotient.mk ⟨cb c, hcb c⟩
  haveI := Fintype.ofFinite (H1 ρ')
  let pick : H1 ρ' → Z1 ρ := fun y => if hy : ∃ c, κ c = y then hy.choose else 0
  refine ⟨Finset.univ.image pick, fun c => ?_⟩
  have hex : ∃ c', κ c' = κ c := ⟨c, rfl⟩
  have hpick : pick (κ c) = hex.choose := dif_pos hex
  refine ⟨pick (κ c), Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
  set c₀ := pick (κ c)
  have heq : κ c₀ = κ c := by rw [hpick]; exact hex.choose_spec
  have hB := (Submodule.Quotient.eq _).mp heq.symm
  rw [Submodule.mem_comap] at hB
  obtain ⟨q, hq⟩ := (mem_coboundaries1 ρ' _).mp hB
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective N q
  refine ⟨x, fun g => ?_⟩
  have := hq (e g)
  simp only [Submodule.coe_subtype, Submodule.coe_sub, Pi.sub_apply, cb, hρ'mk,
    MulEquiv.symm_apply_apply, ContinuousMulEquiv.symm_apply_apply] at this
  rw [← Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.Quotient.mk_sub]
  rw [this]; abel

end GlobalTheory
