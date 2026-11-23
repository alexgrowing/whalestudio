import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ConvZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WachInclusionInjectiveSaturatedInterStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWittTiltLatticeTensorCancelStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WittTwistInvariantBasisChangeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsWachPrismOverIntegersStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrysLatOfTrivial
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismaticFCrystalValueLocalPrismAinfWittTensorStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdicCoordinatesOfBasisModPStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsBaseChangeLatticeOfBasisAfterExtensionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitMatrixOfPowSmulSpanInvertStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectiveOfFreeLatticeOverFiniteFreeRingStatement

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism

namespace GlobalTheory.WachLattice

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem jD_smulA (E : WEt I) (T : LocLat G Qp LL O) (α : LetA O n) (x : E.DD T) :
    E.jD T (α • x) = I.ioE (algebraMap _ R.EE α) • E.jD T x := by
  rw [← E.jD_smul, algebraMap_smul]

theorem isUnit_Q (R : WSer Γ) : IsUnit (algebraMap (LetA O n) R.EE R.Q) := by
  have h0 : IsUnit (algebraMap (LetA O n) R.EE (fun _ => R.q₀)) := by
    have h := R.EE_π.map R.φE
    rw [R.φE_ext] at h
    have e : letφ (n := n) R.φ₀ letπ = letπ * (fun _ => R.q₀) := funext fun i => R.φ₀_X
    rw [e, map_mul] at h
    exact isUnit_of_mul_isUnit_right h
  unfold WSer.Q
  induction (s - 1) with
  | zero => simpa using h0
  | succ k ih =>
    rw [pow_succ', AlgHom.mul_apply, ← R.φE_ext]
    exact ih.map R.φE

set_option maxHeartbeats 1000000 in

theorem build (E : WEt I) [Nontrivial R.EE] {Zl S W : Type} [CommRing Zl] [CommRing S] [CommRing W]
    (a : S →+* LetA O n) (z : PowerSeries Zl →+* S) (c : W →+* RW) (ψ : S →+* W) (π Q : S)
    (hψ : ∀ s, I.ioE (algebraMap _ R.EE (a s)) = c (ψ s)) (ha : Function.Injective a)
    (hinj : Function.Injective I.ioE) (hunit : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x)
    (hπ : a π = letπ) (hQ : a Q = R.Q)
    (hz : ∃ (d : ℕ) (w : Fin d → S), ∀ y : S, ∃! c : Fin d → PowerSeries Zl, y = ∑ i, z (c i) * w i)
    (d : ℕ) (o : Fin d → O) (hA : ∀ α : LetA O n, ∃ s : Fin d → S, α = ∑ j, o j • a (s j))
    (hE : ∀ e : R.EE, ∃ e' : Fin d → R.EE, (∀ j, I.ioE (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j)
    (L : ∀ T : LocLat G Qp LL O, Set (TW RW T))
    (hB : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∃ (q : ℕ) (x : Fin q → E.DD T),
      q = d * Module.finrank O ↥T.L.T ∧ (∀ y, ∃! w : Fin q → W, y = ∑ i, c (w i) • E.jD T (x i)) ∧
      ∀ y, y ∈ L T ↔ ∃ s : Fin q → S, y = ∑ i, c (ψ (s i)) • E.jD T (x i))
    (hφ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ k : ℕ, c (ψ Q) ^ k • TWmap φR T y ∈ L T)
    (hφi : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ (k q : ℕ) (s : Fin q → S) (u : Fin q → TW RW T),
      (∀ i, u i ∈ L T) ∧ c (ψ Q) ^ k • y = ∑ i, c (ψ (s i)) • TWmap φR T (u i))
    (hΓ : ∀ T : LocLat G Qp LL O, IsCrys PD T.ρ → ∀ (g : G), ∀ y ∈ L T, ∃ u ∈ L T,
      TWact (gR g) T g y - y = c (ψ π) • u)
    (hmap : ∀ (T T' : LocLat G Qp LL O) (f : LatHom T.L T'.L), IsCrys PD T.ρ → IsCrys PD T'.ρ → ∀ y ∈ L T,
      TensorProduct.map (LinearMap.id : RW →ₗ[O] RW) ((f.f.restrictScalars O).restrict f.T_le) y ∈ L T')
    (hone : IsCrys PD Γ.one.ρ) (e₀ : ↥Γ.one.L.T) (he₀ : Submodule.span O {e₀} = ⊤)
    (hLone : ∀ y, y ∈ L Γ.one ↔ ∃ α : LetA O n, y = I.ioE (algebraMap _ R.EE α) • ((1 : RW) ⊗ₜ[O] e₀)) :
    Nonempty (WN E (a.comp z)) := by
  classical
  have hj : ∀ T (t : S) (x : E.DD T), E.jD T (a t • x) = c (ψ t) • E.jD T x := fun T t x => by
    rw [jD_smulA, hψ]
  choose q x hq hbas hL using hB
  have hsum : ∀ T hT (t : Fin (q T hT) → S),
      E.jD T (∑ i, a (t i) • x T hT i) = ∑ i, c (ψ (t i)) • E.jD T (x T hT i) := fun T hT t => by
    rw [map_sum]; exact Finset.sum_congr rfl fun i _ => hj _ _ _
  have hD : ∀ T hT (y : E.DD T), E.jD T y ∈ L T ↔ ∃ t : Fin (q T hT) → S, y = ∑ i, a (t i) • x T hT i :=
    fun T hT y => by
      rw [hL T hT]
      refine exists_congr fun t => ?_
      rw [← hsum, (E.jD_inj T).eq_iff]
  have hlift : ∀ T, IsCrys PD T.ρ → ∀ y ∈ L T, ∃ y', E.jD T y' = y := fun T hT y hy => by
    obtain ⟨t, rfl⟩ := (hL T hT y).1 hy
    exact ⟨_, hsum T hT t⟩
  have hadd : ∀ T, IsCrys PD T.ρ → ∀ y y' : E.DD T, E.jD T y ∈ L T → E.jD T y' ∈ L T →
      E.jD T (y + y') ∈ L T := fun T hT y y' hy hy' => by
    obtain ⟨t, rfl⟩ := (hD T hT y).1 hy
    obtain ⟨t', rfl⟩ := (hD T hT y').1 hy'
    refine (hD T hT _).2 ⟨t + t', ?_⟩
    simp only [Pi.add_apply, map_add, add_smul, Finset.sum_add_distrib]
  have hzero : ∀ T, IsCrys PD T.ρ → E.jD T 0 ∈ L T := fun T hT => (hD T hT _).2 ⟨0, by simp⟩
  have hS : ∀ T, IsCrys PD T.ρ → ∀ (t : S) (y : E.DD T), E.jD T y ∈ L T → E.jD T (a t • y) ∈ L T :=
    fun T hT t y hy => by
    obtain ⟨t', rfl⟩ := (hD T hT y).1 hy
    refine (hD T hT _).2 ⟨fun i => t * t' i, ?_⟩
    simp only [map_mul, mul_smul, Finset.smul_sum]
  have hO : ∀ T, IsCrys PD T.ρ → ∀ (t : O) (y : E.DD T), E.jD T y ∈ L T → E.jD T (t • y) ∈ L T :=
    fun T hT t y hy => by
    rw [← E.map_latSmul, E.jD_map]
    exact hmap T T _ hT hT _ hy
  let N₀ : ∀ T, IsCrys PD T.ρ → Submodule (LetA O n) (E.DD T) := fun T hT =>
    { carrier := {y | E.jD T y ∈ L T}
      add_mem' := fun hy hy' => hadd T hT _ _ hy hy'
      zero_mem' := hzero T hT
      smul_mem' := fun α y hy => by
        obtain ⟨t, rfl⟩ := hA α
        rw [Finset.sum_smul]
        refine Finset.sum_induction _ (fun y => E.jD T y ∈ L T) (hadd T hT) (hzero T hT) fun j _ => ?_
        rw [smul_assoc]
        exact hO T hT _ _ (hS T hT _ _ hy) }
  let N : ∀ T, Submodule (LetA O n) (E.DD T) := fun T => if hT : IsCrys PD T.ρ then N₀ T hT else ⊥
  have hN : ∀ T, IsCrys PD T.ρ → ∀ y, y ∈ N T ↔ E.jD T y ∈ L T := fun T hT y => by
    simp only [N, dif_pos hT]; rfl
  have hN0 : ∀ T, ¬ IsCrys PD T.ρ → N T = ⊥ := fun T hT => dif_neg hT
  have hNx : ∀ T hT (y : E.DD T), y ∈ N T ↔ ∃ t : Fin (q T hT) → S, y = ∑ i, a (t i) • x T hT i :=
    fun T hT y => (hN T hT y).trans (hD T hT y)
  have hQk : ∀ T (k : ℕ) (y : E.DD T), E.jD T (R.Q ^ k • y) = c (ψ Q) ^ k • E.jD T y := fun T k y => by
    rw [← hQ, ← map_pow, hj, map_pow, map_pow]
  have hNπ : ∀ T (g : Γ.Gam), ∀ y ∈ N T, ∃ y' ∈ N T, E.γD T g y - y = (letπ : LetA O n) • y' := by
    intro T g y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨g, rfl⟩ := Γ.resΓ_onto g
      obtain ⟨u, hu, h⟩ := hΓ T hT g _ ((hN T hT y).1 hy)
      obtain ⟨y', rfl⟩ := hlift T hT u hu
      refine ⟨y', (hN T hT _).2 hu, E.jD_inj T ?_⟩
      rw [map_sub, E.jD_act, h, ← hπ, hj]
    · rw [hN0 T hT] at hy ⊢
      rw [Submodule.mem_bot] at hy
      exact ⟨0, Submodule.zero_mem _, by simp [hy]⟩
  refine ⟨{ N := N, N_base := ?_, N_φ := ?_, N_φinv := ?_, N_fg := ?_, N_Γ := ?_, N_π := hNπ, map_N := ?_,
            one_e := ?_, N_proj := ?_, N_junk := hN0 }⟩
  · intro T hT
    have hfree := (E.DD_free T).1
    have hfin : Module.Finite R.EE (E.DD T) := by
      rcases Nat.eq_zero_or_pos (Module.finrank R.EE (E.DD T)) with h0 | h0
      · have hq0 : q T hT = 0 := by rw [hq, ← (E.DD_free T).2, h0, mul_zero]
        have : Subsingleton (E.DD T) := ⟨fun y y' => E.jD_inj T (by
          obtain ⟨w, hw, -⟩ := hbas T hT (E.jD T y)
          obtain ⟨w', hw', -⟩ := hbas T hT (E.jD T y')
          have : IsEmpty (Fin (q T hT)) := by rw [hq0]; infer_instance
          rw [hw, hw', Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_empty])⟩
        infer_instance
      · exact Module.finite_of_finrank_pos h0
    exact GlobalTheory.T.isBaseChange_lattice_of_basis_after_extension S (LetA O n) R.EE O W RW (E.DD T) (TW RW T) a I.ioE c (E.jD T).toAddMonoidHom hinj hunit
      (E.jD_smul T) (fun t => ⟨_, (hψ t).symm⟩) d _ o hE ⟨Module.finBasis R.EE (E.DD T)⟩ _ (x T hT)
      (by rw [hq, (E.DD_free T).2]) (hbas T hT) _ (hNx T hT)
  · intro T y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨k, hk⟩ := hφ T hT _ ((hN T hT y).1 hy)
      refine ⟨k, (hN T hT _).2 ?_⟩
      rw [← E.jD_φ, ← hQk] at hk
      exact hk
    · rw [hN0 T hT] at hy ⊢
      rw [Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · intro T y hy
    by_cases hT : IsCrys PD T.ρ
    · obtain ⟨k, m, t, u, hu, hk⟩ := hφi T hT _ ((hN T hT y).1 hy)
      choose u' hu' using fun i => hlift T hT _ (hu i)
      have e : R.Q ^ k • y = ∑ i, a (t i) • E.φD T (u' i) := E.jD_inj T (by
        rw [hQk, hk, map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [hj, E.jD_φ, hu'])
      refine ⟨k, ?_⟩
      change R.Q ^ k • y ∈ _
      rw [e]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _
        (Submodule.subset_span ⟨u' i, (hN T hT _).2 (by rw [hu']; exact hu i), rfl⟩)
    · rw [hN0 T hT, Submodule.mem_bot] at hy
      exact ⟨0, by simp [hy]⟩
  · intro T
    by_cases hT : IsCrys PD T.ρ
    · have e : N T = Submodule.span (LetA O n) (Set.range (x T hT)) := by
        refine le_antisymm (fun y hy => ?_) (Submodule.span_le.2 ?_)
        · obtain ⟨t, rfl⟩ := (hNx T hT y).1 hy
          exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
        · rintro _ ⟨i, rfl⟩
          refine (hNx T hT _).2 ⟨Pi.single i 1, ?_⟩
          rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
          simp
      rw [e]
      exact Submodule.fg_span (Set.finite_range _)
    · rw [hN0 T hT]; exact Submodule.fg_bot
  · intro T g y hy
    obtain ⟨y', hy', h⟩ := hNπ T g y hy
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    exact (N T).add_mem ((N T).smul_mem _ hy') hy
  · intro T T' f hT hT' y hy
    rw [hN T' hT', E.jD_map]
    exact hmap T T' f hT hT' _ ((hN T hT y).1 hy)
  · obtain ⟨e, he⟩ := hlift _ hone _ ((hLone ((1 : RW) ⊗ₜ[O] e₀)).2 ⟨1, by simp⟩)
    refine ⟨e, e₀, he₀, he, Submodule.ext fun y => ?_⟩
    rw [hN _ hone, hLone, Submodule.mem_span_singleton]
    refine exists_congr fun α => ?_
    rw [← he, ← jD_smulA, (E.jD_inj _).eq_iff, eq_comm]
  · intro T
    by_cases hT : IsCrys PD T.ρ
    · refine GlobalTheory.T.projective_of_free_lattice_over_finite_free_ring _ S _ _ z a (N T) _ (x T hT) (hNx T hT) (fun t ht => ?_) hz
      have h1 := congrArg (E.jD T) ht
      rw [hsum, map_zero] at h1
      have h2 := (hbas T hT 0).unique (y₁ := fun i => ψ (t i)) (y₂ := 0) h1.symm (by simp)
      funext i
      apply ha
      apply R.EE_inj
      apply hinj
      rw [hψ, congrFun h2 i]
      simp
    · let _ := Module.compHom ↥(N T) (a.comp z)
      have : Subsingleton ↥(N T) := by rw [hN0 T hT]; infer_instance
      infer_instance

end Generic

section Realisation

variable {l : ℕ} [Fact l.Prime] {K : FinExt l} {PS : Obj l ↥(OL K)} (ioH : Hom PS (ainfObj K))

theorem full (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {T T' : Type} [AddCommGroup T] [Module ℤ_[l] T]
    [AddCommGroup T'] [Module ℤ_[l] T'] {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} {ρ' : ↥(GK K) → (T' →ₗ[ℤ_[l]] T')}
    {E E' : FCrys l ↥(OL K)}
    {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    {j' : E'.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T')}
    (H : Realises K E (ainfObj K) (ainfId K) T ρ j) (H' : Realises K E' (ainfObj K) (ainfId K) T' ρ' j')
    (f : T →ₗ[ℤ_[l]] T') (hf : ∀ g x, f (ρ g x) = ρ' g (f x)) (x : E.M PS) :
    ∃ x' : E'.M PS, j' (E'.tr ioH x') = f.lTensor (WCb l) (j (E.tr ioH x)) := by
  obtain ⟨u, hu, -⟩ := (BS l K _ _ (isAinf_ainfObj K)).2 T T' ρ ρ' E E' j j' H H' f hf
  exact ⟨u.u PS x, by rw [← u.u_tr, hu]⟩

theorem range_trivial (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK K) → (T →ₗ[ℤ_[l]] T)} {E : FCrys l ↥(OL K)}
    {j : E.M (ainfObj K) →ₛₗ[(inclW l).comp (ainfId K).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises K E (ainfObj K) (ainfId K) T ρ j) (hρ : ∀ g x, ρ g x = x) {d : ℕ}
    (b : Module.Basis (Fin d) ℤ_[l] T) (y : WCb l ⊗[ℤ_[l]] T) :
    (∃ x : E.M PS, y = j (E.tr ioH x)) ↔
      ∃ t : Fin d → PS.A, y = ∑ i, inclW l (ainfId K (ioH.f (t i))) ⊗ₜ[ℤ_[l]] b i := by
  have U := (isAinf_ainfObj K).realises_unit
  have h1 : ∀ (w : WCb l) i, (LinearMap.toSpanSingleton ℤ_[l] T (b i)).lTensor (WCb l) (w ⊗ₜ[ℤ_[l]] (1 : ℤ_[l])) =
      w ⊗ₜ[ℤ_[l]] b i := fun w i => by
    rw [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, one_smul]
  have h2 : ∀ t : PS.A, unitMap (ainfObj K) (ainfId K) ((FCrys.unit l ↥(OL K)).tr ioH t) =
      inclW l (ainfId K (ioH.f t)) ⊗ₜ[ℤ_[l]] (1 : ℤ_[l]) := fun t => unitMap_apply _ _ _
  constructor
  · rintro ⟨x, rfl⟩
    choose t ht using fun i => full ioH BS H U (b.coord i) (fun g x => by rw [hρ]; rfl) x
    refine ⟨t, ?_⟩
    have key : ∀ y : WCb l ⊗[ℤ_[l]] T, y = ∑ i,
        (LinearMap.toSpanSingleton ℤ_[l] T (b i)).lTensor (WCb l) ((b.coord i).lTensor (WCb l) y) := fun y => by
      induction y with
      | zero => simp
      | tmul w t =>
        simp only [LinearMap.lTensor_tmul, LinearMap.toSpanSingleton_apply, Module.Basis.coord_apply]
        rw [← TensorProduct.tmul_sum, b.sum_repr]
      | add y y' h h' =>
        simp only [map_add, Finset.sum_add_distrib]
        rw [← h, ← h']
    rw [key (j (E.tr ioH x))]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ht]
    exact (congrArg _ (h2 (t i))).trans (h1 _ _)
  · rintro ⟨t, rfl⟩
    choose x hx using fun i => full ioH BS U H (LinearMap.toSpanSingleton ℤ_[l] T (b i))
      (fun g x => by rw [hρ]; rfl) (t i)
    refine ⟨∑ i, x i, ?_⟩
    rw [map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hx, h2, h1]

end Realisation

section Kappa

variable {Z O W RW T T' : Type} [CommRing Z] [CommRing O] [CommRing W] [CommRing RW] [Algebra Z W] [Algebra O RW]
  [AddCommGroup T] [Module Z T] [Module O T] [AddCommGroup T'] [Module Z T'] [Module O T'] (c : W →+* RW)

theorem kappa_smul (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t) (w : W) (y : W ⊗[Z] T) :
    κ (w • y) = c w • κ y := by
  induction y with
  | zero => simp
  | tmul w' t => rw [TensorProduct.smul_tmul', hκ, hκ, TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add y y' h h' => rw [smul_add, map_add, map_add, smul_add, h, h']

theorem kappa_map (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t)
    (κ' : W ⊗[Z] T' ≃+ RW ⊗[O] T') (hκ' : ∀ w t, κ' (w ⊗ₜ t) = c w ⊗ₜ t)
    (σ : W →ₗ[Z] W) (σ' : RW →ₗ[O] RW) (hσ : ∀ w, σ' (c w) = c (σ w))
    (f : T →ₗ[Z] T') (f' : T →ₗ[O] T') (hf : ∀ t, f' t = f t) (y : W ⊗[Z] T) :
    κ' (TensorProduct.map σ f y) = TensorProduct.map σ' f' (κ y) := by
  induction y with
  | zero => simp
  | tmul w' t => rw [TensorProduct.map_tmul, hκ, hκ', TensorProduct.map_tmul, hσ, hf]
  | add y y' h h' => simp only [map_add, h, h']

theorem kappa_basis (κ : W ⊗[Z] T ≃+ RW ⊗[O] T) (hκ : ∀ w t, κ (w ⊗ₜ t) = c w ⊗ₜ t) {q : ℕ}
    (b : Module.Basis (Fin q) W (W ⊗[Z] T)) (y : RW ⊗[O] T) :
    ∃! w : Fin q → W, y = ∑ i, c (w i) • κ (b i) := by
  have key : ∀ w : Fin q → W, ∑ i, c (w i) • κ (b i) = κ (b.equivFun.symm w) := fun w => by
    rw [b.equivFun_symm_apply, map_sum]
    exact Finset.sum_congr rfl fun i _ => (kappa_smul c κ hκ _ _).symm
  refine ⟨b.equivFun (κ.symm y), by simp only [key]; simp, fun w hw => ?_⟩
  rw [hw, key, AddEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

omit [Module Z T] in

theorem map_mulLeft (r : RW) (y : RW ⊗[O] T) :
    TensorProduct.map (LinearMap.mulLeft O r) (LinearMap.id : T →ₗ[O] T) y = r • y := by
  induction y with
  | zero => simp
  | tmul w' t => rw [TensorProduct.map_tmul, TensorProduct.smul_tmul']; rfl
  | add y y' h h' => rw [map_add, smul_add, h, h']

end Kappa

section Rings

variable {Z O W : Type} [CommRing Z] [CommRing O] [CommRing W] [Algebra Z O] [Algebra Z W]

theorem coord_tensor {d : ℕ} (o : Module.Basis (Fin d) Z O) (r : O ⊗[Z] W) :
    ∃! w : Fin d → W, r = ∑ j, o j • (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W).toRingHom (w j) := by
  let b := o.baseChange W
  have key : ∀ w : Fin d → W,
      ∑ j, o j • (Algebra.TensorProduct.includeRight : W →ₐ[Z] O ⊗[Z] W).toRingHom (w j) =
        TensorProduct.comm Z W O (b.equivFun.symm w) := fun w => by
    rw [b.equivFun_symm_apply, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [b, TensorProduct.smul_tmul']
  refine ⟨b.equivFun ((TensorProduct.comm Z W O).symm r), by simp only [key]; simp, fun w hw => ?_⟩
  rw [hw, key, LinearEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

theorem isUnit_of_one_tmul [Module.Free Z O] [Module.Finite Z O] [Nontrivial (O ⊗[Z] W)] (w : W)
    (h : IsUnit ((1 : O) ⊗ₜ[Z] w)) : IsUnit w := by
  have : Nontrivial (W ⊗[Z] O) := (TensorProduct.comm Z O W).injective.nontrivial
  have h1 : IsUnit (algebraMap W (W ⊗[Z] O) w) := h.map (Algebra.TensorProduct.comm Z O W)
  exact isUnit_of_map_unit _ _ h1

end Rings

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

theorem coord_EE (I : WIo R RA RW inclR φR gR πA) {S W : Type} [CommRing S] [CommRing W]
    (a : S →+* LetA O n) (c : W →+* RW) (ψ : S →+* W) (π : S)
    (hψ : ∀ s, I.ioE (algebraMap _ R.EE (a s)) = c (ψ s)) (hπ : a π = letπ)
    (hcu : ∀ w, IsUnit (c w) → IsUnit w) (hW : IsAdicComplete (Ideal.span {((PD.p : ℕ) : W)}) W)
    {d : ℕ} (o : Fin d → O) (hRW : ∀ r : RW, ∃! w : Fin d → W, r = ∑ j, o j • c (w j))
    (hA : ∀ α : LetA O n, ∃ s : Fin d → S, α = ∑ j, o j • a (s j))
    (e : R.EE) : ∃ e' : Fin d → R.EE, (∀ j, I.ioE (e' j) ∈ Set.range c) ∧ e = ∑ j, o j • e' j := by
  refine GlobalTheory.T.exists_adic_coordinates_of_basis_mod_p PD.p _ R.EE W RW I.ioE c d o hRW R.EE_complete hW (fun e => ?_) e
  obtain ⟨α, m, h⟩ := R.EE_dense e 1
  obtain ⟨t, rfl⟩ := hA α
  obtain ⟨u, hu⟩ := R.EE_π
  have h1 : I.ioE u = c (ψ π) := by rw [hu, ← hπ, hψ]
  obtain ⟨w, hw⟩ : IsUnit (ψ π) := hcu _ (by rw [← h1]; exact u.isUnit.map I.ioE)
  have h2 : I.ioE ((u⁻¹ : R.EEˣ) : R.EE) = c ((w⁻¹ : Wˣ) : W) := by
    have h3 : I.ioE u * c ((w⁻¹ : Wˣ) : W) = 1 := by
      rw [h1, ← hw, ← map_mul, Units.mul_inv, map_one]
    rw [← mul_one (I.ioE _), ← h3, ← mul_assoc, ← map_mul, Units.inv_mul, map_one, one_mul]
  refine ⟨fun j => ((u⁻¹ : R.EEˣ) : R.EE) ^ m * algebraMap _ R.EE (a (t j)),
    fun j => ⟨((w⁻¹ : Wˣ) : W) ^ m * ψ (t j), by simp only [map_mul, map_pow, h2, hψ]⟩, ?_⟩
  rw [pow_one, map_pow, ← hu] at h
  convert Ideal.mul_mem_left _ (((u⁻¹ : R.EEˣ) : R.EE) ^ m) h using 1
  rw [mul_sub, mul_left_comm, ← mul_pow, Units.inv_mul, one_pow, mul_one, map_sum, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.smul_def, Algebra.smul_def, map_mul, ← IsScalarTower.algebraMap_apply, mul_left_comm]

theorem card_basis {Z W : Type} [CommRing Z] [CommRing W] [Nontrivial Z] [Nontrivial W] [Nontrivial O] [Algebra Z O]
    [Algebra Z W] (T : LocLat G Qp LL O) {d q : ℕ} (o : Module.Basis (Fin d) Z O) :
    letI : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
    Module.Basis (Fin q) W (W ⊗[Z] ↥T.L.T) → q = d * Module.finrank O ↥T.L.T := by
  let _ : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
  intro b
  have := Module.Free.of_basis o
  have := T.L.free
  have : IsScalarTower Z O ↥T.L.T := ⟨fun z x t => by
    rw [Algebra.smul_def, mul_smul]; rfl⟩
  have : Module.Free Z ↥T.L.T := Module.Free.trans (S := O)
  have h1 := Module.finrank_eq_card_basis b
  rw [Module.finrank_baseChange, ← Module.finrank_mul_finrank Z O ↥T.L.T,
    Module.finrank_eq_card_basis o, Fintype.card_fin, Fintype.card_fin] at h1
  exact h1.symm

theorem one_basis {Z : Type} [CommRing Z] [Algebra Z O] (Γ : WGam PD LL O v n s)
    (hO : Function.Injective (algebraMap O LL)) {d : ℕ} (o : Module.Basis (Fin d) Z O) :
    letI : Module Z ↥Γ.one.L.T := Module.compHom ↥Γ.one.L.T (algebraMap Z O)
    ∃ (e₀ : ↥Γ.one.L.T) (b : Module.Basis (Fin d) Z ↥Γ.one.L.T),
      Submodule.span O {e₀} = ⊤ ∧ ∀ i, b i = o i • e₀ := by
  let _ : Module Z ↥Γ.one.L.T := Module.compHom ↥Γ.one.L.T (algebraMap Z O)
  obtain ⟨e, he, h⟩ := Γ.one_line
  let e₀ : ↥Γ.one.L.T := ⟨e, by rw [h]; exact Submodule.mem_span_singleton_self e⟩
  have hs : ∀ t : ↥Γ.one.L.T, ∃ x : O, x • e₀ = t := fun t => by
    have ht : (t : Γ.one.V) ∈ Submodule.span O {e} := h ▸ t.2
    obtain ⟨x, hx⟩ := Submodule.mem_span_singleton.1 ht
    exact ⟨x, Subtype.ext hx⟩
  let f : O →ₗ[Z] ↥Γ.one.L.T :=
    { toFun := fun x => x • e₀
      map_add' := fun x y => add_smul x y e₀
      map_smul' := fun z x => by rw [Algebra.smul_def, mul_smul]; rfl }
  have hf : Function.Bijective f := by
    refine ⟨(injective_iff_map_eq_zero f).2 fun x hx => ?_, hs⟩
    have h1 : x • e = 0 := congrArg Subtype.val hx
    rw [← algebraMap_smul LL x e] at h1
    exact hO (((smul_eq_zero.1 h1).resolve_right he).trans (map_zero _).symm)
  exact ⟨e₀, o.map (LinearEquiv.ofBijective f hf),
    eq_top_iff.2 fun t _ => Submodule.mem_span_singleton.2 (hs t), fun i => rfl⟩

theorem exists_restrict {Z : Type} [CommRing Z] [Algebra Z O] {T T' : LocLat G Qp LL O} (f : LatHom T.L T'.L) :
    letI : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
    letI : Module Z ↥T'.L.T := Module.compHom ↥T'.L.T (algebraMap Z O)
    ∃ f' : ↥T.L.T →ₗ[Z] ↥T'.L.T, (∀ t, (f.f.restrictScalars O).restrict f.T_le t = f' t) ∧
      ∀ g t, f' (T.actT g t) = T'.actT g (f' t) := by
  let _ : Module Z ↥T.L.T := Module.compHom ↥T.L.T (algebraMap Z O)
  let _ : Module Z ↥T'.L.T := Module.compHom ↥T'.L.T (algebraMap Z O)
  exact ⟨{ toFun := (f.f.restrictScalars O).restrict f.T_le
           map_add' := map_add _
           map_smul' := fun z x => ((f.f.restrictScalars O).restrict f.T_le).map_smul (algebraMap Z O z) x },
    fun _ => rfl, fun g t => Subtype.ext (f.equiv g t)⟩

theorem resΓ_eq_one (Γ : WGam PD LL O v n s) (hO : Function.Injective (algebraMap O LL)) (g : G)
    (hg : ((PD.χ g : Qpˣ) : Qp) = 1) : Γ.resΓ g = 1 := by
  apply Γ.χΓ_inj
  rw [map_one]
  apply Units.ext
  apply hO
  rw [Γ.χΓ_res g, hg, Units.val_one, map_one, map_one]

end Generic

theorem perfect_tilt {l : ℕ} [Fact l.Prime] : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, -, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  obtain ⟨a', rfl⟩ := surjective_frobenius (OCb l) l a
  obtain ⟨b', rfl⟩ := surjective_frobenius (OCb l) l b
  refine ⟨algebraMap _ _ a' / algebraMap _ _ b', ?_⟩
  simp [frobenius_def, div_pow]

theorem exists_basis_OL {l : ℕ} [Fact l.Prime] (LL : FinExt l) :
    ∃ d, Nonempty (Module.Basis (Fin d) ℤ_[l] ↥(OL LL)) := by
  have := LL.2
  have : Module.IsTorsionFree ℤ_[l] ↥LL.1 := Module.isTorsionFree_iff_algebraMap_injective.mpr (by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] ↥LL.1]
    exact (algebraMap ℚ_[l] ↥LL.1).injective.comp (IsFractionRing.injective ℤ_[l] ℚ_[l]))
  have : Module.Free ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.module_free ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  have : Module.Finite ℤ_[l] ↥(OL LL) :=
    IsIntegralClosure.finite ℤ_[l] ℚ_[l] ↥LL.1 ↥(integralClosure ℤ_[l] ↥LL.1)
  exact ⟨_, ⟨Module.finBasis ℤ_[l] ↥(OL LL)⟩⟩

end GlobalTheory.WachLattice
