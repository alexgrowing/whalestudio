import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsUnitOfOneTmul

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL GlobalTheory.Prism

namespace GlobalTheory.WachLattice

section Generic

variable {l : ℕ} [Fact l.Prime] {F : FinExt l} {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData ↥(GK F) Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n s : ℕ}
    {Γ : WGam PD LL O v n s} {R : WSer Γ}
    {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : ↥(GK F) → (RW →ₐ[O] RW)} {πA : RA}
    {I : WIo R RA RW inclR φR gR πA}

set_option maxHeartbeats 2000000 in

theorem build_prism (BS : GlobalTheory.Published.BhattScholzeCrystallineLattices) (E : WEt I) [Algebra ℤ_[l] O]
    [Nontrivial O] [FiniteDimensional Qp LL] (hO : Function.Injective (algebraMap O LL)) (hp : PD.p = l)
    {PS PW : Obj l ↥(OL F)} (ev : Hom PS PW) (ioH : Hom PS (ainfObj F)) (gH : ↥(GK F) → Hom PS PS)
    (a : PS.A →+* LetA O n) (z : PowerSeries ℤ_[l] →+* PS.A) (π Q : PS.A) (c : WCb l →+* RW)
    (hψ₀ : ∀ x, I.ioE (algebraMap _ R.EE (a x)) = c (inclW l (ainfId F (ioH.f x)))) (ha : Function.Injective a)
    (hinj : Function.Injective I.ioE) (hunit : ∀ x : R.EE, IsUnit (I.ioE x) → IsUnit x)
    (hγ : ∀ g x, a ((gH g).f x) = letγ (R.γ₀ (Γ.resΓ g)) (a x))
    (hio : ∀ g, ioH.comp (gH g) = (ainfHom F g).comp ioH) (hev : ∀ g, ev.comp (gH g) = ev)
    (hπ : a π = letπ) (hker : RingHom.ker ev.f = Ideal.span {π}) (hI : PS.I = Ideal.span {Q}) (hQ : a Q = R.Q)
    (hloc : IsLocalRing PS.A)
    (hz : ∃ (d : ℕ) (w : Fin d → PS.A), ∀ x, ∃! c : Fin d → PowerSeries ℤ_[l], x = ∑ i, z (c i) * w i)
    {d : ℕ} (o : Module.Basis (Fin d) ℤ_[l] O)
    (hA₀ : ∀ x : LetA O n, ∃! c : Fin d → PS.A, ∀ k, x k = ∑ i, PowerSeries.C (o i) * a (c i) k)
    (hRW : ∀ r : RW, ∃! w : Fin d → WCb l, r = ∑ j, o j • c (w j)) (hcu : ∀ w, IsUnit (c w) → IsUnit w)
    (hcφ : ∀ w, φR (c w) = c (frobW l w)) (hcg : ∀ (g : ↥(GK F)) w, gR g (c w) = c (galW l (g : GQ l) w))
    (hκ : ∀ T : LocLat ↥(GK F) Qp LL O,
      letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
      ∃ κ : (WCb l ⊗[ℤ_[l]] ↥T.L.T) ≃+ TW RW T, ∀ w t, κ (w ⊗ₜ[ℤ_[l]] t) = c w ⊗ₜ[O] t)
    (hreal : ∀ T : LocLat ↥(GK F) Qp LL O, IsCrys PD T.ρ →
      letI : Module ℤ_[l] ↥T.L.T := Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
      ∃ (ρ : ↥(GK F) → (↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T)) (C : FCrys l ↥(OL F))
        (j : C.M (ainfObj F) →ₛₗ[(inclW l).comp (ainfId F).toRingHom] (WCb l ⊗[ℤ_[l]] ↥T.L.T)),
        Realises F C (ainfObj F) (ainfId F) ↥T.L.T ρ j ∧ ∀ g t, T.actT g t = ρ g t)
    (H : ↥(GK F) → Prop) (hH : ∀ g, H g → Γ.resΓ g = 1)
    (hmem : ∀ (T : LocLat ↥(GK F) Qp LL O) (q : ℕ) (x : Fin q → TW RW T) (A : Matrix (Fin q) (Fin q) R.EE),
      IsUnit A → (∀ g, H g → ∀ i, TWact (gR g) T g (x i) = x i) →
      (∀ j, TWmap φR T (x j) = ∑ i, TensorProduct.map (LinearMap.mulLeft O (I.ioE (A i j)))
        (LinearMap.id : ↥T.L.T →ₗ[O] ↥T.L.T) (x i)) → ∀ i, x i ∈ Set.range (E.jD T)) :
    Nonempty (WN E (a.comp z)) := by
  classical
  let _ : ∀ T : LocLat ↥(GK F) Qp LL O, Module ℤ_[l] ↥T.L.T :=
    fun T => Module.compHom ↥T.L.T (algebraMap ℤ_[l] O)
  have : Nontrivial R.EE := R.EE_inj.nontrivial
  have : Nontrivial RW := hinj.nontrivial
  let ψ : PS.A →+* WCb l := ((inclW l).comp (ainfId F).toRingHom).comp ioH.f
  have hψ1 : ∀ x, ψ x = inclW l (ainfId F (ioH.f x)) := fun _ => rfl
  have hψ : ∀ x, I.ioE (algebraMap _ R.EE (a x)) = c (ψ x) := hψ₀
  have hA : ∀ α : LetA O n, ∃ t : Fin d → PS.A, α = ∑ j, o j • a (t j) := fun α => by
    obtain ⟨t, ht, -⟩ := hA₀ α
    refine ⟨t, funext fun k => ?_⟩
    rw [ht, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ => (PowerSeries.smul_eq_C_mul _ _).symm
  have hQu : IsUnit (algebraMap _ R.EE (a Q)) := hQ ▸ isUnit_Q R
  have hQ0 : ψ Q ≠ 0 := fun h => (hQu.map I.ioE).ne_zero (by rw [hψ, h, map_zero])
  have := perfect_tilt (l := l)
  have hE := coord_EE I a c ψ π hψ hπ hcu (by rw [hp]; exact WittVector.isAdicCompleteIdealSpanP) o hRW hA
  choose κ hκ using hκ
  choose ρ C j hR hρ using hreal
  choose q b cb hcb h1 h2 h3 h4 using fun T hT => GlobalTheory.T.prismaticFCrystal_value_localPrism_ainf_wittTensor l F PS PW ev ioH gH π Q ψ hψ1 hio hev hker
    (hI ▸ Ideal.mem_span_singleton_self Q) hloc hQ0 _ _ _ _ (hR T hT)
  have hκs := fun T => kappa_smul c (κ T) (hκ T)
  have hκφ : ∀ T y, κ T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) = TWmap φR T (κ T y) :=
    fun T y => kappa_map c (κ T) (hκ T) (κ T) (hκ T) _ _ hcφ _ _ (fun _ => rfl) y
  have hκg : ∀ T hT (g : ↥(GK F)) y, κ T (TensorProduct.map (galW l (g : GQ l)).toLinearMap (ρ T hT g) y) =
      TWact (gR g) T g (κ T y) :=
    fun T hT g y => kappa_map c (κ T) (hκ T) (κ T) (hκ T) _ _ (hcg g) _ _ (hρ T hT g) y
  let ν : ∀ T hT, (C T hT).M PS → TW RW T := fun T hT x => κ T (j T hT ((C T hT).tr ioH x))
  have hνs : ∀ T hT (t : PS.A) x, ν T hT (t • x) = c (ψ t) • ν T hT x := fun T hT t x => by
    simp only [ν]
    rw [LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ, hκs]; rfl
  have hνsum : ∀ T hT (t : Fin (q T hT) → PS.A),
      ν T hT (∑ i, t i • b T hT i) = ∑ i, c (ψ (t i)) • κ T (cb T hT i) := fun T hT t => by
    simp only [ν]
    rw [map_sum, map_sum, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hcb]; exact hνs T hT _ _
  have hν1 : ∀ T hT x, ∃ (k : ℕ) (m : (C T hT).M PS), c (ψ Q) ^ k • TWmap φR T (ν T hT x) = ν T hT m :=
    fun T hT x => by
      obtain ⟨k, m, h⟩ := h1 T hT x
      exact ⟨k, m, by simp only [ν]; rw [← h, hκs, map_pow, hκφ]⟩
  have hν2 : ∀ T hT x, ∃ (k : ℕ) (t : Fin (q T hT) → PS.A),
      c (ψ Q) ^ k • ν T hT x = ∑ i, c (ψ (t i)) • TWmap φR T (κ T (cb T hT i)) := fun T hT x => by
    obtain ⟨k, t, h⟩ := h2 T hT x
    refine ⟨k, t, ?_⟩
    simp only [ν]
    rw [← map_pow, ← hκs, h, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [hκs, hκφ]
  have hν3 : ∀ T hT g x, TWact (gR g) T g (ν T hT x) = ν T hT ((C T hT).tr (gH g) x) := fun T hT g x => by
    simp only [ν]
    rw [← h3, hκg]
  have hνb : ∀ T hT i, κ T (cb T hT i) = ν T hT (b T hT i) := fun T hT i => by rw [hcb]
  let L : ∀ T : LocLat ↥(GK F) Qp LL O, Set (TW RW T) := fun T => {y | ∃ hT x, y = ν T hT x}
  have hone : IsCrys PD Γ.one.ρ := GlobalTheory.TrivCrys.isCrys_lat_of_trivial Γ.one Γ.one_triv
  obtain ⟨e₀, bo, he₀, hbo⟩ := one_basis Γ hO o
  refine build E a z c ψ π Q hψ ha hinj hunit hπ hQ hz d o hA hE L ?_ ?_ ?_ ?_ ?_ hone e₀ he₀ ?_
  · intro T hT
    have hbas := kappa_basis c (κ T) (hκ T) (cb T hT)
    obtain ⟨A, hAu, hAφ⟩ := GlobalTheory.T.exists_isUnit_matrix_of_pow_smul_span_invert PS.A R.EE (WCb l) RW (TW RW T) ((algebraMap _ R.EE).comp a)
      I.ioE.toRingHom c ψ Q hinj hψ hQu _ (fun i => κ T (cb T hT i)) (fun i => TWmap φR T (κ T (cb T hT i)))
      (fun w hw => (hbas 0).unique hw.symm (by simp))
      (fun i => by
        obtain ⟨k, m, h⟩ := hν1 T hT (b T hT i)
        exact ⟨k, (b T hT).repr m, by rw [hνb, h, ← hνsum, (b T hT).sum_repr]⟩)
      (fun i => by rw [hνb]; exact hν2 T hT _)
    have hm := hmem T _ (fun i => κ T (cb T hT i)) A hAu (fun g hg i => by
      have e : gH g = Hom.id PS := Hom.ext' (RingHom.ext fun x => ha (by
        rw [hγ, hH g hg, map_one]; rfl))
      rw [hνb, hν3, e, FCrys.tr_id]) (fun i => by
        rw [hAφ]
        exact Finset.sum_congr rfl fun i _ => (map_mulLeft _ _).symm)
    choose x hx using hm
    refine ⟨q T hT, x, card_basis T o (cb T hT), by simpa only [hx] using hbas, fun y => ?_⟩
    simp only [hx, ← hνsum]
    constructor
    · rintro ⟨_, m, rfl⟩
      exact ⟨(b T hT).repr m, by rw [(b T hT).sum_repr]⟩
    · rintro ⟨t, rfl⟩
      exact ⟨hT, _, rfl⟩
  · rintro T hT _ ⟨_, x, rfl⟩
    obtain ⟨k, m, h⟩ := hν1 T hT x
    exact ⟨k, hT, m, h⟩
  · rintro T hT _ ⟨_, x, rfl⟩
    obtain ⟨k, t, h⟩ := hν2 T hT x
    exact ⟨k, _, t, _, fun i => ⟨hT, _, hνb T hT i⟩, h⟩
  · rintro T hT g _ ⟨_, x, rfl⟩
    obtain ⟨y, hy⟩ := h4 T hT g x
    refine ⟨_, ⟨hT, y, rfl⟩, ?_⟩
    rw [hν3, ← hνs, ← hy]
    simp only [ν, map_sub]
  · rintro T T' f hT hT' _ ⟨_, x, rfl⟩
    obtain ⟨f', hf, hf'⟩ := exists_restrict (Z := ℤ_[l]) f
    obtain ⟨x', hx'⟩ := full ioH BS (hR T hT) (hR T' hT') f' (fun g t => by rw [← hρ, ← hρ, hf']) x
    refine ⟨hT', x', ?_⟩
    simp only [ν]
    rw [hx']
    exact (kappa_map c (κ T) (hκ T) (κ T') (hκ T') LinearMap.id LinearMap.id (fun _ => rfl) f' _ hf _).symm
  · intro y
    have key : ∀ t : Fin d → PS.A, κ Γ.one (∑ i, inclW l (ainfId F (ioH.f (t i))) ⊗ₜ[ℤ_[l]] bo i) =
        I.ioE (algebraMap _ R.EE (∑ i, o i • a (t i))) • ((1 : RW) ⊗ₜ[O] e₀) := fun t => by
      rw [map_sum, map_sum, map_sum, Finset.sum_smul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hκ, hbo, Algebra.smul_def (o i) (a _), map_mul, ← IsScalarTower.algebraMap_apply, map_mul,
        AlgHom.commutes, hψ₀, TensorProduct.smul_tmul', smul_eq_mul, mul_one, ← Algebra.smul_def,
        TensorProduct.smul_tmul]
    have hr := range_trivial ioH BS (hR _ hone)
      (fun g x => by rw [← hρ]; exact Subtype.ext (Γ.one_triv g x)) bo
    constructor
    · rintro ⟨_, x, rfl⟩
      obtain ⟨t, ht⟩ := (hr _).1 ⟨x, rfl⟩
      exact ⟨_, by rw [← key, ← ht]⟩
    · rintro ⟨α, rfl⟩
      obtain ⟨t, rfl⟩ := hA α
      obtain ⟨x, hx⟩ := (hr _).2 ⟨t, rfl⟩
      exact ⟨hone, x, by rw [← key, hx]⟩

end Generic

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 200000 in

theorem main : GlobalTheory.Published.BhattScholzeCrystallineLattices →
    ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → WachEx AI := by
  intro BS l _ P AI tied K s LL hG Γ R I hW E
  obtain ⟨PS, PW, ev, ioH, gH, a, z, π, Q, ha, hio, -, hγ, hioH, hev, hπ, -, hker, hI, hQ, hz, hloc, -, hS, hA⟩ :=
    GlobalTheory.T.exists_wach_prism_over_integers l P AI K s LL hG Γ R I hW
  obtain ⟨hinj, hunit, -, -⟩ := GlobalTheory.T.wachInclusion_injective_saturated_inter l P AI K s LL hG Γ R I hW
  obtain ⟨d, ⟨o⟩⟩ := exists_basis_OL LL
  have := LL.2
  have := Module.Free.of_basis o
  have := Module.Finite.of_basis o
  have : Nontrivial R.EE := R.EE_inj.nontrivial
  have : Nontrivial (RW LL) := hinj.nontrivial
  have hO : Function.Injective (algebraMap ↥(OL LL) ↥LL.1) := Subtype.val_injective
  change Nonempty (WN E _)
  rw [← hz]
  refine build_prism BS E hO (P.PD_p K) ev ioH gH a z π Q
    (Algebra.TensorProduct.includeRight : WCb l →ₐ[ℤ_[l]] ↥(OL LL) ⊗[ℤ_[l]] WCb l).toRingHom
    (fun x => ?_) ha hinj hunit hγ hioH hev hπ hker hI hQ hloc hS o (hA d o) (coord_tensor o)
    (fun w => isUnit_of_one_tmul w) (fun w => ?_) (fun g w => ?_) (GlobalTheory.T.exists_wittTilt_lattice_tensor_cancel l K LL) (fun T hT => ?_)
    (fun g => P.χQ (g : GQ l) = 1) (fun g hg => resΓ_eq_one Γ hO g ?_)
    (GlobalTheory.T.witt_twist_invariant_basis_change l P AI K s LL hG Γ R I hW E)
  · rw [I.ioE_ext, hio]
    exact Algebra.TensorProduct.map_tmul _ _ _ _
  · exact Algebra.TensorProduct.map_tmul _ _ _ _
  · rw [← locAinf_actWCbHom_eq AI]
    exact Algebra.TensorProduct.map_tmul _ _ _ _
  · obtain ⟨C, j, h⟩ := (BS l K _ _ (isAinf_ainfObj K)).1 P AI ⟨tied⟩ LL T hT
    exact ⟨_, C, j, h, fun _ _ => rfl⟩
  · rw [P.PD_χ, hg, Units.val_one]

end GlobalTheory.WachLattice
