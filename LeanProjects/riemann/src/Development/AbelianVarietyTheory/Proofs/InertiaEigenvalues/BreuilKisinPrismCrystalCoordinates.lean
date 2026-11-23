import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKCoord

theorem semiBC_injective {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) [Module.Projective A M]
    (hf : Function.Injective f) : Function.Injective u := by
  refine (injective_iff_map_eq_zero u).2 fun x hx => ?_
  by_contra h0
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_ne_zero A h0
  obtain ⟨w, hw, -⟩ := h B (f.toSemilinearMap.comp φ)
  have h1 := hw x
  rw [hx, map_zero] at h1
  exact hφ (hf (h1.symm.trans (map_zero f).symm))

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]

theorem ev_eis_ne_zero (ϖ : PiSys l e) : ϖ.ev a (eis l a e) ≠ 0 := fun h =>
  (ϖ.isUnit_inclW_ev_eis a).ne_zero (by rw [h, map_zero])

theorem ev_injective (ϖ : PiSys l e) : Function.Injective (ϖ.ev a) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  have key : ∀ n : ℕ, ∃ y, x = eis l a e ^ n * y ∧ ϖ.ev a y = 0 := fun n => by
    induction n with
    | zero => exact ⟨x, by simp, hx⟩
    | succ n ih =>
      obtain ⟨y, h1, h2⟩ := ih
      obtain ⟨z, rfl⟩ := (ϖ.theta_ev_eq_zero_iff a y).1 (by rw [h2, map_zero])
      rw [map_mul] at h2
      exact ⟨z, by rw [h1]; ring, (mul_eq_zero.1 h2).resolve_left (ev_eis_ne_zero ϖ)⟩
  refine (complete_eis l a e).haus x fun n => ?_
  obtain ⟨y, h1, -⟩ := key n
  rw [SModEq.zero, h1]
  exact Submodule.smul_mem_smul
    (Ideal.pow_mem_pow (Ideal.mem_sup_right (Ideal.mem_span_singleton_self _)) n) Submodule.mem_top

section Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [NormedField K] [Algebra O K] [NormedAlgebra ℚ_[l] K]
  {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O)

theorem kappa_smul (w : WCb l) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (w • y) = ((1 : O) ⊗ₜ[ℤ_[l]] w : OW l O) • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => rw [smul_zero, map_zero, smul_zero]
  | tmul v x =>
    rw [smul_tmul', kappa_tmul, kappa_tmul, smul_tmul', smul_eq_mul, smul_eq_mul,
      Algebra.TensorProduct.tmul_mul_tmul, one_mul]
  | add x y hx hy => rw [smul_add, map_add, map_add, smul_add, hx, hy]

theorem kappa_frob :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T (TensorProduct.map (frobW l).toLinearMap LinearMap.id y) =
      TWmap (frobOW l O) T (kappa T y) := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul v x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

def mulZ (o : O) :
    letI := zlLat T
    ↥T.L.T →ₗ[ℤ_[l]] ↥T.L.T :=
  letI := zlLat T
  { toFun := fun x => o • x
    map_add' := smul_add o
    map_smul' := fun c x => smul_comm o (algebraMap ℤ_[l] O c) x }

theorem kappa_mulZ (o : O) :
    letI := zlLat T
    ∀ y : WCb l ⊗[ℤ_[l]] ↥T.L.T, kappa T ((mulZ T o).lTensor (WCb l) y) = o • kappa T y := by
  letI := zlLat T
  intro y
  induction y using TensorProduct.induction_on with
  | zero => simp only [map_zero, smul_zero]
  | tmul v x => exact tmul_smul o ((1 : O) ⊗ₜ[ℤ_[l]] v : OW l O) x
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]

end Kappa

variable {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  {t : Wq l a →ₐ[ℤ_[l]] O} {ϖ : PiSys l e} {ι : Type} [Fintype ι] [DecidableEq ι]
  {G : Type} [Group G] [TopologicalSpace G] {P : PhiMod O K l e a ι} {T : LocLat G ℚ_[l] K O}

theorem exists_coord (I : Ident t ϖ P T) {N : Type} [AddCommGroup N] (J : N →+ TW (OW l O) T)
    (h : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩)) :
    ∃ (c : N →+ Vec K a ι) (hc : ∀ x, c x ∈ P.M),
      (∀ x, J x = I.j (toW t ϖ P ⟨c x, mem_ME_of_mem_M (hc x)⟩)) ∧ ∀ m ∈ P.M, ∃ x, c x = m := by
  choose c hc hJ using fun x => (h (J x)).1 ⟨x, rfl⟩
  refine ⟨AddMonoidHom.mk' c fun x y => ?_, hc, hJ, fun m hm => ?_⟩
  · have h1 := map_add J x y
    rw [hJ, hJ, hJ, ← map_add, ← map_add] at h1
    exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h1))
  · obtain ⟨x, hx⟩ := (h _).2 ⟨m, hm, rfl⟩
    rw [hJ] at hx
    exact ⟨x, (congrArg Subtype.val (toW_injective t ϖ P (I.j.injective hx))).symm⟩

theorem eq_of_j_eq (I : Ident t ϖ P T) (f : ZMod a → A O K) (v w : ME P)
    (h : I.j (toW t ϖ P w) = inclO l O (ϖ.iTot t K f) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (f τ : K⟦X⟧) * v.1 τ i := by
  have hm : (fun τ i => (f τ : K⟦X⟧) * v.1 τ i) ∈ ME P :=
    mem_tot.2 fun τ i => mul_mem (le_away _ _ (f τ).2) (mem_tot.1 v.2 τ i)
  have h1 := toW_smul t ϖ P (fun τ => ⟨f τ, le_away _ _ (f τ).2⟩) v ⟨_, hm⟩ fun τ => rfl
  rw [← map_smul, ← ϖ.iW_of_mem t K, ← h1] at h
  exact congrArg Subtype.val (toW_injective t ϖ P (I.j.injective h))

variable (K t ϖ) in

theorem inclO_iTot_E_pow (k : ℕ) : inclO l O (ϖ.iTot t K ((fun _ => EIn l e _) ^ k)) =
    (1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) := by
  rw [map_pow, map_pow, PiSys.iTot_E, inclO_tmul, Algebra.TensorProduct.tmul_pow, one_pow]

theorem eq_of_j_eq_const (I : Ident t ϖ P T) (o : O) (v w : ME P)
    (h : I.j (toW t ϖ P w) = o • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => PowerSeries.C (algebraMap O K o) * v.1 τ i := by
  refine (eq_of_j_eq I (algebraMap O _ o) v w ?_).trans
    (funext fun τ => funext fun i => congrArg (· * v.1 τ i) (algebraMap_eq_C o))
  rwa [AlgHom.commutes, AlgHom.commutes, algebraMap_smul]

theorem eq_of_j_eq_toAc (I : Ident t ϖ P T) (f : (Wq l a)⟦X⟧) (v w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] inclW l (ϖ.ev a f) : OW l O) • I.j (toW t ϖ P v)) :
    w.1 = fun τ i => (toAc t K f τ : K⟦X⟧) * v.1 τ i := by
  refine eq_of_j_eq I (toAc t K f) v w ?_
  rwa [PiSys.iTot_toAc, inclO_tmul]

theorem eq_of_j_eq_phi (I : Ident t ϖ P T) (k : ℕ) {v : Vec K a ι} (hv : v ∈ P.M) (w : ME P)
    (h : I.j (toW t ϖ P w) = ((1 : O) ⊗ₜ[ℤ_[l]] (inclW l (ϖ.ev a (eis l a e)) ^ k) : OW l O) •
      TWmap (frobOW l O) T (I.j (toW t ϖ P ⟨v, mem_ME_of_mem_M hv⟩))) :
    w.1 = fun τ i => E K l e ^ k * P.phi v τ i := by
  refine eq_of_j_eq I ((fun _ => EIn l e _) ^ k) ⟨_, mem_ME_of_mem_L (P.phi_mem_L hv)⟩ w ?_
  rwa [toW_phi t ϖ P hv, I.j_φ, inclO_iTot_E_pow]

theorem j_frob {EE : FCrys l ↥(OL (ϖ.field a))} {T : Type} [AddCommGroup T] [Module ℤ_[l] T]
    {ρ : ↥(GK (ϖ.field a)) → (T →ₗ[ℤ_[l]] T)}
    {j : EE.M (ainfObj (ϖ.field a)) →ₛₗ[(inclW l).comp (ainfId (ϖ.field a)).toRingHom] (WCb l ⊗[ℤ_[l]] T)}
    (H : Realises (ϖ.field a) EE (ainfObj _) (ainfId _) T ρ j) (x m : EE.M (ϖ.prism a)) (k : ℕ)
    (h : IsFrac (A := (ϖ.prism a).A) (eis l a e)
      (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k) :
    j (EE.tr (ϖ.toAinf a) m) = inclW l (ϖ.ev a (eis l a e)) ^ k •
      TensorProduct.map (frobW l).toLinearMap LinearMap.id (j (EE.tr (ϖ.toAinf a) x)) := by
  let d : ↥(ainfObj (ϖ.field a)).I := ⟨ϖ.ev a (eis l a e), ϖ.theta_ev_eis a⟩
  obtain ⟨n, i, hn⟩ := exists_isFrac (d : (ainfObj (ϖ.field a)).A) (EE.Φ _ d (EE.tr (ϖ.toAinf a) x))
  obtain ⟨r, hr⟩ := EE.Φ_nat (ϖ.toAinf a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ d x m k n i h hn
  have h1 := H.j_φ d (ev_eis_ne_zero ϖ) _ n i hn
  have : IsDomain (ainfObj (ϖ.field a)).A := (ainfId (ϖ.field a)).toMulEquiv.isDomain
  have := EE.proj (ainfObj (ϖ.field a))
  have h0 : (d : (ainfObj (ϖ.field a)).A) ≠ 0 := ev_eis_ne_zero ϖ
  have h2 : (d : (ainfObj (ϖ.field a)).A) ^ i • EE.tr (ϖ.toAinf a) m = (d : (ainfObj (ϖ.field a)).A) ^ k • n :=
    sub_eq_zero.1 ((smul_eq_zero.1 hr).resolve_left (pow_ne_zero _ (mul_ne_zero h0 h0)))
  exact (smul_eq_of_isUnit j (ϖ.isUnit_inclW_ev_eis a) h2 h1).symm

theorem main : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : GlobalTheory.BKReal.Lat a O K ϖ) (I : Ident t ϖ P T), GlobalTheory.Published.BhattScholzeCrystallineLattices → IsBK I → ∃ (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c ∧ (∀ x, c x ∈ P.M) ∧ (∀ m ∈ P.M, ∃ x, c x = m) ∧ (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) ∧ (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) ∧ (∀ (x m : EE.M (ϖ.prism a)) (k : ℕ), IsFrac (A := (ϖ.prism a).A) (eis l a e) (EE.Φ (ϖ.prism a) ⟨eis l a e, Ideal.mem_span_singleton_self _⟩ x) m k → c m = fun τ i => E K l e ^ k * P.phi (c x) τ i) := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I hBS hBK
  letI := zlLat T
  obtain ⟨EE, j, H, him⟩ := hBK
  have h0 : ∃ J : EE.M (ϖ.prism a) →+ TW (OW l O) T, ∀ x, J x = kappa T (j (EE.tr (ϖ.toAinf a) x)) :=
    ⟨(kappa T).comp (j.toAddMonoidHom.comp (EE.tr (ϖ.toAinf a)).toAddMonoidHom), fun _ => rfl⟩
  obtain ⟨J, hJ⟩ := h0
  have h1 : ∀ y : TW (OW l O) T, (∃ x, y = J x) ↔
      ∃ (m : Vec K a ι) (hm : m ∈ P.M), y = I.j (toW t ϖ P ⟨m, mem_ME_of_mem_M hm⟩) := fun y => by
    simp only [hJ]
    exact him y
  have h2 := exists_coord I J h1
  obtain ⟨c, hc, hcJ, hs⟩ := h2
  have hi : Function.Injective J := by
    have := EE.proj (ainfObj (ϖ.field a))
    have := EE.proj (ϖ.prism a)
    intro x y h
    rw [hJ, hJ] at h
    exact semiBC_injective (EE.tr_bc (ϖ.toAinf a)) (ev_injective ϖ)
      (semiBC_injective H.bc inclW_injective ((kappa_bijective T).1 h))
  refine ⟨EE, c, fun x y hxy => hi ?_, hc, hs, fun w x => ?_, fun o => ?_, fun x m k h => ?_⟩
  · rw [hcJ, hcJ]
    simp only [hxy]
  · refine eq_of_j_eq_toAc I w ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := congrArg j ((EE.tr (ϖ.toAinf a)).map_smulₛₗ w x)
    have h4 := congrArg (kappa T) (h3.trans (j.map_smulₛₗ _ _))
    have h5 := h4.trans (kappa_smul T _ _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h5
  · have h3 := (hBS l _ _ _ (isAinf_ainfObj (ϖ.field a))).2 _ _ _ _ EE EE j j H H (mulZ T o)
      fun g x => ((T.actT g).map_smul o x).symm
    obtain ⟨U, hU, -⟩ := h3
    refine ⟨U, fun x => eq_of_j_eq_const I o ⟨_, mem_ME_of_mem_M (hc x)⟩ ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_⟩
    have h3 := (congrArg j (U.u_tr (ϖ.toAinf a) x)).symm.trans (hU _)
    have h4 := (congrArg (kappa T) h3).trans (kappa_mulZ T o _)
    rewrite [← hcJ, ← hcJ, hJ, hJ]
    exact h4
  · refine eq_of_j_eq_phi I k (hc x) ⟨_, mem_ME_of_mem_M (hc _)⟩ ?_
    have h3 := (congrArg (kappa T) (j_frob H x m k h)).trans (kappa_smul T _ _)
    have h4 := kappa_frob T (j (EE.tr (ϖ.toAinf a) x))
    rewrite [← hcJ, ← hcJ, hJ, hJ, ← h4]
    exact h3

end GlobalTheory.BKCoord
