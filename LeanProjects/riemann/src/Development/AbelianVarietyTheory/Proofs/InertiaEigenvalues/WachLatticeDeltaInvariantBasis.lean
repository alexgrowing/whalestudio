import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.UsedLocalConclusion
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NotFullBot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingsCyclotomic
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NBasisLoc
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices

namespace GlobalTheory.NL.InvBasis

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    (W : LocWach PD LL O v n) (T : LocLat G Qp LL O)

theorem γD_smulA (g : W.Gam) (a : LetA O n) (x : W.DD T) :
    W.γD T g (a • x) = W.γA g a • W.γD T g x := by
  have := W.γD_smul T g (algebraMap (LetA O n) W.EE a) x
  rw [algebraMap_smul, W.γE_ext, algebraMap_smul] at this
  exact this

theorem mem_DelF_iff (g : W.Gam) : g ∈ W.DelF ↔ IsOfFinOrder g := by
  rw [W.DelF_def, isOfFinOrder_iff_pow_eq_one]

theorem sum_inv (x : W.DD T) (δ : W.Gam) (hδ : δ ∈ W.DelF) :
    W.γD T δ (∑ d ∈ W.DelF, W.γD T d x) = ∑ d ∈ W.DelF, W.γD T d x := by
  rw [map_sum]
  rw [mem_DelF_iff] at hδ
  refine Finset.sum_bij' (fun d _ => δ * d) (fun d _ => δ⁻¹ * d) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    rw [mem_DelF_iff] at hd ⊢
    exact hδ.mul hd
  · intro d hd
    rw [mem_DelF_iff] at hd ⊢
    exact hδ.inv.mul hd
  · intro d _
    simp
  · intro d _
    simp
  · intro d _
    rw [W.γD_mul]

theorem exists_avg (hc : IsUnit ((W.DelF.card : ℕ) : O)) (x : ↥(W.N T)) :
    ∃ x' y : ↥(W.N T), (x' : W.DD T) ∈ W.NΔ T ∧ x' = x + (letπ : LetA O n) • y := by
  classical
  obtain ⟨c, hc⟩ := hc.exists_left_inv
  choose y hy hy' using fun g => W.N_π T g x x.2
  have hmem : ∀ z ∈ W.N T, c • z ∈ W.N T := fun z hz => by
    rw [← algebraMap_smul (LetA O n) c z]
    exact (W.N T).smul_mem _ hz
  have h1 : c • ∑ d ∈ W.DelF, W.γD T d x ∈ W.N T :=
    hmem _ (Submodule.sum_mem _ fun d _ => W.N_Γ T d x x.2)
  refine ⟨⟨_, h1⟩, ⟨c • ∑ d ∈ W.DelF, y d, hmem _ (Submodule.sum_mem _ fun d _ => hy d)⟩,
    ⟨h1, fun δ hδ => ?_⟩, ?_⟩
  · change W.γD T δ (c • _) = c • _
    rw [map_smul, sum_inv W T _ δ hδ]
  · apply Subtype.ext
    change c • _ = (x : W.DD T) + (letπ : LetA O n) • (c • ∑ d ∈ W.DelF, y d)
    have h2 : ∀ d ∈ W.DelF, W.γD T d x = x + (letπ : LetA O n) • y d := fun d _ => by
      rw [← hy']; abel
    rw [Finset.sum_congr rfl h2, Finset.sum_add_distrib, Finset.sum_const, smul_add,
      ← Finset.smul_sum, ← Nat.cast_smul_eq_nsmul O, smul_smul, hc, one_smul,
      ← algebraMap_smul (LetA O n) c, ← algebraMap_smul (LetA O n) c, smul_comm]

theorem basis_of_congr {M : Type} [AddCommGroup M] [Module (LetA O n) M] {r : ℕ}
    (b : Module.Basis (Fin r) (LetA O n) M) (x y : Fin r → M)
    (h : ∀ j, x j = b j + (letπ : LetA O n) • y j) :
    ∃ b' : Module.Basis (Fin r) (LetA O n) M, ∀ j, b' j = x j := by
  classical
  have hu : IsUnit (b.det x) := by
    rw [Pi.isUnit_iff]
    intro i
    rw [PowerSeries.isUnit_iff_constantCoeff]
    let ψ : LetA O n →+* O := (PowerSeries.constantCoeff (R := O)).comp
      (Pi.evalRingHom (fun _ : ZMod n => PowerSeries O) i)
    have hψ : ψ letπ = 0 := by simp [ψ, letπ]
    change IsUnit (ψ (b.det x))
    rw [Module.Basis.det_apply, RingHom.map_det]
    have : ψ.mapMatrix (b.toMatrix x) = 1 := by
      ext j k
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, Module.Basis.toMatrix_apply, h, map_add,
        map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul, map_add, map_mul, hψ,
        zero_mul, add_zero, b.repr_self, Finsupp.single_apply, Matrix.one_apply]
      by_cases hjk : j = k
      · simp [hjk]
      · simp [hjk, Ne.symm hjk]
    rw [this, Matrix.det_one]
    exact isUnit_one
  obtain ⟨h1, h2⟩ := (b.is_basis_iff_det).mpr hu
  exact ⟨Module.Basis.mk h1 h2.ge, fun j => Module.Basis.mk_apply _ _ _⟩

theorem div_param [IsDomain O] {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O} (hs : 0 < s')
    (h9 : wachRingRelations W e s' π' E) (a c : LetA O n) (ha : InAΔ W a) (hac : a = letπ * c) :
    ∃ a', InAΔ W a' ∧ a = π' * a' := by
  obtain ⟨hπ, hser, ⟨w, hw⟩, -⟩ := h9
  obtain ⟨f, hf, -⟩ := hser a ha
  have h0 : ∀ i, PowerSeries.constantCoeff (π' i) = 0 := fun i => by
    rw [hw]
    simp [letπ, hs.ne']
  have hsub : ∀ i, PowerSeries.HasSubst (π' i) := fun i =>
    PowerSeries.HasSubst.of_constantCoeff_zero' (h0 i)
  have hne : ∀ i, π' i ≠ 0 := fun i => by
    rw [hw]
    refine mul_ne_zero ?_ (pow_ne_zero _ PowerSeries.X_ne_zero)
    exact (Pi.isUnit_iff.mp w.isUnit i).ne_zero
  have hdiv : ∀ i, ∃ g, a i = π' i * g := fun i => by
    have e1 : f i = PowerSeries.X * (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i)) +
        PowerSeries.C (PowerSeries.constantCoeff (f i)) := PowerSeries.eq_X_mul_shift_add_const _
    have e2 : a i = π' i * PowerSeries.subst (π' i) (PowerSeries.mk fun p => PowerSeries.coeff (p + 1) (f i))
        + PowerSeries.C (PowerSeries.constantCoeff (f i)) := by
      rw [hf i]
      conv_lhs => rw [e1]
      rw [← PowerSeries.coe_substAlgHom (hsub i), map_add, map_mul, PowerSeries.substAlgHom_X]
      congr 1
      exact (PowerSeries.substAlgHom (hsub i)).commutes _
    have e3 : PowerSeries.constantCoeff (a i) = 0 := by
      rw [hac]
      simp [letπ]
    have e4 : PowerSeries.constantCoeff (f i) = 0 := by
      rw [e2] at e3
      simpa [h0 i] using e3
    exact ⟨_, by rw [e2, e4, map_zero, add_zero]⟩
  choose g hg using hdiv
  have hag : a = π' * g := funext hg
  refine ⟨g, fun δ hδ => ?_, hag⟩
  have h1 := ha δ hδ
  rw [hag, map_mul, hπ δ hδ] at h1
  funext i
  exact mul_left_cancel₀ (hne i) (congrFun h1 i)

theorem invariant_basis_of_basis [IsDomain O] (hc : IsUnit ((W.DelF.card : ℕ) : O)) {r : ℕ}
    (b₀ : Module.Basis (Fin r) (LetA O n) ↥(W.N T))
    {e s' : ℕ} {π' : LetA O n} {E : ZMod n → Polynomial O} (hs : 0 < s')
    (h9 : wachRingRelations W e s' π' E) : wachModuleOverLetters W T π' := by
  choose x y hx hxy using fun j => exists_avg W T hc (b₀ j)
  obtain ⟨b, hb⟩ := basis_of_congr b₀ x y hxy
  have hbΔ : ∀ j, (b j : W.DD T) ∈ W.NΔ T := fun j => hb j ▸ hx j
  have huniq : ∀ a a' : Fin r → LetA O n,
      ∑ j, a j • (b j : W.DD T) = ∑ j, a' j • (b j : W.DD T) → a = a' := by
    intro a a' h
    apply b.equivFun.symm.injective
    apply Subtype.ext
    simpa [Module.Basis.equivFun_symm_apply] using h
  have hex : ∀ z ∈ W.N T, ∃ a : Fin r → LetA O n, z = ∑ j, a j • (b j : W.DD T) := by
    intro z hz
    refine ⟨b.repr ⟨z, hz⟩, ?_⟩
    have := congrArg Subtype.val (b.sum_repr ⟨z, hz⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  have hact : ∀ (a : Fin r → LetA O n) δ, δ ∈ W.DelF →
      W.γD T δ (∑ j, a j • (b j : W.DD T)) = ∑ j, W.γA δ (a j) • (b j : W.DD T) := by
    intro a δ hδ
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [γD_smulA, (hbΔ j).2 δ hδ]
  have hinv : ∀ z ∈ W.NΔ T, ∃ a : Fin r → LetA O n, (∀ j, InAΔ W (a j)) ∧
      z = ∑ j, a j • (b j : W.DD T) := by
    intro z hz
    obtain ⟨a, ha⟩ := hex z hz.1
    refine ⟨a, fun j δ hδ => ?_, ha⟩
    have h1 := hz.2 δ hδ
    rw [ha, hact a δ hδ] at h1
    exact congrFun (huniq _ _ h1) j
  refine ⟨⟨r, fun j => b j, hbΔ, fun z hz => ?_, hinv⟩, fun z hz => ?_⟩
  · obtain ⟨a, ha⟩ := hex z hz
    exact ⟨a, ha, fun a' ha' => huniq _ _ (ha'.symm.trans ha)⟩
  · have hmem : W.γ T z - z ∈ W.NΔ T := by
      refine (W.NΔ T).sub_mem ⟨W.N_Γ T _ z hz.1, fun δ hδ => ?_⟩ hz
      change W.γD T δ (W.γD T W.gam z) = W.γD T W.gam z
      rw [← W.γD_mul, mul_comm, W.γD_mul, hz.2 δ hδ]
    obtain ⟨a, ha, ha'⟩ := hinv _ hmem
    obtain ⟨u, hu, hu'⟩ := W.N_π T W.gam z hz.1
    obtain ⟨c, hc'⟩ := hex u hu
    have hac : a = fun j => letπ * c j := by
      apply huniq
      rw [← ha']
      change W.γD T W.gam z - z = _
      rw [hu', hc', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => smul_smul _ _ _
    choose a' h1 h2 using fun j => div_param W hs h9 (a j) (c j) (ha j) (congrFun hac j)
    refine ⟨∑ j, a' j • (b j : W.DD T),
      ⟨Submodule.sum_mem _ fun j _ => (W.N T).smul_mem _ (b j).2, fun δ hδ => ?_⟩, ?_⟩
    · rw [hact a' δ hδ]
      exact Finset.sum_congr rfl fun j _ => by rw [h1 j δ hδ]
    · rw [ha', Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [h2 j, smul_smul]

theorem not_dvd_card (l : ℕ) [Fact l.Prime] (h : ∀ g : W.Gam, g ^ l = 1 → g = 1) :
    ¬ l ∣ W.DelF.card := by
  classical
  intro hd
  have hcard : Nat.card (CommGroup.torsion W.Gam) = W.DelF.card := by
    rw [← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun g => (mem_DelF_iff W g).symm)
  haveI : Finite (CommGroup.torsion W.Gam) :=
    Finite.of_equiv _ (Equiv.subtypeEquivRight fun g => (mem_DelF_iff W g) :
      {g // g ∈ W.DelF} ≃ CommGroup.torsion W.Gam)
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := CommGroup.torsion W.Gam) l (hcard ▸ hd)
  have h1 : g = 1 := Subtype.ext (h g (by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this))
  rw [h1, orderOf_one] at hg
  exact (Fact.out : l.Prime).one_lt.ne hg

end Generic

theorem padic_root_one {l : ℕ} [Fact l.Prime] (hl : l ≠ 2) (x : ℤ_[l]) (hx : x ^ l = 1) : x = 1 := by
  by_contra hne
  have hp : l.Prime := Fact.out
  have h1 : PadicInt.toZMod (x - 1) = 0 := by
    have := congrArg (PadicInt.toZMod (p := l)) hx
    rw [map_pow, ZMod.pow_card] at this
    rw [map_sub, this, sub_self]
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p,
    Ideal.mem_span_singleton] at h1
  obtain ⟨b, hb⟩ := h1
  have hx' : x = 1 + l * b := by rw [← hb]; ring
  have h2 := odd_sq_dvd_geom_sum₂_sub (1 : ℤ_[l]) b (hp.odd_of_ne_two hl)
  have h3 : ∑ i ∈ Finset.range l, x ^ i = 0 := by
    have := geom_sum_mul x l
    rw [hx, sub_self] at this
    exact (mul_eq_zero.mp this).resolve_right (sub_ne_zero.mpr hne)
  simp only [one_pow, mul_one, ← hx', h3, zero_sub, dvd_neg] at h2
  obtain ⟨c, hc⟩ := h2
  have hl0 : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have h4 : (l : ℤ_[l]) * c = 1 := mul_left_cancel₀ hl0 (by linear_combination -hc)
  exact PadicInt.prime_p.not_isUnit (IsUnit.of_mul_eq_one _ h4)

set_option maxHeartbeats 1000000 in

theorem invariant_basis : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; let _E := ((F l).E K s LL h).tie; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → W.s = 1 → l ≠ 2 → ∀ (e s' : ℕ) (π' : AA K LL) (E' : Let K → Polynomial ↥(OL LL)), 0 < s' → wachRingRelations W e s' π' E' → wachModuleOverLetters W T π' := by
  intro D HW F l _ K s LL h W _E T hT _ hl e s' π' E' hs h9
  obtain ⟨b₀⟩ := N_basis D HW F l K s LL h T hT
  obtain ⟨χ, hχ, -⟩ := GlobalTheory.NL.CycRing.rings_cyclotomic D HW l K s LL h
  have hnd : ¬ l ∣ W.DelF.card := by
    refine not_dvd_card W l fun g hg => W.χΓ_inj ?_
    have h1 : (χ g : ℤ_[l]) = 1 := padic_root_one hl _ (by
      rw [← Units.val_pow_eq_pow_val, ← map_pow, hg, map_one, Units.val_one])
    apply Units.ext
    rw [map_one, Units.val_one, ← hχ g, h1, map_one]
  have hu : IsUnit ((W.DelF.card : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hnd
  have hc : IsUnit ((W.DelF.card : ℕ) : ↥(OL LL)) := by
    simpa using hu.map (algebraMap ℤ_[l] ↥(OL LL))
  exact invariant_basis_of_basis W T hc b₀ hs h9

end GlobalTheory.NL.InvBasis
