import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsAdapted
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RelatedPairsOrbitalTermEq
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ProjSumSumEmbeddingsEqTrace
import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.PDifferentLatIndex
import Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenLatticesDifferentStatementHoldsStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.TorPart

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements
open GroundTheory.Heights₂.Heights.LowerBoundFree

variable {E L V : Type} [Field E] [NumberField E] [Field L] [AddCommGroup V] [Module L V]

theorem rho_eigProj (ρ : 𝓞 E →+* Module.End L V) (t : E →+* L) (o : 𝓞 E) (y : V) :
    ρ o (HT.eigProj ρ t y) = t (o : E) • HT.eigProj ρ t y := by
  have := congrArg (fun T : Module.End L V => T y) (HT.ProjEig.rho_mul_eigProj ρ t o)
  simpa using this

variable [Fintype (E →+* L)]

def theta (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) :
    ((E →+* L) → Fin r → L) →ₗ[L] V where
  toFun z := ∑ t, ∑ a, z t a • HT.eigProj ρ t (v a)
  map_add' z z' := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c z := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply]

theorem theta_apply (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (z : (E →+* L) → Fin r → L) :
    theta ρ v z = ∑ t, ∑ a, z t a • HT.eigProj ρ t (v a) := rfl

def emb {r : ℕ} : (Fin r → E) →+ ((E →+* L) → Fin r → L) where
  toFun x t a := t (x a)
  map_zero' := by ext; simp
  map_add' x y := by ext; simp

theorem emb_apply {r : ℕ} (x : Fin r → E) (t : E →+* L) (a : Fin r) : emb x t a = t (x a) := rfl

def psi (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) : (Fin r → E) →+ V :=
  (theta ρ v).toAddMonoidHom.comp emb

theorem psi_apply (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (x : Fin r → E) :
    psi ρ v x = ∑ t, ∑ a, t (x a) • HT.eigProj ρ t (v a) := rfl

theorem psi_smul (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (o : 𝓞 E) (x : Fin r → E) :
    psi ρ v (o • x) = ρ o (psi ρ v x) := by
  simp only [psi_apply, map_sum, map_smul, rho_eigProj, Pi.smul_apply, smul_smul]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Algebra.smul_def, map_mul, mul_comm]

variable [CharZero L]

theorem rho_eq_sum (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) (o : 𝓞 E) (y : V) :
    ρ o y = ∑ t : E →+* L, t (o : E) • HT.eigProj ρ t y := by
  have h := congrArg (fun T : Module.End L V => T (ρ o y)) (HT.sum_eigProj_eq_one L V E ρ hcard)
  simp only [LinearMap.sum_apply, Module.End.one_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← rho_eigProj, ← Module.End.mul_apply, ← Module.End.mul_apply,
    (HT.ProjEig.eigProj_spec L V E ρ t).2.2.2]

theorem psi_int (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (c : Fin r → 𝓞 E) :
    psi ρ v (fun a => (c a : E)) = ∑ a, ρ (c a) (v a) := by
  simp only [psi_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => (rho_eq_sum hcard ρ _ _).symm

omit [Fintype (E →+* L)] [CharZero L] in
theorem mem_oSpan_iff (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (y : V) :
    y ∈ oSpan ρ v ↔ ∃ c : Fin r → 𝓞 E, y = ∑ a, ρ (c a) (v a) := by
  classical
  constructor
  · intro hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨o, i, rfl⟩ := hy
      refine ⟨Pi.single i o, ?_⟩
      rw [Finset.sum_eq_single i]
      · simp
      · intro b _ hb
        simp [Pi.single_eq_of_ne hb]
      · simp
    | zero => exact ⟨0, by simp⟩
    | add y z _ _ hy hz =>
      obtain ⟨c, rfl⟩ := hy
      obtain ⟨d, rfl⟩ := hz
      exact ⟨c + d, by simp [Finset.sum_add_distrib]⟩
    | neg y _ hy =>
      obtain ⟨c, rfl⟩ := hy
      exact ⟨-c, by simp⟩
  · rintro ⟨c, rfl⟩
    exact sum_mem fun a _ => AddSubgroup.subset_closure ⟨c a, a, rfl⟩

theorem psi_injective (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V)
    (hind : ∀ a : Fin r → 𝓞 E, ∑ i, ρ (a i) (v i) = 0 → a = 0) : Function.Injective (psi ρ v) := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors (𝓞 E)) x
  choose c hc using hb
  have hcx : (fun a => (c a : E)) = (b : 𝓞 E) • x := by
    funext a
    exact hc a
  have h1 : psi ρ v (fun a => (c a : E)) = 0 := by
    rw [hcx, psi_smul, hx, map_zero]
  rw [psi_int hcard] at h1
  have h2 := hind c h1
  have hb0 : ((b : 𝓞 E) : E) ≠ 0 := by
    have := nonZeroDivisors.ne_zero b.2
    exact_mod_cast this
  funext a
  have h3 := hc a
  rw [h2] at h3
  simp only [Pi.zero_apply, map_zero] at h3
  rw [Algebra.smul_def] at h3
  exact (mul_eq_zero.1 h3.symm).resolve_left hb0

theorem exists_psi (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    {y : V} (hy : y ∈ I) : ∃ x, psi ρ v x = y := by
  set m := (oSpan ρ v).relIndex I with hm
  have hm0 : m ≠ 0 := hv.2.2
  have h1 : m • y ∈ oSpan ρ v := by
    have h := AddSubgroup.nsmul_index_mem ((oSpan ρ v).addSubgroupOf I) ⟨y, hy⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    exact h
  obtain ⟨c, hc⟩ := (mem_oSpan_iff ρ v _).1 h1
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm0
  have hmL : (m : L) ≠ 0 := by exact_mod_cast hm0
  refine ⟨fun a => (m : E)⁻¹ * c a, ?_⟩
  have h2 : m • (fun a => (m : E)⁻¹ * c a) = fun a => (c a : E) := by
    funext a
    simp [nsmul_eq_mul, hmE]
  have h3 : m • psi ρ v (fun a => (m : E)⁻¹ * c a) = m • y := by
    rw [← map_nsmul, h2, psi_int hcard, hc]
  rw [← Nat.cast_smul_eq_nsmul L, ← Nat.cast_smul_eq_nsmul L] at h3
  exact smul_right_injective V hmL h3

def lat (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (I : AddSubgroup V)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) : Submodule (𝓞 E) (Fin r → E) where
  carrier := {x | psi ρ v x ∈ I}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_setOf_eq, map_add] at *
    exact I.add_mem hx hy
  zero_mem' := by simp [I.zero_mem]
  smul_mem' c x hx := by
    simp only [Set.mem_setOf_eq, psi_smul] at *
    exact hst c _ hx

omit [CharZero L] in
theorem mem_lat {ρ : 𝓞 E →+* Module.End L V} {r : ℕ} {v : Fin r → V} {I : AddSubgroup V}
    {hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I} {x : Fin r → E} : x ∈ lat ρ v I hst ↔ psi ρ v x ∈ I := Iff.rfl

omit [Fintype (E →+* L)] [CharZero L] [NumberField E] in
theorem sum_smul_single {r : ℕ} (c : Fin r → 𝓞 E) :
    ∑ a, c a • (Pi.single a 1 : Fin r → E) = fun b => (c b : E) := by
  funext b
  simp only [Finset.sum_apply, Pi.smul_apply]
  rw [Finset.sum_eq_single b]
  · simp [Algebra.smul_def]
  · intro a _ hab
    simp [Pi.single_eq_of_ne hab.symm]
  · simp

theorem psi_single (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (a : Fin r) :
    psi ρ v (Pi.single a 1) = v a := by
  classical
  have h := psi_int hcard ρ v (Pi.single a 1)
  have e : (fun b => (((Pi.single a 1 : Fin r → 𝓞 E) b : 𝓞 E) : E)) = Pi.single a 1 := by
    funext b
    by_cases hb : b = a
    · subst hb
      simp
    · simp [Pi.single_eq_of_ne hb]
  rw [e] at h
  rw [h, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

theorem map_psi_lat (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) : (lat ρ v I hst).toAddSubgroup.map (psi ρ v) = I := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := exists_psi hcard ρ hv hy
    exact ⟨x, hy, rfl⟩

theorem map_psi_span (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) :
    (Submodule.span (𝓞 E) (Set.range fun a : Fin r => (Pi.single a 1 : Fin r → E))).toAddSubgroup.map
      (psi ρ v) = oSpan ρ v := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).1 hx
    rw [sum_smul_single]
    change psi ρ v (fun b => (c b : E)) ∈ _
    rw [psi_int hcard]
    exact (mem_oSpan_iff ρ v _).2 ⟨c, rfl⟩
  · intro hy
    obtain ⟨c, rfl⟩ := (mem_oSpan_iff ρ v _).1 hy
    refine ⟨fun b => (c b : E), ?_, psi_int hcard ρ v c⟩
    exact (Submodule.mem_span_range_iff_exists_fun (𝓞 E)).2 ⟨c, sum_smul_single c⟩

theorem isNzFamily_lat (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hr : 1 ≤ r)
    (hv : IsOFamily ρ I v) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) :
    IsNzFamily (lat ρ v I hst) r (fun a => Pi.single a 1) ∧
      familyIndex (lat ρ v I hst) (fun a => Pi.single a 1) = (oSpan ρ v).relIndex I := by
  have hidx : familyIndex (lat ρ v I hst) (fun a => Pi.single a 1) = (oSpan ρ v).relIndex I := by
    rw [familyIndex, ← AddSubgroup.relIndex_map_map_of_injective _ _ (psi_injective hcard ρ v hv.2.1),
      map_psi_span hcard, map_psi_lat hcard ρ hv]
  refine ⟨⟨hr, fun a => ?_, ?_, ?_⟩, hidx⟩
  · rw [mem_lat, psi_single hcard]
    exact hv.1 a
  · rw [Fintype.linearIndependent_iff]
    intro c hc a
    rw [sum_smul_single] at hc
    have := congrFun hc a
    simpa using this
  · have h : familyIndex (lat ρ v I hst) (fun a => Pi.single a 1) ≠ 0 := by
      rw [hidx]
      exact hv.2.2
    exact h

omit [Fintype (E →+* L)] [CharZero L] in

theorem sum_dual_mul [DecidableEq (E →+* L)] (t u : E →+* L) :
    ∑ k, t (HT.dualInt E k) * u ((RingOfIntegers.basis E k : 𝓞 E) : E) = if t = u then 1 else 0 := by
  let ρ' : 𝓞 E →+* Module.End L L :=
    (algebraMap L (Module.End L L)).comp (u.comp (algebraMap (𝓞 E) E))
  have hρ : ∀ (o : 𝓞 E) (y : L), ρ' o y = u (o : E) * y := fun o y => by
    simp [ρ', Module.algebraMap_end_apply]
  have h1 : (1 : L) ∈ HT.eigSp ρ' u := by
    rw [HT.ProjEig.mem_eigSp_iff_apply]
    intro a
    simp [hρ]
  have h2 : HT.eigProj ρ' t 1 =
      ∑ k, t (HT.dualInt E k) * u ((RingOfIntegers.basis E k : 𝓞 E) : E) := by
    simp [HT.eigProj, LinearMap.sum_apply, hρ]
  rw [← h2]
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem h1
  · exact HT.LatBasic.eigProj_of_ne h h1

omit [NumberField E] [Fintype (E →+* L)] [CharZero L] in
theorem exists_linearMap_of_independent {W : Type} [AddCommGroup W] [Module L W] {n : ℕ} {e : Fin n → V}
    (he : LinearIndependent L e) (g : Fin n → W) : ∃ G : V →ₗ[L] W, ∀ j, G (e j) = g j := by
  let b := Module.Basis.span he
  obtain ⟨G, hG⟩ := LinearMap.exists_extend (b.constr L g)
  refine ⟨G, fun j => ?_⟩
  have h1 : (b j : V) = e j := congrArg Subtype.val (Module.Basis.span_apply he j)
  rw [← h1]
  have h2 := LinearMap.congr_fun hG (b j)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h2
  rw [h2, Module.Basis.constr_basis]

theorem theta_injective (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I)
    (hI : ∃ (n : ℕ) (e : Fin n → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I) :
    Function.Injective (theta ρ v) := by
  classical
  obtain ⟨n, e, hli, hcl⟩ := hI
  have hinj := psi_injective hcard ρ v hv.2.1
  have he : ∀ j, e j ∈ I := fun j => hcl ▸ AddSubgroup.subset_closure ⟨j, rfl⟩
  choose x hx using fun j => exists_psi hcard ρ hv (he j)
  obtain ⟨G, hG⟩ := exists_linearMap_of_independent hli (fun j => (emb (x j) : (E →+* L) → Fin r → L))
  have hGI : ∀ y ∈ I, ∀ x', psi ρ v x' = y → G y = emb x' := by
    intro y hy
    rw [← hcl] at hy
    induction hy using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, rfl⟩ := hy
      intro x' h
      rw [hinj (h.trans (hx j).symm), hG]
    | zero =>
      intro x' h
      rw [hinj (h.trans (map_zero _).symm)]
      simp
    | add y z hy hz ihy ihz =>
      intro x' h
      obtain ⟨xy, hxy⟩ := exists_psi hcard ρ hv (hcl ▸ hy)
      obtain ⟨xz, hxz⟩ := exists_psi hcard ρ hv (hcl ▸ hz)
      have : x' = xy + xz := hinj (by rw [h, map_add, hxy, hxz])
      rw [map_add, ihy xy hxy, ihz xz hxz, this, map_add]
    | neg y hy ih =>
      intro x' h
      obtain ⟨xy, hxy⟩ := exists_psi hcard ρ hv (hcl ▸ hy)
      have : x' = -xy := hinj (by rw [h, map_neg, hxy])
      rw [map_neg, ih xy hxy, this, map_neg]
  have hGP : ∀ (t : E →+* L) (a : Fin r),
      G (HT.eigProj ρ t (v a)) = Pi.single t (Pi.single a 1) := by
    intro t a
    have h1 : ∀ k, G (ρ (RingOfIntegers.basis E k) (v a)) =
        emb ((RingOfIntegers.basis E k : 𝓞 E) • (Pi.single a 1 : Fin r → E)) := by
      intro k
      refine hGI _ (hst _ _ (hv.1 a)) _ ?_
      rw [psi_smul, psi_single hcard]
    simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, h1]
    funext u b
    simp only [Finset.sum_apply, Pi.smul_apply, emb_apply, smul_eq_mul]
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same, Algebra.smul_def, mul_one]
      have := sum_dual_mul t u
      by_cases htu : u = t
      · subst htu
        simpa using this
      · rw [if_neg (Ne.symm htu)] at this
        rw [Pi.single_eq_of_ne htu]
        simpa using this
    · have h0 : (Pi.single a 1 : Fin r → E) b = 0 := Pi.single_eq_of_ne hb 1
      simp only [h0, smul_zero, map_zero, mul_zero, Finset.sum_const_zero]
      by_cases htu : u = t
      · subst htu
        simp [Pi.single_eq_of_ne hb]
      · simp [Pi.single_eq_of_ne htu]
  have hleft : Function.LeftInverse G (theta ρ v) := by
    intro z
    simp only [theta_apply, map_sum, map_smul, hGP]
    funext u b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [Finset.sum_eq_single u, Finset.sum_eq_single b]
    · simp
    · intro a _ hab
      simp [Pi.single_eq_of_ne hab.symm]
    · simp
    · intro t _ htu
      simp [Pi.single_eq_of_ne htu.symm]
    · simp
  exact hleft.injective

section Index

variable [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

def thetaO (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) :
    ((E →+* L) → Fin r → L) →ₗ[𝓞 L] V := (theta ρ v).restrictScalars (𝓞 L)

theorem thetaO_apply (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V)
    (z : (E →+* L) → Fin r → L) : thetaO ρ v z = theta ρ v z := rfl

theorem map_baseChangeLat (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I) [NumberField L] :
    (baseChangeLat L (lat ρ v I hst)).map (thetaO ρ v) = Submodule.span (𝓞 L) (I : Set V) := by
  rw [baseChangeLat, Submodule.map_span, ← Set.image_comp]
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hy
    obtain ⟨x, rfl⟩ := exists_psi hcard ρ hv hy
    exact ⟨x, hy, rfl⟩

open Classical in
omit [Fintype (E →+* L)] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
theorem eigProj_eigProj (ρ : 𝓞 E →+* Module.End L V) {t u : E →+* L} (y : V) :
    HT.eigProj ρ t (HT.eigProj ρ u y) = if u = t then HT.eigProj ρ u y else 0 := by
  split_ifs with h
  · subst h
    exact HT.LatBasic.eigProj_of_mem (HT.LatBasic.eigProj_mem ρ u y)
  · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) (HT.LatBasic.eigProj_mem ρ u y)

open Classical in

def phi (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (t : E →+* L) :
    (Fin r → L) →ₗ[𝓞 L] V :=
  (thetaO ρ v).comp (LinearMap.single (𝓞 L) (fun _ : E →+* L => Fin r → L) t)

theorem phi_apply (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (t : E →+* L)
    (w : Fin r → L) : phi ρ v t w = ∑ a, w a • HT.eigProj ρ t (v a) := by
  classical
  simp only [phi, LinearMap.comp_apply, thetaO_apply, theta_apply, LinearMap.coe_single]
  rw [Finset.sum_eq_single t]
  · simp
  · intro u _ hu
    simp [Pi.single_eq_of_ne hu]
  · simp

theorem map_eigenLat [NumberField L] (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I)
    (hI : ∃ (n : ℕ) (e : Fin n → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I)
    (t : E →+* L) :
    (eigenLat (lat ρ v I hst) t).map (phi ρ v t) =
      Submodule.span (𝓞 L) (I : Set V) ⊓ (HT.eigSp ρ t).restrictScalars (𝓞 L) := by
  classical
  have hinj := theta_injective hcard ρ hv hst hI
  ext y
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_baseChangeLat hcard ρ hv hst]
      exact ⟨_, hw, rfl⟩
    · change phi ρ v t w ∈ HT.eigSp ρ t
      rw [phi_apply]
      exact sum_mem fun a _ => Submodule.smul_mem _ _ (HT.LatBasic.eigProj_mem ρ t _)
  · rintro ⟨h1, h2⟩
    rw [SetLike.mem_coe, ← map_baseChangeLat hcard ρ hv hst] at h1
    obtain ⟨z, hz, rfl⟩ := h1
    have h3 : thetaO ρ v z ∈ HT.eigSp ρ t := h2
    have h4 := HT.LatBasic.eigProj_of_mem h3
    have h5 : HT.eigProj ρ t (thetaO ρ v z) = phi ρ v t (z t) := by
      rw [phi_apply, thetaO_apply, theta_apply, map_sum, Finset.sum_eq_single t]
      · simp only [map_sum, map_smul]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [eigProj_eigProj, if_pos rfl]
      · intro u _ hu
        simp only [map_sum, map_smul]
        refine Finset.sum_eq_zero fun a _ => ?_
        rw [eigProj_eigProj, if_neg hu, smul_zero]
      · simp
    have h6 : z = Pi.single t (z t) := by
      apply hinj
      change thetaO ρ v z = phi ρ v t (z t)
      rw [← h5, h4]
    refine ⟨z t, ?_, ?_⟩
    · change LinearMap.single (𝓞 L) (fun _ : E →+* L => Fin r → L) t (z t) ∈ baseChangeLat L _
      rw [LinearMap.coe_single, ← h6]
      exact hz
    · rw [← h5, h4]

theorem map_familyLat [NumberField L] (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {r : ℕ} (v : Fin r → V) (t : E →+* L) :
    (familyLat t (fun a => (Pi.single a 1 : Fin r → E))).map (phi ρ v t) =
      Submodule.span (𝓞 L) (Set.range fun a => HT.eigProj ρ t (v a)) := by
  classical
  rw [familyLat, Submodule.map_span, ← Set.range_comp]
  congr 2
  funext a
  simp only [Function.comp_apply, phi_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [Pi.single_eq_of_ne hb]
  · simp

omit [Fintype (E →+* L)] [CharZero L] in
theorem map_toAddSubgroup {M N : Type} [AddCommGroup M] [AddCommGroup N] [Module (𝓞 L) M]
    [Module (𝓞 L) N] (f : M →ₗ[𝓞 L] N) (P : Submodule (𝓞 L) M) :
    (P.map f).toAddSubgroup = P.toAddSubgroup.map f.toAddMonoidHom := rfl

theorem phi_injective (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hv : IsOFamily ρ I v)
    (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I)
    (hI : ∃ (n : ℕ) (e : Fin n → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I)
    (t : E →+* L) : Function.Injective (phi ρ v t) := by
  classical
  intro w w' h
  have := theta_injective hcard ρ hv hst hI h
  exact Pi.single_injective t this

end Index

section Final

omit [Fintype (E →+* L)] [CharZero L] in
theorem eigSp_comp (ρ : 𝓞 E →+* Module.End L V) (t : E →+* L) :
    eigSp ρ (t.comp (algebraMap (𝓞 E) E)) = HT.eigSp ρ t := by
  ext x
  rw [HT.ProjEig.mem_eigSp_iff_apply]
  simp [eigSp, Submodule.mem_iInf, sub_eq_zero]

theorem eigComp_comp (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (hsur : ∀ σ' : 𝓞 E →+* L, ∃ u : E →+* L, u.comp (algebraMap (𝓞 E) E) = σ')
    (ρ : 𝓞 E →+* Module.End L V) (t : E →+* L) (x : V) :
    eigComp ρ (t.comp (algebraMap (𝓞 E) E)) x = HT.eigProj ρ t x := by
  classical
  set σ := t.comp (algebraMap (𝓞 E) E) with hσ
  have hres : ∀ u : E →+* L, u ≠ t → u.comp (algebraMap (𝓞 E) E) ≠ σ := by
    intro u hu h
    exact hu (IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h)
  have hker : ∀ y ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* L | σ' ≠ σ}, eigSp ρ σ', HT.eigProj ρ t y = 0 := by
    intro y hy
    have hle : (⨆ σ' ∈ {σ' : 𝓞 E →+* L | σ' ≠ σ}, eigSp ρ σ') ≤ LinearMap.ker (HT.eigProj ρ t) := by
      refine iSup₂_le fun σ' hσ' z hz => ?_
      obtain ⟨u, rfl⟩ := hsur σ'
      rw [eigSp_comp] at hz
      have hut : t ≠ u := by
        rintro rfl
        exact hσ' rfl
      exact HT.LatBasic.eigProj_of_ne hut hz
    exact hle hy
  have hex : ∃ p ∈ eigSp ρ σ, x - p ∈ ⨆ σ' ∈ {σ' : 𝓞 E →+* L | σ' ≠ σ}, eigSp ρ σ' := by
    refine ⟨HT.eigProj ρ t x, ?_, ?_⟩
    · rw [hσ, eigSp_comp]
      exact HT.LatBasic.eigProj_mem ρ t x
    · have h1 := congrArg (fun T : Module.End L V => T x) (HT.sum_eigProj_eq_one L V E ρ hcard)
      simp only [LinearMap.sum_apply, Module.End.one_apply] at h1
      have h2 : x - HT.eigProj ρ t x = ∑ u ∈ Finset.univ.erase t, HT.eigProj ρ u x :=
        sub_eq_of_eq_add' ((Finset.add_sum_erase Finset.univ (fun u => HT.eigProj ρ u x)
          (Finset.mem_univ t)).trans h1).symm
      rw [h2]
      refine sum_mem fun u hu => ?_
      have hut := (Finset.mem_erase.1 hu).1
      have hmem : HT.eigProj ρ u x ∈ eigSp ρ (u.comp (algebraMap (𝓞 E) E)) := by
        rw [eigSp_comp]
        exact HT.LatBasic.eigProj_mem ρ u x
      exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (hres u hut) hmem)
  unfold eigComp
  rw [dif_pos hex]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  have h3 := hker _ h2
  rw [map_sub, sub_eq_zero] at h3
  have h1' : hex.choose ∈ HT.eigSp ρ t := (eigSp_comp ρ t).le h1
  rw [h3, HT.LatBasic.eigProj_of_mem h1']

variable [NumberField L] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V]

omit [CharZero L] [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] in
theorem exists_split {V : Type} (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E) (ι : L →+* ℂ) (σ : E →+* ℂ) :
    ∃ t : E →+* L, ι.comp t = σ := by
  have hbij : Function.Bijective (fun t : E →+* L => ι.comp t) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨fun a b h => ?_, ?_⟩
    · ext x
      exact ι.injective (DFunLike.congr_fun h x)
    · rw [hcard, NumberField.Embeddings.card]
  exact hbij.2 σ

theorem genIndex_tor (hE : EigenLatDifferent.Statement)
    (hcard : Fintype.card (E →+* L) = Module.finrank ℚ E)
    (ρ : 𝓞 E →+* Module.End L V) {I : AddSubgroup V} {r : ℕ} {v : Fin r → V} (hr : 1 ≤ r)
    (hv : IsOFamily ρ I v) (hst : ∀ a, ∀ x ∈ I, ρ a x ∈ I)
    (hI : ∃ (n : ℕ) (e : Fin n → V), LinearIndependent L e ∧ AddSubgroup.closure (Set.range e) = I)
    (t : E →+* L) :
    genIndex (Submodule.span (𝓞 L) (I : Set V) ⊓ (HT.eigSp ρ t).restrictScalars (𝓞 L)).toAddSubgroup
      (Submodule.span (𝓞 L) (Set.range fun a => HT.eigProj ρ t (v a))).toAddSubgroup =
      ((((oSpan ρ v).relIndex I : ℕ) : ℝ) / |(discr E : ℝ)| ^ r) ^
        ((Module.finrank ℚ L : ℝ) / Module.finrank ℚ E) := by
  let ι : L →+* ℂ := (IsAlgClosed.lift : L →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨hnz, hidx⟩ := isNzFamily_lat hcard ρ hr hv hst
  have hT := TorusIndex.proof hE DifferentLatIndex.proof E L ι
    (exists_split (V := V) hcard ι) r (lat ρ v I hst) r _ hnz t
  rw [hidx] at hT
  rw [← hT, ← map_eigenLat hcard ρ hv hst hI, ← map_familyLat hcard ρ v t, genIndex, genIndex,
    map_toAddSubgroup, map_toAddSubgroup]
  have hinj : Function.Injective (phi ρ v t).toAddMonoidHom := phi_injective hcard ρ hv hst hI t
  rw [AddSubgroup.relIndex_map_map_of_injective _ _ hinj,
    AddSubgroup.relIndex_map_map_of_injective _ _ hinj]

end Final

end TorPart

open NumberField GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NineStatements TorPart in

theorem torusPartDegree : ∀ (E L Ψ : Type) [Field E] [NumberField E] [Field L] [NumberField L] [Fintype Ψ] (V : Type) [AddCommGroup V] [Module L V] [Module (𝓞 L) V] [IsScalarTower (𝓞 L) L V] (A : LinPt E L Ψ V) (r : ℕ) (v : Fin r → V), 2 * Fintype.card Ψ = Module.finrank ℚ E → IsOFamily A.ρ A.I v → ∀ s, logIdx (A.tor s) (fun a => eigComp A.ρ (A.σ s) (v a)) / Module.finrank ℚ L = -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) + Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
  intro E L Ψ _ _ _ _ _ V _ _ _ _ A r v hΨ hv s
  classical

  have hres : Function.Bijective (fun t : E →+* L => t.comp (algebraMap (𝓞 E) E)) := by
    refine ⟨fun a b h => IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) h, fun g => ?_⟩
    obtain ⟨q, rfl⟩ := A.σ_bij.2 g
    exact ⟨IsFractionRing.lift (A.σ_inj q), RingHom.ext fun x => IsFractionRing.lift_algebraMap (A.σ_inj q) x⟩
  have hfin1 : Finite (𝓞 E →+* L) := Finite.of_surjective A.σ A.σ_bij.2
  have hfin2 : Finite (E →+* L) := Finite.of_injective _ hres.1
  letI : Fintype (E →+* L) := Fintype.ofFinite _
  have hcard : Fintype.card (E →+* L) = Module.finrank ℚ E := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr (Equiv.ofBijective _ hres),
      ← Nat.card_congr (Equiv.ofBijective _ A.σ_bij), ← hΨ, Nat.card_eq_fintype_card,
      Fintype.card_sum]
    ring
  obtain ⟨t, ht⟩ := hres.2 (A.σ s)
  change t.comp (algebraMap (𝓞 E) E) = A.σ s at ht
  have hsur : ∀ σ' : 𝓞 E →+* L, ∃ u : E →+* L, u.comp (algebraMap (𝓞 E) E) = σ' := hres.2
  have hcomp : (fun a => eigComp A.ρ (A.σ s) (v a)) = fun a => HT.eigProj A.ρ t (v a) := by
    funext a
    rw [← ht, eigComp_comp hcard hsur]
  have htor : A.tor s = Submodule.span (𝓞 L) (A.I : Set V) ⊓ (HT.eigSp A.ρ t).restrictScalars (𝓞 L) := by
    rw [LinPt.tor, ← ht, eigSp_comp]
  have hnL : (Module.finrank ℚ L : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hnE : (Module.finrank ℚ E : ℝ) ≠ 0 := by exact_mod_cast Module.finrank_pos.ne'
  have hd : |(discr E : ℝ)| ≠ 0 := abs_ne_zero.2 (by exact_mod_cast discr_ne_zero E)
  have hdp : 0 < |(discr E : ℝ)| := lt_of_le_of_ne (abs_nonneg _) hd.symm
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · have hI0 : A.I = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨x, rfl⟩ := exists_psi hcard A.ρ hv hy
      rw [Subsingleton.elim x 0, map_zero]
      exact AddSubgroup.zero_mem _
    have hO : oSpan A.ρ v = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      obtain ⟨c, rfl⟩ := (mem_oSpan_iff A.ρ v y).1 hy
      simp
    have hF : A.tor s = ⊥ := by
      rw [htor, hI0, eq_bot_iff]
      rintro y ⟨hy, -⟩
      simpa using hy
    simp [logIdx, hF, hO, hI0]
  · have hg := genIndex_tor GlobalTheory.T.eigen_lattices_different_statement_holds hcard A.ρ hr hv A.I_stable A.I_basis t
    have hi : (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hv.2.2
    have hip : 0 < (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) :=
      lt_of_le_of_ne (Nat.cast_nonneg _) hi.symm
    have hbase : 0 < (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / |(discr E : ℝ)| ^ r :=
      div_pos hip (pow_pos hdp r)
    have key : ∀ p q : ℕ, (p : ℝ) / q = ((((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / |(discr E : ℝ)| ^ r) ^
        ((Module.finrank ℚ L : ℝ) / Module.finrank ℚ E) →
        (Real.log p - Real.log q) / Module.finrank ℚ L =
          -(r * Real.log (|(discr E : ℝ)| ^ (1 / (Module.finrank ℚ E : ℝ)))) +
            Real.log (((oSpan A.ρ v).relIndex A.I : ℕ) : ℝ) / Module.finrank ℚ E := by
      intro p q h
      have hR := Real.rpow_pos_of_pos hbase ((Module.finrank ℚ L : ℝ) / Module.finrank ℚ E)
      rw [← h] at hR
      have hp : (p : ℝ) ≠ 0 := by
        intro h0
        rw [h0, zero_div] at hR
        exact lt_irrefl _ hR
      have hq : (q : ℝ) ≠ 0 := by
        intro h0
        rw [h0, div_zero] at hR
        exact lt_irrefl _ hR
      have hlog := congrArg Real.log h
      rw [Real.log_div hp hq, Real.log_rpow hbase, Real.log_div hi (pow_ne_zero _ hd), Real.log_pow] at hlog
      rw [Real.log_rpow hdp, hlog]
      field_simp
      ring
    rw [hcomp, htor, logIdx]
    exact key _ _ hg

end GlobalTheory.CompanionTheory.Ar.Cusp
