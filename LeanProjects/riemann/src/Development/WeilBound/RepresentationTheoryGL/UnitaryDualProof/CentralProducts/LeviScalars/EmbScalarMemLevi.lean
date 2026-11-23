import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.CentralProducts.TopProdD
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.WhittakerCuspidal.UnipBEqUnipotent
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DerCharEqOneOfMemUnipRad
import GroundTheory.AutomorphicForms.AdmissibleFiniteLength

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib

namespace PositivityTheory.RgUd.Prod.LF

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def bb (n N : ℕ) : Fin N → Bool := fun i => decide (n ≤ (i : ℕ))

theorem bb_eq_true {n N : ℕ} (i : Fin N) : bb n N i = true ↔ n ≤ (i : ℕ) := by
  simp [bb]

theorem bb_eq_false {n N : ℕ} (i : Fin N) : bb n N i = false ↔ (i : ℕ) < n := by
  simp [bb]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in

theorem unip_entries {n N : ℕ} {g : GL (Fin N) k}
    (hg : g ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (i j : Fin N)
    (hij : ¬ ((i : ℕ) < n ∧ n ≤ (j : ℕ))) :
    (g : Matrix (Fin N) (Fin N) k) i j = (1 : Matrix (Fin N) (Fin N) k) i j := by
  obtain ⟨hP, hD⟩ := GroundTheory.Automorphic.Parabolic.mem_unipotentRadical.1 hg
  by_cases he : bb n N i = bb n N j
  · exact hD i j he
  · have hji : (j : ℕ) < n ∧ n ≤ (i : ℕ) := by
      by_cases hi : n ≤ (i : ℕ)
      · refine ⟨?_, hi⟩
        by_contra hj
        exact he (((bb_eq_true i).2 hi).trans ((bb_eq_true j).2 (by omega)).symm)
      · exfalso
        by_cases hj : n ≤ (j : ℕ)
        · exact hij ⟨by omega, hj⟩
        · exact he (((bb_eq_false i).2 (by omega)).trans ((bb_eq_false j).2 (by omega)).symm)
    have hlt : bb n N j < bb n N i := by
      rw [(bb_eq_false j).2 hji.1, (bb_eq_true i).2 hji.2]
      decide
    have h0 : (g : Matrix (Fin N) (Fin N) k) i j = 0 := hP hlt
    rw [h0, one_apply_ne (fun e => by rw [e] at hji; omega)]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem unip_le_derUnip {n N : ℕ} :
    GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N) ≤ derUnip k N n := by
  intro g hg
  have hE := unip_entries hg
  refine Subgroup.mem_inf.2 ⟨(mem_unipB k).2 ⟨fun i j hji => ?_, fun i => ?_⟩,
    (GlobalTheory.CompanionTheory.BZMirStep.mem_colFix_iff _).2 fun i j hj => hE i j (by omega)⟩
  · have := Fin.lt_def.1 hji
    rw [hE i j (by omega), one_apply_ne (ne_of_gt hji)]
  · rw [hE i i (by omega), one_apply_eq]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem derChar_unip {n N : ℕ} (ψ : AddChar k Circle) (u : derUnip k N n)
    (hu : (u : GL (Fin N) k) ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) :
    derChar k ψ N n u = 1 := by
  have hE := unip_entries hu
  show Circle.toUnits _ = 1
  rw [Finset.sum_eq_zero, AddChar.map_zero_eq_one, map_one]
  intro p hp
  obtain ⟨h1, h2⟩ := (Finset.mem_filter.1 hp).2
  refine (hE p.1 p.2 (by omega)).trans (one_apply_ne fun e => ?_)
  rw [e] at h1
  omega

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem sub_mem_twKer {n N : ℕ} (ψ : AddChar k Circle) {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (u : GL (Fin N) k)
    (hu : u ∈ GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)) (w : V) :
    π u w - w ∈ twKer π (derUnip k N n) (derChar k ψ N n) :=
  Submodule.subset_span ⟨⟨u, unip_le_derUnip hu⟩, w, by rw [derChar_unip ψ _ hu]; simp⟩

def dd (n N : ℕ) (x : kˣ) : Fin N → k := fun i => if (i : ℕ) < n then (x : k) else 1

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) : Matrix (Fin N) (Fin N) k) =
      diagonal (dd n N x) := by
  ext i j
  obtain ⟨a, rfl⟩ := (stdSum h).surjective i
  obtain ⟨b, rfl⟩ := (stdSum h).surjective j
  rcases a with a | a <;> rcases b with b | b
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inl]
    by_cases hab : a = b
    · subst hab
      simp [dd, GeneralLinearGroup.scalar]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inl_injective ((stdSum h).injective e)))]
      simp [GeneralLinearGroup.scalar, hab]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inl_inr,
      diagonal_apply_ne _ (fun e => Sum.inl_ne_inr ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inl,
      diagonal_apply_ne _ (fun e => Sum.inr_ne_inl ((stdSum h).injective e))]
  · rw [GlobalTheory.CompanionTheory.BZMirJac.emb_inr_inr]
    by_cases hab : a = b
    · subst hab
      simp [dd]
    · rw [diagonal_apply_ne _ (fun e => hab (Sum.inr_injective ((stdSum h).injective e)))]
      simp [hab]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_mem_levi {n t N : ℕ} (h : n + t = N) (x : kˣ) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N) := by
  rw [GroundTheory.Automorphic.Parabolic.mem_levi]
  intro i j hij
  have hne : i ≠ j := fun e => hij (e ▸ rfl)
  show ((emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) : GL (Fin N) k) :
    Matrix (Fin N) (Fin N) k) i j = 0
  rw [emb_scalar, diagonal_apply_ne _ hne]

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem emb_scalar_comm {n t N : ℕ} (h : n + t = N) (x : kˣ) (y : GL (Fin N) k)
    (hy : y ∈ GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) :
    emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) * y =
      y * emb₂ k (stdSum h) (GeneralLinearGroup.scalar (Fin n) x, 1) := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, emb_scalar]
  ext i j
  rw [diagonal_mul, mul_diagonal]
  by_cases he : bb n N i = bb n N j
  · have hd : dd n N x i = dd n N x j := by
      by_cases hi : (i : ℕ) < n
      · have hj : (j : ℕ) < n := (bb_eq_false j).1 (he.symm.trans ((bb_eq_false i).2 hi))
        simp [dd, hi, hj]
      · have hj : ¬ (j : ℕ) < n := fun hj =>
          hi ((bb_eq_false i).1 (he.trans ((bb_eq_false j).2 hj)))
        simp [dd, hi, hj]
    rw [hd, mul_comm]
  · have h0 : (y : Matrix (Fin N) (Fin N) k) i j = 0 := GroundTheory.Automorphic.Parabolic.mem_levi.1 hy i j he
    rw [h0, mul_zero, zero_mul]

theorem lfin_of_quot {n t N : ℕ} (h : n + t = N) (ψ : AddChar k Circle) {V X : Type} [AddCommGroup V]
    [Module ℂ V] [AddCommGroup X] [Module ℂ X] (π : Representation ℂ (GL (Fin N) k) V)
    (hπ : GlobalTheory.PRep.IsAdmissible π) (ρ : Representation ℂ (GL (Fin n) k) X) (p : V →ₗ[ℂ] X)
    (hp : Function.Surjective p) (hk : twKer π (derUnip k N n) (derChar k ψ N n) ≤ LinearMap.ker p)
    (hi : ∀ g v, p (π (emb₂ k (stdSum h) (g, 1)) v) = ρ g (p v)) (a : X) :
    ∃ U : Submodule ℂ X, FiniteDimensional ℂ U ∧ a ∈ U ∧
      ∀ (x : kˣ), ∀ u ∈ U, ρ (GeneralLinearGroup.scalar (Fin n) x) u ∈ U := by
  obtain ⟨v, rfl⟩ := hp a
  have hF : GroundTheory.Automorphic.IsAdmissible π := (PositivityTheory.rg.gu.whit.isAdmissible_iff π).1 hπ
  have hA := GroundTheory.Automorphic.Parabolic.isAdmissible_jacquetRep (β := bb n N) hF
  let J := GroundTheory.Automorphic.Parabolic.jacquetAction k N (bb n N) π
  have hpu : ∀ u : GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N),
      p ∘ₗ (π.comp (GroundTheory.Automorphic.Parabolic.unipotentRadical k N (bb n N)).subtype) u = p := by
    intro u
    refine LinearMap.ext fun w => ?_
    show p (π u w) = p w
    rw [← sub_eq_zero, ← map_sub]
    exact hk (sub_mem_twKer ψ π u u.2 w)
  let pb : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π →ₗ[ℂ] X :=
    Representation.Coinvariants.lift _ p hpu
  have hpb : ∀ w, pb (Representation.Coinvariants.mk _ w) = p w := fun w =>
    Representation.Coinvariants.lift_mk _ p hpu w
  let w₀ : GroundTheory.Automorphic.Parabolic.JacquetModule k N (bb n N) π := Representation.Coinvariants.mk _ v
  let KM : ℕ → Subgroup (GroundTheory.Automorphic.Parabolic.levi k N (bb n N)) := fun m =>
    (GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k N m).subgroupOf (GroundTheory.Automorphic.Parabolic.levi k N (bb n N))
  obtain ⟨m, hm⟩ := GroundTheory.Automorphic.Parabolic.exists_subgroupOf_congruenceSubgroup_subset (F := k) (n := N)
    (β := bb n N) ((hA.1 w₀).mem_nhds (one_mem (GroundTheory.Automorphic.stabilizerOf _ w₀)))
  have hfix : w₀ ∈ GroundTheory.Automorphic.fixedVectors J (KM m) := by
    have : w₀ ∈ GroundTheory.Automorphic.fixedVectors (GroundTheory.Automorphic.Parabolic.jacquetRep k N (bb n N) π) (KM m) :=
      fun x hx => hm hx
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors J (KM m)) := by
    have := hA.2 (KM m)
      (GroundTheory.Automorphic.Parabolic.isCompact_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k N m))
      (GroundTheory.Automorphic.Parabolic.isOpen_subgroupOf_levi
        (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k N m))
    rwa [GroundTheory.Automorphic.Parabolic.fixedVectors_jacquetRep_congruenceSubgroup] at this
  refine ⟨(GroundTheory.Automorphic.fixedVectors J (KM m)).map pb, inferInstance, ⟨w₀, hfix, hpb v⟩, ?_⟩
  rintro x _ ⟨y, hy, rfl⟩
  obtain ⟨w, rfl⟩ := Representation.Coinvariants.mk_surjective _ y
  let z : GroundTheory.Automorphic.Parabolic.levi k N (bb n N) :=
    ⟨_, emb_scalar_mem_levi h x⟩
  refine ⟨J z (Representation.Coinvariants.mk _ w), ?_, ?_⟩
  · intro g hg
    have hc : g * z = z * g := Subtype.ext (emb_scalar_comm h x g g.2).symm
    show J g (J z _) = J z _
    rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply]
    exact congrArg _ (hy g hg)
  · show pb (Representation.Coinvariants.mk _ (π _ w)) = _
    rw [hpb, hpb, hi]

theorem lfin_self {n : ℕ} (A : GRep k n) (hA : GlobalTheory.PRep.IsAdmissible A.ρ) : LFin A := by
  intro v
  have hF : GroundTheory.Automorphic.IsAdmissible A.ρ := (PositivityTheory.rg.gu.whit.isAdmissible_iff A.ρ).1 hA
  have hO : {g : GL (Fin n) k | A.ρ g v = v} ∈ nhds (1 : GL (Fin n) k) :=
    (hA.1 v).mem_nhds (by simp)
  obtain ⟨m, -, hm⟩ := (GroundTheory.Automorphic.GLnLocal.hasBasis_nhds_one k n).mem_iff.1 hO
  let K := GroundTheory.Automorphic.GLnLocal.congruenceSubgroup k n m
  have hfin : FiniteDimensional ℂ (GroundTheory.Automorphic.fixedVectors A.ρ K) :=
    hF.2 K (GroundTheory.Automorphic.GLnLocal.isCompact_congruenceSubgroup k n m)
      (GroundTheory.Automorphic.GLnLocal.isOpen_congruenceSubgroup k n m)
  refine ⟨GroundTheory.Automorphic.fixedVectors A.ρ K, hfin, fun g hg => hm hg, ?_⟩
  intro x u hu g hg
  have hc : g * sc n x = sc n x * g := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    show (g : Matrix (Fin n) (Fin n) k) * scalar (Fin n) (x : k) = scalar (Fin n) (x : k) * g
    exact ((scalar_commute (x : k) (fun r => Commute.all _ r) (g : Matrix (Fin n) (Fin n) k))).symm.eq
  show A.ρ g (A.ρ (sc n x) u) = A.ρ (sc n x) u
  rw [← Module.End.mul_apply, ← map_mul, hc, map_mul, Module.End.mul_apply, hu g hg]

variable (k)

theorem lfDeriv : LFDeriv k := by
  intro ψ _ n j π _ hA
  cases j with
  | zero => exact lfin_self π hA
  | succ j =>
    intro a
    obtain ⟨p, hp, hpk, hpi⟩ := GlobalTheory.CompanionTheory.BZMirJac.iterPhi_quotient ψ n j (resM k π.ρ)
    refine lfin_of_quot (rfl : n + (j + 1) = n + j + 1) ψ π.ρ hA (deriv k ψ j π.ρ) p hp ?_ ?_ a
    · intro w hw
      have hw' : w ∈ LinearMap.ker p := by
        rw [hpk, GlobalTheory.CompanionTheory.BZMirDer.twKer_resM_derUnipM]
        exact hw
      exact hw'
    · intro g v
      rw [← GlobalTheory.CompanionTheory.BZMirJac.iotaM_eq_emb]
      exact hpi g v

end PositivityTheory.RgUd.Prod.LF
