import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.Inertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamZl
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.LamFactor
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoEvLow
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoMvps
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoRes
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.LocallyConstantOfOpenSet

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.W

private theorem teich_ex (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [IsLocalRing O]
    [IsAdicComplete (maximalIdeal O) O] [Finite (ResidueField O)] [CharP (ResidueField O) l] :
    ∃ τ : ResidueField O →* O, ∀ x, residue O (τ x) = x := by
  haveI : CharP (O ⧸ maximalIdeal O) l := inferInstanceAs (CharP (ResidueField O) l)
  haveI : PerfectRing (ResidueField O) l := inferInstance
  let j : ResidueField O →+* Perfection (O ⧸ maximalIdeal O) l :=
    Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O) (RingHom.id (ResidueField O))
  have hj : ∀ x, Perfection.coeff (O ⧸ maximalIdeal O) l 0 (j x) = x := fun x => by
    have := (Perfection.lift l (ResidueField O) (O ⧸ maximalIdeal O)).symm_apply_apply (RingHom.id (ResidueField O))
    exact RingHom.congr_fun this x
  refine ⟨(Perfection.teichmuller l (maximalIdeal O)).comp j, fun x => ?_⟩
  exact (Perfection.mk_teichmuller (j x)).trans (hj x)

private theorem lc_of_open {G H : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group H]
    (f : G →* H) (h : IsOpen (f.ker : Set G)) : IsLocallyConstant f :=
  _root_.UpperTheory.Reformulated.B.LocallyConstantOfOpenSet.lc_of_open f h

theorem UpperTheory.V.W.psib_mu (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O]
    [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (v : F.Vl) (i : Fin n) (g : F.mu v) : r.psib v i g = 1 := by
  obtain ⟨k, hk⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l)) ⟨_, g.2⟩
  have h1 : (QuotientGroup.mk' (commutator (F.Gv v)).topologicalClosure (g : F.Gv v)) ^ l ^ k = 1 :=
    congrArg Subtype.val hk
  rw [← map_pow] at h1
  have h2 : (g : F.Gv v) ^ l ^ k ∈ (commutator (F.Gv v)).topologicalClosure := (QuotientGroup.eq_one_iff _).1 h1
  have h3 : (commutator (F.Gv v)).topologicalClosure ≤ (r.psib v i).ker :=
    Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker _)
      (Subgroup.isClosed_of_isOpen _ (r.psib_open v i))
  have h4 : r.psib v i g ^ l ^ k = 1 := by rw [← map_pow]; exact h3 h2
  have h5 : ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) ^ l ^ k = 1 := by
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
  have h6 : (((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) - 1) ^ l ^ k = 0 := by
    rw [sub_pow_char_pow, h5]; simp
  exact Units.ext (sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero k (Fact.out : l.Prime).ne_zero) |>.1 h6))

theorem UpperTheory.V.W.exists_character_lifting_psi_free :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, LocAb l (F.Gv v) (F.Iv v) (d v)), ∀ v i, ∃ ψ : F.Gv v →* Oˣ, r.IsPsi v i ψ := by
  intro l _ F O _ _ _ _ _ _ _ n r d A v i
  obtain ⟨τ, hτ⟩ := teich_ex l O
  let P := CommGroup.primaryComponent (TopologicalAbelianization (F.Gv v)) l
  let q : F.mu v →* P := ((QuotientGroup.mk' _).comp (F.mu v).subtype).codRestrict P fun g => g.2
  have hq : Function.Surjective q := by
    rintro ⟨x, hx⟩
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    exact ⟨⟨g, hx⟩, rfl⟩
  have hker : q.ker ≤ (r.th v i).ker := fun g hg => by
    have h1 : (q g : TopologicalAbelianization (F.Gv v)) = 1 := by rw [MonoidHom.mem_ker.1 hg]; rfl
    exact r.th_comm v i g ((QuotientGroup.eq_one_iff _).1 h1)
  let t : P →* Oˣ := q.liftOfSurjective hq ⟨r.th v i, hker⟩
  have ht : ∀ g, t (q g) = r.th v i g := fun g => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ g
  have hres : ∀ x : P, residue O (t x) = 1 := fun x => by
    obtain ⟨k, hk⟩ := (CommGroup.primaryComponent.isPGroup (G := TopologicalAbelianization (F.Gv v)) (p := l)) x
    have h1 : residue O (t x) ^ l ^ k = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, ← map_pow, hk]; simp
    have h2 : (residue O (t x) - 1) ^ l ^ k = 0 := by rw [sub_pow_char_pow, h1]; simp
    exact sub_eq_zero.1 (pow_eq_zero_iff (pow_ne_zero k (Fact.out : l.Prime).ne_zero) |>.1 h2)
  have hb : ∀ g : F.mu v, (A v).b g = q g := fun g => Subtype.ext ((A v).b_mu g g.2)
  have hrO : ∀ x : O, res O O x = residue O x := fun x => (res O O).commutes x
  refine ⟨(Units.map τ).comp (r.psib v i) * t.comp (A v).b, fun N => ?_, fun g => ?_, fun g => ?_⟩
  · exact ((lc_of_open _ (r.psib_open v i)).prodMk (lc_of_open _ (A v).b_open)).comp
      fun p => Ideal.Quotient.mk (maximalIdeal O ^ N) ((Units.map τ p.1 * t p.2 : Oˣ) : O)
  · rw [hrO]
    show residue O (τ (r.psib v i g) * t ((A v).b g)) = _
    rw [map_mul, hτ, hres, mul_one]
  · show τ (r.psib v i g) * t ((A v).b g) = (r.th v i g : O)
    have h1 : ((r.psib v i g : (ResidueField O)ˣ) : ResidueField O) = 1 := by
      exact congrArg Units.val (psib_mu l F O n r v i g)
    rw [h1, map_one, one_mul, hb, ht]

private theorem lam_cont {O R R' Γ : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] [TopologicalSpace Γ] (f : R →ₐ[O] R') (x : Γ → R)
    (hx : AdicCont (maximalIdeal R) x) : AdicCont (maximalIdeal R') fun g => f (x g) := fun N => by
  have hle : maximalIdeal R ^ N ≤ (maximalIdeal R' ^ N).comap (f : R →+* R') := by
    refine le_trans (Ideal.pow_right_mono (fun y hy => ?_) N) (Ideal.le_comap_pow _ N)
    show f y ∈ maximalIdeal R'
    rw [← res_eq_zero_iff O, res_map, res_eq_zero_iff]
    exact hy
  exact (hx N).comp (Ideal.quotientMap _ (f : R →+* R') hle)

private theorem lam_res (l : ℕ) [Fact l.Prime] {O R ι : Type} [CommRing O] [IsLocalRing O]
    [CharP (ResidueField O) l] [CommRing R] [Algebra O R] [IsCO O R] [Fintype ι] [DecidableEq ι]
    (χ : Multiplicative (ι → ℤ_[l]) →* Rˣ) (hc : AdicCont (maximalIdeal R) fun x => ((χ x : Rˣ) : R))
    (h1 : ∀ i, res O R (χ (Multiplicative.ofAdd (Pi.single i 1))) = 1) (x) : res O R (χ x) = 1 := by
  haveI := (co_res O).1
  have h := (lam_zl l O (ResidueField O) ι (fun _ => 1) (fun _ => by simp)).unique
    (y₁ := pushCh (res O R : R →+* ResidueField O) χ) (y₂ := 1)
    ⟨lam_cont (res O R) _ hc, fun i => Units.ext (h1 i)⟩
    ⟨fun N => IsLocallyConstant.of_constant _ fun _ _ => rfl, fun i => rfl⟩
  exact congrArg Units.val (DFunLike.congr_fun h x)

private theorem lam_push {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} {R R' : Type} [CommRing R] [Algebra O R] [IsCO O R]
    [CommRing R'] [Algebra O R'] [IsCO O R'] (f : R →ₐ[O] R') {v : F.Vl} {i : Fin n} {ψ : F.Gv v →* Rˣ}
    (h : r.IsPsi v i ψ) : r.IsPsi v i (pushCh (f : R →+* R') ψ) where
  cont := lam_cont f _ h.cont
  red g := (res_map f _).trans (h.red g)
  mu g := (congrArg f (h.mu g)).trans (f.commutes _)

private def lam_fst (l : ℕ) [Fact l.Prime] (d : ℕ) :
    Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]) →* Multiplicative (Fin d → ℤ_[l]) where
  toFun x := Multiplicative.ofAdd x.toAdd.1
  map_one' := rfl
  map_mul' _ _ := rfl

private noncomputable def lam_inl (l : ℕ) [Fact l.Prime] (d : ℕ) :
    Multiplicative (Fin d → ℤ_[l]) →* Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]) where
  toFun x := Multiplicative.ofAdd (x.toAdd, 0)
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp

private theorem lam_fst_cont (l : ℕ) [Fact l.Prime] (d : ℕ) : Continuous (lam_fst l d) :=
  continuous_ofAdd.comp (continuous_fst.comp continuous_toAdd)

private theorem lam_inl_cont (l : ℕ) [Fact l.Prime] (d : ℕ) : Continuous (lam_inl l d) :=
  continuous_ofAdd.comp (continuous_toAdd.prodMk continuous_const)

private theorem lam_inl_fst (l : ℕ) [Fact l.Prime] (d : ℕ) (x : Multiplicative ((Fin d → ℤ_[l]) × ℤ_[l]))
    (hx : x.toAdd.2 = 0) : lam_inl l d (lam_fst l d x) = x := by
  apply Multiplicative.toAdd.injective
  exact Prod.ext rfl hx.symm

private theorem lam_uniq {l : ℕ} [Fact l.Prime] {F : GFrame l} {O : Type} [CommRing O] [IsLocalRing O]
    [Algebra ℤ_[l] O] {n : ℕ} {r : Resid F O n} (L M : LamObj r) :
    ∃ e : L.Λ ≃ₐ[O] M.Λ, ∀ v i g, e ((L.κ v i g : L.Λˣ) : L.Λ) = M.κ v i g := by
  obtain ⟨f, hf, -⟩ := L.univ M.Λ M.κ M.inert
  obtain ⟨g, hg, -⟩ := M.univ L.Λ L.κ L.inert
  refine ⟨AlgEquiv.ofAlgHom f g ((M.univ M.Λ M.κ M.inert).unique (fun v i => ?_) fun v i => rfl)
    ((L.univ L.Λ L.κ L.inert).unique (fun v i => ?_) fun v i => rfl),
    fun v i x => congrArg Units.val (DFunLike.congr_fun (hf v i) x)⟩
  · rw [← hf v i]
    conv_rhs => rw [← hg v i]
    rw [hf v i]
    rfl
  · rw [← hg v i]
    conv_rhs => rw [← hf v i]
    rw [hg v i]
    rfl

theorem UpperTheory.V.W.lam_ex_free :
    ∀ (l : ℕ) [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [IsAdicComplete (maximalIdeal O) O] [Algebra ℤ_[l] O] [Finite (ResidueField O)] [CharP (ResidueField O) l] (n : ℕ) (r : Resid F O n) (d : F.Vl → ℕ) (A : ∀ v, LocAb l (F.Gv v) (F.Iv v) (d v)), Nonempty (LamObj r) ∧ ∀ Λ : LamObj r, ∃ (e : MvPowerSeries (Σ v, Fin n × Fin (d v)) O ≃ₐ[O] Λ.Λ) (ψ₀ : ∀ v, Fin n → F.Gv v →* Oˣ), (∀ v i, r.IsPsi v i (ψ₀ v i)) ∧
      ∀ v i j (g : F.Iv v), (A v).a g = Multiplicative.ofAdd (Pi.single j 1, 0) → ((Λ.κ v i g : Λ.Λˣ) : Λ.Λ) = algebraMap O Λ.Λ (ψ₀ v i g) * (1 + e (MvPowerSeries.X ⟨v, i, j⟩)) := by
  intro l _ F O _ _ _ _ _ _ _ n r d A
  choose ψ₀ hψ₀ using exists_character_lifting_psi_free l F O n r d A
  have hI : ∀ v (g : F.Iv v), ((A v).a g).toAdd.2 = 0 := fun v g => ((A v).inertia _).1 ⟨g, g.2, rfl⟩
  have fac : ∀ (R : Type) [CommRing R] [Algebra O R] [IsCO O R] v i (κ : F.Iv v →* Rˣ),
      (∃ ψ : F.Gv v →* Rˣ, r.IsPsi v i ψ ∧ κ = ψ.comp (F.Iv v).subtype) ↔
      ∃ χ : Multiplicative (Fin (d v) → ℤ_[l]) →* Rˣ,
        AdicCont (maximalIdeal R) (fun x => ((χ x : Rˣ) : R)) ∧ (∀ x, res O R (χ x) = 1) ∧
        κ = (pushCh (Algebra.ofId O R : O →+* R) (ψ₀ v i) * χ.comp ((lam_fst l (d v)).comp (A v).a)).comp
          (F.Iv v).subtype := by
    intro R _ _ _ v i κ
    have hf := lam_factor l F O n r d A R v i _ (lam_push (Algebra.ofId O R) (hψ₀ v i))
    constructor
    · rintro ⟨ψ, hψ, rfl⟩
      obtain ⟨χ, h1, h2, rfl⟩ := (hf ψ).1 hψ
      refine ⟨χ.comp (lam_inl l _), fun N => (h1 N).comp_continuous (lam_inl_cont l _), fun x => h2 _, ?_⟩
      refine MonoidHom.ext fun g => ?_
      show _ * χ ((A v).a g) = _ * χ (lam_inl l _ (lam_fst l _ ((A v).a g)))
      rw [lam_inl_fst l _ _ (hI v g)]
    · rintro ⟨χ, h1, h2, rfl⟩
      exact ⟨_, (hf _).2 ⟨χ.comp (lam_fst l _), fun N => (h1 N).comp_continuous (lam_fst_cont l _),
        fun x => h2 _, rfl⟩, rfl⟩
  let σ : Type := Σ v, Fin n × Fin (d v)
  let P : Type := MvPowerSeries σ O
  haveI : IsCO O P := co_mvps O O σ
  have hX : ∀ s : σ, (MvPowerSeries.X s : P) ∈ maximalIdeal P := fun s h => by
    simpa using MvPowerSeries.isUnit_constantCoeff _ h
  have hu : ∀ s : σ, IsUnit (1 + MvPowerSeries.X s : P) := fun s => by
    rw [MvPowerSeries.isUnit_iff_constantCoeff]; simp
  have hu1 : ∀ s : σ, res O P ((hu s).unit : Pˣ) = 1 := fun s => by
    rw [IsUnit.unit_spec, map_add, map_one, (res_eq_zero_iff O P _).2 (hX s), add_zero]
  choose χ hχ using fun v i => (lam_zl l O P (Fin (d v)) (fun j => (hu ⟨v, i, j⟩).unit) fun j => hu1 _).exists
  have hχ1 : ∀ v i j, ((χ v i (Multiplicative.ofAdd (Pi.single j 1)) : Pˣ) : P) = 1 + MvPowerSeries.X ⟨v, i, j⟩ :=
    fun v i j => congrArg Units.val ((hχ v i).2 j)
  let L : LamObj r :=
    { Λ := P
      κ := fun v i => (pushCh (Algebra.ofId O P : O →+* P) (ψ₀ v i) *
        (χ v i).comp ((lam_fst l (d v)).comp (A v).a)).comp (F.Iv v).subtype
      inert := fun v i => (fac P v i _).2 ⟨χ v i, (hχ v i).1,
        lam_res l _ (hχ v i).1 fun j => by rw [(hχ v i).2 j]; exact hu1 _, rfl⟩
      univ := by
        intro R _ _ _ κ' hκ'
        choose χ' h1 h2 h3 using fun v i => (fac R v i _).1 (hκ' v i)
        have key : ∀ (G : P →ₐ[O] R) v i, pushCh (G : P →+* R) ((pushCh (Algebra.ofId O P : O →+* P) (ψ₀ v i) *
            (χ v i).comp ((lam_fst l (d v)).comp (A v).a)).comp (F.Iv v).subtype) =
            (pushCh (Algebra.ofId O R : O →+* R) (ψ₀ v i) *
            (pushCh (G : P →+* R) (χ v i)).comp ((lam_fst l (d v)).comp (A v).a)).comp (F.Iv v).subtype :=
          fun G v i => by
          ext g
          show G (algebraMap O P _ * _) = algebraMap O R _ * G _
          rw [map_mul, AlgHom.commutes]
          rfl
        obtain ⟨G, ⟨-, hG⟩, hG'⟩ := co_ev O O R σ (Algebra.ofId O R)
          (fun s => (χ' s.1 s.2.1 (Multiplicative.ofAdd (Pi.single s.2.2 1)) : R) - 1) fun s => by
            rw [← res_eq_zero_iff O, map_sub, h2, map_one, sub_self]
        refine ⟨G, fun v i => ?_, fun H hH => hG' H ⟨fun x => H.commutes x, ?_⟩⟩
        · have : pushCh (G : P →+* R) (χ v i) = χ' v i :=
            (lam_zl l O R (Fin (d v)) (fun j => χ' v i (Multiplicative.ofAdd (Pi.single j 1)))
              fun j => h2 v i _).unique ⟨lam_cont G _ (hχ v i).1, fun j => Units.ext (by
                show G ((χ v i _ : Pˣ) : P) = _
                rw [hχ1, map_add, map_one, hG]
                simp)⟩ ⟨h1 v i, fun j => rfl⟩
          rw [key, this, ← h3]
        · rintro ⟨v, i, j⟩
          have h4 := hH v i
          rw [key, h3 v i] at h4
          obtain ⟨g, hgI, hg⟩ := ((A v).inertia (Pi.single j 1, 0)).2 rfl
          have h5 := mul_left_cancel (DFunLike.congr_fun h4 ⟨g, hgI⟩)
          have h6 : H ((χ v i (lam_fst l _ ((A v).a g)) : Pˣ) : P) = χ' v i (lam_fst l _ ((A v).a g)) :=
            congrArg Units.val h5
          have h7 : lam_fst l _ ((A v).a g) = Multiplicative.ofAdd (Pi.single j 1) := by rw [hg]; rfl
          rw [h7, hχ1, map_add, map_one] at h6
          rw [← h6]
          simp }
  refine ⟨⟨L⟩, fun Λ => ?_⟩
  obtain ⟨e, he⟩ := lam_uniq L Λ
  let e' : P ≃ₐ[O] Λ.Λ := e
  refine ⟨e', ψ₀, hψ₀, fun v i j g hg => ?_⟩
  have h7 : lam_fst l _ ((A v).a g) = Multiplicative.ofAdd (Pi.single j 1) := by rw [hg]; rfl
  rw [← he]
  show e' (algebraMap O P (ψ₀ v i g) * ((χ v i (lam_fst l _ ((A v).a g)) : Pˣ) : P)) = _
  rw [h7, hχ1, map_mul, map_add, map_one, AlgEquiv.commutes]
