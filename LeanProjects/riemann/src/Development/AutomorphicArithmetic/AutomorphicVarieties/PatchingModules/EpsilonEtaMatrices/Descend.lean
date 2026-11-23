import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.EpsilonEtaMatrices.EpsilonEtaTensorDual
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.PolZCases
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.AdicLC
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.LcOfOpen
import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DegreeCountCohomology.DdSumZero
open Matrix Filter NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

private theorem pow_mem_of_PL (l : ℕ) {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
    (H : Subgroup Γ) (V : Set Γ) (hV : IsOpen V) (hle : (PL l H : Set Γ) ⊆ V) : ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ V := by
  let ι := {U : OpenNormalSubgroup Γ // ∀ h ∈ H, ∃ e : ℕ, h ^ l ^ e ∈ U}
  haveI : Nonempty ι := ⟨⟨⟨⊤, Subgroup.normal_top⟩, fun h _ => ⟨0, trivial⟩⟩⟩
  have hd : Directed (· ⊇ ·) fun U : ι => (U.1 : Set Γ) := by
    intro U U'
    refine ⟨⟨U.1 ⊓ U'.1, fun h hh => ?_⟩, fun a ha => ha.1, fun a ha => ha.2⟩
    obtain ⟨e, he⟩ := U.2 h hh
    obtain ⟨e', he'⟩ := U'.2 h hh
    refine ⟨e + e', ?_, ?_⟩
    · rw [pow_add, pow_mul]
      exact U.1.toSubgroup.pow_mem he _
    · rw [pow_add, mul_comm, pow_mul]
      exact U'.1.toSubgroup.pow_mem he' _
  have hs : Vᶜ ∩ ⋂ U : ι, (U.1 : Set Γ) = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun a ha => ha.1 (hle ?_)
    have := Set.mem_iInter.1 ha.2
    simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf]
    exact fun U hU => this ⟨U, hU⟩
  obtain ⟨U, hU⟩ := hV.isClosed_compl.isCompact.elim_directed_family_closed (fun U : ι => (U.1 : Set Γ))
    (fun U => U.1.toOpenSubgroup.isClosed) hs hd
  intro h hh
  obtain ⟨e, he⟩ := U.2 h hh
  refine ⟨e, ?_⟩
  by_contra hn
  exact Set.eq_empty_iff_forall_notMem.1 hU _ ⟨hn, he⟩

private theorem affine_ker {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup M] [Module R M] [Finite M] (ρ : Representation R Γ M) (hρ : LC ρ) (y : Γ → M) (hy : y ∈ Zl ρ) :
    ∃ U : OpenNormalSubgroup Γ, ∀ g, g ∈ U ↔ ρ g = 1 ∧ y g = 0 := by
  obtain ⟨h1, h2⟩ := hy
  have y1 : y 1 = 0 := by simpa using h2 1 1
  let a : Γ →* Function.End M :=
    { toFun := fun g m => y g + ρ g m
      map_one' := funext fun m => by simp [y1]; rfl
      map_mul' := fun g h => funext fun m => by
        show _ = y g + ρ g (y h + ρ h m)
        rw [h2, map_mul, map_add, add_assoc]; rfl }
  have key : ∀ g, g ∈ a.ker ↔ ρ g = 1 ∧ y g = 0 := by
    intro g
    rw [MonoidHom.mem_ker]
    constructor
    · intro h
      have h' : ∀ m, y g + ρ g m = m := congrFun h
      have h0 : y g = 0 := by simpa using h' 0
      exact ⟨LinearMap.ext fun m => by simpa [h0] using h' m, h0⟩
    · rintro ⟨e1, e2⟩
      funext m
      show y g + ρ g m = m
      simp [e1, e2]
  have ho : IsOpen (a.ker : Set Γ) := by
    have : (a.ker : Set Γ) = (⋂ m, {g | ρ g m = m}) ∩ {g | y g = 0} := by
      ext g
      simp only [SetLike.mem_coe, key, Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq]
      exact and_congr_left' ⟨fun h m => by rw [h]; rfl, fun h => LinearMap.ext h⟩
    rw [this]
    exact (isOpen_iInter_of_finite fun m => (hρ m).isOpen_fiber m).inter (h1.isOpen_fiber 0)
  exact ⟨⟨⟨a.ker, ho⟩, MonoidHom.normal_ker a⟩, key⟩

private theorem cocycle_pow {R Γ M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ]
    [AddCommGroup M] [Module R M] (ρ : Representation R Γ M) (y : Γ → M) (hy : y ∈ Zl ρ) (g : Γ) (hg : ρ g = 1) (k : ℕ) :
    y (g ^ k) = k • y g := by
  induction k with
  | zero => simpa using hy.2 1 1
  | succ k ih => rw [pow_succ', hy.2, hg, ih, succ_nsmul']; rfl

private theorem factor_lc {R Γ Γ' M : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] [T2Space Γ'] [AddCommGroup M] [Module R M] (ρ : Representation R Γ M)
    (y : Γ → M) (hy : y ∈ Zl ρ) (p : Γ →* Γ') (hc : Continuous p) (hs : Function.Surjective p)
    (hk : ∀ g ∈ p.ker, y g = 0) : ∃ Z : Γ' → M, IsLocallyConstant Z ∧ ∀ g, y g = Z (p g) := by
  have e : ∀ g, y g = y (Function.surjInv hs (p g)) := by
    intro g
    have : g⁻¹ * Function.surjInv hs (p g) ∈ p.ker := by
      rw [MonoidHom.mem_ker, map_mul, Function.surjInv_eq hs, map_inv, inv_mul_cancel]
    have h := hy.2 g (g⁻¹ * Function.surjInv hs (p g))
    rw [hk _ this, map_zero, add_zero, mul_inv_cancel_left] at h
    exact h.symm
  refine ⟨fun γ => y (Function.surjInv hs γ), fun s => ?_, e⟩
  have hq : Topology.IsQuotientMap p := hc.isClosedMap.isQuotientMap hc hs
  rw [← hq.isOpen_preimage]
  convert hy.1 s using 1
  ext g
  simp only [Set.mem_preimage, ← e g]

private theorem epM_mul {X : Type} [CommRing X] {g n : ℕ} (Z : Fin g → Matrix (Fin n) (Fin n) X) :
    DD.epM Z * DD.epM Z = 0 := by
  refine Matrix.ext fun a b => ?_
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  ext <;> simp [DD.epM]

private theorem one_add_pow {S : Type} [Ring S] (E : S) (h : E * E = 0) (k : ℕ) : (1 + E) ^ k = 1 + k • E := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, add_mul, mul_add, mul_add, smul_mul_assoc k E E, h, succ_nsmul]; simp; abel

private theorem rho1_pow_eq_one_pro_l (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n)
    (k : Kap x) (m : ℕ) (hPL : ∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) (g : G0.G₀)
    (hg : (g : G0.Γ) ∈ T.H) : ∃ e : ℕ, k.ρ1 (x.Am m) (g ^ l ^ e) = 1 := by
  have hI : IsLocalRing.maximalIdeal x.A ^ m = Ideal.span {x.t ^ m} := by
    rw [PowerSeries.maximalIdeal_eq_span_X, Ideal.span_singleton_pow]
  have h0 : ∀ i j, IsLocallyConstant fun g : G0.G₀ => x.ρX (DD (x.Am m) k.g) g i j := fun i j =>
    ((x.cont i j m).comp (Ideal.Quotient.factor hI.le)).comp (DD.C : x.Am m →+* DD (x.Am m) k.g)
  have ho : IsOpen {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g = 1} := by
    have : {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g = 1} = ⋂ i, ⋂ j,
        {g : G0.G₀ | x.ρX (DD (x.Am m) k.g) g i j = (1 : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) i j} := by
      ext g
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Matrix.ext_iff]
    rw [this]
    exact isOpen_iInter_of_finite fun i => isOpen_iInter_of_finite fun j => (h0 i j).isOpen_fiber _
  obtain ⟨e, g', h1, h2⟩ := pow_mem_of_PL l T.H.toSubgroup _ (G0.η_open.isOpenMap_subtype_val _ ho) (fun a ha => by
    have hη : a ∈ G0.η.ker := by
      have ha' := ha
      simp only [PL, SetLike.mem_coe, Subgroup.mem_iInf] at ha'
      exact ha' ⟨⟨G0.η.ker, G0.η_open⟩, MonoidHom.normal_ker _⟩ fun h hh =>
        ⟨0, by rw [pow_zero, pow_one]; exact T.H_η h hh⟩
    refine ⟨⟨a, hη⟩, ?_, rfl⟩
    show x.ρX _ _ = 1
    rw [NP.ρX]
    simp [mat, hPL ⟨a, hη⟩ ha]) g hg
  have h3 : g' = g ^ l ^ e := Subtype.ext h2
  subst h3
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  have hp : ∀ (u : G0.G₀) (j : ℕ), k.ρ1 (x.Am m) (u ^ j) = k.ρ1 (x.Am m) u ^ j := fun u j => by
    induction j with
    | zero => rw [pow_zero, pow_zero]; exact r1
    | succ j ih => rw [pow_succ, pow_succ, ← ih]; exact r2 _ _
  refine ⟨e + 1, ?_⟩
  have h1' : x.ρX (DD (x.Am m) k.g) (g ^ l ^ e) = 1 := h1
  rw [pow_succ, pow_mul, hp, Kap.ρ1, h1', mul_one, one_add_pow _ (epM_mul _), add_eq_left]
  exact Matrix.ext fun i j => (finAm l G0.frame n x m k.g).2.2.2.2.1 _

private theorem epsD_one (l : ℕ) [Fact l.Prime] (F : GFrame l) (n : ℕ) (x : NP F n)
    (k : Kap x) (m : ℕ) (g : F.Γ) (hg : PadicInt.toZMod ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) = 1) : epsD k (x.Am m) g = 1 := by
  have hl : (l : DD (x.Am m) k.g) = 0 := by
    have := (finAm l F n x m k.g).2.2.2.2.1 1
    rwa [nsmul_eq_mul, mul_one] at this
  have : ((F.ε g : ℤ_[l]ˣ) : ℤ_[l]) - 1 ∈ RingHom.ker (PadicInt.toZMod (p := l)) := by
    rw [RingHom.mem_ker, map_sub, hg, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at this
  obtain ⟨c, hc⟩ := this
  rw [epsD, eq_add_of_sub_eq hc]
  simp [hl]

theorem UpperTheory.V.Pa.descend :
    ∀ (l : ℕ) [Fact l.Prime] (L : Loc) (G0 : Glob l L) (T : TWGrp G0) (n : ℕ) (x : NP G0.frame n) (k : Kap x) (m N : ℕ) (rep' : Representation x.A (T.GN N).Γ (k.EpsilonEtaTensorDual (x.Am m))), (∀ g : G0.G₀, (g : G0.Γ) ∈ PL l T.H.toSubgroup → x.ρ g = 1) → IsAd (T.GN N).frame (fun g => k.ρ1 (x.Am m) ((T.h N).p₀ g)) (fun g => epsD k (x.Am m) ((T.h N).p g)) (k.EpsilonEtaTensorDual (x.Am m)) rep' → ∀ y ∈ Zl rep', y (T.GN N).c = 0 → (∀ j, y (T.ta N j) = 0) → ∃ z ∈ TwZ k (x.Am m), ∀ g : (T.GN N).G₀, (y g : Matrix (Fin n) (Fin n) (DD (x.Am m) k.g)) = z ((T.h N).p₀ g) := by
  intro l _ L G0 T n x k m N rep' hPL had y hy hc hta
  obtain ⟨-, -, f1, -, f2, -, f3, -⟩ := finAm l G0.frame n x m k.g
  obtain ⟨r1, r2, -⟩ := rho1 l G0.frame n x k (x.Am m)
  obtain ⟨-, c2, c3⟩ := lc1 l L (T.GN N) G0 (T.h N) n x k m
  obtain ⟨U, hU⟩ := affine_ker rep' (c3 _ _ rep' c2 had) y hy
  have htriv : ∀ g : (T.GN N).G₀, (T.h N).p g ∈ T.H → k.ρ1 (x.Am m) ((T.h N).p₀ g) = 1 → rep' g = 1 := by
    intro g hg h1
    have h2 : k.ρ1 (x.Am m) ((T.h N).p₀ g⁻¹) = 1 := by
      have := r2 ((T.h N).p₀ g) ((T.h N).p₀ g⁻¹)
      rw [h1, one_mul] at this
      rw [← this, ← map_mul, mul_inv_cancel, map_one]
      exact r1
    refine LinearMap.ext fun Z => Subtype.ext ((had.1 g Z).trans ?_)
    simp only []
    rw [h1, h2, epsD_one l G0.frame n x k m _ (T.H_ε _ hg), one_smul, one_mul, mul_one]
    rfl
  have hker : (T.h N).p.ker ≤ U.toSubgroup := by
    refine (T.ker_le N).trans (Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) U.toOpenSubgroup.isClosed)
    · haveI := U.isNormal'
      refine Subgroup.normalClosure_le_normal ?_
      rintro _ ⟨j, rfl⟩
      refine (hU _).2 ⟨htriv _ (by rw [T.ta_ker]; exact T.H.toSubgroup.one_mem) ?_, hta j⟩
      have : (T.h N).p₀ (T.ta N j) = 1 := Subtype.ext (T.ta_ker N j)
      rw [this]
      exact r1
    · refine iInf₂_le U fun h hh => ?_
      have hη : h ∈ (T.GN N).η.ker := by
        rw [MonoidHom.mem_ker, ← (T.h N).η]
        exact T.H_η _ hh
      obtain ⟨e, he⟩ := rho1_pow_eq_one_pro_l l L G0 T n x k m hPL ((T.h N).p₀ ⟨h, hη⟩) hh
      have h1 : rep' (h ^ l ^ e) = 1 := htriv (⟨h, hη⟩ ^ l ^ e)
        ((T.H.toSubgroup.comap (T.h N).p).pow_mem hh _) (by rw [map_pow]; exact he)
      refine ⟨e + 1, (hU _).2 ⟨?_, ?_⟩⟩
      · rw [pow_succ, pow_mul, map_pow, h1, one_pow]
      · rw [pow_succ, pow_mul, cocycle_pow rep' y hy _ h1]
        exact Subtype.ext (Matrix.ext fun i j => f2 _)
  obtain ⟨Z, z1, z2⟩ := factor_lc rep' y hy (T.h N).p (T.h N).cont (T.h N).surj fun g hg => ((hU g).1 (hker hg)).2
  have hs : ∀ g0 : G0.G₀, ∃ g : (T.GN N).G₀, (T.h N).p₀ g = g0 := by
    intro g0
    obtain ⟨g, hg⟩ := (T.h N).surj g0
    refine ⟨⟨g, ?_⟩, Subtype.ext hg⟩
    rw [MonoidHom.mem_ker, ← (T.h N).η, hg]
    exact g0.2
  have z3 : ∀ g : (T.GN N).G₀, Z ((T.h N).p₀ g : G0.G₀) = y g := fun g => (z2 g).symm
  refine ⟨fun g0 => Z g0, ⟨fun g => (Z g).2, fun i j => ?_, fun g0 h0 => ?_, fun g0 => ?_⟩, fun g => by rw [← z3]⟩
  · exact (adicLC _ _ _ m _ f3).2 ((z1.comp_continuous continuous_subtype_val).comp fun W => W.1 i j)
  · obtain ⟨g, rfl⟩ := hs g0
    obtain ⟨h, rfl⟩ := hs h0
    have e := congrArg Subtype.val (hy.2 g h)
    rw [Submodule.coe_add, had.1 g] at e
    simp only []
    rw [← map_mul, z3, z3, z3, ← map_inv]
    exact e
  · obtain ⟨g, rfl⟩ := hs g0
    have e := ((polZ l (T.GN N).frame _ _ n _ _ _ rep' had).2 y hy hc).1 g
    have e2 : G0.frame.conj ((T.h N).p₀ g) = (T.h N).p₀ ((T.GN N).frame.conj g) := by
      refine Subtype.ext ?_
      show G0.c * (T.h N).p g * G0.c⁻¹ = (T.h N).p ((T.GN N).c * g * (T.GN N).c⁻¹)
      rw [map_mul, map_mul, map_inv, (T.h N).c]
    simp only []
    rw [e2, z3, z3]
    refine e.trans ?_
    show -(epsD k (x.Am m) ((T.h N).p (T.GN N).c) • _) = _
    rw [(T.h N).c]
