import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.ChainRows
import Development.AutomorphicSpectrum.Definitions.NonGaloisLines.TopLine
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CardCocyclesMulInvariantsDiscrete
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousFixingSubgroupEquiv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CardDualZmodModuleEqCard
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.OrthogonalFreeOfPerfectAltZmod
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module GlobalTheory.CompanionTheory.LocDual

noncomputable section

namespace GlobalTheory.CompanionTheory.LocDual.Pair

private theorem exists_injective_zmod_addCircle_torsion (N : ℕ) [NeZero N] :
    ∃ j : ZMod N →+ AddCircle (1 : ℚ), Function.Injective j ∧
      ∀ t : AddCircle (1 : ℚ), N • t = 0 → t ∈ j.range := by
  have hN : (N : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (NeZero.ne N)
  have hf : zmultiplesHom (AddCircle (1 : ℚ)) (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) (N : ℤ) = 0 := by
    rw [zmultiplesHom_apply, ← AddCircle.coe_zsmul, AddCircle.coe_eq_zero_iff]
    refine ⟨1, ?_⟩
    rw [zsmul_eq_mul, zsmul_eq_mul]
    push_cast
    field_simp
  refine ⟨ZMod.lift N ⟨_, hf⟩, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro k hk
    have hk' : ((k.val : ℤ) : ZMod N) = k := by simp
    rw [← hk', ZMod.lift_coe, zmultiplesHom_apply, ← AddCircle.coe_zsmul,
      AddCircle.coe_eq_zero_iff] at hk
    obtain ⟨m, hm⟩ := hk
    rw [zsmul_eq_mul, zsmul_eq_mul, mul_one] at hm
    have hlt := ZMod.val_lt k
    have hm' : (m : ℚ) * N = k.val := by rw [hm]; push_cast; field_simp
    have hm'' : m * (N : ℤ) = (k.val : ℤ) := by exact_mod_cast hm'
    have hNpos : 0 < (N : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hlt' : (k.val : ℤ) < N := by exact_mod_cast hlt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h | h | h
      · nlinarith
      · exact h
      · nlinarith
    rw [hm0, zero_mul] at hm''
    have hv : k.val = 0 := by exact_mod_cast hm''.symm
    exact (ZMod.val_eq_zero k).1 hv
  · intro t ht
    obtain ⟨r, rfl⟩ := QuotientAddGroup.mk_surjective t
    change N • ((r : ℚ) : AddCircle (1 : ℚ)) = 0 at ht
    rw [← AddCircle.coe_nsmul, AddCircle.coe_eq_zero_iff] at ht
    obtain ⟨m, hm⟩ := ht
    have hm' : (m : ℚ) = N * r := by simpa [zsmul_eq_mul, nsmul_eq_mul] using hm
    refine ⟨(m : ZMod N), ?_⟩
    rw [ZMod.lift_coe]
    change m • (((1 : ℚ) / N : ℚ) : AddCircle (1 : ℚ)) = ((r : ℚ) : AddCircle (1 : ℚ))
    rw [← AddCircle.coe_zsmul]
    congr 1
    rw [zsmul_eq_mul, mul_one_div, div_eq_iff hN, hm']
    ring

theorem mem_of_cup_flip {N : ℕ} [NeZero N] {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    (ψ : Γ →* (ZMod N)ˣ) {M : Type} [AddCommGroup M] [Module (ZMod N) M] [TopologicalSpace M]
    [DiscreteTopology M] (rho : Representation (ZMod N) Γ M)
    (hrho : ReciprocityTheory.Gal.ContAction (rho.comp (MonoidHom.id Γ)))
    (e : ReciprocityTheory.Gal.H2 ((ReciprocityTheory.Gal.charRep ψ).comp (MonoidHom.id Γ)) ≃ₗ[ZMod N] ZMod N)
    (hs : Function.Surjective (ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho).flip)
    (A : AddSubgroup (ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))))
    (hB : ∀ z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)),
      z.1 ∈ ReciprocityTheory.Gal.B1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) → z ∈ A)
    (z : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)))
    (h : ∀ y : ReciprocityTheory.Gal.H1 (rho.comp (MonoidHom.id Γ)),
      (∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0) →
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk z) y = 0) : z ∈ A := by
  classical
  by_contra hz
  let π : ReciprocityTheory.Gal.Z1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+
      ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) :=
    { toFun := fun s => Submodule.Quotient.mk s
      map_zero' := Submodule.Quotient.mk_zero _
      map_add' := fun s t => Submodule.Quotient.mk_add _ }
  have hzA : π z ∉ A.map π := by
    rintro ⟨s, hs', hsz⟩
    apply hz
    have hq : (Submodule.Quotient.mk s :
        ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ))) = Submodule.Quotient.mk z := hsz
    rw [Submodule.Quotient.eq] at hq
    have hq' := Submodule.neg_mem _ hq
    rw [neg_sub] at hq'
    have hmem : z - s ∈ A := hB (z - s) hq'
    have hsum := A.add_mem hmem hs'
    rwa [sub_add_cancel] at hsum
  have hq0 : (QuotientAddGroup.mk (π z) : _ ⧸ A.map π) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]
    exact hzA
  obtain ⟨c, hc⟩ := CharacterModule.exists_character_apply_ne_zero_of_ne_zero hq0
  let c' : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ AddCircle (1 : ℚ) :=
    c.comp (QuotientAddGroup.mk' (A.map π))
  have htors : ∀ h, N • c' h = 0 := by
    intro h
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod N), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨j, hj, hjr⟩ := exists_injective_zmod_addCircle_torsion N
  let φ0 : ReciprocityTheory.Gal.H1 ((ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id Γ)) →+ ZMod N :=
    (AddMonoidHom.ofInjective hj).symm.toAddMonoidHom.comp
      (c'.codRestrict j.range (fun h => hjr _ (htors h)))
  have key : ∀ h, j (φ0 h) = c' h := by
    intro h
    have hh := (AddMonoidHom.ofInjective hj).apply_symm_apply
      (c'.codRestrict j.range (fun h => hjr _ (htors h)) h)
    rw [Subtype.ext_iff, AddMonoidHom.ofInjective_apply] at hh
    exact hh
  let Lm := e.symm.toLinearMap ∘ₗ φ0.toZModLinearMap N
  obtain ⟨y, hy⟩ := hs Lm
  have hval : ∀ s, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y =
      e.symm (φ0 (π s)) := by
    intro s
    have hh := LinearMap.congr_fun hy (Submodule.Quotient.mk s)
    rw [LinearMap.flip_apply] at hh
    rw [hh]
    rfl
  have hyA : ∀ s ∈ A, ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id Γ) hrho (Submodule.Quotient.mk s) y = 0 := by
    intro s hs'
    rw [hval]
    have h0 : φ0 (π s) = 0 := by
      apply hj
      rw [key, map_zero]
      show c (QuotientAddGroup.mk (π s)) = 0
      rw [(QuotientAddGroup.eq_zero_iff _).2 (AddSubgroup.mem_map_of_mem π hs'), map_zero]
    rw [h0, map_zero]
  have hfin := h y hyA
  rw [hval, LinearEquiv.map_eq_zero_iff] at hfin
  apply hc
  have hj0 := congrArg j hfin
  rw [key, map_zero] at hj0
  exact hj0

theorem exists_equiv_dual {n : ℕ} [NeZero n] {M : Type} [AddCommGroup M] [Module (ZMod n) M] [Finite M]
    {M' : Type} [AddCommGroup M'] [Module (ZMod n) M'] [Finite M'] (P : M →+ M' →+ ZMod n)
    (h1 : ∀ x, (∀ y, P x y = 0) → x = 0) (h2 : ∀ y, (∀ x, P x y = 0) → y = 0) :
    ∃ e : M' ≃+ ReciprocityTheory.Gal.TDual (ZMod n) M, ∀ y x, e y x = P x y := by
  classical
  have hfin : ∀ (A : Type) [AddCommGroup A] [Module (ZMod n) A] [Finite A],
      Finite (Module.Dual (ZMod n) A) := fun A _ _ _ => (GlobalTheory.CocycleCount.card_linear_le n A).1
  let f : M' →+ Module.Dual (ZMod n) M :=
    { toFun := fun y => (P.flip y).toZModLinearMap n
      map_zero' := LinearMap.ext fun x => by
        show P x 0 = 0
        exact map_zero (P x)
      map_add' := fun y y' => LinearMap.ext fun x => by
        show P x (y + y') = P x y + P x y'
        exact map_add (P x) y y' }
  let g : M → Module.Dual (ZMod n) M' := fun x => (P x).toZModLinearMap n
  have hf : Function.Injective f := by
    intro y y' hyy
    have hyx : ∀ x, P x (y - y') = 0 := by
      intro x
      have hx := LinearMap.congr_fun hyy x
      change P x y = P x y' at hx
      rw [map_sub, hx, sub_self]
    exact sub_eq_zero.1 (h2 _ hyx)
  have hg : Function.Injective g := by
    intro x x' hxx
    have hxy : ∀ y, P (x - x') y = 0 := by
      intro y
      have hy := LinearMap.congr_fun hxx y
      change P x y = P x' y at hy
      rw [map_sub, AddMonoidHom.sub_apply, hy, sub_self]
    exact sub_eq_zero.1 (h1 _ hxy)
  haveI := hfin M
  haveI := hfin M'
  have c1 := Nat.card_le_card_of_injective f hf
  have c2 := Nat.card_le_card_of_injective g hg
  rw [GlobalTheory.ZModDual.card_dual_eq] at c1 c2
  have hb : Function.Bijective f :=
    hf.bijective_of_nat_card_le (by rw [GlobalTheory.ZModDual.card_dual_eq]; exact c2)
  exact ⟨AddEquiv.ofBijective f hb, fun y x => rfl⟩

theorem double_annihilator : Formalism.GaloisCohomology.LocalTateDualityK → ∀ (D : D7) (l : ℕ) [Fact l.Prime] (K : FinExt l), ∀ (n : ℕ) (χ : ↥(GK K) →* (ZMod (l ^ n))ˣ), 0 < n → (∀ g, ∃ u : ℤ_[l], (u : ℚ_[l]) = ((((D.loc l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) ∧ PadicInt.toZModPow n u = (χ g : ZMod (l ^ n))) → ∀ (W : Type) [AddCommGroup W] [Finite W] (a : ↥(GK K) → W →+ W), (∀ m, a 1 m = m) → (∀ g h m, a (g * h) m = a g (a h m)) → (∀ m, IsLocallyConstant fun g => a g m) → ∀ (W' : Type) [AddCommGroup W'] [Finite W'] (a' : ↥(GK K) → W' →+ W'), (∀ m, a' 1 m = m) → (∀ g h m, a' (g * h) m = a' g (a' h m)) → (∀ m, IsLocallyConstant fun g => a' g m) → ∀ P : W →+ W' →+ ZMod (l ^ n), (∀ x, (∀ y, P x y = 0) → x = 0) → (∀ y, (∀ x, P x y = 0) → y = 0) → (∀ g x y, P (a g x) (a' g y) = (χ g : ZMod (l ^ n)) * P x y) → ∀ S : AddSubgroup (↥(GK K) → W), (∀ m : W, (fun g => a g m - m) ∈ S) → (∀ s ∈ S, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a g (s h))) → ∀ c : ↥(GK K) → W, (IsLocallyConstant c ∧ ∀ g h, c (g * h) = c g + a g (c h)) → (∀ c' : ↥(GK K) → W', (IsLocallyConstant c' ∧ ∀ g h, c' (g * h) = c' g + a' g (c' h)) → (∀ s ∈ S, (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (s g) (a' g (c' h)))) → (∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h, (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (c g) (a' g (c' h)))) → c ∈ S := by
  intro hT D l _ K n χ hn hχ W _ _ a h1 hmul hlc W' _ _ a' h1' hmul' hlc' P hP1 hP2 hP S hBS hS c hc H
  have hne : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  have mW : Module (ZMod (l ^ n)) W := AddCommGroup.zmodModule fun x => hP1 _ fun y => by
    rw [map_nsmul, AddMonoidHom.nsmul_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have mW' : Module (ZMod (l ^ n)) W' := AddCommGroup.zmodModule fun y => hP2 _ fun x => by
    rw [map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  letI tW' : TopologicalSpace W' := ⊥
  haveI dW' : DiscreteTopology W' := ⟨rfl⟩
  haveI hK : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  let φ : ↥(GK K) ≃* Formalism.GaloisCohomology.GK l K.1 := IntermediateField.fixingSubgroupEquiv K.1
  have hφ : Continuous φ ∧ Continuous φ.symm :=
    GlobalTheory.fixingSubgroupEquiv_bicontinuous ℚ_[l] (Om l) K.1
  let rho : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) W' :=
    GlobalTheory.CocycleCount.repOfAction _ (fun g => a' (φ.symm g)) (fun m => by rw [map_one, h1'])
      (fun g h m => by rw [map_mul, hmul'])
  have hrho_apply : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (m : W'), rho g m = a' (φ.symm g) m := fun _ _ => rfl
  have hrho : ReciprocityTheory.Gal.ContAction rho :=
    continuous_prod_of_discrete_right.2 fun m => (hlc' m).continuous.comp hφ.2
  obtain ⟨⟨e⟩, -, -, hb, -⟩ := hT l K.1 K.2 n W' rho hn hrho
  let ψ := Formalism.GaloisCohomology.cycK l K.1 n
  have hψ : ∀ g : ↥(GK K), ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) = (χ g : ZMod (l ^ n)) := by
    intro g
    obtain ⟨u, hu1, hu2⟩ := hχ g
    have hcyc : (D.loc l).χQ = GlobalTheory.Cyc.cycChar l :=
      GlobalTheory.Cyc.TwistLift.isCyc_unique (D.loc l).χQ_cyc (GlobalTheory.Cyc.isCyc_cycChar l)
    rw [(D.loc l).PD_χ K g, hcyc] at hu1
    have hu : u = ((cyclotomicCharacter (PadicAlgCl l) l
        (MulSemiringAction.toRingAut (GQ l) (PadicAlgCl l) g.1) : ℤ_[l]ˣ) : ℤ_[l]) := Subtype.ext hu1
    rw [← hu2, hu]
    rfl
  obtain ⟨E, hE⟩ := exists_equiv_dual (n := l ^ n) P.flip hP2 hP1
  have hE' : ∀ x y, E x y = P x y := fun x y => hE x y
  let τ : Representation (ZMod (l ^ n)) (Formalism.GaloisCohomology.GK l K.1) (ReciprocityTheory.Gal.TDual (ZMod (l ^ n)) W') :=
    (ReciprocityTheory.Gal.twDual ψ rho).comp (MonoidHom.id _)
  have hEq : ∀ (g : ↥(GK K)) (x : W), E (a g x) = τ (φ g) (E x) := by
    intro g x
    apply ReciprocityTheory.Gal.TDual.ext
    intro y
    change E (a g x) y = ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * E x (rho (φ g)⁻¹ y)
    have hy : a' g (a' g⁻¹ y) = y := by rw [← hmul', mul_inv_cancel, h1']
    have hinv : rho (φ g)⁻¹ y = a' g⁻¹ y := by
      rw [hrho_apply, map_inv, MulEquiv.symm_apply_apply]
    rw [hE', hE', hψ, hinv, ← hP, hy]
  have ev : ∀ (g : Formalism.GaloisCohomology.GK l K.1) (t : ReciprocityTheory.Gal.TDual (ZMod (l ^ n)) W') (y : W'),
      t y = P (E.symm t) y := fun g t y => by rw [← hE', E.apply_symm_apply]
  let toS : ReciprocityTheory.Gal.Z1 τ →+ (↥(GK K) → W) :=
    AddMonoidHom.mk' (fun z g => E.symm (z.1 (φ g))) (fun z z' => by funext g; simp)
  have toS_apply : ∀ z g, toS z g = E.symm (z.1 (φ g)) := fun _ _ => rfl
  let A : AddSubgroup (ReciprocityTheory.Gal.Z1 τ) := S.comap toS
  have lift : ∀ s : ↥(GK K) → W, (IsLocallyConstant s ∧ ∀ g h, s (g * h) = s g + a g (s h)) →
      ∃ z : ReciprocityTheory.Gal.Z1 τ, toS z = s := by
    intro s hs
    refine ⟨⟨fun g => E (s (φ.symm g)), ((hs.1.comp E).continuous).comp hφ.2, fun g h => ?_⟩,
      funext fun g => ?_⟩
    · have := hEq (φ.symm g) (s (φ.symm h))
      rw [MulEquiv.apply_symm_apply] at this
      change E (s (φ.symm (g * h))) = E (s (φ.symm g)) + τ g (E (s (φ.symm h)))
      rw [map_mul, hs.2, map_add, this]
    · rw [toS_apply, AddEquiv.symm_apply_eq]
      change E (s (φ.symm (φ g))) = _
      rw [MulEquiv.symm_apply_apply]
  obtain ⟨zc, hcz⟩ := lift c hc
  have hBA : ∀ z : ReciprocityTheory.Gal.Z1 τ, z.1 ∈ ReciprocityTheory.Gal.B1 τ → z ∈ A := by
    intro z hz
    obtain ⟨t, ht⟩ := (ReciprocityTheory.Gal.mem_coboundaries1 _ _).1 hz
    change toS z ∈ S
    have : toS z = fun g => a g (E.symm t) - E.symm t := by
      funext g
      rw [toS_apply, ht, AddEquiv.symm_apply_eq, map_sub, hEq, AddEquiv.apply_symm_apply]
    rw [this]
    exact hBS _
  have key : ∀ (x : ReciprocityTheory.Gal.Z1 τ) (y : ReciprocityTheory.Gal.Z1 (rho.comp (MonoidHom.id _))),
      ReciprocityTheory.Gal.cupH1H1TwistedDual ψ rho (MonoidHom.id _) (hrho.comp' continuous_id)
        (Submodule.Quotient.mk x) (Submodule.Quotient.mk y) = 0 ↔
      ∃ f : ↥(GK K) → ZMod (l ^ n), IsLocallyConstant f ∧ ∀ g h,
        (χ g : ZMod (l ^ n)) * f h - f (g * h) + f g = P (toS x g) (a' g (y.1 (φ h))) := by
    intro x y
    constructor
    · intro h0
      obtain ⟨f, hf, hd⟩ := (ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem _ _).1 ((Submodule.Quotient.mk_eq_zero _).1 h0)
      refine ⟨fun g => f (φ g), (IsLocallyConstant.iff_continuous _).2 (hf.comp hφ.1), fun g h => ?_⟩
      have h2 := congrFun hd (φ g, φ h)
      have h3 : ((ψ (φ g) : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f (φ h) - f (φ g * φ h) + f (φ g) =
          (x.1 (φ g)) (rho (φ g) (y.1 (φ h))) := h2
      rw [hψ, ← map_mul, hrho_apply, MulEquiv.symm_apply_apply, ev (φ g)] at h3
      exact h3
    · rintro ⟨f, hf, hd⟩
      refine (Submodule.Quotient.mk_eq_zero _).2 ((ReciprocityTheory.Gal.separated_dvr_second_cohomology_mem _ _).2
        ⟨fun g => f (φ.symm g), hf.continuous.comp hφ.2, funext fun p => ?_⟩)
      obtain ⟨g, h⟩ := p
      have h3 := hd (φ.symm g) (φ.symm h)
      rw [← hψ, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, ← map_mul] at h3
      change ((ψ g : (ZMod (l ^ n))ˣ) : ZMod (l ^ n)) * f (φ.symm h) - f (φ.symm (g * h)) + f (φ.symm g) =
          (x.1 g) (rho g (y.1 h))
      rw [ev g, hrho_apply]
      have := toS_apply x (φ.symm g)
      rw [MulEquiv.apply_symm_apply] at this
      rw [← this]
      exact h3
  have hmain : zc ∈ A := by
    refine mem_of_cup_flip ψ rho (hrho.comp' continuous_id) e hb.2 A hBA zc fun y hy => ?_
    induction y using Submodule.Quotient.induction_on with | H y =>
    have hc' : IsLocallyConstant (fun g => y.1 (φ g)) ∧
        ∀ g h, y.1 (φ (g * h)) = y.1 (φ g) + a' g (y.1 (φ h)) := by
      refine ⟨(IsLocallyConstant.iff_continuous _).2 (y.2.1.comp hφ.1), fun g h => ?_⟩
      have := y.2.2 (φ g) (φ h)
      rw [map_mul]
      refine this.trans ?_
      change _ + rho (φ g) _ = _
      rw [hrho_apply, MulEquiv.symm_apply_apply]
    have hz := H (fun g => y.1 (φ g)) hc' (fun s hs => ?_)
    · refine (key zc y).2 ?_
      rw [hcz]
      obtain ⟨f, hf, hd⟩ := hz
      exact ⟨f, hf, hd⟩
    · obtain ⟨zs, hzs⟩ := lift s (hS s hs)
      have hA : zs ∈ A := by
        change toS zs ∈ S
        rw [hzs]
        exact hs
      obtain ⟨f, hf, hd⟩ := (key zs y).1 (hy zs hA)
      rw [hzs] at hd
      exact ⟨f, hf, hd⟩
  have hmem : toS zc ∈ S := hmain
  rwa [hcz] at hmem

end GlobalTheory.CompanionTheory.LocDual.Pair
