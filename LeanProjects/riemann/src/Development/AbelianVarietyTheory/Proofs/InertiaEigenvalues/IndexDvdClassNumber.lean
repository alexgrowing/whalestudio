import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GlobalCore
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRingClassHost

noncomputable section

open Formalism Formalism.MainNotions Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Module GlobalTheory.Pass GlobalTheory.Cut

namespace GlobalTheory.UnramHom

section Algebra

variable {O M G Γ : Type} [CommRing O] [AddCommGroup M] [Module O M] [Group G] [CommGroup Γ]

def asHom (f : G → M) (hf : ∀ a b, f (a * b) = f a + f b) : G →* Multiplicative M :=
  MonoidHom.mk' (fun g => Multiplicative.ofAdd (f g)) fun a b => by rw [hf, ofAdd_add]

theorem length_le {l : ℕ} (hl : l.Prime) (hu : ∀ p : ℕ, p.Prime → p ≠ l → IsUnit (p : O)) (L : ℕ∞)
    (hL : Module.length O (Submodule.torsionBy O M (l : O)) ≤ L) (π : G →* Γ) (hπ : Function.Surjective π) (n : ℕ) :
    n ≠ 0 → ∀ N : Subgroup Γ, N.index = n → ∀ C : Submodule O (G → M), (∀ f ∈ C, ∀ a b, f (a * b) = f a + f b) →
      (∀ f ∈ C, ∀ a, π a ∈ N → f a = 0) → Module.length O C ≤ L * (padicValNat l n : ℕ∞) := by
  have := Fact.mk hl
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro hn N hN C hadd hker
  by_cases h1 : n = 1
  · have hT : N = ⊤ := Subgroup.index_eq_one.1 (hN.trans h1)
    have : C = ⊥ := (Submodule.eq_bot_iff _).2 fun f hf => funext fun a => hker f hf a (hT ▸ trivial)
    subst this
    simp
  obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd h1
  have := Fact.mk hp
  have : N.FiniteIndex := ⟨hN ▸ hn⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Γ ⧸ N) p (hN ▸ hpn :)
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  obtain ⟨a, rfl⟩ := hπ y
  let N' : Subgroup Γ := (Subgroup.zpowers (π a : Γ ⧸ N)).comap (QuotientGroup.mk' N)
  have hi : p * N'.index = n := by
    rw [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N), ← hx, ← Nat.card_zpowers,
      Subgroup.card_mul_index, ← hN]
    rfl
  have hi0 : N'.index ≠ 0 := fun h => hn (by rw [← hi, h, mul_zero])
  have hlt : N'.index < n := by
    rw [← hi]
    exact lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hi0) hp.one_lt
  let ev : C →ₗ[O] M := (LinearMap.proj a).comp C.subtype
  let C' : Submodule O (G → M) := (LinearMap.ker ev).map C.subtype
  have hC' := ih _ hlt hi0 N' rfl C' (by rintro _ ⟨f, -, rfl⟩; exact hadd f f.2) (by
    rintro _ ⟨f, hf, rfl⟩ b ⟨k, hk⟩
    have hf' : asHom f.1 (hadd f f.2) a = 1 := congrArg Multiplicative.ofAdd (LinearMap.mem_ker.1 hf)
    have h2 : π ((a ^ k)⁻¹ * b) ∈ N := by
      rw [map_mul, map_inv, map_zpow]
      exact QuotientGroup.eq.1 hk
    have h3 : asHom f.1 (hadd f f.2) ((a ^ k)⁻¹ * b) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_mul, map_inv, map_zpow, hf', one_zpow, inv_one, one_mul] at h3
    exact congrArg Multiplicative.toAdd h3)
  have hk : Module.length O (LinearMap.ker ev) = Module.length O C' :=
    (Submodule.equivMapOfInjective _ C.injective_subtype _).length_eq
  have hr : LinearMap.range ev ≤ Submodule.torsionBy O M (p : O) := by
    rintro _ ⟨f, rfl⟩
    have h2 : π (a ^ p) ∈ N := by
      rw [← QuotientGroup.eq_one_iff, map_pow, QuotientGroup.mk_pow, ← hx, pow_orderOf_eq_one]
    have h3 : asHom f.1 (hadd f f.2) (a ^ p) = 1 := congrArg Multiplicative.ofAdd (hker f f.2 _ h2)
    rw [map_pow] at h3
    rw [Submodule.mem_torsionBy_iff, Nat.cast_smul_eq_nsmul]
    exact congrArg Multiplicative.toAdd h3
  have hsum : Module.length O C = Module.length O (LinearMap.ker ev) + Module.length O (LinearMap.range ev) :=
    Module.length_eq_add_of_exact (LinearMap.ker ev).subtype ev.rangeRestrict (Submodule.injective_subtype _)
      ev.surjective_rangeRestrict (by
        rw [LinearMap.exact_iff, LinearMap.ker_rangeRestrict, Submodule.range_subtype])
  have hr' := Module.length_le_of_injective (Submodule.inclusion hr) (Submodule.inclusion_injective hr)
  rw [hsum, hk, ← hi, padicValNat.mul hp.ne_zero hi0, Nat.cast_add, mul_add, add_comm (L * _)]
  refine add_le_add hC' (hr'.trans ?_)
  by_cases hpl : p = l
  · subst hpl
    rwa [padicValNat_self, Nat.cast_one, mul_one]
  · have : Submodule.torsionBy O M (p : O) = ⊥ := (Submodule.eq_bot_iff _).2 fun m hm =>
      ((hu p hp hpl).smul_eq_zero).1 ((Submodule.mem_torsionBy_iff _ _).1 hm)
    rw [this]
    simp

theorem length_torsionBy_le {O : Type} [CommRing O] [IsDomain O] {a : O} (ha : a ≠ 0) :
    Module.length O (Submodule.torsionBy O (KOG O 1) a) ≤ Module.length O (O ⧸ Ideal.span {a}) := by
  have ha' : algebraMap O (FractionRing O) a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O _)).2 ha
  let u : KOG O 1 := Submodule.Quotient.mk fun _ => (algebraMap O (FractionRing O) a)⁻¹
  have hu : a • u = 0 := by
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    refine ⟨fun _ => 1, funext fun j => ?_⟩
    simp [Algebra.smul_def, ha']
  let g : (O ⧸ Ideal.span {a}) →ₗ[O] Submodule.torsionBy O (KOG O 1) a :=
    Submodule.liftQ _ (LinearMap.toSpanSingleton O _ ⟨u, hu⟩) (by
      rw [Ideal.span_le, Set.singleton_subset_iff]
      exact Subtype.ext hu)
  refine Module.length_le_of_surjective g ?_
  rintro ⟨m, hm⟩
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ m
  rw [Submodule.mem_torsionBy_iff, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hm
  obtain ⟨c, hc⟩ := hm
  refine ⟨Submodule.Quotient.mk (c 0), Subtype.ext ?_⟩
  show c 0 • u = _
  rw [← Submodule.Quotient.mk_smul]
  congr 1
  funext j
  obtain rfl : j = 0 := Subsingleton.elim _ _
  have h0 : algebraMap O (FractionRing O) (c 0) = a • x 0 := congrFun hc 0
  rw [Pi.smul_apply, Algebra.smul_def, h0, Algebra.smul_def]
  field_simp

end Algebra

section Galois

open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr GlobalTheory.HeckeGal GlobalTheory.Mem.UnitIndex Filter

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

theorem eq_one_of_class [IsTotallyComplex E] {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art)
    {B : Type} [CommGroup B] [TopologicalSpace B] [DiscreteTopology B] (φ : G E Ω →* B) (hφ : Continuous φ)
    (A : HeightOneSpectrum (𝓞 E) → ValuationSubring Ω) (hA : ∀ v, IsPlaceOver (A v) v)
    (hI : ∀ v, ∀ σ ∈ Ine (F := E) (A v), φ σ = 1) (σ : G E Ω)
    (hσ : toAb E Ω σ ∈ (classHom E).ker.map art) : φ σ = 1 := by
  obtain ⟨x, hx, e⟩ := hσ
  let ψ : Ideles E →* B := (liftAb φ hφ).comp art
  have hψ : Continuous ψ := (continuous_liftAb φ hφ).comp ha.quot.continuous
  have ho : IsOpen (ψ.ker : Set (Ideles E)) := (isOpen_discrete {1}).preimage hψ
  have hfin : Finite ψ.range := by
    refine ((isCompact_range hφ).finite_of_discrete.subset ?_).to_subtype
    rintro _ ⟨y, rfl⟩
    obtain ⟨τ, hτ⟩ := toAb_surjective (art y)
    exact ⟨τ, by rw [MonoidHom.comp_apply, ← hτ, liftAb_toAb]⟩
  have hu : ∀ v x, IsUnitAt v x → ψ (localIdele E v x) = 1 := fun v y hy => by
    obtain ⟨τ, hτ, e⟩ := (ha.ine v (A v) (hA v) _).1 ⟨y, hy, rfl⟩
    rw [MonoidHom.comp_apply, ← e, liftAb_toAb, hI v τ hτ]
  have hle : unitIdl E ⊔ (diagUnits E).range ≤ ψ.ker := by
    refine sup_le (fun b hb => ?_) ?_
    · have e1 : ψ (finPartI E b) = ψ b := congrArg Subtype.val (GlobalTheory.RingCls.map_finPartI ψ.rangeRestrict b)
      rw [MonoidHom.mem_ker, ← e1]
      refine (ψ.ker.isClosed_of_isOpen ho).mem_of_tendsto
        (GlobalTheory.Mem.LocTriv.tendsto_part (finPartI_mem_unitIdl.2 hb) fun _ => rfl) (Eventually.of_forall fun S => ?_)
      refine Subgroup.prod_mem _ fun v _ => ?_
      exact hu v _ (hb v)
    · rintro _ ⟨k, rfl⟩
      have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hk, map_one]
  have := MonoidHom.mem_ker.1 (hle (ker_classHom_le E hx))
  rwa [MonoidHom.comp_apply, e, liftAb_toAb] at this

omit [IsAlgClosure E Ω] in

theorem index_dvd_classNumber {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) :
    ((classHom E).ker.map art).index ∣ classNumber E := by
  refine (Subgroup.index_map_dvd _ ha.quot.surjective).trans ?_
  rw [Subgroup.index_ker, classNumber, ← Nat.card_eq_fintype_card]
  exact Subgroup.card_subgroup_dvd_card _

end Galois

theorem wkg_one (D : D7) (i : D.nd.Loc) (g : GE D.nd) (m : KOG (D.nd.O i) 1) :
    WKG (chiRatO D.nd i 1) g m = m := by
  have h : chiRatO D.nd i 1 g = chiRatO D.nd i 1 1 := by
    rw [map_one]
    simp [chiRatO, twistM]
  have h2 : WKG (chiRatO D.nd i 1) g = WKG (chiRatO D.nd i 1) 1 := by
    refine Submodule.linearMap_qext _ (LinearMap.ext fun x => ?_)
    exact congrArg (fun X : Matrix (Fin 1) (Fin 1) (D.nd.O i) => (Submodule.Quotient.mk
      (Matrix.toLinAlgEquiv' (X.map (algebraMap (D.nd.O i) (FractionRing (D.nd.O i)))) x) : KOG (D.nd.O i) 1)) h
  rw [h2, map_one]
  rfl

theorem length_le_classNumber : GlobalTheory.Published.GlobalArtinReciprocity →
    ∀ (D : D7) (i : D.nd.Loc) (C : Submodule (D.nd.O i) (GE D.nd → KOG (D.nd.O i) 1)),
      C ≤ Z1 (WKG (chiRatO D.nd i 1)) → (∀ v, resIne i C v = ⊥) →
      Module.length (D.nd.O i) ↥C ≤
        lenQ i ((D.nd.l i : ℕ) : D.nd.O i) * ((padicValNat (D.nd.l i) (hE D.host) : ℕ) : ℕ∞) := by
  intro H D i C hC hres
  have : IsCMField D.host.E := D.host.isCMField_hostE
  obtain ⟨art, ha⟩ := H D.host.E D.nd.Om
  have hl : (D.nd.l i).Prime := (D.nd.lPrime i).out
  have hadd : ∀ f ∈ C, ∀ a b, f (a * b) = f a + f b := fun f hf a b => by
    rw [(hC hf).2, wkg_one]
  have hl0 : ((D.nd.l i : ℕ) : D.nd.O i) ≠ 0 := fun h => by
    have h1 := congrArg (algebraMap (D.nd.O i) (FractionRing (D.nd.O i))) h
    rw [map_natCast, map_zero, ← map_natCast (D.nd.embK i), map_eq_zero] at h1
    exact hl.ne_zero (Nat.cast_eq_zero.1 h1)
  have hu : ∀ p : ℕ, p.Prime → p ≠ D.nd.l i → IsUnit (p : D.nd.O i) := fun p hp hpl => by
    have h1 : IsUnit (p : ℤ_[D.nd.l i]) :=
      PadicInt.isUnit_iff.2 (PadicInt.norm_natCast_eq_one_iff.2 ((Nat.coprime_primes hl hp).2 hpl.symm))
    simpa using h1.map (algebraMap ℤ_[D.nd.l i] (D.nd.O i))
  have hd := index_dvd_classNumber ha
  have hh : classNumber D.host.E ≠ 0 := classNumber_ne_zero _
  refine (length_le hl hu _ (length_torsionBy_le hl0) (GlobalTheory.HeckeGal.toAb D.host.E D.nd.Om)
    GlobalTheory.HeckeGal.toAb_surjective _ (ne_zero_of_dvd_ne_zero hh hd) _ rfl C hadd fun f hf σ hσ => ?_).trans ?_
  · refine congrArg Multiplicative.toAdd (eq_one_of_class ha (asHom f (hadd f hf)) (hC hf).1 D.nd.plOm.1 D.nd.plOm.2
      (fun v τ hτ => ?_) σ hσ)
    have h1 : LinearMap.funLeft (D.nd.O i) (KOG (D.nd.O i) 1) Subtype.val f ∈ resIne i C v := ⟨f, hf, rfl⟩
    rw [hres v, Submodule.mem_bot] at h1
    exact congrArg Multiplicative.ofAdd (congrFun h1 ⟨τ, hτ⟩)
  · refine mul_le_mul_right (Nat.cast_le.2 ?_) _
    exact (padicValNat_dvd_iff_le hh).1 (pow_padicValNat_dvd.trans hd)

end GlobalTheory.UnramHom

end
