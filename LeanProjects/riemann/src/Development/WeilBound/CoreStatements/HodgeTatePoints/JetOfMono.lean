import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ToFirst
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPowEqFractionRingOfPderivEqZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.IsLocalRingOfAug
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TjEqZeroIff
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCharts
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1 GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace PositivityTheory.HtPt.Cg

open IsLocalRing

theorem spMap_comp' {k A B C : Type} [CommRing k] [CommRing A] [CommRing B] [CommRing C] [Algebra k A] [Algebra k B]
    [Algebra k C] (f : A →ₐ[k] B) (g : B →ₐ[k] C) :
    spMap (g : B →+* C) ≫ spMap (f : A →+* B) = spMap (g.comp f : A →+* C) := by
  rw [← Spec.map_comp]; rfl

section
variable {k : Type} [Field k] {Z : Scheme.{0}} {π : Z ⟶ Sp k} {κ : Type}

def UnivJet (π : Z ⟶ Sp k) (e : Sp k ⟶ Z) {m : ℕ} (x : Sp (Jet k κ m) ⟶ Z) : Prop :=
  ∀ (B : Type) [CommRing B] [Algebra k B] (aug : B →ₐ[k] k), RingHom.ker aug ^ (m + 1) = ⊥ →
    ∀ y : Sp B ⟶ Z, y ≫ π = spMap (algebraMap k B) → spMap (aug : B →+* k) ≫ y = e →
      ∃! χ : Jet k κ m →ₐ[k] B, aug.comp χ = jetAug ∧ y = spMap (χ : Jet k κ m →+* B) ≫ x

theorem jet_of_mono {e : Sp k ⟶ Z} {m : ℕ} {x : Sp (Jet k κ m) ⟶ Z} (hu : UnivJet π e x)
    (hxa : spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x = e)
    {O : Type} [CommRing O] [Algebra k O] (s : Sp O ⟶ Z) [Mono s] (hs : s ≫ π = spMap (algebraMap k O))
    (ε : O →ₐ[k] k) (hε : spMap (ε : O →+* k) ≫ s = e) (τ : O →ₐ[k] Jet k κ m)
    (hτ : spMap (τ : O →+* Jet k κ m) ≫ s = x) :
    Function.Surjective τ ∧ ∀ a, τ a = 0 ↔ a ∈ RingHom.ker ε ^ (m + 1) := by
  have canc : ∀ {A : Type} [CommRing A] [Algebra k A] (f f' : O →ₐ[k] A),
      spMap (f : O →+* A) ≫ s = spMap (f' : O →+* A) ≫ s → f = f' := by
    intro A _ _ f f' h
    have h3 := Spec.map_injective ((cancel_mono s).1 h)
    ext a
    exact congrArg (fun q => q.hom a) h3
  let aJ : Jet k κ m →ₐ[k] k := jetAug
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow (R := k) κ m
  have haug : aJ.comp τ = ε := canc _ _ (by rw [← spMap_comp', Category.assoc, hτ, hxa, hε])
  set I : Ideal O := RingHom.ker ε ^ (m + 1) with hI
  have hkill : ∀ a ∈ I, τ a = 0 := by
    intro a ha
    have hle : RingHom.ker ε ≤ (RingHom.ker aJ).comap τ := fun c hc => by
      show aJ (τ c) = 0
      rw [← AlgHom.comp_apply, haug]; exact hc
    have h2 := Ideal.le_comap_pow τ (m + 1) (Ideal.pow_right_mono hle (m + 1) ha)
    rw [hJ] at h2
    simpa using h2
  have hε0 : ∀ a ∈ I, ε a = 0 := fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha
  let aA : (O ⧸ I) →ₐ[k] k := Ideal.Quotient.liftₐ I ε hε0
  have haA : aA.comp (Ideal.Quotient.mkₐ k I) = ε := by ext a; rfl
  have hA : RingHom.ker aA ^ (m + 1) = ⊥ := by
    have hle : RingHom.ker aA ≤ (RingHom.ker ε).map (Ideal.Quotient.mk I) := by
      intro c hc
      obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective c
      exact Ideal.mem_map_of_mem _ hc
    rw [← le_bot_iff]
    refine (Ideal.pow_right_mono hle _).trans ?_
    rw [← Ideal.map_pow, ← hI, Ideal.map_quotient_self]
  obtain ⟨ψ, ⟨h1, h2⟩, -⟩ := hu (O ⧸ I) aA hA (spMap (Ideal.Quotient.mkₐ k I : O →+* O ⧸ I) ≫ s)
    (by rw [Category.assoc, hs, spMap_comp_alg]) (by rw [← Category.assoc, spMap_comp', haA, hε])
  have hψτ : ψ.comp τ = Ideal.Quotient.mkₐ k I :=
    canc _ _ (by rw [← spMap_comp', Category.assoc, hτ, h2])
  let τ' : (O ⧸ I) →ₐ[k] Jet k κ m := Ideal.Quotient.liftₐ I τ hkill
  have hτ' : τ'.comp (Ideal.Quotient.mkₐ k I) = τ := by ext a; rfl
  have haτ' : aJ.comp τ' = aA := by
    refine Ideal.Quotient.algHom_ext k ?_
    rw [AlgHom.comp_assoc, hτ', haug, haA]
  have hid : τ'.comp ψ = AlgHom.id k _ := by
    refine (hu (Jet k κ m) aJ hJ x (by rw [← hτ, Category.assoc, hs, spMap_comp_alg]) hxa).unique
      ⟨?_, ?_⟩ ⟨rfl, ?_⟩
    · rw [← AlgHom.comp_assoc, haτ', h1]
    · rw [← spMap_comp', Category.assoc, ← h2, ← Category.assoc, spMap_comp', hτ', hτ]
    · exact (Category.id_comp x).symm.trans (congrArg (· ≫ x) (Spec.map_id _).symm)
  refine ⟨fun c => ?_, fun a => ⟨fun ha => ?_, hkill a⟩⟩
  · obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (ψ c)
    refine ⟨a, ?_⟩
    have := AlgHom.congr_fun hid c
    rw [AlgHom.comp_apply, ← ha] at this
    exact this
  · have := AlgHom.congr_fun hψτ a
    rw [AlgHom.comp_apply, ha, map_zero] at this
    exact Ideal.Quotient.eq_zero_iff_mem.1 this.symm

theorem stalk_jet {e : Sp k ⟶ Z} (he : e ≫ π = 𝟙 _) {m : ℕ} {x : Sp (Jet k κ m) ⟶ Z} (hu : UnivJet π e x)
    (hx : x ≫ π = spMap (algebraMap k _))
    (hxa : spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x = e)
    (b : Z) (hb : e (closedPoint k) = b) [alg : Algebra k (Z.presheaf.stalk b)]
    (hs : Z.fromSpecStalk b ≫ π = spMap (algebraMap k (Z.presheaf.stalk b))) :
    ∃ τ : Z.presheaf.stalk b →ₐ[k] Jet k κ m,
      spMap (τ : Z.presheaf.stalk b →+* Jet k κ m) ≫ Z.fromSpecStalk b = x ∧ Function.Surjective τ ∧
        ∀ a, τ a = 0 ↔ a ∈ maximalIdeal (Z.presheaf.stalk b) ^ (m + 1) := by
  let aJ : Jet k κ m →ₐ[k] k := jetAug
  have hJ : RingHom.ker aJ ^ (m + 1) = ⊥ := Chart.ker_jetAug_pow (R := k) κ m
  have := GlobalTheory.StalkJet.isLocalRing_of_aug aJ hJ
  have hxb : x (closedPoint _) = b := by
    have : IsLocalHom (aJ : Jet k κ m →+* k) :=
      IsLocalHom.of_surjective _ (fun c => ⟨algebraMap _ _ c, aJ.commutes c⟩)
    rw [← hb, ← hxa, ← IsLocalRing.comap_closedPoint (aJ : Jet k κ m →+* k)]
    rfl
  let s : Sp (Z.presheaf.stalk b) ⟶ Z := Z.fromSpecStalk b
  have : Mono s := inferInstanceAs (Mono (Z.fromSpecStalk b))
  have hs' : s ≫ π = spMap (algebraMap k (Z.presheaf.stalk b)) := hs
  obtain ⟨ε, hε⟩ : ∃ ε : Z.presheaf.stalk b →ₐ[k] k, spMap (ε : Z.presheaf.stalk b →+* k) ≫ s = e := by
    obtain ⟨ε, -, hε⟩ := @GlobalTheory.StalkJet.exists_factor k _ (Over.mk π) b alg hs k _ _ _
      (Over.homMk e (he.trans (Spec.map_id _).symm)) hb
    exact ⟨ε, hε⟩
  obtain ⟨τ, hτ⟩ : ∃ τ : Z.presheaf.stalk b →ₐ[k] Jet k κ m,
      spMap (τ : Z.presheaf.stalk b →+* Jet k κ m) ≫ s = x := by
    obtain ⟨τ, -, hτ⟩ := @GlobalTheory.StalkJet.exists_factor k _ (Over.mk π) b alg hs
      (Jet k κ m) _ _ _ (Over.homMk x hx) hxb
    exact ⟨τ, hτ⟩
  have hker : RingHom.ker ε = maximalIdeal _ :=
    IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective ε (fun c => ⟨algebraMap _ _ c, ε.commutes c⟩))
  have := jet_of_mono hu hxa s hs' ε hε τ hτ
  rw [hker] at this
  exact ⟨τ, hτ, this⟩

theorem tj_eq [Fintype κ] [DecidableEq κ] (m : ℕ) (F : MvPowerSeries κ k) :
    GlobalTheory.JetExpansion.tj m F = psJet m F := by
  rw [psJet, FBIdJet.psTrunc_eq]; rfl

theorem taylor [PerfectField k] (p : ℕ) [Fact p.Prime] [CharP k p] [IsIntegral Z] [LocallyOfFiniteType π]
    [Fintype κ] [DecidableEq κ] {e : Sp k ⟶ Z} (he : e ≫ π = 𝟙 _) (x : ∀ m, Sp (Jet k κ m) ⟶ Z)
    (hu : ∀ m, UnivJet π e (x m)) (hx : ∀ m, x m ≫ π = spMap (algebraMap k _))
    (hxa : ∀ m, spMap ((jetAug : Jet k κ m →ₐ[k] k) : Jet k κ m →+* k) ≫ x m = e)
    (ht : ∀ m, spMap ((jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m) : Jet k κ (m + 1) →+* Jet k κ m) ≫ x (m + 1) = x m)
    (U : Z.Opens) (hU : ∀ m, ⊤ ≤ x m ⁻¹ᵁ U) [Nonempty U] (f : Γ(Z, U)) :
    ∃ F : MvPowerSeries κ k, (∀ m, ((x m).appLE U ⊤ (hU m)).hom f = toΓ _ (psJet m F)) ∧ (F = 0 → f = 0) ∧
      ((∀ q, MvPowerSeries.pderiv k q F = 0) → ∃ r : Z.functionField, r ^ p = (Z.germToFunctionField U).hom f) := by
  obtain ⟨b, hbdef⟩ : ∃ b, e (closedPoint k) = b := ⟨_, rfl⟩
  have hb : b ∈ U := by
    rw [← hbdef, ← hxa 0]
    exact hU 0 (x := _) trivial
  let φ : CommRingCat.of k ⟶ Z.presheaf.stalk b := StructureSheaf.toStalk k (π b) ≫ π.stalkMap b
  let _ : Algebra k (Z.presheaf.stalk b) := φ.hom.toAlgebra
  have hφ : Z.fromSpecStalk b ≫ π = spMap (algebraMap k (Z.presheaf.stalk b)) := by
    rw [← Scheme.SpecMap_stalkMap_fromSpecStalk]
    erw [Spec.fromSpecStalk_eq']
    exact (Spec.map_comp _ _).symm
  have : Algebra.EssFiniteType k (Z.presheaf.stalk b) := by
    have e0 : ∀ p : PrimeSpectrum k, (StructureSheaf.toStalk k p).hom.EssFiniteType := fun p =>
      Algebra.EssFiniteType.of_isLocalization (R := k) ((Spec.structureSheaf k).presheaf.stalk p) p.asIdeal.primeCompl
    exact RingHom.EssFiniteType.comp (e0 (π b)) (LocallyOfFiniteType.stalkMap π b)
  have : IsNoetherianRing (Z.presheaf.stalk b) := Algebra.EssFiniteType.isNoetherianRing k _
  choose τ h1 h2 h3 using fun m => stalk_jet he (hu m) (hx m) (hxa m) b hbdef hφ
  have hc : ∀ m a, jetTrunc (τ (m + 1) a) = τ m a := by
    intro m a
    have e : spMap (((jetTrunc : Jet k κ (m + 1) →ₐ[k] Jet k κ m).comp (τ (m + 1)) :
        Z.presheaf.stalk b →ₐ[k] Jet k κ m) : Z.presheaf.stalk b →+* Jet k κ m) =
        spMap (τ m : Z.presheaf.stalk b →+* Jet k κ m) := by
      rw [← cancel_mono (Z.fromSpecStalk b), h1, ← ht m, ← h1, ← spMap_comp', Category.assoc]
    exact congrArg (fun q => q.hom a) (Spec.map_injective e)
  choose F hF using fun a : Z.presheaf.stalk b =>
    GlobalTheory.JetExpansion.exists_tj (k := k) (κ := κ) (fun m => τ m a) (fun m => hc m a)
  let σ : ∀ m, Z.presheaf.stalk b →ₐ[k] JetR k κ m := τ
  have hF' : ∀ a m, GlobalTheory.JetExpansion.tj m (F a) = σ m a := hF
  let j : Z.presheaf.stalk b →ₐ[k] MvPowerSeries κ k :=
    { toFun := F
      map_one' := GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', map_one, map_one]
      map_mul' := fun a b => GlobalTheory.JetExpansion.tj_ext fun m => by rw [map_mul, hF', hF', hF', map_mul]
      map_zero' := GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', map_zero, map_zero]
      map_add' := fun a b => GlobalTheory.JetExpansion.tj_ext fun m => by rw [map_add, hF', hF', hF', map_add]
      commutes' := fun r => GlobalTheory.JetExpansion.tj_ext fun m => by rw [hF', AlgHom.commutes, AlgHom.commutes] }
  have hj : ∀ m a, GlobalTheory.JetExpansion.tj m (j a) = σ m a := fun m a => hF a m
  have j1 : ∀ (m : ℕ) a, j a ∈ Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ m ↔
      a ∈ maximalIdeal (Z.presheaf.stalk b) ^ m := fun m a => by
    rcases m with _ | m
    · simp
    · rw [← GlobalTheory.JetExpansion.tj_eq_zero_iff, hj]; exact h3 m a
  have j2 : ∀ (m : ℕ) (s : MvPowerSeries κ k), ∃ a, j a - s ∈
      Ideal.span (Set.range (MvPowerSeries.X : κ → MvPowerSeries κ k)) ^ m := fun m s => by
    obtain ⟨a, ha⟩ := h2 m (GlobalTheory.JetExpansion.tj m s)
    refine ⟨a, Ideal.pow_le_pow_right (Nat.le_succ m) ?_⟩
    rw [← GlobalTheory.JetExpansion.tj_eq_zero_iff, map_sub, hj]
    exact sub_eq_zero.2 ha
  have htop : ⊤ ≤ Z.fromSpecStalk b ⁻¹ᵁ U :=
    (Scheme.preimage_eq_top_of_closedPoint_mem _ (by rw [Scheme.fromSpecStalk_closedPoint]; exact hb)).ge
  have hv : valR (A := Z.presheaf.stalk b) (Z.fromSpecStalk b) U f = (Z.presheaf.germ U b hb).hom f := by
    refine (dif_pos htop).trans ?_
    have : (Z.fromSpecStalk b).appLE U ⊤ htop ≫ (Scheme.ΓSpecIso (Z.presheaf.stalk b)).hom =
        Z.presheaf.germ U b hb := by
      rw [Scheme.Hom.appLE, Scheme.fromSpecStalk_app hb]
      simp only [Category.assoc]
      have e : (Spec (Z.presheaf.stalk b)).presheaf.map (homOfLE (le_top : Z.fromSpecStalk b ⁻¹ᵁ U ≤ ⊤)).op ≫
          (Spec (Z.presheaf.stalk b)).presheaf.map (homOfLE htop).op = 𝟙 _ := by
        rw [← Functor.map_comp]; exact CategoryTheory.Functor.map_id _ _
      rw [reassoc_of% e, Iso.inv_hom_id, Category.comp_id]
    exact congrArg (fun q => q.hom f) this
  refine ⟨j ((Z.presheaf.germ U b hb).hom f), fun m => ?_, fun h0 => ?_, fun hd => ?_⟩
  · have e1 : valR (x m) U f = psJet m (j ((Z.presheaf.germ U b hb).hom f)) := by
      rw [← tj_eq, hj, ← hv, ← h1]
      exact (GlobalTheory.ZH.CrdCalc.valR_spMap (τ m : Z.presheaf.stalk b →+* Jet k κ m) _ U htop).2 f
    rw [← e1, valR, dif_pos (hU m)]
    exact (Iso.hom_inv_id_apply (Scheme.ΓSpecIso (CommRingCat.of (Jet k κ m))) _).symm
  · apply germ_injective_of_isIntegral Z b hb
    rw [map_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal _).ne_top,
      Ideal.mem_iInf]
    intro m
    rw [← j1, h0]
    exact zero_mem _
  · obtain ⟨r, hr⟩ := GlobalTheory.CubeFib.exists_pow_eq_fractionRing_of_pderiv_eq_zero k p _ κ j j1 j2 _ hd
    refine ⟨FractionRing.algEquiv (Z.presheaf.stalk b) Z.functionField r, ?_⟩
    rw [← map_pow, hr, AlgEquiv.commutes]
    exact Scheme.algebraMap_germ_eq_germToFunctionField Z hb f

end

end PositivityTheory.HtPt.Cg
