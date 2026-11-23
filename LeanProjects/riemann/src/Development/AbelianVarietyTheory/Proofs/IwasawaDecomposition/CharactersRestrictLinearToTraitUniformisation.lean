import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedUniformization
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.PsiCoordExistsUniqueUpToUnitLocal
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AssociatedPsiCoordinatesOfTauUnits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalBundlePairingCompatiblePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPushEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTorsionMapUniformisationGenericStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjEqAddKummerTorusTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInertiaMovesTameRootStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TameInertiaFixedDvdValuationOrderStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitTauCoordinateAddNsmulFirstVariableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTraitNonlocalTorusExtensionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExtendSplitTorusHomOverDvrStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniformisationTorusMonoAndFactorStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InertiaFixesAbelianPartOfTorsionPointStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionCommutesRingActionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TorusCharacterRestrictionTraitSurjectiveStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToricTorsionUniformisationEqRestrictCharactersStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauForm

open GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues

theorem exists_eq_add_nsmul {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] {F : Type} [Field F]
    {k : ℕ} {ζ : Fˣ} (hζ : IsPrimitiveRoot ζ k) {u v : X}
    (h : ∀ τ : Multiplicative X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd u) = τ (Multiplicative.ofAdd v)) :
    ∃ z : X, v = u + k • z := by
  let b := Module.Free.chooseBasis ℤ X
  have key : ∀ i, ∃ c : ℤ, b.repr (v - u) i = k * c := fun i => by
    let τ : Multiplicative X →* Fˣ := (zpowersHom Fˣ ζ).comp (AddMonoidHom.toMultiplicative (b.coord i).toAddMonoidHom)
    have e : ζ ^ (b.repr u i) = ζ ^ (b.repr v i) := h τ (MonoidHom.ext fun x => by
      show (ζ ^ (b.coord i x.toAdd)) ^ k = 1
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow])
    refine (hζ.zpow_eq_one_iff_dvd _).1 ?_
    rw [map_sub, Finsupp.sub_apply, zpow_sub, e, mul_inv_cancel]
  choose c hc using key
  refine ⟨∑ i, c i • b i, ?_⟩
  rw [← sub_eq_iff_eq_add', ← b.sum_repr (v - u), Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [hc, mul_smul, natCast_zsmul]

section Ord

variable {W : Type} [CommRing W] [IsDomain W] {Γ : Type} [AddCommGroup Γ] (v : LatticeVal W Γ)

theorem val_one : v.toFun 1 = 0 := by
  have := v.map_mul 1 1
  rw [_root_.mul_one] at this
  exact left_eq_add.1 this

theorem val_pow (x : (FractionRing W)ˣ) (k : ℕ) : v.toFun (x ^ k) = k • v.toFun x := by
  induction k with
  | zero => rw [pow_zero, val_one, zero_nsmul]
  | succ k ih => rw [pow_succ, v.map_mul, ih, succ_nsmul]

theorem val_div (x y : (FractionRing W)ˣ) : v.toFun (x / y) = v.toFun x - v.toFun y := by
  rw [eq_sub_iff_add_eq, ← v.map_mul, div_mul_cancel]

theorem exists_unit_of_ord_eq [IsDiscreteValuationRing W] {x y : (FractionRing W)ˣ}
    (h : (ord_vw W).toFun x = (ord_vw W).toFun y) :
    ∃ u : Wˣ, (x : FractionRing W) = algebraMap W (FractionRing W) (u : W) * (y : FractionRing W) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible hϖ (x / y).ne_zero
  have h1 := ord_vw_uniformiser hϖ.ne_zero hϖ.maximalIdeal_eq
  have e : x / y = Units.map (algebraMap W (FractionRing W)).toMonoidHom u * toUnitK ϖ hϖ.ne_zero ^ n :=
    Units.ext (by rw [hu, Units.smul_def, Algebra.smul_def, Units.val_mul, Units.val_zpow_eq_zpow_val]; rfl)
  have hz : (ord_vw W).toFun (toUnitK ϖ hϖ.ne_zero ^ n) = n := by
    obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [zpow_natCast, val_pow, h1]; simp
    · rw [zpow_neg, zpow_natCast, ← one_div, val_div, val_one, val_pow, h1]; simp
  have h0 : n = 0 := by
    have := congrArg (ord_vw W).toFun e
    rw [val_div, h, sub_self, (ord_vw W).map_mul, (ord_vw W).map_unit, hz, zero_add] at this
    exact this.symm
  rw [h0, zpow_zero, _root_.mul_one, div_eq_iff_eq_mul] at e
  exact ⟨u, congrArg Units.val e⟩

end Ord

theorem cubWeil_push {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {S S' : Scheme.{0}} {t : SAB H S}
    {t' : SAB H S'} {f : S' ⟶ S} (m : SABMap t' t f) {k : ℕ} (T : Over S') (s : T.left ⟶ S) (hs : s = T.hom ≫ f)
    {x y : T ⟶ t'.G} {x₁ y₁ : Over.mk s ⟶ t.G} (hx : x₁.left = x.left ≫ m.φ) (hy : y₁.left = y.left ≫ m.φ)
    {z : Γ(T.left, ⊤)ˣ} (h : GlobalTheory.UU.CubWeil t'.cub k x y z) : GlobalTheory.UU.CubWeil t.cub k x₁ y₁ z := by
  subst hs
  obtain rfl : x₁ = toBase m.cart.1.w x := Over.OverMorphism.ext hx
  obtain rfl : y₁ = toBase m.cart.1.w y := Over.OverMorphism.ext hy
  exact GlobalTheory.UU.cubWeil_of_isPullCubical _ _ f t.G t'.G m.cm m.cart.1.w
    (fun T a b => Over.OverMorphism.ext (m.cart.2 T a b _ _ rfl rfl).symm) _ _ _ _ m.lin k T x y z h

theorem dvd_ord_sub {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {R : Type} [CommRing R] [IsDomain R]
    [IsLocalRing R] [CharZero R] {t : SAB H (Sp R)} (P : PELUnif (maximalIdeal R) t) (hR : AdmBase R (maximalIdeal R))
    {W : Type} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W] {t' : SAB H (Sp W)}
    (P' : PELUnif (maximalIdeal W) t') (hW : AdmBase W (maximalIdeal W)) {g : R →+* W} (m : SABMap t' t (spMap g))
    (ρ : P.D.toPre.X →+ P'.D.toPre.X) (gK : FractionRing R →+* FractionRing W)
    (hgK : ∀ r, gK (algebraMap R _ r) = algebraMap W _ (g r))
    {F : Type} [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F]
    (hF : ∀ x, algebraMap (FractionRing R) F x = algebraMap (FractionRing W) F (gK x))
    {k : ℕ} (hk : IsUnit (k : R)) {ϖ : W} (hϖ : Irreducible ϖ) (O : ValuationSubring F) (φ : W →+* O)
    (σ : F →ₐ[FractionRing W] F) (π : F) (hφ : IsLocalHom φ)
    (eφ : ∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w))
    (hσ : ∀ x ∈ O, O.valuation (σ x - x) < 1)
    (hπ : π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ)) (hζ : IsPrimitiveRoot (σ π / π) k)
    (hT : ∀ (τ : Multiplicative P.D.toPre.X →* Fˣ) (τ' : Multiplicative P'.D.toPre.X →* Fˣ)
      (q : QkPt P.D.toPre F k) (q' : QkPt P'.D.toPre F k) (v : Sp F ⟶ t.G.left) (v' : Sp F ⟶ t'.G.left),
      τ' ^ k = 1 → (∀ χ, τ (Multiplicative.ofAdd χ) = τ' (Multiplicative.ofAdd (ρ χ))) →
      q.y = 0 → GlobalTheory.UT.IsTor τ q.g → q'.y = 0 → GlobalTheory.UT.IsTor τ' q'.g →
      GlobalTheory.FlatTors.IsImage P F k q v → GlobalTheory.FlatTors.IsImage P' F k q' v' → v = v' ≫ m.φ)
    {a b : P.D.toPre.X} {x : (FractionRing R)ˣ} {x' : (FractionRing W)ˣ} (hx : IsTauCoord P.D.toPre a b x)
    (hx' : IsTauCoord P'.D.toPre (ρ a) (ρ b) x') :
    (k : ℤ) ∣ (ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x' := by
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkO : IsUnit (k : O) := by simpa using hk.map (φ.comp g)
  have hB := P.D.tau_bimult
  have hB' := P'.D.tau_bimult
  obtain ⟨f, i₁, p₁, s₁, a₁, w₁, c₁⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H R t P hR F k hk1
  obtain ⟨f', i₂, p₂, s₂, a₂, w₂, c₂⟩ := GlobalTheory.T.exists_torsionMap_uniformisation_generic E H W t' P' hW F k hk1
  have hs : jFK (R := R) F ≫ jK R = (TF (R := W) F).hom ≫ spMap g := by
    show spMap _ ≫ spMap _ = (spMap _ ≫ spMap _) ≫ spMap g
    rw [← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun r => (hF _).trans (congrArg _ (hgK r))))
  obtain ⟨e, he⟩ : ∃ e : (TF (R := W) F ⟶ t'.G) ≃* (TF (R := R) F ⟶ t.G), ∀ u, (e u).left = u.left ≫ m.φ :=
    GlobalTheory.LiePull.exists_pushEquiv m.cart (TF (R := W) F) _ hs

  have tor : ∀ (τ' : Multiplicative P'.D.toPre.X →* Fˣ) (q' : QkPt P'.D.toPre F k), τ' ^ k = 1 → q'.y = 0 →
      GlobalTheory.UT.IsTor τ' q'.g → ∀ p : QkPt P.D.toPre F k,
      GlobalTheory.UU.CubWeil t.cub k (e (f' q')) (f p) (unitOn (τ' (Multiplicative.ofAdd (ρ p.y)))) := by
    intro τ' q' h₁ h₂ h₃ p
    obtain ⟨q, h₄, h₅⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB (k := k) (τ'.comp (AddMonoidHom.toMultiplicative ρ))
      (MonoidHom.ext fun χ => DFunLike.congr_fun h₁ _)
    have : f q = e (f' q') := Over.OverMorphism.ext
      ((hT _ τ' q q' _ _ h₁ (fun _ => rfl) h₄ h₅ h₂ h₃ ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl)).trans (he _).symm)
    exact this ▸ w₁ q p _ h₄ h₅
  obtain ⟨p, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 a
  obtain ⟨pb, rfl⟩ := GlobalTheory.TorusExt.exists_qkPt (F := F) GlobalTheory.firstFiveLaws.1.mulN (Or.inl hR.1) hB hk0 b
  obtain ⟨p', hp'⟩ := s₂ (e.symm (f p)) (by rw [← map_pow, p₁, map_one])
  have hp : f p = e (f' p') := by rw [hp', e.apply_symm_apply]
  have π0 : π ≠ 0 := fun h => by
    rw [h, zero_pow hk0, eq_comm, map_eq_zero, map_eq_zero_iff _ (IsFractionRing.injective W _)] at hπ
    exact hϖ.ne_zero hπ
  obtain ⟨z, hz⟩ : ∃ z, p'.y = ρ p.y + k • z := by
    refine exists_eq_add_nsmul (ζ := (hζ.isUnit hk0).unit) (IsPrimitiveRoot.coe_units_iff.1 hζ) fun τ' h₁ => ?_
    obtain ⟨q', h₂, h₃⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor hB' (k := k) τ' h₁
    exact GlobalTheory.ZH.TorusPerp.unitOn_injective ((tor τ' q' h₁ h₂ h₃ p).unique
      (cubWeil_push m (TF (R := W) F) _ hs (he _) (by rw [hp, he]) (w₂ q' p' τ' h₂ h₃)))

  let σR : F →ₐ[FractionRing R] F := { σ.toRingHom with commutes' := fun y => by rw [hF]; exact σ.commutes _ }
  have eφR : ∀ r, ((φ.comp g) r : F) = algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r) := fun r => by
    rw [hF, hgK]; exact eφ _
  obtain ⟨r, hr, -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB σR.toRingHom (RingHom.ext σR.commutes) p
  obtain ⟨r', hr', -⟩ := GlobalTheory.TorusExt.existsUnique_qkExt hB' σ.toRingHom (RingHom.ext σ.commutes) p'
  obtain ⟨τ₁, q₁, -, y₁, t₁, d₁, v₁⟩ := GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint R _ hB F O (φ.comp g) eφR k σR p r hr
    (GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint R _ hB F O (φ.comp g) eφR k hkO σR hσ p)
  obtain ⟨τ₂, q₂, k₂, y₂, t₂, d₂, v₂⟩ := GlobalTheory.T.conj_eq_add_kummer_torusTorsionPoint W _ hB' F O φ eφ k σ p' r' hr'
    (GlobalTheory.T.inertia_fixes_abelianPart_of_torsionPoint W _ hB' F O φ eφ k hkO σ hσ p')
  have hq : f q₁ = e (f' q₂) := by
    have h₁ : f r = e (f' r') := Over.OverMorphism.ext (by
      rw [c₁ σR p r hr, he, c₂ σ p' r' hr', hp, he, Category.assoc])
    rw [a₁ _ _ _ d₁, a₂ _ _ _ d₂, map_mul, ← hp] at h₁
    exact mul_left_cancel h₁
  have hτ : τ₁ (Multiplicative.ofAdd pb.y) = τ₂ (Multiplicative.ofAdd (ρ pb.y)) :=
    GlobalTheory.ZH.TorusPerp.unitOn_injective ((w₁ q₁ pb τ₁ y₁ t₁).unique (hq ▸ tor τ₂ q₂ k₂ y₂ t₂ pb))
  obtain ⟨x'', hx''⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord W P'.D.toPre p'.y (ρ pb.y)
  obtain ⟨xz, hxz⟩ := GlobalTheory.PsiFromTau.exists_isTauCoord W P'.D.toPre z (ρ pb.y)
  obtain ⟨s, s0, sv, sσ⟩ := v₁ _ x hx
  obtain ⟨s', s0', sv', sσ'⟩ := v₂ _ x'' hx''
  have sσ : σ s = _ := sσ
  have dv := GlobalTheory.T.tameInertia_fixed_dvd_valuation_order W F ϖ hϖ k O φ σ π hkO hφ eφ hσ hπ hζ (s / s') (Units.map gK.toMonoidHom x / x'')
    (by rw [map_div₀, sσ, sσ', hτ, mul_div_mul_left _ _ (Units.ne_zero _)])
    (by rw [map_div₀, div_pow, sv, sv', Units.val_div_eq_div_val, map_div₀, map_div₀, hF]; rfl)
  obtain ⟨u, hu⟩ := GlobalTheory.T.exists_unit_tauCoordinate_add_nsmul_first_variable W _ hB' _ z _ k x' xz x'' hx' hxz (hz ▸ hx'')
  rw [val_div, hu, (ord_vw W).map_mul, (ord_vw W).map_unit, (ord_vw W).map_mul, val_pow, zero_add, nsmul_eq_mul,
    ← sub_sub] at dv
  exact (dvd_sub_left (dvd_mul_right _ _)).1 dv

theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] (t : SAB H (Sp R)) (P : PELUnif (maximalIdeal R) t), GlobalTheory.TorRef.IsCN R → P.TorsionIso →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], GlobalTheory.UU.CDVR W → ∀ (g : R →+* W) (hg : Function.Injective g), ¬ IsLocalHom g →
    ∀ (t' : SAB H (Sp W)) (_ : SABMap t' t (spMap g)) (P' : PELUnif (maximalIdeal W) t'),
      ∃ ρ : P.D.toPre.X →ₗ[𝓞 E] P'.D.toPre.X, Function.Surjective ρ ∧
        ∀ (a b : P.D.toPre.X) (x : (FractionRing R)ˣ) (x' : (FractionRing W)ˣ),
          GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P.D.toPre a b x → GlobalTheory.IndefiniteRowSideFullHecke.GeneratorValues.IsTauCoord P'.D.toPre (ρ a) (ρ b) x' →
          ∃ u : Wˣ, IsFractionRing.lift (A := R) (K := FractionRing R)
              (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg) (x : FractionRing R) =
            algebraMap W (FractionRing W) (u : W) * (x' : FractionRing W) := by
  intro E _ _ _ H R _ _ _ t P hR _ W _ _ _ hW g hg hnl t' m P'
  obtain ⟨hn, hi, hc, hz⟩ := hR
  obtain ⟨hd, hc', hz'⟩ := hW
  have hR : AdmBase R (maximalIdeal R) := ⟨hn, inferInstance, hi, hc⟩
  have hW : AdmBase W (maximalIdeal W) := ⟨inferInstance, inferInstance, inferInstance, hc'⟩
  have sc : ∀ {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (u : A →+* B) (v : B →+* C),
      spMap v ≫ spMap u = spMap (v.comp u) := fun u v => (Spec.map_comp _ _).symm
  have pull : ∀ {S S' : Scheme.{0}} (f : S' ⟶ S) (u : SAB H S), ∃ u' : SAB H S', Nonempty (SABMap u' u f) := fun f u => by
    obtain ⟨_, _, _, _, _, n, -⟩ := sabPull proved_CubePullSt f u
    exact ⟨_, ⟨n⟩⟩
  have comp : ∀ {S S' S'' : Scheme.{0}} {u : SAB H S} {u' : SAB H S'} {u'' : SAB H S''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
      {f'' : S'' ⟶ S} (n : SABMap u' u f) (n' : SABMap u'' u' f'), f' ≫ f = f'' →
      ∃ n'' : SABMap u'' u f'', n''.φ = n'.φ ≫ n.φ := by
    rintro _ _ _ _ _ _ _ _ _ n n' rfl
    exact GlobalTheory.ObjMaps.exists_sab_comp n n'
  have cancel : ∀ {S S' S'' : Scheme.{0}} {u : SAB H S} {u' : SAB H S'} {u'' : SAB H S''} {f : S' ⟶ S} {f' : S'' ⟶ S'}
      {f'' : S'' ⟶ S} (n : SABMap u' u f) (n'' : SABMap u'' u f''), f' ≫ f = f'' →
      ∃ n' : SABMap u'' u' f', n''.φ = n'.φ ≫ n.φ := by
    rintro _ _ _ _ _ _ _ _ _ n n' rfl
    exact GlobalTheory.ObjMaps.exists_sab_cancel n n'
  obtain ⟨V, _, _, _, ψ, Ω, _, α, β, hψ, hβ, eα, hT⟩ := GlobalTheory.T.exists_trait_nonlocal_torusExtension' R t.G t.semi W g hnl
  obtain ⟨tV, ⟨mV⟩⟩ := pull (spMap ψ) t
  obtain ⟨_, _, _, _, _, mL, -⟩ := sabPull proved_CubePullSt (spMap ((algebraMap V (FractionRing V)).comp ψ)) t
  obtain ⟨mL', -⟩ := cancel mV mL (sc ψ (algebraMap V (FractionRing V)))
  obtain ⟨tΩ, ⟨n'⟩⟩ := pull (spMap β) t'
  obtain ⟨n'', en⟩ := comp m n' ((sc g β).trans (congrArg spMap eα.symm))
  obtain ⟨n, en'⟩ := cancel mV n'' (sc ψ (α.comp (algebraMap V (FractionRing V))))
  obtain ⟨j, hj, ej⟩ := GlobalTheory.T.extend_splitTorus_hom_over_dvr V tV.G tV.semi _ _ mL'.cart hT Ω α tΩ.G n.φ n.cart _
    (GlobalTheory.TorusPart.PELUnif.torus P' hβ n') inferInstance
  obtain ⟨t₀, ⟨m₀⟩⟩ := pull (spMap (residue V)) tV
  obtain ⟨m₀', e₀⟩ := comp mV m₀ (sc ψ (residue V))
  have h₀ : ∀ x ∈ maximalIdeal R, (residue V).comp ψ x = 0 := GlobalTheory.TorusPart.map_eq_zero_of_isLocalHom _
  obtain ⟨ρ, hρ⟩ := (GlobalTheory.T.uniformisationTorus_mono_and_factor E H R _ t P (ResidueField V) _ 0 (GlobalTheory.TorusPart.map_pow_one_eq_zero h₀) t₀.G _
    m₀'.cart).2 _ (GlobalTheory.TorusPart.pullTorus m₀.cart j) inferInstance
  have hα : Function.Injective (α.comp (algebraMap V (FractionRing V))) :=
    α.injective.comp (IsFractionRing.injective V _)
  refine ⟨{ ρ with map_smul' := GlobalTheory.T.torusCharacterRestriction_commutes_ringAction E H R t P W t' P' V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ },
    GlobalTheory.T.torusCharacterRestriction_trait_surjective E H R t P W t' P' V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ, fun a b x x' hx hx' => ?_⟩
  let gK : FractionRing R →+* FractionRing W := IsFractionRing.lift (A := R) (K := FractionRing R)
    (g := (algebraMap W (FractionRing W)).comp g) ((IsFractionRing.injective W (FractionRing W)).comp hg)
  have hgK : ∀ r, gK (algebraMap R _ r) = algebraMap W _ (g r) := IsFractionRing.lift_algebraMap _
  refine exists_unit_of_ord_eq (x := Units.map gK.toMonoidHom x) ?_
  obtain ⟨l, hl2, hl⟩ : ∃ l : ℕ, 2 ≤ l ∧ IsUnit (l : R) := by
    rcases IsLocalRing.isUnit_or_isUnit_of_isUnit_add (a := (3 : R)) (b := -2) (by norm_num) with h | h
    · exact ⟨3, by norm_num, by simpa using h⟩
    · exact ⟨2, le_rfl, by simpa using h.neg⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  let F := AlgebraicClosure (FractionRing W)
  letI : Algebra (FractionRing R) F := ((algebraMap (FractionRing W) F).comp gK).toAlgebra
  have key : ∀ k : ℕ, IsUnit (k : R) →
      (k : ℤ) ∣ (ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x' := fun k hk => by
    obtain ⟨O, φ, σ, π, h₁, h₂, h₃, h₄, h₅⟩ := GlobalTheory.T.exists_inertia_moves_tame_root W F ϖ hϖ k (by simpa using hk.map g)
    exact dvd_ord_sub P hR P' hW m ρ gK hgK (fun _ => rfl) hk hϖ O φ σ π h₁ h₂ h₃ h₄ h₅
      (GlobalTheory.T.toricTorsion_uniformisation_eq_restrictCharacters E H R t P W t' P' hR hW g m V ψ tV mV Ω _ β hβ tΩ n n' j t₀ m₀ h₀ m₀' ρ hα ej e₀ hρ eα
        (en'.symm.trans en) F O φ h₁ h₂ (fun r => congrArg (algebraMap (FractionRing W) F) (hgK r)) k hk) hx hx'
  rw [← sub_eq_zero]
  refine Int.eq_zero_of_dvd_of_natAbs_lt_natAbs (key (l ^ Int.natAbs
    ((ord_vw W).toFun (Units.map gK.toMonoidHom x) - (ord_vw W).toFun x')) (by simpa using hl.pow _)) ?_
  rw [Int.natAbs_natCast]
  exact Nat.lt_pow_self (by omega)

end GlobalTheory.TauForm
