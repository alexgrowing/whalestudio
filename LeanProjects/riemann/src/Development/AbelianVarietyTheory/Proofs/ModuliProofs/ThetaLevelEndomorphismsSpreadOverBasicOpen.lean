import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.WeilIsGrpPullbackOfCommute
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenWeilIsIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsUniqueSectionOfDense
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.SpreadLevel

theorem pushHom_bijective {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) :=
  ⟨fun x y hxy =>
      Over.OverMorphism.ext (h.1.hom_ext (congrArg CommaMorphism.left hxy) (by rw [Over.w x, Over.w y])),
    fun x₀ => ⟨Over.homMk (h.1.lift x₀.left T.hom (Over.w x₀)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

theorem map_linComb {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {T : Over S} {T' : Over S'}
    (ρ : (T' ⟶ G') →* (T ⟶ G)) {n : ℕ} (y : Fin n → (T' ⟶ G')) (a : Fin n → ℕ) :
    ρ (Out.linComb y a) = Out.linComb (fun i => ρ (y i)) a := by
  simp only [Out.linComb, map_list_prod, List.map_ofFn, Function.comp_def, map_pow]

theorem unitS_comp {o : Type} [CommRing o] {S S' : Scheme.{0}} (f : S' ⟶ S) (s : S ⟶ Sp o) (u : oˣ) :
    unitS (f ≫ s) u = Units.map f.appTop.hom.toMonoidHom (unitS s u) := by
  apply Units.ext
  show (f ≫ s).appTop.hom _ = f.appTop.hom (s.appTop.hom _)
  rw [Scheme.Hom.comp_appTop]
  rfl

theorem unitS_spMap_pow {o R : Type} [CommRing o] [CommRing R] (β : o →+* R) (u : oˣ) (k : ℕ) (h : β u ^ k = 1) :
    unitS (spMap β) u ^ k = 1 := by
  apply Units.ext
  have e : (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom (β u) :=
    (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm
  rw [Units.val_pow_eq_pow_val]
  show (spMap β).appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u) ^ k = 1
  rw [e, ← map_pow, h, map_one]

theorem exists_extension (hL : Out.Laws) {o : Type} [CommRing o] {g k : ℕ} {J : Type} {b : TBase o k}
    {K : Type} [Field K] {S : Scheme.{0}} [PreconnectedSpace S] (s : S ⟶ Sp o) (j : Sp K ⟶ S) [QuasiCompact j]
    [IsSchemeTheoreticallyDominant j] {sK : Sp K ⟶ Sp o} (hs : j ≫ s = sK) (hk : 0 < k)
    (hζ : unitS s b.ζ ^ k = 1) (t : TObj g k J b sK)
    (P : Out.PolAV S) (φ : t.A.left ⟶ P.A.left) (hg : P.g = g) (hφ : IsGrpPullback t.A P.A j φ)
    (hφL : LBIso t.L (P.L.pull φ)) (p : Fin (2 * g) → (Out.baseOver S ⟶ P.A))
    (hp : ∀ i, (t.pt i).left ≫ φ = j ≫ (p i).left) (a : J → (P.A ⟶ P.A))
    (ha : ∀ i, (t.act i).left ≫ φ = φ ≫ (a i).left) : ∃ t' : TObj g k J b s, TMap t t' j := by
  subst hs
  have := P.isAb.proper
  have := P.isAb.smooth
  have := P.isAb.comm
  have hku : IsUnit (k : Γ(S, ⊤)) := by
    have := b.unit.map (s.appTop.hom.comp (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom)
    rwa [map_natCast] at this
  let h : Over.mk ((Out.baseOver (Sp K)).hom ≫ j) ⟶ Out.baseOver S := Over.homMk j (by simp)
  have hpush : ∀ i, pushHom hφ _ (t.pt i) = h ≫ p i := fun i => Over.OverMorphism.ext (hp i)
  have tors : ∀ i, p i ^ k = 1 := fun i => by
    have e : h ≫ (p i ^ k) = h ≫ (1 : Out.baseOver S ⟶ P.A) := by
      have e₁ := map_pow (preHom (G := P.A) h) (p i) k
      have e₂ := map_one (preHom (G := P.A) h)
      refine e₁.trans (Eq.trans ?_ e₂.symm)
      show (h ≫ p i) ^ k = 1
      rw [← hpush, ← map_pow, t.torsion, map_one]
    exact Over.OverMorphism.ext (ExtUnique.hom_ext_of_dominant P.A.hom (by rw [Over.w, Over.w]) j
      (congrArg CommaMorphism.left e))
  refine ⟨{ A := P.A, ab := P.isAb, dim := hg ▸ P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
            ample := P.ample, ktriv := P.ktriv, pt := p, torsion := tors, bij := ?_, pairing := fun i i' => ?_
            act := a, hom := fun i => ?_ }, φ, hφ, hφL, hp, ha⟩
  · refine GlobalTheory.torsion_basis_of_dense S P.A k (2 * g) p (Set.range j) P.isAb hk hku tors j.denseRange ?_
    rintro _ ⟨z, rfl⟩
    let x₀ : Sp (AlgebraicClosure K) ⟶ Sp K := spMap (algebraMap K _)
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    refine ⟨AlgebraicClosure K, inferInstance, inferInstance, x₀ ≫ j,
      ⟨IsLocalRing.closedPoint _, (Scheme.Hom.comp_apply _ _ _).trans (congrArg j (Subsingleton.elim _ _))⟩,
      fun y hy => ?_⟩
    have hb := pushHom_bijective hφ (Over.mk x₀)
    obtain ⟨y', rfl⟩ := hb.2 y
    have hy' : y' ^ k = 1 := hb.1 (by rw [map_pow, map_one]; exact hy)
    refine (existsUnique_congr fun c => ?_).1 (t.bij _ x₀ y' hy')
    rw [← hb.1.eq_iff, map_linComb]
    refine Eq.congr_left (congrArg (fun q => Out.linComb q _) (funext fun i => Over.OverMorphism.ext ?_))
    show (x₀ ≫ (t.pt i).left) ≫ φ = (x₀ ≫ j) ≫ (p i).left
    rw [Category.assoc, hp, Category.assoc]
  · obtain ⟨U, hU, H⟩ := GlobalTheory.exists_clopen_weilIs_iff hL S P k (Out.baseOver S) (p i) (p i')
      (unitS s b.ζ ^ Out.stdSymp g i i') hk hku (tors i) (tors i')
      (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow])
    have w := (GlobalTheory.weilIs_grpPullback_of_comm S (Sp K) P.A t.A j φ P.L t.L P.isLB t.isLB hφ hφL (Out.baseOver (Sp K))
      k (t.pt i) (t.pt i') (h ≫ p i) (h ≫ p i') _ (hp i).symm (hp i').symm).1 (t.pairing i i')
    rw [unitS_comp, ← map_zpow] at w
    have hr : Set.range h.left ⊆ U := (H _ h).1 w
    have hall : (U : Set (Out.baseOver S).left) = Set.univ :=
      IsClopen.eq_univ (α := S) ⟨hU, U.isOpen⟩ ⟨_, hr ⟨IsLocalRing.closedPoint K, rfl⟩⟩
    have := (H _ (𝟙 _)).2 (fun y _ => hall ▸ Set.mem_univ y)
    simpa using this
  · have := t.hom i
    exact ExtUnique.isMonHom_of_isGrpPullback hφ hφ (t.act i) (a i) (ha i)

theorem main : Out.Laws → Out.Laws2 → ∀ (o : Type) [CommRing o] (g k : ℕ) (J : Type) (b : TBase o k) [Finite J] (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (β : o →+* R) (t : TObj g k J b (spMap (algebraMap R K) ≫ spMap β)) (P' : Out.PolAV (Sp R)) (φ : t.A.left ⟶ P'.A.left), P'.g = g → IsGrpPullback t.A P'.A (spMap (algebraMap R K)) φ → LBIso t.L (P'.L.pull φ) → ∃ (f : R) (_ : f ≠ 0) (t' : TObj g k J b (spMap (algebraMap R (Localization.Away f)) ≫ spMap β)) (ψ : Localization.Away f →+* K), ψ.comp (algebraMap R _) = algebraMap R K ∧ TMap t t' (spMap ψ) := by
  intro hL _ o _ g k J b _ R K _ _ _ _ _ _ β t P' φ hg hφ hφL
  have := P'.isAb.proper
  have := P'.isAb.smooth
  let e : pullback P'.A.hom (spMap (algebraMap R K)) ⟶ t.A.left :=
    hφ.1.lift (pullback.fst _ _) (pullback.snd _ _) pullback.condition
  have e₁ : e ≫ φ = pullback.fst _ _ := hφ.1.lift_fst _ _ _
  have e₂ : e ≫ t.A.hom = pullback.snd _ _ := hφ.1.lift_snd _ _ _
  let e' : t.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R K)) := pullback.lift φ t.A.hom hφ.1.w
  have ee : e' ≫ e = 𝟙 _ := by
    apply hφ.1.hom_ext
    · rw [Category.assoc, e₁, Category.id_comp]; exact pullback.lift_fst _ _ _
    · rw [Category.assoc, e₂, Category.id_comp]; exact pullback.lift_snd _ _ _
  have wpt : ∀ i, (t.pt i).left ≫ t.A.hom = 𝟙 (Sp K) := fun i => Over.w (t.pt i)
  let v : Fin (2 * g) ⊕ J → (t.A.left ⟶ t.A.left) :=
    Sum.elim (fun i => t.A.hom ≫ (t.pt i).left) (fun j => (t.act j).left)
  have hv : ∀ i, v i ≫ t.A.hom = t.A.hom := by
    rintro (i | j)
    · exact (Category.assoc _ _ _).trans ((congrArg (t.A.hom ≫ ·) (wpt i)).trans (Category.comp_id _))
    · exact Over.w (t.act j)
  obtain ⟨f, hf, u', hu'⟩ := GlobalTheory.morphisms_generic_spread_out R K P'.A.left P'.A.left P'.A.hom P'.A.hom (Fin (2 * g) ⊕ J)
    (fun i => e ≫ v i ≫ φ) inferInstance inferInstance inferInstance (fun i => by
      rw [Category.assoc, Category.assoc, hφ.1.w, ← Category.assoc (v i), hv, ← Category.assoc, e₂,
        pullback.condition])
  have hfK : IsUnit (algebraMap R K f) :=
    IsUnit.mk0 _ fun h0 => hf (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  let ψ : Localization.Away f →+* K := IsLocalization.Away.lift f hfK
  have hψ : ψ.comp (algebraMap R _) = algebraMap R K := IsLocalization.Away.lift_comp f hfK
  have hψs : spMap ψ ≫ spMap (algebraMap R (Localization.Away f)) = spMap (algebraMap R K) := by
    rw [← hψ]; exact (Spec.map_comp _ _).symm
  have hle : Submonoid.powers f ≤ nonZeroDivisors R := powers_le_nonZeroDivisors_of_noZeroDivisors hf
  have : IsDomain (Localization.Away f) := IsLocalization.isDomain_localization hle
  have hψi : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨⟨r, m⟩, h⟩ := IsLocalization.surj (Submonoid.powers f) x
    have h₁ := congrArg ψ h
    rw [map_mul, hx, zero_mul, ← RingHom.comp_apply, hψ] at h₁
    have h₂ : r = 0 := IsFractionRing.injective R K (h₁.symm.trans (map_zero _).symm)
    rw [h₂, map_zero] at h
    exact (IsLocalization.map_units (Localization.Away f) m).mul_left_eq_zero.1 h
  have : IsSchemeTheoreticallyDominant (spMap ψ) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective _ hψi
  have : PreconnectedSpace (Sp (Localization.Away f)) :=
    inferInstanceAs (PreconnectedSpace (PrimeSpectrum (Localization.Away f)))
  have hprim := b.prim K ((algebraMap R K).comp β)
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 => by
    have := b.unit.map β
    rw [h0, Nat.cast_zero, map_zero] at this
    exact not_isUnit_zero this
  have hζ : unitS (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) b.ζ ^ k = 1 := by
    rw [unitS_comp, ← map_pow, unitS_spMap_pow β b.ζ k (IsFractionRing.injective R K (by
      rw [map_pow, map_one]; exact hprim.pow_eq_one)), map_one]
  obtain ⟨P, χ, hχ₀, hgP, hm, c, hc⟩ := hL.polBaseChange _ _ (spMap (algebraMap R (Localization.Away f))) P'
  have hχ : IsGrpPullback P.A P'.A (spMap (algebraMap R (Localization.Away f))) χ :=
    ⟨hχ₀, fun T x y x₀ y₀ hx hy => by
      rw [(Over.OverMorphism.ext hx : x₀ = Out.toBase hχ₀.w x), (Over.OverMorphism.ext hy : y₀ = Out.toBase hχ₀.w y),
        ← hm]
      rfl⟩
  let w : t.A.left ⟶ P.A.left := hχ₀.lift φ (t.A.hom ≫ spMap ψ) (by rw [Category.assoc, hψs, hφ.1.w])
  have w₁ : w ≫ χ = φ := hχ₀.lift_fst _ _ _
  have w₂ : w ≫ P.A.hom = t.A.hom ≫ spMap ψ := hχ₀.lift_snd _ _ _
  have hw : IsGrpPullback t.A P.A (spMap ψ) w := hχ.cancel (hφ.congr hψs.symm w₁.symm) w₂
  have hwL : LBIso t.L (P.L.pull w) :=
    hφL.trans t.isLB (pull_isLB P'.isLB _) (pull_isLB P.isLB _)
      (LBIso.chartPull (chartPullSame P'.L (fun _ : PUnit => φ) (fun _ : PUnit => χ) (fun _ => 1) w fun _ => w₁.symm)
        (chartPullPull P.L w w rfl) ⟨c, hc⟩)
  let d : P.A.left ⟶ pullback P'.A.hom (spMap (algebraMap R (Localization.Away f))) := pullback.lift χ P.A.hom hχ₀.w
  have d₁ : d ≫ pullback.fst _ _ = χ := pullback.lift_fst _ _ _
  let v' : Fin (2 * g) ⊕ J → (P.A ⟶ P.A) := fun i => Over.homMk (hχ₀.lift (d ≫ u' i) P.A.hom (by
    rw [Category.assoc, (hu' i).1, ← Category.assoc, d₁, hχ₀.w])) (hχ₀.lift_snd _ _ _)
  have hv' : ∀ i, v i ≫ w = w ≫ (v' i).left := fun i => by
    have a₁ : (v' i).left ≫ χ = d ≫ u' i := hχ₀.lift_fst _ _ _
    have a₂ := (hu' i).2 (e ≫ w ≫ d) (by rw [Category.assoc, Category.assoc, d₁, w₁, e₁])
    apply hχ₀.hom_ext
    · rw [Category.assoc, Category.assoc, w₁, a₁]
      have a₃ := congrArg (e' ≫ ·) a₂
      simp only [← Category.assoc, ee, Category.id_comp] at a₃
      rw [← a₃, Category.assoc]
    · rw [Category.assoc, Category.assoc, Over.w (v' i), w₂, ← Category.assoc, hv]
  have z₁ : eSec P.A ≫ P.A.hom = 𝟙 _ := Over.w η[P.A]
  have z₂ : eSec t.A ≫ t.A.hom = 𝟙 _ := Over.w η[t.A]
  refine ⟨f, hf, ?_⟩
  obtain ⟨t', ht'⟩ := exists_extension hL (spMap (algebraMap R (Localization.Away f)) ≫ spMap β) (spMap ψ)
    (by rw [← Category.assoc, hψs]) hk hζ t P w (hgP.trans hg) hw hwL
    (fun i => Over.homMk (eSec P.A ≫ (v' (.inl i)).left) (by
      show (eSec P.A ≫ (v' (.inl i)).left) ≫ P.A.hom = 𝟙 _
      rw [Category.assoc, Over.w (v' _), z₁]))
    (fun i => by
      show (t.pt i).left ≫ w = spMap ψ ≫ eSec P.A ≫ (v' (.inl i)).left
      refine Eq.symm ((Category.assoc _ _ _).symm.trans ?_)
      refine (congrArg (· ≫ (v' (.inl i)).left) (PolBaseChange.eSec_comm hw).symm).trans ?_
      refine (Category.assoc _ _ _).trans ((congrArg (eSec t.A ≫ ·) (hv' (.inl i)).symm).trans ?_)
      show eSec t.A ≫ (t.A.hom ≫ (t.pt i).left) ≫ w = _
      rw [Category.assoc, ← Category.assoc, z₂]
      exact Category.id_comp _)
    (fun j => v' (.inr j)) (fun j => hv' (.inr j))
  exact ⟨t', ψ, hψ, ht'⟩

end GlobalTheory.SpreadLevel
