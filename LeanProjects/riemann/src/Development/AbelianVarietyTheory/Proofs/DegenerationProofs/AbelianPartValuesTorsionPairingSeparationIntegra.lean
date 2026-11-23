import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaCoordinatesExistUniqueSeparatePointsStatement
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTorsionLift
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsGeneratorNeZero
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingHenselianAndSmoothPointsLift
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalPolarisationVolumeFormSymmetricAmple
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionDivision

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesTorsion
open IsLocalRing GlobalTheory.UT.ExactTerm

theorem nonempty_equiv_of_basis {G : Type} [CommGroup G] {k r : ℕ} (hk : k ≠ 0) (v : Fin r → G) (hv : ∀ i, v i ^ k = 1)
    (h : ∀ y : G, y ^ k = 1 → ∃! c : Fin r → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y) :
    Nonempty ((powMonoidHom k : G →* G).ker ≃* Multiplicative (Fin r → ZMod k)) := by
  have : NeZero k := ⟨hk⟩
  simp only [List.prod_ofFn] at h
  let f : Multiplicative (Fin r → ZMod k) →* (powMonoidHom k : G →* G).ker := MonoidHom.mk'
    (fun c => ⟨∏ i, v i ^ (c.toAdd i).val, by
      show (∏ i, v i ^ (c.toAdd i).val) ^ k = 1
      rw [← Finset.prod_pow]
      exact Finset.prod_eq_one fun i _ => by rw [← pow_mul, mul_comm, pow_mul, hv, one_pow]⟩)
    fun a b => Subtype.ext (by
      show ∏ i, v i ^ (a.toAdd i + b.toAdd i).val = (∏ i, v i ^ (a.toAdd i).val) * ∏ i, v i ^ (b.toAdd i).val
      rw [← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => by rw [ZMod.val_add, ← pow_eq_pow_mod _ (hv i), pow_add])
  refine ⟨(MulEquiv.ofBijective f ⟨fun a b e => ?_, fun y => ?_⟩).symm⟩
  · exact (h _ (f b).2).unique (congrArg Subtype.val e) rfl
  · obtain ⟨c, hc⟩ := (h y.1 y.2).exists
    exact ⟨Multiplicative.ofAdd c, Subtype.ext hc⟩

section Geom
variable (hL : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S) {K : Type} [Field K] [IsAlgClosed K]
  (t : Sp K ⟶ S)
include hL

theorem exists_pow_eq (a : Over.mk t ⟶ P.A) {n : ℕ} (hn : 1 ≤ n) : ∃ b : Over.mk t ⟶ P.A, b ^ n = a := by
  obtain ⟨hfin, -, hsurj, -, -⟩ := hL.mulN S P n hn
  obtain ⟨s, hs⟩ := H1.SectionDivision.exists_section (k := K) (pullback.snd (mulA P.A n).left a.left)
  have hb : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ (mulA P.A n).left = a.left := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs]; exact Category.id_comp _
  have hw : (s ≫ pullback.fst (mulA P.A n).left a.left) ≫ P.A.hom = t := by
    rw [← Over.w (mulA P.A n), ← Category.assoc, hb]; exact Over.w a
  refine ⟨Over.homMk _ hw, ?_⟩
  have e : ∀ b : Over.mk t ⟶ P.A, b ^ n = b ≫ mulA P.A n := fun b =>
    (congrArg (· ^ n) (Category.comp_id b).symm).trans (MonObj.comp_pow (𝟙 P.A) n b).symm
  rw [e]
  exact Over.OverMorphism.ext hb

theorem exists_basis {k : ℕ} (hk : (k : K) ≠ 0) : ∃ v : Fin (2 * P.g) → (Over.mk t ⟶ P.A), (∀ i, v i ^ k = 1) ∧
    ∀ y : Over.mk t ⟶ P.A, y ^ k = 1 →
      ∃! c : Fin (2 * P.g) → ZMod k, (List.ofFn fun i => v i ^ (c i).val).prod = y := by
  have := P.isAb.comm
  let c : Γ(Sp K, ⊤) ≃+* K := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  have : IsDomain Γ(Sp K, ⊤) := c.toMulEquiv.isDomain _
  have hk0 : k ≠ 0 := fun e => hk (by rw [e, Nat.cast_zero])
  have : NeZero (k : K) := ⟨hk⟩
  have : NeZero k := ⟨hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot K k
  have hζ' : IsPrimitiveRoot (c.symm ζ) k := hζ.map_of_injective c.symm.injective
  obtain ⟨w₁, w₂, w₃, -⟩ := hL.weil _ P k (Over.mk t)
  exact PrincipalNumerics.exists_basis_of_pairing (G := Over.mk t ⟶ P.A) (g := P.g) (Nat.pos_of_ne_zero hk0)
    (fun d hd => (hL.mulN _ P d (Nat.pos_of_dvd_of_pos hd (Nat.pos_of_ne_zero hk0))).2.2.2.2 K t (by
      obtain ⟨e, rfl⟩ := hd
      rw [Nat.cast_mul] at hk
      exact left_ne_zero_of_mul hk))
    (hζ'.isUnit_unit hk0) (fun x y c => WeilIs P.A P.L k x y c) w₁ w₂ w₃
    (fun _ _ _ h => CommPairing.weilIs_symm P.isLB h) (ThetaRep.eq_one_of_weilIs hL P t hk)
end Geom

section Val
variable {C : Type} [NormedField C] (S : ValuationSubring C)

theorem affine_ext {R : Type} [CommRing R] {f g : Sp S ⟶ Sp R} (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) :
    f = g := by
  obtain ⟨a, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) f
  obtain ⟨b, rfl⟩ := Spec.map_surjective (R := CommRingCat.of R) (S := CommRingCat.of S) g
  have e₁ : a ≫ CommRingCat.ofHom S.subtype = b ≫ CommRingCat.ofHom S.subtype :=
    Spec.map_injective (by rw [Spec.map_comp, Spec.map_comp]; exact h)
  exact congrArg Spec.map (CommRingCat.hom_ext (RingHom.ext fun x => Subtype.ext
    (RingHom.congr_fun (congrArg CommRingCat.Hom.hom e₁) x)))

theorem separated_ext {R : Type} [CommRing R] {X : Scheme.{0}} (p : X ⟶ Sp R) [IsSeparated p] {f g : Sp S ⟶ X}
    (h : spMap S.subtype ≫ f = spMap S.subtype ≫ g) : f = g := by
  have e : f ≫ p = g ≫ p := affine_ext S (by rw [← Category.assoc, h, Category.assoc])
  let Q : ValuativeCommSq p :=
    { R := S, K := C, i₁ := spMap S.subtype ≫ f, i₂ := f ≫ p, commSq := ⟨Category.assoc _ _ _⟩ }
  exact congrArg CommSq.LiftStruct.l ((IsSeparated.valuativeCriterion p Q).elim ⟨f, rfl, rfl⟩ ⟨g, h.symm, e.symm⟩)

variable {S} (hS : ∀ x, x ∈ S ↔ ‖x‖ ≤ 1)
include hS

theorem norm_valF {X : Scheme.{0}} (x : Sp S ⟶ X) (U : X.Opens) (a : Γ(X, U))
    (ha : x (closedPoint S) ∈ X.basicOpen a) : ‖valF (spMap S.subtype ≫ x) U a‖ = 1 := by
  have h₁ : x ⁻¹ᵁ X.basicOpen a = ⊤ := DVR.eq_top_of_closedPoint_mem _ ha
  have ht : ⊤ ≤ x ⁻¹ᵁ U := fun q _ => X.basicOpen_le a (h₁.ge (Set.mem_univ q))
  have h' : ⊤ ≤ (spMap S.subtype ≫ x) ⁻¹ᵁ U := fun q _ => ht (Set.mem_univ (spMap S.subtype q))
  have hu : IsUnit ((x.appLE U ⊤ ht).hom a) := by
    refine (Sp S).toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => ((Sp S).mem_basicOpen _ y hy).1 ?_
    rw [Scheme.basicOpen_appLE, h₁]
    exact ⟨trivial, trivial⟩
  obtain ⟨u, hu⟩ := hu.map (Scheme.ΓSpecIso (CommRingCat.of S)).hom.hom
  have e : (spMap S.subtype ≫ x).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso (CommRingCat.of C)).hom =
      x.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of S)).hom ≫ CommRingCat.ofHom S.subtype := by
    rw [← Scheme.ΓSpecIso_naturality, ← Scheme.Hom.appLE_comp_appLE (spMap S.subtype) x U ⊤ ⊤ ht le_rfl,
      Category.assoc]
    rfl
  have e' : valF (spMap S.subtype ≫ x) U a = S.subtype u.val := by
    rw [valF, dif_pos h', hu]
    exact congrArg (fun g => g.hom a) e
  have m : ‖S.subtype u.val‖ * ‖S.subtype u.inv‖ = 1 := by
    rw [← norm_mul, ← map_mul]
    exact (congrArg (fun q => ‖S.subtype q‖) u.val_inv).trans (by rw [map_one, norm_one])
  have b₁ : ‖S.subtype u.val‖ ≤ 1 := (hS _).1 (show S from u.val).2
  have b₂ : ‖S.subtype u.inv‖ ≤ 1 := (hS _).1 (show S from u.inv).2
  rw [e']
  nlinarith [norm_nonneg (S.subtype u.val), norm_nonneg (S.subtype u.inv)]

variable {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} (m : Sp S ⟶ Y)
  {J : (Sp C ⟶ X) → L.ι} (hm : ∀ k, ⊤ ≤ (m ≫ φ k) ⁻¹ᵁ L.U (J ((spMap S.subtype ≫ m) ≫ φ k)))
include hm

theorem norm_vF (t : LB.Gen (LB.LinComb L φ ε)) : ‖vF t (spMap S.subtype ≫ m) J‖ = 1 := by
  refine norm_valF hS m _ _ ?_
  exact (Scheme.basicOpen_of_isUnit Y (Units.isUnit _)).ge (Set.mem_iInter.2 fun k => hm k trivial)

theorem norm_sF (hL : L.IsLB) (s : LB.Sec (LB.LinComb L φ ε))
    (h : ∀ z J', Good L z J' → IsUnit (sval s (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z J')) :
    ‖sF s (spMap S.subtype ≫ m) J‖ = 1 := by
  let z : Spec (CommRingCat.of (ResidueField S)) := closedPoint (ResidueField S)
  obtain ⟨J', hJ'⟩ := GlobalTheory.UT.CoefBasic.exists_good' hL z
  have e : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z = m (closedPoint S) :=
    congrArg m (IsLocalRing.comap_closedPoint (residue S))
  have h₁ : (Spec.map (CommRingCat.ofHom (residue S)) ≫ m) z ∈
      LB.wchart L φ fun k => J ((spMap S.subtype ≫ m) ≫ φ k) := by
    rw [e]
    exact Set.mem_iInter.2 fun k => hm k trivial
  have h₂ := (congrArg IsUnit (sec_trans s _ z (hJ'.mem φ _) h₁)).mp (h z J' hJ')
  refine norm_valF hS m _ _ ?_
  rw [← e]
  exact (isUnit_gs_iff _ z _ h₁ _).1 (isUnit_of_mul_isUnit_right h₂)
end Val

theorem exists_norm_th (hL : Laws) {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R]
    {D : DegPre R} {C : Type} [NormedField C] [IsAlgClosed C] [Algebra (FractionRing R) C] (hR : CExt R ⊥ C)
    {N : NumD C} (ν : NumOf D C N) (hν : ν.IntN) {n : ℕ} (hn : 2 ≤ n) (hC : ‖(n : C)‖ = 1) (a : N.A) :
    ∃ t, t ^ n = 1 ∧ ‖N.th (a * t)‖ = 1 := by
  obtain ⟨S, hS, hI⟩ := hν
  have := D.P.isAb.proper
  let f : R →+* S := ((algebraMap (FractionRing R) C).comp (algebraMap R _)).codRestrict S fun r => (hS _).2 (hR.1 r)
  have hf : spMap S.subtype ≫ spMap f = (TF (R := R) C).hom := by
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]; rfl
  let ρ : TF (R := R) C ⟶ Over.mk (spMap f) := Over.homMk (spMap S.subtype) hf
  have hJ : ∀ y : Sp S ⟶ D.P.A.left, y ≫ D.P.A.hom = spMap f →
      ⊤ ≤ y ⁻¹ᵁ D.P.L.U (ν.J (spMap S.subtype ≫ y)) := fun y hy => by
    obtain ⟨x₀, e, h⟩ := hI (Over.homMk (spMap S.subtype ≫ y) (by rw [Category.assoc, hy]; exact hf))
    obtain rfl : x₀ = y := separated_ext S D.P.A.hom e
    exact h
  obtain ⟨m₀, hm₀, -⟩ := hI (ν.eA a)
  let m : Over.mk (spMap f) ⟶ D.P.A := Over.homMk m₀ (affine_ext S (by
    rw [← Category.assoc, hm₀]; exact (Over.w (ν.eA a)).trans hf.symm))
  have hm : ρ ≫ m = ν.eA a := Over.OverMorphism.ext hm₀
  have : IsAlgClosed (ResidueField S) := isAlgClosed_residueField_of_valuationRing_of_isAlgClosed S C
  have hκ : (n : ResidueField S) ≠ 0 := by
    have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
    have hu : IsUnit (n : S) := IsUnit.of_mul_eq_one (⟨(n : C)⁻¹, (hS _).2 (by simp [hC])⟩ : S)
      (Subtype.ext (by simp [h0]))
    have := (hu.map (residue S)).ne_zero
    rwa [map_natCast] at this
  let r : Over.mk (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f) ⟶ Over.mk (spMap f) := Over.homMk _ rfl
  obtain ⟨β, -, hβ⟩ := exists_generator_ne_zero hL.secBaseChange D.P
  obtain ⟨th, h₀, hth⟩ := hβ (ResidueField S) (Spec.map (CommRingCat.ofHom (residue S)) ≫ spMap f)
  obtain ⟨x₀, hx₀, hu⟩ := exists_good_point hL.goodPt hL.polBaseChange D.P _ hn hκ th h₀ (r ≫ m)
  obtain ⟨hfin, hflat, -⟩ := hL.mulN _ D.P n (by omega)
  obtain ⟨x, hx, ex⟩ : ∃ x : Over.mk (spMap f) ⟶ D.P.A, x ^ n = 1 ∧
      Spec.map (CommRingCat.ofHom (residue S)) ≫ x.left = x₀.left :=
    exists_torsion_lift S D.P.A n (spMap f) x₀ hx₀
  have ex' : r ≫ x = x₀ := Over.OverMorphism.ext ex
  obtain ⟨c, hc⟩ := ν.th_gen β
  refine ⟨ν.eA.symm (ρ ≫ x), by rw [← map_pow, ← MonObj.comp_pow, hx, MonObj.comp_one, map_one], ?_⟩
  have e : (ν.eA (a * ν.eA.symm (ρ ≫ x))).left = spMap S.subtype ≫ (m * x).left := by
    rw [map_mul, MulEquiv.apply_symm_apply, ← hm, ← MonObj.comp_mul]; rfl
  have h₁ : ‖sF ν.th (spMap S.subtype ≫ (m * x).left) ν.J‖ = 1 :=
    norm_sF hS (m * x).left (fun _ => by
      simpa only [Category.comp_id] using hJ (m * x).left (Over.w _)) D.P.isLB ν.th fun z J hz => by
      have q := hu z J hz
      rw [hth _ _ z J hz, ThetaPtMove.ptSecT_snd, ← ex', ← MonObj.comp_mul] at q
      exact isUnit_of_mul_isUnit_right ((congrArg IsUnit
        (IndivisibleSection.sval_of_secIsMul (s := β) (t := ν.th) hc _ z hz)).mp q)
  have h₂ : ‖vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
      (spMap S.subtype ≫ spMap f) ν.J‖ = 1 :=
    norm_vF hS (spMap f) (fun _ => by
      rw [Category.assoc]
      exact hJ _ (Over.w (1 : Over.mk (spMap f) ⟶ D.P.A))) _
  have h₃ := congrArg norm (ν.th_eq (a * ν.eA.symm (ρ ≫ x)))
  rw [norm_mul, e, h₁, ← hf, h₂, _root_.mul_one] at h₃
  exact h₃

theorem tors_of_integral : Laws → Laws2 → BrUthSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [IsAlgClosed C] [Algebra (FractionRing R) C], CExt R ⊥ C → ∀ (N : NumD C) (ν : NumOf D C N), ν.IntN → ∀ n : ℕ, n.Prime → Odd n → ‖(n : C)‖ = 1 → N.Tors n D.P.g := by
  intro hL _ hB R _ _ _ _ D he hb C _ _ _ _ hR N ν hν n hp ho hC
  have h0 : (n : C) ≠ 0 := fun e => by simp [e] at hC
  have hj : ∀ j : ℕ, ((n ^ j : ℕ) : C) ≠ 0 := fun j => by rw [Nat.cast_pow]; exact pow_ne_zero _ h0
  obtain ⟨hW, hU⟩ := hB R D he hb C N ν
  have tor : ∀ (b : N.A) (k : ℕ), ν.eA b ^ k = 1 ↔ b ^ k = 1 := fun b k => by
    rw [← map_pow, MulEquiv.map_eq_one_iff]
  refine ⟨fun x => ?_, fun j => ?_, fun j b hb h => ?_, exists_norm_th hL hR ν hν hp.two_le hC, fun j h1 x x' l hl h => ?_⟩
  · obtain ⟨y, hy⟩ := exists_pow_eq hL D.P (jFK (R := R) C ≫ jK R) (ν.eA x) hp.pos
    exact ⟨ν.eA.symm y, by rw [← map_pow, hy, MulEquiv.symm_apply_apply]⟩
  · obtain ⟨v, hv, h⟩ := exists_basis hL D.P (jFK (R := R) C ≫ jK R) (hj j)
    refine nonempty_equiv_of_basis (pow_ne_zero j hp.ne_zero) (fun i => ν.eA.symm (v i))
      (fun i => by rw [← map_pow, hv, map_one]) fun y hy => ?_
    refine (existsUnique_congr fun c => ?_).1 (h (ν.eA y) ((tor _ _).2 hy))
    simp only [List.prod_ofFn, ← map_pow, ← map_prod, MulEquiv.symm_apply_eq]
  · refine ν.eA.map_eq_one_iff.1 (ThetaRep.eq_one_of_weilIs hL D.P (jFK (R := R) C ≫ jK R) (hj j) _
      ((tor _ _).2 hb) fun y hy => ?_)
    obtain ⟨b', rfl⟩ := ν.eA.surjective y
    have hb' := (tor _ _).1 hy
    have := hW (n ^ j) (Nat.pos_of_ne_zero (pow_ne_zero j hp.ne_zero)) b b' hb hb'
    rwa [h b' hb', show unitOn (1 : Cˣ) = 1 from map_one (Units.map _)] at this
  · obtain ⟨-, hc⟩ := hU (n ^ j) ho.pow (hj j) {b : N.A // b ^ (n ^ j) ^ 2 = 1} Subtype.val Subtype.property
    obtain ⟨-, hs, -, hsep⟩ := GlobalTheory.T.thetaCoordinates_exist_unique_separate_points hL C _ D.P (jFK (R := R) C ≫ jK R) (n ^ j) ho.pow (hj j)
      {b : N.A // b ^ (n ^ j) ^ 2 = 1} (fun i => ν.eA i.1) fun i => (tor _ _).2 i.2
    have h3 : 3 ≤ n ^ j := by
      have : 3 ≤ n := by
        have := hp.two_le
        obtain ⟨k, rfl⟩ := ho
        omega
      exact this.trans (Nat.le_self_pow (by omega) n)
    refine ν.eA.injective (hsep h3 (fun y hy => ?_) _ _ (fun i => N.uth (n ^ j) i.1 x) (hc x)
      ((hs _ (fun i => N.uth (n ^ j) i.1 x') _ (hc x')).2 ⟨Units.mk0 l hl, funext fun i => h i.1 i.2⟩)).1
    obtain ⟨b, rfl⟩ := ν.eA.surjective y
    exact ⟨⟨b, (tor _ _).1 hy⟩, rfl⟩

end GlobalTheory.ValuesTorsion
end
