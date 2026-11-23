import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjIsAbelianSchemeDimRigidifiedSym
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsEquivStdSymp
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsGenOfMemChart
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueWeilIs
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsCommVOfLe
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.WeilIsAlternatingSkewNatural
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ObjTheta

theorem prod_ev {M Q : Type} [AddCommGroup M] [Group Q] {m : ℕ} (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) (c : Fin m → ℕ) :
    (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ c i).prod = ev (bas fun i => (c i : ℤ)) := by
  let f : Multiplicative M →* Q := MonoidHom.mk' (fun x => ev x.toAdd) fun a b => add _ _
  have h : (fun i => ev (bas (Pi.single i 1)) ^ c i) =
      f ∘ fun i => Multiplicative.ofAdd (bas (Pi.single i 1)) ^ c i := by
    funext i
    exact (map_pow f (Multiplicative.ofAdd (bas (Pi.single i 1))) (c i)).symm
  rw [h, ← List.map_ofFn, ← map_list_prod, List.prod_ofFn]
  show ev _ = _
  congr 1
  rw [toAdd_prod]
  simp only [toAdd_pow, toAdd_ofAdd, ← map_nsmul, ← map_sum]
  congr 1
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

theorem ev_pow {M Q : Type} [AddCommGroup M] [Group Q] (ev : M → Q) (add : ∀ a c, ev (a + c) = ev a * ev c)
    (n : ℕ) (a : M) : ev a ^ n = ev (n • a) :=
  (map_pow (MonoidHom.mk' (fun x : Multiplicative M => ev x.toAdd) fun _ _ => add _ _) (Multiplicative.ofAdd a) n).symm

theorem existsUnique_label {M Q : Type} [AddCommGroup M] [Group Q] {m n : ℕ} (hn : 0 < n) (ev : M → Q)
    (add : ∀ a c, ev (a + c) = ev a * ev c) (ker : ∀ a, ev a = 1 ↔ ∃ b, a = n • b)
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] M) {y : Q} (hy : ∃ a, ev a = y) :
    ∃! c : Fin m → ZMod n, (List.ofFn fun i => ev (bas (Pi.single i 1)) ^ (c i).val).prod = y := by
  have : NeZero n := ⟨hn.ne'⟩
  have key : ∀ u v : Fin m → ℤ, ev (bas u) = ev (bas v) ↔ ∀ i, (u i : ZMod n) = v i := by
    intro u v
    have e : ev (bas u) = ev (bas (u - v)) * ev (bas v) := by rw [← add, ← map_add, sub_add_cancel]
    rw [e, mul_eq_right, ker]
    constructor
    · rintro ⟨b, hb⟩ i
      obtain ⟨w, rfl⟩ := bas.surjective b
      rw [← map_nsmul] at hb
      have := congrFun (bas.injective hb) i
      simp only [Pi.sub_apply, Pi.smul_apply, nsmul_eq_mul] at this
      rw [← sub_eq_zero, ← Int.cast_sub, this]
      simp
    · intro h
      have : ∀ i, ∃ w : ℤ, u i - v i = n * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 (by rw [Int.cast_sub, h, sub_self])
      choose w hw using this
      refine ⟨bas w, ?_⟩
      rw [← map_nsmul]
      congr 1
      funext i
      simpa using hw i
  obtain ⟨a, rfl⟩ := hy
  obtain ⟨u, rfl⟩ := bas.surjective a
  refine ⟨fun i => (u i : ZMod n), ?_, fun c hc => ?_⟩
  · beta_reduce
    rw [prod_ev ev add, key]
    intro i
    simp
  · beta_reduce at hc
    rw [prod_ev ev add, key] at hc
    funext i
    simpa using hc i

theorem root_ext {S : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(S, ⊤))) {u v : Γ(S, ⊤)ˣ} (hu : u ^ n = 1) (hv : v ^ n = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ S),
      Units.map x.appTop.hom.toMonoidHom u = Units.map x.appTop.hom.toMonoidHom v) : u = v := by
  let w : Γ(S, ⊤) := (u * v⁻¹ : Γ(S, ⊤)ˣ)
  have hw : w ^ n = 1 := by
    have : (u * v⁻¹) ^ n = 1 := by rw [mul_pow, inv_pow, hu, hv, inv_one, _root_.mul_one]
    exact congrArg Units.val this
  have unit : IsUnit (∑ i ∈ Finset.range n, w ^ i) := by
    refine RingedSpace.isUnit_of_isUnit_germ S.toLocallyRingedSpace.toRingedSpace ⊤ _ fun p hp => ?_
    refine (S.mem_basicOpen _ p hp).1 ?_
    let K := AlgebraicClosure (S.residueField p)
    let x : Sp K ⟶ S := Spec.map (CommRingCat.ofHom (algebraMap (S.residueField p) K)) ≫ S.fromSpecResidueField p
    have hx : x (default : PrimeSpectrum K) = p := Scheme.fromSpecResidueField_apply p _
    have h1 : x.appTop.hom w = 1 := by
      have : Units.map x.appTop.hom.toMonoidHom (u * v⁻¹) = 1 := by
        rw [map_mul, map_inv, h K x, mul_inv_cancel]
      exact congrArg Units.val this
    have h2 : IsUnit (x.appTop.hom (∑ i ∈ Finset.range n, w ^ i)) := by
      rw [map_sum]
      simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one]
      simpa using hn.map x.appTop.hom
    have h3 : x ⁻¹ᵁ S.basicOpen (∑ i ∈ Finset.range n, w ^ i) = ⊤ := by
      rw [Scheme.preimage_basicOpen_top]
      exact Scheme.basicOpen_of_isUnit _ h2
    rw [← hx]
    exact (h3.ge : _) (Set.mem_univ (default : PrimeSpectrum K))
  have h0 : w - 1 = 0 := by
    have := geom_sum_mul w n
    rw [hw, sub_self] at this
    exact (unit.mul_right_eq_zero).1 this
  exact mul_inv_eq_one.1 (Units.ext (sub_eq_zero.1 h0))

theorem exists_weilIs_root (hG : Out.GlobalFnsSt) {S : Scheme.{0}} (P : Out.PolAV S) (t : LB.Gen (Theta P.A P.L))
    (ht : t.IsGen) (n : ℕ) {T : Over S} {x y : T ⟶ P.A} (hx : x ^ n = 1) (hy : y ^ n = 1) :
    ∃ c : Γ(T.left, ⊤)ˣ, Out.WeilIs P.A P.L n x y c ∧ c ^ n = 1 := by
  have := P.isAb.comm
  have loc : ∀ z : T ⟶ P.A, z ^ n = 1 → ∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt = Out.overResι V ≫ z := fun z hz p => by
    obtain ⟨V, hV, H⟩ := (KerPow.locGen_theta_iff P.isLB P.ktriv
      (fun a c => (KerPow.locGen_iff _ _ _).1 (AbSquare.square_local P.isLB t ht T a c)) z n).2 hz p
    exact ⟨V, hV, KerPow.exists_theta z n V H⟩
  obtain ⟨c, hc⟩ := CommutatorPairing.exists_weilIs hG P.isAb P.isLB (loc x hx) (loc y hy)
  have pw : ∀ m : ℕ, Out.WeilIs P.A P.L n (x ^ (m + 1)) y (c ^ (m + 1)) := fun m => by
    induction m with
    | zero => rw [zero_add, pow_one, pow_one]; exact hc
    | succ m ih => rw [pow_succ x (m + 1), pow_succ c (m + 1)]; exact weilIs_mul_left hG S P n T _ _ _ _ _ ih hc
  have e := pw n
  rw [pow_succ x, hx, _root_.one_mul] at e
  have := CommutatorPairing.weilIs_unique hG P.isAb P.isLB e hc
  rw [pow_succ, mul_eq_right] at this
  exact ⟨c, hc, this⟩

theorem map_unitS {o K : Type} [CommRing o] [CommRing K] {S : Scheme.{0}} (s : S ⟶ Sp o) (x : Sp K ⟶ S) (β : o →+* K)
    (h : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  apply Units.ext
  have e₁ := congrArg (fun q : Sp K ⟶ Sp o => q.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom u)) h
  have e₂ := congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))
  simp only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.comp_apply] at e₁ e₂
  exact e₁.trans e₂.symm

theorem exists_tObj : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g : ℕ) (J : Type) (a : J → 𝓞 E) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] D.La) (l : Level H) (B o : Type) [CommRing B] [CommRing o] (bB : Base l B) (b : TBase o l.A) (ρ : o) (j : o →+* B) (S : Scheme.{0}) (s : S ⟶ Sp B) (ob : Obj D l bB s), IsSympBasis D bas → j ρ = bB.ρ → j (b.ζ : o) = bB.ζ → ∃ t : TObj g l.A J b (s ≫ spMap j), ObjUnder ob a bas t ∧ IsPEL D a bas ρ t ob.t := by
  intro hL _ E _ _ _ H D g J a bas l B o _ _ bB b ρ j S s ob hbas hρ hζ
  have hG := hL.globalFns
  have hg : Module.finrank ℚ E / 2 * (D.p + D.q) = g := by
    have h₁ := finrank_int_lattice D
    have h₂ := bas.finrank_eq
    rw [Module.finrank_fin_fun] at h₂
    omega
  let pt : Fin (2 * g) → (Out.baseOver S ⟶ ob.t.G) := fun i => toUnit _ ≫ ob.etaA (bas (Pi.single i 1))
  have hpt : ∀ (T : Over S) (f : T ⟶ Out.baseOver S) (i), f ≫ pt i = toUnit T ≫ ob.etaA (bas (Pi.single i 1)) :=
    fun T f i => by rw [← Category.assoc, comp_toUnit]
  have tors : ∀ i, pt i ^ l.A = 1 := fun i => by
    rw [← MonObj.comp_pow, ev_pow ob.etaA ob.etaA_add, ob.etaA_ker, MonObj.comp_one]
  have hβ : ∀ (K : Type) [Field K] (x : Sp K ⟶ S), x ≫ s = spMap (Spec.preimage (x ≫ s)).hom :=
    fun K _ x => (Spec.map_preimage (x ≫ s)).symm
  have hiso : LBIso ob.t.PP.L (ob.t.PP.L.pull (𝟙 ob.t.G.left)) :=
    (PolBaseChange.lbIso_refl ob.t.PP.isLB).chartPull (chartPullId _) (chartPullPull _ _ _ rfl)
  refine ⟨{ A := ob.t.G
            ab := ObjDim.isAbelianScheme ob
            dim := hg ▸ ObjDim.smoothOfRelativeDimension ob
            L := ob.t.PP.L
            isLB := ob.t.PP.isLB
            rigid := ObjDim.rigidified
            sym := ObjDim.sym
            ample := ob.ample
            ktriv := ob.ktriv
            pt := pt
            torsion := tors
            bij := fun K _ _ x y hy => ?_
            pairing := fun i i' => ?_
            act := fun c => ob.t.act.act (a c)
            hom := fun c => ob.t.act.hom (a c) },
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun i => ?_⟩,
    ⟨Iso.refl _, (inferInstance : IsMonHom (𝟙 ob.t.G)), hiso,
      fun c => (Category.comp_id _).trans (Category.id_comp _).symm, fun K _ _ _ x β hx => ?_⟩⟩
  · obtain ⟨-, I, -, hI, -⟩ := ob.geom K x _ (hβ K x)
    simp only [hpt, hI]
    exact existsUnique_label l.A_pos (I.ev l.A) (I.add l.A) (I.ker l.A l.A_pos) bas ((I.onto l.A l.A_pos y).1 hy)
  · obtain ⟨c, hc, hcn⟩ := exists_weilIs_root hG (Obj.toPolAV ob) ob.t.cub.t ob.t.cub.isGen l.A (tors i) (tors i')
    have hu : IsUnit ((l.A : ℕ) : Γ(S, ⊤)) := by
      simpa using ((bB.unit l.A l.A_pos).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom).map s.appTop.hom
    have hz : unitS (s ≫ spMap j) b.ζ ^ l.A = 1 := by
      have e := map_unitS (spMap j) (𝟙 _) j (Category.id_comp _) b.ζ
      have e₀ : Units.map j.toMonoidHom b.ζ ^ l.A = 1 := Units.ext (by
        show j b.ζ ^ l.A = 1
        rw [hζ, bB.ζ_prim.pow_eq_one])
      have e₁ : unitS (s ≫ spMap j) b.ζ = Units.map s.appTop.hom.toMonoidHom (unitOn (Units.map j.toMonoidHom b.ζ)) := by
        rw [← e]
        apply Units.ext
        simp [unitS]
        rfl
      rw [e₁, ← map_pow, unitOn, ← map_pow, e₀, map_one, map_one]
    have : c = unitS (s ≫ spMap j) b.ζ ^ Out.stdSymp g i i' := by
      refine root_ext (S := S) hu hcn (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow])
        fun K _ _ x => ?_
      obtain ⟨-, I, hIζ, hI, -⟩ := ob.geom K x _ (hβ K x)
      have h₁ := CommPairing.weilIs_pull hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB
        (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) hc
      rw [hpt, hpt, hI, hI] at h₁
      have h₂ := I.isom l.A l.A_pos (bas (Pi.single i 1)) (bas (Pi.single i' 1))
      refine (CommutatorPairing.weilIs_unique hG (ObjDim.isAbelianScheme ob) ob.t.PP.isLB h₁ h₂).trans ?_
      rw [hbas, map_zpow, map_unitS (s ≫ spMap j) x ((Spec.preimage (x ≫ s)).hom.comp j)
        (by rw [← Category.assoc, Geo.Tor.spMap_comp, ← hβ K x]), unitOn, unitOn, map_zpow]
      congr 2
      exact Units.ext (hIζ.trans (congrArg _ hζ.symm))
    exact this ▸ hc
  · have e : (toUnit (Out.baseOver S)).left = 𝟙 S :=
      (Category.comp_id _).symm.trans (Over.w (toUnit (Out.baseOver S)))
    show (ob.etaA _).left ≫ 𝟙 _ = (toUnit (Out.baseOver S)).left ≫ (ob.etaA _).left
    rw [e]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  · have e : (Spec.preimage (x ≫ s)).hom.comp j = β := by
      have : spMap ((Spec.preimage (x ≫ s)).hom.comp j) = spMap β := by
        rw [Geo.Tor.spMap_comp, ← hβ K x, Category.assoc, hx]
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective this)
    have e₁ : (Spec.preimage (x ≫ s)).hom bB.ρ = β ρ := by rw [← hρ]; exact RingHom.congr_fun e ρ
    have e₂ : (Spec.preimage (x ≫ s)).hom bB.ζ = β b.ζ := by rw [← hζ]; exact RingHom.congr_fun e b.ζ
    have hx' := ob.geom K x _ (hβ K x)
    rw [e₁, e₂] at hx'
    obtain ⟨hd, I, hIζ, hI, -⟩ := hx'
    refine ⟨hd, I, hIζ, fun i => ?_⟩
    exact (Category.comp_id _).trans ((hI _).symm.trans (hpt _ _ i).symm)

end GlobalTheory.ObjTheta
