import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.GoodClass
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.ThetaCosetLabels
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaLevelPullbackIdCompCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.HasThetaConstantsIffOfThetaLevelPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaConstantsLocallyOnBase
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverOfSubsingleton
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.ZM GlobalTheory.IndefiniteRowSideFullHecke.ThetaCosetLabels

noncomputable section
namespace GlobalTheory.ThetaObjCompare

def idx (g : ℕ) : Fin g ⊕ Fin g ≃ Fin (2 * g) := finSumFinEquiv.trans (finCongr (two_mul g).symm)

def labEquiv (g k : ℕ) : Lab g k ≃+ Ix g k where
  toFun a i := a ((idx g).symm i)
  invFun c j := c (idx g j)
  left_inv a := by funext j; simp
  right_inv c := by funext j; simp
  map_add' _ _ := rfl

theorem sum_stdSymp {g k : ℕ} (a c : Lab g k) :
    ∑ i, ∑ j, (Out.stdSymp g i j : ZMod k) * (labEquiv g k a i * labEquiv g k c j) = omegaLab a c := by
  have h₁ : ∀ i : Fin g, ((idx g (.inl i) : Fin (2 * g)) : ℕ) = i := fun i => rfl
  have h₂ : ∀ i : Fin g, ((idx g (.inr i) : Fin (2 * g)) : ℕ) = g + i := fun i => rfl
  have e₁ : ∀ i j : Fin g, Out.stdSymp g (idx g (.inl i)) (idx g (.inl j)) = 0 := fun i j => by
    simp only [Out.stdSymp, h₁]; rw [if_neg (by omega), if_neg (by omega)]
  have e₂ : ∀ i j : Fin g, Out.stdSymp g (idx g (.inr i)) (idx g (.inr j)) = 0 := fun i j => by
    simp only [Out.stdSymp, h₂]; rw [if_neg (by omega), if_neg (by omega)]
  have e₃ : ∀ i j : Fin g, Out.stdSymp g (idx g (.inl i)) (idx g (.inr j)) = if i = j then 1 else 0 := fun i j => by
    simp only [Out.stdSymp, h₁, h₂, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  have e₄ : ∀ i j : Fin g, Out.stdSymp g (idx g (.inr i)) (idx g (.inl j)) = if i = j then -1 else 0 := fun i j => by
    simp only [Out.stdSymp, h₁, h₂, Fin.ext_iff]
    split_ifs <;> first | rfl | omega
  rw [← (idx g).sum_comp]
  simp_rw [← (idx g).sum_comp]
  simp [Fintype.sum_sum_type, e₁, e₂, e₃, e₄, labEquiv, omegaLab, Finset.sum_sub_distrib, sub_eq_add_neg,
    Finset.sum_add_distrib, add_comm]

theorem zpow_eq_pow_val {U : Type} [CommGroup U] {u : U} {k : ℕ} [NeZero k] (hu : u ^ k = 1) {z : ℤ} {w : ZMod k}
    (h : (z : ZMod k) = w) : u ^ z = u ^ w.val := by
  rw [← zpow_natCast, zpow_eq_zpow_iff_modEq]
  refine Int.ModEq.of_dvd (Int.natCast_dvd_natCast.2 (orderOf_dvd_of_pow_eq_one hu)) ?_
  rw [← ZMod.intCast_eq_intCast_iff, h]; simp

section Weil
open Out
variable {S : Scheme.{0}} (P : PolAV S) {k : ℕ} {T : Over S}

theorem exists_weil {x y : T ⟶ P.A} (hx : x ^ k = 1) (hy : y ^ k = 1) : ∃ c, WeilIs P.A P.L k x y c :=
  have lft := (GlobalTheory.kerPow_of_square (GlobalTheory.AbSquare.square_of_cube GlobalTheory.AbLaw.CubeAssembly.cube_gen).1).2.2
  CommutatorPairing.exists_weilIs globalFns_holds P.isAb P.isLB (lft S P k T x hx) (lft S P k T y hy)

theorem weil_one {y : T ⟶ P.A} (hy : y ^ k = 1) : WeilIs P.A P.L k 1 y 1 := by
  obtain ⟨c, hc⟩ := exists_weil P (one_pow k) hy
  have h := weilIs_mul_left globalFns_holds S P k T _ _ _ _ _ hc hc
  rw [_root_.mul_one] at h
  have := CommutatorPairing.weilIs_unique globalFns_holds P.isAb P.isLB h hc
  rwa [mul_eq_left.1 this] at hc

theorem weil_prod {I : Type} (F : Finset I) {x : I → (T ⟶ P.A)} {y : T ⟶ P.A} (hy : y ^ k = 1) {c : I → Γ(T.left, ⊤)ˣ}
    (h : ∀ i, WeilIs P.A P.L k (x i) y (c i)) (a : I → ℕ) :
    letI := P.isAb.comm
    WeilIs P.A P.L k (∏ i ∈ F, x i ^ a i) y (∏ i ∈ F, c i ^ a i) := by
  letI := P.isAb.comm
  classical
  have hp : ∀ i n, WeilIs P.A P.L k (x i ^ n) y (c i ^ n) := fun i n => by
    induction n with
    | zero => simpa using weil_one P hy
    | succ n ih => rw [pow_succ, pow_succ]; exact weilIs_mul_left globalFns_holds S P k T _ _ _ _ _ ih (h i)
  induction F using Finset.induction_on with
  | empty => simpa using weil_one P hy
  | insert i F hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact weilIs_mul_left globalFns_holds S P k T _ _ _ _ _ (hp i _) ih

theorem linComb_eq {A : Over S} [GrpObj A] [IsCommMonObj A] {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    linComb y a = ∏ i, y i ^ a i := by
  rw [linComb, List.prod_ofFn]

theorem comp_linComb {A : Over S} [GrpObj A] {T' : Over S} (f : T' ⟶ T) {n : ℕ} (y : Fin n → (T ⟶ A)) (a : Fin n → ℕ) :
    f ≫ linComb y a = linComb (fun i => f ≫ y i) a :=
  ThetaObjPull.map_linComb (MonoidHom.mk' (fun x : T ⟶ A => f ≫ x) (fun x y => MonObj.comp_mul f x y)) y a

theorem weil_linComb {g : ℕ} [NeZero k] {p : Fin (2 * g) → (T ⟶ P.A)} (hp : ∀ i, p i ^ k = 1) {u : Γ(T.left, ⊤)ˣ}
    (hu : u ^ k = 1) (h : ∀ i j, WeilIs P.A P.L k (p i) (p j) (u ^ stdSymp g i j)) (a c : Lab g k) :
    WeilIs P.A P.L k (linComb p fun i => (labEquiv g k a i).val) (linComb p fun i => (labEquiv g k c i).val)
      (u ^ (omegaLab a c).val) := by
  letI := P.isAb.comm
  have h₁ := fun j => CommPairing.weilIs_symm P.isLB
    (weil_prod P Finset.univ (hp j) (fun i => h i j) fun i => (labEquiv g k a i).val)
  have h₂ := CommPairing.weilIs_symm P.isLB (weil_prod P Finset.univ
    (by rw [← linComb_eq]; exact ThetaLocal.linComb_pow_eq_one hp _) h₁ fun i => (labEquiv g k c i).val)
  rw [linComb_eq, linComb_eq]
  convert h₂ using 1
  rw [← zpow_eq_pow_val hu (z := ∑ j, ∑ i, stdSymp g i j * ((labEquiv g k a i).val * (labEquiv g k c j).val : ℕ))
    (by rw [← sum_stdSymp, Finset.sum_comm]; simp)]
  have hs : ∀ (F : Finset (Fin (2 * g))) (f : Fin (2 * g) → ℤ), u ^ ∑ i ∈ F, f i = ∏ i ∈ F, u ^ f i := fun F f =>
    map_prod (zpowersHom _ u) (fun i => Multiplicative.ofAdd (f i)) F ▸ rfl
  simp only [inv_pow, Finset.prod_inv_distrib, inv_inv, hs]
  refine Finset.prod_congr rfl fun j _ => ?_
  rw [← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← pow_mul, zpow_mul, zpow_natCast]

theorem notMem_basicOpen_of_geom {X : Scheme.{0}} {d : Γ(X, ⊤)}
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), x.appTop.hom d = 0) (p : X) : p ∉ X.basicOpen d := by
  intro hu
  let K := AlgebraicClosure (X.residueField p)
  let x : Sp K ⟶ X := spMap (algebraMap (X.residueField p) K) ≫ X.fromSpecResidueField p
  have hx : x (IsLocalRing.closedPoint K) = p := Scheme.fromSpecResidueField_apply p _
  have h₂ : IsLocalRing.closedPoint K ∈ x ⁻¹ᵁ X.basicOpen d := by
    show x _ ∈ X.basicOpen _
    rwa [hx]
  rw [Scheme.preimage_basicOpen_top] at h₂
  erw [h K x, Scheme.basicOpen_zero] at h₂
  exact h₂

theorem unit_eq_of_geom {X : Scheme.{0}} (hk : IsUnit (k : Γ(X, ⊤))) {c c' : Γ(X, ⊤)ˣ} (hc : c ^ k = 1) (hc' : c' ^ k = 1)
    (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X), x.appTop.hom c = x.appTop.hom c') : c = c' := by
  refine unit_ext fun p _ => ?_
  set φ : Γ(X, ⊤) →+* X.presheaf.stalk p := (X.presheaf.germ ⊤ p trivial).hom
  have key : φ c = φ c' := by
    have h₁ : IsLocalRing.residue _ (φ c) = IsLocalRing.residue _ (φ c') := by
      rw [← sub_eq_zero, ← map_sub, ← map_sub, IsLocalRing.residue_eq_zero_iff]
      exact fun hu => notMem_basicOpen_of_geom (fun K _ _ x => by rw [map_sub, h K x, sub_self]) p
        ((X.mem_basicOpen_top _ p).2 hu)
    set z := φ ((c * c'⁻¹ : Γ(X, ⊤)ˣ) : Γ(X, ⊤))
    have hz : z ^ k = 1 := by
      rw [← map_pow, ← Units.val_pow_eq_pow_val, mul_pow, inv_pow, hc, hc']; simp
    have hz' : z * φ c' = φ c := by rw [← map_mul]; simp
    have hr : IsLocalRing.residue _ z = 1 := by
      have hne : IsLocalRing.residue _ (φ c') ≠ 0 := ((c'.isUnit.map φ).map _).ne_zero
      apply mul_right_cancel₀ hne
      rw [← map_mul, hz', h₁, _root_.one_mul]
    have hs : IsUnit (∑ i ∈ Finset.range k, z ^ i) := by
      rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
      simpa [hr] using ((hk.map φ).map (IsLocalRing.residue _)).ne_zero
    have : z = 1 := sub_eq_zero.1 (hs.mul_right_eq_zero.1 (by rw [geom_sum_mul, hz, sub_self]))
    rw [← hz', this, _root_.one_mul]
  ext
  rw [gm_val (𝟙 X) p ⊤ trivial, gm_val (𝟙 X) p ⊤ trivial]
  exact key

end Weil

section Objects
variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}

theorem unitS_pull {T : Scheme.{0}} (x : T ⟶ S) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitS (x ≫ s) u := by
  ext; simp [unitS]; rfl

theorem unitS_spMap {K : Type} [CommRing K] (β : o →+* K) (u : oˣ) :
    unitS (spMap β) u = unitOn (Units.map β.toMonoidHom u) := by
  ext
  exact congrArg (fun f => f.hom u) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β)).symm

theorem unitOn_pow {K : Type} [CommRing K] (u : Kˣ) (n : ℕ) : unitOn (u ^ n) = unitOn u ^ n := map_pow _ _ _

theorem unitOn_root (K : Type) [Field K] (β : o →+* K) : unitOn (Units.map β.toMonoidHom b.ζ) ^ k = 1 := by
  rw [← unitOn_pow, show Units.map β.toMonoidHom b.ζ ^ k = 1 from Units.ext (b.prim K β).pow_eq_one]
  exact map_one _

theorem exists_spMap {R : Type} [CommRing R] (x : Sp R ⟶ Sp o) : ∃ β : o →+* R, x = spMap β :=
  ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩

theorem homMk_eq {T : Scheme.{0}} (x : T ⟶ S) :
    (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) = toUnit (Over.mk x) := toUnit_unique _ _

variable [NeZero k]

theorem lab_add (t : TObj g k J b s) (a c : Ix g k) : t.lab (a + c) = t.lab a * t.lab c := by
  letI := t.ab.comm
  simp only [TObj.lab, linComb_eq, ← Finset.prod_mul_distrib, ← pow_add]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (t.torsion i)]

theorem lab_single (t : TObj g k J b s) (i : Fin (2 * g)) : t.lab (Pi.single i 1) = t.pt i := by
  letI := t.ab.comm
  rw [TObj.lab, linComb_eq, Finset.prod_eq_single i (fun j _ hj => by simp [hj]) (by simp), Pi.single_eq_same,
    ZMod.val_one_eq_one_mod, ← pow_eq_pow_mod _ (t.torsion i), pow_one]

def toTh (t : TObj g k J b s) : ThObj g k J b.ζ s where
  P := t.pol
  dim := rfl
  lev a := t.lab (labEquiv g k a)
  lev_add a c := by rw [map_add]; exact lab_add t _ _
  geom K _ _ x β hβ := by
    have e : ∀ a, toUnit (Over.mk x) ≫ t.lab a = Out.linComb
        (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) (fun i => (a i).val) := fun a => by
      rw [homMk_eq]; exact comp_linComb _ _ _
    have hp : ∀ i, ((Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ t.pt i) ^ k = 1 := fun i => by
      rw [← MonObj.comp_pow, t.torsion, MonObj.comp_one]
    refine ⟨fun a c h => ?_, fun y hy => ?_, fun a c => ?_⟩
    · letI := t.ab.comm
      refine (labEquiv g k).injective ((t.bij K x _ (ThetaLocal.linComb_pow_eq_one hp _)).unique ?_ rfl)
      exact (e _).symm.trans (h.trans (e _))
    · obtain ⟨c, hc, -⟩ := t.bij K x y hy
      exact ⟨(labEquiv g k).symm c, by rw [AddEquiv.apply_symm_apply]; exact (e c).trans hc⟩
    · have hu := unitOn_root (b := b) K β
      have := weil_linComb t.pol hp hu (fun i j => by
        have h := CommPairing.weilIs_pull globalFns_holds t.ab t.isLB
          (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) (t.pairing i j)
        rw [map_zpow] at h
        erw [unitS_pull, hβ, unitS_spMap] at h
        exact h) a c
      rw [unitOn_pow]
      exact (e _).symm ▸ (e _).symm ▸ this
  endo := t.act
  endo_hom := t.hom

theorem toTh_injective : Function.Injective (toTh : TObj g k J b s → ThObj g k J b.ζ s) := by
  intro t t' h
  have hp : ∀ i, HEq (t.pt i) (t'.pt i) := fun i => by
    have : ∀ u : TObj g k J b s, u.pt i = (toTh u).lev ((labEquiv g k).symm (Pi.single i 1)) := fun u => by
      simp [toTh, lab_single]
    have hh : ∀ (X Y : ThObj g k J b.ζ s) (a), X = Y → HEq (X.lev a) (Y.lev a) := by rintro _ _ _ rfl; rfl
    exact (heq_of_eq (this t)).trans ((hh _ _ _ h).trans (heq_of_eq (this t')).symm)
  have ha : HEq (toTh t).endo (toTh t').endo := by rw [h]
  have hP : t.pol = t'.pol := congrArg ThObj.P h
  cases t; cases t'
  simp only [TObj.pol, Out.PolAV.mk.injEq] at hP
  obtain ⟨rfl, h₁, -, h₂⟩ := hP
  cases h₁; cases h₂
  obtain rfl := funext fun i => eq_of_heq (hp i)
  cases ha
  rfl

theorem toTh_surjective (hζ : unitS s b.ζ ^ k = 1) :
    Function.Surjective (toTh : TObj g k J b s → ThObj g k J b.ζ s) := by
  rintro ⟨P, rfl, lev, hadd, geom, endo, hendo⟩
  letI := P.isAb.comm
  let ℓ : Multiplicative (Lab P.g k) →* (𝟙_ (Over S) ⟶ P.A) := MonoidHom.mk' (fun a => lev a.toAdd) fun a c => hadd _ _
  have hℓ : ∀ a, lev a = ℓ (Multiplicative.ofAdd a) := fun _ => rfl
  let pt : Fin (2 * P.g) → (Out.baseOver S ⟶ P.A) := fun i => lev ((labEquiv P.g k).symm (Pi.single i 1))
  have tors : ∀ a, lev a ^ k = 1 := fun a => by
    rw [hℓ, ← map_pow, ← ofAdd_nsmul, show k • a = 0 from by funext i; simp, ofAdd_zero, map_one]
  have comb : ∀ c : Ix P.g k, Out.linComb pt (fun i => (c i).val) = lev ((labEquiv P.g k).symm c) := fun c => by
    have : c = ∑ i, (c i).val • Pi.single i 1 := by
      funext j; simp [-ZMod.natCast_val, Finset.sum_apply, Pi.single_apply, ZMod.natCast_zmod_val]
    conv_rhs => rw [this, map_sum, hℓ, ofAdd_sum, map_prod]
    rw [linComb_eq]
    exact Finset.prod_congr rfl fun i _ => by rw [map_nsmul, ofAdd_nsmul, map_pow]; rfl
  refine ⟨{ A := P.A, ab := P.isAb, dim := P.smoothDim, L := P.L, isLB := P.isLB, rigid := P.rigid, sym := P.sym
            ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := fun i => tors _, bij := fun K _ _ x y hy => ?_
            pairing := fun i j => ?_, act := endo, hom := hendo }, ?_⟩
  · obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨h₁, h₂, -⟩ := geom K x β hβ
    simp only [← comp_linComb, comb, homMk_eq]
    obtain ⟨a, ha⟩ := h₂ y hy
    exact ⟨labEquiv _ _ a, by simpa using ha, fun c hc => by
      rw [← h₁ _ _ (hc.trans ha.symm), AddEquiv.apply_symm_apply]⟩
  · obtain ⟨c, hc⟩ := exists_weil P (tors ((labEquiv P.g k).symm (Pi.single i 1)))
      (tors ((labEquiv P.g k).symm (Pi.single j 1)))
    have hck : c ^ k = 1 := by
      have h := weil_prod P (Finset.univ : Finset Unit) (tors _) (fun _ => hc) (fun _ => k)
      simp only [Finset.univ_unique, Finset.prod_singleton, tors] at h
      exact CommutatorPairing.weilIs_unique globalFns_holds P.isAb P.isLB h (weil_one P (tors _))
    have hk : IsUnit (k : Γ(S, ⊤)) := by
      simpa using (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
    have : c = unitS s b.ζ ^ Out.stdSymp P.g i j := by
      refine unit_eq_of_geom (X := S) hk hck (by rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow])
        fun K _ _ x => ?_
      obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
      have h := CommutatorPairing.weilIs_unique globalFns_holds P.isAb P.isLB
        (CommPairing.weilIs_pull globalFns_holds P.isAb P.isLB (toUnit (Over.mk x)) hc) ((geom K x β hβ).2.2 _ _)
      have hu := unitOn_root (b := b) K β
      rw [unitOn_pow, ← zpow_eq_pow_val hu (z := Out.stdSymp P.g i j)
        (by rw [← sum_stdSymp]; simp [Pi.single_apply]), ← unitS_spMap, ← hβ, ← unitS_pull, ← map_zpow] at h
      exact congrArg Units.val h
    exact this ▸ hc
  · simp only [toTh, TObj.lab, comb, AddEquiv.symm_apply_apply]
    rfl

def objEquiv (hζ : unitS s b.ζ ^ k = 1) : TObj g k J b s ≃ ThObj g k J b.ζ s :=
  Equiv.ofBijective toTh ⟨toTh_injective, toTh_surjective hζ⟩

end Objects

section Maps
variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g k : ℕ} {J : Type} {b : TBase o k} {s : S ⟶ Sp o} {s' : S' ⟶ Sp o}
  [NeZero k]

theorem toTh_lev (t : TObj g k J b s) (c : Ix g k) : (toTh t).lev ((labEquiv g k).symm c) = t.lab c :=
  congrArg t.lab (AddEquiv.apply_symm_apply _ c)

theorem level_iff {t' : TObj g k J b s'} {t : TObj g k J b s} {f : S' ⟶ S} {φ : t'.A.left ⟶ t.A.left}
    (h : IsGrpPullback t'.A t.A f φ) :
    (∀ i, (t'.pt i).left ≫ φ = f ≫ (t.pt i).left) ↔ ∀ a, ((toTh t').lev a).left ≫ φ = f ≫ ((toTh t).lev a).left := by
  refine ⟨fun H a => ?_, fun H i => by
    have := H ((labEquiv g k).symm (Pi.single i 1))
    simp only [toTh_lev, lab_single] at this
    exact this⟩
  have e := ThetaObjPull.map_linComb (pushHom h (Out.baseOver S')) t'.pt fun i => (labEquiv g k a i).val
  have e' := comp_linComb (ThetaObjPull.toBase f) t.pt fun i => (labEquiv g k a i).val
  have e'' : (fun i => pushHom h (Out.baseOver S') (t'.pt i)) = fun i => ThetaObjPull.toBase f ≫ t.pt i :=
    funext fun i => Over.OverMorphism.ext (H i)
  rw [e'', ← e'] at e
  exact congrArg (fun z => z.left) e

def forgetEnd (t : TObj g k J b s) : TObj g k PEmpty b s := { t with act := PEmpty.elim, hom := fun j => j.elim }

theorem isPB₀_iff (t' : TObj g k J b s') (t : TObj g k J b s) (f : S' ⟶ S) :
    IsPB₀ (toTh t') (toTh t) f ↔ f ≫ s = s' ∧ TMap (forgetEnd t') (forgetEnd t) f :=
  ⟨fun ⟨φ, h₀, h₁, h₂, h₃⟩ => ⟨h₀, φ, h₁, h₂, (level_iff h₁).2 h₃, fun j => j.elim⟩,
    fun ⟨h₀, φ, h₁, h₂, h₃, _⟩ => ⟨φ, h₀, h₁, h₂, (level_iff (t' := t') (t := t) h₁).1 h₃⟩⟩

end Maps

section Cosets
variable {g n N' : ℕ} {R : Type} [CommRing R]

theorem sameCoset_iff (h : n ∣ N') (hN : N' ≠ 0) (a c : Lab g (N' ^ 2)) :
    SameCoset n N' a c ↔ ∃ d, a = c + (N' / n) • d := by
  refine ⟨fun H => ?_, ?_⟩
  · obtain ⟨r, rfl⟩ := h
    have hn : n ≠ 0 := left_ne_zero_of_mul hN
    rw [Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hn)]
    have key : ∀ i, ∃ d : ZMod ((n * r) ^ 2), a i = c i + r • d := fun i => by
      rw [SameCoset, smul_smul] at H
      have Hi := congrFun H i
      rw [Pi.smul_apply, nsmul_eq_mul, Pi.sub_apply, Pi.zero_apply] at Hi
      obtain ⟨z, hz⟩ := ZMod.intCast_surjective (a i - c i)
      have h0 : (((n * (n * r) : ℕ) * z : ℤ) : ZMod ((n * r) ^ 2)) = 0 := by
        rw [Int.cast_mul, Int.cast_natCast, hz]; exact Hi
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h0
      have h2 : ((n * (n * r) : ℕ) : ℤ) ≠ 0 := by exact_mod_cast mul_ne_zero hn hN
      obtain ⟨d, rfl⟩ : (r : ℤ) ∣ z := (mul_dvd_mul_iff_left h2).1 (by
        rwa [show ((n * (n * r) : ℕ) : ℤ) * r = (((n * r) ^ 2 : ℕ) : ℤ) by push_cast; ring])
      refine ⟨(d : ZMod _), ?_⟩
      rw [nsmul_eq_mul]; push_cast at hz; linear_combination -hz
    choose d hd using key
    exact ⟨d, funext hd⟩
  · rintro ⟨d, rfl⟩
    rw [SameCoset, add_sub_cancel_left, smul_smul, smul_smul, show n * N' * (N' / n) = N' ^ 2 by
      rw [mul_right_comm, Nat.mul_div_cancel' h, sq]]
    funext i; simp [-Nat.cast_pow]

theorem coset_iff (h : n ∣ N') (hN : N' ≠ 0) (v : Ix g (N' ^ 2) → R) (q : Ideal R) :
    Coset n N' v q ↔ ∀ c, ∃ a, SameCoset n N' a c ∧ v (labEquiv g _ a) ∉ q := by
  simp only [sameCoset_iff h hN]
  refine ⟨fun H c => ?_, fun H a => ?_⟩
  · obtain ⟨d, hd⟩ := H (labEquiv g _ c)
    exact ⟨_, ⟨(labEquiv g _).symm d, rfl⟩, by simpa only [map_add, map_nsmul, AddEquiv.apply_symm_apply] using hd⟩
  · obtain ⟨_, ⟨d, rfl⟩, hd⟩ := H ((labEquiv g _).symm a)
    exact ⟨labEquiv g _ d, by simpa only [map_add, map_nsmul, AddEquiv.apply_symm_apply] using hd⟩

end Cosets

section Classes
variable {o : Type} [CommRing o] {S S' : Scheme.{0}} {g N' : ℕ} {J : Type} {b : TBase o (N' ^ 2)} {s : S ⟶ Sp o}
  {em : o →+* ℂ} [NeZero N']

def toClass (C : TObj g (N' ^ 2) J b (spMap em) → Prop) : CClass g N' J b.ζ em := toTh '' {t | C t}

theorem spMap_comp {A B D : Type} [CommRing A] [CommRing B] [CommRing D] (f : A →+* B) (h : B →+* D) :
    spMap h ≫ spMap f = spMap (h.comp f) := (Spec.map_comp (CommRingCat.ofHom f) (CommRingCat.ofHom h)).symm

theorem spMap_injective {A B : Type} [CommRing A] [CommRing B] {f h : A →+* B} (e : spMap f = spMap h) : f = h :=
  congrArg (fun z => z.hom) (Spec.map_injective e)

end Classes

end GlobalTheory.ThetaObjCompare
end
