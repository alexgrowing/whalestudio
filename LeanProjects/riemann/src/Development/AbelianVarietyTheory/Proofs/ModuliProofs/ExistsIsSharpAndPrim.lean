import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfUnimodular
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.BiadditiveOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsClopenOfIsLocallyNoetherian
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.EighthPower

open MatrixBundle CechPic

theorem eq_of_sq_eq {U : Type*} [CommGroup U] {k : ℕ} (hk : Odd k) {a b : U} (ha : a ^ k = 1) (hb : b ^ k = 1)
    (h : a ^ 2 = b ^ 2) : a = b := by
  obtain ⟨m, rfl⟩ := hk
  rw [pow_succ, pow_mul] at ha hb
  rw [h] at ha
  exact mul_left_cancel (ha.trans hb.symm)

theorem omegaStd_add_left {h : ℕ} (a a' b : Fin h ⊕ Fin h → ℤ) : omegaStd (a + a') b = omegaStd a b + omegaStd a' b := by
  simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem omegaStd_add_right {h : ℕ} (a b b' : Fin h ⊕ Fin h → ℤ) : omegaStd a (b + b') = omegaStd a b + omegaStd a b' := by
  simp only [omegaStd, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem existsUnique_label {H Λ I : Type} [CommGroup H] [AddCommGroup Λ] {m k : ℕ} [NeZero k]
    (bas : (Fin m → ℤ) ≃ₗ[ℤ] (I → Λ)) (l : Λ → H) (hl : ∀ a b, l (a + b) = l a * l b)
    (hk : ∀ a, l a = 1 ↔ ∃ b, a = k • b) (a : I → Λ) :
    ∃! c : Fin m → ZMod k, ∀ u, ∏ i, l (bas (Pi.single i 1) u) ^ (c i).val = l (a u) := by
  let F : Λ →+ Additive H := AddMonoidHom.mk' (fun a => Additive.ofMul (l a)) fun a b => congrArg _ (hl a b)
  have e : ∀ (n : Fin m → ℕ) u, ∏ i, l (bas (Pi.single i 1) u) ^ n i = l (bas (fun i => (n i : ℤ)) u) := fun n u => by
    have : (fun i => (n i : ℤ)) = ∑ i, n i • (Pi.single i 1 : Fin m → ℤ) := by
      ext j
      simp [Finset.sum_apply, Pi.single_apply]
    rw [this, map_sum, Finset.sum_apply]
    refine Eq.trans ?_ (congrArg Additive.toMul (map_sum F _ _)).symm
    rw [toMul_sum]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [map_nsmul, Pi.smul_apply, map_nsmul]
    rfl
  have eq : ∀ a a', l a = l a' ↔ ∃ b, a - a' = k • b := fun a a' => by
    rw [← hk, ← div_eq_one]
    exact Eq.congr_left (congrArg Additive.toMul (map_sub F a a')).symm
  have iff : ∀ c : Fin m → ZMod k, (∀ u, ∏ i, l (bas (Pi.single i 1) u) ^ (c i).val = l (a u)) ↔
      c = fun i => ((bas.symm a i : ℤ) : ZMod k) := fun c => by
    simp only [e, eq]
    constructor
    · intro h
      choose b hb using h
      have h₁ : (fun i => ((c i).val : ℤ)) - bas.symm a = k • bas.symm b := by
        apply bas.injective
        rw [map_sub, map_nsmul, bas.apply_symm_apply, bas.apply_symm_apply]
        exact funext hb
      funext i
      have h₂ := congrArg (fun z : ℤ => (z : ZMod k)) (congrFun h₁ i)
      simpa [sub_eq_zero] using h₂
    · rintro rfl u
      have : ∀ i, ∃ w : ℤ, ((((bas.symm a i : ℤ) : ZMod k).val : ℤ)) - bas.symm a i = k * w := fun i =>
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ k).1 (by simp)
      choose w hw using this
      have h₁ : (fun i => ((((bas.symm a i : ℤ) : ZMod k).val : ℤ))) - bas.symm a = k • w := funext fun i => by
        simpa using hw i
      have h₂ := congrArg bas h₁
      rw [map_sub, map_nsmul, bas.apply_symm_apply] at h₂
      exact ⟨bas w u, congrFun h₂ u⟩
  exact ⟨_, (iff _).2 rfl, fun c hc => (iff c).1 hc⟩

theorem isMonHom_of_matrix {S : Scheme.{0}} {A G : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj G] {n : ℕ}
    {pr : Fin n → (G ⟶ A)} (hpr : ∀ u, IsMonHom (pr u))
    (hu : ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) {f : G ⟶ G}
    {m₀ : Matrix (Fin n) (Fin n) ℤ} (hf : ∀ u, f ≫ pr u = ∏ v, pr v ^ m₀ u v) : IsMonHom f := by
  let F : ∀ (T : Over S) (u : Fin n), (T ⟶ G) →* (T ⟶ A) := fun T u =>
    MonoidHom.mk' (fun z => z ≫ pr u) fun x y => congrFun (coord_mul hpr x y) u
  have m : ∀ (T : Over S) (x : T ⟶ G) u, (x ≫ f) ≫ pr u = ∏ v, (x ≫ pr v) ^ m₀ u v := fun T x u => by
    let F' : (G ⟶ A) →* (T ⟶ A) := MonoidHom.mk' (fun z => x ≫ z) fun a b => MonObj.comp_mul _ _ _
    refine (Category.assoc _ _ _).trans ((congrArg F' (hf u)).trans ((map_prod F' _ _).trans ?_))
    exact Finset.prod_congr rfl fun v _ => map_zpow F' _ _
  have m₁ : ∀ T : Over S, (1 : T ⟶ G) ≫ f = 1 := fun T =>
    (hu T 1).unique (fun u => (m T 1 u).trans (Finset.prod_eq_one fun v _ => by
      rw [show (1 : T ⟶ G) ≫ pr v = 1 from map_one (F T v), one_zpow])) fun u => map_one (F T u)
  have m₂ : ∀ (T : Over S) (x y : T ⟶ G), (x * y) ≫ f = (x ≫ f) * (y ≫ f) := fun T x y =>
    (hu T fun u => ((x * y) ≫ f) ≫ pr u).unique (fun u => rfl) fun u => by
      refine (map_mul (F T u) _ _).trans ((congrArg₂ (· * ·) (m T x u) (m T y u)).trans (Eq.trans ?_ (m T _ u).symm))
      rw [← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun v _ => ?_
      rw [show (x * y) ≫ pr v = (x ≫ pr v) * (y ≫ pr v) from map_mul (F T v) x y, mul_zpow]
  constructor
  · simpa only [Hom.one_def, toUnit_unit, Category.id_comp] using m₁ (𝟙_ _)
  · have := m₂ _ (fst G G) (snd G G)
    rw [Hom.mul_def, Hom.mul_def, lift_fst_snd, Category.id_comp] at this
    rw [this]
    congr 1

theorem exists_power {S : Scheme.{0}} (A : Over S) [GrpObj A] (hA : IsAbelianScheme A) {h : ℕ}
    (hd : SmoothOfRelativeDimension h A.hom) (n : ℕ) : ∃ (G : Over S) (_ : GrpObj G) (pr : Fin n → (G ⟶ A)),
      IsAbelianScheme G ∧ SmoothOfRelativeDimension (n * h) G.hom ∧ (∀ u, IsMonHom (pr u)) ∧
      ∀ (T : Over S) (y : Fin n → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u :=
  ⟨Out.powObj A n, inferInstance, Out.powPr A, (PowGrp.powers S _ A n (Out.powIsPowGrp A n)).2.2.2.1 hA,
    PowGrp.relDim_powObj A h hd n, fun u => Out.powPr.isMonHom A u, fun T y =>
    ⟨(Out.powIsLimit A n).lift (Fan.mk T y), fun u => (Out.powIsLimit A n).fac (Fan.mk T y) ⟨u⟩,
      fun x hx => (Out.powIsLimit A n).uniq (Fan.mk T y) x fun u => hx u.as⟩⟩

theorem eq_of_geometric {X : Scheme.{0}} {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤))) {c c' : Γ(X, ⊤)ˣ} (hc : c ^ n = 1)
    (hc' : c' ^ n = 1) (h : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Sp K ⟶ X),
      Units.map x.appTop.hom.toMonoidHom c = Units.map x.appTop.hom.toMonoidHom c') : c = c' := by
  obtain ⟨U, -, H⟩ := PairingLocus.exists_clopen_eq hn hc hc'
  have e := (H X (𝟙 X)).2 fun p _ => (H _ _).1 (h (AlgebraicClosure (X.residueField p))
    (spMap (algebraMap (X.residueField p) _) ≫ X.fromSpecResidueField p))
    ⟨IsLocalRing.closedPoint _, Scheme.fromSpecResidueField_apply p _⟩
  exact Units.ext (by simpa using congrArg Units.val e)

theorem map_unitS {o R : Type} [CommRing o] [CommRing R] {S : Scheme.{0}} {s : S ⟶ Sp o} {x : Sp R ⟶ S} {β : o →+* R}
    (hβ : x ≫ s = spMap β) (u : oˣ) :
    Units.map x.appTop.hom.toMonoidHom (unitS s u) = unitOn (Units.map β.toMonoidHom u) := by
  have r₁ : Units.map x.appTop.hom.toMonoidHom (unitS s u) =
      Units.map (x ≫ s).appTop.hom.toMonoidHom (unitOn u) := rfl
  rw [r₁, hβ]
  exact Units.ext (congrArg (fun q => q.hom (u : o)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom β))).symm

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (f : Sp B ⟶ Sp A) : ∃ β : A →+* B, f = spMap β :=
  ⟨(Spec.preimage f).hom, (Spec.map_preimage f).symm⟩

variable {h g : ℕ} {W : Matrix (Fin 8) (Fin 8) ℤ} {J : Type} {k : ℕ} {o : Type} [CommRing o] {b : TBase o k}
  {S : Scheme.{0}} {s : S ⟶ Sp o}

theorem isSymBilin (hG : Out.GlobalFnsSt) {ζ : o} (c : SiegPre h k ζ s) (hc : Out.RelAmple c.A c.diag) :
    IsSymBilin (cls c.P c.isLB) :=
  isSymBilin_of_gen c.isLB (fun T x x' y => (Biadditive.biadditive_of_triv_axes hG S c.A c.diag c.ab
    (pull_isLB c.isLB _) hc c.P c.isLB c.rig₁ c.rig₂ T x x' y).1) c.symm

theorem exists_isSharp (hG : Out.GlobalFnsSt) (a : J → Matrix (Fin 8) (Fin 8) ℤ)
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : IsE8 W) (hbas : IsSharpBasis W bas)
    (c : SiegPre h k (b.ζ : o) s)
    (hex : ∀ (P : Out.PolAV S) (x y : Out.baseOver S ⟶ P.A), x ^ k = 1 → y ^ k = 1 → ∃ c, Out.WeilIs P.A P.L k x y c)
    (hζ : b.ζ ^ k = 1) (hk : Odd k) (hc : c.Principal) (hd : SmoothOfRelativeDimension h c.A.hom) :
    ∃ t : TObj g k J b s, IsSharp W a bas t c := by
  have hg : g = 8 * h := by
    have := bas.finrank_eq
    simp only [Module.finrank_pi_fintype, Module.finrank_self, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      Fintype.card_sum, smul_eq_mul] at this
    omega
  haveI : NeZero k := ⟨hk.pos.ne'⟩
  obtain ⟨G, _, pr, hA, hdim, hpr, hu⟩ := exists_power c.A c.ab hd 8
  have := hA.comm
  have hb := isSymBilin hG c hc.1
  have hL : (matLB c.P pr W).IsLB := LB.isLB_linComb c.isLB _ _
  let F : ∀ (T : Over S) (u : Fin 8), (T ⟶ G) →* (T ⟶ c.A) := fun T u =>
    MonoidHom.mk' (fun z => z ≫ pr u) fun x y => congrFun (coord_mul hpr x y) u
  have hl : ∀ (T : Over S) a a', toUnit T ≫ c.lev (a + a') = (toUnit T ≫ c.lev a) * (toUnit T ≫ c.lev a') :=
    fun T a a' => by rw [c.lev_add, MonObj.comp_mul]
  choose pt hpt using fun i => (hu (Out.baseOver S) fun u => toUnit _ ≫ c.lev (bas (Pi.single i 1) u)).exists
  have hpt' : ∀ (T : Over S) (x : T ⟶ Out.baseOver S) i u,
      (x ≫ pt i) ≫ pr u = toUnit T ≫ c.lev (bas (Pi.single i 1) u) := fun T x i u => by
    rw [Category.assoc, hpt, comp_toUnit_assoc]
  have tors : ∀ i, pt i ^ k = 1 := fun i => (hu _ 1).unique (fun u => by
    refine (map_pow (F _ u) _ _).trans ((congrArg (· ^ k) (hpt i u)).trans ?_)
    rw [← MonObj.comp_pow, c.lev_tors, MonObj.comp_one]; rfl) fun u => map_one (F _ u)
  choose act hact using fun j => (hu G fun u => ∏ v, pr v ^ a j u v).exists
  let P : Out.PolAV S :=
    { A := G, isAb := hA, g := g, smoothDim := hg ▸ hdim, L := matLB c.P pr W, isLB := hL
      rigid := rigidified_matLB c.isLB hb hpr, sym := sym_matLB c.isLB hb hpr
      ample := _root_.GlobalTheory.PosDefAmple.relAmple_linComb_of_posDef hG h k 8 o _ S s c G pr W hpr hu hc.1 hW.1
      ktriv := kTriv_matLB c.isLB hb hpr hu hW.2 hc.2 }
  refine ⟨{ A := G, ab := hA, dim := P.smoothDim, L := matLB c.P pr W, isLB := hL, rigid := P.rigid, sym := P.sym
            ample := P.ample, ktriv := P.ktriv, pt := pt, torsion := tors, bij := ?_, pairing := ?_, act := act
            hom := ?_ }, pr, hpr, hu, PolBaseChange.lbIso_refl hL, fun j u => ?_, fun i u => ?_⟩
  · intro K _ _ x y hy
    obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
    obtain ⟨g₁, g₂, -⟩ := c.geom K x β (Units.map β.toMonoidHom b.ζ) hβ rfl
    choose α hα using fun u => g₂ (y ≫ pr u) ((map_pow (F _ u) _ _).symm.trans (by rw [hy, map_one]))
    refine (existsUnique_congr fun n => ?_).1
      (existsUnique_label bas (fun a => toUnit (Over.mk x) ≫ c.lev a) (hl _) g₁ α)
    have e : ∀ u, Out.linComb (fun i => (Over.homMk x (by simp) : Over.mk x ⟶ Out.baseOver S) ≫ pt i)
        (fun i => (n i).val) ≫ pr u = ∏ i, (toUnit (Over.mk x) ≫ c.lev (bas (Pi.single i 1) u)) ^ (n i).val := fun u => by
      rw [Out.linComb, List.prod_ofFn]
      refine (map_prod (F _ u) _ _).trans (Finset.prod_congr rfl fun i _ => ?_)
      exact (map_pow (F _ u) _ _).trans (congrArg (· ^ (n i).val) (hpt' _ _ i u))
    constructor
    · exact fun H => (hu _ fun u => y ≫ pr u).unique (fun u => (e u).trans ((H u).trans (hα u))) fun u => rfl
    · exact fun H u => (e u).symm.trans ((congrArg (· ≫ pr u) H).trans (hα u).symm)
  · intro i j
    obtain ⟨c₀, h₀⟩ := hex P (pt i) (pt j) (tors i) (tors j)
    have p₀ : c₀ ^ k = 1 := PairingLocus.pow_eq_one hG P k (tors i) h₀
    have p₁ : unitS s b.ζ ^ k = 1 := by
      rw [unitS, unitOn, ← map_pow, ← map_pow, hζ, map_one, map_one]
    have p₂ : (unitS s b.ζ ^ Out.stdSymp g i j) ^ k = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, p₁, one_zpow]
    have hn : IsUnit (k : Γ(S, ⊤)) := by
      have := (b.unit.map (Scheme.ΓSpecIso (CommRingCat.of o)).inv.hom).map s.appTop.hom
      rwa [map_natCast, map_natCast] at this
    have e' := eq_of_geometric (X := S) hn p₀ p₂ fun K _ _ x => by
      obtain ⟨β, hβ⟩ := exists_spMap (x ≫ s)
      obtain ⟨-, -, g₃⟩ := c.geom K x β (Units.map β.toMonoidHom b.ζ) hβ rfl
      let X : Over.mk x ⟶ Out.baseOver S := Over.homMk x (by simp)
      have q := sq_eq_of_weilIs c.isLB hb hpr hG hA (fun a => toUnit (Over.mk x) ≫ c.lev a) (hl _) omegaStd
        omegaStd_add_left omegaStd_add_right (unitOn (Units.map β.toMonoidHom b.ζ))
        (fun a a' => (congrArg (Out.WeilIs _ _ _ _ _) (map_zpow _ _ _)).mp (g₃ a a')) (hpt' _ X i) (hpt' _ X j)
        (CommPairing.weilIs_pull hG hA hL X h₀)
      rw [hbas i j] at q
      refine eq_of_sq_eq hk (by rw [← map_pow, p₀, map_one]) (by rw [← map_pow, p₂, map_one]) (q.trans ?_)
      rw [map_zpow, map_unitS hβ, mul_comm, zpow_mul]
      rfl
    exact e' ▸ h₀
  · exact fun j => isMonHom_of_matrix hpr hu (hact j)
  · exact (hact j u).trans List.prod_ofFn.symm
  · refine (congrArg CommaMorphism.left (hpt i u)).trans ?_
    exact Category.id_comp _

theorem prim_of_isSharp (hG : Out.GlobalFnsSt) {a : J → Matrix (Fin 8) (Fin 8) ℤ} {w w' : J}
    {bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))} (hW : (W + W.transpose).det = 1)
    (hw : (W + W.transpose) * a w = W) (hw' : (W + W.transpose) * a w' = W.transpose)
    {c : SiegPre h k (b.ζ : o) s} (hc : Out.RelAmple c.A c.diag) {t : TObj g k J b s} (H : IsSharp W a bas t c) :
    t.Prim w w' := by
  obtain ⟨pr, hpr, hu, hL, ha, -⟩ := H
  have hb := isSymBilin hG c hc
  have ha' : ∀ j u, t.act j ≫ pr u = ∏ v, pr v ^ a j u v := fun j u => (ha j u).trans List.prod_ofFn
  have hone : ∀ u, ∏ v, pr v ^ (1 : Matrix (Fin 8) (Fin 8) ℤ) u v = pr u := fun u => by
    rw [Finset.prod_eq_single u (fun v _ hv => by rw [Matrix.one_apply_ne' hv, zpow_zero]) (by simp),
      Matrix.one_apply_eq, zpow_one]
  have hid : ∀ u, 𝟙 t.A ≫ pr u = ∏ v, pr v ^ (1 : Matrix (Fin 8) (Fin 8) ℤ) u v := fun u =>
    (Category.id_comp _).trans (hone u).symm
  have h₁ : a w + a w' = 1 := by
    have hu : IsUnit (W + W.transpose) := (Matrix.isUnit_iff_isUnit_det _).2 (hW ▸ isUnit_one)
    apply hu.mul_left_cancel
    rw [Matrix.mul_add, hw, hw', Matrix.mul_one]
  have h₂ : (a w).transpose * (W + W.transpose) = W.transpose := by
    have := congrArg Matrix.transpose hw
    rwa [Matrix.transpose_mul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm W.transpose] at this
  refine ⟨(hu t.A pr).unique (fun u => ?_) (fun u => Category.id_comp _), ?_, ?_⟩
  · haveI := hpr u
    rw [MonObj.mul_comp, ha', ha', ← Finset.prod_mul_distrib, ← hone u, ← h₁]
    exact Finset.prod_congr rfl fun v _ => (zpow_add _ _ _).symm
  · refine (cls_eq_iff (LB.isLB_linComb t.isLB _ _) (LB.isLB_linComb t.isLB _ _)).1
      ((cls_cube_two t.isLB _ _ _).trans (Eq.trans ?_ (cls_cube_two t.isLB _ _ _).symm))
    have e₁ := lam_subst c.isLB hb hpr t.isLB hL (fst t.A t.A) (snd t.A t.A) (ha' w) hid
    have e₂ := lam_subst c.isLB hb hpr t.isLB hL (fst t.A t.A) (snd t.A t.A) hid (ha' w')
    rw [Category.comp_id, Matrix.mul_one, h₂] at e₁
    rw [Category.comp_id, Matrix.transpose_one, Matrix.one_mul, hw'] at e₂
    exact e₁.trans e₂.symm
  · refine (cls_eq_iff t.isLB (LB.isLB_linComb t.isLB _ _)).1 (Eq.trans ?_ (cls_cube_two t.isLB _ _ _).symm)
    have e₁ := lam_subst c.isLB hb hpr t.isLB hL (𝟙 t.A) (𝟙 t.A) hid (ha' w)
    rw [Category.comp_id, Category.id_comp, Matrix.transpose_one, Matrix.one_mul, hw,
      ← pull_matLB c.isLB (LB.isLB_linComb c.isLB _ _)] at e₁
    exact ((cls_eq_iff t.isLB (LB.isLB_linComb c.isLB _ _)).2 hL).trans ((pull_id _).symm.trans e₁.symm)

end GlobalTheory.EighthPower

theorem GlobalTheory.exists_isSharp_and_prim : Out.Laws → Out.Laws2 → (∀ (S : Scheme.{0}) (P : Out.PolAV S) (M : LB P.A.left), M.IsLB → ∃ t : LB.Gen (Theta P.A M), t.IsGen) → ∀ (h g : ℕ) (W : Matrix (Fin 8) (Fin 8) ℤ) (J : Type) [Finite J] (a : J → Matrix (Fin 8) (Fin 8) ℤ) (w w' : J) (bas : (Fin (2 * g) → ℤ) ≃ₗ[ℤ] (Fin 8 → (Fin h ⊕ Fin h → ℤ))), IsE8 W → IsSharpBasis W bas → (W + W.transpose) * a w = W → (W + W.transpose) * a w' = W.transpose → (∀ u v, ∃ j, a j = Matrix.single u v 1) → ∀ (k : ℕ) (o : Type) [CommRing o] (b : TBase o k) (S : Scheme.{0}) [IsLocallyNoetherian S] (s : S ⟶ Sp o) (c : SiegPre h k (b.ζ : o) s), b.ζ ^ k = 1 → Odd k → c.Principal → SmoothOfRelativeDimension h c.A.hom → ∃ t : TObj g k J b s, IsSharp W a bas t c ∧ t.Prim w w' := by
  intro hL _ _ h g W J _ a w w' bas hW hbas hw hw' _ k o _ b S _ s c hζ hk hc hd
  obtain ⟨t, ht⟩ := GlobalTheory.EighthPower.exists_isSharp hL.globalFns a hW hbas c
    (fun P x y hx hy => ((hL.weil S P k _).1 x y hx hy).exists) hζ hk hc hd
  exact ⟨t, ht, GlobalTheory.EighthPower.prim_of_isSharp hL.globalFns hW.2 hw hw' hc.1 ht⟩

end
