import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToIThCapDegOfAddNsmulDivP
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ScaledTwistingSheafSpec
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace TensorProduct IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert
open GlobalTheory.LB (resG_resG resG_self val_res toMod coord ofSec)

namespace GlobalTheory.ShFam.Pad

namespace FinLB

variable {X Y : Scheme.{0}}

def ofCharts (L : LB X) (hL : L.IsLB) {n : ℕ} (f : Fin n → L.ι) (hf : ⨆ i, L.U (f i) = ⊤) : FinLB X :=
  ⟨n, fun i => L.U (f i), fun i j => L.g (f i) (f j), hf, fun _ => hL.g_self _, fun _ _ _ => hL.cocycle _ _ _⟩

def cls (L : FinLB X) : Pic X := CechPic.cls L.lb L.isLB

theorem cls_ofCharts (L : LB X) (hL : L.IsLB) {n : ℕ} (f : Fin n → L.ι) (hf : ⨆ i, L.U (f i) = ⊤) :
    (ofCharts L hL f hf).cls = CechPic.cls L hL :=
  (cls_eq_iff _ hL).2 (iso_of_chart hL ⟨f, fun _ => le_rfl, fun _ _ _ _ _ => rfl⟩)

def ofFintype (L : LB X) (hL : L.IsLB) [Fintype L.ι] : FinLB X :=
  ofCharts L hL (Fintype.equivFin L.ι).symm ((Fintype.equivFin L.ι).symm.iSup_comp.trans hL.cover)

theorem cls_ofFintype (L : LB X) (hL : L.IsLB) [Fintype L.ι] : (ofFintype L hL).cls = CechPic.cls L hL :=
  cls_ofCharts _ _ _ _

theorem exists_charts [CompactSpace X] {L : LB X} (hL : L.IsLB) :
    ∃ (n : ℕ) (f : Fin n → L.ι), ⨆ i, L.U (f i) = ⊤ := by
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun i => (L.U i : Set X)) (fun i => (L.U i).isOpen)
    fun x _ => Set.mem_iUnion.2 (LB.mem_of_cover hL x)
  refine ⟨s.card, fun i => (s.equivFin.symm i).1, top_le_iff.1 fun x _ => ?_⟩
  obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
  exact Opens.mem_iSup.2 ⟨s.equivFin ⟨i, hi⟩, by simpa using hx⟩

theorem cls_surjective [CompactSpace X] : Function.Surjective (cls (X := X)) := fun c => by
  obtain ⟨L, hL, rfl⟩ := cls_surj c
  obtain ⟨n, f, hf⟩ := exists_charts hL
  exact ⟨_, cls_ofCharts L hL f hf⟩

theorem cls_eq_iff {L M : FinLB X} : L.cls = M.cls ↔ LBIso L.lb M.lb := CechPic.cls_eq_iff _ _

def dual (L : FinLB X) : FinLB X := ⟨L.n, L.U, fun i j => (L.g i j)⁻¹, isLB_dual L.isLB⟩

theorem lb_dual (L : FinLB X) : L.dual.lb = CechPic.dual L.lb := rfl

variable (X) in

def triv : FinLB X := ofFintype (LB.triv X) (LB.isLB_triv X)

def tens (L M : FinLB X) : FinLB X :=
  @ofFintype X (CechPic.tens L.lb M.lb) (isLB_tens L.isLB M.isLB) (inferInstanceAs (Fintype (Fin L.n × Fin M.n)))

@[simp] theorem cls_dual (L : FinLB X) : L.dual.cls = -L.cls := CechPic.cls_dual L.isLB _

@[simp] theorem cls_triv : (triv X).cls = 0 := cls_ofFintype _ _

@[simp] theorem cls_tens (L M : FinLB X) : (L.tens M).cls = L.cls + M.cls :=
  @cls_ofFintype X (CechPic.tens L.lb M.lb) _ (inferInstanceAs (Fintype (Fin L.n × Fin M.n)))

@[simp] theorem cls_pull (L : FinLB X) (f : Y ⟶ X) : (L.pull f).cls = CechPic.pull f L.cls :=
  (CechPic.cls_eq_iff _ (Semi.LB.isLB_pull L.isLB f)).2 (L.lbIso_pull f)

def c1 (L : FinLB X) : PicSym X := Vert.c1 L.lb L.isLB

theorem c1_eq (L : FinLB X) : L.c1 = firstChernPic L.cls := rfl

@[simp] theorem firstChern_dual (L : FinLB X) : L.dual.c1 = -L.c1 := by simp [c1_eq]

@[simp] theorem firstChern_trivial : (triv X).c1 = 0 := by simp [c1_eq]

@[simp] theorem firstChernTensor (L M : FinLB X) : (L.tens M).c1 = L.c1 + M.c1 := by simp [c1_eq]

theorem firstChernCongr {L M : FinLB X} (h : LBIso L.lb M.lb) : L.c1 = M.c1 := by
  rw [c1_eq, c1_eq, cls_eq_iff.2 h]

@[simp] theorem pullback_firstChern (L : FinLB X) (f : Y ⟶ X) : picSymPull f L.c1 = (L.pull f).c1 := by
  simp [c1_eq, picSymPull_c1Pic]

theorem existsUnique_lift [CompactSpace X] {A : Type} [CommRing A] [Algebra ℚ A] (φ : FinLB X → A)
    (hiso : ∀ L M : FinLB X, LBIso L.lb M.lb → φ L = φ M) (hadd : ∀ L M, φ (L.tens M) = φ L + φ M) :
    ∃! ψ : PicSym X →ₐ[ℚ] A, ∀ L : FinLB X, ψ L.c1 = φ L := by
  choose σ hσ using cls_surjective (X := X)
  have h (L : FinLB X) : φ (σ L.cls) = φ L := hiso _ _ (cls_eq_iff.1 (hσ _))
  let f : Pic X →+ A := AddMonoidHom.mk' (fun c => φ (σ c)) fun a b => by
    rw [← hadd, ← h ((σ a).tens (σ b)), cls_tens, hσ, hσ]
  refine ⟨symLift (f.comp (smallPicEquiv X).toAddMonoidHom), fun L => ?_, fun ψ hψ => ?_⟩
  · refine (symLift_symOf _ _).trans ?_
    change φ (σ (smallPicEquiv X (smallCls _ _))) = _
    rw [smallPicEquiv_smallCls]
    exact h L
  · refine AlgHom.toLinearMap_injective (picSym_linearMap_ext fun n g => ?_)
    simp only [AlgHom.toLinearMap_apply, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    refine Eq.trans ?_ (symLift_symOf _ _).symm
    change _ = φ (σ (smallPicEquiv X ((smallPicEquiv X).symm (g i))))
    rw [AddEquiv.apply_symm_apply, ← hψ, c1_eq, hσ]

theorem aeval_firstChern_surjective [CompactSpace X] :
    Function.Surjective (MvPolynomial.aeval (R := ℚ) (c1 (X := X))) := fun x => by
  have hx : x ∈ _ := (span_prod_symOf (G := SmallPic X)).ge Submodule.mem_top
  refine (Submodule.span_le (p := (MvPolynomial.aeval (R := ℚ) (c1 (X := X))).range.toSubmodule)).2 ?_ hx
  rintro _ ⟨s, rfl⟩
  refine Subalgebra.multiset_prod_mem _ fun y hy => ?_
  obtain ⟨c, -, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨L, hL⟩ := cls_surjective (smallPicEquiv X c)
  exact ⟨MvPolynomial.X L, by simp [c1_eq, hL, firstChernPic]⟩

end FinLB

theorem exists_mul_of_opens {X : Scheme.{0}} (U : X.Opens) {G V : X.Opens} {W₀ T : U.toScheme.Opens} (hT : T ≤ W₀)
    (hW : W₀ ≤ U.ι ⁻¹ᵁ V) (e : T ≤ U.ι ⁻¹ᵁ (G ⊓ V)) (hG : U.ι ⁻¹ᵁ G ⊓ W₀ ≤ T) {a c : Γ(X, G ⊓ V)}
    {b : Γ(U.toScheme, W₀)} (h : (U.ι.appLE _ _ e).hom a = resG _ hT b * (U.ι.appLE _ _ e).hom c) {x : U.toScheme}
    (hx : x ∈ W₀) : ∃ (W : X.Opens) (hW : W ≤ V) (b' : Γ(X, W)), U.ι x ∈ W ∧
      resG X (inf_le_inf_left G hW) a = resG X inf_le_right b' * resG X (inf_le_inf_left G hW) c := by
  have h₁ : U.ι ''ᵁ W₀ ≤ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact hW hy
  have h₂ : U.ι ''ᵁ T ≤ G ⊓ V := by
    rintro _ ⟨y, hy, rfl⟩
    exact e hy
  have h₃ : G ⊓ U.ι ''ᵁ W₀ ≤ U.ι ''ᵁ T := by
    rintro _ ⟨hg, y, hy, rfl⟩
    exact ⟨y, hG ⟨hg, hy⟩, rfl⟩
  refine ⟨_, h₁, b, ⟨x, hx, rfl⟩, ?_⟩
  rw [Scheme.Opens.ι_appLE] at h
  have h₄ : resG X h₂ a = resG X (U.ι.image_mono hT) b * resG X h₂ c := h
  simpa only [map_mul, resG_resG] using congrArg (resG X h₃) h₄

structure NModel (O : Type) [CommRing O] where

  X : Scheme.{0}

  str : X ⟶ Sp O

  [normal : GlobalTheory.IsNormalScheme X]

  isProjOver : IsProjOver str

  [flat : Flat str]

attribute [instance] NModel.normal NModel.flat

namespace NModel

section Local

variable {O : Type} [CommRing O] (Z : NModel O)

instance compactSpace : CompactSpace Z.X := by
  have := (isProper_and_exists_isAmpleLB_of_isProjOver Z.isProjOver).1
  exact QuasiCompact.compactSpace_of_compactSpace Z.str

def const : O →+* Γ(Z.X, ⊤) := Z.str.appTop.hom.comp (Scheme.ΓSpecIso (.of O)).inv.hom

variable [IsLocalRing O]

def gen : Z.X.Opens :=
  Z.str ⁻¹ᵁ ⟨{closedPoint O}ᶜ, (IsLocalRing.isClosed_singleton_closedPoint O).isOpen_compl⟩

structure VPair where

  M : LB Z.X

  isLB : M.IsLB

  t : Γ(toMod M, Z.gen)

  isUnit : ∀ i, IsUnit (coord t i)

namespace VPair

variable {Z} (P P' P'' : VPair Z)

def eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : Γ(Z.X, W) := resG Z.X h (coord P.t i)

theorem isUnit_eqn (i : P.M.ι) {W : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) : IsUnit (P.eqn i h) :=
  (P.isUnit i).map _

@[simp] theorem resG_eqn (i : P.M.ι) {W W' : Z.X.Opens} (h : W ≤ Z.gen ⊓ P.M.U i) (h' : W' ≤ W) :
    resG Z.X h' (P.eqn i h) = P.eqn i (h'.trans h) := resG_resG _ _ _

theorem eqn_rel (i j : P.M.ι) {W : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hij : W ≤ P.M.U i ⊓ P.M.U j) :
    P.eqn i hi = resG Z.X hij (P.M.g i j : Γ(Z.X, P.M.U i ⊓ P.M.U j)) * P.eqn j hj :=
  LB.coord_rel P.t i j hi hj hij

theorem eqn_mul_rel (i j : P.M.ι) (i' j' : P'.M.ι) {W V : Z.X.Opens} (hi : W ≤ Z.gen ⊓ P.M.U i)
    (hj : W ≤ Z.gen ⊓ P.M.U j) (hi' : W ≤ Z.gen ⊓ P'.M.U i') (hj' : W ≤ Z.gen ⊓ P'.M.U j')
    (h : W ≤ V) (hij : V ≤ P.M.U i ⊓ P.M.U j) (hij' : V ≤ P'.M.U i' ⊓ P'.M.U j') :
    P.eqn i hi * P'.eqn i' hi' =
      resG Z.X h (res hij (P.M.g i j) * res hij' (P'.M.g i' j')).val * (P.eqn j hj * P'.eqn j' hj') := by
  rw [P.eqn_rel i j hi hj (h.trans hij), P'.eqn_rel i' j' hi' hj' (h.trans hij'), mul_mul_mul_comm,
    Units.val_mul, map_mul, val_res, val_res, resG_resG, resG_resG]

def ofUnits (M : LB Z.X) (hM : M.IsLB) (u : ∀ i, Γ(Z.X, Z.gen ⊓ M.U i))
    (hu : ∀ i, IsUnit (u i)) (h : u ∈ secOn M Z.gen) : VPair Z :=
  ⟨M, hM, LB.mkSec u h, hu⟩

variable (Z) in

def zero : VPair Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => 1) (fun _ => isUnit_one) fun _ _ => by
    change _ = resG Z.X _ 1 * _
    simp only [map_one, mul_one]

def add : VPair Z :=
  ofUnits (tens P.M P'.M) (isLB_tens P.isLB P'.isLB)
    (fun p => P.eqn p.1 (inf_le_inf_left _ inf_le_left) * P'.eqn p.2 (inf_le_inf_left _ inf_le_right))
    (fun _ => (P.isUnit_eqn _ _).mul (P'.isUnit_eqn _ _)) fun p q => by
      simp only [map_mul, resG_eqn]
      exact eqn_mul_rel P P' p.1 q.1 p.2 q.2 _ _ _ _ _ _ _

def neg : VPair Z :=
  ofUnits (dual P.M) (isLB_dual P.isLB) (fun i => ((P.isUnit i).unit⁻¹).val)
    (fun _ => Units.isUnit _) fun i j => by
      have : res (inf_le_left : Z.gen ⊓ P.M.U i ⊓ P.M.U j ≤ _) (P.isUnit i).unit =
          res (inf_le_inf_right _ inf_le_right) (P.M.g i j) *
            res (inf_le_inf_right _ inf_le_left) (P.isUnit j).unit :=
        Units.ext (LB.coord_mem P.t i j)
      have := congrArg (fun u => Units.val u⁻¹) this
      simp only [mul_inv, ← map_inv] at this
      exact this

def ofCharts {n : ℕ} (f : Fin n → P.M.ι) (hf : ⨆ i, P.M.U (f i) = ⊤) : VPair Z :=
  ofUnits (FinLB.ofCharts P.M P.isLB f hf).lb (FinLB.isLB _) (fun i => coord P.t (f i)) (fun _ => P.isUnit _)
    fun i j => LB.coord_mem P.t (f i) (f j)

def IsIsom : Prop := ∃ w : LB.Iso P.M P'.M, w.IsGen ∧ ∀ (p : P'.M.ι) (q : P.M.ι),
  P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
    resG Z.X inf_le_right (Twist.isoUnit w p q : Γ(Z.X, P'.M.U p ⊓ P.M.U q)) *
      P.eqn q (inf_le_inf_left _ inf_le_right)

def IsSum : Prop := ∀ (i : P.M.ι) (j : P'.M.ι) (k : P''.M.ι),
  ∃ u : Γ(Z.X, P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k)ˣ,
    P''.eqn k (inf_le_inf_left _ inf_le_right : Z.gen ⊓ (P.M.U i ⊓ P'.M.U j ⊓ P''.M.U k) ≤ _) =
      resG Z.X inf_le_right u * (P.eqn i (inf_le_inf_left _ (inf_le_left.trans inf_le_left)) *
        P'.eqn j (inf_le_inf_left _ (inf_le_left.trans inf_le_right)))

theorem isSum_add : IsSum P P' (P.add P') := fun i j k =>
  ⟨res (le_inf (inf_le_right.trans inf_le_left)
    (inf_le_left.trans inf_le_left)) (P.M.g k.1 i) * res (le_inf (inf_le_right.trans inf_le_right)
    (inf_le_left.trans inf_le_right)) (P'.M.g k.2 j), by
      refine Eq.trans ?_ (eqn_mul_rel P P' k.1 i k.2 j (inf_le_inf_left _
        (inf_le_right.trans inf_le_left)) _ (inf_le_inf_left _ (inf_le_right.trans inf_le_right))
        _ _ _ _)
      exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (resG_eqn _ _ _ _) (resG_eqn _ _ _ _))⟩

theorem isSum_neg : IsSum P P.neg (zero Z) := by
  refine fun i j k =>
    ⟨res (le_inf (inf_le_left.trans inf_le_right) (inf_le_left.trans inf_le_left)) (P.M.g j i), ?_⟩
  rw [val_res, resG_resG, ← mul_assoc]
  refine Eq.trans ?_ (congrArg (· * _) (P.eqn_rel j i
    (inf_le_inf_left _ (inf_le_left.trans inf_le_right)) _ _))
  change resG Z.X _ 1 = resG Z.X _ (coord P.t j) * resG Z.X _ ((P.isUnit j).unit⁻¹).val
  rw [← map_mul, IsUnit.mul_val_inv, map_one, map_one]

theorem IsIsom.refl : IsIsom P P := ⟨idIso P.M, idIso_isGen P.isLB, fun p q => P.eqn_rel p q _ _ _⟩

variable {P P'} in

theorem IsIsom.isSum (H : IsIsom P P') : IsSum P (zero Z) P' := fun i _ k => by
  obtain ⟨w, -, hw⟩ := H
  refine ⟨res (le_inf inf_le_right (inf_le_left.trans inf_le_left)) (Twist.isoUnit w k i), ?_⟩
  have := congrArg (resG Z.X (inf_le_inf_left _ (le_inf inf_le_right
    (inf_le_left.trans inf_le_left)) : Z.gen ⊓ (P.M.U i ⊓ ⊤ ⊓ P'.M.U k) ≤ _)) (hw k i)
  simp only [map_mul, resG_eqn, resG_resG] at this
  refine this.trans (congrArg₂ (· * ·) (resG_resG _ _ _).symm ?_)
  exact (mul_one _).symm.trans (congrArg _ (map_one _).symm)

theorem isSum_ofCharts {n : ℕ} (f : Fin n → P.M.ι) (hf : ⨆ i, P.M.U (f i) = ⊤) :
    IsSum P (zero Z) (P.ofCharts f hf) := fun i _ k =>
  ⟨res (le_inf inf_le_right (inf_le_left.trans inf_le_left)) (P.M.g (f k) i), by
    rw [val_res, resG_resG]
    exact (P.eqn_rel (f k) i _ _ _).trans (congrArg _ ((mul_one _).symm.trans (congrArg _ (map_one _).symm)))⟩

end VPair

end Local

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (Z : NModel O)

instance isNoetherian : AlgebraicGeometry.IsNoetherian Z.X := isNoetherian_of_isProjOver Z.isProjOver

def ofModel (B : Model O) [GlobalTheory.IsNormalScheme B.X] : NModel O := ⟨B.X, B.str, B.isProjOver⟩

def Comp : Type := irreducibleComponents Z.X

variable {Z} in

abbrev Comp.opens (C : Z.Comp) : Z.X.Opens := IsNormalScheme.component C

def comp (C : Z.Comp) : Model O where
  X := C.opens.toScheme
  str := C.opens.ι ≫ Z.str
  isProjOver := ProjSpace.isProjOver_comp_of_isClosedImmersion _ Z.isProjOver

def compι (C : Z.Comp) : (Z.comp C).X ⟶ Z.X := C.opens.ι

theorem compι_str (C : Z.Comp) : Z.compι C ≫ Z.str = (Z.comp C).str := rfl

instance : Fintype Z.Comp := @Fintype.ofFinite _ (IsNormalScheme.finite_irreducibleComponents Z.X)

theorem exists_comp (x : Z.X) : ∃ C : Z.Comp, x ∈ C.opens :=
  ⟨⟨_, irreducibleComponent_mem_irreducibleComponents x⟩, mem_irreducibleComponent⟩

variable {Z} in

theorem mem_basicOpen_const {x : Z.X} {g : O} : x ∈ Z.X.basicOpen (Z.const g) ↔ g ∉ (Z.str x).asIdeal := by
  change x ∈ Z.X.basicOpen (Z.str.appTop ((Scheme.ΓSpecIso (.of O)).inv g)) ↔ _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]
  rfl

variable {Z} in

theorem mem_gen_iff_eq_bot {x : Z.X} : x ∈ Z.gen ↔ (Z.str x).asIdeal = ⊥ := by
  refine ⟨fun h => by_contra fun h' => h (PrimeSpectrum.ext
    (eq_maximalIdeal ((Z.str x).isPrime.isMaximal h'))), fun h h' => ?_⟩
  exact IsDiscreteValuationRing.not_a_field O ((congrArg PrimeSpectrum.asIdeal h').symm.trans h)

theorem gen_le_basicOpen {g : O} (hg : g ≠ 0) : Z.gen ≤ Z.X.basicOpen (Z.const g) :=
  fun _ hx => mem_basicOpen_const.2 (by rwa [mem_gen_iff_eq_bot.1 hx])

theorem gen_eq_basicOpen {g : O} (hg : g ≠ 0) (hm : g ∈ maximalIdeal O) : Z.gen = Z.X.basicOpen (Z.const g) :=
  (Z.gen_le_basicOpen hg).antisymm fun _ hx h => mem_basicOpen_const.1 hx (h ▸ hm)

theorem isUnit_const {g : O} (hg : g ≠ 0) {V : Z.X.Opens} (h : V ≤ Z.gen) :
    IsUnit (resG Z.X (le_top : V ≤ ⊤) (Z.const g)) := by
  rw [← resG_resG (Z.X.basicOpen_le (Z.const g)) (h.trans (Z.gen_le_basicOpen hg))]
  exact (Z.X.toRingedSpace.isUnit_res_basicOpen _).map _

theorem exists_specializes (x : Z.X) : ∃ y ∈ Z.gen, y ⤳ x :=
  have ⟨C, hC⟩ := Z.exists_comp x
  ⟨Z.compι C (genericPoint _), (Z.comp C).genericPoint_mem_gen,
    (genericPoint_specializes (show (Z.comp C).X from ⟨x, hC⟩)).map (Z.compι C).continuous⟩

theorem resG_injective {V W : Z.X.Opens} (h : W ≤ V) (hW : Z.gen ⊓ V ≤ W) : Function.Injective (resG Z.X h) := by
  refine (injective_iff_map_eq_zero _).2 fun a ha => eq_zero_of_basicOpen_eq_bot a (eq_bot_iff.2 fun x hx => ?_)
  obtain ⟨y, hy, hyx⟩ := Z.exists_specializes x
  have hy' : y ∈ Z.X.basicOpen a := hyx.mem_open (Z.X.basicOpen a).isOpen hx
  have : y ∈ Z.X.basicOpen (resG Z.X h a) :=
    (Z.X.basicOpen_res a (homOfLE h).op).ge ⟨hW ⟨hy, Z.X.basicOpen_le a hy'⟩, hy'⟩
  simp [ha] at this

theorem exists_extension {V : Z.X.Opens} (a : Γ(Z.X, Z.gen ⊓ V))
    (h : ∀ x ∈ V, ∃ (W : Z.X.Opens) (hW : W ≤ V) (b : Γ(Z.X, W)), x ∈ W ∧
      resG Z.X inf_le_right b = resG Z.X (inf_le_inf_left Z.gen hW) a) :
    ∃ b : Γ(Z.X, V), resG Z.X inf_le_right b = a := by
  choose W hW b hx hb using h
  obtain ⟨c, hc, -⟩ := Z.X.sheaf.existsUnique_gluing' (fun x : V => W x.1 x.2) V (fun x => homOfLE (hW x.1 x.2))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'⟩, hx x hx'⟩) (fun x => b x.1 x.2) fun x y =>
      Z.resG_injective inf_le_right le_rfl <| by
        have h₁ := congrArg (resG Z.X (inf_le_inf_left Z.gen (inf_le_left : W x.1 x.2 ⊓ W y.1 y.2 ≤ _))) (hb x.1 x.2)
        have h₂ := congrArg (resG Z.X (inf_le_inf_left Z.gen (inf_le_right : W x.1 x.2 ⊓ W y.1 y.2 ≤ _))) (hb y.1 y.2)
        simp only [resG_resG] at h₁ h₂
        exact (resG_resG _ _ _).trans (h₁.trans (h₂.symm.trans (resG_resG _ _ _).symm))
  refine ⟨c, Z.X.sheaf.eq_of_locally_eq' (fun x : V => Z.gen ⊓ W x.1 x.2) _
    (fun x => homOfLE (inf_le_inf_left _ (hW x.1 x.2)))
    (fun x hx' => Opens.mem_iSup.2 ⟨⟨x, hx'.2⟩, hx'.1, hx x hx'.2⟩) _ _ fun x => ?_⟩
  refine Eq.trans ?_ (hb x.1 x.2)
  rw [← hc x]
  exact (resG_resG _ _ _).trans (resG_resG _ _ _).symm

section Over

variable {Z} {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str)
include hf

theorem preimage_gen : f ⁻¹ᵁ Z.gen = B.gen := by
  rw [gen, ← Scheme.Hom.comp_preimage, hf]; rfl

theorem appTop_const (g : O) : f.appTop (Z.const g) = B.const g := by
  rw [Model.const, Model.const_eq, ← hf, Scheme.Hom.comp_appTop]; rfl

end Over

namespace VPair

variable {Z} {P P' P'' : VPair Z}

variable (Z) in

def const (g : O) (hg : g ≠ 0) : VPair Z :=
  ofUnits (LB.triv _) (LB.isLB_triv _) (fun _ => resG Z.X le_top (Z.const g))
    (fun _ => Z.isUnit_const hg inf_le_left) fun _ _ => by
      change _ = resG Z.X _ 1 * _
      simp only [map_one, one_mul, resG_resG]

section Pull

variable {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str)

variable (P) in

def pull : VertDiv B where
  M := P.M.pull f
  isLB := Semi.LB.isLB_pull P.isLB f
  t := Twist.resM _ (preimage_gen hf).ge (LB.pullSec P.M f _ P.t)
  isUnit j := ((P.isUnit (j ⟨⟩)).map (f.appLE _ _ (LB.pull_inf_le f _ j)).hom).map _

variable (P) in

theorem eqn_pull (j : (P.pull hf).M.ι) {W : B.X.Opens} (h : W ≤ B.gen ⊓ (P.pull hf).M.U j) {V : Z.X.Opens}
    (hV : V ≤ Z.gen ⊓ P.M.U (j ⟨⟩)) (e : W ≤ f ⁻¹ᵁ V) :
    (P.pull hf).eqn j h = (f.appLE V W e).hom (P.eqn (j ⟨⟩) hV) := by
  rw [eqn, LB.appLE_resG]
  exact (resG_resG _ _ _).trans (LB.resG_appLE f (LB.pull_inf_le f _ j) _ _)

theorem IsSum.pull (H : IsSum P P' P'') : VertDiv.IsSum (P.pull hf) (P'.pull hf) (P''.pull hf) := fun i j k => by
  obtain ⟨u, hu⟩ := H (i ⟨⟩) (j ⟨⟩) (k ⟨⟩)
  have e : (P.pull hf).M.U i ⊓ (P'.pull hf).M.U j ⊓ (P''.pull hf).M.U k ≤
      f ⁻¹ᵁ (P.M.U (i ⟨⟩) ⊓ P'.M.U (j ⟨⟩) ⊓ P''.M.U (k ⟨⟩)) :=
    inf_le_inf (inf_le_inf (LB.pull_U_le f i) (LB.pull_U_le f j)) (LB.pull_U_le f k)
  have e' : B.gen ⊓ ((P.pull hf).M.U i ⊓ (P'.pull hf).M.U j ⊓ (P''.pull hf).M.U k) ≤
      f ⁻¹ᵁ (Z.gen ⊓ (P.M.U (i ⟨⟩) ⊓ P'.M.U (j ⟨⟩) ⊓ P''.M.U (k ⟨⟩))) := inf_le_inf (preimage_gen hf).ge e
  refine ⟨Units.map (f.appLE _ _ e).hom.toMonoidHom u, ?_⟩
  rw [eqn_pull _ hf k _ (inf_le_inf_left _ inf_le_right) e',
    eqn_pull _ hf i _ (inf_le_inf_left _ (inf_le_left.trans inf_le_left)) e',
    eqn_pull _ hf j _ (inf_le_inf_left _ (inf_le_left.trans inf_le_right)) e', hu, map_mul, map_mul, LB.appLE_resG]
  exact congrArg (· * _) (LB.resG_appLE f e _ _).symm

@[simp] theorem cls_pull_zero : ((zero Z).pull hf).cls = 0 := by
  simpa using ((IsIsom.refl (zero Z)).isSum.pull hf).cls_eq

@[simp] theorem cls_pull_const (g : O) (hg : g ≠ 0) : ((const Z g hg).pull hf).cls = B.div g hg := by
  rw [← VertDiv.cls_const, ← add_zero (VertDiv.const B g hg).cls, ← VertDiv.cls_zero B]
  refine VertDiv.IsSum.cls_eq fun i j k => ⟨1, ?_⟩
  rw [eqn_pull _ hf k _ le_rfl (inf_le_inf (preimage_gen hf).ge (inf_le_right.trans (LB.pull_U_le f k)))]
  change (f.appLE _ _ _).hom (resG _ _ (resG _ _ _)) = resG _ _ 1 * (resG _ _ (resG _ _ _) * resG _ _ 1)
  rw [map_one, map_one, one_mul, mul_one, resG_resG, resG_resG, LB.appLE_resG, ← appTop_const hf]
  rfl

end Pull

theorem isIsom_of_units (u : ∀ (p : P'.M.ι) (q : P.M.ι), Γ(Z.X, P'.M.U p ⊓ P.M.U q)ˣ)
    (hu : ∀ p q, P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
      resG Z.X inf_le_right (u p q).val * P.eqn q (inf_le_inf_left _ inf_le_right)) : IsIsom P P' := by
  refine ⟨⟨fun p => u p.1 p.2⟩, fun p q => ?_, hu⟩
  change res _ (u p.1 p.2) = res _ _ * (res _ _)⁻¹ * res _ (u q.1 q.2)
  rw [mul_right_comm, eq_mul_inv_iff_mul_eq]
  refine Units.ext (Z.resG_injective inf_le_right le_rfl ?_)
  have hp := congrArg (resG Z.X (inf_le_inf_left _ inf_le_left :
    Z.gen ⊓ (P'.M.U p.1 ⊓ P.M.U p.2 ⊓ (P'.M.U q.1 ⊓ P.M.U q.2)) ≤ _)) (hu p.1 p.2)
  have hq := congrArg (resG Z.X (inf_le_inf_left _ inf_le_right :
    Z.gen ⊓ (P'.M.U p.1 ⊓ P.M.U p.2 ⊓ (P'.M.U q.1 ⊓ P.M.U q.2)) ≤ _)) (hu q.1 q.2)
  simp only [map_mul, resG_eqn, resG_resG] at hp hq
  rw [P'.eqn_rel p.1 q.1 _ (inf_le_inf_left _ (inf_le_right.trans inf_le_left))
      (inf_le_right.trans (inf_le_inf inf_le_left inf_le_left)), hq,
    P.eqn_rel p.2 q.2 _ (inf_le_inf_left _ (inf_le_right.trans inf_le_right))
      (inf_le_right.trans (inf_le_inf inf_le_right inf_le_right)), ← mul_assoc, ← mul_assoc] at hp
  simp only [Units.val_mul, map_mul, val_res, resG_resG]
  exact (congrArg _ (resG_resG _ _ _)).trans (((P.isUnit_eqn _ _).mul_right_cancel hp).symm.trans
    (congrArg (· * _) (resG_resG _ _ _).symm))

theorem exists_ratio (h : ∀ C, ((P.pull (Z.compι_str C))).IsIsom (P'.pull (Z.compι_str C))) (p : P'.M.ι) (q : P.M.ι) :
    ∃ b : Γ(Z.X, P'.M.U p ⊓ P.M.U q),
      P'.eqn p (inf_le_inf_left _ inf_le_left : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _) =
        resG Z.X inf_le_right b * P.eqn q (inf_le_inf_left _ inf_le_right) := by
  have hq := P.isUnit_eqn q (inf_le_inf_left _ inf_le_right : Z.gen ⊓ (P'.M.U p ⊓ P.M.U q) ≤ _)
  obtain ⟨b, hb⟩ := Z.exists_extension (P'.eqn p (inf_le_inf_left _ inf_le_left) * (hq.unit⁻¹).val) fun x hx => by
    obtain ⟨C, hC⟩ := Z.exists_comp x
    obtain ⟨w, -, hw⟩ := h C
    have e₀ : (P'.pull (Z.compι_str C)).M.U (fun _ => p) ⊓ (P.pull (Z.compι_str C)).M.U (fun _ => q) ≤
        Z.compι C ⁻¹ᵁ (P'.M.U p ⊓ P.M.U q) := inf_le_inf (LB.pull_U_le _ _) (LB.pull_U_le _ _)
    have e : (Z.comp C).gen ⊓ ((P'.pull (Z.compι_str C)).M.U (fun _ => p) ⊓
        (P.pull (Z.compι_str C)).M.U (fun _ => q)) ≤ Z.compι C ⁻¹ᵁ (Z.gen ⊓ (P'.M.U p ⊓ P.M.U q)) :=
      inf_le_inf (preimage_gen (Z.compι_str C)).ge e₀
    have := (eqn_pull P' (Z.compι_str C) (fun _ => p) _ (inf_le_inf_left _ inf_le_left) e).symm.trans
      ((hw (fun _ => p) (fun _ => q)).trans (congrArg _
        (eqn_pull P (Z.compι_str C) (fun _ => q) _ (inf_le_inf_left _ inf_le_right) e)))
    obtain ⟨W, hW, b, hxW, hb⟩ := exists_mul_of_opens C.opens inf_le_right e₀ e
      (inf_le_inf_right _ (preimage_gen (Z.compι_str C)).le) this (x := ⟨x, hC⟩) ⟨mem_pull.2 hx.1, mem_pull.2 hx.2⟩
    exact ⟨W, hW, b, hxW, by rw [map_mul, hb, mul_assoc, ← map_mul, IsUnit.mul_val_inv, map_one, mul_one]⟩
  exact ⟨b, by rw [hb, mul_assoc, IsUnit.val_inv_mul, mul_one]⟩

theorem isIsom_of_comp (h : ∀ C, (P.pull (Z.compι_str C)).cls = (P'.pull (Z.compι_str C)).cls) : IsIsom P P' := by
  choose b hb using exists_ratio fun C => VertDiv.cls_eq_iff.1 (h C)
  choose b' hb' using exists_ratio fun C => VertDiv.cls_eq_iff.1 (h C).symm
  refine isIsom_of_units (fun p q => Units.mkOfMulEqOne (b p q) (resG Z.X (inf_comm _ _).le (b' q p))
    (Z.resG_injective inf_le_right le_rfl ?_)) hb
  have h₁ := congrArg (resG Z.X (inf_le_inf_left Z.gen (inf_comm (P'.M.U p) (P.M.U q)).le)) (hb' q p)
  simp only [map_mul, resG_eqn, resG_resG] at h₁
  refine (P'.isUnit_eqn p (inf_le_inf_left _ inf_le_left)).mul_right_cancel ?_
  rw [map_one, one_mul, map_mul, resG_resG, mul_assoc, ← h₁]
  exact (hb p q).symm

variable (P) in

def toProd : SmallPic Z.X × ∀ C, (Z.comp C).VDivZ :=
  (smallCls P.M P.isLB, fun C => (P.pull (Z.compι_str C)).cls)

theorem toProd_eq_iff : P.toProd = P'.toProd ↔ IsIsom P P' :=
  ⟨fun h => isIsom_of_comp (congrFun (congrArg Prod.snd h)), fun h => Prod.ext
    ((smallCls_eq_iff _ _).2 ⟨h.choose, h.choose_spec.1⟩) (funext fun C => by
      simpa [toProd] using (h.isSum.pull (Z.compι_str C)).cls_eq.symm)⟩

variable (P P') in

theorem toProd_add : (P.add P').toProd = P.toProd + P'.toProd :=
  Prod.ext (map_add (smallPicEquiv Z.X).symm (cls _ P.isLB) (cls _ P'.isLB))
    (funext fun C => ((isSum_add P P').pull (Z.compι_str C)).cls_eq)

variable (Z) in

theorem toProd_zero : (zero Z).toProd = 0 :=
  Prod.ext (map_zero (smallPicEquiv Z.X).symm) (funext fun C => cls_pull_zero (Z.compι_str C))

variable (P) in

theorem toProd_neg : P.neg.toProd = -P.toProd :=
  Prod.ext ((congrArg (smallPicEquiv Z.X).symm (cls_dual P.isLB _)).trans (map_neg _ _)) (funext fun C =>
    eq_neg_of_add_eq_zero_right ((P.isSum_neg.pull (Z.compι_str C)).cls_eq.symm.trans (cls_pull_zero _)))

end VPair

def vdivSubgroup : AddSubgroup (SmallPic Z.X × ∀ C, (Z.comp C).VDivZ) where
  carrier := Set.range VPair.toProd
  zero_mem' := ⟨_, VPair.toProd_zero Z⟩
  add_mem' := by
    rintro _ _ ⟨P, rfl⟩ ⟨P', rfl⟩
    exact ⟨_, P.toProd_add P'⟩
  neg_mem' := by
    rintro _ ⟨P, rfl⟩
    exact ⟨_, P.toProd_neg⟩

abbrev VDivZ : Type := Z.vdivSubgroup

namespace VPair

variable {Z} {P P' P'' : VPair Z}

variable (P) in

def cls : Z.VDivZ := ⟨P.toProd, P, rfl⟩

theorem cls_surjective : Function.Surjective (cls (Z := Z)) := fun ⟨_, P, h⟩ => ⟨P, Subtype.ext h⟩

theorem cls_eq_iff : P.cls = P'.cls ↔ IsIsom P P' := Subtype.ext_iff.trans toProd_eq_iff

variable (P P') in

@[simp] theorem cls_add : (P.add P').cls = P.cls + P'.cls := Subtype.ext (P.toProd_add P')

variable (Z) in

@[simp] theorem cls_zero : (zero Z).cls = 0 := Subtype.ext (toProd_zero Z)

variable (P) in

@[simp] theorem cls_neg : P.neg.cls = -P.cls := Subtype.ext P.toProd_neg

theorem isSum_iff : IsSum P P' P'' ↔ P''.cls = P.cls + P'.cls := by
  rw [← cls_add]
  refine ⟨fun h => cls_eq_iff.2 (isIsom_of_comp fun C =>
    (h.pull _).cls_eq.trans ((isSum_add P P').pull _).cls_eq.symm), fun h i j k => ?_⟩
  obtain ⟨w, -, hw⟩ := cls_eq_iff.1 h.symm
  refine ⟨res (inf_comm _ _).le (Twist.isoUnit w k (i, j)), ?_⟩
  have := congrArg (resG Z.X (inf_le_inf_left Z.gen (inf_comm (P.M.U i ⊓ P'.M.U j) (P''.M.U k)).le)) (hw k (i, j))
  rw [map_mul, resG_eqn, resG_eqn] at this
  refine this.trans (congrArg₂ (· * ·) ((resG_resG _ _ _).trans (resG_resG _ _ _).symm) ?_)
  exact (map_mul _ _ _).trans (congrArg₂ (· * ·) (resG_eqn _ _ _ _) (resG_eqn _ _ _ _))

theorem exists_finLB (D : Z.VDivZ) : ∃ (M : FinLB Z.X) (t : Γ(toMod M.lb, Z.gen)) (h : ∀ i, IsUnit (coord t i)),
    cls ⟨M.lb, M.isLB, t, h⟩ = D := by
  obtain ⟨P, rfl⟩ := cls_surjective D
  obtain ⟨n, f, hf⟩ := FinLB.exists_charts P.isLB
  exact ⟨FinLB.ofCharts P.M P.isLB f hf, _, (P.ofCharts f hf).isUnit,
    (isSum_iff.1 (P.isSum_ofCharts f hf)).trans (by simp)⟩

end VPair

section Lift

variable {Z} {A : Type*} [AddCommGroup A] (φ : VPair Z → A)
  (h : ∀ P P' P'' : VPair Z, P.IsSum P' P'' → φ P'' = φ P + φ P')

def vLift : Z.VDivZ →+ A :=
  AddMonoidHom.mk' (fun D => φ (VPair.cls_surjective D).choose) fun D D' => h _ _ _ (VPair.isSum_iff.2 (by
    simp only [(VPair.cls_surjective _).choose_spec]))

@[simp] theorem vLift_cls (P : VPair Z) : vLift φ h P.cls = φ P := by
  have h₀ : φ (.zero Z) = 0 := by simpa using h _ _ _ (VPair.IsIsom.refl (.zero Z)).isSum
  exact (h P _ _ (VPair.cls_eq_iff.1 (VPair.cls_surjective P.cls).choose_spec.symm).isSum).trans (by simp [h₀])

end Lift

def vCls : Z.VDivZ →+ Pic Z.X :=
  (smallPicEquiv Z.X).toAddMonoidHom.comp ((AddMonoidHom.fst _ _).comp Z.vdivSubgroup.subtype)

def vRes (C : Z.Comp) : Z.VDivZ →+ (Z.comp C).VDivZ :=
  (Pi.evalAddMonoidHom _ C).comp ((AddMonoidHom.snd _ _).comp Z.vdivSubgroup.subtype)

def div (g : O) (hg : g ≠ 0) : Z.VDivZ := (VPair.const Z g hg).cls

variable {Z}

@[simp] theorem vCls_cls (P : VPair Z) : Z.vCls P.cls = cls P.M P.isLB := smallPicEquiv_smallCls _ _

theorem vRes_cls (P : VPair Z) (C : Z.Comp) : Z.vRes C P.cls = (P.pull (Z.compι_str C)).cls := rfl

theorem vDivZ_ext {D D' : Z.VDivZ} (h : ∀ C, Z.vRes C D = Z.vRes C D') : D = D' := by
  obtain ⟨P, rfl⟩ := VPair.cls_surjective D
  obtain ⟨P', rfl⟩ := VPair.cls_surjective D'
  exact VPair.cls_eq_iff.2 (VPair.isIsom_of_comp fun C => by simpa only [vRes_cls] using h C)

theorem vCls_vRes (D : Z.VDivZ) (C : Z.Comp) : (Z.comp C).vCls (Z.vRes C D) = pull (Z.compι C) (Z.vCls D) := by
  obtain ⟨P, rfl⟩ := VPair.cls_surjective D
  rw [vRes_cls, VertDiv.vCls_cls, vCls_cls]
  rfl

@[simp] theorem vRes_div (g : O) (hg : g ≠ 0) (C : Z.Comp) : Z.vRes C (Z.div g hg) = (Z.comp C).div g hg :=
  (vRes_cls _ C).trans (VPair.cls_pull_const (Z.compι_str C) g hg)

@[simp] theorem vCls_div (g : O) (hg : g ≠ 0) : Z.vCls (Z.div g hg) = 0 := vCls_cls _

theorem div_eq_addVal_smul {ϖ g : O} (hϖ : Irreducible ϖ) (hg : g ≠ 0) :
    Z.div g hg = (IsDiscreteValuationRing.addVal O g).toNat • Z.div ϖ hϖ.ne_zero :=
  vDivZ_ext fun C => by rw [map_nsmul, vRes_div, vRes_div, Model.div_eq_addVal_smul _ hϖ]

def vPull {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str) : Z.VDivZ →+ B.VDivZ :=
  vLift (fun P => (P.pull hf).cls) fun _ _ _ h => (h.pull hf).cls_eq

@[simp] theorem vPull_cls {B : Model O} {f : B.X ⟶ Z.X} (hf : f ≫ Z.str = B.str) (P : VPair Z) :
    vPull hf P.cls = (P.pull hf).cls := vLift_cls _ _ P

theorem picSymPull_mem_symDeg {X Y : Scheme.{0}} (f : Y ⟶ X) {n : ℕ} {x : PicSym X} (hx : x ∈ symDeg (SmallPic X) n) :
    picSymPull f x ∈ symDeg (SmallPic Y) n := by
  refine (Submodule.span_le (p := (symDeg (SmallPic Y) n).comap (picSymPull f).toLinearMap)).2 ?_ hx
  rintro _ ⟨g, rfl⟩
  exact Submodule.subset_span ⟨fun i => smallPull f (g i), by simp [picSymPull]⟩

variable (Z) in

def vDeg (d : ℕ) : Z.VDivZ →+ (PicSym Z.X →ₗ[ℚ] ℚ) :=
  ∑ C ∈ Finset.univ.filter fun C : Z.Comp => (Z.comp C).relDim = d,
    (LinearMap.lcomp ℚ ℚ (picSymPull (Z.compι C)).toLinearMap).toAddMonoidHom.comp ((Z.comp C).vDeg.comp (Z.vRes C))

theorem vDeg_apply (d : ℕ) (D : Z.VDivZ) (x : PicSym Z.X) : Z.vDeg d D x =
    ∑ C ∈ Finset.univ.filter fun C : Z.Comp => (Z.comp C).relDim = d,
      (Z.comp C).vDeg (Z.vRes C D) (picSymPull (Z.compι C) x) := by
  rw [vDeg, AddMonoidHom.finset_sum_apply, LinearMap.sum_apply]
  rfl

theorem vDeg_of_mem {d : ℕ} (D : Z.VDivZ) {x : PicSym Z.X} (hx : x ∈ symDeg (SmallPic Z.X) d) :
    Z.vDeg d D x = ∑ C, (Z.comp C).vDeg (Z.vRes C D) (picSymPull (Z.compι C) x) := by
  rw [vDeg_apply, Finset.sum_filter]
  refine Finset.sum_congr rfl fun C _ => ?_
  split_ifs with h
  · rfl
  · exact (Model.vDeg_eq_zero _ (Ne.symm h) (picSymPull_mem_symDeg _ hx)).symm

theorem vDeg_eq_zero {d n : ℕ} (D : Z.VDivZ) (hn : n ≠ d) {x : PicSym Z.X} (hx : x ∈ symDeg (SmallPic Z.X) n) :
    Z.vDeg d D x = 0 := by
  rw [vDeg_apply]
  exact Finset.sum_eq_zero fun C hC => Model.vDeg_eq_zero _ ((Finset.mem_filter.1 hC).2 ▸ hn)
    (picSymPull_mem_symDeg _ hx)

theorem vDeg_of_relDim {d : ℕ} (h : ∀ C, (Z.comp C).relDim = d) (D : Z.VDivZ) (x : PicSym Z.X) :
    Z.vDeg d D x = ∑ C, (Z.comp C).vDeg (Z.vRes C D) (picSymPull (Z.compι C) x) := by
  rw [vDeg_apply, Finset.filter_true_of_mem fun C _ => h C]

end NModel

end GlobalTheory.ShFam.Pad
