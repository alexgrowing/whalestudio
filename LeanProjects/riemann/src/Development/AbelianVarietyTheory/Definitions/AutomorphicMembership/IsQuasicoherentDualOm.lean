import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FibLatPreSubSpanSubLe
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelLabelExtendsOfOrthogonalToExtended

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace NumberField MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions GlobalTheory.ShFam
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM)
open GlobalTheory.QCoh (IsFiniteQC freeModule freeBasis sectionsHom)
open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.HTSheaf
open GlobalTheory.KernelNoTorsion (torsionLift torsionLift_ι)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HTSheaf

section Groups

variable {S S' : Scheme.{0}}

def torsUnit (G : Over S) [GrpObj G] (N : ℕ) : 𝟙_ (Over S) ⟶ torsion G N := torsionLift 1 (one_pow N)

theorem torsUnit_ι (G : Over S) [GrpObj G] (N : ℕ) : torsUnit G N ≫ torsion.ι G N = η[G] :=
  (torsionLift_ι _ _).trans (MonObj.one_eq_one G).symm

def torsRes (G : Over S) [GrpObj G] (N : ℕ) : omega G ⟶ Conormal.conormal (sec (torsUnit G N)) :=
  cotMap (torsion.ι G N) (torsUnit_ι G N)

structure TruncBT {O : Type} [CommRing O] (c : O →+* O) {G : Over S} [GrpObj G] (act₀ : OAct O G) (p n : ℕ)
    (K : Over S) : Type where
  [grp : GrpObj K]
  [comm : IsCommMonObj K]
  finite : IsFinite K.hom
  flat : Flat K.hom
  lfp : LocallyOfFinitePresentation K.hom
  kill : 𝟙 K ^ p ^ n = 1
  bt : ∀ i ≤ n, ∀ r : K ⟶ torsion K (p ^ i), r ≫ torsion.ι K _ = 𝟙 K ^ p ^ (n - i) → Flat r.left ∧ Surjective r.left

  act : OAct O K

  e : K ⊗ K ⟶ Gm S
  e_mul_left : ∀ (T : Over S) (x x' y : T ⟶ K), lift (x * x') y ≫ e = (lift x y ≫ e) * (lift x' y ≫ e)
  e_mul_right : ∀ (T : Over S) (x y y' : T ⟶ K), lift x (y * y') ≫ e = (lift x y ≫ e) * (lift x y' ≫ e)
  e_self : ∀ (T : Over S) (x : T ⟶ K), lift x x ≫ e = 1
  e_act : ∀ (a : O) (T : Over S) (x y : T ⟶ K), lift (x ≫ act.act a) y ≫ e = lift x (y ≫ act.act (c a)) ≫ e
  perfect : ∀ (T : Over S) (χ : T ⊗ K ⟶ Gm S),
    (∀ (T' : Over S) (t : T' ⟶ T) (y y' : T' ⟶ K), lift t (y * y') ≫ χ = (lift t y ≫ χ) * (lift t y' ≫ χ)) →
      ∃! x : T ⟶ K, χ = x ▷ K ≫ e

  j : torsion G (p ^ n) ⟶ K
  j_one : torsUnit G (p ^ n) ≫ j = η[K]
  j_mul : ∀ (T : Over S) (x y z : T ⟶ torsion G (p ^ n)),
    z ≫ torsion.ι G _ = (x ≫ torsion.ι G _) * (y ≫ torsion.ι G _) → z ≫ j = (x ≫ j) * (y ≫ j)
  j_act : ∀ (a : O) (T : Over S) (x y : T ⟶ torsion G (p ^ n)),
    y ≫ torsion.ι G _ = x ≫ torsion.ι G _ ≫ act₀.act a → y ≫ j = x ≫ j ≫ act.act a

  lie : LocM.modN (omega G) (p ^ n) ≅ omega K
  lie_j : cokernel.π _ ≫ lie.hom ≫ cotMap j j_one = torsRes G (p ^ n)

def IsProd (G : Over S) [GrpObj G] {T : Scheme.{0}} (b : T ⟶ S) (x y z : T ⟶ G.left) : Prop :=
  ∃ x' y' : Over.mk b ⟶ G, x'.left = x ∧ y'.left = y ∧ (x' * y').left = z

namespace TruncBT

variable {O : Type} [CommRing O] {c : O →+* O} {G : Over S} [GrpObj G] {act₀ : OAct O G} {p n : ℕ} {K : Over S}

def Extends [IsCommMonObj G] (B : TruncBT c act₀ p n K) (L : LB G.left) (U : Set S) : Prop :=
  IsOpenImmersion B.j.left ∧
  (∀ T : Over S, Set.range T.hom ⊆ abLocus G → Function.Bijective fun x : T ⟶ torsion G (p ^ n) => x ≫ B.j) ∧
  ∀ (k : Type) [Field k] [IsAlgClosed k] (s : Sp k ⟶ S), Set.range s ⊆ U → ∀ x y : Over.mk s ⟶ torsion G (p ^ n),
    ∃ w : Γ((Over.mk s).left, ⊤)ˣ, Out.WeilIs G L (p ^ n : ℕ) (x ≫ torsion.ι G _) (y ≫ torsion.ι G _) w ∧
      SplitTorus.val (lift (x ≫ B.j) (y ≫ B.j) ≫ B.e) (ULift.up 1) = w

def IsTorsionOf {G' : Over S'} [GrpObj G'] {act₀' : OAct O G'} {n' : ℕ} {K' : Over S'} (B : TruncBT c act₀ p n K)
    (B' : TruncBT c act₀' p n' K') (f : S' ⟶ S) (φ : G'.left ⟶ G.left) : Prop :=
  letI := B.grp
  letI := B'.grp
  ∃ ψ : (torsion K' (p ^ n)).left ⟶ K.left, IsPullback ψ (torsion K' (p ^ n)).hom K.hom f ∧
    (∀ (T : Scheme.{0}) (b : T ⟶ S') (x y z : T ⟶ (torsion K' (p ^ n)).left),
      IsProd K' b (x ≫ (torsion.ι K' _).left) (y ≫ (torsion.ι K' _).left) (z ≫ (torsion.ι K' _).left) →
        IsProd K (b ≫ f) (x ≫ ψ) (y ≫ ψ) (z ≫ ψ)) ∧
    (∀ (a : O) (T : Scheme.{0}) (x y : T ⟶ (torsion K' (p ^ n)).left),
      y ≫ (torsion.ι K' _).left = x ≫ (torsion.ι K' _).left ≫ (B'.act.act a).left → y ≫ ψ = x ≫ ψ ≫ (B.act.act a).left) ∧
    ∀ (T : Scheme.{0}) (u' : T ⟶ (torsion G' (p ^ n')).left) (u : T ⟶ (torsion G (p ^ n)).left)
      (x : T ⟶ (torsion K' (p ^ n)).left), u ≫ (torsion.ι G _).left = u' ≫ (torsion.ι G' _).left ≫ φ →
        x ≫ (torsion.ι K' _).left = u' ≫ B'.j.left → x ≫ ψ = u ≫ B.j.left

end TruncBT

end Groups

end GlobalTheory.HTSheaf

namespace GlobalTheory.LocM.HTm

open EigenSplit (IsSplitting eigenSub baseChangeAction tensorAction)

section Free

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

section Coeff

variable {l : Level H} (c : Coeff l) (W : ValuationSubring ℂ)

def embV (σ : E →+* ℂ) : 𝓞 E →+* c.V W := (embK c σ).codRestrict (c.V W) fun a => by
  obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := c.V W) (K := c.F)).1
    (((Algebra.IsIntegral.isIntegral (R := ℤ) a).map (embK c σ).toIntAlgHom).tower_top)
  exact (show (y : c.F) = embK c σ a from hy) ▸ y.2

theorem coe_embV (σ : E →+* ℂ) (a : 𝓞 E) : (((embV c W σ a : c.V W) : c.F) : ℂ) = σ a := rfl

theorem subtype_comp_embV (σ : E →+* ℂ) : (c.V W).subtype.comp (embV c W σ) = embK c σ := RingHom.ext fun _ => rfl

theorem embV_injective : Function.Injective (embV c W) := fun σ σ' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun a =>
    (coe_embV c W σ a).symm.trans ((congrArg (fun f : 𝓞 E →+* c.V W => ((f a : c.F) : ℂ)) h).trans (coe_embV c W σ' a)))

theorem isSplitting_embK : IsSplitting (embK c) := by
  classical
  obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E ℂ)
  exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field (φ := embF c)
    (fun _ _ h => RingHom.ext fun x => congrArg Subtype.val (RingHom.congr_fun h x)) b)
    (Int.cast_ne_zero.2 (NumberField.discr_ne_zero E)).isUnit

theorem splitMap_embV_injective : Function.Injective (EigenSplit.splitMap (embV c W)) := by
  have e (x : c.V W ⊗[ℤ] 𝓞 E) : EigenSplit.splitMap (embK c) ((c.V W).subtype.toIntAlgHom.toLinearMap.rTensor _ x) =
      fun σ => (EigenSplit.splitMap (embV c W) x σ : c.F) := by
    induction x with
    | zero => simp [Pi.zero_def]
    | add y z hy hz => simp only [map_add, hy, hz]; rfl
    | tmul r a =>
      funext σ
      rw [LinearMap.rTensor_tmul, EigenSplit.splitMap_tmul, EigenSplit.splitMap_tmul]
      rfl
  intro x y h
  refine Module.Flat.rTensor_preserves_injective_linearMap (M := 𝓞 E) (c.V W).subtype.toIntAlgHom.toLinearMap
    Subtype.val_injective ((isSplitting_embK c).1 ?_)
  rw [e, e, h]

end Coeff

variable (Dw : Datum H)

instance finite_La : Module.Finite ℤ Dw.La := (Coisotropic.lattice_rank E H Dw).2.1

instance free_La : Module.Free ℤ Dw.La := (Coisotropic.lattice_rank E H Dw).1

def dimA : ℕ := Module.finrank ℚ E / 2 * (Dw.p + Dw.q)

variable {Dw} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}
  (Z : Mdl Y i₀)

instance quasiSeparated_G : QuasiSeparated Z.t.G.hom := have := Z.t.semi; inferInstance

theorem exists_isFrame_om (x : Z.X) : ∃ (U : Z.X.Opens) (n : ℕ) (s : Fin n → Γ(Z.om, U)), x ∈ U ∧ VB.IsFrame s :=
  have := Z.t.semi.smooth
  exists_isFrame_omega Z.t.G x

instance isQuasicoherent_dual_om : (dual Z.om).IsQuasicoherent :=
  OmegaGlobal.isQuasicoherent_of_frames fun x => have ⟨U, n, _, hx, hs⟩ := exists_isFrame_om Z x; ⟨U, n, _, hx, hs.dual⟩

instance isFiniteQC_om : IsFiniteQC Z.om := .of_forall_exists_affine fun x => by
  obtain ⟨U, n, s, hx, hs⟩ := exists_isFrame_om Z x
  obtain ⟨V, hV, hx', hle⟩ := QCoh.exists_affine_mem_le x hx
  exact ⟨V, hV, hx', .of_basis (hs.basis hle)⟩

def scal : Z.i.c.V W →+* Γ(Z.X, ⊤) := QCoh.structureRingHom (R := .of (Z.i.c.V W)) Z.s

def omAct : 𝓞 E →+* End Z.om := omegaConjAct Z.t.act (H.bar : 𝓞 E →+* 𝓞 E)

abbrev red (n : ℕ) : Z.om ⟶ modN Z.om (p ^ n) := cokernel.π _

def HTOn (n : ℕ) : Type :=
  {h : Dw.La →+ Γ(modN Z.om (p ^ n), ⊤) //
    ∀ (a : 𝓞 E) t, h (a • t) = (modNMap (act (omAct Z) a) (p ^ n)).app ⊤ (h t)}

instance (n : ℕ) : Zero (HTOn Z n) := ⟨0, fun _ _ => (map_zero _).symm⟩

variable {Z} {n : ℕ} (h : HTOn Z n)

def imHT : Sub (modN Z.om (p ^ n)) := spanSub fun i => h.1 (Module.Free.chooseBasis ℤ Dw.La i)

theorem mem_imHT (t : Dw.La) : h.1 t ∈ (imHT h).sec ⊤ := by
  rw [← (Module.Free.chooseBasis ℤ Dw.La).sum_repr t, map_sum]
  refine sum_mem fun i _ => ?_
  rw [map_zsmul]
  have := res_mem_spanSub (fun i => h.1 (Module.Free.chooseBasis ℤ Dw.La i)) i ⊤
  rw [resM_self] at this
  exact zsmul_mem this _

theorem imHT_le {U : Z.X.Opens} (hU : IsAffineOpen U) :
    (imHT h).sec U = Submodule.span _ (Set.range fun t => resM _ le_top (h.1 t)) := by
  refine le_antisymm (fun s hs => ?_) (Submodule.span_le.2 ?_)
  · obtain ⟨a, rfl⟩ := (mem_spanSub_iff _ hU).1 hs
    exact sum_mem fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  · rintro _ ⟨t, rfl⟩
    exact (imHT h).res_mem le_top (mem_imHT h t)

def omP : Sub Z.om := preSub (red Z n) (imHT h)

instance isQuasicoherent_omP : (omP h).toMod.IsQuasicoherent :=
  haveI : (imHT h).toMod.IsQuasicoherent := isQuasicoherent_spanSub _
  isQuasicoherent_preSub _ _

theorem mem_omP_iff {U : Z.X.Opens} {s : Γ(Z.om, U)} : s ∈ (omP h).sec U ↔ (red Z n).app U s ∈ (imHT h).sec U :=
  mem_preSub_iff _ _

theorem pow_smul_mem_omP {U : Z.X.Opens} (s : Γ(Z.om, U)) : p ^ n • s ∈ (omP h).sec U := by
  rw [mem_omP_iff, map_nsmul, nsmul_sec_modN]
  exact zero_mem _

def IsLift (t : Dw.La) {U : Z.X.Opens} (s : Γ((omP h).toMod, U)) : Prop :=
  (red Z n).app U ((omP h).incl.app U s) = resM _ le_top (h.1 t)

theorem exists_isLift (t : Dw.La) {U : Z.X.Opens} (hU : IsAffineOpen U) : ∃ s : Γ((omP h).toMod, U), IsLift h t s :=
  have ⟨s, hs⟩ := QCoh.surjective_cokernel_π_app (p ^ n • 𝟙 Z.om) hU (resM _ le_top (h.1 t))
  ⟨(omP h).mkSec s ((mem_omP_iff h).2 (hs ▸ (imHT h).res_mem le_top (mem_imHT h t))), hs⟩

section Pull

variable (Z) (B : Mdl Y i₀) [IsIso B.π] (e : Z.i = B.i)

def toBase : Z.X ⟶ B.X := Z.π ≫ eqToHom (congrArg (fun i => (Y i).X) e) ≫ inv B.π

theorem isGrpPullback_cast {i i' : Idx H p} (e : i = i') : IsGrpPullback (Y i).t.G (Y i').t.G
    (eqToHom (congrArg (fun i => (Y i).X) e)) (eqToHom (congrArg (fun i => (Y i).t.G.left) e)) ∧
    ∀ a, ((Y i).t.act.act a).left ≫ eqToHom (congrArg (fun i => (Y i).t.G.left) e) =
      eqToHom (congrArg (fun i => (Y i).t.G.left) e) ≫ ((Y i').t.act.act a).left := by
  subst e
  refine ⟨⟨IsPullback.id_horiz _, fun T x y x₀ y₀ hx hy => ?_⟩, fun a => by simp⟩
  have k : ∀ {b b' : T.left ⟶ (Y i).X} (_ : b = b') (x y : Over.mk b ⟶ (Y i).t.G) (x₀ y₀ : Over.mk b' ⟶ (Y i).t.G),
      x₀.left = x.left → y₀.left = y.left → (x₀ * y₀).left = (x * y).left := by
    rintro b _ rfl x y x₀ y₀ hx hy
    rw [Over.OverMorphism.ext hx, Over.OverMorphism.ext hy]
  exact (k (Category.comp_id _).symm x y x₀ y₀ (hx.trans (Category.comp_id _)) (hy.trans (Category.comp_id _))).trans
    (Category.comp_id _).symm

theorem toBase_π : toBase Z B e ≫ B.π = Z.π ≫ eqToHom (congrArg (fun i => (Y i).X) e) := by simp [toBase]

def toBaseG : Z.t.G.left ⟶ B.t.G.left :=
  B.tMap.cart.1.lift (Z.tMap.φ ≫ eqToHom (congrArg (fun i => (Y i).t.G.left) e)) (Z.t.G.hom ≫ toBase Z B e)
    (by rw [Category.assoc _ (toBase Z B e), toBase_π]; exact (Z.tMap.cart.comp (isGrpPullback_cast e).1).1.w)

theorem toBaseG_φ : toBaseG Z B e ≫ B.tMap.φ = Z.tMap.φ ≫ eqToHom (congrArg (fun i => (Y i).t.G.left) e) :=
  B.tMap.cart.1.lift_fst _ _ _

theorem isGrpPullback_toBaseG : IsGrpPullback Z.t.G B.t.G (toBase Z B e) (toBaseG Z B e) :=
  B.tMap.cart.cancel ((Z.tMap.cart.comp (isGrpPullback_cast e).1).congr (toBase_π Z B e).symm (toBaseG_φ Z B e).symm)
    (B.tMap.cart.1.lift_snd _ _ _)

theorem act_toBaseG (a : 𝓞 E) : (Z.t.act.act a).left ≫ toBaseG Z B e = toBaseG Z B e ≫ (B.t.act.act a).left := by
  have h₁ : toBaseG Z B e ≫ B.tMap.cm.F = Z.tMap.cm.F ≫ _ := toBaseG_φ Z B e
  apply B.tMap.cart.1.hom_ext
  · rw [Category.assoc, Category.assoc, B.tMap.act, h₁, reassoc_of% h₁, reassoc_of% Z.tMap.act a,
      (isGrpPullback_cast e).2]
  · rw [Category.assoc, Category.assoc, Over.w, (isGrpPullback_toBaseG Z B e).1.w, Over.w_assoc]

variable {B} in

def pull (h : HTOn B n) : HTOn Z n :=
  ⟨(pbMod (isGrpPullback_toBaseG Z B e) (p ^ n) le_top).comp h.1, fun a t => by
    have := Z.t.act.hom (H.bar a)
    have := B.t.act.hom (H.bar a)
    exact (congrArg _ (h.2 a t)).trans (pbMod_omegaMap _ _ _ (act_toBaseG Z B e (H.bar a)) _ _ _)⟩

end Pull

variable (Z) in

def laAct : 𝓞 E →+* Module.End (Z.i.c.V W) (Z.i.c.V W ⊗[ℤ] Dw.La) :=
  baseChangeAction (Z.i.c.V W) (Module.toModuleEnd ℤ Dw.La)

variable (Z) in

def tSub (σ : E →+* ℂ) : Submodule (Z.i.c.V W) (Z.i.c.V W ⊗[ℤ] Dw.La) := eigenSub (laAct Z) (embV Z.i.c W σ)

end Free

variable {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} {p : ℕ} (ct : At S κ p) (Z : ct.Mdl)

theorem isPrincipalIdealRing_V : IsPrincipalIdealRing (Z.i.c.V ct.W) :=
  have := ModelPresentation.isNoetherianRing_place Z.i.c ct.W ct.hp.ne_zero ct.hW
  inferInstance

theorem exists_eps (σ : D.host.E →+* ℂ) : ∃ ε, ann (embV Z.i.c ct.W σ) = Submodule.span _ {ε} ∧
    EigenSplit.splitMap (embV Z.i.c ct.W) ε σ ≠ 0 :=
  have := isPrincipalIdealRing_V ct Z
  exists_ann_eq_span (embV_injective _ _) (splitMap_embV_injective _ _) σ

def eps (σ : D.host.E →+* ℂ) : Z.i.c.V ct.W ⊗[ℤ] 𝓞 D.host.E := (exists_eps ct Z σ).choose

theorem ann_eq_span_eps (σ : D.host.E →+* ℂ) : ann (embV Z.i.c ct.W σ) = Submodule.span _ {eps ct Z σ} :=
  (exists_eps ct Z σ).choose_spec.1

theorem eps_mem (σ : D.host.E →+* ℂ) : eps ct Z σ ∈ ann (embV Z.i.c ct.W σ) :=
  (ann_eq_span_eps ct Z σ).ge (Submodule.mem_span_singleton_self _)

def dif (σ : D.host.E →+* ℂ) : Z.i.c.V ct.W := EigenSplit.splitMap (embV Z.i.c ct.W) (eps ct Z σ) σ

theorem dif_ne_zero (σ : D.host.E →+* ℂ) : dif ct Z σ ≠ 0 := (exists_eps ct Z σ).choose_spec.2

open Classical in

theorem map_eps (σ : D.host.E →+* ℂ) {R : Type} [CommRing R] (f : Z.i.c.V ct.W →+* R)
    (hf : IsSplitting fun τ => f.comp (embV Z.i.c ct.W τ)) :
    Algebra.TensorProduct.map f.toIntAlgHom (AlgHom.id ℤ _) (eps ct Z σ) = f (dif ct Z σ) • EigenSplit.idem hf σ :=
  map_eq_smul_idem (embV_injective _ _) (eps_mem ct Z σ) f hf

def epsHom (σ : D.host.E →+* ℂ) : Z.om ⟶ Z.om := act (tensAct (scal Z) (omAct Z)) (eps ct Z σ)

variable {Z} {n : ℕ} (h : HTOn Z n) (σ : D.host.E →+* ℂ)

def epsOm : Sub Z.om := imSub ((omP h).incl ≫ epsHom ct Z σ)

def toEps : (omP h).toMod ⟶ (epsOm ct h σ).toMod := toIm _

instance isQuasicoherent_epsOm : (epsOm ct h σ).toMod.IsQuasicoherent := isQuasicoherent_imSub _

instance epi_toEps : Epi (toEps ct h σ) := epi_toIm _

theorem isFiniteQC_omP : IsFiniteQC (omP h).toMod :=
  have := ct.isLocallyNoetherian Z
  .of_mono (omP h).incl

instance isFiniteQC_epsOm : IsFiniteQC (epsOm ct h σ).toMod :=
  have := ct.isLocallyNoetherian Z
  .of_mono (epsOm ct h σ).incl

def wSheaf : Z.X.Modules := dual (epsOm ct h (conjEmb σ)).toMod

instance isFiniteQC_wSheaf : IsFiniteQC (wSheaf ct h σ) :=
  have := ct.isLocallyNoetherian Z
  have : IsFiniteQC (dual (Z.ofMod (epsOm ct h (conjEmb σ)).toMod).toMod) :=
    PtNorm.isFiniteQC_homMod_cokernel (ct.isVB_free Z _ _) (ct.isVB_free Z _ _) _
  .of_iso (dualIso (ct.presIso (epsOm ct h (conjEmb σ)).toMod).symm)

def htIdeal : Z.X.IdealSheafData :=
  minorIdeal (omP h) (dimA S.Dw) * ∏ σ : D.host.E →+* ℂ, minorIdeal (epsOm ct h σ) (S.Dw.mult (conjEmb σ))

open Classical in

def htIdl : ct.Idl Z :=
  if H : ∀ x ∈ (htIdeal ct h).support, x ∉ Z.opn then ⟨htIdeal ct h, H⟩ else ⟨⊤, fun x hx => by
    rw [Scheme.IdealSheafData.support_top] at hx
    exact hx.elim⟩

theorem htIdl_val (H : ∀ x ∈ (htIdeal ct h).support, x ∉ Z.opn) : (htIdl ct h).1 = htIdeal ct h :=
  congrArg Subtype.val (dif_pos H : htIdl ct h = _)

variable (Z)

instance finite_tSub : Module.Finite (Z.i.c.V ct.W) (tSub Z σ) :=
  have := isPrincipalIdealRing_V ct Z
  inferInstance

instance free_tSub : Module.Free (Z.i.c.V ct.W) (tSub Z σ) :=
  have := isPrincipalIdealRing_V ct Z
  Module.free_of_finite_type_torsion_free'

def tSheaf : Z.X.Modules := freeModule Z.X (Fin (Module.finrank (Z.i.c.V ct.W) (tSub Z σ)))

theorem isVB_tSheaf : IsVB (tSheaf ct Z σ) (Module.finrank (Z.i.c.V ct.W) (tSub Z σ)) := isVB_freeModule_fin _ _

instance isFiniteQC_tSheaf : IsFiniteQC (tSheaf ct Z σ) := (isVB_tSheaf ct Z σ).isFiniteQC

def tSec (x : tSub Z σ) : Γ(tSheaf ct Z σ, ⊤) :=
  ∑ i, scal Z ((Module.finBasis _ (tSub Z σ)).repr x i) • freeBasis Z.X i

def epsT (t : S.Dw.La) : tSub Z σ :=
  ⟨tensorAction (laAct Z) (eps ct Z σ) (1 ⊗ₜ t), EigenSplit.mem_eigenSub.2 fun a => by
    have := congrArg (fun x => tensorAction (laAct Z) x (1 ⊗ₜ t)) (eps_mem ct Z σ a)
    simpa only [map_mul, map_smul, Module.End.mul_apply, EigenSplit.tensorAction_tmul, one_smul,
      LinearMap.smul_apply] using this⟩

def pairHom (t : S.Dw.La) : tSheaf ct Z σ ⟶ QCoh.structureModule Z.X :=
  sectionsHom fun i => scal Z (S.Dw.EF.baseChange (Z.i.c.V ct.W) (Module.finBasis _ (tSub Z σ) i) (1 ⊗ₜ t))

variable {Z}

abbrev redN {X : Scheme.{0}} (F : X.Modules) (m : ℕ) : F ⟶ modN F m := cokernel.π _

def IsSnd {m : ℕ} (g : modN (tSheaf ct Z σ) m ⟶ modN (epsOm ct h σ).toMod m) : Prop :=
  ∀ (t : S.Dw.La) (U : Z.X.Opens) (s : Γ((omP h).toMod, U)), IsLift h t s →
    g.app U ((redN _ m).app U (resM _ le_top (tSec ct Z σ (epsT ct Z σ t)))) =
      (redN _ m).app U ((toEps ct h σ).app U s)

def IsFst {m : ℕ} (f : modN (wSheaf ct h σ) m ⟶ modN (tSheaf ct Z σ) m) : Prop :=
  ∀ (U : Z.X.Opens) (l : Γ(wSheaf ct h σ, U)) (x : Γ(tSheaf ct Z σ, U)),
    f.app U ((redN _ m).app U l) = (redN _ m).app U x →
    ∀ (t : S.Dw.La) (s : Γ((omP h).toMod, U)), IsLift h t s → ∃ r : Γ(Z.X, U),
      QCoh.structureModuleSectionsEquiv U ((pairHom ct Z σ t).app U x) -
        dualApp l le_rfl ((toEps ct h (conjEmb σ)).app U s) = m • r

open Classical in

def sndMap (m : ℕ) : modN (tSheaf ct Z σ) m ⟶ modN (epsOm ct h σ).toMod m :=
  if H : ∃ g, IsSnd ct h σ (m := m) g then H.choose else 0

open Classical in

def fstMap (m : ℕ) : modN (wSheaf ct h σ) m ⟶ modN (tSheaf ct Z σ) m :=
  if H : ∃ f, IsFst ct h σ (m := m) f then H.choose else 0

theorem isSnd_sndMap {m : ℕ} (H : ∃ g, IsSnd ct h σ (m := m) g) : IsSnd ct h σ (sndMap ct h σ m) := by
  rw [sndMap, dif_pos H]
  exact H.choose_spec

theorem isFst_fstMap {m : ℕ} (H : ∃ f, IsFst ct h σ (m := m) f) : IsFst ct h σ (fstMap ct h σ m) := by
  rw [fstMap, dif_pos H]
  exact H.choose_spec

def ses : ct.SES Z where
  F₁ := Z.ofMod (wSheaf ct h σ)
  F₂ := Z.ofMod (tSheaf ct Z σ)
  F₃ := Z.ofMod (epsOm ct h σ).toMod
  k₀ := n - 2
  f := modNMap (ct.presIso _).hom _ ≫ fstMap ct h σ _ ≫ modNMap (ct.presIso _).inv _
  g := modNMap (ct.presIso _).hom _ ≫ sndMap ct h σ _ ≫ modNMap (ct.presIso _).inv _

variable (Z n) in

def BTOn : Type :=
  Σ (m : ℕ) (I : (PSpace (Z.i.c.V ct.W) m).IdealSheafData) (q : I.subscheme ⟶ Z.X),
    TruncBT (A.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) Z.t.act p n (Over.mk q)

def BTOn.Ext (B : BTOn ct Z n) : Prop := B.2.2.2.Extends Z.t.PP.L Z.opn

def BTOn.Compat {Z' : ct.Mdl} {n' : ℕ} (B : BTOn ct Z n) (B' : BTOn ct Z' n') : Prop :=
  ∃ (τ : (ct.Y Z'.i).X ⟶ (ct.Y Z.i).X) (mu : SABMap (ct.Y Z'.i).t (ct.Y Z.i).t τ) (f : Z'.X ⟶ Z.X)
    (φ : Z'.t.G.left ⟶ Z.t.G.left), LocM.IsTrans Z.i Z'.i τ mu ∧ f ≫ Z.π = Z'.π ≫ τ ∧ φ ≫ Z.tMap.φ = Z'.tMap.φ ≫ mu.φ ∧
      φ ≫ Z.t.G.hom = Z'.t.G.hom ≫ f ∧ B.2.2.2.IsTorsionOf B'.2.2.2 f φ

end GlobalTheory.LocM.HTm
