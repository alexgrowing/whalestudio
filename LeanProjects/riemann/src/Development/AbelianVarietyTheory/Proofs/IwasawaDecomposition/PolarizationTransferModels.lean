import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStableOfNoBoundary
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SemiAbelianModelDeterminedByGenericFibre

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.FiniteStable

namespace GlobalTheory.TraitOrder

theorem idlAlong_eq_map {X : Scheme.{0}} (J : X.IdealSheafData) {R : Type} [CommRing R] [IsLocalRing R] (χ : Sp R ⟶ X)
    (U : X.affineOpens) (hle : ⊤ ≤ χ ⁻¹ᵁ U.1) :
    idlAlong J χ = (J.ideal U).map (χ.appLE U.1 ⊤ hle ≫ (Scheme.ΓSpecIso (.of R)).hom).hom := by
  have hx : χ (closedPoint R) ∈ U.1 := hle trivial
  unfold idlAlong
  rw [ds_stalkId_eq_map J U _ hx, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.germ_stalkClosedPointTo]
  congr 2

theorem idlAlong_comp {X : Scheme.{0}} (J : X.IdealSheafData) {R S : Type} [CommRing R] [IsLocalRing R] [CommRing S]
    [IsLocalRing S] (χ : Sp R ⟶ X) (f : R →+* S) : idlAlong J (spMap f ≫ χ) = (idlAlong J χ).map f := by
  obtain ⟨U, hU, hx, -⟩ := Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show χ (closedPoint R) ∈ (⊤ : X.Opens) from trivial)
  have hle : ⊤ ≤ χ ⁻¹ᵁ U := (Scheme.preimage_eq_top_of_closedPoint_mem χ hx).ge
  have hle' : ⊤ ≤ (spMap f ≫ χ) ⁻¹ᵁ U := fun x _ => hle (show spMap f x ∈ (⊤ : (Sp R).Opens) from trivial)
  rw [idlAlong_eq_map J χ ⟨U, hU⟩ hle, idlAlong_eq_map J _ ⟨U, hU⟩ hle', Ideal.map_map]
  congr 1
  have e : (spMap f ≫ χ).appLE U ⊤ hle' = χ.appLE U ⊤ hle ≫ (spMap f).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  rw [e, Category.assoc, Scheme.ΓSpecIso_naturality, ← Category.assoc, CommRingCat.hom_comp]
  rfl

theorem map_injective {R S : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing S] [IsDomain S]
    [IsLocalRing S] (f : R →+* S) (hf : Function.Injective f) [IsLocalHom f] {I J : Ideal R}
    (h : I.map f = J.map f) : I = J := by
  letI := f.toAlgebra
  have : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective _ _).2 hf
  have : IsLocalHom (algebraMap R S) := ‹IsLocalHom f›
  have : Module.Flat R S := inferInstance
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) I, ← Ideal.comap_map_eq_self_of_faithfullyFlat (B := S) J]
  exact congrArg _ h

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

def twistOAct (σ : 𝓞 E ≃+* 𝓞 E) {S : Scheme.{0}} {A : PolAV S} (o : letI := H.starRing; A.OAct (𝓞 E)) :
    letI := H.starRing; A.OAct (𝓞 E) :=
  letI := H.starRing
  { act := fun a => o.act (σ a)
    hom := fun a => o.hom _
    map_one := by rw [_root_.map_one, o.map_one]
    map_mul := fun a b => by rw [_root_.map_mul, o.map_mul]
    map_add := fun a b => by rw [_root_.map_add, o.map_add]
    rosati := fun a => by
      have := o.rosati (σ a)
      change RosatiAdj _ _ _ (o.act (H.bar _)) at this
      rwa [← aut_bar] at this }

def twistUnif (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {R : Type} [CommRing R] [IsDomain R] {I : Ideal R}
    {t : SAB H (Sp R)} (P : PELUnif I t) : PELUnif I (FiniteStable.twist σ hσ t) :=
  letI := H.starRing
  @PELUnif.mk E _ _ _ H R _ _ I (FiniteStable.twist σ hσ t) P.D (Module.compHom _ σ.toRingHom)
    (@DegPre.OAct.mk R _ _ (𝓞 E) _ _ P.D.toPre (Module.compHom _ σ.toRingHom) (twistOAct σ P.oD.onB)
      (fun a y => P.oD.c_lin (σ a) y) (fun a => by
        have := P.oD.tau_bal (σ a)
        change DegPre.TauBal _ _ (P.oD.onB.act (H.bar _)) _ (fun y => H.bar _ • y) at this
        rw [← aut_bar] at this
        exact this))
    P.A (twistOAct σ P.oA) P.U P.bundle
    (@UnifPre.OLinear.mk R _ _ I (𝓞 E) _ _ P.D (Module.compHom _ σ.toRingHom) _ _ _ _ _ _ _ _
      (fun a => P.lin.ext (σ a)) (fun e a => P.lin.q_lin e (σ a)) (fun e a => by
        have := P.lin.i_lin e (σ a)
        change ∃ _, TorusEndOf _ (fun y => H.bar _ • y) _ ∧ _ at this
        rw [← aut_bar] at this
        exact this))
    (by
      have := P.w0
      rw [← hσ] at this
      exact this)

theorem evalZ_twist {φ : InvFun (𝓞 E)} (hφ : IsTwInv H φ) (σ : 𝓞 E ≃+* 𝓞 E) (hσ : σ H.w0 = H.w0) {X : Type}
    [AddCommGroup X] [m : Module (𝓞 E) X] [hf : Module.Finite (𝓞 E) X]
    (hf' : @Module.Finite (𝓞 E) X _ _ (Module.compHom _ σ.toRingHom)) (be : LinearMap.BilinForm ℤ X) :
    @InvFun.evalZ _ _ φ X _ (Module.compHom _ σ.toRingHom) hf' be = φ.evalZ be := by
  obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
  unfold InvFun.evalZ
  rw [φ.eval_eq hr, ← hφ σ hσ]
  let g : (Fin n → 𝓞 E) →+ X := r.toAddMonoidHom.comp
    ⟨⟨fun a i => σ (a i), by ext; simp⟩, fun a b => by ext; simp⟩
  have hg : ∀ (c : 𝓞 E) a, g (c • a) = σ c • g a := fun c a => by
    change r _ = σ c • r _
    rw [← map_smul]
    congr 1
    ext i
    simp
  have hs : Function.Surjective g := hr.comp fun a => ⟨fun i => σ.symm (a i), funext fun i => σ.apply_symm_apply _⟩
  letI : Module (𝓞 E) X := Module.compHom _ σ.toRingHom
  exact φ.eval_eq (r := ⟨g.toAddHom, hg⟩) hs _

theorem exists_pull {S S' : Scheme.{0}} (f : S' ⟶ S) (t : SAB H S) : ∃ t' : SAB H S', Nonempty (SABMap t' t f) := by
  obtain ⟨_, _, _, _, _, m, -⟩ := sabPull CubePf.cubePull f t
  exact ⟨_, ⟨m⟩⟩

theorem comp {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (m' : SABMap t'' t' g) : Nonempty (SABMap t'' t h) :=
  e ▸ ⟨(sabComp pullCubComp E H _ _ _ _ _ _ _ _ m m').choose⟩

theorem cancel {S S' S'' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {t'' : SAB H S''} {f : S' ⟶ S} {g : S'' ⟶ S'}
    {h : S'' ⟶ S} (e : g ≫ f = h) (m : SABMap t' t f) (n : SABMap t'' t h) : Nonempty (SABMap t'' t' g) := by
  subst e
  exact ⟨(sabCancel pullCubCancel E H _ _ _ _ _ _ _ _ m n).choose⟩

theorem idlAlong_eq : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l' : Level H) (Xo : Moduli D l)
    (Xo' : Moduli D l') (c : Coeff l) (c' : Coeff l') (O O' : Type) [CommRing O] [CommRing O'] (β : O →+* c.F)
    (β' : O' →+* c'.F) (Z : Model Xo c β) (Z' : Model Xo' c' β') (BD : EffCartierData Z.X) (BD' : EffCartierData Z'.X)
    (φ : InvFun (𝓞 E)) (σ : 𝓞 E ≃+* 𝓞 E) (r : Xo'.XF c' ⟶ Xo.XF c)
    (ν : TwMap σ Z'.oF.t Z.oF.t r), IsDedFrac β → IsDedFrac β' → IsTwInv H φ → σ H.w0 = H.w0 →
    IsPhiDiv φ Z BD → IsPhiDiv φ Z' BD' →
    ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W], CDvr W → ∀ (χ : Sp W ⟶ Z.X) (χ' : Sp W ⟶ Z'.X)
      (y : Sp (FractionRing W) ⟶ Xo'.XF c'), jK W ≫ χ' = y ≫ Z'.j → jK W ≫ χ = y ≫ r ≫ Z.j →
      idlAlong BD'.idealSheaf χ' = idlAlong BD.idealSheaf χ := by
  intro E _ _ _ H D l l' Xo Xo' c c' O O' _ _ β β' Z Z' BD BD' φ σ r ν _ _ hφ hσ hd hd' W _ _ _ hW χ χ' y hy' hy
  obtain ⟨h₁, h₂, h₃⟩ := hW
  let T : CDVR := { V := W }
  obtain ⟨t', ⟨m'⟩⟩ := exists_pull χ' Z'.t
  obtain ⟨s, ⟨ms⟩⟩ := exists_pull χ (FiniteStable.twist σ hσ Z.t)
  obtain ⟨tK, ⟨mK⟩⟩ := exists_pull y Z'.oF.t
  let ν' : SABMap Z'.oF.t (FiniteStable.twist σ hσ Z.oF.t) r := ⟨ν.cm, ν.cart, ν.base, ν.act, ν.lin⟩
  let mZ : SABMap (FiniteStable.twist σ hσ Z.oF.t) (FiniteStable.twist σ hσ Z.t) Z.j :=
    ⟨Z.m.cm, Z.m.cart, Z.m.base, fun a => Z.m.act (σ a), Z.m.lin⟩
  obtain ⟨a₁⟩ := comp hy'.symm (show SABMap Z'.oF.t Z'.t Z'.j from Z'.m) mK
  obtain ⟨a₂⟩ := cancel rfl m' a₁
  obtain ⟨b₀⟩ := comp rfl mZ ν'
  obtain ⟨b₁⟩ := comp hy.symm b₀ mK
  obtain ⟨b₂⟩ := cancel rfl ms b₁
  obtain ⟨ψ, -⟩ := GlobalTheory.semiAbelian_model_determined_by_generic_fibre E H W h₂ t' s tK
    (MorphismProperty.of_isPullback (P := @IsProper) mK.cart.1 Z'.oF.proper) a₂ b₂
  obtain ⟨n⟩ := comp (Category.id_comp χ) ms ψ
  have hp := GlobalTheory.GoodTrait.polAt_of_point Z' m' (jK W) y hy'.symm
  obtain ⟨T', f, u, hi, hl, ⟨mu⟩, ⟨P⟩⟩ := exists_unif_ext T t' hp
  obtain ⟨n'⟩ := comp rfl m' mu
  obtain ⟨n₁⟩ := comp rfl n mu
  have hσ' : σ.symm H.w0 = H.w0 := σ.symm_apply_eq.2 hσ.symm
  let n₂ : SABMap (FiniteStable.twist σ.symm hσ' u) Z.t (spMap f ≫ χ) :=
    ⟨n₁.cm, n₁.cart, n₁.base, fun a => by
      have := n₁.act (σ.symm a)
      change _ = _ ≫ (Z.t.act.act (σ (σ.symm a))).left at this
      rwa [σ.apply_symm_apply] at this, n₁.lin⟩
  have j : Function.Injective ((algebraMap T'.V (FractionRing T'.V)).comp f) :=
    (IsFractionRing.injective T'.V _).comp hi
  let g : FractionRing W →+* FractionRing T'.V := IsFractionRing.lift j
  have e : jK T'.V ≫ spMap f = spMap g ≫ jK W :=
    (GlobalTheory.Ex.UnifModel.spMap_comp fun _ => rfl).trans
      (GlobalTheory.Ex.UnifModel.spMap_comp (IsFractionRing.lift_algebraMap j)).symm
  have hr' : Set.range (jK T'.V ≫ spMap f ≫ χ') ⊆ Set.range Z'.j := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, ← hy', ← Category.assoc, ← e, Category.assoc]
  have hr : Set.range (jK T'.V ≫ spMap f ≫ χ) ⊆ Set.range Z.j := by
    rintro _ ⟨p, rfl⟩
    refine ⟨(spMap g ≫ y ≫ r) p, ?_⟩
    rw [← Scheme.Hom.comp_apply, Category.assoc, Category.assoc, ← hy, ← Category.assoc, ← e, Category.assoc]
  have hW' : CDvr T'.V := ⟨T'.dvr, T'.cpl, T'.ch0⟩
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T'.V
  obtain ⟨be, hbe, hmon, -⟩ := exists_periodForm P hϖ
  obtain ⟨k', hk', hid'⟩ := hd' T'.V hW' ϖ hϖ _ u n' P hr' be hbe hmon
  obtain ⟨k, hk, hid⟩ := hd T'.V hW' ϖ hϖ _ _ n₂ (twistUnif σ.symm hσ' P) hr be
    ⟨hbe.1, fun a x z => by
      have := hbe.2.1 (σ.symm a) x z
      rw [← aut_bar] at this
      exact this, hbe.2.2⟩ hmon
  have hkk : (k : ℝ) = k' := hk.trans ((evalZ_twist hφ σ.symm hσ' _ be).trans hk'.symm)
  obtain rfl : k = k' := by exact_mod_cast hkk
  refine map_injective f hi ?_
  rw [← idlAlong_comp, ← idlAlong_comp]
  exact hid'.trans hid.symm

end GlobalTheory.TraitOrder
