import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ChernOn
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfSpecializesOfFinite
import Development.AbelianVarietyTheory.Definitions.Divisors.AnalyticOnNhdFinChartIff
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.ExistsRetractTensorTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstChernClassPotential
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChartDirectionalDerivativeRegularCoordinate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ResidueFieldMapFiniteOfQuasiFinite

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts

namespace GlobalTheory.Mean4O

variable {F : Type} [Field F] [NumberField F] {C : CxSt F} {Y : Var F}

structure ManIs {e : ℕ} (M : Man e) (Y : Var F) : Type where

  ε : Fin (M.n + 1) ≃ (F →+* ℂ)

  pt : ∀ a, M.X a ≃ₜ Pts Y (ε a)

  alg : ∀ a j, ∃ c : AlgChart Y.str (ε a) e, (M.A a).chart j = (pt a).transOpenPartialHomeomorph c.finChart

theorem ManIs.κ_eq {e : ℕ} {M : Man e} (I : ManIs M Y) : M.κ = (Module.finrank ℚ F : ℝ)⁻¹ := by
  have h := Fintype.card_congr I.ε
  rw [Fintype.card_fin, NumberField.Embeddings.card] at h
  rw [M.κ_eq, ← h]
  push_cast
  rfl

variable (F) in

def embIdx : Fin (Fintype.card (F →+* ℂ) - 1 + 1) ≃ (F →+* ℂ) :=
  (Fintype.equivFinOfCardEq (Nat.sub_add_cancel Fintype.card_pos).symm).symm

instance compactSpace_pts (σ : F →+* ℂ) : CompactSpace (Pts Y σ) := CxPts.compactSpace σ Y.isProjOver

variable (Y) in

def atlasOf (σ : F →+* ℂ) : FinHolAtlas Y.dim (Pts Y σ) := (AnRead.all Y.str σ Y.dim).finAtlas

theorem isAlgAtlas_atlasOf (σ : F →+* ℂ) : IsAlgAtlas (atlasOf Y σ) := AnRead.isAlgAtlas_finAtlas _

variable (Y) in

def manOf (Z : ∀ σ, Set (Pts Y σ)) (r : ∀ σ, Pts Y σ → ℝ) (Om : ∀ σ, LocPot (Pts Y σ))
    (h : ∀ σ, IsBd (atlasOf Y σ) (Z σ) (r σ) (Om σ)) : Man Y.dim where
  n := Fintype.card (F →+* ℂ) - 1
  X a := Pts Y (embIdx F a)
  t2 _ := CxPts.t2Space_cxPts_of_isProjOver _ Y.isProjOver
  A _ := atlasOf Y _
  Z _ := Z _
  r _ := r _
  Om _ := Om _
  bd _ := h _
  κ := _
  κ_pos := by positivity
  κ_eq := rfl

def manIsOf (Z : ∀ σ, Set (Pts Y σ)) (r : ∀ σ, Pts Y σ → ℝ) (Om : ∀ σ, LocPot (Pts Y σ))
    (h : ∀ σ, IsBd (atlasOf Y σ) (Z σ) (r σ) (Om σ)) : ManIs (manOf Y Z r Om h) Y where
  ε := embIdx F
  pt _ := Homeomorph.refl _
  alg a j := (isAlgAtlas_atlasOf (Y := Y) (embIdx F a) j).imp fun c hc => hc.trans (by ext <;> rfl)

variable (Y) in

def fsPot (σ : F →+* ℂ) : LocPot (Pts Y σ) := ((ProjAn.fsO1 F σ Y.N).pull Y.ι Y.ι_str).locPot

theorem isBd_fsPot (σ : F →+* ℂ) : IsBd (atlasOf Y σ) ∅ (fun _ => Real.exp 1) (fsPot Y σ) :=
  have := CxPts.t2Space_cxPts_of_isProjOver σ Y.isProjOver
  InhabCalc.isBd_empty _ _
    ((ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (AnRead.all Y.str σ Y.dim)).isPotential (isAlgAtlas_atlasOf σ))
    (((ProjPos.fubiniStudy_weight_pullback_isSmooth _ _ (AnRead.all Y.str σ Y.dim)).isPosPot_iff (isAlgAtlas_atlasOf σ)).2
      (ProjPos.fubiniStudy_weight_pullback_closed_immersion_strictPos _ _ _))

theorem exists_manIs (Y : Var F) : ∃ M : Man Y.dim, Nonempty (ManIs M Y) :=
  ⟨_, ⟨manIsOf _ _ _ isBd_fsPot⟩⟩

section Norms

variable {σ : F →+* ℂ} {Δ : Y.Dv}

abbrev genAt (Δ : Y.Dv) (x : Y.X) : Y.Fn := ((eqn Δ x)⁻¹ : Y.Fnˣ)

omit [NumberField F] in

theorem generatesAt_genAt (Δ : Y.Dv) (x : Y.X) : Δ.GeneratesAt x (genAt Δ x) := by
  rw [genAt, Units.val_inv_eq_inv_val]
  exact CartierDiv.isEqn_iff_generatesAt_inv.1 (Base.isEqn_eqn Δ x)

def lnN (m : C.Met Y σ Δ) (f : Y.Fn) (y : Pts Y σ) : ℝ := Real.log (C.pn Y σ Δ m (C.cx Y σ f) y) / 2

def lnRatio (m m' : C.Met Y σ Δ) (y : Pts Y σ) : ℝ :=
  lnN m (genAt Δ (under y)) y - lnN m' (genAt Δ (under y)) y

def PosAt (m : C.Met Y σ Δ) (y : Pts Y σ) : Prop := 0 < C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under y))) y

theorem exists_pn_eq {f : Y.Fn} {y : Pts Y σ} (hf : Δ.GeneratesAt (under y) f) : ∃ a : ℝ, 0 < a ∧ ∀ m : C.Met Y σ Δ,
    C.pn Y σ Δ m (C.cx Y σ f) y = a * C.pn Y σ Δ m (C.cx Y σ (genAt Δ (under y))) y := by
  have he := Base.isEqn_eqn Δ (under y)
  have hu := he.generatesAt_iff.1 hf
  refine ⟨‖ratVal (f * (eqn Δ (under y) : Y.Fn)) y‖ ^ 2, ?_, fun m => ?_⟩
  · exact pow_pos (norm_pos_iff.2 (ratVal_ne_zero hu)) 2
  · rw [← C.pn_mul Y σ Δ m _ _ y hu.regAt (generatesAt_genAt Δ _).regularAt]
    congr 2
    simp [genAt]

theorem lnRatio_eq {m m' : C.Met Y σ Δ} {f : Y.Fn} {y : Pts Y σ} (hf : Δ.GeneratesAt (under y) f) (h : PosAt m y)
    (h' : PosAt m' y) : lnRatio m m' y = lnN m f y - lnN m' f y := by
  obtain ⟨a, ha, e⟩ := exists_pn_eq (C := C) hf
  simp only [lnRatio, lnN]
  rw [e m, e m', Real.log_mul ha.ne' (ne_of_gt h), Real.log_mul ha.ne' (ne_of_gt h')]
  ring

def IsPot {X : Type} [TopologicalSpace X] (h : X → Pts Y σ) (m : C.Met Y σ Δ) (P : LocPot X) : Prop :=
  ∀ x, ∃ f : Y.Fn, ∀ y ∈ P.U x, Δ.GeneratesAt (under (h y)) f ∧ PosAt m (h y) ∧ P.φ x y = -lnN m f (h y)

theorem isPot_ofWeight {L : LB Y.X} {r : L.ι → Y.Fnˣ} (h : Presents Δ L r) (φ : Weight Y.str σ L) :
    IsPot id (C.ofWeight Y σ Δ L r h φ) φ.locPot := fun x => by
  refine ⟨(r (pick φ.isLB x) : Y.Fn)⁻¹, fun y hy => ?_⟩
  have hi : under y ∈ L.U (pick φ.isLB x) := CxPts.mem_ptsIn.1 hy
  have hg := CartierDiv.isEqn_iff_generatesAt_inv.1 (h.isEqn _ _ hi)
  have e := C.pn_ofWeight Y σ Δ L r h φ _ y _ hi hg.regularAt
  rw [inv_mul_cancel₀ (Units.ne_zero _), Base.ratVal_one, norm_one, one_pow, one_mul] at e
  obtain ⟨a, ha, e'⟩ := exists_pn_eq (C := C) hg
  refine ⟨hg, ?_, ?_⟩
  · exact (mul_pos_iff_of_pos_left ha).1 ((Real.exp_pos _).trans_eq (e.symm.trans (e' _)))
  · simp only [lnN, id]
    rw [e, Real.log_exp, neg_div, neg_neg]
    rfl

end Norms

def ManIs.FormOf {e : ℕ} {M : Man e} (I : ManIs M Y) {ι : Type} [Fintype ι] {Δ : ι → Y.Dv}
    (m : ∀ i σ, C.Met Y σ (Δ i)) (t : ι → ℝ) (P : M.Pot) : Prop :=
  ∀ a, ∃ Q : ι → LocPot (M.X a), (∀ i, IsPot (I.pt a) (m i _) (Q i) ∧ IsPotential (M.A a) (Q i)) ∧
    ∀ j, ∀ y ∈ ((M.A a).chart j).target, ∀ w, leviAt (M.A a) (P a) j y w = ∑ i, t i * leviAt (M.A a) (Q i) j y w

theorem formOf_ofWeight {Z : ∀ σ, Set (Pts Y σ)} {r : ∀ σ, Pts Y σ → ℝ} {Om : ∀ σ, LocPot (Pts Y σ)}
    (h : ∀ σ, IsBd (atlasOf Y σ) (Z σ) (r σ) (Om σ)) {Δ : Y.Dv} {L : LB Y.X} {g : L.ι → Y.Fnˣ} (hL : Presents Δ L g)
    (φ : ∀ σ, Weight Y.str σ L) (hφ : ∀ σ, (φ σ).IsCInf) :
    (manIsOf Z r Om h).FormOf (fun (_ : Unit) σ => C.ofWeight Y σ Δ L g hL (φ σ)) (fun _ => 1) fun _ => (φ _).locPot :=
  fun a => ⟨fun _ => (φ _).locPot, fun _ => ⟨isPot_ofWeight hL _,
    ((Weight.isCInf_iff_isSmooth (AnRead.all Y.str _ Y.dim)).1 (hφ _)).isPotential (isAlgAtlas_atlasOf _)⟩,
    fun j y _ w => by simp⟩

def ManIs.Lists {e : ℕ} {M : Man e} (I : ManIs M Y) (x : Y.X) {d : ℕ} (z : ∀ a, Fin d → M.X a) : Prop :=
  ∀ a, Function.Injective (z a) ∧ Set.range (z a) = {w | under (I.pt a w) = x}

structure Cover (Y : Var F) : Type 1 where

  X : Scheme.{0}
  [int : IsIntegral X]

  p : X ⟶ Sp (𝓞 F)

  ar : IsArithVar p Y.dim

  normal : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X

  G : Scheme.{0}
  [intG : IsIntegral G]

  j : G ⟶ X

  π : G ⟶ Y.X

  pb : IsPullback j (π ≫ Y.str) p (spMap (algebraMap (𝓞 F) F))
  [fin : IsFinite π]
  [surj : Surjective π]

  φ : Y.Fn →+* G.functionField

  φ_spec : G.fromSpecStalk (genericPoint G) ≫ π = spMap φ ≫ Y.X.fromSpecStalk (genericPoint Y.X)

attribute [instance] Cover.int Cover.intG Cover.fin Cover.surj

namespace Cover

variable (V : Cover Y)

def deg : ℕ := V.π.residueDegree (genericPoint V.G)

def ν : ℝ := (Module.finrank ℚ F : ℝ) * V.deg

theorem deg_pos : 0 < V.deg := by
  let := (V.π.residueFieldMap (genericPoint V.G)).hom.toAlgebra
  have : Module.Finite (Y.X.residueField (V.π (genericPoint V.G))) (V.G.residueField (genericPoint V.G)) :=
    residueFieldMap_finite_of_locallyQuasiFinite V.π _
  exact Module.finrank_pos

theorem ν_pos : 0 < V.ν := mul_pos (Nat.cast_pos.2 Module.finrank_pos) (Nat.cast_pos.2 V.deg_pos)

def arMod {e : ℕ} (h : Y.dim = e) : ArMod e := ⟨𝓞 F, V.X, V.p, h ▸ V.ar⟩

def ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : Cover Y where
  X := M.X
  int := M.ar.isIntegral
  p := M.p
  ar := M.ar
  normal := h
  G := Y.X
  j := M.j
  π := 𝟙 _
  pb := by simpa using M.pb
  φ := RingHom.id _
  φ_spec := (Category.comp_id _).trans ((congrArg (· ≫ _) (Spec.map_id _)).trans (Category.id_comp _)).symm

theorem deg_ofModel (M : TrueGeo.Model Y) (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X) : (ofModel M h).deg = 1 :=
  Scheme.Hom.residueDegree_id _

def Induces (A : Adl C Y) (L : HermLB V.p) (k : ℕ) : Prop :=
  ∃ r : (L.B.pull V.j).ι → V.G.functionFieldˣ, IsRatSec (L.B.pull V.j) r ∧
    (∀ i, ∀ x ∈ (L.B.pull V.j).U i, UnitAt x (V.φ (genAt A.D (V.π x)) ^ k * r i)) ∧
    (∀ (σ : F →+* ℂ) (z : CxPts (V.π ≫ Y.str) σ) (y : Pts Y σ) (y' : CxPts V.p (σ.comp (algebraMap (𝓞 F) F)))
      (i : (L.B.pull V.j).ι), y.1 = z.1 ≫ V.π → y'.1 = z.1 ≫ V.j → under z ∈ (L.B.pull V.j).U i →
      (Real.exp (-(2 * (A.n : ℕ) * A.ci (InfinitePlace.mk σ))) *
          C.pn Y σ A.D (A.m σ) (C.cx Y σ (genAt A.D (under y))) y) ^ k =
        ‖ratVal (V.φ (genAt A.D (under y)) ^ k * (r i : V.G.functionField)) z‖ ^ 2 * Real.exp (-(L.φ _).φ (i PUnit.unit) y')) ∧
    ∀ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : AlgPt Y) (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X)
      (i : (L.B.pull V.j).ι), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ L.B.U (i PUnit.unit) →
      k * A.lg v e y = Real.log (e.w (valAt z (V.φ (genAt A.D (below y.1)) ^ k * (r i : V.G.functionField))))

theorem induces_ofModel {A : Adl C Y} {M : TrueGeo.Model Y} (h : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.X)
    {L : HermLB M.p} {k : ℕ+} (hL : A.Induced M L k 0) : (ofModel M h).Induces A L k := by
  obtain ⟨-, r, hr, h₁, h₂⟩ := hL
  have hg (x : Y.X) : ((k : ℕ) • A.D).GeneratesAt x (genAt A.D x ^ (k : ℕ)) := by
    have := CartierDiv.isEqn_iff_generatesAt_inv.1 ((Base.isEqn_eqn A.D x).nsmul k)
    rwa [Units.val_pow_eq_pow_val, ← inv_pow, ← Units.val_inv_eq_inv_val] at this
  refine ⟨r, hr.isRatSec, fun i x hx => (hr.isEqn i x hx).generatesAt_iff.1 (hg x), fun σ z y y' i e₁ e₂ hi => ?_,
    fun v e y z yt i e₁ e₂ hi => ?_⟩
  · obtain rfl : y = z := Subtype.ext (e₁.trans (Category.comp_id _))
    have := h₁ σ y y' i _ e₂ hi (hg _).regularAt
    rw [C.pn_mPow Y σ A.D k _ _ y (generatesAt_genAt _ _)] at this
    rw [mul_pow, ← Real.exp_nat_mul]
    refine Eq.trans ?_ this
    congr 2
    ring
  · obtain rfl : z = y.1 := (Category.comp_id _).symm.trans e₁
    have := h₂ v e y yt i e₂ hi
    rw [Pi.zero_apply, mul_zero, sub_zero, Units.val_mul, Units.val_pow_eq_pow_val] at this
    exact this

def IsDown {e : ℕ} {M : Man e} (I : ManIs M Y) (ε : (𝓞 F →+* ℂ) → Fin (M.n + 1))
    (π : ∀ σ, CxPts V.p σ → M.X (ε σ)) : Prop :=
  ∀ σ, (I.ε (ε σ)).comp (algebraMap (𝓞 F) F) = σ ∧
    ∀ z, ∃ w : Sp ℂ ⟶ V.G, w ≫ V.j = z.1 ∧ w ≫ V.π = (I.pt _ (π σ z)).1

theorem exists_isDown {e : ℕ} {M : Man e} (I : ManIs M Y) : ∃ ε π, V.IsDown I ε π := by
  have h (σ : 𝓞 F →+* ℂ) : ∃ a, (I.ε a).comp (algebraMap (𝓞 F) F) = σ := by
    have hi : Function.Injective σ := (RingHom.injective_iff_ker_eq_bot _).2
      (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))
    obtain ⟨τ, hτ⟩ : ∃ τ : F →+* ℂ, τ.comp (algebraMap (𝓞 F) F) = σ :=
      ⟨IsFractionRing.lift (K := F) hi, RingHom.ext fun x => by
        rw [RingHom.comp_apply, IsFractionRing.lift_algebraMap]⟩
    exact ⟨I.ε.symm τ, by rwa [Equiv.apply_symm_apply]⟩
  choose ε hε using h
  have h' (σ : 𝓞 F →+* ℂ) (z : CxPts V.p σ) : ∃ y : M.X (ε σ), ∃ w : Sp ℂ ⟶ V.G,
      w ≫ V.j = z.1 ∧ w ≫ V.π = (I.pt _ y).1 := by
    have e : z.1 ≫ V.p = spMap (I.ε (ε σ)) ≫ spMap (algebraMap (𝓞 F) F) := by
      rw [z.2, ← hε σ, hε σ]
      exact (congrArg spMap (hε σ).symm).trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom _))
    refine ⟨(I.pt _).symm ⟨V.pb.lift _ _ e ≫ V.π, by rw [Category.assoc, V.pb.lift_snd]⟩, V.pb.lift _ _ e,
      V.pb.lift_fst _ _ _, ?_⟩
    rw [Homeomorph.apply_symm_apply]
  choose π hπ using h'
  exact ⟨ε, π, fun σ => ⟨hε σ, hπ σ⟩⟩

end Cover

example (C : CxSt ℚ) (n : ℕ) : ∃ V : Cover (proj ℚ n), V.deg = 1 ∧ V.Induces (Adl.triv C _) (HermLB.triv V.p) 1 :=
  have : IsPrincipalIdealRing (𝓞 ℚ) :=
    .of_surjective Rat.ringOfIntegersEquiv.symm.toRingHom Rat.ringOfIntegersEquiv.symm.surjective
  ⟨.ofModel (Model.pspace ℚ n) (Models.isNormalScheme_projSpace _ n), Cover.deg_ofModel _ _,
    Cover.induces_ofModel _ (Adl.induced_triv C _)⟩

end GlobalTheory.Mean4O
