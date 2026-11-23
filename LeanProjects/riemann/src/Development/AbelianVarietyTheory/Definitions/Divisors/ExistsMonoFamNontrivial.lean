import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsOverIff
import Development.AbelianVarietyTheory.Definitions.Divisors.RigidForFan
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsConstAlongConeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitPartOfPeriodTauMonomial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPosCombinationSmoothConeSymmIntForm
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PullbackModelArcPeriod
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FormallyUnramifiedEtaleCompletion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConeAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSemiAbelianPolarized
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformizationAbelian
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IntBilinFormToRealMemBalancedPsdCone
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ArcWitnessModelPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CompactifiedModuliPartOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsFan

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UChart

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}

def Classifies (Xo : Moduli Dw l) (c : Coeff l) {T T' : Scheme.{0}} (t : SAB H T) (g : T' ⟶ T) (y : T' ⟶ Xo.XF c) : Prop :=
  ∃ t' : SAB H T', Nonempty (SABMap t' t g) ∧ Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _))

theorem genOf_iff (Xo : Moduli Dw l) (c : Coeff l) {R : Type} [CommRing R] [IsDomain R] (y : Sp (FractionRing R) ⟶ Xo.XF c)
    (t : SAB H (Sp R)) : GlobalTheory.UPoinc.GenOf Xo c y t ↔ Classifies Xo c t (jK R) y := Iff.rfl

theorem Classifies.pull {Xo : Moduli Dw l} {c : Coeff l} {T T' T'' : Scheme.{0}} {t : SAB H T} {g : T' ⟶ T}
    {y : T' ⟶ Xo.XF c} (h : Classifies Xo c t g y) (f : T'' ⟶ T') : Classifies Xo c t (f ≫ g) (f ≫ y) := by
  obtain ⟨t', ⟨m₁⟩, ⟨m₂⟩⟩ := h
  obtain ⟨t'', ⟨n⟩⟩ := GlobalTheory.TraitOrder.exists_pull f t'
  exact ⟨t'', GlobalTheory.TraitOrder.comp rfl m₁ n, GlobalTheory.TraitOrder.comp (Category.assoc _ _ _).symm m₂ n⟩

structure Fam (Xo : Moduli Dw l) (c : Coeff l) (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] where

  b : c.F →+* R

  t : SAB H (Sp R)

  P : PELUnif (maximalIdeal R) t

  y : Sp (FractionRing R) ⟶ Xo.XF c
  y_over : y ≫ pullback.snd _ _ = jK R ≫ spMap b
  gen : GlobalTheory.UPoinc.GenOf Xo c y t

structure MonoFam (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (R : Type) [CommRing R] [IsDomain R]
    [IsLocalRing R] extends Fam Xo c R where

  m : ℕ

  s : Fin m → R
  s_mem : ∀ i, s i ∈ maximalIdeal R

  δ : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X
  cone : IsCone H.bar φ δ
  rank : Module.finrank (𝓞 E) P.D.toPre.X ≤ min Dw.p Dw.q
  mono : IsMonomial P.D.toPre s (fun i => (l.M' : ℤ) • δ i)

variable {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

abbrev Gens {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) : Type :=
  ∀ a b : Q.X, LB.Gen (LB.LinComb Q.P.L (K := Fin 4) ![(Q.c (a + b)).left, (Q.c a).left, (Q.c b).left, (Q.c 0).left]
    ![-1, 1, 1, -1])

def TauIn {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V)
    (ε : Fin N → LinearMap.BilinForm ℤ Q.X) : Prop :=
  ∀ a b, (τ₀ a b).IsGen ∧ ∃ k : (FractionRing V)ˣ,
    (k : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ ε i a b ∧ ∀ z J, Good Q.P.L z J →
      val (Q.tau a b) (𝟙 _) z J = gm (𝟙 (TK V).left) z ⊤ (unitOn k) * val (τ₀ a b) (toUnit (TK V)).left z J

theorem tauIn_iff {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) (τ₀ : Gens Q) {N : ℕ} (s : Fin N → V)
    (ε : Fin N → LinearMap.BilinForm ℤ Q.X) :
    TauIn Q τ₀ s ε ↔ ∀ a b, GlobalTheory.RigChart.IsUnitTau Q s ε a b (τ₀ a b) := Iff.rfl

def lamUnit {B B₀ B' Z : Scheme.{0}} {M : LB B} {M₀ : LB B₀} {π₁ : B' ⟶ B} {π₀ : B' ⟶ B₀}
    (w : LB.Iso (M.pull π₁) (M₀.pull π₀)) {X : Type} [AddCommGroup X] (x : X → (Z ⟶ B')) (a b : X) (z : Z)
    (J : (Z ⟶ B) → M.ι) (J₀ : (Z ⟶ B₀) → M₀.ι) : (Z.presheaf.stalk z)ˣ :=
  gw w (x (a + b)) z (J₀ (x (a + b) ≫ π₀)) (fun _ => J (x (a + b) ≫ π₁)) *
    (gw w (x a) z (J₀ (x a ≫ π₀)) (fun _ => J (x a ≫ π₁)))⁻¹ *
    (gw w (x b) z (J₀ (x b ≫ π₀)) (fun _ => J (x b ≫ π₁)))⁻¹ *
    gw w (x 0) z (J₀ (x 0 ≫ π₀)) (fun _ => J (x 0 ≫ π₁))

def SepAt {V : Type} [CommRing V] [IsDomain V] (Q : DegPre V) {m : ℕ} (s : Fin m → V)
    (gam : Fin m → LinearMap.BilinForm ℤ Q.X) {K : Type} [Field K] (ev : V →+* K) (k₀ : Subfield K) : Prop :=
  (∀ i, ev (s i) = 0) ∧
  ∃ (B₀ : Over (Sp k₀)) (_ : GrpObj B₀) (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (c₀ : Q.X → (Sp k₀ ⟶ B₀.left))
    (B' : Over (Sp K)) (_ : GrpObj B') (π₁ : B'.left ⟶ Q.P.A.left) (π₀ : B'.left ⟶ B₀.left)
    (w : LB.Iso (Q.P.L.pull π₁) (M₀.pull π₀)) (c' : Q.X → (Sp K ⟶ B'.left)) (α : Fin m → Kˣ),
    IsAbelianScheme B₀ ∧ M₀.IsLB ∧ IsGrpPullback B' Q.P.A (spMap ev) π₁ ∧ IsGrpPullback B' B₀ (spMap k₀.subtype) π₀ ∧
    w.IsGen ∧
    (∀ a, c' a ≫ B'.hom = 𝟙 _ ∧ c' a ≫ π₁ = spMap ev ≫ (Q.c a).left ∧ c' a ≫ π₀ = spMap k₀.subtype ≫ c₀ a) ∧
    ∀ a b τ₀, GlobalTheory.RigChart.IsUnitTau Q s gam a b τ₀ →
      ∃ τ₁ : LB.Gen (LB.LinComb M₀ (K := Fin 4) ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] ![-1, 1, 1, -1]), τ₁.IsGen ∧
        ∀ z J J₀, Good Q.P.L z J → Good M₀ z J₀ →
          val τ₀ (spMap ev) z J = lamUnit w c' a b z J J₀ *
            gm (𝟙 (Sp K)) z ⊤ (unitOn (∏ i, α i ^ gam i a b)) * val τ₁ (spMap k₀.subtype) z J₀

abbrev DefOver {K : Type} [Field K] (k₀ : Subfield K) {Y : Scheme.{0}} (P : Sp K ⟶ Y) : Prop :=
  GlobalTheory.Poinc.Sep.DefOver k₀ P

def Sep (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) : Prop :=
  ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (C : MonoFam Xo c φ V), GlobalTheory.Mum.Base V →
    ∀ ξ : Sp V ⟶ S, C.y ≫ j = jK V ≫ ξ →
    ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : V →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
      (∀ p, (spMap ev ≫ ξ) p = ξ (closedPoint V)) → DefOver k₀ (spMap ev ≫ ξ) →
      SepAt C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ev k₀

variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]

def OpenCls (C : MonoFam Xo c φ R) : Prop :=
  ∃ (yo : Sp (Localization.Away (∏ i, C.s i)) ⟶ Xo.XF c) (tO : SAB H (Sp (Localization.Away (∏ i, C.s i)))),
    Nonempty (SABMap tO C.t (spMap (algebraMap R (Localization.Away (∏ i, C.s i))))) ∧
    Nonempty (SABMap tO Xo.univ.t (yo ≫ pullback.fst _ _)) ∧
    ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, C.s i)),
      g ≫ spMap (algebraMap R (Localization.Away (∏ i, C.s i))) = jK R → g ≫ yo = C.y

theorem openCls_iff (C : MonoFam Xo c φ R) : OpenCls C ↔
    ∃ yo : Sp (Localization.Away (∏ i, C.s i)) ⟶ Xo.XF c,
      Classifies Xo c C.t (spMap (algebraMap R (Localization.Away (∏ i, C.s i)))) yo ∧
      ∀ g : Sp (FractionRing R) ⟶ Sp (Localization.Away (∏ i, C.s i)),
        g ≫ spMap (algebraMap R (Localization.Away (∏ i, C.s i))) = jK R → g ≫ yo = C.y :=
  ⟨fun ⟨yo, tO, h₁, h₂, h₃⟩ => ⟨yo, ⟨tO, h₁, h₂⟩, h₃⟩, fun ⟨yo, ⟨tO, h₁, h₂⟩, h₃⟩ => ⟨yo, tO, h₁, h₂, h₃⟩⟩

def Inj (C : MonoFam Xo c φ R) : Prop :=
  ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsLocalRing R'], GlobalTheory.Mum.Base R' → ∀ θ₁ θ₂ : R →+* R',
    Function.Injective θ₁ → Function.Injective θ₂ → IsLocalHom θ₁ → IsLocalHom θ₂ →
    ∀ κ₁ κ₂ : Sp (FractionRing R') ⟶ Sp (FractionRing R), κ₁ ≫ jK R = jK R' ≫ spMap θ₁ →
      κ₂ ≫ jK R = jK R' ≫ spMap θ₂ → κ₁ ≫ C.y = κ₂ ≫ C.y → θ₁ = θ₂

def PointRigid (C : MonoFam Xo c φ R) : Prop :=
  ∀ (K : Type) [Field K] [IsAlgClosed K] (ev : R →+* K) (k₀ : Subfield K), IsAlgClosed k₀ →
    Nonempty (k₀ →+* AlgebraicClosure (ResidueField R)) → SepAt C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ev k₀ →
    (∀ r ∈ maximalIdeal R, ev r = 0) ∧ ∀ r, ev r ∈ k₀

def IsTaut {k : Type} [Field k] {m e : ℕ} (C : MonoFam Xo c φ (ChartRing k m e)) : Prop :=
  ∃ hm : C.m = m, (∀ i, C.s i = bdParam k m e (Fin.cast hm i)) ∧ OpenCls C ∧ Inj C ∧
    (GlobalTheory.RigChart.IsRigid C.P.D.toPre C.s (fun i => (l.M' : ℤ) • C.δ i) ∧ PointRigid C ∧
      ((residue (ChartRing k m e)).comp C.b).EssFiniteType) ∧
    (∃ (N : ℕ) (s : Fin C.m ⊕ Fin N → ChartRing k m e)
      (ε : Module.Basis (Fin C.m ⊕ Fin N) ℤ (balForms H.bar C.P.D.toPre.X)) (τ₀ : Gens C.P.D.toPre),
      (∀ i, s (.inl i) = C.s i) ∧ (∀ i, (ε (.inl i) : LinearMap.BilinForm ℤ _) = C.δ i) ∧ (∀ k, IsUnit (s (.inr k))) ∧
      TauIn C.P.D.toPre τ₀ (fun k => s (finSumFinEquiv.symm k))
        (fun k => (l.M' : ℤ) • (ε (finSumFinEquiv.symm k) : LinearMap.BilinForm ℤ C.P.D.toPre.X))) ∧
    (letI := ((residue (ChartRing k m e)).comp C.b).toAlgebra;
      ((m + e : ℕ) : Cardinal) + Algebra.trdeg c.F (ResidueField (ChartRing k m e)) = Dw.dim)

def UPre (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) {S : Scheme.{0}} (j : Xo.XF c ⟶ S) [IsOpenImmersion j]
    (BD : EffCartierData S) (d : ℕ) (x : S) : Prop :=
  ∃ (k : Type) (_ : Field k) (m e : ℕ) (C : MonoFam Xo c φ (ChartRing k m e)) (ξ : Sp (ChartRing k m e) ⟶ S)
    (a : Fin C.m → ℕ),
    IsTaut C ∧ C.y ≫ j = jK _ ≫ ξ ∧ ξ (closedPoint _) = x ∧ IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom ∧
    idlAlong (Scheme.IdealSheafData.vanishingIdeal j.opensRange.compl) ξ = Ideal.span {∏ i, C.s i} ∧
    (∀ p : Sp (ChartRing k m e), ξ p ∈ Set.range j ↔ ∏ i, C.s i ∉ p.asIdeal) ∧
    (∀ i, (a i : ℝ) = d * φ.evalZ ((l.M' : ℤ) • C.δ i)) ∧ idlAlong BD.idealSheaf ξ = Ideal.span {∏ i, C.s i ^ a i}

theorem Fam.rank_le [IsNoetherianRing R] (C : Fam Xo c R) :
    Module.finrank (𝓞 E) C.P.D.toPre.X ≤ min Dw.p Dw.q := by
  haveI : CharZero R := C.b.charZero_iff C.b.injective |>.1 inferInstance
  obtain ⟨tK, ⟨m₁⟩, ⟨m₂⟩⟩ := C.gen
  let K := AlgebraicClosure (FractionRing R)
  let f : R →+* K := (algebraMap (FractionRing R) K).comp (algebraMap R (FractionRing R))
  have hf : Function.Injective f :=
    (algebraMap (FractionRing R) K).injective.comp (IsFractionRing.injective R (FractionRing R))
  haveI : CharZero K := ⟨fun a b h => Nat.cast_injective (R := R) (hf (by simpa using h))⟩
  let u : Sp K ⟶ Sp (FractionRing R) := spMap (algebraMap (FractionRing R) K)
  have hu : u ≫ jK R = spMap f := (Spec.map_comp _ _).symm
  obtain ⟨β₀, hβ₀⟩ := Spec.map_surjective ((u ≫ C.y ≫ pullback.fst _ _) ≫ Xo.s)
  have hdet := (Xo.univ.geom K _ β₀.hom hβ₀.symm).1
  have hr : (β₀.hom (baseKA l).ρ) ^ 2 = -(H.d : K) := by
    rw [← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have bound : ∀ (τ : 𝓞 E →+* K) (N : ℕ), LieMult Xo.univ.t.act (u ≫ C.y ≫ pullback.fst _ _) τ N →
      Module.finrank (𝓞 E) C.P.D.toPre.X ≤ N := by
    intro τ N hN
    have h₅ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₂.cart tK.act Xo.univ.t.act m₂.act u τ N).2 hN
    have h₆ := (GlobalTheory.lieMult_iff_of_isGrpPullback m₁.cart tK.act C.t.act m₁.act u τ N).1 h₅
    rw [hu] at h₆
    obtain ⟨n, -, hn⟩ := GlobalTheory.CharRank.lieMult_unif_loc H R C.t C.P K f hf τ N h₆
    omega
  obtain ⟨τ₁, τ₂, h₁, h₂⟩ := GlobalTheory.CharRank.exists_chars H K _ hr
  exact le_min (bound τ₁ _ ((hdet τ₁).1 h₁)) (bound τ₂ _ ((hdet τ₂).2 h₂))

theorem level_pos (l : Geo.Tor.Level H) : 0 < l.M' :=
  Nat.lcm_pos (by have := l.three_le; omega) l.A_pos

theorem MonoFam.s_ne_zero (C : MonoFam Xo c φ R) (i : Fin C.m) : C.s i ≠ 0 := by
  intro h0
  have hy : ∃ y, C.δ i y y ≠ 0 := by
    by_contra hn
    push Not at hn
    refine C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => ?_)
    have := hn (a + b)
    simp only [map_add, LinearMap.add_apply, hn, (C.cone.mem i).1 b a] at this
    simp only [LinearMap.zero_apply]
    omega
  obtain ⟨y, hy⟩ := hy
  obtain ⟨u, n, hn, e⟩ := C.mono y
  have hni : n i ≠ 0 := fun h1 => by
    have := hn i
    simp only [h1, LinearMap.smul_apply, smul_eq_mul, Nat.cast_zero, mul_zero, mul_eq_zero] at this
    exact this.elim (by exact_mod_cast (level_pos l).ne') hy
  exact GlobalTheory.PsiCoordLocal.ne_zero_of_coord e (by
    rw [Finset.prod_eq_zero (Finset.mem_univ i) (by rw [h0, zero_pow hni]), mul_zero])

theorem MonoFam.exists_tauIn (C : MonoFam Xo c φ R) :
    ∃ τ₀ : Gens C.P.D.toPre, TauIn C.P.D.toPre τ₀ C.s (fun i => (l.M' : ℤ) • C.δ i) := by
  choose τ₀ h using GlobalTheory.UnitTau.exists_isUnitTau C.P.D.toPre C.s _ C.mono
    (fun i y z => by simp only [LinearMap.smul_apply, (C.cone.mem i).1 y z]) C.s_ne_zero
  exact ⟨τ₀, h⟩

theorem exists_monoFam_of_point (φ : InvFun (𝓞 E)) (hR : GlobalTheory.Mum.Base R) (x : Sp R ⟶ Xo.XF c) :
    ∃ C : MonoFam Xo c φ R, C.m = 0 ∧ C.y = jK R ≫ x ∧ Nonempty (SABMap C.t Xo.univ.t (x ≫ pullback.fst _ _)) := by
  obtain ⟨t, ⟨m⟩⟩ := GlobalTheory.TraitOrder.exists_pull (x ≫ pullback.fst _ _) Xo.univ.t
  have hCN : GlobalTheory.TorRef.IsCN R := ⟨hR.1.1, hR.1.2.2.1, hR.1.2.2.2, hR.2⟩
  have hprop : IsProper t.G.hom := MorphismProperty.of_isPullback (P := @IsProper) m.cart.1 Xo.univ.proper
  obtain ⟨PP', cub, sym, adj, prim, m₂, hm₂⟩ := sabPull Out.CubePf.cubePull (jK R) t
  obtain ⟨m₃⟩ := GlobalTheory.TraitOrder.comp (h := (jK R ≫ x) ≫ pullback.fst _ _) (Category.assoc _ _ _).symm m m₂
  have hpol : GlobalTheory.LN.PolAt t (jK R) := by
    have h₂ : LBIso PP'.L (t.PP.L.pull m₂.φ) := m₂.lin.imp fun _ h => h.1
    rw [hm₂] at h₂
    have h₃ : LBIso PP'.L (Xo.univ.t.PP.L.pull m₃.φ) := m₃.lin.imp fun _ h => h.1
    have hL := LB.isLB_pull t.PP.isLB (pullback.fst t.G.hom (jK R))
    exact ⟨inferInstanceAs (IsProper (pullback.snd _ _)), amplePt _ _ _ _ _ m₃.φ m₃.cart _ _ Xo.univ.t.PP.isLB hL
      (LBIso.trans hL PP'.isLB (LB.isLB_pull Xo.univ.t.PP.isLB _) h₂.symm h₃) Xo.univ.ample Xo.univ.ktriv⟩
  have hPI : PushInvertible Xo.univ.t.G Xo.univ.t.PP.L :=
    GlobalTheory.PushInv.pushInvertible_any GlobalTheory.allSixLaws.2.1.secBaseChangeAny GlobalTheory.allSixLaws.1.globalSectionsRank _ (GlobalTheory.Obj.toPolAV Xo.univ)
  obtain ⟨P, -, hX⟩ := GlobalTheory.GenFan.exists_pelUnif_torsionIso_subsingleton_of_abLocus R t hCN hpol
    (GlobalTheory.ThetaLocal.thetaNZ_of_pushInvertible E H _ Xo.univ.t hPI R _ t m) (fun p K _ _ q _ => inferInstance)
  obtain ⟨b, hb⟩ := Spec.map_surjective (x ≫ pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
  let F : Fam Xo c R := ⟨b.hom, t, P, jK R ≫ x, by rw [Category.assoc, ← hb]; rfl, _, ⟨m₂⟩, ⟨m₃⟩⟩
  refine ⟨⟨F, 0, Fin.elim0, fun i => i.elim0, Fin.elim0, GlobalTheory.GenFan.isCone_empty H φ _,
    by rw [Module.finrank_zero_of_subsingleton]; exact Nat.zero_le _, fun y => ?_⟩, rfl, rfl, ⟨m⟩⟩
  obtain rfl : y = 0 := Subsingleton.elim _ _
  have := hR.2
  obtain ⟨r, hr, -, -, hu⟩ := (GlobalTheory.PsiCoordLocal.main R P.D hCN.2.1 0).1
  obtain ⟨u, rfl⟩ := hu rfl
  exact ⟨u, Fin.elim0, fun i => i.elim0, by simpa using hr⟩

theorem Fam.exists_monoFam [IsNoetherianRing R] (C : Fam Xo c R) (hφ : IsPolFan H.bar (min Dw.p Dw.q) φ) {u : R}
    (hu : u ∈ maximalIdeal R) {β : LinearMap.BilinForm ℤ C.P.D.toPre.X} (hβ : β ∈ balForms H.bar C.P.D.toPre.X)
    (h : IsMonomial C.P.D.toPre ![u] ![(l.M' : ℤ) • β]) : ∃ C' : MonoFam Xo c φ R, C'.toFam = C := by
  haveI : Module.Projective (𝓞 E) C.P.D.toPre.X := GlobalTheory.Forms.projective_of_int (𝓞 E) _
  have hM : (0 : ℤ) < l.M' := by exact_mod_cast level_pos l
  have h0 : ∀ y, 0 ≤ β y y := fun y => nonneg_of_mul_nonneg_right (h.nonneg 0 y) hM
  obtain ⟨m, δ, cf, hδ, hcf, hsum⟩ := GlobalTheory.ConeInterior.exists_pos_comb (hφ _ C.rank_le) hβ
    (toReal_mem_psdCone_of_nonneg E H _ β hβ h0)
  refine ⟨⟨C, m, fun i => u ^ cf i, fun i => Ideal.pow_mem_of_mem _ hu _ (hcf i), δ, hδ, C.rank_le, fun y => ?_⟩, rfl⟩
  obtain ⟨v, n, hn, hc⟩ := h y
  have ev : ∀ i, ∃ k : ℕ, ((l.M' : ℤ) • δ i) y y = 2 * k := fun i => by
    have h1 := apply_self_eq_two_mul ((balForms_eq_levelForms H C.P.D.toPre.X).le (hδ.mem i)) y
    have h2 := hδ.nonneg i y
    obtain ⟨k, hk⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ δ i y (H.w0 • y) by omega)
    exact ⟨l.M' * k, by rw [LinearMap.smul_apply, LinearMap.smul_apply, h1, hk]; push_cast; simp; ring⟩
  choose k hk using ev
  have e : n 0 = ∑ i, cf i * k i := by
    have h1 : ((l.M' : ℤ) • β) y y = 2 * n 0 := hn 0
    have h2 : ((l.M' : ℤ) • β) y y = ∑ i, cf i * ((l.M' : ℤ) • δ i) y y := by
      simp only [hsum, LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul, nsmul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp only [hk] at h2
    have : (2 : ℤ) * n 0 = 2 * ((∑ i, cf i * k i : ℕ) : ℤ) := by
      rw [← h1, h2]; push_cast; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    omega
  refine ⟨v, k, hk, ?_⟩
  simpa only [Fin.prod_univ_one, Matrix.cons_val_zero, e, ← pow_mul, Finset.prod_pow_eq_pow_sum] using hc

theorem exists_monoFam_nontrivial : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (H : Host E) (Dw : Datum H)
    (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)) (C : MonoFam Xo c φ (PowerSeries ℂ)),
    IsPolFan H.bar (min Dw.p Dw.q) φ ∧ NoSelfInt H.bar (min Dw.p Dw.q) φ ∧ GlobalTheory.Mum.Base (PowerSeries ℂ) ∧
      Nontrivial C.P.D.toPre.X ∧ 1 ≤ C.m := by
  obtain ⟨E, i₁, i₂, i₃, H, D, l, Xo, c, W₀, Y, bF, -, -, a, χ, w, -, -, -, -, -, -, hs, -, hab, -⟩ :=
    GlobalTheory.ArcWitness.exists_arcWit GlobalTheory.partI_closed
  haveI : CharZero (PowerSeries ℂ) := algebraRat.charZero _
  have hc : IsAdicComplete (maximalIdeal (PowerSeries ℂ)) (PowerSeries ℂ) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; infer_instance
  rw [← PowerSeries.maximalIdeal_eq_span_X] at w
  obtain ⟨φ, hφ, hns, -⟩ := GlobalTheory.CompanionTheory.Ar.Fan.exists_fan E H (min D.p D.q)
  let b : c.F →+* PowerSeries ℂ := (PowerSeries.C (R := ℂ)).comp bF
  have hq : (jK _ ≫ χ) ≫ Y.s = (jK _ ≫ spMap b) ≫ spMap (c.V W₀).subtype := by
    rw [Category.assoc, hs, Category.assoc]
    congr 1
    exact (Spec.map_comp _ _).symm.trans (Spec.map_comp (CommRingCat.ofHom (c.V W₀).subtype) (CommRingCat.ofHom b))
  have := Y.jQ_open
  have hr : Set.range (pullback.lift _ _ hq) ⊆ Set.range Y.jQ := by
    rintro _ ⟨p, rfl⟩
    rw [← Y.ab_gen, Set.mem_preimage, ← Scheme.Hom.comp_apply, pullback.lift_fst, Scheme.Hom.comp_apply, hab]
    intro hX
    have h1 : algebraMap (PowerSeries ℂ) (FractionRing (PowerSeries ℂ)) PowerSeries.X ∈ p.asIdeal := hX
    rw [@Ideal.eq_bot_of_prime _ _ _ p.isPrime, Ideal.mem_bot, map_eq_zero_iff _ (IsFractionRing.injective _ _)] at h1
    exact PowerSeries.X_ne_zero h1
  let y := IsOpenImmersion.lift Y.jQ _ hr
  have hy : y ≫ Y.jQ = pullback.lift _ _ hq := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨tK, ⟨n₀⟩⟩ := GlobalTheory.TraitOrder.exists_pull (jK _) w.t
  obtain ⟨n₁⟩ := GlobalTheory.TraitOrder.comp rfl w.m n₀
  obtain ⟨n₂⟩ := GlobalTheory.TraitOrder.cancel (g := y) (by rw [← Category.assoc, hy, pullback.lift_fst]) Y.m n₁
  let F : Fam Xo c (PowerSeries ℂ) := ⟨b, w.t, w.P, y, by rw [← Y.jQ_over, ← Category.assoc, hy, pullback.lift_snd],
    tK, ⟨n₀⟩, GlobalTheory.TraitOrder.comp rfl Y.m0.toSABMap n₂⟩
  obtain ⟨be, hbe, hmono, hval⟩ := GlobalTheory.ArcOrder.exists_form (PowerSeries.C_injective) w PowerSeries.X_irreducible 1 1 (by simp)
  have hM : be ∈ levelForms H l.M' w.P.D.toPre.X := ⟨hbe.1, hbe.2.1, fun y z => by
    obtain ⟨y, rfl⟩ := w.e.surjective y
    obtain ⟨z, rfl⟩ := w.e.surjective z
    rw [hval]
    exact ((Dvd.intro_left 2 rfl).trans (a.be_dvd y z)).mul_left _⟩
  obtain ⟨β, hβ, rfl⟩ := (mem_levelForms_iff_smul (level_pos l).ne').1 hM
  obtain ⟨C, hC⟩ := F.exists_monoFam hφ (u := PowerSeries.X) (by rw [PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _)
    ((balForms_eq_levelForms H _).ge hβ) hmono
  have hn : Nontrivial C.P.D.toPre.X := by
    haveI := a.nontriv
    rw [hC]
    exact w.e.injective.nontrivial
  obtain ⟨x, hx⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hx
  exact ⟨E, _, _, _, H, D, l, Xo, c, φ, C, hφ, hns, ⟨⟨inferInstance, inferInstance, inferInstance, hc⟩, inferInstance⟩, hn, i.pos⟩

section Tests

open GlobalTheory.RigChart GlobalTheory.RigChart.Model GlobalTheory.ToricData ReciprocityTheory.ChartRestriction.G.Out.InhTate

variable {V : Type} [CommRing V] [IsDomain V] {m : ℕ} {K : Type} [Field K]

theorem sepAt_rescale (Q : DegPre V) (s : Fin m → V) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (ev : V →+* K)
    (k₀ : Subfield K) (u : Fin m → Vˣ) (h : SepAt Q s gam ev k₀) : SepAt Q (fun i => u i * s i) gam ev k₀ := by
  obtain ⟨h0, B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', α, h₁, h₂, h₃, h₄, h₅, h₆, h₇⟩ := h
  refine ⟨fun i => by rw [map_mul, h0, mul_zero], B₀, _, inferInstance, M₀, c₀, B', _, π₁, π₀, w, c',
    fun i => α i * (Units.map ev.toMonoidHom (u i))⁻¹, h₁, h₂, h₃, h₄, h₅, h₆, fun a b τ₀ ⟨hg, k, hk, hv⟩ => ?_⟩
  let v : Vˣ := ∏ i, u i ^ gam i a b
  let f : Vˣ →* (FractionRing V)ˣ := Units.map (algebraMap V (FractionRing V)).toMonoidHom
  have hk' : ((k * (f v)⁻¹ : (FractionRing V)ˣ) : FractionRing V) = ∏ i, algebraMap V (FractionRing V) (s i) ^ gam i a b := by
    rw [Units.val_mul, hk, Units.val_inv_eq_inv_val, mul_inv_eq_iff_eq_mul₀ (f v).ne_zero]
    simp only [v, f, map_prod, map_zpow, Units.coe_prod, Units.val_zpow_eq_zpow_val, map_mul, mul_zpow,
      Finset.prod_mul_distrib]
    exact mul_comm _ _
  have hv' : ∀ z J, Good Q.P.L z J → val (Q.tau a b) (𝟙 _) z J =
      gm (𝟙 (TK V).left) z ⊤ (unitOn (k * (f v)⁻¹)) * val (GlobalTheory.UU.scaleGen (unitOn v) τ₀) (toUnit (TK V)).left z J := by
    intro z J hJ
    have e : gm (toUnit (TK V)).left z ⊤ (unitOn v) = gm (𝟙 (TK V).left) z ⊤ (unitOn (f v)) := by
      rw [GlobalTheory.UU.gm_top]
      exact congrArg _ (pullTop_unitOn (algebraMap V (FractionRing V)) _)
    refine (hv z J hJ).trans (Eq.symm ?_)
    refine (congrArg _ (GlobalTheory.UU.val_scaleGen _ _ _ hJ)).trans ?_
    rw [e, ← _root_.mul_assoc, ← map_mul, ← unitOn_mul, inv_mul_cancel_right]
  obtain ⟨τ₁, hτ, hval⟩ := h₇ a b (GlobalTheory.UU.scaleGen (unitOn v) τ₀) ⟨GlobalTheory.UU.scaleGen_isGen _ hg, k * (f v)⁻¹, hk', hv'⟩
  refine ⟨τ₁, hτ, fun z J J₀ hJ hJ₀ => ?_⟩
  have e := (GlobalTheory.UU.val_scaleGen _ _ _ hJ).symm.trans (hval z J J₀ hJ hJ₀)
  have e₁ : gm (spMap ev) z ⊤ (unitOn v) = gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map ev.toMonoidHom v)) := by
    rw [GlobalTheory.UU.gm_top]
    exact congrArg _ (pullTop_unitOn ev v)
  have e₂ : ∏ i, (α i * (Units.map ev.toMonoidHom (u i))⁻¹) ^ gam i a b =
      (Units.map ev.toMonoidHom v)⁻¹ * ∏ i, α i ^ gam i a b := by
    simp only [v, map_prod, map_zpow, mul_zpow, Finset.prod_mul_distrib, inv_zpow', zpow_neg, Finset.prod_inv_distrib]
    exact mul_comm _ _
  rw [e₂, unitOn_mul, unitOn_inv, map_mul, map_inv, ← e₁]
  refine (eq_inv_mul_of_mul_eq e).trans ?_
  ac_rfl

theorem exists_val_eq (k₀ : Subfield K) {Y : Scheme.{0}} {M : LB Y} {I : Type} [Fintype I] {p : I → (Sp k₀ ⟶ Y)} {n : I → ℤ}
    (τ : LB.Gen (LB.LinComb M p n)) {z : Sp K} {J : (Sp K ⟶ Y) → M.ι} (hJ : Good M z J) :
    ∃ x : k₀ˣ, val τ (spMap k₀.subtype) z J = gm (𝟙 (Sp K)) z ⊤ (unitOn (Units.map k₀.subtype.toMonoidHom x)) := by
  have : Subsingleton (Sp k₀) := inferInstanceAs (Subsingleton (PrimeSpectrum k₀))
  have ht : LB.wchart M p (fun k => J (spMap k₀.subtype ≫ p k)) = ⊤ :=
    top_unique fun q _ => Subsingleton.elim (spMap k₀.subtype z) q ▸ hJ.mem p _
  obtain ⟨x, hx⟩ := unitOn_bijective.2 (res ht.ge (τ.s fun k => J (spMap k₀.subtype ≫ p k)))
  exact ⟨x, (gm_eq_of_top _ z ht _).trans (congrArg _ (hx ▸ pullTop_unitOn k₀.subtype x))⟩

theorem one_isGen₂ {W W' Y : Scheme.{0}} (f : Y ⟶ W) (g : Y ⟶ W') :
    LB.Gen.IsGen (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull f) ((Inh.trivLB W').pull g)) := by
  intro i j
  have hg : (LB.div ((Inh.trivLB W').pull g) ((Inh.trivLB W).pull f)).g i j = 1 := by
    have h₁ := Inh.linComb_triv_g (fun _ : PUnit => f) (fun _ => 1) i.2 j.2
    have h₂ := Inh.linComb_triv_g (fun _ : PUnit => g) (fun _ => 1) i.1 j.1
    unfold LB.div
    dsimp only
    rw [h₁, h₂, map_one, map_one, inv_one, _root_.mul_one]
  rw [hg, _root_.one_mul]
  rfl

theorem exists_iso_pull_pull {B B₀ B' : Scheme.{0}} {M : LB B} (hM : M.IsLB) (β : B₀ ⟶ B) (π : B' ⟶ B₀) :
    ∃ w : LB.Iso (M.pull (π ≫ β)) ((M.pull β).pull π), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j k : PUnit → M.ι), β (π (f z)) ∈ M.U (j PUnit.unit) →
        β (π (f z)) ∈ M.U (k PUnit.unit) →
        gw w f z j k = gm (f ≫ π ≫ β) z _ (M.g (j PUnit.unit) (k PUnit.unit)) := by
  have le : ∀ p : (PUnit → PUnit → M.ι) × (PUnit → M.ι), ((M.pull β).pull π).U p.1 ⊓ (M.pull (π ≫ β)).U p.2 ≤
      (π ≫ β) ⁻¹ᵁ (M.U (p.1 PUnit.unit PUnit.unit) ⊓ M.U (p.2 PUnit.unit)) := fun p y hy =>
    ⟨(mem_pull (F := β)).1 ((mem_pull (F := π)).1 hy.1), (mem_pull (F := π ≫ β)).1 hy.2⟩
  let w : LB.Iso (M.pull (π ≫ β)) ((M.pull β).pull π) := ⟨fun p => res (le p) (pullU (π ≫ β) _ (M.g _ _))⟩
  have hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ B') (z : Z) (j k : PUnit → M.ι), β (π (f z)) ∈ M.U (j PUnit.unit) →
      β (π (f z)) ∈ M.U (k PUnit.unit) →
      gw w f z j k = gm (f ≫ π ≫ β) z _ (M.g (j PUnit.unit) (k PUnit.unit)) := fun Z f z j k hj hk =>
    (gm_res f z (le (fun _ => j, k)) ⟨mem_pull.2 (mem_pull.2 hj), mem_pull.2 hk⟩ _).trans
      (gm_pull f (π ≫ β) z (M.U (j PUnit.unit) ⊓ M.U (k PUnit.unit)) ⟨hj, hk⟩ _)
  refine ⟨w, (isGen_iff w).2 fun Z f z j j' k k' hj hj' hk hk' => ?_, hw⟩
  have a₁ := mem_pull.1 hj
  have a₂ := mem_pull.1 hj'
  have a₃ := mem_pull.1 hk
  have a₄ := mem_pull.1 hk'
  rw [hw Z f z j k a₁ a₃, hw Z f z j' k' a₂ a₄, gm_pull_g M β (f ≫ π) z j j' hj hj', gm_pull_g M (π ≫ β) f z k k' hk hk',
    Category.assoc, mul_right_comm, gm_cocycle hM (f ≫ π ≫ β) z a₁ a₂ a₄, ← gm_cocycle hM (f ≫ π ≫ β) z a₁ a₃ a₄,
    mul_inv_cancel_right]

theorem sepAt_of_range (Q : DegPre V) (s : Fin m → V) (gam : Fin m → LinearMap.BilinForm ℤ Q.X) (ev : V →+* K)
    (k₀ : Subfield K) (h0 : ∀ i, ev (s i) = 0) (h : ∀ v, ev v ∈ k₀) : SepAt Q s gam ev k₀ := by
  let e₀ : Sp k₀ ⟶ Sp V := spMap (ev.codRestrict k₀ h)
  let u : Sp K ⟶ Sp k₀ := spMap k₀.subtype
  have hu : u ≫ e₀ = spMap ev := (Spec.map_comp _ _).symm
  have hab : IsAbelianScheme ((Over.pullback e₀).obj Q.P.A) := GlobalTheory.isAbelianScheme_pullback_obj e₀ Q.P.A Q.P.isAb
  let B₀ := (Over.pullback e₀).obj Q.P.A
  let β : B₀.left ⟶ Q.P.A.left := pullback.fst _ _
  let B' := (Over.pullback u).obj B₀
  let π : B'.left ⟶ B₀.left := pullback.fst _ _
  have w₀ : ∀ a, (e₀ ≫ (Q.c a).left) ≫ Q.P.A.hom = 𝟙 _ ≫ e₀ := fun a => by
    rw [Category.assoc, Over.w (Q.c a)]; exact (Category.comp_id _).trans (Category.id_comp _).symm
  let c₀ : Q.X → (Sp k₀ ⟶ B₀.left) := fun a => pullback.lift _ _ (w₀ a)
  have c₀β : ∀ a, c₀ a ≫ β = e₀ ≫ (Q.c a).left := fun a => pullback.lift_fst _ _ _
  have w₁ : ∀ a, (u ≫ c₀ a) ≫ B₀.hom = 𝟙 _ ≫ u := fun a => by
    rw [Category.assoc, show c₀ a ≫ B₀.hom = 𝟙 _ from pullback.lift_snd _ _ _, Category.comp_id, Category.id_comp]
  let c' : Q.X → (Sp K ⟶ B'.left) := fun a => pullback.lift _ _ (w₁ a)
  have c'π : ∀ a, c' a ≫ π = u ≫ c₀ a := fun a => pullback.lift_fst _ _ _
  have c'πβ : ∀ a, c' a ≫ π ≫ β = spMap ev ≫ (Q.c a).left := fun a => by
    rw [← Category.assoc, c'π, Category.assoc, c₀β, ← Category.assoc, hu]
  obtain ⟨w, hw, hwv⟩ := exists_iso_pull_pull Q.P.isLB β π
  refine ⟨h0, B₀, inferInstance, inferInstance, Q.P.L.pull β, c₀, B', inferInstance, π ≫ β, π, w, c', 1,
    hab, LB.isLB_pull Q.P.isLB β,
    ((isGrpPullback_pullback B₀ u).comp (isGrpPullback_pullback Q.P.A e₀)).congr hu rfl, isGrpPullback_pullback B₀ u, hw,
    fun a => ⟨pullback.lift_snd _ _ _, c'πβ a, c'π a⟩, fun a b τ₀ hτ => ?_⟩
  clear_value c' c₀ π β B' B₀
  let x : Fin 4 → Q.X := ![a + b, a, b, 0]
  have hx : ∀ {T : Type} (f : Q.X → T), ![f (a + b), f a, f b, f 0] = fun k => f (x k) := fun f => by
    funext k; fin_cases k <;> rfl
  let A := chartPullLinComb Q.P.L β ![c₀ (a + b), c₀ a, c₀ b, c₀ 0]
    ![(Q.c (a + b)).left, (Q.c a).left, (Q.c b).left, (Q.c 0).left] ![-1, 1, 1, -1] e₀ (fun k => by fin_cases k <;> exact c₀β _)
  refine ⟨⟨fun i => res (A.le i) (pullU e₀ _ (τ₀.s (A.idx i)))⟩, fun i j => unit_ext fun y hy => ?_, fun z J J₀ hJ hJ₀ => ?_⟩
  · have hm := And.intro (A.le i hy.1) (A.le j hy.2)
    have e := (gm_res e₀ y _ hm _).symm.trans ((congrArg (gm e₀ y _) (hτ.1 (A.idx i) (A.idx j))).trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) rfl (gm_res e₀ y _ hm _))))
    exact ((gm_res _ y _ hy _).trans (gm_rp₁ e₀ y _ _ (A.le i) hy.1 _)).trans (e.trans ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (A.g y i j hy.1 hy.2) ((gm_res _ y _ hy _).trans (gm_rp₁ e₀ y _ _ (A.le j) hy.2 _)))).symm)
  · have m₀ := hJ₀.mem ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] u
    have m₁ := A.le _ m₀
    have m₂ : spMap ev z ∈ LB.wchart Q.P.L ![(Q.c (a + b)).left, (Q.c a).left, (Q.c b).left, (Q.c 0).left]
        (A.idx fun k => J₀ (u ≫ ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] k)) := by rw [← hu]; exact m₁
    refine (gen_trans hτ.1 (spMap ev) z (hJ.mem _ _) m₂).trans (congrArg₂ (· * ·) ?_ ?_)
    · have key : ∀ y, gw w (c' y) z (J₀ (c' y ≫ π)) (fun _ => J (c' y ≫ π ≫ β)) =
          (gm (spMap ev ≫ (Q.c y).left) z _ (Q.P.L.g (J (spMap ev ≫ (Q.c y).left)) (J₀ (u ≫ c₀ y) PUnit.unit)))⁻¹ := fun y => by
        have a₁ : (c' y ≫ π ≫ β) z ∈ Q.P.L.U (J₀ (c' y ≫ π) PUnit.unit) := (mem_pull (F := β)).1 (hJ₀ (c' y ≫ π))
        have a₂ := hJ (c' y ≫ π ≫ β)
        rw [hwv _ _ _ _ _ a₁ a₂, ← c'πβ, ← c'π, eq_inv_iff_mul_eq_one, gm_cocycle Q.P.isLB _ z a₁ a₂ a₁,
          gm_self Q.P.isLB _ z a₁]
      simp only [lamUnit, key, Pi.one_apply, one_zpow, Finset.prod_const_one, unitOn_one, map_one, _root_.mul_one, inv_inv, trF,
        Fin.prod_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, zpow_neg, zpow_one]
      rfl
    · refine Eq.trans ?_ (gm_res u z (A.le _) m₀ _).symm
      have e := gm_pull u e₀ z _ m₁ (τ₀.s (A.idx fun k => J₀ (u ≫ ![c₀ (a + b), c₀ a, c₀ b, c₀ 0] k)))
      rw [hu] at e
      exact e.symm

theorem lamUnit_one {W W' B' Z : Scheme.{0}} {π₁ : B' ⟶ W} {π₀ : B' ⟶ W'} {X : Type} [AddCommGroup X] (x : X → (Z ⟶ B'))
    (a b : X) (z : Z) (J J₀) :
    lamUnit (⟨fun _ => 1⟩ : LB.Iso ((Inh.trivLB W).pull π₁) ((Inh.trivLB W').pull π₀)) x a b z J J₀ = 1 := by
  unfold lamUnit gw
  erw [map_one, map_one, map_one, map_one]
  simp

theorem sepAt_toric_iff {X : Type} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] (q : X → (FractionRing V)ˣ)
    (s : Fin m → V) (gam : Fin m → LinearMap.BilinForm ℤ X) (ev : V →+* K) (k₀ : Subfield K) :
    SepAt (toricPre V X q) s gam ev k₀ ↔ (∀ i, ev (s i) = 0) ∧ ∃ α : Fin m → Kˣ, ∀ (a b : X) (u : Vˣ),
      (polar q a b : FractionRing V) = (∏ i, algebraMap V (FractionRing V) (s i) ^ gam i a b) * algebraMap V _ u →
      ∃ x ∈ k₀, ev u = (∏ i, (α i : K) ^ gam i a b) * x := by
  refine and_congr_right' ⟨?_, ?_⟩
  · rintro ⟨B₀, _, _, M₀, c₀, B', _, π₁, π₀, w, c', α, -, h₂, h₃, -, -, hc, h⟩
    have : IsIso B'.hom := by
      have : IsIso (toricPre V X q).P.A.hom := by show IsIso (𝟙 _); infer_instance
      exact h₃.1.isIso_snd_of_isIso
    have hc' : ∀ y, c' y = inv B'.hom := fun y => by
      rw [← cancel_mono B'.hom, (hc y).1, IsIso.inv_hom_id]
    obtain rfl : c' = fun _ => inv B'.hom := funext hc'
    refine ⟨α, fun a b u hq => ?_⟩
    have hu := cg_isConst (K := Fin 4) ![((toricPre V X q).c (a + b)).left, ((toricPre V X q).c a).left,
      ((toricPre V X q).c b).left, ((toricPre V X q).c 0).left] ![-1, 1, 1, -1] (unitOn u)
    obtain ⟨τ₁, -, hτ⟩ := h a b _ ((isUnitTau_iff q s gam a b _).2 ⟨u, hu, hq⟩)
    have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
    let z : Sp K := (default : PrimeSpectrum K)
    obtain ⟨J₀, hJ₀, -⟩ := exists_good M₀ h₂ z (K := Empty) Empty.elim Empty.elim (fun a => a.elim) (fun a => a.elim)
    obtain ⟨x, hx⟩ := exists_val_eq k₀ τ₁ hJ₀
    have e : unitOn (Units.map ev.toMonoidHom u) = unitOn ((∏ i, α i ^ gam i a b) * Units.map k₀.subtype.toMonoidHom x) := by
      refine unit_ext fun z' _ => ?_
      obtain rfl : z = z' := Subsingleton.elim _ _
      have h1 := (val_const hu (spMap ev) z (fun _ => PUnit.unit)).symm.trans (hτ z (fun _ => PUnit.unit) J₀ (good_triv z) hJ₀)
      rw [hx, pullTop_unitOn] at h1
      unfold lamUnit at h1
      beta_reduce at h1
      rw [mul_inv_cancel, _root_.one_mul, inv_mul_cancel, _root_.one_mul] at h1
      rw [unitOn_mul, map_mul]
      exact h1
    exact ⟨x, x.1.2, by simpa using congrArg Units.val (unitOn_inj.1 e)⟩
  · rintro ⟨α, h⟩
    have pb : ∀ {S T : Scheme.{0}} (f : S ⟶ T), IsGrpPullback (𝟙_ (Over S)) (𝟙_ (Over T)) f f := fun f =>
      ⟨IsPullback.of_vert_isIso (fst := f) (snd := 𝟙 _) (f := 𝟙 _) (g := f) ⟨by simp⟩, fun T x y x₀ y₀ hx _ => by
        rw [toUnit_unique (x₀ * y₀) x₀, toUnit_unique (x * y) x, hx]⟩
    have hc : ∀ y, ((toricPre V X q).c y).left = 𝟙 (Sp V) := fun y =>
      congrArg (·.left) (toUnit_unique ((toricPre V X q).c y) (𝟙 (𝟙_ (Over (Sp V)))))
    refine ⟨(Inh.zeroPolAV (Sp k₀)).A, inferInstance, inferInstance, (Inh.zeroPolAV (Sp k₀)).L, fun _ => 𝟙 _, 𝟙_ _, inferInstance,
      spMap ev, spMap k₀.subtype, ⟨fun _ => 1⟩, fun _ => 𝟙 _, α, (Inh.zeroPolAV (Sp k₀)).isAb, (Inh.zeroPolAV (Sp k₀)).isLB,
      pb _, pb _, one_isGen₂ _ _, fun y => ⟨Category.id_comp _, ?_, ?_⟩, fun a b τ₀ hτ => ?_⟩
    · exact (Category.id_comp _).trans ((Category.comp_id _).symm.trans (congrArg _ (hc y).symm))
    · exact (Category.id_comp _).trans (Category.comp_id _).symm
    · obtain ⟨u, hu, hq⟩ := (isUnitTau_iff q s gam a b _).1 hτ
      obtain ⟨x, hx, e⟩ := h a b u hq
      have hx0 : (⟨x, hx⟩ : k₀) ≠ 0 := fun h0 => by
        obtain rfl : x = 0 := congrArg Subtype.val h0
        exact (u.isUnit.map ev).ne_zero (by rw [e, mul_zero])
      refine ⟨cg _ _ (unitOn (Units.mk0 _ hx0)), cg_isGen _ _ _, fun z J J₀ _ _ => ?_⟩
      have e' : Units.map ev.toMonoidHom u = (∏ i, α i ^ gam i a b) * Units.map k₀.subtype.toMonoidHom (Units.mk0 _ hx0) := by
        ext1; simpa using e
      refine (val_const hu _ z J).trans (Eq.trans ?_ (congrArg₂ (· * ·) rfl (val_const (cg_isConst _ _ _) _ z J₀).symm))
      erw [lamUnit_one, _root_.one_mul]
      erw [pullTop_unitOn, pullTop_unitOn]
      rw [e', unitOn_mul _ (Units.map _ _), map_mul]
      rfl

theorem sepAt_per_iff (v : Aˣ) (b : ℤ × ℤ → ℤ) (ev : A →+* K) (k₀ : Subfield K) :
    SepAt (toricPre A (ℤ × ℤ) (per v b)) ![tt] ![frm] ev k₀ ↔ ev tt = 0 ∧ ∃ α : Kˣ, ∀ y z : ℤ × ℤ,
      ∃ x ∈ k₀, ev (v ^ (b (y + z) - b y - b z) : Aˣ) = (α : K) ^ frm y z * x := by
  refine (sepAt_toric_iff (per v b) ![tt] ![frm] ev k₀).trans (and_congr (by simp) ⟨fun ⟨α, h⟩ => ⟨α 0, fun y z => ?_⟩,
    fun ⟨α, h⟩ => ⟨![α], fun y z u hq => ?_⟩⟩)
  · simpa using h y z (v ^ (b (y + z) - b y - b z)) (by simpa using polar_per v b y z)
  · have ht : algebraMap A (FractionRing A) tt ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective A _)).2 PowerSeries.X_ne_zero
    rw [polar_per, Fin.prod_univ_one] at hq
    have hu := IsFractionRing.injective A (FractionRing A) (mul_left_cancel₀ (zpow_ne_zero _ ht) hq)
    rw [← hu]
    simpa using h y z

theorem sepAt_mixed_iff (ev : A →+* K) (k₀ : Subfield K) :
    SepAt (toricPre A (ℤ × ℤ) (per vs fun y => y.1 * y.2)) ![tt] ![frm] ev k₀ ↔ ev tt = 0 ∧ ev ss ∈ k₀ := by
  have hv : ev vs = 1 + ev ss := by simp [vs]
  have hz : ∀ n : ℤ, ev (vs ^ n : Aˣ) = ev vs ^ n := fun n =>
    (congrArg Units.val (map_zpow (Units.map ev.toMonoidHom) vs n)).trans (Units.val_zpow_eq_zpow_val _ _)
  refine (sepAt_per_iff _ _ ev k₀).trans (and_congr_right' ⟨fun ⟨α, h⟩ => ?_, fun h => ⟨1, fun y z => ⟨_, ?_, by rw [Units.val_one, one_zpow, _root_.one_mul]⟩⟩⟩)
  · obtain ⟨x, hx, e⟩ := h (1, 0) (0, 1)
    have : ev ss = x - 1 := by
      rw [eq_sub_iff_add_eq', ← hv]
      simpa [frm] using e
    exact this ▸ k₀.sub_mem hx k₀.one_mem
  · rw [hz, hv]
    exact k₀.zpow_mem (k₀.add_mem k₀.one_mem h) _

theorem sepAt_cone_iff (ev : A →+* K) (k₀ : Subfield K) :
    SepAt (toricPre A (ℤ × ℤ) (per vs fun y => nrm y)) ![tt] ![frm] ev k₀ ↔ ev tt = 0 := by
  refine (sepAt_per_iff _ _ ev k₀).trans (and_iff_left ⟨Units.map ev.toMonoidHom vs, fun y z => ⟨1, k₀.one_mem, ?_⟩⟩)
  have e : frm y z = nrm (y + z) - nrm y - nrm z := by
    simp only [nrm_cast, frm, LinearMap.mk₂_apply, Prod.fst_add, Prod.snd_add]; ring
  rw [_root_.mul_one, e]
  exact (congrArg Units.val (map_zpow (Units.map ev.toMonoidHom) vs _)).trans (Units.val_zpow_eq_zpow_val _ _)

end Tests

end GlobalTheory.UChart
