import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenOfIsoRel
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMember
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GsAppTopOfSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GmSpMapUnitOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaNonvanishTorsion
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIntegralSectionUnitAt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep.Coef.Idx

open GlobalTheory.Poinc.Sep.Coef (om exists_transport)

section Galois

variable {Jx V₁ W₀ K : Type} [CommRing V₁] [CommRing W₀] [Field K] {A : Over (Sp V₁)} [GrpObj A] {B₀ : Over (Sp W₀)}
  [GrpObj B₀] (f : W₀ →+* V₁) (q : Jx → (A.left ⟶ B₀.left))

def PowPts : Prop := ∀ (T : Over (Sp V₁)) (g : T.left ⟶ Sp W₀), T.hom ≫ spMap f = g →
  ∃ Φ : (T ⟶ A) ≃* (Jx → (Over.mk g ⟶ B₀)), ∀ x a, (Φ x a).left = x.left ≫ q a

variable (ev : V₁ →+* K) (k₀ : Subfield K)

def IsConj (σ : K ≃+* K) (σt : (Over.mk (spMap ev) ⊗ A).left ⟶ (Over.mk (spMap ev) ⊗ A).left) : Prop :=
  σt ≫ (fst (Over.mk (spMap ev)) A).left = (fst (Over.mk (spMap ev)) A).left ≫ spMap σ.toRingHom ∧
    ∀ a, σt ≫ (snd (Over.mk (spMap ev)) A).left ≫ q a = (snd (Over.mk (spMap ev)) A).left ≫ q a

def RatM (ψ : (Over.mk (spMap ev) ⊗ A).left ⟶ A.left) : Prop :=
  ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∀ σt, IsConj q ev σ σt → ∀ a, σt ≫ ψ ≫ q a = ψ ≫ q a

def RatP (x : Sp K ⟶ A.left) : Prop := ∀ a, DefOver k₀ (x ≫ q a)

variable {f q ev k₀}

theorem exists_conj (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt, IsConj q ev σ σt ∧ ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ A).left,
      x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ → RatP q k₀ (x ≫ (snd (Over.mk (spMap ev)) A).left) →
        x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E A).left with hfK
  set s := (snd E A).left with hs
  have hw : s ≫ A.hom = fK ≫ spMap ev := (Over.w (snd E A)).trans (Over.w (fst E A)).symm
  have hf : ∀ a, (ev.comp f) a ∈ k₀ := hk
  have h2 : spMap ev ≫ spMap f = spMap (ev.comp f) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ₀, hΦ₀⟩ := hP (Over.mk (fK ≫ spMap ev)) (fK ≫ spMap (ev.comp f)) (by
    show (fK ≫ spMap ev) ≫ spMap f = _
    rw [Category.assoc, h2])
  obtain ⟨Φ₁, hΦ₁⟩ := hP (Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev)) (fK ≫ spMap (ev.comp f)) (by
    show (fK ≫ spMap σ.toRingHom ≫ spMap ev) ≫ spMap f = _
    rw [Category.assoc, Category.assoc, h2, spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ A := Over.homMk s hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ A).left ⟶ (E ⊗ A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ s = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : ∀ a, σt ≫ s ≫ q a = s ≫ q a := by
    intro a
    rw [reassoc_of% hsnd, ← hΦ₁ σD a, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, ⟨hfst, hproj⟩, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ A).hom = fK ≫ spMap ev := (Over.w (fst E A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := hP T (spMap (ev.comp f)) (by
        show (spMap σ.toRingHom ≫ spMap ev) ≫ spMap f = _
        rw [Category.assoc, h2, spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      funext a
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show ((x ≫ σt) ≫ s) ≫ q a = ((spMap σ.toRingHom ≫ x) ≫ s) ≫ q a
      obtain ⟨P₀, hP₀⟩ := hdef a
      simp only [Category.assoc] at hP₀ ⊢
      rw [hproj, ← hP₀, ← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem ratM_snd : RatM q ev k₀ (snd (Over.mk (spMap ev)) A).left := fun _ _ _ h => h.2

theorem ratM_const (x : Over.mk (spMap ev) ⟶ A) (hx : RatP q k₀ x.left) :
    RatM q ev k₀ (fst (Over.mk (spMap ev)) A ≫ x).left := fun σ hσ σt h a => by
  obtain ⟨P₀, hP₀⟩ := hx a
  show σt ≫ ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a = ((fst (Over.mk (spMap ev)) A).left ≫ x.left) ≫ q a
  simp only [Category.assoc]
  rw [reassoc_of% h.1]
  erw [← hP₀]
  congr 1
  rw [← Category.assoc, spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]

theorem ratM_mul (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) {x y : Over.mk (spMap ev) ⊗ A ⟶ A}
    (hx : RatM q ev k₀ x.left) (hy : RatM q ev k₀ y.left) : RatM q ev k₀ (x * y).left := fun σ hσ σt h a => by
  have hf : ∀ a, (ev.comp f) a ∈ k₀ := hk
  have h2 : spMap ev ≫ spMap f = spMap (ev.comp f) := by
    simp only [spMap, ← Spec.map_comp]; rfl
  obtain ⟨Φ, hΦ⟩ := hP (Over.mk (spMap ev) ⊗ A) ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) (by
    rw [← h2, ← Category.assoc]
    exact congrArg (· ≫ spMap f) (Over.w (fst (Over.mk (spMap ev)) A)).symm)
  let τ : Over.mk ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) ⟶
      Over.mk ((fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)) := Over.homMk σt (by
    show σt ≫ (fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f) = (fst (Over.mk (spMap ev)) A).left ≫ spMap (ev.comp f)
    rw [reassoc_of% h.1]
    erw [spMap_conj k₀ _ hf σ hσ])
  have e : ∀ {x : Over.mk (spMap ev) ⊗ A ⟶ A}, RatM q ev k₀ x.left → τ ≫ Φ x a = Φ x a := fun {x} hx =>
    Over.OverMorphism.ext (by
      show σt ≫ (Φ x a).left = _
      rw [hΦ]; exact hx σ hσ σt h a)
  rw [← hΦ]
  show (τ ≫ Φ (x * y) a).left = _
  rw [map_mul, Pi.mul_apply, MonObj.comp_mul, e hx, e hy]

theorem ratP_mul (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) {x y : Over.mk (spMap ev) ⟶ A}
    (hx : RatP q k₀ x.left) (hy : RatP q k₀ y.left) : RatP q k₀ (x * y).left := fun a => by
  obtain ⟨Φ, hΦ⟩ := hP (Over.mk (spMap ev)) _ rfl
  erw [← hΦ]
  rw [map_mul, Pi.mul_apply]
  refine defOver_comp k₀ (P := (lift (Φ x a) (Φ y a)).left) (defOver_pullback k₀ ?_ ?_) (μ[B₀]).left
  · have e : (lift (Φ x a) (Φ y a)).left ≫ (fst B₀ B₀).left = x.left ≫ q a :=
      (congrArg (fun m => m.left) (lift_fst (Φ x a) (Φ y a))).trans (hΦ x a)
    exact e ▸ hx a
  · have e : (lift (Φ x a) (Φ y a)).left ≫ (snd B₀ B₀).left = y.left ≫ q a :=
      (congrArg (fun m => m.left) (lift_snd (Φ x a) (Φ y a))).trans (hΦ y a)
    exact e ▸ hy a

theorem ratM_one (h1 : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ A).left) :
    RatM q ev k₀ (1 : Over.mk (spMap ev) ⊗ A ⟶ A).left := by
  have := ratM_const 1 h1
  rwa [MonObj.comp_one] at this

variable {L : LB A.left} {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (A.left ⟶ X₂)} {e : I → ℤ}

theorem galois_sec [IsAlgClosed K] (hk₀ : IsAlgClosed k₀) (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) (hL : L.IsLB)
    (hL₂ : L₂.IsLB) (u : LB.Iso L (LB.LinComb L₂ π e)) (hu : u.IsGen)
    (hπ : ∀ (Z : Scheme.{0}) (x y : Z ⟶ A.left), (∀ a, x ≫ q a = y ≫ q a) → ∀ i, x ≫ π i = y ≫ π i)
    {Ix : Type} [Fintype Ix] (φ : Ix → ((Over.mk (spMap ev) ⊗ A).left ⟶ A.left)) (ε : Ix → ℤ)
    (hφ : ∀ k, RatM q ev k₀ (φ k)) (s : LB.Sec (LB.LinComb L φ ε))
    (h1 : ∀ t : LB.Sec (LB.LinComb L φ ε), ∃ c : K, ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ A).left,
      x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ → ∀ z J, Good L z J → sval t x z J = toStk z c * sval s x z J) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ p : Over.mk (spMap ev) ⟶ A, RatP q k₀ p.left → ∀ (z : Sp K) J J₂, Good L z J → Good L₂ z J₂ →
      ∃ c ∈ k₀, (∏ k, om (Z := Sp K) u z J J₂ ((lift (𝟙 _) p).left ≫ φ k) ^ ε k).val *
        sval (Z := Sp K) s (lift (𝟙 _) p).left z J = toStk z (κ * c) := by
  obtain ⟨U, hU, vU⟩ := exists_transport u hu φ ε
  have hA := DVR.linComb_isLB L hL φ ε
  have hB := DVR.linComb_isLB L₂ hL₂ (fun p : Ix × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2)
  obtain ⟨s', hs'⟩ := DVR.FlatBC.exists_isoRel hA hB hU s
  obtain ⟨κ, hκ, hval⟩ := galois_values k₀ hk₀ _ _ s' (fun x => x ≫ (fst (Over.mk (spMap ev)) A).left = 𝟙 _ ∧
      RatP q k₀ (x ≫ (snd (Over.mk (spMap ev)) A).left))
    (fun t' => by
      obtain ⟨t, ht⟩ := GlobalTheory.MBLow.lbIso_sec_onto _ _ _ U hA hB hU t'
      obtain ⟨c, hc⟩ := h1 t
      refine ⟨c, fun x hx z J₂ hJ₂ => ?_⟩
      choose J hJ using fun χ : Sp K ⟶ A.left => exists_chart hL (χ z)
      rw [vU t t' (fun i k => ht (i, k)) _ x z J J₂ hJ hJ₂, vU s s' hs' _ x z J J₂ hJ hJ₂, hc x hx.1 z J hJ]
      exact mul_left_comm _ _ _)
    (fun σ hσ => by
      obtain ⟨σt, hc, hfix⟩ := exists_conj hP hk σ hσ
      refine ⟨σt, fun p => ?_, fun x hx => hfix x hx.1 hx.2⟩
      rw [← Category.assoc]
      exact hπ _ _ _ (fun a => (Category.assoc _ _ _).trans (hφ p.1 σ hσ σt hc a)) p.2)
  refine ⟨κ, hκ, fun p hp z J J₂ hJ hJ₂ => ?_⟩
  obtain ⟨c, hc, he⟩ := hval (lift (𝟙 _) p).left ⟨congrArg (fun m => m.left) (lift_fst (𝟙 _) p), by
    have e : (lift (𝟙 _) p).left ≫ (snd (Over.mk (spMap ev)) A).left = p.left :=
      congrArg (fun m => m.left) (lift_snd (𝟙 _) p)
    exact e ▸ hp⟩ z J₂ hJ₂
  exact ⟨c, hc, (vU s s' hs' _ _ z J J₂ hJ hJ₂).symm.trans he⟩

end Galois

section Normalised

open GlobalTheory.UT

variable {Jx V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Jx → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}

structure Desc (f : W₀ →+* V₁) (q : Jx → (D.P.A.left ⟶ B₀.left)) (ev : V₁ →+* K) (k₀ : Subfield K)
    (u : LB.Iso D.P.L (LB.LinComb L₂ π e)) : Prop where
  hk₀ : IsAlgClosed k₀
  hP : PowPts f q
  hk : ∀ a, ev (f a) ∈ k₀
  hL₂ : L₂.IsLB
  hu : u.IsGen
  hπ : ∀ (Z : Scheme.{0}) (x y : Z ⟶ D.P.A.left), (∀ a, x ≫ q a = y ≫ q a) → ∀ i, x ≫ π i = y ≫ π i
  one : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ D.P.A).left

variable {u : LB.Iso D.P.L (LB.LinComb L₂ π e)}

theorem galois_gen (H : Desc f q ev k₀ u) {P v} (G : SymFrame.GRep D.P.L (Over.mk (spMap ev) ⊗ D.P.A) P v)
    {Ix : Type} [Fintype Ix] (φ : Ix → ((Over.mk (spMap ev) ⊗ D.P.A).left ⟶ D.P.A.left)) (ε : Ix → ℤ)
    (hφ : ∀ k, RatM q ev k₀ (φ k))
    (hP : ∀ (U : Type) [CommGroup U] (h : _ → U), P U h = ∏ k, h (φ k) ^ ε k)
    (h₀ : ∀ (U : Type) [CommGroup U] (h : (Sp K ⟶ D.P.A.left) → U),
      P U (fun ψ => h ((lift (𝟙 (Over.mk (spMap ev))) (1 : _ ⟶ D.P.A)).left ≫ ψ)) = 1)
    (h₁ : ∀ z J, Good D.P.L z J → v (Over.mk (spMap ev)) (lift (𝟙 _) 1) z J = 1)
    (p : Over.mk (spMap ev) ⟶ D.P.A) (hp : RatP q k₀ p.left) (z : Sp K) (J J₂) (hJ : Good D.P.L z J) (hJ₂ : Good L₂ z J₂) :
    ∃ c ∈ k₀, (P _ (fun ψ => om (Z := Sp K) u z J J₂ ((lift (𝟙 _) p).left ≫ ψ)) *
      @id ((Sp K).presheaf.stalk z)ˣ (v (Over.mk (spMap ev)) (lift (𝟙 _) p) z J)).val = toStk z c := by
  obtain ⟨t, ht, vt⟩ := G.out D.P.isLB φ ε hP
  obtain ⟨κ, hκ, hval⟩ := galois_sec H.hk₀ H.hP H.hk D.P.isLB H.hL₂ u H.hu H.hπ φ ε hφ (genSec t ht) (fun s => by
    obtain ⟨w, hw⟩ := exists_sec D.P.isLB (K' := PEmpty) (φ' := PEmpty.elim) (ε' := PEmpty.elim)
      (fun U _ hh => by simp [Fintype.prod_sum_type, ← Finset.prod_mul_distrib])
      (pullMulSec s (𝟙 _) (LB.invGen D.P.L _ _ t) (DVR.invGen_isGen _ _ _ _ ht))
    have le : (⊤ : (Over.mk (spMap ev) ⊗ D.P.A).left.Opens) ≤
        LB.wchart D.P.L (K := PEmpty) (Y := (Over.mk (spMap ev) ⊗ D.P.A).left) PEmpty.elim PEmpty.elim :=
      fun _ _ => Set.mem_iInter.2 fun k => k.elim
    obtain ⟨a, ha⟩ := surj_fst GlobalTheory.abelianSchemeLaws_all.1.globalFns D.P.isAb (Over.mk (spMap ev))
      (((Over.mk (spMap ev) ⊗ D.P.A).left.presheaf.map (homOfLE le).op).hom (w.f PEmpty.elim))
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom a, fun x hx z J hJ => ?_⟩
    have e₁ := hw _ x z J hJ
    rw [sval_pullMulSec _ _ _ _ _ z hJ, Category.comp_id, val_inv, sval_of w _ z J PEmpty.elim (fun k => k.elim)] at e₁
    rw [sval_genSec _ _ _ z hJ, ← gs_appTop_of_section x _ hx z a]
    erw [ha]
    refine Eq.trans ?_ (congrArg (· * _) ((gs_res x z le trivial _).trans e₁).symm)
    rw [_root_.mul_assoc, Units.inv_mul, _root_.mul_one])
  obtain ⟨c₀, hc₀, e₀⟩ := hval 1 H.one z J J₂ hJ hJ₂
  obtain ⟨c, hc, e₁⟩ := hval p hp z J J₂ hJ hJ₂
  rw [sval_genSec _ _ _ z hJ] at e₀ e₁
  have a₀ := (hP _ (fun ψ => om (Z := Sp K) u z J J₂ ((lift (𝟙 (Over.mk (spMap ev))) (1 : _ ⟶ D.P.A)).left ≫ ψ))).symm.trans
    (h₀ _ (om (Z := Sp K) u z J J₂))
  have b₀ := (vt _ (lift (𝟙 _) 1) z J hJ).trans (h₁ z J hJ)
  erw [a₀, b₀] at e₀
  have k1 : κ * c₀ = 1 := (toStk z).injective (by rw [← e₀, map_one]; exact _root_.mul_one _)
  refine ⟨κ * c, k₀.mul_mem (eq_inv_of_mul_eq_one_left k1 ▸ k₀.inv_mem hc₀) hc, ?_⟩
  rw [← e₁, hP, Units.val_mul]
  exact congrArg₂ (· * ·) rfl (congrArg Units.val (vt _ (lift (𝟙 _) p) z J hJ).symm)

theorem cub_mem (H : Desc f q ev k₀ u) (x x' y : Over.mk (spMap ev) ⟶ D.P.A) (hx : RatP q k₀ x.left)
    (hx' : RatP q k₀ x'.left) (hy : RatP q k₀ y.left) (z : Sp K) (J J₂) (hJ : Good D.P.L z J) (hJ₂ : Good L₂ z J₂) :
    ∃ c ∈ k₀, ((om (Z := Sp K) u z J J₂ (x * x' * y).left * (om (Z := Sp K) u z J J₂ (x * x').left)⁻¹ *
      (om (Z := Sp K) u z J J₂ (x * y).left)⁻¹ * (om (Z := Sp K) u z J J₂ (x' * y).left)⁻¹ *
      om (Z := Sp K) u z J J₂ x.left * om (Z := Sp K) u z J J₂ x'.left * om (Z := Sp K) u z J J₂ y.left *
      (om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left)⁻¹) *
      @id ((Sp K).presheaf.stalk z)ˣ (cubV D.cub (T := Over.mk (spMap ev)) z J x x' y)).val = toStk z c := by
  have r₁ := ratM_const x hx
  have r₂ := ratM_const x' hx'
  have r₃ : RatM q ev k₀ _ := ratM_snd
  have m := fun {a b} => ratM_mul (x := a) (y := b) H.hP H.hk
  have key := galois_gen H (SymFrame.grep_cub (D := D) (fst (Over.mk (spMap ev)) D.P.A ≫ x) (fst _ _ ≫ x') (snd _ _))
    ![((fst (Over.mk (spMap ev)) D.P.A ≫ x) * (fst _ _ ≫ x') * snd _ _).left,
      ((fst (Over.mk (spMap ev)) D.P.A ≫ x) * (fst _ _ ≫ x')).left, ((fst (Over.mk (spMap ev)) D.P.A ≫ x) * snd _ _).left,
      ((fst (Over.mk (spMap ev)) D.P.A ≫ x') * snd _ _).left, (fst (Over.mk (spMap ev)) D.P.A ≫ x).left,
      (fst (Over.mk (spMap ev)) D.P.A ≫ x').left, (snd (Over.mk (spMap ev)) D.P.A).left,
      (1 : Over.mk (spMap ev) ⊗ D.P.A ⟶ D.P.A).left] ![1, -1, -1, -1, 1, 1, 1, -1]
    (fun k => by
      fin_cases k
      exacts [m (m r₁ r₂) r₃, m r₁ r₂, m r₁ r₃, m r₂ r₃, r₁, r₂, r₃, ratM_one H.one])
    (fun U _ h => by simp [Fin.prod_univ_eight])
    (fun U _ h => by
      simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp,
        _root_.mul_one, _root_.one_mul]
      simp)
    (fun z J hJ => by
      simp only [lift_snd]
      exact (isCub_cubV D.cub hJ).face₃ _ _) y hy z J J₂ hJ hJ₂
  simp only [← Over.comp_left, MonObj.comp_mul, MonObj.comp_one, lift_fst_assoc, lift_snd, Category.id_comp] at key
  exact key

end Normalised

end GlobalTheory.Poinc.Sep.Coef.Idx
