import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SharpBundleFibre
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValMemOfCorrPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueScalar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefOverOfFiniteOrbit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFromBase
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FlatBCSec
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.SectionArithmetic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LbIsoSecOnto
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsNormalizedBoth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Poinc.Sep

def chartPullComp {X Y Y' : Scheme.{0}} (L : LB X) {Ix : Type} [Fintype Ix] (φ : Ix → (Y ⟶ X)) (ε : Ix → ℤ)
    (h : Y' ⟶ Y) : ChartPull (LB.LinComb L (fun k => h ≫ φ k) ε) (LB.LinComb L φ ε) h where
  idx j := j
  le j _ hy := Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy k
  g y j j' hj hj' := by
    refine (gm_linComb L (fun k => h ≫ φ k) ε (𝟙 Y') y j j' hj hj').trans ?_
    refine Eq.trans ?_ (gm_linComb L φ ε h y j j' (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj k)
      (Set.mem_iInter.2 fun k => Set.mem_iInter.1 hj' k)).symm
    simp only [Category.id_comp]

theorem sval_spMap {K : Type} [Field K] {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ : Ix → (Y ⟶ X)}
    {ε : Ix → ℤ} (s : LB.Sec (LB.LinComb L φ ε)) (σ : K →+* K) (x : Sp K ⟶ Y) (z : Sp K) {J : (Sp K ⟶ X) → L.ι}
    (hJ : Good L z J) (hφ : ∀ k, spMap σ ≫ x ≫ φ k = x ≫ φ k) :
    sval s (spMap σ ≫ x) z J = toStk z (σ (valF x (LB.wchart L φ (fun k => J (x ≫ φ k))) (s.f (fun k => J (x ≫ φ k))))) := by
  have hj : ∀ k, J ((spMap σ ≫ x) ≫ φ k) = (fun k => J (x ≫ φ k)) k := fun k => by
    simp only [Category.assoc, hφ k]
  rw [sval_of s (spMap σ ≫ x) z J _ hj]
  have hm : x z ∈ LB.wchart L φ (fun k => J (x ≫ φ k)) := hJ.mem φ x
  have hm' : (spMap σ ≫ x) z ∈ LB.wchart L φ (fun k => J (x ≫ φ k)) := by
    have := hJ.mem φ (spMap σ ≫ x)
    have e : (fun k => J ((spMap σ ≫ x) ≫ φ k)) = fun k => J (x ≫ φ k) := funext hj
    rw [e] at this
    exact this
  refine (toStk_valF_gs (spMap σ ≫ x) _ z hm' _).symm.trans ?_
  exact congrArg (toStk z) (valF_spMap_comp σ x _ ((top_le_iff_mem x _ z).2 hm) _)

theorem sval_cast {X Y Z : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] {φ φ' : Ix → (Y ⟶ X)} {ε : Ix → ℤ}
    (e : φ' = φ) (p : LB.Sec (LB.LinComb L φ' ε)) (x : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → L.ι) :
    sval (e ▸ p : LB.Sec (LB.LinComb L φ ε)) x z J = sval p x z J := by
  subst e; rfl

theorem galois_values {K : Type} [Field K] [IsAlgClosed K] (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    {X Y : Scheme.{0}} {L : LB X} {Ix : Type} [Fintype Ix] (φ : Ix → (Y ⟶ X)) (ε : Ix → ℤ)
    (s : LB.Sec (LB.LinComb L φ ε)) (R : (Sp K ⟶ Y) → Prop)
    (h1 : ∀ t : LB.Sec (LB.LinComb L φ ε), ∃ c : K, ∀ x, R x → ∀ z J, Good L z J →
      sval t x z J = toStk z c * sval s x z J)
    (h2 : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ σt : Y ⟶ Y, (∀ k, σt ≫ φ k = φ k) ∧
      ∀ x, R x → x ≫ σt = spMap σ.toRingHom ≫ x) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ x, R x → ∀ z J, Good L z J → ∃ c ∈ k₀, sval s x z J = toStk z (κ * c) := by
  classical
  let v : (Sp K ⟶ Y) → ((Sp K ⟶ X) → L.ι) → K := fun x J =>
    valF x (LB.wchart L φ (fun k => J (x ≫ φ k))) (s.f (fun k => J (x ≫ φ k)))
  have hv : ∀ x z J, Good L z J → sval s x z J = toStk z (v x J) := fun x z J hJ =>
    (toStk_valF_gs x _ z (hJ.mem φ x) _).symm
  have key : ∀ σ : K ≃+* K, (∀ a ∈ k₀, σ a = a) → ∃ c : K, ∀ x, R x → ∀ z J, Good L z J →
      σ (v x J) = c * v x J := by
    intro σ hσ
    obtain ⟨σt, hφ, hx⟩ := h2 σ hσ
    have e : (fun k => σt ≫ φ k) = φ := funext hφ
    obtain ⟨c, hc⟩ := h1 (e ▸ ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s σt)
    refine ⟨c, fun x hR z J hJ => ?_⟩
    have a1 := hc x hR z J hJ
    rw [sval_cast, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s σt x z hJ, hx x hR,
      sval_spMap s σ.toRingHom x z hJ (fun k => by rw [← Category.assoc, ← hx x hR, Category.assoc, hφ]),
      hv x z J hJ, ← map_mul] at a1
    exact (toStk z).injective a1
  by_cases hex : ∃ x J z, R x ∧ Good L z J ∧ v x J ≠ 0
  · obtain ⟨x₀, J₀, z₀, hR₀, hJ₀, hne⟩ := hex
    refine ⟨v x₀ J₀, hne, fun x hR z J hJ => ⟨v x J / v x₀ J₀, ?_, ?_⟩⟩
    · apply mem_of_finite_conj k₀ hk₀
      apply (Set.finite_singleton (v x J / v x₀ J₀)).subset
      rintro b ⟨σ, hσ, rfl⟩
      obtain ⟨c, hc⟩ := key σ hσ
      have h0 := hc x₀ hR₀ z₀ J₀ hJ₀
      have h1' := hc x hR z J hJ
      have hc0 : c ≠ 0 := by
        rintro rfl
        rw [zero_mul] at h0
        exact hne (σ.injective (h0.trans (map_zero σ).symm))
      show σ (v x J / v x₀ J₀) = v x J / v x₀ J₀
      rw [map_div₀, h0, h1', mul_div_mul_left _ _ hc0]
    · rw [hv x z J hJ, mul_div_cancel₀ _ hne]
  · push Not at hex
    refine ⟨1, one_ne_zero, fun x hR z J hJ => ⟨0, k₀.zero_mem, ?_⟩⟩
    rw [hv x z J hJ, hex x J z hR hJ, mul_zero]

variable {V V₁ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁]

theorem spMap_conj {K : Type} [Field K] (k₀ : Subfield K) {R : Type} [CommRing R] (f : R →+* K) (hf : ∀ a, f a ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) : spMap σ.toRingHom ≫ spMap f = spMap f := by
  simp only [spMap, ← Spec.map_comp]
  congr 1
  ext a
  exact hσ _ (hf a)

theorem exists_conj_fibre {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (ib : W₀ →+* V) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] (β : Q.B.left ⟶ B₀.left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (K : Type) [Field K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀)
    (σ : K ≃+* K) (hσ : ∀ a ∈ k₀, σ a = a) :
    ∃ σt : (Over.mk (spMap ev) ⊗ D.P.A).left ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left,
      (∀ a, σt ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
        (snd (Over.mk (spMap ev)) D.P.A).left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β) ∧
      ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
        (∀ a, DefOver k₀ (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ (pr a).left ≫
          pullback.fst Q.B.hom (spMap ρ) ≫ β)) →
        x ≫ σt = spMap σ.toRingHom ≫ x := by
  set E := Over.mk (spMap ev) with hE
  set fK := (fst E D.P.A).left with hfK
  set q := (snd E D.P.A).left with hq
  have hw : q ≫ D.P.A.hom = fK ≫ spMap ev := (Over.w (snd E D.P.A)).trans (Over.w (fst E D.P.A)).symm
  have hf : ∀ a, ((ev.comp ρ).comp ib) a ∈ k₀ := hk
  obtain ⟨Φ₀, hΦ₀⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (fK ≫ spMap ev)
    (fK ≫ spMap ((ev.comp ρ).comp ib)) (by rw [Category.assoc, spMap_three])
  obtain ⟨Φ₁, hΦ₁⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (fK ≫ spMap σ.toRingHom ≫ spMap ev)
    (fK ≫ spMap ((ev.comp ρ).comp ib))
    (by rw [Category.assoc, Category.assoc, spMap_three, spMap_conj k₀ _ hf σ hσ])
  let qpt : Over.mk (fK ≫ spMap ev) ⟶ D.P.A := Over.homMk q hw
  let σD := Φ₁.symm (Φ₀ qpt)
  let a0 : Over.mk (fK ≫ spMap σ.toRingHom ≫ spMap ev) ⟶ E :=
    Over.homMk (fK ≫ spMap σ.toRingHom) (Category.assoc _ _ _)
  let σt : (E ⊗ D.P.A).left ⟶ (E ⊗ D.P.A).left := (lift a0 σD).left
  have hfst : σt ≫ fK = fK ≫ spMap σ.toRingHom := congrArg (fun z => z.left) (lift_fst a0 σD)
  have hsnd : σt ≫ q = σD.left := congrArg (fun z => z.left) (lift_snd a0 σD)
  have hproj : ∀ a, σt ≫ q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
      q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
    intro a
    rw [reassoc_of% hsnd, ← hΦ₁ σD a, MulEquiv.apply_symm_apply, hΦ₀]
    rfl
  refine ⟨σt, hproj, fun x hx hdef => ?_⟩
  have hEh : (E ⊗ D.P.A).hom = fK ≫ spMap ev := (Over.w (fst E D.P.A)).symm
  let T : Over (Sp V₁) := Over.mk (spMap σ.toRingHom ≫ spMap ev)
  let m1 : T ⟶ E ⊗ D.P.A := Over.homMk (x ≫ σt) (by
    show (x ≫ σt) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hfst, reassoc_of% hx])
  let m2 : T ⟶ E ⊗ D.P.A := Over.homMk (spMap σ.toRingHom ≫ x) (by
    show (spMap σ.toRingHom ≫ x) ≫ (E ⊗ D.P.A).hom = spMap σ.toRingHom ≫ spMap ev
    rw [hEh, Category.assoc, reassoc_of% hx])
  have hm : m1 = m2 := by
    apply CartesianMonoidalCategory.hom_ext
    · apply Over.OverMorphism.ext
      show (x ≫ σt) ≫ fK = (spMap σ.toRingHom ≫ x) ≫ fK
      rw [Category.assoc, hfst, reassoc_of% hx, Category.assoc, hx, Category.comp_id]
    · obtain ⟨Φ₂, hΦ₂⟩ := exists_points_equiv ρ ib Q D pr hpr huniv B₀ β hβ (spMap σ.toRingHom ≫ spMap ev)
        (spMap ((ev.comp ρ).comp ib)) (by rw [Category.assoc, spMap_three, spMap_conj k₀ _ hf σ hσ])
      apply Φ₂.injective
      funext a
      apply Over.OverMorphism.ext
      rw [hΦ₂, hΦ₂]
      show (x ≫ σt) ≫ q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β =
        (spMap σ.toRingHom ≫ x) ≫ q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β
      obtain ⟨P₀, hP₀⟩ := hdef a
      rw [Category.assoc, hproj, Category.assoc, ← hP₀, ← Category.assoc,
        spMap_conj k₀ k₀.subtype (fun a => a.2) σ hσ]
  exact congrArg (fun m => m.left) hm

theorem gs_appTop_of_section {K : Type} [Field K] {Y : Scheme.{0}} (x : Sp K ⟶ Y) (f : Y ⟶ Sp K) (hx : x ≫ f = 𝟙 _)
    (z : Sp K) (r : Γ(Sp K, ⊤)) :
    gs x z ⊤ (f.appTop.hom r) = toStk z ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r) := by
  have e1 := gs_pull x f z ⊤ trivial r
  erw [e1, hx, gs_eq _ z ⊤ trivial]
  show _ = ((Sp K).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom r))
  rw [Iso.hom_inv_id_apply]
  simp
  rfl

theorem gs_isoRel_at {Y Z : Scheme.{0}} {L M : LB Y} {w : LB.Iso L M} {s : LB.Sec L} {s' : LB.Sec M}
    (h : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.IsoRel w s s') (i : M.ι) (k : L.ι) (r : Z ⟶ Y) (z : Z) (hi : r z ∈ M.U i)
    (hk : r z ∈ L.U k) :
    gs r z (M.U i) (s'.f i) = (gm r z ((LB.div M L).U (i, k)) (w.s (i, k))).val * gs r z (L.U k) (s.f k) := by
  have hy : r z ∈ M.U i ⊓ L.U k := ⟨hi, hk⟩
  have e := congrArg (gs r z (M.U i ⊓ L.U k)) (h i k)
  rw [gs_res _ z _ hy, gs_mul _ z _ hy, gs_res _ z _ hy] at e
  rw [e]
  congr 1
  exact gs_unit _ z _ hy _

theorem fibre_one_dim (D : DegPre V₁) {K : Type} [Field K] (ev : V₁ →+* K)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (spMap ev)) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D ev θ')
    {X : Scheme.{0}} {L₂ : LB X} {Ix : Type} [Fintype Ix] (φ : Ix → (D.P.A.left ⟶ X)) (ε : Ix → ℤ) (hL₂ : L₂.IsLB)
    (u : LB.Iso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) (LB.LinComb L₂ φ ε)) (hu : u.IsGen)
    (s : LB.Sec (LB.LinComb L₂ φ ε)) (hs : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.IsoRel u θ s)
    (s₂ : LB.Sec (LB.LinComb L₂ (fun k => (snd (Over.mk (spMap ev)) D.P.A).left ≫ φ k) ε)) :
    ∃ c : K, ∀ x : Sp K ⟶ (Over.mk (spMap ev) ⊗ D.P.A).left, x ≫ (fst (Over.mk (spMap ev)) D.P.A).left = 𝟙 _ →
      ∀ z J, Good L₂ z J →
        sval s₂ x z J = toStk z c * sval (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s (snd (Over.mk (spMap ev)) D.P.A).left) x z J := by
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  have hL : D.P.L.IsLB := D.P.isLB
  have hA : (LB.LinComb D.P.L (fun i => q ≫ D.famφB 0 i) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ hL _ _
  have hB : (LB.LinComb L₂ (fun k => q ≫ φ k) ε).IsLB := DVR.linComb_isLB _ hL₂ _ _
  let u' := GlobalTheory.PolDeg.TautFrom.isoPull (chartPullComp D.P.L (D.famφB 0) (DegPre.famε 1) q) (chartPullComp L₂ φ ε q) u
  have hu' : u'.IsGen := GlobalTheory.PolDeg.TautFrom.isoPull_isGen _ _ u hu
  obtain ⟨a, ha⟩ := GlobalTheory.MBLow.lbIso_sec_onto _ _ _ u' hA hB hu' s₂
  have ha' : ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.IsoRel u' a s₂ := fun i k => ha (i, k)
  obtain ⟨r, hr, -⟩ := hθ (GlobalTheory.Poinc.ThetaOne.pullTo D ev θ) (GlobalTheory.Poinc.ThetaOne.isPullSecLC_pullTo D ev θ) a
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom (r 0), fun x hx z J hJ => ?_⟩
  choose I hI using fun χ : Sp K ⟶ D.P.A.left => exists_chart hL (χ z)
  have hIg : Good D.P.L z I := hI
  let jA : Fin 4 → D.P.L.ι := fun i => I (x ≫ q ≫ D.famφB 0 i)
  let jB : Ix → L₂.ι := fun k => J (x ≫ q ≫ φ k)
  have hmA : x z ∈ LB.wchart D.P.L (fun i => q ≫ D.famφB 0 i) jA := hIg.mem _ x
  have hmB : x z ∈ LB.wchart L₂ (fun k => q ≫ φ k) jB := hJ.mem _ x
  have hmA₀ : (x ≫ q) z ∈ LB.wchart D.P.L (D.famφB 0) jA :=
    (chartPullComp D.P.L (D.famφB 0) (DegPre.famε 1) q).le jA hmA
  have hmB₀ : (x ≫ q) z ∈ LB.wchart L₂ φ jB := (chartPullComp L₂ φ ε q).le jB hmB
  have lhs1 := gs_isoRel_at ha' jB jA x z hmB hmA
  have lhs2 := GlobalTheory.PolDeg.TautFrom.gm_isoPull (chartPullComp D.P.L (D.famφB 0) (DegPre.famε 1) q)
    (chartPullComp L₂ φ ε q) u x z (jB, jA) ⟨hmB, hmA⟩
  have rhs1 := gs_isoRel_at hs jB jA (x ≫ q) z hmB₀ hmA₀
  have hrA := hr jA
  rw [Fin.sum_univ_one] at hrA
  have mid : gs x z (LB.wchart D.P.L (fun i => q ≫ D.famφB 0 i) jA) (a.f jA) =
      toStk z ((Scheme.ΓSpecIso (CommRingCat.of K)).hom (r 0)) *
        gs (x ≫ q) z (LB.wchart D.P.L (D.famφB 0) jA) (θ.f jA) := by
    refine (congrArg (gs x z _) hrA).trans ((gs_mul x z _ hmA _ _).trans ?_)
    congr 1
    · refine (gs_res x z _ hmA _).trans ?_
      exact gs_appTop_of_section x _ hx z (r 0)
    · exact (gs_res _ z _ hmA _).trans (gs_pull x q z _ hmA₀ _)
  show gs x z _ (s₂.f jB) = _
  rw [ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ, sval_of s (x ≫ q) z J jB (fun k => by simp only [jB, Category.assoc])]
  rw [lhs1]
  erw [lhs2]
  erw [mid, rhs1]
  exact mul_left_comm _ _ _

theorem sharpPair_fst {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀]
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (hsq : IsSquare β β₂) (a b : Fin 8) :
    sharpPair ρ Q D pr a b ≫ β₂ ≫ (fst B₀ B₀).left = (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  rw [hsq.1]
  show (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b)) ≫ fst Q.B Q.B).left ≫ β = _
  rw [lift_fst]
  rfl

theorem sharpPair_snd {W₀ : Type} [CommRing W₀] (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀]
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (hsq : IsSquare β β₂) (a b : Fin 8) :
    sharpPair ρ Q D pr a b ≫ β₂ ≫ (snd B₀ B₀).left = (pr b).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β := by
  rw [hsq.2]
  show (lift (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr a))
    (pushPt (isGrpPullback_pullback Q.B (spMap ρ)).1.w (pr b)) ≫ snd Q.B Q.B).left ≫ β = _
  rw [lift_snd]
  rfl

theorem kzero_theta_of_iso {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (hsq : IsSquare β β₂)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ')
    (u : LB.Iso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))
      (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂) (fun p => W p.1 p.2)))
    (hu : u.IsGen)
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∃ κ : K, κ ≠ 0 ∧ ∀ r : Sp K ⟶ D.P.A.left, r ≫ D.P.A.hom = spMap ev →
      (∀ a, DefOver k₀ (r ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)) →
      ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ (G2 B₀).left) → (abelian₂ B₀ M₀).ι),
        Good D.P.L z J → Good (abelian₂ B₀ M₀) z J₀ →
        ∃ c ∈ k₀, (gm r z _ (u.s (fun p => J₀ (r ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂),
          fun i => J (r ≫ D.famφB 0 i)))).val * sval θ r z J = toStk z (κ * c) := by
  have hLam : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)).IsLB := DVR.linComb_isLB _ hLam _ _
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.exists_isoRel hL hM hu θ
  let E := Over.mk (spMap ev)
  let q := (snd E D.P.A).left
  let R : (Sp K ⟶ (E ⊗ D.P.A).left) → Prop := fun x => x ≫ (fst E D.P.A).left = 𝟙 _ ∧
    ∀ a, DefOver k₀ (x ≫ q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)
  obtain ⟨κ, hκ, hval⟩ := galois_values k₀ hk₀ (fun p : Fin 8 × Fin 8 => q ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
    (fun p => W p.1 p.2) (ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.pullSec s q) R
    (fun t => by
      obtain ⟨c, hc⟩ := fibre_one_dim D ev θ (hθ K ev) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
        (fun p => W p.1 p.2) hLam u hu s hs t
      exact ⟨c, fun x hR z J hJ => hc x hR.1 z J hJ⟩)
    (fun σ hσ => by
      obtain ⟨σt, hproj, hfix⟩ := exists_conj_fibre ρ ib Q D pr hpr huniv B₀ β hβ K ev k₀ hk σ hσ
      refine ⟨σt, fun p => ?_, fun x hR => hfix x hR.1 hR.2⟩
      apply pullback.hom_ext
      · show (σt ≫ q ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂) ≫ (fst B₀ B₀).left =
          (q ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂) ≫ (fst B₀ B₀).left
        simp only [Category.assoc]
        rw [sharpPair_fst ρ Q D pr B₀ β β₂ hsq]
        exact hproj p.1
      · show (σt ≫ q ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂) ≫ (snd B₀ B₀).left =
          (q ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂) ≫ (snd B₀ B₀).left
        simp only [Category.assoc]
        rw [sharpPair_snd ρ Q D pr B₀ β β₂ hsq]
        exact hproj p.2)
  refine ⟨κ, hκ, fun r hr hdef z J J₀ hJ hJ₀ => ?_⟩
  let a1 : Over.mk (spMap ev) ⟶ E := Over.homMk (𝟙 (Sp K)) (Category.id_comp _)
  let b1 : Over.mk (spMap ev) ⟶ D.P.A := Over.homMk r hr
  let x : Sp K ⟶ (E ⊗ D.P.A).left := (lift a1 b1).left
  have hxf : x ≫ (fst E D.P.A).left = 𝟙 _ :=
    congrArg (fun m : Over.mk (spMap ev) ⟶ E => m.left) (lift_fst a1 b1)
  have hxq : x ≫ q = r := congrArg (fun m : Over.mk (spMap ev) ⟶ D.P.A => m.left) (lift_snd a1 b1)
  have hRx : R x := ⟨hxf, fun a => by
    show DefOver k₀ (x ≫ q ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)
    rw [reassoc_of% hxq]
    exact hdef a⟩
  obtain ⟨c, hc, he⟩ := hval x hRx z J₀ hJ₀
  refine ⟨c, hc, ?_⟩
  rw [← he, ReciprocityTheory.ChartRestriction.G.H1.SectionArithmetic.sval_pullSec s q x z hJ₀, hxq]
  exact (gs_isoRel_at hs _ _ r z (hJ₀.mem _ r) (hJ.mem _ r)).symm

theorem theta_bundle_lbIso (D : DegPre V₁) : LBIso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) D.P.L := by
  have hL : D.P.L.IsLB := D.P.isLB
  have h1 : toUnit D.P.A ≫ D.c 0 = toUnit D.P.A ≫ η[D.P.A] := by
    rw [GlobalTheory.Poinc.ThetaOne.c_zero D, MonObj.comp_one]
    rfl
  have h2 : padd D.P.A (𝟙 D.P.A) (toUnit D.P.A ≫ η[D.P.A]) = 𝟙 D.P.A := mul_one (𝟙 D.P.A)
  have hc : LBIso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)) (D.P.L.pull (𝟙 D.P.A.left)) := by
    refine (GlobalTheory.PrimNorm.lbIso_iff hL _ _ _ _).2 ?_
    simp only [DegPre.famφB, DegPre.famε, Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, h1, h2, Fintype.prod_unique]
    simp
  exact ((GlobalTheory.TripleCompare.lbIso_iff_pull_id D.P.L _).2 hc).symm

theorem kzero_theta {W₀ : Type} [CommRing W₀] (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (ib : W₀ →+* V)
    (Q : Data V) (D : DegPre V₁)
    (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (hpr : ∀ a, IsMonHom (pr a))
    (huniv : ∀ (T : Over (Sp V₁)) (y : Fin 8 → (T ⟶ (Over.pullback (spMap ρ)).obj Q.B)),
      ∃! x : T ⟶ D.P.A, ∀ a, x ≫ pr a = y a)
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀] (M₀ : LB B₀.left) (hM₀ : M₀.IsLB)
    (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left) (hβ : IsGrpPullback Q.B B₀ (spMap ib) β)
    (hsq : IsSquare β β₂) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen)
    (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ (R' : Type) [CommRing R'] (f : V₁ →+* R') θ',
      IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (Spec.map (CommRingCat.ofHom f))) D.P.A).left θ θ' →
        GlobalTheory.Poinc.ThetaOne.OneBasisAt D f θ')
    (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K) (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀)
    (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∃ u : LB.Iso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))
        (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂) (fun p => W p.1 p.2)),
      u.IsGen ∧ ∃ κ : K, κ ≠ 0 ∧ ∀ r : Sp K ⟶ D.P.A.left, r ≫ D.P.A.hom = spMap ev →
        (∀ a, DefOver k₀ (r ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)) →
        ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ (G2 B₀).left) → (abelian₂ B₀ M₀).ι),
          Good D.P.L z J → Good (abelian₂ B₀ M₀) z J₀ →
          ∃ c ∈ k₀, (gm r z _ (u.s (fun p => J₀ (r ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂),
            fun i => J (r ≫ D.famφB 0 i)))).val * sval θ r z J = toStk z (κ * c) := by
  have hLam : (abelian₂ B₀ M₀).IsLB := DVR.linComb_isLB _ hM₀ _ _
  have hL : (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)).IsLB := DVR.linComb_isLB _ D.P.isLB _ _
  have hM : (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂)
      (fun p => W p.1 p.2)).IsLB := DVR.linComb_isLB _ hLam _ _
  obtain ⟨u, hu⟩ := LBIso.trans hL D.P.isLB hM (theta_bundle_lbIso D)
    (sharp_bundle W ρ Q D pr w hw B₀ M₀ hM₀ β₂ w₀ hw₀)
  exact ⟨u, hu, kzero_theta_of_iso W ρ ib Q D pr hpr huniv B₀ M₀ hM₀ β β₂ hβ hsq θ hθ u hu K ev k₀ hk₀ hk⟩

example {W₀ : Type} [CommRing W₀] [IsLocalRing V₁] (hV : IsCN V₁) (W : Matrix (Fin 8) (Fin 8) ℤ) (Q : Data V)
    (ρ : V →+* V₁) (D : DegPre V₁) (e : (Fin 8 → Q.X) ≃+ D.X) (τ₀ : Gens Q) (ib : W₀ →+* V)
    (h₁ : SharpRef W Q ρ D e) (h₂ : FromBase Q τ₀ ib) (K : Type) [Field K] [IsAlgClosed K] (ev : V₁ →+* K)
    (k₀ : Subfield K) (hk₀ : IsAlgClosed k₀) (hk : ∀ a, ev (ρ (ib a)) ∈ k₀) :
    ∃ (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
      (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) (_ : GrpObj B₀)
      (_ : IsCommMonObj B₀) (M₀ : LB B₀.left) (β : Q.B.left ⟶ B₀.left) (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)
      (u : LB.Iso (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1))
        (LB.LinComb (abelian₂ B₀ M₀) (K := Fin 8 × Fin 8) (fun p => sharpPair ρ Q D pr p.1 p.2 ≫ β₂) (fun p => W p.1 p.2))),
      (∃ j, (GlobalTheory.Poinc.ThetaOne.pullTo D ev θ).f j ≠ 0) ∧ u.IsGen ∧ ∃ κ : K, κ ≠ 0 ∧
        ∀ r : Sp K ⟶ D.P.A.left, r ≫ D.P.A.hom = spMap ev →
        (∀ a, DefOver k₀ (r ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)) →
        ∀ (z : Sp K) (J : (Sp K ⟶ D.P.A.left) → D.P.L.ι) (J₀ : (Sp K ⟶ (G2 B₀).left) → (abelian₂ B₀ M₀).ι),
          Good D.P.L z J → Good (abelian₂ B₀ M₀) z J₀ →
          ∃ c ∈ k₀, (gm r z _ (u.s (fun p => J₀ (r ≫ sharpPair ρ Q D pr p.1 p.2 ≫ β₂),
            fun i => J (r ≫ D.famφB 0 i)))).val * sval θ r z J = toStk z (κ * c) := by
  obtain ⟨pr, w, hpr, huniv, hw, -, -⟩ := h₁
  obtain ⟨B₀, iG, iC, M₀, -, -, β, β₂, w₀, -, hM₀, hβ, hsq, hw₀, -, -, -⟩ := h₂
  obtain ⟨θ, hθ, hnz, -, -, -⟩ := GlobalTheory.Poinc.ThetaOne.main hV D
  obtain ⟨u, hu, rest⟩ := kzero_theta W ρ ib Q D pr hpr huniv w hw B₀ M₀ hM₀ β β₂ hβ hsq w₀ hw₀ θ hθ K ev k₀ hk₀ hk
  exact ⟨θ, pr, B₀, iG, iC, M₀, β, β₂, u, hnz K ev, hu, rest⟩

end GlobalTheory.Poinc.Sep
