import Mathlib
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

namespace GlobalTheory.Poinc.Sep.Coef

section Tools

variable {X X₂ Y : Scheme.{0}}

def isoV {A C : LB Y} (u : LB.Iso A C) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : C.ι) (a : A.ι) :
    (Z.presheaf.stalk z)ˣ := gm r z (C.U c ⊓ A.U a) (u.s (c, a))

def flatChart (L : LB X₂) {I K : Type} [Fintype I] [Fintype K] (π : I → (X ⟶ X₂)) (e : I → ℤ) (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : ChartPull (LB.LinComb L (fun p : K × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2))
      (LB.LinComb (LB.LinComb L π e) φ ε) (𝟙 Y) :=
  have le : ∀ j : K × I → L.ι, LB.wchart L (fun p : K × I => φ p.1 ≫ π p.2) j ≤
      LB.wchart (LB.LinComb L π e) φ (fun k i => j (k, i)) := fun j y hy =>
    Set.mem_iInter.2 fun k => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy (k, i)
  { idx := fun j k i => j (k, i)
    le := le
    g := fun y j j' hj hj' => by
      refine (gm_linComb L _ _ (𝟙 Y) y j j' hj hj').trans (Eq.trans ?_
        (gm_linComb (LB.LinComb L π e) φ ε (𝟙 Y) y _ _ (le j hj) (le j' hj')).symm)
      rw [Fintype.prod_prod_type]
      refine Finset.prod_congr rfl fun k _ => Eq.symm ?_
      refine (congrArg (· ^ ε k) (gm_linComb L π e (𝟙 Y ≫ φ k) y (fun i => j (k, i)) (fun i => j' (k, i))
        (Set.mem_iInter.1 (le j hj) k) (Set.mem_iInter.1 (le j' hj') k))).trans ?_
      rw [← Finset.prod_zpow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← zpow_mul, mul_comm (e i), Category.assoc] }

theorem isoV_isoPull {A' C' A C : LB Y} (a : ChartPull A' A (𝟙 Y)) (b : ChartPull C' C (𝟙 Y)) (u : LB.Iso A C)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : C'.ι) (i : A'.ι) (hc : r z ∈ C'.U c) (hi : r z ∈ A'.U i) :
    isoV (TautFrom.isoPull a b u) r z c i = isoV u r z (b.idx c) (a.idx i) :=
  (TautFrom.gm_isoPull a b u r z (c, i) ⟨hc, hi⟩).trans (by rw [Category.comp_id]; rfl)

theorem isoV_linComb {A C : LB X} (u : LB.Iso A C) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (c : K → C.ι) (a : K → A.ι) (hc : r z ∈ LB.wchart C φ c)
    (ha : r z ∈ LB.wchart A φ a) :
    isoV (LB.linCombIso u φ ε) r z c a = ∏ k, isoV u (r ≫ φ k) z (c k) (a k) ^ ε k := by
  refine (map_prod _ _ _).trans (Finset.prod_congr rfl fun k _ => (map_zpow _ _ _).trans (congrArg (· ^ ε k) ?_))
  exact (gm_res r z _ (show r z ∈ LB.wchart C φ c ⊓ LB.wchart A φ a from ⟨hc, ha⟩) _).trans
    (gm_pull r (φ k) z (C.U (c k) ⊓ A.U (a k)) ⟨Set.mem_iInter.1 hc k, Set.mem_iInter.1 ha k⟩ _)

theorem isoV_trans {A C : LB Y} {u : LB.Iso A C} (hu : u.IsGen) {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {c c' : C.ι}
    {a a' : A.ι} (hc : r z ∈ C.U c) (hc' : r z ∈ C.U c') (ha : r z ∈ A.U a) (ha' : r z ∈ A.U a') :
    isoV u r z c a = gm r z _ (C.g c c') * (gm r z _ (A.g a a'))⁻¹ * isoV u r z c' a' := by
  have hm : r z ∈ C.U c ⊓ A.U a ⊓ (C.U c' ⊓ A.U a') := ⟨⟨hc, ha⟩, ⟨hc', ha'⟩⟩
  have e := congrArg (gm r z (C.U c ⊓ A.U a ⊓ (C.U c' ⊓ A.U a'))) (hu (c, a) (c', a'))
  exact (gm_res r z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A C r z (c, a) (c', a') hm) (gm_res r z _ hm _))))

theorem exists_comp_form {M : LB X} (hM : M.IsLB) {A C : LB Y} (hA : A.IsLB) (hC : C.IsLB) {K K' : Type} [Fintype K]
    [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} (h : FormEq φ ε φ' ε')
    (u₁ : LB.Iso A (LB.LinComb M φ ε)) (h₁ : u₁.IsGen) (u₂ : LB.Iso (LB.LinComb M φ' ε') C) (h₂ : u₂.IsGen) :
    ∃ u : LB.Iso A C, u.IsGen ∧ ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J : (Z ⟶ X) → M.ι) (c : C.ι) (a : A.ι),
      Good M z J → r z ∈ C.U c → r z ∈ A.U a →
      isoV u r z c a = isoV u₂ r z c (fun k => J (r ≫ φ' k)) * isoV u₁ r z (fun k => J (r ≫ φ k)) a := by
  let Wd : ((Y ⟶ X) → M.ι) → Y.Opens := fun I =>
    LB.wchart M φ (fun k => I (φ k)) ⊓ LB.wchart M φ' (fun k => I (φ' k))
  let v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I : (Y ⟶ X) → M.ι) (c : C.ι) (a : A.ι), (Z.presheaf.stalk z)ˣ :=
    fun Z r z I c a => isoV u₂ r z c (fun k => I (φ' k)) * isoV u₁ r z (fun k => I (φ k)) a
  have tr : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (I I' : (Y ⟶ X) → M.ι) (c c' : C.ι) (a a' : A.ι),
      r z ∈ Wd I → r z ∈ Wd I' → r z ∈ C.U c → r z ∈ C.U c' → r z ∈ A.U a → r z ∈ A.U a' →
      v Z r z I c a = gm r z _ (C.g c c') * (gm r z _ (A.g a a'))⁻¹ * v Z r z I' c' a' := by
    intro Z r z I I' c c' a a' hI hI' hc hc' ha ha'
    have e₁ := isoV_trans h₁ r z hI.1 hI'.1 ha ha'
    have e₂ := isoV_trans h₂ r z hc hc' hI.2 hI'.2
    have f₁ := gm_linComb M φ ε r z _ _ hI.1 hI'.1
    have f₂ := gm_linComb M φ' ε' r z _ _ hI.2 hI'.2
    have f := h.trF (L := M) r z I I'
    have f' := (f₁.trans f).trans f₂.symm
    have alg : ∀ {U : Type} [CommGroup U] (g₁ g₂ gc ga x₁ x₂ : U), g₁ = g₂ →
        gc * g₂⁻¹ * x₂ * (g₁ * ga⁻¹ * x₁) = gc * ga⁻¹ * (x₂ * x₁) := by
      rintro U _ g₁ _ gc ga x₁ x₂ rfl
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel
    exact (congrArg₂ (· * ·) e₂ e₁).trans (alg _ _ _ _ _ _ f')
  have cov : ∀ y : Y, ∃ I, y ∈ Wd I := fun y => by
    choose I hI using fun ψ : Y ⟶ X => exists_chart hM (ψ y)
    exact ⟨I, Set.mem_iInter.2 fun k => hI _, Set.mem_iInter.2 fun k => hI _⟩
  let b : ∀ (p : C.ι × A.ι) (I : (Y ⟶ X) → M.ι), Γ(Y, C.U p.1 ⊓ A.U p.2 ⊓ Wd I)ˣ := fun p I =>
    res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_right))
      (@id Γ(Y, C.U p.1 ⊓ LB.wchart M φ' (fun k => I (φ' k)))ˣ (u₂.s (p.1, fun k => I (φ' k)))) *
    res (le_inf (inf_le_right.trans inf_le_left) (inf_le_left.trans inf_le_right))
      (@id Γ(Y, LB.wchart M φ (fun k => I (φ k)) ⊓ A.U p.2)ˣ (u₁.s (fun k => I (φ k), p.2)))
  have hb : ∀ p I (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ C.U p.1 ⊓ A.U p.2 ⊓ Wd I →
      gm r z _ (b p I) = v Z r z I p.1 p.2 := fun p I Z r z hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  have gl : ∀ p : C.ι × A.ι, ∃ s : Γ(Y, C.U p.1 ⊓ A.U p.2)ˣ, ∀ I, res inf_le_left s = b p I := fun p =>
    glue_unit _ (fun I => C.U p.1 ⊓ A.U p.2 ⊓ Wd I) (fun _ => inf_le_left)
      (fun y hy => by
        obtain ⟨I, hI⟩ := cov y
        exact TopologicalSpace.Opens.mem_iSup.2 ⟨I, hy, hI⟩) (b p)
      (fun I I' y hy => by
        rw [hb p I _ _ y hy.1, hb p I' _ _ y hy.2, tr Y (𝟙 Y) y I I' p.1 p.1 p.2 p.2 hy.1.2 hy.2.2 hy.1.1.1 hy.1.1.1
          hy.1.1.2 hy.1.1.2, gm_self hC (𝟙 Y) y hy.1.1.1, gm_self hA (𝟙 Y) y hy.1.1.2]
        simp)
  choose s hs using gl
  have hv : ∀ p I (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z), r z ∈ C.U p.1 ⊓ A.U p.2 ⊓ Wd I →
      gm r z _ (s p) = v Z r z I p.1 p.2 := fun p I Z r z hz =>
    (gm_res r z inf_le_left hz _).symm.trans ((congrArg (gm r z _) (hs p I)).trans (hb p I Z r z hz))
  refine ⟨⟨s⟩, fun p q => unit_ext fun y hy => ?_, fun Z r z J c a hJ hc ha =>
    hv (c, a) (fun ψ => J (r ≫ ψ)) Z r z ⟨⟨hc, ha⟩, hJ.mem φ r, hJ.mem φ' r⟩⟩
  obtain ⟨I, hI⟩ := cov y
  refine ((gm_res (𝟙 Y) y _ hy _).trans (hv p I _ _ y ⟨hy.1, hI⟩)).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div A C (𝟙 Y) y p q hy)
    ((gm_res (𝟙 Y) y _ hy _).trans (hv q I _ _ y ⟨hy.2, hI⟩)))).trans ?_
  exact (tr Y (𝟙 Y) y I I p.1 q.1 p.2 q.2 hI hI hy.1.1 hy.2.1 hy.1.2 hy.2.2).symm

variable {L : LB X} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (X ⟶ X₂)} {e : I → ℤ}

def om (u : LB.Iso L (LB.LinComb L₂ π e)) {Z : Scheme.{0}} (z : Z) (J : (Z ⟶ X) → L.ι) (J₂ : (Z ⟶ X₂) → L₂.ι)
    (x : Z ⟶ X) : (Z.presheaf.stalk z)ˣ := isoV u x z (fun i => J₂ (x ≫ π i)) (J x)

theorem exists_transport (u : LB.Iso L (LB.LinComb L₂ π e)) (hu : u.IsGen) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) : ∃ U : LB.Iso (LB.LinComb L φ ε)
      (LB.LinComb L₂ (fun p : K × I => φ p.1 ≫ π p.2) (fun p => ε p.1 * e p.2)), U.IsGen ∧
      ∀ (s : LB.Sec (LB.LinComb L φ ε)) s', DVR.FlatBC.IsoRel U s s' →
        ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) J J₂, Good L z J → Good L₂ z J₂ →
          sval s' r z J₂ = (∏ k, om u z J J₂ (r ≫ φ k) ^ ε k).val * sval s r z J := by
  refine ⟨TautFrom.isoPull (chartPullId _) (flatChart L₂ π e φ ε) (LB.linCombIso u φ ε),
    TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen u hu φ ε), fun s s' hs Z r z J J₂ hJ hJ₂ => ?_⟩
  refine (gs_isoRel_at hs _ _ r z (hJ₂.mem _ r) (hJ.mem φ r)).trans (congrArg (fun t => Units.val t * _) ?_)
  refine (isoV_isoPull _ _ _ r z _ _ (hJ₂.mem _ r) (hJ.mem φ r)).trans ?_
  refine (isoV_linComb u φ ε r z _ _ ((flatChart L₂ π e φ ε).le _ (hJ₂.mem _ r)) (hJ.mem φ r)).trans ?_
  refine Finset.prod_congr rfl fun k _ => congrArg (· ^ ε k) ?_
  simp only [om, Category.assoc]
  rfl

theorem exists_gen_of_isoRel {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ} {C : LB Y} (hC : C.IsLB)
    {U : LB.Iso (LB.LinComb L φ ε) C} {s : LB.Sec (LB.LinComb L φ ε)} {t : LB.Gen C} (ht : t.IsGen)
    (h : DVR.FlatBC.IsoRel U s (genSec t ht)) : ∃ (g : LB.Gen (LB.LinComb L φ ε)) (hg : g.IsGen), genSec g hg = s := by
  have hu : ∀ j, IsUnit (s.f j) := fun j => by
    refine RingedSpace.isUnit_of_isUnit_germ (X := Y.toRingedSpace) _ _ fun y hy => ?_
    obtain ⟨c, hc⟩ := exists_chart hC y
    have e := gs_isoRel_at h c j (𝟙 Y) y hc hy
    have u1 : IsUnit (gs (𝟙 Y) y (C.U c) ((genSec t ht).f c)) := by
      erw [gs_unit (𝟙 Y) y _ hc (t.s c)]; exact Units.isUnit _
    rw [e] at u1
    have u2 := isUnit_of_mul_isUnit_right u1
    rw [gs_eq _ y _ hy] at u2
    exact u2
  exact ⟨⟨fun j => (hu j).unit⟩, fun i j => Units.ext (s.compat i j), rfl⟩

end Tools

section Galois

variable {V₁ W₀ K : Type} [CommRing V₁] [CommRing W₀] [Field K] {A : Over (Sp V₁)} [GrpObj A] {B₀ : Over (Sp W₀)}
  [GrpObj B₀] (f : W₀ →+* V₁) (q : Fin 8 → (A.left ⟶ B₀.left))

def PowPts : Prop := ∀ (T : Over (Sp V₁)) (g : T.left ⟶ Sp W₀), T.hom ≫ spMap f = g →
  ∃ Φ : (T ⟶ A) ≃* (Fin 8 → (Over.mk g ⟶ B₀)), ∀ x a, (Φ x a).left = x.left ≫ q a

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

theorem ratM_pow (hP : PowPts f q) (hk : ∀ a, ev (f a) ∈ k₀) (h1 : RatP q k₀ (1 : Over.mk (spMap ev) ⟶ A).left)
    {x : Over.mk (spMap ev) ⊗ A ⟶ A} (hx : RatM q ev k₀ x.left) (n : ℕ) : RatM q ev k₀ (x ^ n).left := by
  induction n with
  | zero => rw [pow_zero]; exact ratM_one h1
  | succ n ih => rw [pow_succ]; exact ratM_mul hP hk ih hx

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

variable {V₁ W₀ K : Type} [CommRing V₁] [IsDomain V₁] [CommRing W₀] [Field K] [IsAlgClosed K] {D : DegPre V₁}
  {B₀ : Over (Sp W₀)} [GrpObj B₀] {f : W₀ →+* V₁} {q : Fin 8 → (D.P.A.left ⟶ B₀.left)} {ev : V₁ →+* K} {k₀ : Subfield K}
  {X₂ : Scheme.{0}} {L₂ : LB X₂} {I : Type} [Fintype I] {π : I → (D.P.A.left ⟶ X₂)} {e : I → ℤ}

structure Desc (f : W₀ →+* V₁) (q : Fin 8 → (D.P.A.left ⟶ B₀.left)) (ev : V₁ →+* K) (k₀ : Subfield K)
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

theorem kap_mem (H : Desc f q ev k₀ u) {n : ℕ} (κ : LB.Gen (kapLB D (𝟙 D.P.A ^ n) (n ^ 2) 1)) (hκ : Normd κ)
    (y : Over.mk (spMap ev) ⟶ D.P.A) (hy : RatP q k₀ y.left) (z : Sp K) (J J₂) (hJ : Good D.P.L z J)
    (hJ₂ : Good L₂ z J₂) :
    ∃ c ∈ k₀, ((om (Z := Sp K) u z J J₂ y.left ^ ((n : ℤ) ^ 2) * (om (Z := Sp K) u z J J₂ (y ^ n).left)⁻¹ *
      om (Z := Sp K) u z J J₂ (1 : Over.mk (spMap ev) ⟶ D.P.A).left ^ (1 - (n : ℤ) ^ 2)) *
      val (Z := Sp K) κ y.left z J).val = toStk z c := by
  have r₃ : RatM q ev k₀ _ := ratM_snd
  have key := galois_gen H (SymFrame.grep_kap (D := D) κ hκ.1 (snd (Over.mk (spMap ev)) D.P.A))
    ![(snd (Over.mk (spMap ev)) D.P.A).left, (snd (Over.mk (spMap ev)) D.P.A ^ n).left,
      (1 : Over.mk (spMap ev) ⊗ D.P.A ⟶ D.P.A).left] ![(n : ℤ) ^ 2, -1, 1 - (n : ℤ) ^ 2]
    (fun k => by
      fin_cases k
      exacts [r₃, ratM_pow H.hP H.hk H.one r₃ n, ratM_one H.one])
    (fun U _ h => by simp [Fin.prod_univ_three])
    (fun U _ h => by
      simp only [← Over.comp_left, MonObj.comp_pow, MonObj.comp_one, lift_snd, one_pow]
      group)
    (fun z J hJ => by
      simp only [lift_snd]
      exact SymFrame.normd_one hκ hJ) y hy z J J₂ hJ hJ₂
  simp only [← Over.comp_left, MonObj.comp_pow, MonObj.comp_one, lift_snd] at key
  exact key

theorem theta_mem (H : Desc f q ev k₀ u) (θ : LB.Sec (LB.LinComb D.P.L (D.famφB 0) (DegPre.famε 1)))
    (hθ : ∀ θ', IsPullSecLC D.P.L (D.famφB 0) (DegPre.famε 1) (snd (Over.mk (spMap ev)) D.P.A).left θ θ' →
      GlobalTheory.Poinc.ThetaOne.OneBasisAt D ev θ') :
    ∃ κ : K, κ ≠ 0 ∧ ∀ p : Over.mk (spMap ev) ⟶ D.P.A, RatP q k₀ p.left → ∀ (z : Sp K) J J₂, Good D.P.L z J →
      Good L₂ z J₂ → ∃ c ∈ k₀, (om (Z := Sp K) u z J J₂ p.left).val * sval (Z := Sp K) θ p.left z J = toStk z (κ * c) := by
  have r₃ : RatM q ev k₀ _ := ratM_snd
  have e : ∀ {T : Over (Sp V₁)} (y : T ⟶ D.P.A), (fun k => y.left ≫ D.famφB 0 k) =
      ![y.left, y.left, (1 : T ⟶ D.P.A).left, (1 : T ⟶ D.P.A).left] := fun {T} y => by
    funext k
    fin_cases k
    · exact Category.comp_id _
    · show (y ≫ (𝟙 D.P.A * (toUnit D.P.A ≫ D.c 0))).left = y.left
      rw [ThetaOne.c_zero, MonObj.comp_one, _root_.mul_one, Category.comp_id]
    · show (y ≫ toUnit D.P.A ≫ D.c 0).left = (1 : T ⟶ D.P.A).left
      rw [ThetaOne.c_zero, MonObj.comp_one, MonObj.comp_one]
    · show (y ≫ (1 : D.P.A ⟶ D.P.A)).left = (1 : T ⟶ D.P.A).left
      rw [MonObj.comp_one]
  obtain ⟨κ, hκ, hval⟩ := galois_sec H.hk₀ H.hP H.hk D.P.isLB H.hL₂ u H.hu H.hπ
    (fun k => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k) (DegPre.famε 1)
    (fun k => by
      rw [congrFun (e (snd (Over.mk (spMap ev)) D.P.A)) k]
      fin_cases k
      exacts [r₃, r₃, ratM_one H.one, ratM_one H.one])
    (H1.SectionArithmetic.pullSec θ (snd (Over.mk (spMap ev)) D.P.A).left) (fun a => by
      obtain ⟨r, hr, -⟩ := hθ (H1.SectionArithmetic.pullSec θ (snd (Over.mk (spMap ev)) D.P.A).left) (fun _ => rfl) a
      refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom (r 0), fun x hx z J hJ => ?_⟩
      have hm := hJ.mem (fun k => (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k) x
      have hrA := hr (fun k => J (x ≫ (snd (Over.mk (spMap ev)) D.P.A).left ≫ D.famφB 0 k))
      rw [Fin.sum_univ_one] at hrA
      refine (congrArg (gs x z _) hrA).trans ((gs_mul x z _ hm _ _).trans (congrArg (· * _) ?_))
      exact (gs_res x z _ hm _).trans (gs_appTop_of_section x _ hx z (r 0)))
  refine ⟨κ, hκ, fun p hp z J J₂ hJ hJ₂ => ?_⟩
  obtain ⟨c, hc, he⟩ := hval p hp z J J₂ hJ hJ₂
  refine ⟨c, hc, Eq.trans ?_ he⟩
  have e₂ : (lift (𝟙 _) p).left ≫ (snd (Over.mk (spMap ev)) D.P.A).left = p.left :=
    congrArg (fun m => m.left) (lift_snd (𝟙 _) p)
  rw [H1.SectionArithmetic.sval_pullSec _ _ _ z hJ]
  simp only [← Category.assoc]
  erw [e₂]
  congr 2
  have e₃ := fun k => congrFun (e p) k
  simp only [e₃, Fin.prod_univ_four]
  simp [DegPre.famε]

end Normalised

section Omega

open GlobalTheory.UT GlobalTheory.UT.SymFrame

theorem grep_one {S X : Scheme.{0}} (L : LB X) (Y : Over S) : GRep L Y (fun _ _ _ => 1) (fun _ _ _ _ => 1) :=
  ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, Frames.oneGen_gen _,
    fun _ _ _ => by simp, fun _ _ _ _ _ => by simp [val_one]⟩

theorem grep_zpow {S X : Scheme.{0}} {L : LB X} {Y : Over S} {P v} (h : GRep L Y P v) (n : ℤ) :
    GRep L Y (fun U _ h => P U h ^ n) (fun T r z J => v T r z J ^ n) := by
  obtain ⟨m, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact (h.pow m).congr (fun _ _ _ => (zpow_natCast _ _).symm) (fun _ _ _ _ _ => (zpow_natCast _ _).symm)
  · exact (h.pow m).inv.congr (fun _ _ _ => by rw [zpow_neg, zpow_natCast]) (fun _ _ _ _ _ => by rw [zpow_neg, zpow_natCast])

theorem grep_prod {S X : Scheme.{0}} {L : LB X} {Y : Over S} {I : Type} (s : Finset I)
    {P : I → ∀ (U : Type) [CommGroup U], ((Y.left ⟶ X) → U) → U}
    {v : I → ∀ (T : Over S) (_ : T ⟶ Y) (z : T.left) (_ : (T.left ⟶ X) → L.ι), (T.left.presheaf.stalk z)ˣ}
    (h : ∀ i, GRep L Y (P i) (v i)) :
    GRep L Y (fun U _ h => ∏ i ∈ s, P i U h) (fun T r z J => ∏ i ∈ s, v i T r z J) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact (grep_one L Y).congr (fun _ _ _ => by simp) (fun _ _ _ _ _ => by simp)
  | insert a s ha ih =>
    exact ((h a).mul ih).congr (fun _ _ _ => by rw [Finset.prod_insert ha]) (fun _ _ _ _ _ => by rw [Finset.prod_insert ha])

theorem prod_pair {S : Scheme.{0}} {B T : Over S} [GrpObj B] [IsCommMonObj B] (x y : T ⟶ B) {U : Type} [CommGroup U]
    (h : (T.left ⟶ B.left) → U) :
    ∏ I : ULift.{0} (Finset (Fin 2)), h ((lift x y).left ≫ (psum B (x2 B) I.down).left) ^ ((-1 : ℤ) ^ (2 - I.down.card)) =
      (∏ k, h (lamPts x y k) ^ negε k)⁻¹ := by
  have e := GlobalTheory.PrimNorm.prod_square (lift x y) (fst B B) (snd B B) h
  rw [lift_fst, lift_snd] at e
  refine e.trans ?_
  rw [Fin.prod_univ_four]
  simp only [lamPts, negε, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.tail_cons, GlobalTheory.PrimNorm.diff₂, zpow_neg, zpow_one, mul_inv, inv_inv]

variable {V V₁ W₀ : Type} [CommRing V] [IsDomain V] [CommRing V₁] [IsDomain V₁] [CommRing W₀]
  (W : Matrix (Fin 8) (Fin 8) ℤ) (ρ : V →+* V₁) (Q : Data V) (D : DegPre V₁)
  (pr : Fin 8 → (D.P.A ⟶ (Over.pullback (spMap ρ)).obj Q.B)) (B₀ : Over (Sp W₀)) [GrpObj B₀] [IsCommMonObj B₀]
  (β₂ : (G2 Q.B).left ⟶ (G2 B₀).left)

abbrev piB (p : (Fin 8 × Fin 8) × PUnit × ULift.{0} (Finset (Fin 2))) : D.P.A.left ⟶ B₀.left :=
  sharpPair ρ Q D pr p.1.1 p.1.2 ≫ β₂ ≫ (psum B₀ (x2 B₀) p.2.2.down).left

abbrev exB (p : (Fin 8 × Fin 8) × PUnit × ULift.{0} (Finset (Fin 2))) : ℤ :=
  W p.1.1 p.1.2 * (1 * (-1) ^ (2 - p.2.2.down.card))

theorem formEq_sharp : FormEq (K := (Fin 8 × Fin 8) × Fin 4)
    (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))
    (fun p : (Fin 8 × Fin 8) × ULift.{0} (Finset (Fin 2)) =>
      sharpPair ρ Q D pr p.1.1 p.1.2 ≫ (psum Q.B (x2 Q.B) p.2.down).left)
    (fun p => W p.1.1 p.1.2 * (-1) ^ (2 - p.2.down.card)) := fun U _ h => by
  rw [Fintype.prod_prod_type, Fintype.prod_prod_type (α₁ := Fin 8 × Fin 8)]
  refine Finset.prod_congr rfl fun p _ => ?_
  have hP := isGrpPullback_pullback Q.B (spMap ρ)
  have e := prod_pair (pushPt hP.1.w (pr p.1)) (pushPt hP.1.w (pr p.2)) h
  have l : ∀ k, lamPts (pushPt hP.1.w (pr p.1)) (pushPt hP.1.w (pr p.2)) k =
      lamPts (pr p.1) (pr p.2) k ≫ pullback.fst Q.B.hom (spMap ρ) := fun k => by
    fin_cases k
    · exact hP.2 D.P.A (pr p.1) (pr p.2) _ _ rfl rfl
    · rfl
    · rfl
    · exact (congrArg (fun z => z.left) (map_one (pushHom hP D.P.A))).symm
  simp only [l] at e
  simp only [mul_comm (W p.1 p.2), zpow_mul, zpow_neg, Finset.prod_zpow, Finset.prod_inv_distrib]
  rw [← inv_zpow, ← e]
  rfl

theorem exists_omega
    (w : LB.Iso D.P.L (LB.LinComb Q.M.L (K := (Fin 8 × Fin 8) × Fin 4)
      (fun k => lamPts (pr k.1.1) (pr k.1.2) k.2 ≫ pullback.fst Q.B.hom (spMap ρ)) (fun k => -(W k.1.1 k.1.2 * negε k.2))))
    (hw : w.IsGen) (M₀ : LB B₀.left) (hM₀ : M₀.IsLB) (w₀ : LB.Iso (abelian₂ Q.B Q.M.L) ((abelian₂ B₀ M₀).pull β₂)) (hw₀ : w₀.IsGen) :
    ∃ u : LB.Iso D.P.L (LB.LinComb M₀ (piB ρ Q D pr B₀ β₂) (exB W)), u.IsGen ∧
      ∀ (Z : Scheme.{0}) (x : Z ⟶ D.P.A.left) (z : Z) J JQ J₀, Good D.P.L z J → Good Q.M.L z JQ → Good M₀ z J₀ →
        om u z J J₀ x = gm x z _ (w.s (fun k : (Fin 8 × Fin 8) × Fin 4 => JQ (x ≫ lamPts (pr k.1.1) (pr k.1.2) k.2 ≫
            pullback.fst Q.B.hom (spMap ρ)), J x)) *
          ∏ a, ∏ b, lamVal w₀ (x ≫ sharpPair ρ Q D pr a b) z J₀ JQ ^ W a b := by
  let c₁ := flatChart M₀ (fun I : ULift.{0} (Finset (Fin 2)) => (psum B₀ (x2 B₀) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (fun _ : PUnit => β₂) (fun _ => 1)
  let w₁ := TautFrom.isoPull (chartPullId _) c₁ w₀
  have hw₁ : w₁.IsGen := TautFrom.isoPull_isGen _ _ _ hw₀
  let c₂ := flatChart Q.M.L (fun I : ULift.{0} (Finset (Fin 2)) => (psum Q.B (x2 Q.B) I.down).left)
    (fun I => (-1) ^ (2 - I.down.card)) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)
  let c₃ := flatChart M₀ (fun p : PUnit × ULift.{0} (Finset (Fin 2)) => β₂ ≫ (psum B₀ (x2 B₀) p.2.down).left)
    (fun p => 1 * (-1) ^ (2 - p.2.down.card)) (fun p : Fin 8 × Fin 8 => sharpPair ρ Q D pr p.1 p.2) (fun p => W p.1 p.2)
  let w₂ := TautFrom.isoPull c₂ c₃ (LB.linCombIso w₁ _ _)
  have hw₂ : w₂.IsGen := TautFrom.isoPull_isGen _ _ _ (DVR.linCombIso_isGen w₁ hw₁ _ _)
  obtain ⟨u, hu, vu⟩ := exists_comp_form Q.M.isLB D.P.isLB (DVR.linComb_isLB _ hM₀ _ _) (formEq_sharp W ρ Q D pr) w hw w₂ hw₂
  refine ⟨u, hu, fun Z x z J JQ J₀ hJ hJQ hJ₀ => ?_⟩
  refine (vu Z x z JQ _ _ hJQ (hJ₀.mem _ x) (hJ x)).trans ((mul_comm _ _).trans (congrArg₂ (· * ·) rfl ?_))
  refine (isoV_isoPull _ _ _ x z _ _ (hJ₀.mem _ x) (hJQ.mem _ x)).trans ?_
  refine (isoV_linComb w₁ _ _ x z _ _ (c₃.le _ (hJ₀.mem _ x)) (c₂.le _ (hJQ.mem _ x))).trans ?_
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => Finset.prod_congr rfl fun b _ => congrArg (· ^ W a b) ?_
  refine (isoV_isoPull _ _ _ _ z _ _ (Set.mem_iInter.1 (c₃.le _ (hJ₀.mem _ x)) (a, b))
    (Set.mem_iInter.1 (c₂.le _ (hJQ.mem _ x)) (a, b))).trans ?_
  simp only [lamVal, Category.assoc]
  rfl

theorem piB_congr {β : Q.B.left ⟶ B₀.left} (hsq : IsSquare β β₂) (Z : Scheme.{0}) (x y : Z ⟶ D.P.A.left)
    (h : ∀ a, x ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β = y ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β)
    (i) : x ≫ piB ρ Q D pr B₀ β₂ i = y ≫ piB ρ Q D pr B₀ β₂ i := by
  have : x ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂ = y ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂ := by
    apply pullback.hom_ext
    · show (x ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂) ≫ (fst B₀ B₀).left =
        (y ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂) ≫ (fst B₀ B₀).left
      simp only [Category.assoc]
      rw [sharpPair_fst ρ Q D pr B₀ β β₂ hsq]
      exact h _
    · show (x ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂) ≫ (snd B₀ B₀).left =
        (y ≫ sharpPair ρ Q D pr i.1.1 i.1.2 ≫ β₂) ≫ (snd B₀ B₀).left
      simp only [Category.assoc]
      rw [sharpPair_snd ρ Q D pr B₀ β β₂ hsq]
      exact h _
  simpa only [Category.assoc] using congrArg (· ≫ (psum B₀ (x2 B₀) i.2.2.down).left) this

theorem exists_psi_gen {M₀ : LB B₀.left} (hM₀ : M₀.IsLB) {β : Q.B.left ⟶ B₀.left} (hsq : IsSquare β β₂)
    (u : LB.Iso D.P.L (LB.LinComb M₀ (piB ρ Q D pr B₀ β₂) (exB W))) (hu : u.IsGen)
    (g : Sp V₁ ⟶ Sp W₀) (c : 𝟙_ (Over (Sp V₁)) ⟶ D.P.A) (c₀ : Fin 8 → (𝟙_ (Over (Sp W₀)) ⟶ B₀))
    (hc : ∀ a, c.left ≫ (pr a).left ≫ pullback.fst Q.B.hom (spMap ρ) ≫ β = g ≫ (c₀ a).left)
    (τ₁ : ∀ a b, LB.Gen (LB.LinComb M₀ (lamPts (c₀ a) (c₀ b)) negε)) (hτ : ∀ a b, (τ₁ a b).IsGen) :
    ∃ t : LB.Gen (LB.LinComb D.P.L (K := PUnit) (fun _ => c.left) (fun _ => -1)), t.IsGen ∧
      ∀ (T : Over (Sp V₁)) (z : T.left) J J₀, Good D.P.L z J → Good M₀ z J₀ →
        val t (toUnit T).left z J = om u z J J₀ (toUnit T ≫ c).left * ∏ a, ∏ b, val (τ₁ a b) (T.hom ≫ g) z J₀ ^ W a b := by
  have G := grep_prod Finset.univ (fun p : Fin 8 × Fin 8 =>
    grep_zpow (grep_gen (Y := 𝟙_ (Over (Sp V₁))) (τ₁ p.1 p.2) (hτ p.1 p.2) g) (W p.1 p.2))
  have pe : ∀ a b, c.left ≫ sharpPair ρ Q D pr a b ≫ β₂ = g ≫ (lift (c₀ a) (c₀ b)).left := fun a b => by
    apply pullback.hom_ext
    · show (c.left ≫ sharpPair ρ Q D pr a b ≫ β₂) ≫ (fst B₀ B₀).left = (g ≫ (lift (c₀ a) (c₀ b)).left) ≫ (fst B₀ B₀).left
      simp only [Category.assoc]
      rw [sharpPair_fst ρ Q D pr B₀ β β₂ hsq, hc]
      exact congrArg (fun m => g ≫ m.left) (lift_fst (c₀ a) (c₀ b)).symm
    · show (c.left ≫ sharpPair ρ Q D pr a b ≫ β₂) ≫ (snd B₀ B₀).left = (g ≫ (lift (c₀ a) (c₀ b)).left) ≫ (snd B₀ B₀).left
      simp only [Category.assoc]
      rw [sharpPair_snd ρ Q D pr B₀ β β₂ hsq, hc]
      exact congrArg (fun m => g ≫ m.left) (lift_snd (c₀ a) (c₀ b)).symm
  obtain ⟨G₀, hG₀, vG⟩ := G.out hM₀ (fun p : PUnit × _ => c.left ≫ piB ρ Q D pr B₀ β₂ p.2) (fun p => -1 * exB W p.2)
    (fun U _ h => by
      refine Eq.symm ((Fintype.prod_prod_type _).trans ((Fintype.prod_unique _).trans ((Fintype.prod_prod_type _).trans
        (Finset.prod_congr rfl fun p _ => (Fintype.prod_prod_type _).trans ((Fintype.prod_unique _).trans (Eq.symm ?_))))))
      have e := prod_pair (c₀ p.1) (c₀ p.2) (fun ψ => h (g ≫ ψ))
      rw [← inv_inj, ← inv_zpow]
      erw [← e]
      rw [← Finset.prod_zpow, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun I _ => ?_
      rw [← zpow_mul, ← zpow_neg]
      congr 1
      · exact congrArg h (by simpa only [Category.assoc] using
          (congrArg (· ≫ (psum B₀ (x2 B₀) I.down).left) (pe p.1 p.2)).symm)
      · simp only [exB]; ring)
  obtain ⟨U, hU, vU⟩ := exists_transport u hu (fun _ : PUnit => c.left) (fun _ => -1)
  have hB := DVR.linComb_isLB M₀ hM₀ (fun p : PUnit × _ => c.left ≫ piB ρ Q D pr B₀ β₂ p.2) (fun p => -1 * exB W p.2)
  obtain ⟨s, hs⟩ := GlobalTheory.MBLow.lbIso_sec_onto _ _ _ U (DVR.linComb_isLB _ D.P.isLB _ _) hB hU (genSec G₀ hG₀)
  obtain ⟨t, ht, rfl⟩ := exists_gen_of_isoRel hB hG₀ (fun i k => hs (i, k))
  refine ⟨t, ht, fun T z J J₀ hJ hJ₀ => ?_⟩
  have e := vU _ _ (fun i k => hs (i, k)) _ (toUnit T).left z J J₀ hJ hJ₀
  rw [sval_genSec _ _ _ z hJ, sval_genSec _ _ _ z hJ₀, ← Units.val_mul, Fintype.prod_unique, zpow_neg, zpow_one,
    vG T _ z J₀ hJ₀, Fintype.prod_prod_type] at e
  exact (inv_mul_eq_iff_eq_mul.1 (Units.ext e).symm)

end Omega

end GlobalTheory.Poinc.Sep.Coef
