import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentFrameAtFieldPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TangentBasisOfSplitTorsion
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalModelOverProjective
open CategoryTheory Limits AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.DV Formalism.L2.Pj Formalism.L2.Geo
open GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Vert GlobalTheory.LocM GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open Formalism.MainNotions.DIV.Cons (intO)

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TanSec.Norm

open GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.Conormal GlobalTheory.DualPull
open GlobalTheory.Twist (resM resM_resM resM_self app_resM resM_smul)

section Tan

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
  {X : Scheme.{0}} (t : SAB H X)

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem exists_tanEv_comb {k : Type} [CommRing k] {x : Sp k ⟶ X} {V : X.Opens} (hV : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ}
    {m : Fin n → Γ(omega t.G, V)} (hm : VB.IsFrame m) {r : ℕ} {u : Fin r → (Sp (DualNumber k) ⟶ t.G.left)}
    (hu : ∀ i, IsTanAtG t x (u i)) {c : Fin r → k} {v : Sp (DualNumber k) ⟶ t.G.left} (h : IsCombAtG t x u c v) :
    ∃ hv : IsTanAtG t x v, ∀ b, tanEv t hv hV (m b) = ∑ i, c i * tanEv t (hu i) hV (m b) := by
  obtain ⟨w, hw, hc⟩ := FlagEmb.exists_comb t hu c
  obtain rfl : w = v := FlagEmb.comb_unique t hu hc h
  obtain ⟨Φ, hΦ⟩ := TanPair.exists_tanM_equiv _ _ _ t k _ V hV n m hm
  have e := (LieMet.isComb_iff (fun i => LieMet.tanOf (hu i)) c (LieMet.tanOf hw)).1 h
  refine ⟨hw, fun b => (hΦ (LieMet.tanOf hw) b).symm.trans ?_⟩
  rw [e, map_sum, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, Pi.smul_apply, hΦ]
  rfl

open ReciprocityTheory.ChartRestriction.G.PullbackSections MonoidalCategory CartesianMonoidalCategory MonObj in
attribute [local instance] Over.cartesianMonoidalCategory in

theorem mem_latDR_iff_tanEv (hX : X.IsSeparated) {C : Type} [NontriviallyNormedField C] [IsUltrametricDist C]
    {xO : Sp ↥(intO C) ⟶ X} {x : Sp C ⟶ X} (hx : spMap (intO C).subtype ≫ xO = x) {V : X.Opens} (hO : ⊤ ≤ xO ⁻¹ᵁ V)
    (hV : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} {m : Fin n → Γ(omega t.G, V)} (hm : VB.IsFrame m)
    {v : Sp (DualNumber C) ⟶ t.G.left} (hv : IsTanAtG t x v) :
    v ∈ latDR t x ↔ ∀ b, tanEv t hv hV (m b) ∈ intO C := by
  subst hx
  constructor
  · rintro ⟨xO', hx', vO, hvO, rfl⟩ b
    obtain rfl := HTPres.ext_uniq hX C _ _ hx'
    rw [GlobalTheory.LocM.tanEv_baseChange _ _ _ t _ _ V hO vO hvO C (intO C).subtype hv hV]
    exact Subtype.property _
  · intro hb
    obtain ⟨Φ, hΦ⟩ := TanPair.exists_tanM_equiv _ _ _ t _ _ V hO n m hm
    obtain ⟨Ψ, hΨ⟩ := TanPair.exists_tanM_equiv _ _ _ t _ _ V hV n m hm
    obtain ⟨q, hq⟩ := Φ.surjective fun b => ⟨_, hb b⟩
    have hq' := LieMet.isTan_map (intO C).subtype rfl (LieMet.isTan_tv q)
    refine ⟨xO, rfl, _, LieMet.isTan_tv q, ?_⟩
    have e : LieMet.tanOf hq' = LieMet.tanOf hv := Ψ.injective (funext fun b => by
      rw [hΨ, hΨ]
      refine (GlobalTheory.LocM.tanEv_baseChange _ _ _ t _ _ V hO _ (LieMet.isTan_tv q) C (intO C).subtype hq' hV _).trans ?_
      rw [← hΦ, hq]
      rfl)
    exact congrArg (fun z => (PullbackSections.tv z).left) e

end Tan

theorem exists_inv_pairing {X : Scheme.{0}} {P : X.Modules} {r n : ℕ} {V V' T : X.Opens} {ε : Fin r → Γ(dual P, V)}
    (hε : VB.IsFrame ε) {μ : Fin n → Γ(P, V')} (hμ : VB.IsFrame μ) (hT : T ≤ V) (hT' : T ≤ V') :
    ∃ B : Fin n → Fin r → Γ(X, T), ∀ l l', ∑ b, dualApp (ε l) hT (resM P hT' (μ b)) * B b l' =
      if l = l' then 1 else 0 := by
  refine ⟨fun b l' => (hε.basis hT).repr (hμ.dual.basis hT' b) l', fun l l' => ?_⟩
  have e := congrArg (fun s => (hε.basis hT).repr s l') ((hμ.dual.basis hT').sum_repr (hε.basis hT l))
  simp only [map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
    Module.Basis.repr_self, Finsupp.single_apply, IsFrame.dual_basis_repr] at e
  rw [← e]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [IsFrame.basis_apply hε, dualApp_res]

theorem forall_mem_iff {K : Type} [CommRing K] (O : Subring K) {r n : ℕ} (A : Fin r → Fin n → O) (B : Fin n → Fin r → O)
    (h : ∀ l l', ∑ b, A l b * B b l' = if l = l' then 1 else 0) (d : Fin r → K) :
    (∀ b, ∑ l, d l * (A l b : K) ∈ O) ↔ ∀ l, d l ∈ O := by
  refine ⟨fun H l => ?_, fun H b => O.sum_mem fun l _ => O.mul_mem (H l) (A l b).2⟩
  have h' (l l' : Fin r) : ∑ b, (A l b : K) * B b l' = if l = l' then 1 else 0 := by
    have := congrArg O.subtype (h l l')
    rw [map_sum, apply_ite O.subtype, map_one, map_zero] at this
    exact this
  have e : d l = ∑ b, (∑ l', d l' * (A l' b : K)) * B b l := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    simp only [mul_assoc, ← Finset.mul_sum, h']
    simp
  rw [e]
  exact O.sum_mem fun b _ => O.mul_mem (H b) (B b l).2

theorem mem_lat_iff_coef : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p) (Z : GlobalTheory.LocM.Mdl Y i₀) (X : Scheme.{0}) (h : X ⟶ Z.X) (r : ℕ) (x : Fin r → Letter Dw), Function.Bijective x → ∀ (hfr : ∀ a, GlobalTheory.VB.IsFrame (GlobalTheory.TanSec.secX Z h x a)) (y : Z.Pt) (w : Sp ↥(intO ↥y.C.S) ⟶ X), w ≫ h = y.z → ∀ (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* ↥y.C.S), spMap φ ≫ Z.chart a = y.gen → ∀ (V : X.Opens) (e : Fin r → Γ(GlobalTheory.TanSec.lieX Z h, V)) (he : GlobalTheory.VB.IsFrame e), ⊤ ≤ w ⁻¹ᵁ V → ∀ (cf : Fin r → ↥y.C.S) (v : Sp (DualNumber ↥y.C.S) ⟶ (Y Z.i).t.G.left), IsCombAtG (Y Z.i).t (y.gen ≫ Z.π) (fun i => (Z.fr a).bc φ (x i).1 (x i).2) cf v → (v ∈ lat (Y Z.i).t p (y.gen ≫ Z.π) false ↔ ∀ l, ‖∑ i, cf i * valF (spMap (intO ↥y.C.S).subtype ≫ w) _ (GlobalTheory.ChainPts.coef false he (hfr a) l i)‖ ≤ 1) := by
  intro E _ _ _ H Dw Xo p W Y i₀ Z X h r x _ hfr y w hw a φ hφ V e he hV cf v hv
  have := (Y Z.i).t.semi
  have := (Y Z.i).t.semi.smooth
  have := LatDRFree.intO_isLocalRing ↥y.C.S
  have hsep : (Y Z.i).X.IsSeparated := by
    have := CommonModel.isProper_of_isProjOver (Y Z.i).proj
    exact ⟨by rw [← terminal.comp_from (Y Z.i).s]; infer_instance⟩
  let ι := (intO ↥y.C.S).subtype
  let g : Sp ↥y.C.S ⟶ X := spMap ι ≫ w
  have hg : g ≫ h = y.gen := by rw [Category.assoc, hw]; rfl
  have hx : spMap ι ≫ w ≫ h ≫ Z.π = y.gen ≫ Z.π := by rw [← hg]; simp only [g, Category.assoc]
  have htan (i : Fin r) : IsTanAtG (Y Z.i).t (y.gen ≫ Z.π) ((Z.fr a).bc φ (x i).1 (x i).2) :=
    LieMet.isTan_map φ (by rw [← Category.assoc, hφ]) ((Z.frame a).1 _ _).1
  obtain ⟨V₀, n, m, hx₀, hm⟩ := exists_isFrame_omega (Y Z.i).t.G ((w ≫ h ≫ Z.π) (IsLocalRing.closedPoint _))
  have hO : ⊤ ≤ (w ≫ h ≫ Z.π) ⁻¹ᵁ V₀ := ((IsLocalRing.closedPoint_mem_iff _).1 hx₀).ge
  have hC : ⊤ ≤ (y.gen ≫ Z.π) ⁻¹ᵁ V₀ := hx ▸ fun q _ => hO (Set.mem_univ (spMap ι q))
  obtain ⟨hv', hev⟩ := exists_tanEv_comb _ hC hm htan hv
  refine (mem_latDR_iff_tanEv _ hsep hx hO hC hm hv').trans ?_

  have hom : ∀ z : Z.X, ∃ (U : Z.X.Opens) (n : ℕ) (s : Fin n → Γ(om Z, U)), z ∈ U ∧ VB.IsFrame s := fun z => by
    obtain ⟨U, n, s, hz, hs⟩ := exists_isFrame_omega (Y Z.i).t.G (Z.π z)
    exact ⟨_, n, _, hz, hs.pullback Z.π⟩
  have := OmegaGlobal.isQuasicoherent_of_frames hom
  have hθ := Glue.isIso_theta_om Z h
  let μ₀ : Fin n → Γ(om Z, Z.π ⁻¹ᵁ V₀) := fun b => pullbackSections Z.π _ le_rfl (m b)
  have hμ₀ : VB.IsFrame μ₀ := hm.pullback Z.π
  have hμ := hμ₀.pullback h
  have hε := @IsFrame.map_iso _ _ _ _ _ _ _ he (theta h (om Z)) hθ
  let T₁ : X.Opens := V ⊓ h ⁻¹ᵁ Z.π ⁻¹ᵁ V₀
  have hw₁ : ⊤ ≤ w ⁻¹ᵁ T₁ := le_inf hV hO
  obtain ⟨B, hB⟩ := exists_inv_pairing hε hμ (T := T₁) inf_le_left inf_le_right
  let ρ : Γ(X, T₁) →+* ↥(intO ↥y.C.S) := (Scheme.ΓSpecIso (.of ↥(intO ↥y.C.S))).hom.hom.comp (w.appLE T₁ ⊤ hw₁).hom
  let A : Fin r → Fin n → Γ(X, T₁) := fun l b => dualApp ((theta h (om Z)).app V (e l)) inf_le_left
    (resM _ inf_le_right (pullbackSections h (om Z) le_rfl (μ₀ b)))
  have hAB (l l' : Fin r) : ∑ b, ρ (A l b) * ρ (B b l') = if l = l' then 1 else 0 := by
    have := congrArg ρ (hB l l')
    rw [map_sum, apply_ite ρ, map_one, map_zero] at this
    simp only [map_mul] at this
    exact this
  refine Iff.trans (forall_congr' fun b => ?_) (forall_mem_iff (intO ↥y.C.S) _ _ hAB _)
  refine iff_of_eq (congrArg (· ∈ intO ↥y.C.S) ?_)

  let T : Z.X.Opens := (Z.U a).1 ⊓ Z.π ⁻¹ᵁ V₀
  have hgT : ⊤ ≤ y.gen ⁻¹ᵁ T := by
    refine fun q hq => ⟨?_, hC hq⟩
    rw [← hφ]
    exact (chart_image_top Z a).le ⟨spMap φ q, trivial, rfl⟩
  let T₂ : X.Opens := V ⊓ h ⁻¹ᵁ T
  have hg₂ : ⊤ ≤ g ⁻¹ᵁ T₂ := fun q hq => ⟨hV (Set.mem_univ (spMap ι q)), (le_preimage_of_comp hg).2 hgT hq⟩
  have h₂ : T₂ ≤ V ⊓ h ⁻¹ᵁ (Z.U a).1 := inf_le_inf_left _ (h.preimage_mono inf_le_left)
  have h₂₁ : T₂ ≤ T₁ := inf_le_inf_left _ (h.preimage_mono inf_le_right)
  let μ : Γ(om Z, T) := pullbackSections Z.π _ inf_le_right (m b)
  let ν : Γ((Scheme.Modules.pullback h).obj (om Z), T₂) := pullbackSections h (om Z) inf_le_right μ
  have hL (i : Fin r) : (Scheme.ΓSpecIso (.of ↥y.C.S)).hom (g.appLE T₂ ⊤ hg₂ (dualApp ((theta h (om Z)).app _
      (resM (lieX Z h) inf_le_right (secX Z h x a i))) h₂ ν)) = tanEv _ (htan i) hC (m b) := by
    have e : resM _ (inf_le_right : V ⊓ h ⁻¹ᵁ (Z.U a).1 ≤ _) (secX Z h x a i) =
        pullbackSections h _ inf_le_right (TanSec.sec Z a (Z.fr a (x i).1 (x i).2)) :=
      res_pullbackSections h _ _ _ _
    rw [e]
    refine Eq.trans (congrArg (Scheme.ΓSpecIso (.of ↥y.C.S)).hom ?_) (Glue.appLE_dualApp_sec Z a ((Z.frame a).1 _ _).1 φ
      hφ rfl (htan i) hC (m b) inf_le_left inf_le_right hgT)
    exact (congrArg (g.appLE _ ⊤ hg₂) (dualApp_theta h _ inf_le_left inf_le_right h₂ inf_le_right μ)).trans
      (appLE_appLE hg _ _ _ _)
  have hA (l : Fin r) : (Scheme.ΓSpecIso (.of ↥y.C.S)).hom (g.appLE T₂ ⊤ hg₂ (dualApp ((theta h (om Z)).app _
      (resM (lieX Z h) inf_le_left (e l))) h₂ ν)) = (ρ (A l b) : ↥y.C.S) := by
    have e₁ : ν = resM _ h₂₁ (resM _ inf_le_right (pullbackSections h (om Z) le_rfl (μ₀ b))) := by
      have e₀ : μ = resM _ inf_le_right (μ₀ b) := (res_pullbackSections Z.π _ _ _ _).symm
      rw [resM_resM]
      refine Eq.trans ?_ (res_pullbackSections h _ _ _ _).symm
      exact (congrArg _ e₀).trans (pullbackSections_res h _ _ _ _)
    have e₂ : dualApp ((theta h (om Z)).app _ (resM (lieX Z h) inf_le_left (e l))) h₂ ν = resG X h₂₁ (A l b) := by
      refine (congrArg (fun s => dualApp s h₂ ν) (app_resM (theta h (om Z)) inf_le_left (e l))).trans ?_
      rw [e₁]
      exact dualApp_resM _ inf_le_left h₂₁ _
    rw [e₂, appLE_resG, ← appLE_appLE (f := spMap ι) (g := w) rfl hw₁ (le_preimage_top _ _)]
    refine (congrArg (Scheme.ΓSpecIso (.of ↥y.C.S)).hom (appLE_top (spMap ι) _)).trans ?_
    exact congr($(Scheme.ΓSpecIso_naturality (CommRingCat.ofHom ι)) _)
  rw [hev b]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine (congrArg (cf i * ·) ((hL i).symm.trans
    (Glue.val_eq_sum_coef (F := lieX Z h) (theta h (om Z)) he (hfr a) g h₂ hg₂ ν i))).trans ?_
  refine (Finset.mul_sum _ _ _).trans (Finset.sum_congr rfl fun l _ => ?_)
  exact (congrArg (cf i * ·) (congrArg (_ * ·) (hA l))).trans (mul_assoc _ _ _).symm

end GlobalTheory.TanSec.Norm
