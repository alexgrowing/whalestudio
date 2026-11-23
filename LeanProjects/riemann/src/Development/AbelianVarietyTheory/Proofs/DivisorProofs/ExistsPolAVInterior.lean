import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniqueCoeffAffine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechGluingOfKodairaSpencerRelation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTranslateOfTangentVectorFibreToGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentOfFibrePullbackTangentAtChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupPullbackTangentVectorsCompat
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LogDerivativePrincipalPolarisationIndependent
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolAVPullbackOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open scoped CategoryTheory.Obj
open GlobalTheory.KS
open TrivSqZeroExt (inl inr)

attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KSUniq

variable {K : Type} [Field K]

theorem exists_isTransl_snd {A : Over (Sp K)} [GrpObj A] [IsCommMonObj A] {u : epsR K ⟶ A} (hu : IsTangent u)
    {dd : ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)} (hd : IsInvDer u dd) {S : Type} [CommRing S]
    (ψ : K →+* S) (x : Sp S ⟶ A.left) (hx : x ≫ A.hom = spMap ψ) :
    ∃ w, GlobalTheory.CechKS.IsTransl ψ x u w ∧ ∀ (O : A.left.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O) (f : Γ(A.left, O)),
      (valR w O f).snd = GlobalTheory.TangentOrigin.evalPt x O h (dd O f) := by
  letI : Algebra K (DualNumber S) := ((algebraMap S (DualNumber S)).comp ψ).toAlgebra
  let z : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    Over.homMk (spMap (algebraMap S (DualNumber S)) ≫ x) (by
      rw [Category.assoc, hx]
      show Spec.map _ ≫ Spec.map _ = Spec.map _
      rw [← Spec.map_comp]; rfl)
  let v' : ReciprocityTheory.ChartRestriction.G.Chart.sp (R₀ := K) (DualNumber S) ⟶ A :=
    ReciprocityTheory.ChartRestriction.G.Chart.spMap (GlobalTheory.SqZero.epsTo K (DualNumber.eps : DualNumber S) (by simp)) ≫ u
  have hv' : v'.left = spMap (dualMap ψ) ≫ u.left := by
    show Spec.map _ ≫ u.left = _
    congr 2
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    ext <;> simp [GlobalTheory.SqZero.epsTo, GlobalTheory.SqZero.dualTo_apply, dualMap, Algebra.ofId_apply,
      RingHom.algebraMap_toAlgebra, TrivSqZeroExt.algebraMap_eq_inl]
  refine ⟨(v' * z).left, ⟨z, v', rfl, hv', by rw [mul_comm]⟩, fun O h f => ?_⟩
  have hz : ⊤ ≤ z.left ⁻¹ᵁ O := fun p _ => h (Set.mem_univ _)
  obtain ⟨h', H⟩ := GlobalTheory.InvFieldBasis.evalPt_translate hu hd (DualNumber.eps : DualNumber S) (by simp) z O hz
  have e1 : valR (v' * z).left O f = GlobalTheory.TangentOrigin.evalPt (v' * z).left O h' f := by
    rw [valR, dif_pos h']; rfl
  have e2 : ∀ s, GlobalTheory.TangentOrigin.evalPt z.left O hz s = inl (GlobalTheory.TangentOrigin.evalPt x O h s) := fun s =>
    GlobalTheory.TangentOrigin.evalPt_spMap_comp (algebraMap S (DualNumber S)) x O h hz s
  rw [e1, H, e2, e2]
  simp

theorem exists_polAV_interior {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (Y : Model Xo c (RingHom.id c.F)) (x0 : Sp K ⟶ Y.X)
    (hx : ⊤ ≤ x0 ⁻¹ᵁ GlobalTheory.LogKS.interior Y) :
    ∃ (P₀ : Out.PolAV (Sp K)) (θ : P₀.A.left ⟶ Y.t.G.left), IsGrpPullback P₀.A Y.t.G x0 θ ∧
      LBIso P₀.L (Y.t.PP.L.pull θ) := by
  have hr : Set.range x0 ⊆ Set.range Y.j := by
    rintro _ ⟨p, rfl⟩
    exact hx (Set.mem_univ p)
  let y' := IsOpenImmersion.lift Y.j x0 hr
  have hy' : y' ≫ Y.j = x0 := IsOpenImmersion.lift_fac _ _ _
  obtain ⟨P, φ, -, hφ, hL, -⟩ := GlobalTheory.exists_polAV_pullback_of_isLocalRing E H _ Y.oF.t Y.oF.proper Y.oF.ample
    Y.oF.ktriv K y'
  have g1 : IsGrpPullback P.A Y.t.G (y' ≫ Y.j) (φ ≫ Y.m.φ) := hφ.comp Y.m.cart
  rw [hy'] at g1
  obtain ⟨w, hw, -⟩ := Y.m.lin
  have i1 : LBIso (Y.oF.t.PP.L.pull φ) (Y.t.PP.L.pull (φ ≫ Y.m.φ)) :=
    LBIso.chartPull (ReciprocityTheory.ChartRestriction.G.Geo.Tor.chartPullPull _ φ φ rfl)
      (chartPullSame _ (fun _ => φ ≫ Y.m.φ) (fun _ => Y.m.φ) (fun _ => 1) φ (fun _ => rfl)) ⟨w, hw⟩
  exact ⟨P, φ ≫ Y.m.φ, g1, LBIso.trans P.isLB (pull_isLB Y.oF.t.PP.isLB _) (pull_isLB Y.t.PP.isLB _) hL i1⟩

theorem valR_eq_evalPt {S : Type} [CommRing S] {Z : Scheme.{0}} (x : Sp S ⟶ Z) (O : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ O)
    (s : Γ(Z, O)) : valR x O s = GlobalTheory.TangentOrigin.evalPt x O h s := by
  rw [valR, dif_pos h]; rfl

theorem eq_of_evalPt_eq {Z : Scheme.{0}} {O : Z.Opens} (s s' : Γ(Z, O))
    (h : ∀ (S : Type) [CommRing S] (x : Sp S ⟶ Z) (hx : ⊤ ≤ x ⁻¹ᵁ O),
      GlobalTheory.TangentOrigin.evalPt x O hx s = GlobalTheory.TangentOrigin.evalPt x O hx s') : s = s' := by
  let J : Type := {V : Z.Opens // IsAffineOpen V ∧ V ≤ O}
  refine eq_of_rsT_eq (fun V : J => V.1) (fun V => V.2.2) (fun p hp => ?_) s s' fun V => ?_
  · obtain ⟨_, ⟨V, hV, rfl⟩, hpV, hle⟩ := Z.isBasis_affineOpens.exists_subset_of_mem_open hp O.isOpen
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨V, hV, hle⟩, hpV⟩
  obtain ⟨t, ht, et⟩ := GlobalTheory.TangentOrigin.exists_evalPt_eq V.2.1 (RingHom.id _)
  have ht' : ⊤ ≤ t ⁻¹ᵁ O := fun p hp => V.2.2 (ht hp)
  have e : ∀ a : Γ(Z, O), rsT a V.1 = GlobalTheory.TangentOrigin.evalPt t O ht' a := fun a => by
    rw [← GlobalTheory.TangentOrigin.evalPt_res t V.2.2 ht' ht, et, rsT_of_le V.2.2]; rfl
  rw [e, e, h _ t ht']

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X : Scheme.{0}}

theorem pull_diff (t : SAB H X) (V : X.Opens) (U : X.affineOpens) {n : ℕ}
    (v : Fin n → (Sp (DualNumber Γ(X, U.1)) ⟶ t.G.left)) (hv : ∀ a, IsTanAtG t (GlobalTheory.LogKS.chart U) (v a))
    (Θ : Matrix (Fin n) (Fin n) Γ(X, U.1)) {J : Type} (W : J → t.G.left.Opens) (j : J → t.PP.L.ι)
    (d : J → ∀ O : t.G.left.Opens, Γ(t.G.left, O) → Γ(t.G.left, O)) (hWj : ∀ i, W i ≤ t.PP.L.U (j i))
    (hdiff : ∀ (i i' : J) (O : t.G.left.Opens), O ≤ W i ⊓ W i' → ∀ (f : Γ(t.G.left, O))
      (S : Type) [CommRing S] (φ : Γ(X, U.1) →+* S) (g₀ : Sp S ⟶ t.G.left)
      (w : Fin n → (Sp (DualNumber S) ⟶ t.G.left)),
      g₀ ≫ t.G.hom = spMap φ ≫ GlobalTheory.LogKS.chart U → ⊤ ≤ g₀ ⁻¹ᵁ O → (∀ a, GlobalTheory.LogKS.IsTranslate t φ g₀ (v a) (w a)) →
      valR g₀ O (d i O f - d i' O f) =
        ∑ a, ∑ b, φ (Θ a b) *
          ((valR (w b) _ (t.PP.L.g (j i) (j i')).val).snd * valR g₀ _ (t.PP.L.g (j i) (j i'))⁻¹.val) *
          (valR (w a) O f).snd)
    (x0 : Sp K ⟶ X) (hU : ⊤ ≤ x0 ⁻¹ᵁ U.1) (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A] (m : A.left ⟶ t.G.left)
    (hm : IsGrpPullback A t.G x0 m) (u : Fin n → (epsR K ⟶ A))
    (hu : ∀ a, (u a).left ≫ m = spMap (dualMap (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ v a)
    (dd : Fin n → ∀ O : A.left.Opens, Γ(A.left, O) → Γ(A.left, O)) (hdd : ∀ a, IsInvDer (u a) (dd a))
    (φ : Fin n → C1 (fun i => m ⁻¹ᵁ t.PP.L.U i)) (hφ : IsDlog m t.PP.L dd φ)
    (i i' : J) (O : t.G.left.Opens) (hO : O ≤ W i ⊓ W i') (f : Γ(t.G.left, O)) :
    (m.app O).hom (d i O f - d i' O f) =
      ∑ a, (∑ b, constFn A.hom _ (GlobalTheory.FlagMod.ev x0 U.1 hU (Θ a b)) * rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) *
        dd a _ ((m.app O).hom f) := by
  have hut : ∀ a, IsTangent (u a) := GlobalTheory.CechKS.isTangent_of_fibre t U v hv x0 hU A m u hm hu
  have hOg : O ≤ t.PP.L.U (j i) ⊓ t.PP.L.U (j i') := fun p hp => ⟨hWj i (hO hp).1, hWj i' (hO hp).2⟩
  have hOg' : m ⁻¹ᵁ O ≤ m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i') := m.preimage_mono hOg
  refine eq_of_evalPt_eq _ _ fun S _ x hx => ?_
  let ψ : K →+* S := (Spec.preimage (x ≫ A.hom)).hom
  have hxA : x ≫ A.hom = spMap ψ := (Spec.map_preimage (x ≫ A.hom)).symm
  choose w hw hw' using fun a => exists_isTransl_snd (hut a) (hdd a) ψ x hxA
  have hbase : (x ≫ m) ≫ t.G.hom = spMap (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) ≫ GlobalTheory.LogKS.chart U := by
    rw [Category.assoc, hm.1.w, ← Category.assoc, hxA, GlobalTheory.Cris.spMap_comp (GlobalTheory.FlagMod.ev x0 U.1 hU), Category.assoc]
    exact congrArg _ (GlobalTheory.FlagMod.spMap_ev x0 U.2 hU).symm
  have key := hdiff i i' O hO f S (ψ.comp (GlobalTheory.FlagMod.ev x0 U.1 hU)) (x ≫ m) (fun a => w a ≫ m) hbase hx
    (fun a => GlobalTheory.CechKS.IsTransl.isTranslate_comp t x0 A m hm _ (v a) (u a) (hu a) ψ x hxA (w a) (hw a))
  have hxg : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) := fun p hp => hOg' (hx hp)
  have ev_g : ∀ b, (valR (w b ≫ m) _ (t.PP.L.g (j i) (j i')).val).snd *
      valR (x ≫ m) _ (t.PP.L.g (j i) (j i'))⁻¹.val =
      GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) := fun b => by
    have hp : ∀ (s : Γ(t.G.left, t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))),
        pbT m s (m ⁻¹ᵁ t.PP.L.U (j i) ⊓ m ⁻¹ᵁ t.PP.L.U (j i')) = (m.app _).hom s := fun s => by
      show pbT m s (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) = _
      rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
    have hxg' : ⊤ ≤ x ⁻¹ᵁ (m ⁻¹ᵁ (t.PP.L.U (j i) ⊓ t.PP.L.U (j i'))) := hxg
    have e1 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) := by
      have := congrArg (GlobalTheory.TangentOrigin.evalPt x _ hxg) (hφ b (j i) (j i'))
      rw [map_mul, hp] at this
      exact this
    have h0 : (m.app _).hom (t.PP.L.g (j i) (j i')).val * (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    have e2 : GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val) *
        GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = 1 :=
      calc _ = GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i')).val *
              (m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) := (map_mul _ _ _).symm
        _ = 1 := by rw [h0]; exact map_one _
    have e3 : GlobalTheory.TangentOrigin.evalPt x (m ⁻¹ᵁ O) hx (rsT (φ b (j i) (j i')) (m ⁻¹ᵁ O)) =
        GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i')) := by
      rw [rsT_of_le hOg', GlobalTheory.TangentOrigin.evalPt_res x hOg' hxg hx]
    rw [GlobalTheory.CechKS.valR_comp_app, GlobalTheory.CechKS.valR_comp_app, hw' b _ hxg', valR_eq_evalPt _ _ hxg', e3]
    show GlobalTheory.TangentOrigin.evalPt x _ hxg (dd b _ ((m.app _).hom (t.PP.L.g (j i) (j i')).val)) *
      GlobalTheory.TangentOrigin.evalPt x _ hxg ((m.app _).hom (t.PP.L.g (j i) (j i'))⁻¹.val) = _
    rw [← e1]
    linear_combination (GlobalTheory.TangentOrigin.evalPt x _ hxg (φ b (j i) (j i'))) * e2
  rw [GlobalTheory.CechKS.valR_comp_app, valR_eq_evalPt _ _ hx] at key
  rw [key, map_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [ev_g, GlobalTheory.CechKS.valR_comp_app (w a) m O f, hw' a _ hx, map_mul, GlobalTheory.TangentOrigin.evalPt_constFn,
    GlobalTheory.InvFieldBasis.evalPt_congr hxA ⊤ le_rfl le_rfl, GlobalTheory.TangentOrigin.evalPt_spMap]
  rfl

theorem coeff_id {A₀ : Over (Sp K)} [GrpObj A₀] {g : ℕ} {v : Fin g → (epsR K ⟶ A₀)}
    {dd : Fin g → ∀ O : A₀.left.Opens, Γ(A₀.left, O) → Γ(A₀.left, O)} (hs : Smooth A₀.hom) (hv : IsLieBasis v)
    (hd : ∀ a, IsInvDer (v a) (dd a)) {S : Scheme.{0}} (x₀ : Sp K ⟶ S) {X : Scheme.{0}} (p : X ⟶ S)
    (m : A₀.left ⟶ X) (H : IsPullback m A₀.hom p x₀) {U : S.Opens} (hU : IsAffineOpen U)
    (W₀ : X.Opens) (hW₀ : W₀ ≤ p ⁻¹ᵁ U) (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m ⁻¹ᵁ W))
    (hadd : ∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f')
    (hmul : ∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m.app W).hom f * d W f' + (m.app W).hom f' * d W f)
    (hrs : ∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m ⁻¹ᵁ W'))
    (hbase : ∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) :
    ∃! c : Fin g → Γ(A₀.left, m ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
      d W f = ∑ a, rsT (c a) _ * dd a (m ⁻¹ᵁ W) ((m.app W).hom f) := by
  have key : ∀ (y : A₀.left ⟶ A₀.left) (m' : A₀.left ⟶ X), y ≫ m = m' →
      ∀ (d : ∀ W : X.Opens, Γ(X, W) → Γ(A₀.left, m' ⁻¹ᵁ W)),
      (∀ W, W ≤ W₀ → ∀ f f', d W (f + f') = d W f + d W f') →
      (∀ W, W ≤ W₀ → ∀ f f', d W (f * f') = (m'.app W).hom f * d W f' + (m'.app W).hom f' * d W f) →
      (∀ W W' (h : W' ≤ W), W ≤ W₀ → ∀ f, d W' (resG X h f) = rsT (d W f) (m' ⁻¹ᵁ W')) →
      (∀ W, W ≤ W₀ → ∀ r : Γ(S, U), d W (pbT p r W) = 0) →
      ∃! c : Fin g → Γ(A₀.left, m' ⁻¹ᵁ W₀), ∀ W, W ≤ W₀ → ∀ f,
        d W f = ∑ a, rsT (c a) _ * pbT y (dd a (m ⁻¹ᵁ W) ((m.app W).hom f)) _ := by
    intro y m' e d h1 h2 h3 h4
    subst e
    exact existsUnique_coeff hs hv hd x₀ p m H hU y W₀ hW₀ d h1 h2 h3 h4
  have := key (𝟙 _) m (Category.id_comp _) d hadd hmul hrs hbase
  simpa only [GlobalTheory.KS.LinDir.pbT_id] using this

theorem app_resG {Y Z : Scheme.{0}} (m : Y ⟶ Z) {W W' : Z.Opens} (h : W' ≤ W) (s : Γ(Z, W)) :
    (m.app W').hom (resG Z h s) = rsT ((m.app W).hom s) (m ⁻¹ᵁ W') := by
  have e : ∀ {O : Z.Opens} (s : Γ(Z, O)), (m.app O).hom s = pbT m s (m ⁻¹ᵁ O) := fun s => by
    rw [pbT_of_le m le_rfl, Scheme.Hom.appLE_eq_app]
  rw [e, e, ← rsT_of_le h, pbT_rsT m h le_rfl, rsT_pbT m le_rfl (m.preimage_mono h)]

theorem field_base {X Z : Scheme.{0}} (π : Z ⟶ X) {U : X.Opens} (W₀ : Z.Opens) (hW₀ : W₀ ≤ π ⁻¹ᵁ U)
    (d : ∀ O : Z.Opens, Γ(Z, O) → Γ(Z, O)) (hf : GlobalTheory.LogKS.IsField W₀ d) (D : Γ(X, U) → Γ(X, U))
    (hl : ∀ (h : W₀ ≤ π ⁻¹ᵁ U) (r : Γ(X, U)), d W₀ ((π.appLE U W₀ h).hom r) = (π.appLE U W₀ h).hom (D r)) :
    ∀ W, W ≤ W₀ → ∀ r, d W (pbT π r W) = pbT π (D r) W := by
  intro W hW r
  have e : ∀ s : Γ(X, U), pbT π s W = resG Z hW (pbT π s W₀) := fun s => by
    rw [← rsT_of_le hW, rsT_pbT π hW₀ hW]
  rw [e, e, hf.2.2 W₀ W hW le_rfl, pbT_of_le π hW₀, pbT_of_le π hW₀, hl hW₀]

theorem isCoc_lc {Y : Scheme.{0}} {I : Type} {Uc : I → Y.Opens} (q : Y ⟶ Sp K) {g : ℕ} (c : Fin g → K)
    (φ : Fin g → C1 Uc) (h : ∀ a, IsCoc Uc (φ a)) : IsCoc Uc (lc q c φ) := by
  intro i j k
  simp only [lc, rsT_sum, rsT_mul, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [rsT_constFn q (O₀ := Uc i ⊓ Uc j) inf_le_left,
    rsT_constFn q (O₀ := Uc j ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.2, h.2⟩),
    rsT_constFn q (O₀ := Uc i ⊓ Uc k) (O := Uc i ⊓ Uc j ⊓ Uc k) (fun _ h => ⟨h.1.1, h.2⟩), ← mul_add, h a i j k]

theorem constFn_sub {Y : Scheme.{0}} (q : Y ⟶ Sp K) (O : Y.Opens) (x y : K) :
    constFn q O (x - y) = constFn q O x - constFn q O y := by
  simp [constFn]

end GlobalTheory.KSUniq
