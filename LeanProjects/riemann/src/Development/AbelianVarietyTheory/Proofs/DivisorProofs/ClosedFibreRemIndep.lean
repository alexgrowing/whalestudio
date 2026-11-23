import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasDefect
import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidChart
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocDerKDesc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHeatOperatorGluedPullbackBundlePower
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeatRatio.Closed

open GlobalTheory.KS GlobalTheory.KS.GlueDer

theorem gs_stalk {Z Y : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : r z ∈ U) (a : Γ(Y, U)) :
    gs r z U a = (r.stalkMap z).hom (gs (𝟙 Y) (r z) U a) := by
  rw [gs_eq r z U h, gs_eq (𝟙 Y) (r z) U h]
  exact (Scheme.Hom.germ_stalkMap_apply r U z h a).symm

theorem exists_sval_stalk {X Y Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] (φ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y) (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    ∃ J', Good L (r z) J' ∧ ∀ s : LB.Sec (LB.LinComb L φ ε),
      sval s r z J = (r.stalkMap z).hom (sval s (𝟙 Y) (r z) J') := by
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) φ (fun k => J (r ≫ φ k)) (fun a b e => by rw [e])
    (fun k => hJ (r ≫ φ k))
  refine ⟨J', hJ', fun s => ?_⟩
  rw [sval_of s (𝟙 Y) (r z) J' (fun k => J (r ≫ φ k)) (fun k => by rw [Category.id_comp]; exact e k)]
  exact gs_stalk r z _ (hJ.mem φ r) _

section Op

variable {R : Type} [CommRing R] {G : Over (Sp R)} {n : ℕ} {X : Scheme.{0}} {m : G.left ⟶ X} {L : LB X}
  {dd : Fin n → Fld G.left} {D : R → R} (h : Heat G m L dd D) (hdd : ∀ a, IsField ⊤ (dd a))
include hdd

theorem rsT_op (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) (f : Γ(G.left, h.W i)) :
    rsT (op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k (h.W i) f) O =
      op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (rsT f O) := by
  have hd : ∀ g, resG G.left hO (h.d i (h.W i) g) = h.d i O (resG G.left hO g) :=
    fun g => ((h.lift i).1.2.2 (h.W i) O hO le_rfl g).symm
  have hdd' : ∀ a g, resG G.left hO (dd a (h.W i) g) = dd a O (resG G.left hO g) :=
    fun a g => ((hdd a).2.2 (h.W i) O hO le_top g).symm
  have hc : ∀ r, resG G.left hO (constFn G.hom (h.W i) r) = constFn G.hom O r :=
    fun r => res_const G.hom hO r
  have hp : ∀ q : Γ(G.left, h.W i), resG G.left hO (rsT q (h.W i)) = rsT q O := fun q => by
    rw [← rsT_of_le hO, rsT_rsT le_rfl hO]
  rw [rsT_of_le hO, rsT_of_le hO]
  simp only [op, map_add, map_sub, map_mul, map_sum, map_pow, map_natCast, map_ofNat, hd, hdd', hc, hp]

theorem rem_eq (k : ℕ) (i : h.J) (O : G.left.Opens) (hO : O ≤ h.W i) {A : Type} [CommRing A] (π : Γ(G.left, O) →+* A)
    (hΘ : ∀ a b, π (constFn G.hom O (h.Θ a b)) = 0) (F T g : Γ(G.left, O)) (hT : IsUnit T)
    (e : op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O (F * T) =
      F * op G dd h.Θ h.u (h.d i) (h.p i) (h.p' i) k O T + g * T) :
    π g - 2 * (k : A) * π (h.d i O F) = 2 * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
  have e₁ := congrArg π e
  have hs : ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O (F * T)) =
      π F * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O T) + π T * ∑ a, π (constFn G.hom O (h.u a)) * π (dd a O F) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [(hdd a).2.1 O le_top, map_add, map_mul, map_mul]
    ring
  simp only [op, map_add, map_sub, map_mul, map_sum, hΘ, zero_mul, Finset.sum_const_zero, sub_zero, map_ofNat, map_pow,
    map_natCast] at e₁
  rw [hs, (h.lift i).1.2.1 O hO, map_add, map_mul, map_mul] at e₁
  refine (hT.map π).mul_left_cancel ?_
  linear_combination -e₁

end Op

section Ray

variable {R : Type} [CommRing R] [IsDomain R] {Q : DegPre R} {O : Type} [CommRing O] [StarRing O] [Module O Q.X]
  {oa : Q.OAct O} (Y : Ray oa) {n : ℕ} {dd : Fin n → Fld Y.H.left} {D : R → R} (h : Heat Y.H Y.q.left Q.P.L dd D)

theorem exists_term_germ (N : ℕ) (β : Q.X) (j : Q.P.L.ι) (V : Y.H.left.Opens) (hV : V ≤ Y.q.left ⁻¹ᵁ Q.P.L.U j)
    (y : Y.H.left) (hy : y ∈ V) : ∃ (J' : (Q.P.A.left ⟶ Q.P.A.left) → Q.P.L.ι) (c : (Y.H.left.presheaf.stalk y)ˣ),
      Good Q.P.L (Y.q.left y) J' ∧ ∀ σ τ, IsTerm Y N β σ τ →
        gs (𝟙 _) y V (rsT (τ.f fun _ => j) V) = (Y.q.left.stalkMap y).hom (sval σ (𝟙 _) (Y.q.left y) J') * c.val := by
  obtain ⟨J, hJ, e⟩ := exists_good Q.P.L Q.P.isLB y (K := Unit) (fun _ => Y.q.left) (fun _ => j) (fun _ _ _ => rfl)
    (fun _ => hV hy)
  obtain ⟨J', hJ', e'⟩ := exists_sval_stalk Q.P.isLB (DegPre.famφB Q β) (DegPre.famε N) Y.q.left y hJ
  refine ⟨J', val ((Y.Φ Y.H (𝟙 _)).s β) (𝟙 _) y J, hJ', fun σ τ hτ => ?_⟩
  have h1 := hτ Y.H (𝟙 _) y J hJ
  rw [Category.id_comp, e'] at h1
  refine Eq.trans ?_ h1
  have hle : V ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => j) := Glue.le_wchart _ hV
  refine Eq.trans ?_ (sval_of τ (𝟙 _) y J (fun _ => j) (fun _ => by rw [Category.id_comp]; exact e ())).symm
  exact (congrArg (gs (𝟙 _) y V) (rsT_of_le hle _)).trans (gs_res (𝟙 _) y hle hy _)

theorem rem_chart (hdd : ∀ a, IsField ⊤ (dd a)) (N : ℕ) (β : Q.X) (σ σ' σp σp' : Q.SecB N β) (U : Q.P.A.left.Opens)
    (f g : Γ(Q.P.A.left, U)) (hr : IsRatio Q σ σ' U f) (h₁ : TActs Y h N β σ σp) (h₂ : TActs Y h N β σ' σp')
    (hg : IsRem Q σ' σp σp' U f g) (i : h.J) (W : Q.P.A.left.Opens) (hWU : W ≤ U) (hW : Y.q.left ⁻¹ᵁ W ≤ h.W i)
    {A : Type} [CommRing A] (π : Γ(Y.H.left, Y.q.left ⁻¹ᵁ W) →+* A)
    (hΘ : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0) :
    π ((Y.q.left.app W).hom (resG _ hWU g)) - 2 * (N : A) * π (h.d i _ ((Y.q.left.app W).hom (resG _ hWU f))) =
      2 * ∑ a, π (constFn Y.H.hom _ (h.u a)) * π (dd a _ ((Y.q.left.app W).hom (resG _ hWU f))) := by
  obtain ⟨τ, τp, t₁, t₂, a₁⟩ := h₁
  obtain ⟨τ', τp', t₃, t₄, a₂⟩ := h₂
  have hV := hW.trans (h.le i)
  have hWc : h.W i ≤ LB.wchart Q.P.L (fun _ : Fin 1 => Y.q.left) (fun _ => h.j i) := Glue.le_wchart _ (h.le i)
  have hfn : ∀ y ∈ Y.q.left ⁻¹ᵁ W, ∀ x : Γ(Q.P.A.left, U),
      gs (𝟙 _) y (Y.q.left ⁻¹ᵁ W) ((Y.q.left.app W).hom (resG _ hWU x)) =
        (Y.q.left.stalkMap y).hom (gs (𝟙 _) (Y.q.left y) U x) := fun y hy x => by
    rw [gs_pull (𝟙 _) Y.q.left y W hy, Category.id_comp]
    exact (gs_res Y.q.left y hWU hy x).trans (gs_stalk _ y U (hWU hy) x)
  have act : ∀ {s s' : SecM Y.q.left Q.P.L N}, h.Acts N s s' → rsT (s'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      op Y.H dd h.Θ h.u (h.d i) (h.p i) (h.p' i) N _ (rsT (s.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) := fun {s s'} a => by
    have := congrArg (fun x => rsT x (Y.q.left ⁻¹ᵁ W)) (a i)
    simp only [rsT_op h hdd N i _ hW] at this
    exact (rsT_rsT hWc hW _).symm.trans (this.trans (congrArg _ (rsT_rsT hWc hW _)))
  have e₁ : rsT (τ.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, e σ τ t₁, e σ' τ' t₃, (hr _ (hWU hy) J' hJ').2, map_mul, _root_.mul_assoc]
  have e₂ : rsT (τp.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) =
      (Y.q.left.app W).hom (resG _ hWU f) * rsT (τp'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) +
      (Y.q.left.app W).hom (resG _ hWU g) * rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W) := fn_ext fun y hy => by
    obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
    rw [gs_add (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, gs_mul (𝟙 _) y (Y.q.left ⁻¹ᵁ W) hy, hfn y hy, hfn y hy, e σp τp t₂, e σ' τ' t₃, e σp' τp' t₄,
      hg _ (hWU hy) J' hJ', map_add, map_mul, map_mul]
    ring
  have hu : IsUnit (rsT (τ'.f fun _ => h.j i) (Y.q.left ⁻¹ᵁ W)) :=
    Y.H.left.toRingedSpace.isUnit_of_isUnit_germ _ _ fun y hy => by
      obtain ⟨J', c, hJ', e⟩ := exists_term_germ Y N β (h.j i) _ hV y hy
      exact (congrArg IsUnit ((gs_eq (𝟙 _) y _ hy _).symm.trans (e σ' τ' t₃))).mpr
        (((hr _ (hWU hy) J' hJ').1.map _).mul c.isUnit)
  refine rem_eq h hdd N i _ hW π hΘ _ _ _ hu ?_
  rw [← e₁, ← act a₁, ← act a₂, e₂]

theorem rem_indep (hdd : ∀ a, IsField ⊤ (dd a)) (hB : IsBasic Y h) {K : Type} [Field K] (φ : R →+* K)
    (hΘ : ∀ a b, φ (h.Θ a b) = 0) {Z : Scheme.{0}} (p : Z ⟶ Sp K) (m : Z ⟶ Q.P.A.left)
    (hm : m ≫ Q.P.A.hom = p ≫ spMap φ) (dl : ∀ W : Q.P.A.left.Opens, Γ(Q.P.A.left, W) → Γ(Z, m ⁻¹ᵁ W)) {D' : R → K}
    (hdl : LocDerK p Q.P.A.hom m D' ⊤ dl)
    (desc : ∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ Z), a ≫ Y.q.left = b ≫ m →
      ∀ (i : h.J) (W : Q.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m ⁻¹ᵁ W)) =
        pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m ⁻¹ᵁ W)))
    (N₁ N₂ : ℕ) (β₁ β₂ : Q.X) (σ σ' σp σp' : Q.SecB N₁ β₁) (ρ ρ' ρp ρp' : Q.SecB N₂ β₂) (U : Q.P.A.left.Opens)
    (f g₁ g₂ : Γ(Q.P.A.left, U)) (r₁ : IsRatio Q σ σ' U f) (r₂ : IsRatio Q ρ ρ' U f)
    (h₁ : TActs Y h N₁ β₁ σ σp) (h₂ : TActs Y h N₁ β₁ σ' σp') (h₃ : TActs Y h N₂ β₂ ρ ρp) (h₄ : TActs Y h N₂ β₂ ρ' ρp')
    (e₁ : IsRem Q σ' σp σp' U f g₁) (e₂ : IsRem Q ρ' ρp ρp' U f g₂) :
    (m.app U).hom g₁ - 2 * (N₁ : Γ(Z, m ⁻¹ᵁ U)) * dl U f = (m.app U).hom g₂ - 2 * (N₂ : Γ(Z, m ⁻¹ᵁ U)) * dl U f := by
  have := Y.smooth_q
  have hs := (AbConst.surjective_q Y).1
  choose V hV using fun i => (hB i).1
  refine eq_of_rsT_eq (fun i => m ⁻¹ᵁ (U ⊓ V i)) (fun i => pre_mono m inf_le_left) (fun y hy => ?_) _ _ fun i => ?_
  · obtain ⟨x, hx⟩ := Y.q.left.surjective (m y)
    have hx' : x ∈ ⨆ i, h.W i := by rw [h.cover]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
    rw [hV] at hi
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨i, hy, hx ▸ hi⟩
  obtain ⟨W, hWe⟩ : ∃ W, W = U ⊓ V i := ⟨_, rfl⟩
  have hWU : W ≤ U := hWe.le.trans inf_le_left
  have hW : Y.q.left ⁻¹ᵁ W ≤ h.W i := (pre_mono _ (hWe.le.trans inf_le_right)).trans (hV i).ge
  rw [← hWe]
  have red : ∀ (N : ℕ) (g : Γ(Q.P.A.left, U)), rsT ((m.app U).hom g - 2 * (N : Γ(Z, m ⁻¹ᵁ U)) * dl U f) (m ⁻¹ᵁ W) =
      (m.app W).hom (resG _ hWU g) - 2 * (N : Γ(Z, m ⁻¹ᵁ W)) * dl W (resG _ hWU f) := fun N g => by
    rw [hdl.res U W hWU le_top, rsT_of_le (pre_mono m hWU), rsT_of_le (pre_mono m hWU), map_sub, map_mul, map_mul,
      map_natCast, map_ofNat, res_app m hWU]
  rw [red, red]
  let a := pullback.fst Y.q.left m
  let b := pullback.snd Y.q.left m
  have w : a ≫ Y.q.left = b ≫ m := pullback.condition
  have hle : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ a ⁻¹ᵁ (Y.q.left ⁻¹ᵁ W) := by
    rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
  let π := (a.appLE _ _ hle).hom
  have key : ∀ x, (b.app _).hom ((m.app W).hom x) = π ((Y.q.left.app W).hom x) := fun x => by
    have k : ∀ (c : pullback Y.q.left m ⟶ Q.P.A.left) (_ : c = b ≫ m) (hc : b ⁻¹ᵁ (m ⁻¹ᵁ W) ≤ c ⁻¹ᵁ W),
        (b.app _).hom ((m.app W).hom x) = (c.appLE W _ hc).hom x := by
      rintro _ rfl hc
      rw [Scheme.Hom.comp_appLE, Scheme.Hom.app_eq_appLE b]
      rfl
    rw [k _ w hle]
    exact congrArg (fun ψ => ψ.hom x) (Scheme.Hom.comp_appLE a Y.q.left W _ hle)
  have hc : ∀ r, π (constFn Y.H.hom _ r) = constFn (b ≫ p) _ (φ r) := fun r => by
    rw [← res_const (b ≫ p) hle, ← app_const φ Y.H.hom (b ≫ p) a (by
      rw [← Over.w Y.q, reassoc_of% w, hm, Category.assoc])]
    rfl
  have hΘ' : ∀ a b, π (constFn Y.H.hom _ (h.Θ a b)) = 0 := fun a b => by
    rw [hc, hΘ, constFn, map_zero, map_zero]
  have hd : ∀ x, (b.app _).hom (dl W x) = π (h.d i _ ((Y.q.left.app W).hom x)) := fun x => by
    have := desc _ a b w i W hW x
    rw [pbT, pbT, dif_pos le_rfl, dif_pos hle] at this
    rw [Scheme.Hom.app_eq_appLE b]
    exact this
  refine GlobalTheory.FunDescent.app_injective b _ ?_
  show (b.app _).hom _ = (b.app _).hom _
  simp only [map_sub, map_mul, map_natCast, map_ofNat, key, hd]
  exact (rem_chart Y h hdd N₁ β₁ σ σ' σp σp' U f g₁ r₁ h₁ h₂ e₁ i W hWU hW π hΘ').trans
    (rem_chart Y h hdd N₂ β₂ ρ ρ' ρp ρp' U f g₂ r₂ h₃ h₄ e₂ i W hWU hW π hΘ').symm

end Ray

theorem closed_fibre_rem_indep : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (k : Type) [Field k] [CharZero k] (m d : ℕ) (t : SAB H (Sp (ChartRing k m d))) (P : PELUnif (maximalIdeal (ChartRing k m d)) t) (gam : Fin m → LinearMap.BilinForm ℤ P.D.toPre.X), IsMonomial P.D.toPre (bdParam k m d) gam → LinearIndependent ℤ gam → (∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal) → letI := H.starRing; ∀ (Y : Ray P.oD) (n' : ℕ) (v' : Module.Basis (Fin n') (ChartRing k m d) (TanM (𝟙 (Sp (ChartRing k m d))) Y.H)) (dd : Fin n' → Fld Y.H.left), (∀ a, IsInv Y.H (v' a) (dd a)) → ∀ (D : Derivation ℤ (ChartRing k m d) (ChartRing k m d)) (q : Fin m → ChartRing k m d), (∀ i, D (bdParam k m d i) = q i * bdParam k m d i) → ∀ h : Heat Y.H Y.q.left P.D.toPre.P.L dd ⇑D, IsBasic Y h → (∀ a b, h.Θ a b ∈ maximalIdeal (ChartRing k m d)) → ∀ ρ : ChartRing k m d →+* DualNumber k, (∀ r, ρ r = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff r) + TrivSqZeroExt.inr (MvPowerSeries.constantCoeff (D r)))  → ∀ (A₀ : Over (Sp k)) (_ : GrpObj A₀) (m₀ : A₀.left ⟶ P.D.toPre.P.A.left), IsGrpPullback A₀ P.D.toPre.P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ dl : ∀ W : P.D.toPre.P.A.left.Opens, Γ(P.D.toPre.P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W), GlobalTheory.KS.LocDerK A₀.hom P.D.toPre.P.A.hom m₀ (fun r => (ρ r).snd) ⊤ dl → (∀ (Z' : Scheme.{0}) (a : Z' ⟶ Y.H.left) (b : Z' ⟶ A₀.left), a ≫ Y.q.left = b ≫ m₀ → ∀ (i : h.J) (W : P.D.toPre.P.A.left.Opens), Y.q.left ⁻¹ᵁ W ≤ h.W i → ∀ f, pbT b (dl W f) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W)) = pbT a (h.d i _ ((Y.q.left.app W).hom f)) (b ⁻¹ᵁ (m₀ ⁻¹ᵁ W))) → ∀ (N₁ N₂ : ℕ), 1 ≤ N₁ → 1 ≤ N₂ → ∀ (β₁ β₂ : P.D.toPre.X) (σ σ' σp σp' : P.D.toPre.SecB N₁ β₁) (ρ₂ ρ₂' ρp ρp' : P.D.toPre.SecB N₂ β₂) (U : P.D.toPre.P.A.left.Opens) (f g₁ g₂ : Γ(P.D.toPre.P.A.left, U)), GlobalTheory.HeatRatio.IsRatio P.D.toPre σ σ' U f → GlobalTheory.HeatRatio.IsRatio P.D.toPre ρ₂ ρ₂' U f → TActs Y h N₁ β₁ σ σp → TActs Y h N₁ β₁ σ' σp' → TActs Y h N₂ β₂ ρ₂ ρp → TActs Y h N₂ β₂ ρ₂' ρp' → GlobalTheory.HeatRatio.IsRem P.D.toPre σ' σp σp' U f g₁ → GlobalTheory.HeatRatio.IsRem P.D.toPre ρ₂' ρp ρp' U f g₂ → (m₀.app U).hom g₁ - 2 * (N₁ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f = (m₀.app U).hom g₂ - 2 * (N₂ : Γ(A₀.left, m₀ ⁻¹ᵁ U)) * dl U f := by
  intro E _ _ _ H k _ _ m d t P gam _ _ _
  letI := H.starRing
  intro Y n' v' dd hdd D q _ h hB hΘ ρ hρ A₀ _ m₀ hm dl hdl desc N₁ N₂ _ _ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂
    r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  refine rem_indep Y h (fun a => (hdd a).1) hB ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ) (fun a b => ?_) A₀.hom m₀
    hm.1.w dl hdl desc N₁ N₂ β₁ β₂ σ σ' σp σp' ρ₂ ρ₂' ρp ρp' U f g₁ g₂ r₁ r₂ h₁ h₂ h₃ h₄ e₁ e₂
  have h0 : MvPowerSeries.constantCoeff (h.Θ a b) = 0 := by
    by_contra hne
    exact hΘ a b (MvPowerSeries.isUnit_iff_constantCoeff.2 (Ne.isUnit hne))
  show (ρ (h.Θ a b)).fst = 0
  simp [hρ, h0]

end GlobalTheory.HeatRatio.Closed
