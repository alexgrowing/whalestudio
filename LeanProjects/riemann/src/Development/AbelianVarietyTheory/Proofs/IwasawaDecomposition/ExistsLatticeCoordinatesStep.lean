import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompGvec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRefinedCocycleEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvLinearCombination
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsCommonModOfIsDiag

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.DRFlag GlobalTheory.GrCl
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod (ev tanPull ev_res ev_appLE le_preimage_inf le_preimage_map le_preimage_mono)
open GlobalTheory.Twist (resM resM_resM app_resM)

namespace GlobalTheory.GrCl

section Frames

variable {X Z : Scheme.{0}} {F : X.Modules} {S : Type} [CommRing S]

def frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') : Matrix (Fin n) (Fin n') Γ(X, U) :=
  ((hm'.basis h').toMatrix (hm.basis h)).transpose

theorem frMat_self {V U : X.Opens} {n : ℕ} {m : Fin n → Γ(F, V)} (hm : VB.IsFrame m) (h : U ≤ V) :
    frMat hm hm h h = 1 := by
  rw [frMat, Module.Basis.toMatrix_self, Matrix.transpose_one]

theorem frMat_mul {V V' V'' U : X.Opens} {n n' n'' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')}
    {m'' : Fin n'' → Γ(F, V'')} (hm : VB.IsFrame m) (hm' : VB.IsFrame m') (hm'' : VB.IsFrame m'') (h : U ≤ V) (h' : U ≤ V')
    (h'' : U ≤ V'') : frMat hm hm' h h' * frMat hm' hm'' h' h'' = frMat hm hm'' h h'' := by
  rw [frMat, frMat, frMat, ← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix]

theorem resG_frMat {V V' U U' : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (e : U' ≤ U) (l : Fin n) (l' : Fin n') :
    resG X e (frMat hm hm' h h' l l') = frMat hm hm' (e.trans h) (e.trans h') l l' := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, VB.IsFrame.basis_apply]
  rw [← hm'.repr_resM h' e, resM_resM]

theorem sum_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (l : Fin n) :
    resM F h (m l) = ∑ l', frMat hm hm' h h' l l' • resM F h' (m' l') := by
  simp only [frMat, Matrix.transpose_apply, Module.Basis.toMatrix_apply, ← hm'.basis_apply h']
  rw [Module.Basis.sum_repr, hm.basis_apply]

theorem map_ev_frMat {V V' U : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)} {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m)
    (hm' : VB.IsFrame m') (h : U ≤ V) (h' : U ≤ V') (g : Z ⟶ X) {B : Z.Opens} (e : B ≤ g ⁻¹ᵁ (V ⊓ V')) (z : Sp S ⟶ Z)
    (hz : ⊤ ≤ z ⁻¹ᵁ B) (hU : ⊤ ≤ (z ≫ g) ⁻¹ᵁ U) :
    ((frMat hm hm' inf_le_left inf_le_right).map (g.appLE _ B e).hom).map (ev z B hz) =
      (frMat hm hm' h h').map (ev (z ≫ g) U hU) := by
  ext l l'
  refine (ev_appLE z g e hz (le_preimage_map g e hz) _).trans ?_
  rw [← ev_res (z ≫ g) (le_inf h h') hU, resG_frMat]
  rfl

def frameCoc (g : Z ⟶ X) {A : Type} (B : A → Z.Opens) (aff : ∀ α, IsAffineOpen (B α)) (cover : ∀ x : Z, ∃ α, x ∈ B α)
    {V : A → X.Opens} {n : A → ℕ} {m : ∀ α, Fin (n α) → Γ(F, V α)} (hm : ∀ α, VB.IsFrame (m α))
    (le : ∀ α, B α ≤ g ⁻¹ᵁ V α) : Coc Z where
  A := A
  B := B
  aff := aff
  cover := cover
  n := n
  T α β := (frMat (hm α) (hm β) inf_le_left inf_le_right).map
    (g.appLE _ _ (show B α ⊓ B β ≤ g ⁻¹ᵁ (V α ⊓ V β) from inf_le_inf (le α) (le β))).hom
  refl α S _ z h := by
    rw [map_ev_frMat (hm α) (hm α) le_rfl le_rfl g _ z _ (le_preimage_map g (le α) h), frMat_self]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  coc α β γ S _ z h₁ h₂ h₃ := by
    have hU : ⊤ ≤ (z ≫ g) ⁻¹ᵁ (V α ⊓ V β ⊓ V γ) := le_preimage_inf (le_preimage_inf (le_preimage_map g (le α) h₁)
      (le_preimage_map g (le β) h₂)) (le_preimage_map g (le γ) h₃)
    have a : V α ⊓ V β ⊓ V γ ≤ V α := inf_le_left.trans inf_le_left
    have b : V α ⊓ V β ⊓ V γ ≤ V β := inf_le_left.trans inf_le_right
    have c : V α ⊓ V β ⊓ V γ ≤ V γ := inf_le_right
    rw [map_ev_frMat (hm α) (hm β) a b g _ z _ hU, map_ev_frMat (hm β) (hm γ) b c g _ z _ hU,
      map_ev_frMat (hm α) (hm γ) a c g _ z _ hU, ← Matrix.map_mul, frMat_mul]

theorem isFrame_incl (N : VB.Sub F) {V U O : X.Opens} {n : ℕ} {m : Fin n → Γ(N.toMod, V)} (hm : VB.IsFrame m)
    (hO : ∀ U : X.Opens, U ≤ O → N.sec U = ⊤) (h : U ≤ V) (h' : U ≤ O) :
    VB.IsFrame fun l => resM F h (N.incl.app V (m l)) :=
  (hm.res h).map_of_linearEquiv
    (fun U' e => LinearEquiv.ofBijective (QCoh.appLinear N.incl U') ⟨N.incl_app_injective U', fun s =>
      N.mem_sec_iff.1 (by rw [hO U' (e.trans h')]; trivial)⟩)
    fun _ e l => (app_resM N.incl e _).trans (congrArg _ (app_resM N.incl h _))

end Frames

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Lin

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {x : Sp S ⟶ X} {V : X.Opens}

def tanLin (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) : TanM x t.G →ₗ[S] (Fin n → S) where
  toFun v l := tanEv t (isTan_tv v) h (s l)
  map_add' v w := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 2 (fun i => (tv (![v, w] i)).left) (fun i => isTan_tv _) ![1, 1] _
      (isTan_tv (v + w)) ((LieMet.isComb_iff _ _ _).2 (by simp)) (s l)
    simpa using this
  map_smul' a v := funext fun l => by
    have := GlobalTheory.LocM.tanEv_comb E H X t S x V h 1 (fun _ => (tv v).left) (fun _ => isTan_tv _) (fun _ => a) _
      (isTan_tv (a • v)) ((LieMet.isComb_iff (fun _ => v) _ _).2 (by simp)) (s l)
    simpa using this

theorem tanLin_apply (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) (l : Fin n) :
    tanLin t h s v l = tanEv t (isTan_tv v) h (s l) := rfl

theorem tanLin_tanOf (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V))
    {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) (l : Fin n) :
    tanLin t h s (tanOf hv) l = tanEv t hv h (s l) := rfl

theorem tanEv_sum_smul (h : ⊤ ≤ x ⁻¹ᵁ V) {v : Sp (DualNumber S) ⟶ t.G.left} (hv : IsTanAtG t x v) {n : ℕ}
    (a : Fin n → Γ(X, V)) (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) :
    tanEv t hv h (∑ l, a l • s l) = ∑ l, ev x V h (a l) * tanEv t hv h (s l) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have := tanEv_smul t hv h 0 0
    simpa using this
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, tanEv_add, tanEv_smul, ih]; rfl

theorem tanLin_tr {F : X.Modules} (θ : F ⟶ GlobalTheory.LieVB.omega t.G) {V' : X.Opens} {n n' : ℕ} {m : Fin n → Γ(F, V)}
    {m' : Fin n' → Γ(F, V')} (hm : VB.IsFrame m) (hm' : VB.IsFrame m') (h : ⊤ ≤ x ⁻¹ᵁ V) (h' : ⊤ ≤ x ⁻¹ᵁ V')
    (v : TanM x t.G) :
    ((frMat hm hm' inf_le_left inf_le_right).map (ev x _ (le_preimage_inf h h'))).mulVec
      (tanLin t h' (fun l => θ.app V' (m' l)) v) = tanLin t h (fun l => θ.app V (m l)) v := by
  funext l
  rw [tanLin_apply, ← tanEv_resM t _ (le_preimage_inf h h') inf_le_left, ← app_resM,
    sum_frMat hm hm' inf_le_left inf_le_right, map_sum]
  simp only [Scheme.Modules.Hom.app_smul, app_resM]
  rw [tanEv_sum_smul]
  simp only [tanEv_resM]
  rfl

theorem tanLin_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') {x' : Sp S' ⟶ X} (e : spMap φ ≫ x = x') (h : ⊤ ≤ x ⁻¹ᵁ V)
    (h' : ⊤ ≤ x' ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) (v : TanM x t.G) :
    tanLin t h' s (tanPull φ e v) = φ ∘ tanLin t h s v := by
  subst e
  exact funext fun l => GlobalTheory.LocM.tanEv_baseChange E H X t S x V h _ (isTan_tv v) S' φ _ h' (s l)

theorem tanLin_injective (h : ⊤ ≤ x ⁻¹ᵁ V) {n : ℕ} (s : Fin n → Γ(GlobalTheory.LieVB.omega t.G, V)) {U : X.Opens} (e : U ≤ V)
    (hU : ⊤ ≤ x ⁻¹ᵁ U) (hs : VB.IsFrame fun l => resM _ e (s l)) : Function.Injective (tanLin t h s) := fun v w hvw =>
  tan_ext ((GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x U hU n _ hs (tanLin t h s w)).unique
    ⟨isTan_tv v, fun l => (tanEv_resM t _ hU e _).trans (congrFun hvw l)⟩
    ⟨isTan_tv w, fun l => tanEv_resM t _ hU e _⟩)

end Lin

section Phi

variable {X X' X₀ Z : Scheme.{0}} {t : SAB H X} {t' : SAB H X'} {t₀ : SAB H X₀} {τ : X ⟶ X₀} {τ' : X' ⟶ X₀}
  (mu : SABMap t t₀ τ) (mu' : SABMap t' t₀ τ') {π : Z ⟶ X} {g : Z ⟶ X'} (e : g ≫ τ' = π ≫ τ)
  {S : Type} [CommRing S]

def tanTrans (z : Sp S ⟶ Z) : TanM (z ≫ π) t.G ≃ₗ[S] TanM (z ≫ g) t'.G :=
  (pushE mu (z ≫ π) rfl).trans
    (pushE mu' (z ≫ g) (by rw [Category.assoc, Category.assoc, e] : (z ≫ g) ≫ τ' = (z ≫ π) ≫ τ)).symm

theorem left_tanTrans (z : Sp S ⟶ Z) (v : TanM (z ≫ π) t.G) :
    (tv (tanTrans mu mu' e z v)).left ≫ mu'.φ = (tv v).left ≫ mu.φ :=
  congrArg (fun w => (tv w).left) ((pushE mu' (z ≫ g) _).apply_symm_apply (pushE mu (z ≫ π) rfl v))

theorem tanTrans_eq (z : Sp S ⟶ Z) (v : TanM (z ≫ π) t.G) (w : TanM (z ≫ g) t'.G)
    (h : (tv w).left ≫ mu'.φ = (tv v).left ≫ mu.φ) : tanTrans mu mu' e z v = w :=
  (pushE mu' (z ≫ g) rfl).injective (tan_ext ((left_tanTrans mu mu' e z v).trans h.symm))

theorem tanTrans_tanPull {S' : Type} [CommRing S'] (φ : S →+* S') (z : Sp S ⟶ Z) (z' : Sp S' ⟶ Z)
    (e₁ : spMap φ ≫ z ≫ π = z' ≫ π) (e₂ : spMap φ ≫ z ≫ g = z' ≫ g) (v : TanM (z ≫ π) t.G) :
    tanTrans mu mu' e z' (tanPull φ e₁ v) = tanPull φ e₂ (tanTrans mu mu' e z v) :=
  tanTrans_eq mu mu' e z' _ _ (by
    rw [FlagMod.tanPull_left, FlagMod.tanPull_left, Category.assoc, Category.assoc, left_tanTrans])

end Phi

theorem tv_comp_eq_of_isTrans {Dw : Datum H} {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ}
    {Y : LocalSystem Xo p W} {i₀ i : Idx H p} {Z : Mdl Y i₀} (hc : i.c.F ≤ Z.i.c.F) {τ τ₀ : (Y Z.i).X ⟶ (Y i).X}
    {mu : SABMap (Y Z.i).t (Y i).t τ} {mu₀ : SABMap (Y Z.i).t (Y i).t τ₀} (tr : LocM.IsTrans i Z.i τ mu)
    (tr₀ : LocM.IsTrans i Z.i τ₀ mu₀) {K : Type} [Field K] (z : Sp K ⟶ Z.X) (hz : Set.range z ⊆ Z.opn)
    (v : TanM (z ≫ Z.π) (Y Z.i).t.G) : (tv v).left ≫ mu.φ = (tv v).left ≫ mu₀.φ := by
  obtain ⟨c, φ, hφ⟩ := Z.exists_chart z hz
  obtain ⟨y, hy, -⟩ := CommonMod.exists_lift_chart Z hφ
  exact (TransUniq.trans_unique E H Dw Xo p W Y _ _ τ τ₀ mu mu₀ hc tr tr₀).2 K y _ _ (tv v).left
    (by rw [hy]; exact (isTan_tv v).1)

theorem exists_lCrd_isLat : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (Xo : ∀ l : Level H, Moduli Dw l) (p : ℕ) (W : ValuationSubring ℂ) (Y : LocalSystem Xo p W) (i₀ : Idx H p), p.Prime → (p : ℂ) ∈ W.nonunits → ∀ (t : Step Y i₀) (Z : Mdl Y i₀) (g : Z.X ⟶ t.B.X), IsMap Z t.B g → ∃ D : LCrd (Y Z.i) Z.π, IsLat t Z g D := by
  intro E _ _ _ H Dw Xo p W Y i₀ hp hW t Z g hg
  cases isEmpty_or_nonempty Z.X with
  | inl hZ =>
    let C : Coc Z.X := ⟨Empty, fun a => a.elim, fun a => a.elim, fun x => hZ.elim x, fun a => a.elim, fun a => a.elim,
      fun a => a.elim, fun a => a.elim⟩
    exact ⟨⟨C, 0, ⟨fun a => a.elim, fun a => a.elim, fun a => a.elim⟩, fun a => a.elim, fun a => a.elim, fun a => a.elim,
      fun a => a.elim⟩, fun a => a.elim⟩
  | inr hZ =>
    obtain ⟨x₀, hx₀⟩ := Z.dense.nonempty
    obtain ⟨τ₀, mu₀, -, tr₀, -⟩ := hg.2 (Z.X.residueField x₀) (Z.X.fromSpecResidueField x₀) (by
      rintro _ ⟨a, rfl⟩
      exact (Scheme.fromSpecResidueField_apply x₀ a).symm ▸ hx₀)
    have e := CommonMod.comp_π_eq hg tr₀
    choose V n m hV hm using fun x : Z.X => t.L.free (g x)
    choose B aff hB le using fun x : Z.X => QCoh.exists_affine_mem_le (U := g ⁻¹ᵁ V x) x (hV x)
    have := isDiscreteValuationRing_V Z.i.c W hp hW
    let C₀ := frameCoc g B aff (fun x => ⟨x, hB x⟩) hm le
    obtain ⟨Γ', a, D, aff', cover, le', N, ⟨Em⟩⟩ := Coc.exists_refine_emb _ Z.X _ (geoOf Z).proj C₀
    have lt : ∀ γ, D γ ≤ g ⁻¹ᵁ V (a γ) := fun γ => (le' γ).trans (le _)
    refine ⟨{ C := C₀.refine a D aff' cover le'
              N := N
              Em := Em
              crd := fun γ S _ z h => (tanLin t.B.t (le_preimage_map g (lt γ) h)
                fun l => t.L.N.incl.app _ (m (a γ) l)).comp (tanTrans mu₀ t.B.tMap e z).toLinearMap
              tr := fun γ δ S _ z hγ hδ v => ?_
              bc := fun γ S S' _ _ φ z z' ez h h' e' v => ?_
              inj := fun γ K _ z h hz => ?_ }, fun γ => ⟨V (a γ), m (a γ), lt γ, hm _, ?_⟩⟩
    · rw [C₀.refine_tr a D aff' cover le' γ δ z hγ hδ]
      refine Eq.trans (congrArg (Matrix.mulVec · _) (map_ev_frMat (hm _) (hm _) inf_le_left inf_le_right g _ z _
        (le_preimage_inf (le_preimage_map g (lt γ) hγ) (le_preimage_map g (lt δ) hδ)))) ?_
      exact tanLin_tr t.B.t t.L.N.incl (hm _) (hm _) _ _ _
    · have e₂ : spMap φ ≫ z ≫ g = z' ≫ g := by rw [← Category.assoc, ez]
      exact (congrArg _ (tanTrans_tanPull mu₀ t.B.tMap e φ z z' e' e₂ v)).trans (tanLin_tanPull t.B.t φ e₂ _ _ _ _)
    · have hO : ⊤ ≤ (z ≫ g) ⁻¹ᵁ t.B.genO := le_preimage_map g (CommonMod.preimage_genO g).ge
        fun y _ => CommonMod.mem_genO_of_mem_opn hp.ne_zero Z (hz ⟨y, rfl⟩)
      exact (tanLin_injective t.B.t _ _ inf_le_left (le_preimage_inf (le_preimage_map g (lt γ) h) hO)
        (isFrame_incl t.L.N (hm _) t.L.gen inf_le_left inf_le_right)).comp (tanTrans mu₀ t.B.tMap e z).injective
    · intro τ mu tr K _ z h hz v v' hv' h' hv l
      have u := tv_comp_eq_of_isTrans hg.1.2.1 tr tr₀ z hz v
      have := tanTrans_eq mu₀ t.B.tMap e z v (tanOf hv') (hv.trans u)
      exact (congrFun (congrArg (tanLin t.B.t (le_preimage_map g (lt γ) h)
        fun l => t.L.N.incl.app _ (m (a γ) l)) this) l).trans (tanLin_tanOf t.B.t _ _ hv' l)

end GlobalTheory.GrCl
