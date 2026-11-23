import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwoChartAtlas.TwoChartSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg

noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj MvPowerSeries
open ReciprocityTheory.ChartRestriction.G.Chart ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Out (rosatiφ rosatiε)
open ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.WickVanishing
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.JetSer.FrameChange

section Val
variable {A : Type} [CommRing A] {X Y : Scheme.{0}}

def evH (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) : Γ(X, U) →+* A :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom.comp (p.appLE U ⊤ h).hom

theorem fnVal_eq (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)) :
    fnVal p U f = evH p U h f := by
  unfold fnVal
  rw [dif_pos h]
  rfl

theorem evH_res (p : Spec (CommRingCat.of A) ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U) (h' : ⊤ ≤ p ⁻¹ᵁ V)
    (f : Γ(X, V)) : evH p U h ((X.presheaf.map (homOfLE hUV).op).hom f) = evH p V h' f := by
  unfold evH
  have := Scheme.Hom.map_appLE p h (homOfLE hUV).op
  simp only [RingHom.comp_apply]
  congr 1
  rw [← this]
  rfl

theorem evH_pull (p : Spec (CommRingCat.of A) ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ (q ⁻¹ᵁ V))
    (h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V) (f : Γ(X, V)) : evH p _ h ((q.app V).hom f) = evH (p ≫ q) V h' f := by
  unfold evH
  simp only [RingHom.comp_apply]
  congr 1

open Classical in

def uv (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) : Γ(X, U)ˣ →* Aˣ :=
  if h : ⊤ ≤ p ⁻¹ᵁ U then Units.map (evH p U h : Γ(X, U) →* A) else 1

theorem fnVal_unit (p : Spec (CommRingCat.of A) ⟶ X) (U : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ U) (f : Γ(X, U)ˣ) :
    fnVal p U f.val = (uv p U f).val := by
  unfold uv
  rw [dif_pos h, fnVal_eq p U h]
  rfl

theorem uv_res (p : Spec (CommRingCat.of A) ⟶ X) {U V : X.Opens} (hUV : U ≤ V) (h : ⊤ ≤ p ⁻¹ᵁ U)
    (f : Γ(X, V)ˣ) : uv p U (res hUV f) = uv p V f := by
  have h' : ⊤ ≤ p ⁻¹ᵁ V := fun z hz => hUV (h hz)
  apply Units.ext
  rw [← fnVal_unit p U h, ← fnVal_unit p V h', fnVal_eq p U h, fnVal_eq p V h']
  exact evH_res p hUV h h' _

theorem uv_pull (p : Spec (CommRingCat.of A) ⟶ Y) (q : Y ⟶ X) (V : X.Opens) (h : ⊤ ≤ p ⁻¹ᵁ (q ⁻¹ᵁ V))
    (f : Γ(X, V)ˣ) : uv p _ (pullU q V f) = uv (p ≫ q) V f := by
  have h' : ⊤ ≤ (p ≫ q) ⁻¹ᵁ V := h
  apply Units.ext
  rw [← fnVal_unit p _ h, ← fnVal_unit _ V h', fnVal_eq p _ h, fnVal_eq _ V h']
  exact evH_pull p q V h h' _

def hv (L : LB X) (j j' : L.ι) (ψ : Spec (CommRingCat.of A) ⟶ X) : Aˣ := uv ψ _ (L.g j j')

theorem uv_linComb (L : LB X) (j j' : L.ι) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j'))) :
    uv p _ ((LB.LinComb L φ ε).g (fun _ => j) (fun _ => j')) = ∏ k, hv L j j' (p ≫ φ k) ^ ε k := by
  refine (map_prod (uv p _) _ _).trans (Finset.prod_congr rfl fun k _ => ?_)
  refine (map_zpow (uv p _) _ _).trans ?_
  congr 1
  refine (uv_res p _ h _).trans ?_
  refine uv_pull p (φ k) (L.U j ⊓ L.U j') (fun z hz => ?_) (L.g j j')
  exact ⟨LB.wchart_le L φ (fun _ => j) k (h hz).1, LB.wchart_le L φ (fun _ => j') k (h hz).2⟩

theorem gen_change (L : LB X) (j j' : L.ι) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Gen (LB.LinComb L φ ε)) (ht : t.IsGen) (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j)) (h' : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j')) :
    uv p _ (t.s (fun _ => j)) = (∏ k, hv L j j' (p ≫ φ k) ^ ε k) * uv p _ (t.s (fun _ => j')) := by
  have h2 : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j')) :=
    fun z hz => ⟨h hz, h' hz⟩
  have := congrArg (uv p _) (ht (fun _ => j) (fun _ => j'))
  rwa [map_mul, uv_res p _ h2, uv_res p _ h2, uv_linComb L j j' φ ε p h2] at this

theorem sec_change (L : LB X) (j j' : L.ι) {K : Type} [Fintype K] (φ : K → (Y ⟶ X)) (ε : K → ℤ)
    (t : LB.Sec (LB.LinComb L φ ε)) (p : Spec (CommRingCat.of A) ⟶ Y)
    (h : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j)) (h' : ⊤ ≤ p ⁻¹ᵁ (LB.LinComb L φ ε).U (fun _ => j')) :
    fnVal p _ (t.f (fun _ => j)) = (∏ k, hv L j j' (p ≫ φ k) ^ ε k).val * fnVal p _ (t.f (fun _ => j')) := by
  have h2 : ⊤ ≤ p ⁻¹ᵁ ((LB.LinComb L φ ε).U (fun _ => j) ⊓ (LB.LinComb L φ ε).U (fun _ => j')) :=
    fun z hz => ⟨h hz, h' hz⟩
  have := congrArg (evH p _ h2) (t.compat (fun _ => j) (fun _ => j'))
  rw [map_mul, evH_res p _ h2 h, evH_res p _ h2 h', ← fnVal_eq p _ h2, fnVal_unit p _ h2,
    uv_linComb L j j' φ ε p h2] at this
  rw [fnVal_eq p _ h, fnVal_eq p _ h', this]

end Val

section Grp
variable {S : Scheme.{0}} (G : Over S) [GrpObj G]

def lamφ : Fin 4 → ((G ⊗ G).left ⟶ G.left) :=
  ![(fst G G * snd G G : G ⊗ G ⟶ G).left, (fst G G).left, (snd G G).left, (1 : G ⊗ G ⟶ G).left]

def lamε : Fin 4 → ℤ := ![1, -1, -1, 1]

variable {G}

theorem lift_lamφ {T : Over S} (x y : T ⟶ G) (k : Fin 4) :
    (lift x y).left ≫ lamφ G k = ((![x * y, x, y, 1] : Fin 4 → (T ⟶ G)) k).left := by
  have e₀ : lift x y ≫ (fst G G * snd G G) = x * y := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₃ : lift x y ≫ (1 : G ⊗ G ⟶ G) = 1 := MonObj.comp_one _
  fin_cases k
  · exact congrArg (fun q => q.left) e₀
  · exact congrArg (fun q => q.left) (lift_fst x y)
  · exact congrArg (fun q => q.left) (lift_snd x y)
  · exact congrArg (fun q => q.left) e₃

def lamV {T : Over S} {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (x y : T ⟶ G) : U :=
  h (x * y).left * (h x.left)⁻¹ * (h y.left)⁻¹ * h (1 : T ⟶ G).left

theorem prod_lam {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h ((lift x y).left ≫ lamφ G k) ^ lamε k = lamV h x y := by
  simp only [lift_lamφ]
  rw [Fin.prod_univ_four]
  show h (x * y).left ^ (1 : ℤ) * h x.left ^ (-1 : ℤ) * h y.left ^ (-1 : ℤ) * h (1 : T ⟶ G).left ^ (1 : ℤ) = _
  simp only [zpow_neg, zpow_one, lamV]

theorem prod_prim {T : Over S} (w : G ⟶ G) (x : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    ∏ k, h (x.left ≫ primφ w k) ^ primε k = h x.left * (lamV h x (x ≫ w))⁻¹ := by
  have e₁ : x ≫ (𝟙 G * w) = x * (x ≫ w) := (MonObj.comp_mul _ _ _).trans (by simp)
  have e₄ : x ≫ (1 : G ⟶ G) = 1 := MonObj.comp_one _
  rw [Fin.prod_univ_five]
  show h (x.left ≫ 𝟙 _) ^ (1 : ℤ) * h (x ≫ (𝟙 G * w)).left ^ (-1 : ℤ) * h (x.left ≫ 𝟙 _) ^ (1 : ℤ) *
    h (x ≫ w).left ^ (1 : ℤ) * h (x ≫ (1 : G ⟶ G)).left ^ (-1 : ℤ) = _
  rw [e₁, e₄, Category.comp_id]
  simp only [zpow_neg, zpow_one, lamV]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem unit_mem_lam (L : LB G.left) (j : L.ι) (hj : ⊤ ≤ η[G].left ⁻¹ᵁ L.U j) :
    ⊤ ≤ (lift η[G] η[G]).left ⁻¹ᵁ (LB.LinComb L (lamφ G) lamε).U (fun _ => j) := by
  have e : η[G] = (1 : 𝟙_ (Over S) ⟶ G) := by simp [Hom.one_def]
  intro z hz
  refine Set.mem_iInter.2 fun k => ?_
  have h1 : (lift η[G] η[G]).left ≫ lamφ G k = η[G].left := by
    rw [lift_lamφ, e]
    fin_cases k <;> simp
  have h2 : z ∈ ((lift η[G] η[G]).left ≫ lamφ G k) ⁻¹ᵁ L.U j := by rw [h1]; exact hj hz
  exact h2

variable [IsCommMonObj G]

theorem cub_lam₁ {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (t : U) :
    t * lamV h (x * x') y =
      (∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I) * t * (lamV h x y * lamV h x' y) := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_cub]
  simp only [lamV]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem cub_lam₂ {T : Over S} (x x' y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) (t : U) :
    t * lamV h x (x' * y) =
      (∏ I : thK, h ((lift x (lift x' y)).left ≫ thφ G (x3 G) I) ^ thε I) * t * (lamV h x x' * lamV h x y) := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_cub]
  simp only [lamV, ← _root_.mul_assoc x x' y]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem ros_lam (f g : G ⟶ G) {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U)
    (t : U) : t⁻¹ * lamV h x (y ≫ g) =
      ((∏ i, h ((lift x y).left ≫ rosatiφ G f g i) ^ rosatiε i) * t)⁻¹ * lamV h (x ≫ f) y := by
  rw [ReciprocityTheory.ChartRestriction.G.Geo.Tor.prod_ros]
  simp only [lamV]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem lamV_comm {T : Over S} (x y : T ⟶ G) {U : Type} [CommGroup U] (h : (T.left ⟶ G.left) → U) :
    lamV h x y = lamV h y x := by
  simp only [lamV, mul_comm x y, mul_right_comm _ (h x.left)⁻¹ (h y.left)⁻¹]

end Grp

section Main

theorem ev_pt_self {R : Type} [CommRing R] {d n : ℕ} (f : PS R n d) : ev (fun j => pt R (n := n) d j) f = f := by
  unfold ev
  exact congrFun MvPowerSeries.subst_self f

theorem eval_standard_points_two {R : Type} [CommRing R] {d : ℕ} (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f := by
  have : (![pt R d 0, pt R d 1] : Fin 2 → Pt R 2 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  rw [this, ev_pt_self]

theorem eval_standard_points_three {R : Type} [CommRing R] {d : ℕ} (f : PS R 3 d) :
    ev (n := 3) ![pt R d 0, pt R d 1, pt R d 2] f = f := by
  have : (![pt R d 0, pt R d 1, pt R d 2] : Fin 3 → Pt R 3 d) = fun j => pt R d j := by
    funext j; fin_cases j <;> rfl
  rw [this, ev_pt_self]

theorem toJet_mul (hJ : JetAlgSt) {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f g : MvPowerSeries κ R) :
    toJet m (f * g) = toJet m f * toJet m g := by
  obtain ⟨τ, hτ, -⟩ := (hJ R κ).1 m
  rw [← hτ, ← hτ, ← hτ, map_mul]

theorem toJet_pow (hJ : JetAlgSt) {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f : MvPowerSeries κ R)
    (n : ℕ) : toJet m (f ^ n) = toJet m f ^ n := by
  obtain ⟨τ, hτ, -⟩ := (hJ R κ).1 m
  rw [← hτ, ← hτ, map_pow]

theorem jet_unit {R : Type} [CommRing R] {κ : Type} [Finite κ] {X : Scheme.{0}}
    {p : ∀ m : ℕ, Spec (CommRingCat.of (JetR R κ m)) ⟶ X} {U : X.Opens} {f : Γ(X, U)ˣ} {g : MvPowerSeries κ R}
    (h : HasSer p U f.val g) (m : ℕ) : toJet m g = (uv (p m) U f).val :=
  (h m).2.symm.trans (fnVal_unit _ _ (h m).1 f)

theorem germ_alg {A : Type} [CommRing A] (f f' : A) (e c r' : Aˣ) (m : ℕ) (σ' : A)
    (h' : f' * r'.val ^ m = σ') (h : f * ((c * e⁻¹) * r').val ^ m = (c ^ m).val * σ') : f' * e.val ^ m = f := by
  rw [← h', ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val] at h
  rw [← Units.val_pow_eq_pow_val, ← Units.mul_left_inj ((c * e⁻¹ * r') ^ m), h, _root_.mul_assoc, ← Units.val_mul,
    mul_left_comm, ← Units.val_mul]
  congr 2
  rw [← mul_pow, ← mul_pow]
  congr 1
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem hMul : JetAlgSt → RepSt → TwoChartSt → SerSt → SerExSt → HMulSt := by
  intro hJ hR hT _ hE R _ G _ _ Lr c O _ _ act u hu d x x' hx hx' j j' hj hj' B B' hB hB'
  obtain ⟨φ, φi, hinv, hφ, -, hlaw, hact⟩ := hT R G d x x' hx hx'
  obtain ⟨ε, hε, -⟩ := (hE R G d x' hx').2.1
    ((LB.LinComb Lr.L (lamφ G) lamε).U (fun _ => j) ⊓ (LB.LinComb Lr.L (lamφ G) lamε).U (fun _ => j'))
    (fun z hz => ⟨unit_mem_lam Lr.L j hj hz, unit_mem_lam Lr.L j' hj' hz⟩)
    ((LB.LinComb Lr.L (lamφ G) lamε).g (fun _ => j) (fun _ => j')).val
  have inj : ∀ {n : ℕ} (g g' : PS R n d), (∀ m, toJet m g = toJet m g') → g = g' :=
    fun {n} => (hJ R (Fin n × Fin d)).2.2.1
  have E : ∀ {n : ℕ} {a b : Pt R n d} {y z : Fam G (Fin n × Fin d)}, Rep x' a y → Rep x' b z → ∀ m,
      toJet m (ev ![a, b] ε) = (lamV (T := sp (R₀ := R) (JetR R (Fin n × Fin d) m)) (hv Lr.L j j') (y m) (z m)).val := by
    intro n a b y z hy hz m
    have H := hε n a b y z hy hz
    refine (jet_unit H m).trans (congrArg Units.val ?_)
    exact (uv_linComb Lr.L j j' _ _ _ (H m).1).trans (prod_lam (y m) (z m) (hv Lr.L j j'))
  have P : ∀ {n : ℕ} (i : Fin n), ∃ y, Rep x' (pt R (n := n) d i) y :=
    fun {n} i => ((hR R G d x' hx' (Fin n × Fin d)).1 _ (gp_pt i)).exists
  have Z : ∀ n : ℕ, Rep x' (0 : Pt R n d) (fun _ => 1) := fun n => (hR R G d x' hx' (Fin n × Fin d)).2.2.2.1
  have C : ∀ {n : ℕ} {a : Pt R n d} {y : Fam G (Fin n × Fin d)}, Rep x' a y → Rep x (comp1 φ a) y := by
    intro n a y hy
    simpa only [Category.comp_id] using hφ.2 n a y hy
  have cub : ∀ {y₀ y₁ y₂ : Fam G (Fin 3 × Fin d)}, Rep x' (pt R d 0) y₀ → Rep x' (pt R d 1) y₁ →
      Rep x' (pt R d 2) y₂ → ∀ m, ∃ t : (JetR R (Fin 3 × Fin d) m)ˣ, toJet m B'.ph1 = t.val ∧
        toJet m (ev (n := 3) ![comp1 φ (pt R (n := 3) d 0), comp1 φ (pt R (n := 3) d 1),
          comp1 φ (pt R (n := 3) d 2)] B.ph1) =
        ((∏ I : thK, hv Lr.L j j' ((lift (y₀ m) (lift (y₁ m) (y₂ m))).left ≫ thφ G (x3 G) I) ^ thε I) * t).val := by
    intro y₀ y₁ y₂ h₀ h₁ h₂ m
    have H' := hB'.ph1 3 _ _ _ _ _ _ h₀ h₁ h₂
    have H := hB.ph1 3 _ _ _ _ _ _ (C h₀) (C h₁) (C h₂)
    rw [eval_standard_points_three] at H'
    exact ⟨_, jet_unit H' m, (jet_unit H m).trans (congrArg Units.val
      (gen_change Lr.L j j' (thφ G (x3 G)) thε c.t c.isGen _ (H m).1 (H' m).1))⟩
  refine ⟨φ, φi, ε, ⟨hinv, ?_, ?_, hlaw _ _ hB.law hB'.law, fun a => hact _ _ _ (hB.map a) (hB'.map a),
    ?_, ?_, ?_, fun a => ?_⟩, hφ, ?_⟩
  · obtain ⟨y, hy⟩ := P (n := 1) 0
    refine inj _ _ fun m => ?_
    rw [E (Z 1) hy m, toJet_one]
    simp [lamV]
  · obtain ⟨y, hy⟩ := P (n := 1) 0
    refine inj _ _ fun m => ?_
    rw [E hy (Z 1) m, toJet_one]
    simp [lamV]
  · obtain ⟨y₀, h₀⟩ := P (n := 3) 0
    obtain ⟨y₁, h₁⟩ := P (n := 3) 1
    obtain ⟨y₂, h₂⟩ := P (n := 3) 2
    refine inj _ _ fun m => ?_
    obtain ⟨t, ht', ht⟩ := cub h₀ h₁ h₂ m
    rw [toJet_mul hJ, toJet_mul hJ, toJet_mul hJ, ht', ht, E (hB'.law.2 3 _ _ _ _ h₀ h₁) h₂ m, E h₀ h₂ m, E h₁ h₂ m]
    simp only [← Units.val_mul]
    exact congrArg Units.val (cub_lam₁ (y₀ m) (y₁ m) (y₂ m) (hv Lr.L j j') t)
  · obtain ⟨y₀, h₀⟩ := P (n := 3) 0
    obtain ⟨y₁, h₁⟩ := P (n := 3) 1
    obtain ⟨y₂, h₂⟩ := P (n := 3) 2
    refine inj _ _ fun m => ?_
    obtain ⟨t, ht', ht⟩ := cub h₀ h₁ h₂ m
    rw [hB.ph2, hB'.ph2, toJet_mul hJ, toJet_mul hJ, toJet_mul hJ, ht', ht, E h₀ (hB'.law.2 3 _ _ _ _ h₁ h₂) m,
      E h₀ h₁ m, E h₀ h₂ m]
    simp only [← Units.val_mul]
    exact congrArg Units.val (cub_lam₂ (y₀ m) (y₁ m) (y₂ m) (hv Lr.L j j') t)
  · obtain ⟨y₀, h₀⟩ := P (n := 2) 0
    obtain ⟨y₁, h₁⟩ := P (n := 2) 1
    rw [hB.sy, hB'.sy, ev_one, _root_.one_mul, _root_.one_mul]
    refine inj _ _ fun m => ?_
    have e := E h₀ h₁ m
    rw [eval_standard_points_two] at e
    rw [e, E h₁ h₀ m, lamV_comm]
  · obtain ⟨y₀, h₀⟩ := P (n := 2) 0
    obtain ⟨y₁, h₁⟩ := P (n := 2) 1
    refine inj _ _ fun m => ?_
    have H' := hB'.ad a 2 _ _ _ _ h₀ h₁
    have H := hB.ad a 2 _ _ _ _ (C h₀) (C h₁)
    rw [eval_standard_points_two] at H'
    have g := gen_change Lr.L j j' _ _ (u a) (hu a) _ (H m).1 (H' m).1
    rw [toJet_mul hJ, toJet_mul hJ, jet_unit H' m, jet_unit H m, E h₀ ((hB'.map (star a)).2 2 _ _ h₁) m,
      E ((hB'.map a).2 2 _ _ h₀) h₁ m, map_inv, map_inv, g]
    simp only [← Units.val_mul]
    exact congrArg Units.val (ros_lam _ _ (y₀ m) (y₁ m) (hv Lr.L j j') _)
  · rintro w0 ρ hρ k s f f' ⟨σ, r, hσ, hr, hf⟩ ⟨σ', r', hσ', hr', hf'⟩
    obtain ⟨y, hy⟩ := P (n := 1) 0
    have hc := C hy
    rw [gt_comp1_pt_right] at hc
    refine inj _ _ fun m => ?_
    have Hσ := hσ 1 _ _ hc
    have Hr := hr 1 _ _ hc
    have Hσ' := hσ' 1 _ _ hy
    have Hr' := hr' 1 _ _ hy
    rw [gt_ev_pt_self] at Hσ' Hr'
    have gr := (gen_change Lr.L j j' _ _ ρ hρ _ (Hr m).1 (Hr' m).1).trans
      (congrArg (· * _) (prod_prim (act.act w0) (y m) (hv Lr.L j j')))
    have gs := sec_change Lr.L j j' _ _ s _ (Hσ m).1 (Hσ' m).1
    rw [(Hσ m).2, (Hσ' m).2, Fintype.prod_unique, zpow_natCast] at gs
    have e' := congrArg (toJet m) hf'
    rw [toJet_mul hJ, toJet_pow hJ, jet_unit Hr' m] at e'
    have hev : ev (n := 1) ![φ] f * ev (n := 1) ![φ] r ^ k = ev (n := 1) ![φ] σ := by
      rw [← hf]
      unfold ev
      rw [← MvPowerSeries.coe_substAlgHom (gt_hasSubst ![φ] (single_point_zero_constant hinv.1)), map_mul, map_pow]
    have e := congrArg (toJet m) hev
    rw [toJet_mul hJ, toJet_pow hJ, jet_unit Hr m, gr, gs] at e
    rw [toJet_mul hJ, toJet_pow hJ, E hy ((hB'.map w0).2 1 _ _ hy) m]
    refine germ_alg _ _ _ (hv Lr.L j j' (y m).left) _ k _ e' (e.trans ?_)
    congr 4

end Main

end GlobalTheory.JetSer.FrameChange
