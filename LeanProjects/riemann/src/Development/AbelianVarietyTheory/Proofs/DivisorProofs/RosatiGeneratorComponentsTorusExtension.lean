import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.MumfordConstruction
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFacts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.WithISelf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GtRelVIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiAdjTensorPowerIntMatrixEndomorphism
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
open GlobalTheory.Ex GlobalTheory.Mum.TensTor

noncomputable section

namespace GlobalTheory.Mum.RosComp

section Alg

variable {O : Type} [CommRing O] {N : NumD O} {Γ Γ₀ Q : Type} [CommGroup Γ] [CommGroup Γ₀] [AddCommGroup Q]
  (ev : Γ →* N.A) (e₀ : Γ →* Γ₀) (ℓ : Γ → Γ → Q) (κ : Additive Oˣ →+ Q)

def PVu {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (χ : Fin r → N.X) (vs : Fin r → N.Gt) : Oˣ :=
  ∏ i, ∏ j, ((vs j).s (χ i) * (vs i).s (χ j) /
      (N.θ (N.c (χ j)) (vs j).b (N.c (χ i)) * N.θ (N.c (χ j)) (vs j).b (vs i).b *
        N.θ (N.c (χ i)) (vs i).b (N.c (χ j) * (vs j).b))) ^ W i j

def cHom (N : NumD O) : Multiplicative N.X →* N.A := MonoidHom.mk' (fun χ => N.c χ.toAdd) fun a b => N.c_add a.toAdd b.toAdd

variable (hs : ∀ a b, ℓ a b = ℓ b a)
  (hc : ∀ a a' b, e₀ b = 1 → ℓ (a * a') b = ℓ a b + ℓ a' b - κ (Additive.ofMul (N.θ (ev a) (ev a') (ev b))))

include hc in
theorem left_sum {r : ℕ} (x : Fin r → Γ) (χ : Fin r → N.X) (hx : ∀ k, ev (x k) = N.c (χ k)) (n : Fin r → ℤ)
    (b : Γ) (g : N.Gt) (hb : ev b = g.b) (h₀ : e₀ b = 1) :
    ℓ (∏ k, x k ^ n k) b - κ (Additive.ofMul (g.s (∑ k, n k • χ k))) =
      ∑ k, n k • (ℓ (x k) b - κ (Additive.ofMul (g.s (χ k)))) := by
  let S : Subgroup (Γ × Multiplicative N.X) :=
    MonoidHom.eqLocus (ev.comp (MonoidHom.fst _ _)) ((cHom N).comp (MonoidHom.snd _ _))
  let φ : S →* Multiplicative Q := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd (ℓ p.1.1 b - κ (Additive.ofMul (g.s p.1.2.toAdd)))) fun p p' => by
      have e : ev p.1.1 = N.c p.1.2.toAdd := p.2
      have e' : ev p'.1.1 = N.c p'.1.2.toAdd := p'.2
      have m := congrArg (fun u => κ (Additive.ofMul u)) (g.mult p.1.2.toAdd p'.1.2.toAdd)
      simp only [ofMul_mul, map_add] at m
      rw [← ofAdd_add]
      congr 1
      show ℓ (p.1.1 * p'.1.1) b - κ (Additive.ofMul (g.s (p.1.2.toAdd + p'.1.2.toAdd))) = _
      rw [hc _ _ _ h₀, e, e', hb]
      linear_combination (norm := abel) -m
  let s : Fin r → S := fun k => ⟨(x k, Multiplicative.ofAdd (χ k)), hx k⟩
  have h := congrArg Multiplicative.toAdd (map_prod φ (fun k => s k ^ n k) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  have c₁ : (∏ k, s k ^ n k).1.1 = ∏ k, x k ^ n k := by
    simp [s, Prod.fst_prod]
  have c₂ : (∏ k, s k ^ n k).1.2.toAdd = ∑ k, n k • χ k := by
    simp [s, Prod.snd_prod, toAdd_prod]
  rw [← c₁, ← c₂]
  exact h

include hs hc in
theorem right_sum {r : ℕ} (y : Fin r → Γ) (g : Fin r → N.Gt) (hy : ∀ k, ev (y k) = (g k).b) (n : Fin r → ℤ)
    (a : Γ) (χ : N.X) (ha : ev a = N.c χ) (h₀ : e₀ a = 1) :
    ℓ a (∏ k, y k ^ n k) - κ (Additive.ofMul ((∏ k, g k ^ n k).s χ)) =
      ∑ k, n k • (ℓ a (y k) - κ (Additive.ofMul ((g k).s χ))) := by
  let S : Subgroup (Γ × N.Gt) :=
    MonoidHom.eqLocus (ev.comp (MonoidHom.fst _ _)) (N.projB.comp (MonoidHom.snd _ _))
  let φ : S →* Multiplicative Q := MonoidHom.mk'
    (fun p => Multiplicative.ofAdd (ℓ a p.1.1 - κ (Additive.ofMul (p.1.2.s χ)))) fun p p' => by
      have e : ev p.1.1 = p.1.2.b := p.2
      have e' : ev p'.1.1 = p'.1.2.b := p'.2
      rw [← ofAdd_add]
      congr 1
      show ℓ a (p.1.1 * p'.1.1) - κ (Additive.ofMul ((p.1.2 * p'.1.2).s χ)) = _
      rw [hs, hc _ _ _ h₀, e, e', ha, NumD.Gt.mul_s, hs a, hs a, N.cub.s12 p.1.2.b, N.cub.s01 p.1.2.b]
      simp only [ofMul_mul, ofMul_div, map_add, map_sub]
      abel
  let s : Fin r → S := fun k => ⟨(y k, g k), hy k⟩
  have h := congrArg Multiplicative.toAdd (map_prod φ (fun k => s k ^ n k) Finset.univ)
  simp only [map_zpow, toAdd_prod, toAdd_zpow] at h
  have c₁ : (∏ k, s k ^ n k).1.1 = ∏ k, y k ^ n k := by
    simp [s, Prod.fst_prod]
  have c₂ : (∏ k, s k ^ n k).1.2 = ∏ k, g k ^ n k := by
    simp [s, Prod.snd_prod]
  rw [← c₁, ← c₂]
  exact h

include hs hc in
theorem quad_mul {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (a y : Fin r → Γ) (χ : Fin r → N.X) (g : Fin r → N.Gt)
    (ha : ∀ k, ev (a k) = N.c (χ k)) (hy : ∀ k, ev (y k) = (g k).b) (a₀ : ∀ k, e₀ (a k) = 1) (y₀ : ∀ k, e₀ (y k) = 1) :
    ∑ i, ∑ j, W i j • ℓ (a i * y i) (a j * y j) = ∑ i, ∑ j, W i j • ℓ (a i) (a j) + ∑ i, ∑ j, W i j • ℓ (y i) (y j) +
      ∑ i, ∑ j, W i j • ((ℓ (a i) (y j) - κ (Additive.ofMul ((g j).s (χ i)))) +
        (ℓ (a j) (y i) - κ (Additive.ofMul ((g i).s (χ j))))) + κ (Additive.ofMul (PVu W χ g)) := by
  simp only [PVu, ofMul_prod, map_sum, ofMul_zpow, map_zsmul, ← Finset.sum_add_distrib, ← smul_add]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  congr 1
  rw [hc _ _ _ (by rw [map_mul, a₀, y₀, _root_.mul_one]), hs (a i), hs (y i), hc _ _ _ (a₀ i), hc _ _ _ (y₀ i), map_mul,
    ha, ha, hy, hy, hs (a j) (a i), hs (y j) (a i), hs (y j) (y i)]
  simp only [ofMul_mul, ofMul_div, map_add, map_sub]
  abel

include hs hc in
theorem total {r : ℕ} (W A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') (x y a b : Fin r → Γ) (χ χ₁ : Fin r → N.X)
    (g : Fin r → N.Gt) (hx : ∀ k, ev (x k) = N.c (χ k)) (hy : ∀ k, ev (y k) = (g k).b) (x₀ : ∀ k, e₀ (x k) = 1)
    (y₀ : ∀ k, e₀ (y k) = 1) (ha : ∀ i, a i = ∏ k, x k ^ A i k) (hb : ∀ i, b i = ∏ k, y k ^ A' i k)
    (h₁ : ∀ i, χ₁ i = ∑ k, A i k • χ k) :
    ∑ i, ∑ j, W i j • ℓ (a i * y i) (a j * y j) - ∑ i, ∑ j, W i j • ℓ (a i) (a j) - ∑ i, ∑ j, W i j • ℓ (y i) (y j) -
      ∑ i, ∑ j, W i j • ℓ (x i * b i) (x j * b j) + ∑ i, ∑ j, W i j • ℓ (x i) (x j) + ∑ i, ∑ j, W i j • ℓ (b i) (b j) =
      κ (Additive.ofMul (PVu W χ₁ g)) - κ (Additive.ofMul (PVu W χ (fun i => ∏ k, g k ^ A' i k))) := by
  have ea : ∀ i, ev (a i) = N.c (χ₁ i) := fun i => by
    have : N.c (χ₁ i) = cHom N (∏ k, Multiplicative.ofAdd (χ k) ^ A i k) := by
      rw [h₁]; show _ = N.c _; simp [toAdd_prod]
    rw [this, ha, map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hx]; rfl
  have eb : ∀ i, ev (b i) = (∏ k, g k ^ A' i k).b := fun i => by
    rw [← N.projB_apply, hb, map_prod, map_prod]
    exact Finset.prod_congr rfl fun k _ => by rw [map_zpow, map_zpow, hy]; rfl
  have a₀ : ∀ i, e₀ (a i) = 1 := fun i => by simp [ha, map_prod, x₀]
  have b₀ : ∀ i, e₀ (b i) = 1 := fun i => by simp [hb, map_prod, y₀]
  rw [quad_mul ev e₀ ℓ κ hs hc W a y χ₁ g ea hy a₀ y₀, quad_mul ev e₀ ℓ κ hs hc W x b χ _ hx eb x₀ b₀]
  have e₁ : ∀ i j, ℓ (a i) (y j) - κ (Additive.ofMul ((g j).s (χ₁ i))) =
      ∑ k, A i k • (ℓ (x k) (y j) - κ (Additive.ofMul ((g j).s (χ k)))) := fun i j => by
    rw [ha, h₁, left_sum ev e₀ ℓ κ hc x χ hx _ _ _ (hy j) (y₀ j)]
  have e₂ : ∀ i j, ℓ (x i) (b j) - κ (Additive.ofMul ((∏ k, g k ^ A' j k).s (χ i))) =
      ∑ k, A' j k • (ℓ (x i) (y k) - κ (Additive.ofMul ((g k).s (χ i)))) := fun i j => by
    rw [hb, right_sum ev e₀ ℓ κ hs hc y g hy _ _ _ (hx i) (x₀ i)]
  have hC := GlobalTheory.TensRosati.key_sum (fun k m => ℓ (x k) (y m) - κ (Additive.ofMul ((g m).s (χ k)))) W A A' h
  simp only [e₁, e₂]
  rw [hC]
  abel

end Alg

end GlobalTheory.Mum.RosComp

namespace GlobalTheory.Mum.RosComp

open GlobalTheory.TensRosati

section Flat

variable {X X' Y Z : Scheme.{0}} {M : LB X} {K₁ : Type} [Fintype K₁] {pr : K₁ → (X' ⟶ X)} {e : K₁ → ℤ}
  {K : Type} [Fintype K]

theorem le_flat (φ' : K → (Y ⟶ X')) (j : K × K₁ → M.ι) :
    LB.wchart M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) j ≤ LB.wchart (LB.LinComb M pr e) φ' (fun a k => j (a, k)) :=
  fun _ hy => Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy (a, k)

def flat (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε)) :
    LB.Gen (LB.LinComb M (fun p : K × K₁ => φ' p.1 ≫ pr p.2) (fun p => ε p.1 * e p.2)) :=
  ⟨fun j : K × K₁ → M.ι => res (le_flat φ' j) (t.s (fun a k => j (a, k)))⟩

theorem flat_isGen (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε))
    (ht : t.IsGen) : (flat φ' ε t).IsGen := by
  refine isGen_of_gm _ fun y j j' h h' => ?_
  refine (gm_res (𝟙 Y) y _ h _).trans ((gen_trans ht (𝟙 Y) y (le_flat φ' j h) (le_flat φ' j' h')).trans
    (congrArg₂ (· * ·) ?_ (gm_res (𝟙 Y) y _ h' _).symm))
  unfold trF
  rw [Fintype.prod_prod_type]
  refine Finset.prod_congr rfl fun a _ => ?_
  refine (congrArg (· ^ ε a) (gm_linComb M pr e (𝟙 Y ≫ φ' a) y (fun k => j (a, k)) (fun k => j' (a, k))
    (Set.mem_iInter.1 (le_flat (e := e) φ' j h) a) (Set.mem_iInter.1 (le_flat (e := e) φ' j' h') a))).trans ?_
  rw [← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  dsimp only
  rw [← zpow_mul, mul_comm (e i), Category.assoc]

theorem good_comb {z : Z} {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    Good (LB.LinComb M pr e) z (fun ψ k => J (ψ ≫ pr k)) := fun ψ => hJ.mem pr ψ

theorem val_flat (φ' : K → (Y ⟶ X')) (ε : K → ℤ) (t : LB.Gen (LB.LinComb (LB.LinComb M pr e) φ' ε)) (r : Z ⟶ Y)
    {z : Z} {J : (Z ⟶ X) → M.ι} (hJ : Good M z J) :
    val (flat φ' ε t) r z J = val t r z (fun ψ k => J (ψ ≫ pr k)) := by
  refine Eq.trans ?_ (val_of t r z (fun ψ k => J (ψ ≫ pr k)) (fun a k => J (r ≫ φ' a ≫ pr k))
    (fun a => funext fun k => congrArg J (Category.assoc _ _ _))).symm
  exact gm_res r z _ (hJ.mem (fun p : K × K₁ => φ' p.1 ≫ pr p.2) r) _

end Flat

section Gens

variable {X Y Z S₀ : Scheme.{0}}

def normGens (L : LB X) (e : S₀ ⟶ Y) (r : Z ⟶ Y) {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    AddSubgroup (FreeAbelianGroup (Y ⟶ X) × Additive (Z.presheaf.stalk z)ˣ) where
  carrier := {s | ∃ (K : Type) (_ : Fintype K) (φ : K → (Y ⟶ X)) (ε : K → ℤ) (t : LB.Gen (LB.LinComb L φ ε)),
    t.IsGen ∧ s.1 = ∑ k, ε k • FreeAbelianGroup.of (φ k) ∧ (∀ y I, Good L y I → val t e y I = 1) ∧
      val t r z J = s.2.toMul}
  zero_mem' := ⟨PEmpty, inferInstance, PEmpty.elim, PEmpty.elim, LB.oneGen L, fun _ _ =>
    (map_one _).trans ((congrArg₂ (· * ·) (Fintype.prod_empty _) (map_one _)).trans (_root_.mul_one _)).symm,
    (Fintype.sum_empty _).symm, fun _ _ _ => val_one _, val_one _⟩
  add_mem' := by
    rintro s s' ⟨K, _, φ, ε, t, ht, hs, h₀, hv⟩ ⟨K', _, φ', ε', t', ht', hs', h₀', hv'⟩
    refine ⟨K ⊕ K', inferInstance, _, _, LB.mulGen L φ ε φ' ε' t t', DVR.mulGen_isGen _ _ _ _ _ _ _ ht ht', ?_,
      fun y I hI => by rw [val_mul hI, h₀ y I hI, h₀' y I hI, _root_.mul_one], by rw [val_mul hJ, hv, hv']; rfl⟩
    rw [Fintype.sum_sum_type, Prod.fst_add, hs, hs']
    rfl
  neg_mem' := by
    rintro s ⟨K, _, φ, ε, t, ht, hs, h₀, hv⟩
    refine ⟨K, inferInstance, φ, _, LB.invGen L φ ε t, DVR.invGen_isGen _ _ _ _ ht, ?_,
      fun y I hI => by rw [val_inv, h₀ y I hI, inv_one], by rw [val_inv, hv]; rfl⟩
    simp only [neg_smul, Finset.sum_neg_distrib, Prod.fst_neg, hs]

end Gens

section Cube

variable {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G]

theorem cube_mem_norm (L : RigLB G) (c : CubicalStr G L) {T T₀ T' : Over S} (e : T₀ ⟶ T) (r : T' ⟶ T) {z : T'.left}
    {J} (hJ : Good L.L z J) (a a' b : T ⟶ G) (hb : e ≫ b = 1) :
    (lam (a * a') b - lam a b - lam a' b, Additive.ofMul (cubV c z J (r ≫ a) (r ≫ a') (r ≫ b))) ∈
      normGens L.L e.left r.left hJ := by
  refine ⟨thK, inferInstance, _, _, LB.pullGen L.L (thφ G (x3 G)) thε c.t (lift a (lift a' b)).left,
    DVR.pullGen_isGen _ _ _ _ c.isGen _, ?_, fun y I hI => ?_, val_cub c r hJ a a' b⟩
  · have := prod_cub a a' b (U := Multiplicative (FreeAbelianGroup (T.left ⟶ G.left)))
      (fun m => Multiplicative.ofAdd (FreeAbelianGroup.of m))
    have e := congrArg Multiplicative.toAdd this
    simp only [toAdd_prod, toAdd_zpow, toAdd_mul, toAdd_inv, toAdd_ofAdd] at e
    rw [e, lam, lam, lam]
    abel
  · refine (val_cub c e hI a a' b).trans ?_
    rw [hb]
    exact (isCub_cubV c hI).face₃ _ _

end Cube

section Total

variable {S : Scheme.{0}} {A A' : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A']
  {r : ℕ} (pr : Fin r → (A' ⟶ A))

theorem ros_flat (W : Matrix (Fin r) (Fin r) ℤ) (f g : A' ⟶ A') :
    ∑ p : Fin 6 × ((Fin r × Fin r) × Fin 4), (rosatiε p.1 * tensε W p.2) •
      FreeAbelianGroup.of (rosatiφ A' f g p.1 ≫ tensφ pr p.2) =
      qf pr W ((fst A' A' ≫ f) * snd A' A') - qf pr W (fst A' A' ≫ f) - qf pr W (snd A' A') -
        qf pr W (fst A' A' * (snd A' A' ≫ g)) + qf pr W (fst A' A') + qf pr W (snd A' A' ≫ g) := by
  rw [Fintype.sum_prod_type]
  simp only [mul_smul, ← Finset.smul_sum, Fin.sum_univ_six]
  rw [← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq, ← flat_eq]
  rw [show rosatiε 0 = 1 from rfl, show rosatiε 1 = -1 from rfl,
    show rosatiε 2 = -1 from rfl, show rosatiε 3 = -1 from rfl, show rosatiε 4 = 1 from rfl,
    show rosatiε 5 = 1 from rfl]
  simp only [one_smul, neg_smul, sub_eq_add_neg]
  rfl

end Total

end GlobalTheory.Mum.RosComp

namespace GlobalTheory.Mum.RosComp

open GlobalTheory.TensRosati

variable {R : Type} [CommRing R] [IsDomain R] {D D' : DegPre R} {r : ℕ} {W : Matrix (Fin r) (Fin r) ℤ}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {N N' : NumD F}

theorem ros_value (T : Tens D D' W) (ν : NumOf D F N) (ν' : NumOf D' F N') (A A' : Matrix (Fin r) (Fin r) ℤ)
    (h : A.transpose * (W + W.transpose) = (W + W.transpose) * A') (f g : D'.P.A ⟶ D'.P.A)
    (hf : letI := D.P.isAb.comm; ∀ i, f ≫ T.pr i = ∏ j, T.pr j ^ A i j)
    (hg : letI := D.P.isAb.comm; ∀ i, g ≫ T.pr i = ∏ j, T.pr j ^ A' i j)
    (ρ : N'.A → N'.A → F) (hρ : TensRos.RosVT T ν ν' f g ρ) (a b : N'.A) (χ χ₁ : Fin r → N.X) (gs : Fin r → N.Gt)
    (ha : ∀ j, TensTor.cmp T ν ν' a j = N.c (χ j)) (hb : ∀ j, TensTor.cmp T ν ν' b j = (gs j).b)
    (h₁ : ∀ i, χ₁ i = ∑ k, A i k • χ k) :
    ρ a b * (PVu W χ₁ gs : Fˣ) = (PVu W χ (fun i => ∏ k, gs k ^ A' i k) : Fˣ) := by
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨u, hu, u₀, hv⟩ := hρ
  obtain ⟨z⟩ : Nonempty (Sp F) := inferInstanceAs (Nonempty (PrimeSpectrum F))
  have hJ : Good D.P.L z ν.J := fun ψ => ν.good ψ trivial
  let τ : Fˣ →* ((Sp F).presheaf.stalk z)ˣ := Units.map (toStk z).toMonoidHom
  have tθ : ∀ a b c, τ (N.θ a b c) = cubV D.cub (T := TF (R := R) F) z ν.J (ν.eA a) (ν.eA b) (ν.eA c) := fun a b c =>
    Units.ext ((Units.coe_map _ _).trans ((congrArg (toStk z) (ν.θ_eq a b c)).trans (toStk_valF _ _ z (hJ.mem _ _) _)))
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A ⊗ D'.P.A := lift η[D'.P.A] η[D'.P.A]
  let p : TF (R := R) F ⟶ D'.P.A ⊗ D'.P.A := lift (ν'.eA a) (ν'.eA b)
  let H := normGens D.P.L (Z := Sp F) e.left p.left hJ
  let ev : (D'.P.A ⊗ D'.P.A ⟶ D.P.A) →* N.A := ν.eA.symm.toMonoidHom.comp (preHom p)
  let ℓ : (D'.P.A ⊗ D'.P.A ⟶ D.P.A) → (D'.P.A ⊗ D'.P.A ⟶ D.P.A) → _ ⧸ H := fun x y =>
    (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) (lam x y)
  let κ : Additive Fˣ →+ _ ⧸ H := ((QuotientAddGroup.mk' H).comp (AddMonoidHom.inr _ _)).comp τ.toAdditive
  have hs : ∀ x y, ℓ x y = ℓ y x := fun x y => by simp only [ℓ, lam_comm x y]
  have hc : ∀ x x' y, preHom e y = 1 →
      ℓ (x * x') y = ℓ x y + ℓ x' y - κ (Additive.ofMul (N.θ (ev x) (ev x') (ev y))) := fun x x' y hy => by
    have m := (QuotientAddGroup.eq_zero_iff _).2
      (cube_mem_norm ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩ D.cub e p hJ x x' y hy)
    have t : τ (N.θ (ev x) (ev x') (ev y)) = cubV D.cub (T := TF (R := R) F) z ν.J (p ≫ x) (p ≫ x') (p ≫ y) := by
      rw [tθ]
      simp only [ev, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
      rfl
    have m' : ℓ (x * x') y - ℓ x y - ℓ x' y + κ (Additive.ofMul (N.θ (ev x) (ev x') (ev y))) = 0 := by
      refine Eq.trans ?_ m
      simp only [ℓ, ← map_sub]
      refine (map_add (QuotientAddGroup.mk' H) _ _).symm.trans (congrArg _ (Prod.ext (add_zero _) ?_))
      exact (zero_add _).trans (congrArg Additive.ofMul t)
    linear_combination (norm := abel) m'
  have one : ∀ k, η[D'.P.A] ≫ T.pr k = 1 := fun k => by
    have := T.pr_hom k
    simp [Hom.one_def]
  have tot := total ev (preHom e) ℓ κ hs hc W A A' h (fun k => fst _ _ ≫ T.pr k) (fun k => snd _ _ ≫ T.pr k)
    (fun k => (fst _ _ ≫ f) ≫ T.pr k) (fun k => (snd _ _ ≫ g) ≫ T.pr k) χ χ₁ gs
    (fun k => (congrArg ν.eA.symm (lift_fst_assoc _ _ _)).trans (ha k))
    (fun k => (congrArg ν.eA.symm (lift_snd_assoc _ _ _)).trans (hb k))
    (fun k => (lift_fst_assoc _ _ _).trans (one k)) (fun k => (lift_snd_assoc _ _ _).trans (one k))
    (fun i => by
      rw [Category.assoc, hf, GlobalTheory.MatrixAction.comp_finsetProd]
      exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow])
    (fun i => by
      rw [Category.assoc, hg, GlobalTheory.MatrixAction.comp_finsetProd]
      exact Finset.prod_congr rfl fun k _ => by rw [GrpObj.comp_zpow]) h₁
  have hm : ∀ (x y : D'.P.A ⊗ D'.P.A ⟶ D'.P.A) (i : Fin r), (x * y) ≫ T.pr i = (x ≫ T.pr i) * (y ≫ T.pr i) :=
    fun x y i => by
      have := T.pr_hom i
      exact MonObj.mul_comp x y (T.pr i)
  have mq : ∀ x : D'.P.A ⊗ D'.P.A ⟶ D'.P.A, (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) (qf T.pr W x) =
      ∑ i, ∑ j, W i j • ℓ (x ≫ T.pr i) (x ≫ T.pr j) := fun x => by
    simp only [qf, map_sum, map_zsmul, ℓ]
  have mem : (∑ q : Fin 6 × ((Fin r × Fin r) × Fin 4), (rosatiε q.1 * tensε W q.2) •
      FreeAbelianGroup.of (rosatiφ D'.P.A f g q.1 ≫ tensφ T.pr q.2),
      Additive.ofMul (τ (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs))) ∈ H := by
    refine (QuotientAddGroup.eq_zero_iff _).1 ?_
    have s : ∀ (x) (v : Fˣ), (QuotientAddGroup.mk (x, Additive.ofMul (τ v)) : _ ⧸ H) =
        (QuotientAddGroup.mk' H).comp (AddMonoidHom.inl _ _) x + κ (Additive.ofMul v) := fun x v =>
      (congrArg _ (Prod.ext (add_zero _).symm (zero_add _).symm)).trans (map_add (QuotientAddGroup.mk' H) _ _)
    rw [s, ros_flat]
    simp only [map_add, map_sub, mq, hm, ofMul_div]
    rw [tot]
    abel
  obtain ⟨K, _, φ, ε, t, ht, hF, t₀, tv⟩ := mem
  have he : e.left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w]; exact Over.w e
  have key := gen_unique' D.P.isLB (formEq_of_eq hF.symm) _ e.left he
    (surj_comp (surj_snd GlobalTheory.globalFns_holds D'.P.isAb _) (GlobalTheory.globalFns_holds _ _ D'.P.isAb).2)
    (flat_isGen _ _ u hu) ht (fun y I hI => by
      have c := val_corr (good_comb (pr := tensφ T.pr) (e := tensε W) hI) u₀ (𝟙 _)
      have c' := (val_pull (good_comb (pr := tensφ T.pr) (e := tensε W) hI) u (zero2 D'.P.A) (𝟙 _)).symm.trans
        (c.trans (val_one _))
      rw [Category.id_comp] at c'
      exact ((val_flat _ _ u _ hI).trans c').trans (t₀ y I hI).symm) (Sp F) p.left z ν.J hJ
  have k2 : toStk z (ρ a b) = (τ (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs)).val := by
    rw [hv]
    refine (toStk_valF _ _ z ((good_comb (pr := tensφ T.pr) (e := tensε W) hJ).mem _ _) _).trans ?_
    exact congrArg Units.val ((val_flat _ _ u p.left hJ).symm.trans (key.trans tv))
  have k3 : ρ a b = (PVu W χ (fun i => ∏ k, gs k ^ A' i k) / PVu W χ₁ gs : Fˣ) :=
    (toStk z).injective (k2.trans (Units.coe_map _ _))
  rw [k3, ← Units.val_mul, div_mul_cancel]

end GlobalTheory.Mum.RosComp

open GlobalTheory.Mum.RosComp in

theorem GlobalTheory.Mum.TensRos.rosVT_components : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ) (T : Tens D.toPre D'.toPre W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (N N' : NumD F) (ν : NumOf D.toPre F N) (ν' : NumOf D'.toPre F N') (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → ∀ (x : 𝓞 E) (ρ'' : N'.A → N'.A → F), (letI := H.starRing; GlobalTheory.Mum.TensRos.RosVT T ν ν' (o.onB.act (star x)) (o.onB.act x) ρ'') → ∀ (χ : N'.X) (b : N'.A) (gs : Fin r → N.Gt), (∀ j, GlobalTheory.Mum.TensTor.cmp T ν ν' b j = (gs j).b) → (letI := H.starRing; ρ'' (N'.c χ) b * GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') (ν'.eX.symm (star x • ν'.eX χ)) gs = GlobalTheory.Mum.TensRos.PV W (GlobalTheory.Mum.TensTor.chi T ν ν') χ (fun i => ∏ j, gs j ^ ρ x i j)) := by
  intro R _ _ _ _ D D' r W T F _ _ _ N N' ν ν' E _ _ _ H ρ hρ _ o hact x ρ'' hros χ b gs hb
  letI := H.starRing
  have h := hρ (star x)
  rw [show H.bar (star x) = x from star_star x] at h
  refine ros_value T ν ν' (ρ (star x)) (ρ x) h _ _ (hact.2 _) (hact.2 _) ρ'' hros (N'.c χ) b (TensTor.chi T ν ν' χ) _ gs
    (fun j => ?_) hb (fun i => ?_)
  · simp only [TensTor.cmp, TensTor.chi]
    rw [ν.eA.symm_apply_eq, ν.c_eq, ν'.c_eq, ν.eX.apply_symm_apply]
    simp only [DegPre.cF, Category.assoc, T.c_pr]
  · simp only [TensTor.chi, AddEquiv.apply_symm_apply, hact.1, map_sum, map_zsmul]

end
