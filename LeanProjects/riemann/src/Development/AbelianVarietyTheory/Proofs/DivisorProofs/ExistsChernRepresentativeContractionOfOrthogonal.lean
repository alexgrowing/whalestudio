import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianSchemeDeRhamFreeHodgeSequenceBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PointWithZeroSecondCoordLeftCompSnd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTangentVectorContractionTwoCochainProduct
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContrCupFormEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemHodgeFiltrationIffPointwiseCoboundary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorEqZeroOfForallDualPairing

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PtExt.ChernRep

variable {R : Type} [CommRing R] {A B : Over (Sp R)} [GrpObj A] [GrpObj B]

theorem isContr_add {z z' : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} {κ κ' : Fn1 A}
    (h : IsContr z v κ) (h' : IsContr z' v κ') : IsContr (z + z') v (κ.add κ') := by
  unfold IsContr at h h' ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Fn1.add, Pi.add_apply, h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ,
    h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ, ← TrivSqZeroExt.snd_add]
  congr 1
  abel

theorem isContr_sum {n : ℕ} {z : Fin n → C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B}
    {κ : Fin n → Fn1 A} (h : ∀ k, IsContr (z k) v (κ k)) :
    IsContr (∑ k, z k) v (fun D _ _ D' _ _ φ x ↦ ∑ k, κ k D D' φ x) := by
  unfold IsContr at h ⊢
  intro D _ _ D' _ _ φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ
  simp only [Finset.sum_apply]
  rw [Finset.sum_congr rfl fun k _ ↦ h k D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]
  simp only [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  have key : ∀ g : Fin n → TrivSqZeroExt D' D', ∑ k, (g k).snd = (∑ k, g k).snd := fun g ↦
    (map_sum (TrivSqZeroExt.sndHom D' D') g Finset.univ).symm
  exact key fun k ↦ z k _ _ _ s τ - z k _ _ _ a s' - z k _ _ _ i τ + z k _ _ _ b i'

theorem isContr_eq {z : C2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _))} {v : epsR R ⟶ B} (hv : IsTangent v)
    {κ κ' : Fn1 A} (h : IsContr z v κ) (h' : IsContr z v κ') (D : Type) [CommRing D] [Algebra R D]
    (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt A D) :
    κ D D' φ x = κ' D D' φ x := by
  obtain ⟨s, i, s', i', a, b, τ, hs, hi, hs', hi', ha, hb, hτ⟩ :=
    (GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv).1 D D' φ x
  rw [h D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ, h' D D' φ x s i s' i' a b τ hs hi hs' hi' ha hb hτ]

theorem sum_split {M N P : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (Φ : M →ₗ[R] N →ₗ[R] P) {n : ℕ} (a a₁ : Fin n → M) (b b₁ : Fin n → N)
    (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) :
    ∑ k, Φ (a k) (b k) = ∑ k, Φ (a₁ k) (b k) + ∑ k, Φ (a k - a₁ k) (b₁ k) := by
  have h0 : ∑ k, Φ (a k - a₁ k) (b k - b₁ k) = 0 := by
    have := congrArg (TensorProduct.lift Φ) h
    simpa only [map_sum, TensorProduct.lift.tmul, map_zero] using this
  rw [← Finset.sum_add_distrib, ← sub_eq_zero, ← Finset.sum_sub_distrib, ← h0]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp only [map_sub, LinearMap.sub_apply]
  abel

theorem fv_sub_sum {X : Over (Sp R)} {n : ℕ} (f : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (t : Fin n → R)
    (u : Fin n → Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D] [Algebra R D] (D' : Type)
    [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (f - ∑ k, t k • u k) D D' φ x = fv f D D' φ x - ∑ k, algebraMap R D' (t k) * fv (u k) D D' φ x := by
  simp only [fv, ev, Submodule.coe_sub, Submodule.coe_sum, Submodule.coe_smul, Pi.sub_apply,
    Finset.sum_apply, Pi.smul_apply, Algebra.smul_def]
  rfl

theorem fv_smul {X : Over (Sp R)} (t : R) (u : Z1 (O (dp0 R) (X.hom ≫ 𝟙 _))) (D : Type) [CommRing D]
    [Algebra R D] (D' : Type) [CommRing D'] [Algebra R D'] (φ : D →ₐ[R] D') (x : Pt X D) :
    fv (t • u) D D' φ x = algebraMap R D' t * fv u D D' φ x := by
  simp only [fv, ev, Submodule.coe_smul, Pi.smul_apply, Algebra.smul_def]

section Rep

variable (m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left)
  (m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left)

omit [GrpObj A] [GrpObj B] in

def cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  cupZ _ (m₁.coef.pullbackOneCocycle a) (m₂.coef.pullbackOneCocycle b)

omit [GrpObj A] [GrpObj B] in

theorem mk_cupPr (a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) (CatCoh.H1.mk _ a))
      (pullOver (dp0 R) (𝟙 _) (snd A B) (CatCoh.H1.mk _ b)) := rfl

def cupPrim (A B : Over (Sp R)) [GrpObj A] [GrpObj B] :
    primDR A →ₗ[R] primDR B →ₗ[R] CatCoh.H2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  (cup _).compl₁₂ (pullOver (dp0 R) (𝟙 _) (fst A B) ∘ₗ (primDR A).subtype)
    (pullOver (dp0 R) (𝟙 _) (snd A B) ∘ₗ (primDR B).subtype)

theorem cupPrim_apply (a : primDR A) (b : primDR B) : cupPrim A B a b =
    cup _ (pullOver (dp0 R) (𝟙 _) (fst A B) a.1) (pullOver (dp0 R) (𝟙 _) (snd A B) b.1) := rfl

theorem mk_cupPr_prim {a : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {b : Z1 (O (dp0 R) (B.hom ≫ 𝟙 _))} {x : primDR A}
    {y : primDR B} (ha : CatCoh.H1.mk _ a = x.1) (hb : CatCoh.H1.mk _ b = y.1) :
    CatCoh.H2.mk _ (cupPr m₁ m₂ a b) = cupPrim A B x y := by
  rw [mk_cupPr, cupPrim_apply, ha, hb]

variable {n : ℕ} (α : Fin n → Form (A.hom ≫ 𝟙 _)) (β : Fin n → Form (B.hom ≫ 𝟙 _))
  (a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))) (b' : Fin n → Z1 (O (dp0 R) (B.hom ≫ 𝟙 _)))

omit [GrpObj A] [GrpObj B] in

def rep : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) :=
  ∑ k, cupPr m₁ m₂ (α k).1 (b' k) + ∑ k, cupPr m₁ m₂ (a' k) (β k).1

omit [GrpObj A] [GrpObj B] in

theorem rep_val : (rep m₁ m₂ α β a' b').1 =
    ∑ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 + ∑ k, (cupPr m₁ m₂ (a' k) (β k).1).1 := by
  rw [rep, Submodule.coe_add, Submodule.coe_sum, Submodule.coe_sum]

omit [GrpObj A] [GrpObj B] in

theorem mk_rep : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') =
    ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (α k).1 (b' k)) + ∑ k, CatCoh.H2.mk _ (cupPr m₁ m₂ (a' k) (β k).1) :=
  ((CatCoh.H2.mk _).map_add _ _).trans (congrArg₂ (· + ·) (map_sum _ _ _) (map_sum _ _ _))

omit [GrpObj A] [GrpObj B] in

theorem rep_triv (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (p : T ⟶ T') (q : T' ⟶ T'') (hT : T.J = ⊥)
    (hT' : T'.J = ⊥) (hT'' : T''.J = ⊥) : (rep m₁ m₂ α β a' b').1 T T' T'' p q = 0 := by
  have h1 : ∀ k, (cupPr m₁ m₂ (α k).1 (b' k)).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₁.coef.pullbackOneCocycle (α k).1).1 T T' p = 0 from (α k).2 (m₁.functor.map p) hT hT', map_zero, zero_mul]
  have h2 : ∀ k, (cupPr m₁ m₂ (a' k) (β k).1).1 T T' T'' p q = 0 := fun k ↦ by
    rw [cupPr, cupZ_apply,
      show (m₂.coef.pullbackOneCocycle (β k).1).1 T' T'' q = 0 from (β k).2 (m₂.functor.map q) hT' hT'', mul_zero]
  rw [rep_val]
  simp only [Pi.add_apply, Finset.sum_apply, h1, h2, Finset.sum_const_zero, add_zero]

theorem rep_contr {v : epsR R ⟶ B} (hv : IsTangent v) (f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)))
    (hcl : CatCoh.H1.mk _ (f - ∑ k, tanVal v (β k) • a' k) ∈ F1 (A.hom ≫ 𝟙 _)) (κ : Fn1 A)
    (hκ : IsContr (rep m₁ m₂ α β a' b').1 v κ) : Cohom (whole A) κ (fv f).neg := by
  obtain ⟨-, hex⟩ := GlobalTheory.PtExt.ContrMor.exists_contr R A B v hv
  choose κX hκX using fun k ↦ hex (cupPr m₁ m₂ (α k).1 (b' k)).1
  choose κY hκY using fun k ↦ hex (cupPr m₁ m₂ (a' k) (β k).1).1
  rw [rep_val] at hκ
  have hsC := isContr_add (isContr_sum hκX) (isContr_sum hκY)
  have hX0 := fun k ↦ GlobalTheory.PtExt.contr_cup_form_eq_zero R A B m₁ m₂ v hv (α k) (b' k) (κX k) (hκX k)
  have hYc := fun k ↦ GlobalTheory.PtExt.cohom_contr_cupA R A B m₁ m₂ v hv (a' k) (β k) (κY k) (hκY k)
  unfold Cohom at hYc
  choose cY hcY using hYc
  obtain ⟨k₀, hk₀⟩ := (GlobalTheory.PtExt.mem_hodgeFiltration_iff_pointwiseCoboundary R A _).1 hcl
  refine ⟨fun D _ _ x ↦ k₀ D x + ∑ k, cY k D x, ?_⟩
  intro D _ _ D' _ _ φ x _
  have e1 := isContr_eq hv hκ hsC D D' φ x
  have e2 := hk₀ D D' φ x (sm_whole x)
  have e3 : ∀ k, κY k D D' φ x = cY k D' (spOver φ ≫ x) - φ (cY k D x) -
      algebraMap R D' (tanVal v (β k)) * fv (a' k) D D' φ x := fun k ↦ by
    have h3 := hcY k D D' φ x (sm_whole x)
    simp only [Fn1.add, Fn1.neg, fv_smul, map_neg] at h3
    linear_combination h3
  rw [fv_sub_sum] at e2
  simp only [Fn1.add, Fn1.neg, hX0, Finset.sum_const_zero, zero_add] at e1 ⊢
  rw [e1, map_add, map_sum]
  simp only [e3, Finset.sum_sub_distrib]
  linear_combination e2

end Rep

theorem apply_sub_sum {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {n : ℕ}
    (a a₁ : Fin n → M) (b b₁ : Fin n → N) (h : ∑ k, (a k - a₁ k) ⊗ₜ[R] (b k - b₁ k) = 0) (x : M →ₗ[R] R)
    (y : N →ₗ[R] R) (hx : ∀ k, x (a₁ k) = 0) (c : M) (hc : x c = ∑ k, x (a k) * y (b k)) :
    x (c - ∑ k, y (b₁ k) • (a k - a₁ k)) = 0 := by
  have e := sum_split ((LinearMap.mul R R).compl₁₂ x y) a a₁ b b₁ h
  simp only [LinearMap.compl₁₂_apply, LinearMap.mul_apply'] at e
  simp only [map_sub, hx, sub_zero, zero_mul, Finset.sum_const_zero, zero_add] at e
  rw [map_sub, map_sum, hc, e]
  simp only [map_smul, map_sub, hx, sub_zero, smul_eq_mul, mul_comm, sub_self]

theorem mk_sub_sum {n : ℕ} {f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {c : primDR A} (hf : CatCoh.H1.mk _ f = c.1)
    {a' : Fin n → Z1 (O (dp0 R) (A.hom ≫ 𝟙 _))} {a : Fin n → primDR A} (ha : ∀ k, CatCoh.H1.mk _ (a' k) = (a k).1)
    (t : Fin n → R) : CatCoh.H1.mk _ (f - ∑ k, t k • a' k) = (c - ∑ k, t k • a k : primDR A).1 := by
  rw [map_sub, map_sum, hf, Submodule.coe_sub, Submodule.coe_sum]
  congr 1
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, ha k, Submodule.coe_smul]

end GlobalTheory.PtExt.ChernRep

open GlobalTheory.PtExt.ChernRep in

theorem GlobalTheory.PtExt.exists_chernRep_contr_of_orth : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, P.IsLB → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → (∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0) → ∀ (h' : HdR B) (v : epsR R ⟶ B), IsLieImage h' v → ∀ c : primDR A, (∀ h ∈ Fil A, φ h h' = h c) → ∀ f : Z1 (O (dp0 R) (A.hom ≫ 𝟙 _)), CatCoh.H1.mk _ f = c.1 → ∃ w : Z2 (O (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)), IsChern (dp0 R) _ P (CatCoh.H2.mk _ w) ∧ (∀ (T T' T'' : Thick (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _)) (a : T ⟶ T') (b : T' ⟶ T''), T.J = ⊥ → T'.J = ⊥ → T''.J = ⊥ → w.1 T T' T'' a b = 0) ∧ ∀ κ : Fn1 A, IsContr w.1 v κ → Cohom (whole A) κ (fv f).neg := by
  intro hHDR R _ A B _ _ g hA hB hgA hgB P hP pf hpf horth h' v hv c hc f hf
  obtain ⟨hFree, hHodge, -⟩ := GlobalTheory.abelianDeRham_free_hodge_baseChange hHDR
  obtain ⟨-, hprA, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hA hgA
  obtain ⟨-, hprB, -⟩ := GlobalTheory.Published.AbelianDeRham.Free.prim hFree hB hgB
  obtain ⟨-, hCA, -⟩ := hHodge R A g hA hgA
  obtain ⟨-, hCB, -⟩ := hHodge R B g hB hgB
  obtain ⟨n, a, b, hch, hab⟩ := hpf
  have L := GlobalTheory.tensor_mem_of_dualAnnihilator R (primDR A) (primDR B) (PrimitiveSubmodule A) (PrimitiveSubmodule B) hCA hCB
  obtain ⟨a₁, b₁, ha₁, hb₁, hsum⟩ := L.2 n a b fun x hx y hy ↦ (hab x y).symm.trans (horth x hx y hy)
  have eα : ∀ k, ∃ α : Form (A.hom ≫ 𝟙 _), Form.cl _ α = (a₁ k).1 := fun k ↦ by
    have h := ha₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose α hα using eα
  have eβ : ∀ k, ∃ β : Form (B.hom ≫ 𝟙 _), Form.cl _ β = (b₁ k).1 := fun k ↦ by
    have h := hb₁ k
    rw [PrimitiveSubmodule, Submodule.mem_comap, hodgeFiltration_eq_range] at h
    exact h
  choose β hβ using eβ
  choose b' hb' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (B.hom ≫ 𝟙 _)) (b k).1
  choose a' ha' using fun k ↦ CatCoh.H1.mk_surjective (O (dp0 R) (A.hom ≫ 𝟙 _)) (a k - a₁ k).1
  have m₁ : IsMor (dp0 R) (A.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (fst A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  have m₂ : IsMor (dp0 R) (B.hom ≫ 𝟙 _) (dp0 R) ((A ⊗ B).hom ≫ 𝟙 _) (RingHom.id R) (snd A B).left :=
    IsMor.of_over _ (by rw [← Category.assoc, Over.w])
  refine ⟨rep m₁ m₂ α β a' b', ?_, rep_triv m₁ m₂ α β a' b', rep_contr m₁ m₂ α β a' b' hv.1 f ?_⟩
  · have hz : CatCoh.H2.mk _ (rep m₁ m₂ α β a' b') = ∑ k, cupPrim A B (a k) (b k) :=
      ((mk_rep m₁ m₂ α β a' b').trans (congrArg₂ (· + ·)
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (hα k) (hb' k))
        (Finset.sum_congr rfl fun k _ ↦ mk_cupPr_prim m₁ m₂ (ha' k) (hβ k)))).trans
        (sum_split (cupPrim A B) a a₁ b b₁ hsum).symm
    exact hz ▸ hch
  · have ht : (fun k ↦ tanVal v (β k)) = fun k ↦ h' (b₁ k) := funext fun k ↦ by
      have hm : Form.cl _ (β k) ∈ primDR B := (hβ k).symm ▸ (b₁ k).2
      exact (hv.2 (β k) hm).symm.trans (congrArg h' (Subtype.ext (hβ k)))
    have hd : c - ∑ k, h' (b₁ k) • (a k - a₁ k) ∈ PrimitiveSubmodule A := L.1 _ fun x hx ↦
      apply_sub_sum a a₁ b b₁ hsum x h' (fun k ↦ (Submodule.mem_dualAnnihilator _).1 hx _ (ha₁ k)) c
        ((hc x hx).symm.trans (hab x h'))
    rw [mk_sub_sum hf ha' fun k ↦ tanVal v (β k)]
    simp only [fun k ↦ congrFun ht k]
    exact hd
