import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section
namespace GlobalTheory.LamCalc

open GlobalTheory.PrimNorm

section Tensor

variable {X X' Y : Scheme.{0}}

theorem exists_gen_tensor {C A B : LB Y} (a : C.ι → A.ι) (b : C.ι → B.ι) (la : ∀ i, C.U i ≤ A.U (a i))
    (lb : ∀ i, C.U i ≤ B.U (b i))
    (hg : ∀ (y : Y) i j, y ∈ C.U i → y ∈ C.U j → gm (𝟙 Y) y (C.U i ⊓ C.U j) (C.g i j) =
      gm (𝟙 Y) y (A.U (a i) ⊓ A.U (a j)) (A.g (a i) (a j)) * gm (𝟙 Y) y (B.U (b i) ⊓ B.U (b j)) (B.g (b i) (b j)))
    (s : LB.Gen A) (hs : s.IsGen) (t : LB.Gen B) (ht : t.IsGen) : ∃ u : LB.Gen C, u.IsGen := by
  refine ⟨⟨fun i => res (la i) (s.s (a i)) * res (lb i) (t.s (b i))⟩, fun i j => unit_ext fun y hy => ?_⟩
  have ma : (𝟙 Y : Y ⟶ Y) y ∈ A.U (a i) ⊓ A.U (a j) := ⟨la i hy.1, la j hy.2⟩
  have mb : (𝟙 Y : Y ⟶ Y) y ∈ B.U (b i) ⊓ B.U (b j) := ⟨lb i hy.1, lb j hy.2⟩
  have ea := (gm_res _ y _ ma _).symm.trans ((congrArg (gm (𝟙 Y) y _) (hs (a i) (a j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ ma _))))
  have eb := (gm_res _ y _ mb _).symm.trans ((congrArg (gm (𝟙 Y) y _) (ht (b i) (b j))).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) rfl (gm_res _ y _ mb _))))
  have v : ∀ i, y ∈ C.U i → gm (𝟙 Y) y (C.U i) (res (la i) (s.s (a i)) * res (lb i) (t.s (b i))) =
      gm (𝟙 Y) y (A.U (a i)) (s.s (a i)) * gm (𝟙 Y) y (B.U (b i)) (t.s (b i)) := fun i hi =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res _ y _ hi _) (gm_res _ y _ hi _))
  refine ((gm_res _ y _ hy _).trans ((v i hy.1).trans (congrArg₂ (· * ·) ea eb))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (hg y i j hy.1 hy.2)
    ((gm_res _ y _ hy _).trans (v j hy.2)))).trans ?_
  exact mul_mul_mul_comm _ _ _ _

theorem lbIso_sum {L : LB X} {M : LB X'} {K K' J J' : Type} [Fintype K] [Fintype K'] [Fintype J] [Fintype J']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ}
    {ψ : J → (Y ⟶ X')} {δ : J → ℤ} {ψ' : J' → (Y ⟶ X')} {δ' : J' → ℤ}
    (h : LBIso (LB.LinComb L φ ε) (LB.LinComb M ψ δ)) (h' : LBIso (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ')) :
    LBIso (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε')) (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ')) := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨w', hw'⟩ := h'
  have l₁ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ (p.1 ∘ Sum.inl) ⊓ LB.wchart L φ (p.2 ∘ Sum.inl) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inl k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inl k)⟩
  have l₂ : ∀ p : (J ⊕ J' → M.ι) × (K ⊕ K' → L.ι),
      LB.wchart M (Sum.elim ψ ψ') p.1 ⊓ LB.wchart L (Sum.elim φ φ') p.2 ≤
        LB.wchart M ψ' (p.1 ∘ Sum.inr) ⊓ LB.wchart L φ' (p.2 ∘ Sum.inr) := fun p y hy =>
    ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.1 (.inr k), Set.mem_iInter.2 fun k => Set.mem_iInter.1 hy.2 (.inr k)⟩
  refine exists_gen_tensor (C := LB.div (LB.LinComb M (Sum.elim ψ ψ') (Sum.elim δ δ'))
    (LB.LinComb L (Sum.elim φ φ') (Sum.elim ε ε'))) (A := LB.div (LB.LinComb M ψ δ) (LB.LinComb L φ ε))
    (B := LB.div (LB.LinComb M ψ' δ') (LB.LinComb L φ' ε')) (fun p => (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl))
    (fun p => (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)) l₁ l₂ (fun y p q hp hq => ?_) w hw w' hw'
  refine ((gm_div _ _ (𝟙 Y) y p q ⟨hp, hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
    (gm_linComb M _ _ (𝟙 Y) y p.1 q.1 hp.1 hq.1) (gm_linComb L _ _ (𝟙 Y) y p.2 q.2 hp.2 hq.2))).trans (Eq.symm ?_)
  refine (congrArg₂ (· * ·)
    ((gm_div (LB.LinComb L φ ε) (LB.LinComb M ψ δ) (𝟙 Y) y (p.1 ∘ Sum.inl, p.2 ∘ Sum.inl) (q.1 ∘ Sum.inl, q.2 ∘ Sum.inl)
      ⟨l₁ p hp, l₁ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ δ (𝟙 Y) y _ _ (l₁ p hp).1 (l₁ q hq).1) (gm_linComb L φ ε (𝟙 Y) y _ _ (l₁ p hp).2 (l₁ q hq).2)))
    ((gm_div (LB.LinComb L φ' ε') (LB.LinComb M ψ' δ') (𝟙 Y) y (p.1 ∘ Sum.inr, p.2 ∘ Sum.inr)
      (q.1 ∘ Sum.inr, q.2 ∘ Sum.inr) ⟨l₂ p hp, l₂ q hq⟩).trans (congrArg₂ (fun a b => a * b⁻¹)
      (gm_linComb M ψ' δ' (𝟙 Y) y _ _ (l₂ p hp).1 (l₂ q hq).1)
      (gm_linComb L φ' ε' (𝟙 Y) y _ _ (l₂ p hp).2 (l₂ q hq).2)))).trans ?_
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, mul_inv]
  exact mul_mul_mul_comm _ _ _ _

end Tensor

section Cube

variable {S : Scheme.{0}} {A B : Over S} [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B]
  {L : LB A.left} {M : LB B.left} {T : Over S}

omit [IsCommMonObj A] in
theorem cubeLB_isLB (hL : L.IsLB) {n : ℕ} (x : Fin n → (T ⟶ A)) : (cubeLB A x L).IsLB :=
  DVR.linComb_isLB _ hL _ _

theorem class_cubeLB {U : Type*} [CommGroup U] (cl : LB T.left → U) (m : (T.left ⟶ A.left) → U)
    (h : ∀ (I : Type) [Fintype I] (φ : I → (T.left ⟶ A.left)) (ε : I → ℤ), cl (LB.LinComb L φ ε) = ∏ k, m (φ k) ^ ε k)
    (x y : T ⟶ A) :
    cl (cubeLB A ![x, y] L) = m (x * y).left * (m x.left)⁻¹ * (m y.left)⁻¹ * m (1 : T ⟶ A).left := by
  have e := congrArg (FreeGroup.lift m |> Abelianization.lift)
    (prod_square_id x y (fun q => Abelianization.of (FreeGroup.of q)))
  simp only [diff₂, map_prod, map_zpow, map_mul, map_inv, Abelianization.lift_apply_of,
    FreeGroup.lift_apply_of] at e
  exact (h _ _ _).trans e

theorem lbIso_cubeLB_swap (hL : L.IsLB) (x y : T ⟶ A) : LBIso (cubeLB A ![x, y] L) (cubeLB A ![y, x] L) :=
  (lbIso_iff hL _ _ _ _).2 ((prod_square_id x y (cls L)).trans ((diff₂_comm _ _).trans
    (prod_square_id y x (cls L)).symm))

def cubeProd (L : LB A.left) (x y x' y' : T ⟶ A) : LB T.left :=
  LB.LinComb L (K := ULift.{0} (Finset (Fin 2)) ⊕ ULift.{0} (Finset (Fin 2)))
    (Sum.elim (fun I => (psum A ![x, y] I.down).left) (fun I => (psum A ![x', y'] I.down).left))
    (Sum.elim (fun I => (-1) ^ (2 - I.down.card)) (fun I => (-1) ^ (2 - I.down.card)))

theorem lbIso_cubeLB_mul_left (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x x' y : T ⟶ A) :
    LBIso (cubeLB A ![x * x', y] L) (cubeProd L x y x' y) := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_left (diff₃_ptCls hL hT) x x' y).trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x' y (cls L)).symm)

theorem lbIso_cubeLB_mul_right (hL : L.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen) (x y y' : T ⟶ A) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeProd L x y x y') := by
  refine (lbIso_iff hL _ _ _ _).2 ((prod_square_id _ _ (cls L)).trans ?_)
  rw [Fintype.prod_sum_type]
  exact (diff₂_mul_right (diff₃_ptCls hL hT) x y y').trans
    (congrArg₂ (· * ·) (prod_square_id x y (cls L)).symm (prod_square_id x y' (cls L)).symm)

theorem lbIso_cubeLB_mul_left_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x x' y : T ⟶ A} {u u' v : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x', y] L) (cubeLB B ![u', v] M)) :
    LBIso (cubeLB A ![x * x', y] L) (cubeLB B ![u * u', v] M) :=
  have a : (cubeProd L x y x' y).IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u' v).IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_left hL hT x x' y)
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_left hM hT' u u' v).symm)

theorem lbIso_cubeLB_mul_right_of (hL : L.IsLB) (hM : M.IsLB) (hT : ∃ t : LB.Gen (Theta A L), t.IsGen)
    (hT' : ∃ t : LB.Gen (Theta B M), t.IsGen) {x y y' : T ⟶ A} {u v v' : T ⟶ B}
    (h : LBIso (cubeLB A ![x, y] L) (cubeLB B ![u, v] M)) (h' : LBIso (cubeLB A ![x, y'] L) (cubeLB B ![u, v'] M)) :
    LBIso (cubeLB A ![x, y * y'] L) (cubeLB B ![u, v * v'] M) :=
  have a : (cubeProd L x y x y').IsLB := DVR.linComb_isLB _ hL _ _
  have b : (cubeProd M u v u v').IsLB := DVR.linComb_isLB _ hM _ _
  LBIso.trans (cubeLB_isLB hL _) a (cubeLB_isLB hM _) (lbIso_cubeLB_mul_right hL hT x y y')
    (LBIso.trans a b (cubeLB_isLB hM _) (lbIso_sum h h') (lbIso_cubeLB_mul_right hM hT' u v v').symm)

theorem lbIso_cubeLB_hom (ψ : A ⟶ B) [IsMonHom ψ] (h : LBIso L (M.pull ψ.left)) (x y : T ⟶ A) :
    LBIso (cubeLB A ![x, y] L) (cubeLB B ![x ≫ ψ, y ≫ ψ] M) := by
  obtain ⟨w, hw⟩ := h
  let ρ : (T ⟶ A) →* (T ⟶ B) := MonoidHom.mk' (· ≫ ψ) fun x y => MonObj.mul_comp x y ψ
  refine (iso_linComb ((isGen_iff w).1 hw) _ _).chartPull (chartPullId _)
    (chartPullSame M _ _ _ (𝟙 _) fun I => ?_)
  have e : (fun i => ρ (![x, y] i)) = ![x ≫ ψ, y ≫ ψ] := funext fun i => by fin_cases i <;> rfl
  rw [Category.id_comp, ← e, ← psum_hom ρ]
  rfl

variable {X Y : Over S} {f₁ : X ⟶ A} {f₂ : Y ⟶ A} {g₁ : X ⟶ B} {g₂ : Y ⟶ B}

theorem lbIso_of_lamEq (h : LamEq L f₁ f₂ M g₁ g₂) (x : T ⟶ X) (y : T ⟶ Y) :
    LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M) :=
  LBIso.chartPull (chartSquare L (lift x y) (by simp) (by simp)) (chartSquare M (lift x y) (by simp) (by simp)) h

end Cube

theorem lamEq_calculus : ∀ (S : Scheme.{0}) (X Y A B C : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] [GrpObj C] [IsCommMonObj C] (L : LB A.left) (M : LB B.left) (N : LB C.left), L.IsLB → M.IsLB → N.IsLB →
  ∀ (f₁ f₁' : X ⟶ A) (f₂ f₂' : Y ⟶ A) (g₁ g₁' : X ⟶ B) (g₂ g₂' : Y ⟶ B) (k₁ : X ⟶ C) (k₂ : Y ⟶ C),
  LamEq L f₁ f₂ L f₁ f₂ ∧ (LamEq L f₁ f₂ M g₁ g₂ → LamEq M g₁ g₂ L f₁ f₂ ∧ LamEq L f₂ f₁ M g₂ g₁ ∧ (LamEq M g₁ g₂ N k₁ k₂ → LamEq L f₁ f₂ N k₁ k₂) ∧
    (∀ (X' Y' : Over S) (a : X' ⟶ X) (b : Y' ⟶ Y), LamEq L (a ≫ f₁) (b ≫ f₂) M (a ≫ g₁) (b ≫ g₂)) ∧
    ∀ (T : Over S) (x : T ⟶ X) (y : T ⟶ Y), LBIso (cubeLB A ![x ≫ f₁, y ≫ f₂] L) (cubeLB B ![x ≫ g₁, y ≫ g₂] M)) ∧
  ((∃ t : LB.Gen (Theta A L), t.IsGen) → (∃ t : LB.Gen (Theta B M), t.IsGen) → LamEq L f₁ f₂ M g₁ g₂ → (LamEq L f₁' f₂ M g₁' g₂ → LamEq L (f₁ * f₁') f₂ M (g₁ * g₁') g₂) ∧ (LamEq L f₁ f₂' M g₁ g₂' → LamEq L f₁ (f₂ * f₂') M g₁ (g₂ * g₂'))) ∧
  ∀ ψ : A ⟶ B, IsMonHom ψ → LBIso L (M.pull ψ.left) → LamEq L f₁ f₂ M (f₁ ≫ ψ) (f₂ ≫ ψ) := by
  intro S X Y A B C _ _ _ _ _ _ L M N hL hM hN f₁ f₁' f₂ f₂' g₁ g₁' g₂ g₂' k₁ k₂
  refine ⟨(lbIso_iff hL _ _ _ _).2 rfl, fun h => ⟨LBIso.symm h, ?_, fun h' => ?_, fun X' Y' a b => ?_,
    fun T x y => lbIso_of_lamEq h x y⟩, fun hT hT' h => ⟨fun h' => ?_, fun h' => ?_⟩, fun ψ hψ h => ?_⟩
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hL _) (cubeLB_isLB hM _) (lbIso_cubeLB_swap hL _ _)
      (LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hM _)
        (lbIso_of_lamEq h (snd Y X) (fst Y X)) (lbIso_cubeLB_swap hM _ _))
  · exact LBIso.trans (cubeLB_isLB hL _) (cubeLB_isLB hM _) (cubeLB_isLB hN _) h h'
  · have e := lbIso_of_lamEq h (fst X' Y' ≫ a) (snd X' Y' ≫ b)
    simp only [Category.assoc] at e
    exact e
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_left_of hL hM hT hT' h h'
  · unfold LamEq
    rw [MonObj.comp_mul, MonObj.comp_mul]
    exact lbIso_cubeLB_mul_right_of hL hM hT hT' h h'
  · have e := lbIso_cubeLB_hom ψ h (fst X Y ≫ f₁) (snd X Y ≫ f₂)
    simp only [Category.assoc] at e
    exact e

end GlobalTheory.LamCalc
