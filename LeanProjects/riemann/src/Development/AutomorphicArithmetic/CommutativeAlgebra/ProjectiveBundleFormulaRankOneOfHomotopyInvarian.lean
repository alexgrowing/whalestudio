import Development.AutomorphicArithmetic.CupPullbacks.ConstCompSingle
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiIsoHypercohomologyBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupProductGradedCommStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateTwistCupUnitAndPrimitiveRootClassesStatement

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC UpperTheory.Pbf Simplicial

noncomputable section

namespace UpperTheory.Rank1

private def tupP (m : ℕ) : PSh where
  obj T := Fin m → (Γ(T.unop, ⊤))ˣ
  map g := TypeCat.ofHom fun v k => Units.map g.unop.appTop.hom.toMonoidHom (v k)
  map_id T := by
    ext v k
    simp
  map_comp f g := by
    ext v k
    simp
    rfl

private def Cn : Spc where
  obj k := tupP (k.unop.len + 1)
  map θ :=
    { app := fun T => TypeCat.ofHom fun v => v ∘ θ.unop.toOrderHom
      naturality := fun T T' g => by
        ext v k
        rfl }
  map_id k := by
    ext T v j
    rfl
  map_comp f g := by
    ext T v j
    rfl

private def hT {A : Type} [One A] {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → A) : Fin (n + 2) → A :=
  fun k => if h : (k : ℕ) ≤ i then v ⟨k, by omega⟩ else 1

private theorem sa_val {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    ((i.succAbove k : Fin (n + 2)) : ℕ) = if (k : ℕ) < i then (k : ℕ) else k + 1 := by
  unfold Fin.succAbove
  split_ifs with h h' <;> simp [Fin.lt_def] at * <;> omega

private theorem pa_val {n : ℕ} (i : Fin (n + 1)) (k : Fin (n + 2)) :
    ((i.predAbove k : Fin (n + 1)) : ℕ) = if (i : ℕ) < k then (k : ℕ) - 1 else k := by
  by_cases h : (i : ℕ) < k
  · have h' : i.castSucc < k := by
      rw [Fin.lt_def]
      simpa using h
    rw [Fin.predAbove_of_castSucc_lt _ _ h', Fin.coe_pred, if_pos h]
  · have h' : k ≤ i.castSucc := by
      rw [Fin.le_def]
      simp
      omega
    rw [Fin.predAbove_of_le_castSucc _ _ h', Fin.coe_castPred, if_neg h]

private theorem hT_val {A : Type} [One A] {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → A) (k : Fin (n + 2)) (a : Fin (n + 1))
    (h : (k : ℕ) ≤ i) (ha : (a : ℕ) = k) : hT i v k = v a := by
  unfold hT
  rw [dif_pos h]
  congr 1
  exact Fin.ext ha.symm

private theorem hT_one {A : Type} [One A] {n : ℕ} (i : Fin (n + 1)) (v : Fin (n + 1) → A) (k : Fin (n + 2))
    (h : (i : ℕ) < k) : hT i v k = 1 := by
  unfold hT
  rw [dif_neg (by omega)]

private theorem hT_a {A : Type} [One A] {n : ℕ} (v : Fin (n + 1) → A) (j : Fin (n + 1)) :
    hT 0 v ((0 : Fin (n + 2)).succAbove j) = 1 :=
  hT_one _ _ _ (by simp [sa_val])

private theorem hT_b {A : Type} [One A] {n : ℕ} (v : Fin (n + 1) → A) (j : Fin (n + 1)) :
    hT (Fin.last n) v ((Fin.last (n + 1)).succAbove j) = v j :=
  hT_val _ _ _ _ (by simp [sa_val]; omega) (by simp [sa_val])

private theorem hT_eq_hT_of_le_iff_of_apply_eq {A : Type} [One A] {n m : ℕ} (a : Fin (n + 1)) (b : Fin (m + 1)) (v : Fin (n + 1) → A)
    (w : Fin (m + 1) → A) (x : Fin (n + 2)) (y : Fin (m + 2)) (h1 : (x : ℕ) ≤ a ↔ (y : ℕ) ≤ b)
    (h2 : ∀ (hx : (x : ℕ) ≤ a) (hy : (y : ℕ) ≤ b), v ⟨x, by omega⟩ = w ⟨y, by omega⟩) :
    hT a v x = hT b w y := by
  unfold hT
  by_cases hx : (x : ℕ) ≤ a
  · rw [dif_pos hx, dif_pos (h1.mp hx)]
    exact h2 hx (h1.mp hx)
  · rw [dif_neg hx, dif_neg (fun hy => hx (h1.mpr hy))]

private theorem hT_c {A : Type} [One A] {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hij : i ≤ j.castSucc) (v : Fin (n + 2) → A)
    (k : Fin (n + 2)) : hT j.succ v (i.castSucc.succAbove k) = hT j (v ∘ i.succAbove) k := by
  rw [Fin.le_def, Fin.coe_castSucc] at hij
  refine hT_eq_hT_of_le_iff_of_apply_eq _ _ _ _ _ _ ?_ ?_
  · simp only [sa_val, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · intro hx hy
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    simp only [sa_val, Fin.coe_castSucc, Fin.val_succ, Fin.val_mk] at hx hy ⊢
    all_goals (split_ifs at hx hy ⊢ <;> omega)

private theorem hT_d {A : Type} [One A] {n : ℕ} (j : Fin (n + 1)) (v : Fin (n + 2) → A)
    (k : Fin (n + 2)) : hT j.succ v (j.castSucc.succ.succAbove k) = hT j.castSucc v (j.castSucc.succ.succAbove k) := by
  refine hT_eq_hT_of_le_iff_of_apply_eq _ _ _ _ _ _ ?_ (fun _ _ => rfl)
  simp only [sa_val, Fin.coe_castSucc, Fin.val_succ]
  split_ifs <;> omega

private theorem hT_e {A : Type} [One A] {n : ℕ} (i : Fin (n + 2)) (j : Fin (n + 1)) (hji : j.castSucc < i) (v : Fin (n + 2) → A)
    (k : Fin (n + 2)) : hT j.castSucc v (i.succ.succAbove k) = hT j (v ∘ i.succAbove) k := by
  rw [Fin.lt_def, Fin.coe_castSucc] at hji
  refine hT_eq_hT_of_le_iff_of_apply_eq _ _ _ _ _ _ ?_ ?_
  · simp only [sa_val, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · intro hx hy
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    simp only [sa_val, Fin.coe_castSucc, Fin.val_succ, Fin.val_mk] at hx hy ⊢
    split_ifs at hx hy ⊢ <;> omega

private theorem hT_f {A : Type} [One A] {n : ℕ} (i j : Fin (n + 1)) (hij : i ≤ j) (v : Fin (n + 1) → A)
    (k : Fin (n + 3)) : hT j v (i.castSucc.predAbove k) = hT j.succ (v ∘ i.predAbove) k := by
  rw [Fin.le_def] at hij
  refine hT_eq_hT_of_le_iff_of_apply_eq _ _ _ _ _ _ ?_ ?_
  · simp only [pa_val, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · intro hx hy
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    simp only [pa_val, Fin.coe_castSucc, Fin.val_succ, Fin.val_mk] at hx hy ⊢
    all_goals (split_ifs at hx hy ⊢ <;> omega)

private theorem hT_g {A : Type} [One A] {n : ℕ} (i j : Fin (n + 1)) (hji : j ≤ i) (v : Fin (n + 1) → A)
    (k : Fin (n + 3)) : hT j v (i.succ.predAbove k) = hT j.castSucc (v ∘ i.predAbove) k := by
  rw [Fin.le_def] at hji
  refine hT_eq_hT_of_le_iff_of_apply_eq _ _ _ _ _ _ ?_ ?_
  · simp only [pa_val, Fin.coe_castSucc, Fin.val_succ]
    split_ifs <;> omega
  · intro hx hy
    simp only [Function.comp_apply]
    congr 1
    apply Fin.ext
    simp only [pa_val, Fin.coe_castSucc, Fin.val_succ, Fin.val_mk] at hx hy ⊢
    split_ifs at hx hy ⊢ <;> omega

private theorem hT_map {A B : Type} [One A] [One B] {n : ℕ} (f : A → B) (hf : f 1 = 1) (i : Fin (n + 1)) (v : Fin (n + 1) → A)
    (k : Fin (n + 2)) : f (hT i v k) = hT i (f ∘ v) k := by
  unfold hT
  split_ifs <;> simp [hf]

private def kap : Cn ⟶ Cn where
  app k :=
    { app := fun T => TypeCat.ofHom fun _ _ => 1
      naturality := fun T T' g => by
        ext v
        funext j
        exact (map_one (Units.map g.unop.appTop.hom.toMonoidHom)).symm }
  naturality k k' θ := by
    ext T v
    rfl

private def Hc : SimplicialObject.Homotopy (𝟙 Cn) kap where
  h {n} i :=
    { app := fun T => TypeCat.ofHom (hT i)
      naturality := fun T T' g => by
        ext v
        funext k
        exact (hT_map (Units.map g.unop.appTop.hom.toMonoidHom) (map_one _) i v k).symm }
  h_zero_comp_δ_zero n := by
    ext T v
    funext j
    exact hT_a v j
  h_last_comp_δ_last n := by
    ext T v
    funext j
    exact hT_b v j
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    ext T v
    funext k
    exact hT_c i j hij v k
  h_succ_comp_δ_castSucc_succ j := by
    ext T v
    funext k
    exact hT_d j v k
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    ext T v
    funext k
    exact hT_e i j hji v k
  h_comp_σ_castSucc_of_le i j hij := by
    ext T v
    funext k
    exact hT_f i j hij v k
  h_comp_σ_succ_of_lt i j hji := by
    ext T v
    funext k
    exact hT_g i j hji v k

private def liftH {C : Type*} [Category C] {X Y₁ Y₂ : SimplicialObject C} (p₁ : X ⟶ Y₁) (p₂ : X ⟶ Y₂)
    (jm : ∀ (k : SimplexCategoryᵒᵖ) (T : C) (a b : T ⟶ X.obj k), a ≫ p₁.app k = b ≫ p₁.app k →
      a ≫ p₂.app k = b ≫ p₂.app k → a = b)
    {f g : X ⟶ X} {f₁ g₁ : Y₁ ⟶ Y₁} {f₂ g₂ : Y₂ ⟶ Y₂}
    (H₁ : SimplicialObject.Homotopy f₁ g₁) (H₂ : SimplicialObject.Homotopy f₂ g₂)
    (hf₁ : f ≫ p₁ = p₁ ≫ f₁) (hf₂ : f ≫ p₂ = p₂ ≫ f₂) (hg₁ : g ≫ p₁ = p₁ ≫ g₁) (hg₂ : g ≫ p₂ = p₂ ≫ g₂)
    (l : ∀ {n : ℕ} (_ : Fin (n + 1)), X _⦋n⦌ ⟶ X _⦋n + 1⦌)
    (l₁ : ∀ {n : ℕ} (i : Fin (n + 1)), l i ≫ p₁.app _ = p₁.app _ ≫ H₁.h i)
    (l₂ : ∀ {n : ℕ} (i : Fin (n + 1)), l i ≫ p₂.app _ = p₂.app _ ≫ H₂.h i) :
    SimplicialObject.Homotopy f g := by
  have l₁' : ∀ {n : ℕ} (i : Fin (n + 1)) {Z : C} (t : Y₁ _⦋n + 1⦌ ⟶ Z), l i ≫ p₁.app _ ≫ t = p₁.app _ ≫ H₁.h i ≫ t :=
    fun i _ t => by rw [← Category.assoc, l₁, Category.assoc]
  have l₂' : ∀ {n : ℕ} (i : Fin (n + 1)) {Z : C} (t : Y₂ _⦋n + 1⦌ ⟶ Z), l i ≫ p₂.app _ ≫ t = p₂.app _ ≫ H₂.h i ≫ t :=
    fun i _ t => by rw [← Category.assoc, l₂, Category.assoc]
  have e₁ := fun k => NatTrans.congr_app hf₁ k
  have e₂ := fun k => NatTrans.congr_app hf₂ k
  have e₃ := fun k => NatTrans.congr_app hg₁ k
  have e₄ := fun k => NatTrans.congr_app hg₂ k
  simp only [NatTrans.comp_app] at e₁ e₂ e₃ e₄
  exact
  { h := l
    h_zero_comp_δ_zero := fun n => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₁', H₁.h_zero_comp_δ_zero, e₃])
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₂', H₂.h_zero_comp_δ_zero, e₄])
    h_last_comp_δ_last := fun n => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₁', H₁.h_last_comp_δ_last, e₁])
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₂', H₂.h_last_comp_δ_last, e₂])
    h_succ_comp_δ_castSucc_of_lt := fun i j hij => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality_assoc, l₁', l₁,
            H₁.h_succ_comp_δ_castSucc_of_lt i j hij])
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality_assoc, l₂', l₂,
            H₂.h_succ_comp_δ_castSucc_of_lt i j hij])
    h_succ_comp_δ_castSucc_succ := fun j => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₁', H₁.h_succ_comp_δ_castSucc_succ j])
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, l₂', H₂.h_succ_comp_δ_castSucc_succ j])
    h_castSucc_comp_δ_succ_of_lt := fun i j hji => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality_assoc, l₁', l₁,
            H₁.h_castSucc_comp_δ_succ_of_lt i j hji])
      (by simp only [Category.assoc, SimplicialObject.δ_naturality, SimplicialObject.δ_naturality_assoc, l₂', l₂,
            H₂.h_castSucc_comp_δ_succ_of_lt i j hji])
    h_comp_σ_castSucc_of_le := fun i j hij => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.σ_naturality, SimplicialObject.σ_naturality_assoc, l₁', l₁,
            H₁.h_comp_σ_castSucc_of_le i j hij])
      (by simp only [Category.assoc, SimplicialObject.σ_naturality, SimplicialObject.σ_naturality_assoc, l₂', l₂,
            H₂.h_comp_σ_castSucc_of_le i j hij])
    h_comp_σ_succ_of_lt := fun i j hji => jm _ _ _ _
      (by simp only [Category.assoc, SimplicialObject.σ_naturality, SimplicialObject.σ_naturality_assoc, l₁', l₁,
            H₁.h_comp_σ_succ_of_lt i j hji])
      (by simp only [Category.assoc, SimplicialObject.σ_naturality, SimplicialObject.σ_naturality_assoc, l₂', l₂,
            H₂.h_comp_σ_succ_of_lt i j hji]) }

private theorem unimodularRow_one_isUnit {A : Type} [CommRing A] (v : Um 1 A) : IsUnit (v.1 0) := by
  have h := v.2
  rw [Set.range_unique] at h
  exact Ideal.span_singleton_eq_top.mp h

private def toU {A : Type} [CommRing A] (v : Um 1 A) : Aˣ := (unimodularRow_one_isUnit v).unit

private def ofU {A : Type} [CommRing A] (u : Aˣ) : Um 1 A :=
  ⟨fun _ => u, by
    refine Ideal.eq_top_of_isUnit_mem _ (Ideal.subset_span ⟨0, rfl⟩) u.isUnit⟩

private theorem toU_ofU {A : Type} [CommRing A] (u : Aˣ) : toU (ofU u) = u := Units.ext rfl

private theorem ofU_toU {A : Type} [CommRing A] (v : Um 1 A) : ofU (toU v) = v := by
  apply Subtype.ext
  funext i
  fin_cases i
  rfl

private theorem rankOne_hom_ext {A : Type} [CommRing A] {v w : Um 1 A} (p p' : v ⟶ w) (h : p.1.1 = p'.1.1) : p = p' := by
  have e1 := p.2
  have e2 := p'.2
  rw [h] at e1
  have e3 : ((p.1.2 : A) • w.1) 0 = ((p'.1.2 : A) • w.1) 0 := by
    rw [← e1, ← e2]
  simp only [Pi.smul_apply, smul_eq_mul] at e3
  have e4 : (p.1.2 : A) = p'.1.2 := (unimodularRow_one_isUnit w).mul_right_cancel e3
  exact Subtype.ext (Prod.ext h (Units.ext e4))

private def arr {A : Type} [CommRing A] (u w : Aˣ) : ofU u ⟶ ofU w :=
  ⟨(1, u * w⁻¹), by
    funext i
    simp [ofU]⟩

private theorem eqToHom_g {A : Type} [CommRing A] {v w : Um 1 A} (h : v = w) : (eqToHom h).1.1 = 1 := by
  subst h
  rfl

private theorem chain_ext {A : Type} [CommRing A] {m : ℕ} (F G : Fin m ⥤ Um 1 A) (h : ∀ k, F.obj k = G.obj k)
    (hg : ∀ {a b : Fin m} (f : a ⟶ b), (F.map f).1.1 = (G.map f).1.1) : F = G := by
  have hc : ∀ {u v w : Um 1 A} (p : u ⟶ v) (p' : v ⟶ w), (p ≫ p').1.1 = p'.1.1 * p.1.1 :=
    fun _ _ => rfl
  refine CategoryTheory.Functor.ext h (fun a b f => ?_)
  apply rankOne_hom_ext
  rw [hc, hc, eqToHom_g, eqToHom_g, one_mul, mul_one]
  exact hg f

private def chainOf {A : Type} [CommRing A] {m : ℕ} (v : Fin m → Aˣ) : Fin m ⥤ Um 1 A where
  obj k := ofU (v k)
  map {a b} _ := arr (v a) (v b)
  map_id a := rankOne_hom_ext _ _ rfl
  map_comp f g := rankOne_hom_ext _ _ (mul_one _).symm

private def phi : Cn ⟶ PGL 1 where
  app k :=
    { app := fun T => TypeCat.ofHom fun v => (chainOf v : Fin (k.unop.len + 1) ⥤ Um 1 Γ(T.unop, ⊤))
      naturality := fun T T' g => by
        ext v
        exact chain_ext _ _ (fun j => Subtype.ext (funext fun _ => rfl))
          (fun f => (map_one (Matrix.GeneralLinearGroup.map (n := Fin 1) g.unop.appTop.hom)).symm) }
  naturality k k' θ := by
    ext T v
    exact chain_ext _ _ (fun j => rfl) (fun f => rfl)

private def ob : PGL 1 ⟶ Cn where
  app k :=
    { app := fun T => TypeCat.ofHom fun c j => toU ((show Fin (k.unop.len + 1) ⥤ Um 1 Γ(T.unop, ⊤) from c).obj j)
      naturality := fun T T' g => by
        ext v
        funext j
        exact Units.ext rfl }
  naturality k k' θ := by
    ext T v
    rfl

private theorem phi_ob : phi ≫ ob = 𝟙 Cn := by
  ext k T v
  funext j
  exact toU_ofU _

private abbrev X1 (E : Spc) : Spc := pullback (triv E 1) (PGL.pr 1)

private abbrev fst1 (E : Spc) : X1 E ⟶ E := pullback.fst _ _

private abbrev snd1 (E : Spc) : X1 E ⟶ PGL 1 := pullback.snd _ _

private theorem isPB (E : Spc) (k : SimplexCategoryᵒᵖ) :
    IsPullback ((fst1 E).app k) ((snd1 E).app k) ((triv E 1).app k) ((PGL.pr 1).app k) :=
  (IsPullback.of_hasPullback (triv E 1) (PGL.pr 1)).map ((evaluation _ _).obj k)

private theorem comp_triv {E E' : Spc} (f : E ⟶ E') : f ≫ triv E' 1 = triv E 1 := by
  ext k T x
  rfl

private theorem phi_pr : phi ≫ PGL.pr 1 = triv Cn 1 := by
  ext k T v
  rfl

private def c1 (E : Spc) : E ⟶ Cn where
  app k :=
    { app := fun T => TypeCat.ofHom fun _ _ => 1
      naturality := fun T T' g => by
        ext v
        funext j
        exact (map_one (Units.map g.unop.appTop.hom.toMonoidHom)).symm }
  naturality k k' θ := by
    ext T v
    rfl

private def sec1 (E : Spc) : E ⟶ X1 E :=
  pullback.lift (𝟙 E) (c1 E ≫ phi) (by rw [Category.assoc, phi_pr, comp_triv, comp_triv])

private theorem diagonal_section_fst (E : Spc) : sec1 E ≫ fst1 E = 𝟙 E := pullback.lift_fst _ _ _

private theorem diagonal_section_snd (E : Spc) : sec1 E ≫ snd1 E = c1 E ≫ phi := pullback.lift_snd _ _ _

private theorem snd_ob_phi (E : Spc) : snd1 E ≫ ob ≫ phi = snd1 E := by
  ext k T x
  apply chain_ext
  · intro j
    exact ofU_toU _
  · intro a b f
    have hc := congr_arg (fun φ => ((φ.app k).app T) x) (pullback.condition (f := triv E 1) (g := PGL.pr 1))
    simp only [NatTrans.comp_app] at hc
    have h2 := CategoryTheory.Functor.congr_hom hc f
    have h3 : (𝟙 (SingleObj.star (GL (Fin 1) Γ(T.unop, ⊤)))) =
        𝟙 _ ≫ (show SingleObj.star (GL (Fin 1) Γ(T.unop, ⊤)) ⟶ SingleObj.star _ from
          ((show Fin ((unop k).len + 1) ⥤ Um 1 Γ(T.unop, ⊤) from ((snd1 E).app k).app T x).map f).1.1) ≫ 𝟙 _ :=
      h2
    rw [Category.id_comp, Category.comp_id] at h3
    exact h3

private def H1 (E : Spc) : SimplicialObject.Homotopy (𝟙 (X1 E)) (fst1 E ≫ sec1 E) := by
  have e : ∀ k, (snd1 E).app k ≫ ob.app k ≫ phi.app k = (snd1 E).app k :=
    fun k => NatTrans.congr_app (snd_ob_phi E) k
  have eo : ∀ k, phi.app k ≫ ob.app k = 𝟙 _ := fun k => NatTrans.congr_app phi_ob k
  have cond : ∀ {n : ℕ} (i : Fin (n + 1)),
      ((fst1 E).app (op ⦋n⦌) ≫ E.σ i) ≫ (triv E 1).app (op ⦋n + 1⦌) =
        ((snd1 E ≫ ob).app (op ⦋n⦌) ≫ Hc.h i ≫ phi.app (op ⦋n + 1⦌)) ≫ (PGL.pr 1).app (op ⦋n + 1⦌) := by
    intro n i
    have h := NatTrans.congr_app phi_pr (op ⦋n + 1⦌)
    simp only [NatTrans.comp_app] at h
    simp only [Category.assoc, NatTrans.comp_app, h]
    ext T x
    rfl
  refine liftH (fst1 E) (snd1 E ≫ ob) ?_ (SimplicialObject.Homotopy.refl (𝟙 E)) Hc ?_ ?_ ?_ ?_
    (fun {n} i => (isPB E (op ⦋n + 1⦌)).lift _ _ (cond i)) ?_ ?_
  · intro k T a b h1 h2
    refine (isPB E k).hom_ext h1 ?_
    have h3 := congrArg (· ≫ phi.app k) h2
    simp only [NatTrans.comp_app, Category.assoc, e] at h3
    exact h3
  · simp
  · simp
  · rw [Category.assoc, diagonal_section_fst, Category.comp_id]
  · rw [Category.assoc, ← Category.assoc (sec1 E), diagonal_section_snd, Category.assoc (c1 E), phi_ob, Category.comp_id]
    ext k T x
    funext j
    rfl
  · intro n i
    simp
  · intro n i
    have h := (isPB E (op ⦋n + 1⦌)).lift_snd _ _ (cond i)
    rw [NatTrans.comp_app (snd1 E) ob (op ⦋n + 1⦌), ← Category.assoc, h, Category.assoc, Category.assoc, eo, Category.comp_id]

private theorem chains_qi (R : Type) [CommRing R] (E : Spc) : QuasiIso ((chains R).map (fst1 E)) := by
  have hH : Homotopy ((chainsN R).map (𝟙 (X1 E))) ((chainsN R).map (fst1 E ≫ sec1 E)) :=
    ((H1 E).whiskerRight (free R)).toChainHomotopy
  have hH' : Homotopy ((chains R).map (𝟙 (X1 E))) ((chains R).map (fst1 E ≫ sec1 E)) :=
    hH.extend ComplexShape.embeddingDownNat
  let e : HomotopyEquiv ((chains R).obj (X1 E)) ((chains R).obj E) :=
    { hom := (chains R).map (fst1 E)
      inv := (chains R).map (sec1 E)
      homotopyHomInvId := (Homotopy.ofEq ((chains R).map_comp _ _).symm).trans
        (hH'.symm.trans (Homotopy.ofEq ((chains R).map_id _)))
      homotopyInvHomId := Homotopy.ofEq (by
        rw [← CategoryTheory.Functor.map_comp, diagonal_section_fst, CategoryTheory.Functor.map_id]) }
  exact e.quasiIso_hom

private theorem eqv1 (R : Type) [CommRing R] (E : Spc) (F : Shv R) : Eqv R (fst1 E) F := by
  haveI := chains_qi R E
  exact fun n => GlobalTheory.T.quasiIso_hypercohomology_bijective R ((chains R).map (fst1 E)) F n

section
variable {q : ℕ} {X : Spc}

private theorem cast_cast {n i n' i' n'' i'' : ℤ} (h1 : n = n') (h2 : i = i') (h3 : n' = n'') (h4 : i' = i'') (x : Ht q X n i) :
    (x.cast h1 h2).cast h3 h4 = x.cast (h1.trans h3) (h2.trans h4) := by
  subst h1 h2 h3 h4
  rfl

private theorem cast_bij {n i n' i' : ℤ} (h1 : n = n') (h2 : i = i') :
    Function.Bijective (Ht.cast h1 h2 : Ht q X n i → Ht q X n' i') := by
  subst h1 h2
  exact Function.bijective_id

private theorem cup_one' [NeZero q] (hX : Inv q X) {n i : ℤ} (x : Ht q X n i) :
    cup q x (one q X) = x.cast (by ring) (by ring) := by
  rw [GlobalTheory.T.tateTwistCupProduct_graded_comm q X x (one q X), (GlobalTheory.T.tateTwistCup_unit_and_primitiveRoot_classes q).1 X hX x, mul_zero, Int.negOnePow_zero, one_smul,
    cast_cast]

private theorem cup_one_cast [NeZero q] (hX : Inv q X) {n i m j : ℤ} (x : Ht q X n i) (hm : 0 = m) (hj : 0 = j) :
    cup q x ((one q X).cast hm hj) = x.cast (by omega) (by omega) := by
  subst hm hj
  exact cup_one' hX x

end

end UpperTheory.Rank1

end

private theorem bijective_cast_cup_cpow_of_eq_zero {q : ℕ} [NeZero q] {X : Spc} (hX : Inv q X) (x : Ht q X 2 1) (k : ℕ) (hk : k = 0)
    {N I a b : ℤ} (ha : N + 2 * (k : ℤ) = a) (hb : I + (k : ℤ) = b) :
    Function.Bijective (fun y : Ht q X N I => Ht.cast ha hb (cup q y (cpow q x k))) := by
  subst hk
  have e : ∀ y : Ht q X N I, Ht.cast ha hb (cup q y (cpow q x 0)) = y.cast (by omega) (by omega) := by
    intro y
    rw [cpow_zero, UpperTheory.Rank1.cup_one_cast hX, UpperTheory.Rank1.cast_cast]
  simp only [e]
  exact UpperTheory.Rank1.cast_bij _ _

theorem UpperTheory.projectiveBundleFormula_rank_one_of_homotopyInvariant :
    ∀ (q : ℕ) [NeZero q] (E : Spc), Inv q E → PBF q E 1 := by
  intro q _ E hE
  have hX : Inv q (pullback (triv E 1) (PGL.pr 1)) := fun U hU =>
    hE U (hU.map (((pullback.fst (triv E 1) (PGL.pr 1)).app _).app _))
  intro n i
  simp only [Fin.sum_univ_one]
  have hp := UpperTheory.Rank1.eqv1 (ZMod q) E (tw q (i - ((0 : Fin 1) : ℕ))) (n - 2 * ((0 : Fin 1) : ℕ))
  exact ((bijective_cast_cup_cpow_of_eq_zero hX _ _ rfl _ _).comp hp).comp (Equiv.piUnique _).bijective
