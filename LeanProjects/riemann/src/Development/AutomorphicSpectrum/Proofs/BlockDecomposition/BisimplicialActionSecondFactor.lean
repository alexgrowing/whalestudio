import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.AbelianDeRham.AbelianHodgeDeRham.H1DimGeAbelianDim
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DnCompDn

set_option autoImplicit false

noncomputable section

open CategoryTheory TensorProduct GlobalTheory.CatCoh MainStatements.Hodge GlobalTheory.CompanionTheory.HodgeCx

namespace GlobalTheory.CompanionTheory.HopfLe

variable {R : Type} [CommRing R] {C : Type} [Category.{0} C]

def front (n : ℕ) : Fin 2 →o Fin (n + 2) := ⟨Fin.castLE (by omega), fun _ _ h ↦ h⟩

def back (n : ℕ) : Fin (n + 1) →o Fin (n + 2) := (Fin.succAboveOrderEmb 0).toOrderHom

def vert0 (n : ℕ) : Fin 1 →o Fin (n + 1) := ⟨fun _ ↦ 0, fun _ _ _ ↦ le_rfl⟩

def cup1 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (y : Cn F 1) (z : Cn F n) : Cn F (n + 1) :=
  act F (front n) y * act F (back n) z

def cup0 (F : C ⥤ CommAlgCat.{0} R) {n : ℕ} (f : Cn F 0) (z : Cn F n) : Cn F n :=
  act F (vert0 n) f * z

abbrev Y (F : C ⥤ CommAlgCat.{0} R) (p q : ℕ) : Type :=
  ∀ (c : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C), F.obj (c.obj (Fin.last p)) ⊗[R] F.obj (b.obj (Fin.last q))

def pc {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1))
    (c : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) : Fin (n + 1) ⥤ C × C :=
  (θ.monotone.functor ⋙ c).prod' (ψ.monotone.functor ⋙ b)

def pcLast {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1))
    (c : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) :
    (pc θ ψ c b).obj (Fin.last n) ⟶ (c.obj (Fin.last p), b.obj (Fin.last q)) :=
  (c.map (homOfLE (Fin.le_last _)), b.map (homOfLE (Fin.le_last _)))

def bi (F : C ⥤ CommAlgCat.{0} R) {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1)) :
    Cn (box F) n →ₗ[R] Y F p q where
  toFun w c b := mp (box F) (pcLast θ ψ c b) (w (pc θ ψ c b))
  map_add' _ _ := by funext c b; simp
  map_smul' _ _ := by funext c b; simp

def a1 (F : C ⥤ CommAlgCat.{0} R) {p p' q : ℕ} (θ : Fin (p + 1) →o Fin (p' + 1)) : Y F p q →ₗ[R] Y F p' q where
  toFun y c b := TensorProduct.map (mp F (c.map (homOfLE (Fin.le_last _)))).toLinearMap LinearMap.id
    (y (θ.monotone.functor ⋙ c) b)
  map_add' _ _ := by funext c b; exact map_add _ _ _
  map_smul' _ _ := by funext c b; exact LinearMap.map_smul _ _ _

def a2 (F : C ⥤ CommAlgCat.{0} R) {p q q' : ℕ} (ψ : Fin (q + 1) →o Fin (q' + 1)) : Y F p q →ₗ[R] Y F p q' where
  toFun y c b := TensorProduct.map LinearMap.id (mp F (b.map (homOfLE (Fin.le_last _)))).toLinearMap
    (y c (ψ.monotone.functor ⋙ b))
  map_add' _ _ := by funext c b; exact map_add _ _ _
  map_smul' _ _ := by funext c b; exact LinearMap.map_smul _ _ _

def th (q : ℕ) (i : Fin (q + 1)) : Fin (q + 2) →o Fin 2 :=
  ⟨fun j ↦ if j ≤ i.castSucc then 0 else 1, fun a b h ↦ by
    dsimp only
    split_ifs with h1 h2 h2
    · exact le_rfl
    · exact Fin.zero_le _
    · exact absurd (h.trans h2) h1
    · exact le_rfl⟩

def sg (q : ℕ) (i : Fin (q + 1)) : Fin (q + 2) →o Fin (q + 1) := Fin.predAboveOrderHom i

def cst (n : ℕ) {p : ℕ} (a : Fin (p + 1)) : Fin (n + 1) →o Fin (p + 1) := ⟨fun _ ↦ a, fun _ _ _ ↦ le_rfl⟩

def S (F : C ⥤ CommAlgCat.{0} R) (q : ℕ) : Cn (box F) (q + 1) →ₗ[R] Y F 1 q :=
  ∑ i : Fin (q + 1), ((-1 : R) ^ (i : ℕ)) • bi F (th q i) (sg q i)

def S0 (F : C ⥤ CommAlgCat.{0} R) (q : ℕ) : Cn (box F) q →ₗ[R] Y F 0 q := bi F (cst q 0) OrderHom.id

open Classical in

def sl (F : C ⥤ CommAlgCat.{0} R) {p : ℕ} [Fintype (Fin (p + 1) ⥤ C)] (q : ℕ) (Λ : Cn F p →ₗ[R] R) :
    Y F p q →ₗ[R] Cn F q where
  toFun y b := ∑ c : Fin (p + 1) ⥤ C,
    TensorProduct.lid R _ (LinearMap.rTensor _ (Λ ∘ₗ LinearMap.single R (fun c : Fin (p + 1) ⥤ C ↦
      (F.obj (c.obj (Fin.last p)) : Type)) c) (y c b))
  map_add' _ _ := by funext b; simp [Finset.sum_add_distrib]
  map_smul' _ _ := by funext b; simp [Finset.smul_sum]

def T (F : C ⥤ CommAlgCat.{0} R) [Fintype (Fin 2 ⥤ C)] (q : ℕ) (Λ : Cn F 1 →ₗ[R] R) :
    Cn (box F) (q + 1) →ₗ[R] Cn F q := sl F q Λ ∘ₗ S F q

def U (F : C ⥤ CommAlgCat.{0} R) [Fintype (Fin 1 ⥤ C)] (q : ℕ) (ν : Cn F 0 →ₗ[R] R) :
    Cn (box F) q →ₗ[R] Cn F q := sl F q ν ∘ₗ S0 F q

section Basic

variable {D : Type} [Category.{0} D] (F : C ⥤ CommAlgCat.{0} R) {G : D ⥤ CommAlgCat.{0} R}

theorem act_mul {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) (u v : Cn F m) :
    act F θ (u * v) = act F θ u * act F θ v := by
  funext c
  exact map_mul (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m)))))) _ _

theorem act_one {m n : ℕ} (θ : Fin (m + 1) →o Fin (n + 1)) : act F θ (1 : Cn F m) = 1 := by
  funext c
  exact map_one (mp F (c.map (homOfLE (Fin.le_last (θ (Fin.last m))))))

variable {F}

theorem pulln_act (m : CoefMap (RingHom.id R) F G) {k n : ℕ} (θ : Fin (k + 1) →o Fin (n + 1)) (f : Cn F k) :
    pulln m n (act F θ f) = act G θ (pulln m k f) := by
  funext c
  exact m.naturality (c.map (homOfLE (Fin.le_last (θ (Fin.last k))))) (f (θ.monotone.functor ⋙ c ⋙ m.G))

theorem pulln_mul (m : CoefMap (RingHom.id R) F G) (n : ℕ) (u v : Cn F n) :
    pulln m n (u * v) = pulln m n u * pulln m n v := by
  funext c
  exact map_mul (m.α (c.obj (Fin.last n))) _ _

theorem pullback_cup1 (m : CoefMap (RingHom.id R) F G) {n : ℕ} (y : Cn F 1) (z : Cn F n) :
    pulln m (n + 1) (cup1 F y z) = cup1 G (pulln m 1 y) (pulln m n z) := by
  rw [cup1, cup1, pulln_mul, pulln_act, pulln_act]

variable (F)

theorem cup1_add_left {n : ℕ} (y y' : Cn F 1) (z : Cn F n) :
    cup1 F (y + y') z = cup1 F y z + cup1 F y' z := by
  simp only [cup1, map_add, add_mul]

theorem cup1_add_right {n : ℕ} (y : Cn F 1) (z z' : Cn F n) :
    cup1 F y (z + z') = cup1 F y z + cup1 F y z' := by
  simp only [cup1, map_add, mul_add]

theorem cup1_zero {n : ℕ} (y : Cn F 1) : cup1 F y (0 : Cn F n) = 0 := by
  simp only [cup1, map_zero, mul_zero]

end Basic

section Bi

variable (F : C ⥤ CommAlgCat.{0} R)

def nu (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) : Cn F 0 →ₗ[R] R :=
  Λ ∘ₗ LinearMap.mulLeft R x ∘ₗ act F (cst 0 (1 : Fin 2))

def evz (T₀ : C) (ε : F.obj T₀ →ₐ[R] R) : Cn F 0 →ₗ[R] R :=
  ε.toLinearMap ∘ₗ LinearMap.proj (φ := fun c : Fin 1 ⥤ C ↦ (F.obj (c.obj (Fin.last 0)) : Type))
    (ComposableArrows.mk₀ T₀)

theorem nu_one (Λ : Cn F 1 →ₗ[R] R) (x : Cn F 1) : nu F Λ x 1 = Λ x := by
  simp [nu, act_one]

theorem mp_box_tmul {X X' : C × C} (φ : X ⟶ X') (a : F.obj X.1) (b : F.obj X.2) :
    mp (box F) φ (a ⊗ₜ[R] b) = mp F φ.1 a ⊗ₜ[R] mp F φ.2 b := rfl

def lh {A B : C} (f : A ⟶ B) (T : C) : ((A, T) : C × C) ⟶ (B, T) := (f, 𝟙 T)

def rh (T : C) {A B : C} (f : A ⟶ B) : ((T, A) : C × C) ⟶ (T, B) := (𝟙 T, f)

theorem map_left_eq {A B T : C} (f : A ⟶ B) (t : F.obj A ⊗[R] F.obj T) :
    TensorProduct.map (mp F f).toLinearMap LinearMap.id t =
      mp (box F) (lh f T) t := by
  induction t with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    exact (congrArg (fun y ↦ mp F f a ⊗ₜ[R] y) (mp_id F T b)).symm

theorem map_right_eq {A B T : C} (f : A ⟶ B) (t : F.obj T ⊗[R] F.obj A) :
    TensorProduct.map LinearMap.id (mp F f).toLinearMap t =
      mp (box F) (rh T f) t := by
  induction t with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul a b =>
    refine (TensorProduct.map_tmul _ _ _ _).trans ?_
    exact (congrArg (fun y ↦ y ⊗ₜ[R] mp F f b) (mp_id F T a)).symm

theorem bi_mul {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1))
    (u v : Cn (box F) n) : bi F θ ψ (u * v) = bi F θ ψ u * bi F θ ψ v := by
  funext c b
  exact map_mul (mp (box F) (pcLast θ ψ c b)) _ _

theorem bi_act {k n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1))
    (ρ : Fin (k + 1) →o Fin (n + 1)) (w : Cn (box F) k) :
    bi F θ ψ (act (box F) ρ w) = bi F (θ.comp ρ) (ψ.comp ρ) w := by
  funext c b
  have e : (pc θ ψ c b).map (homOfLE (Fin.le_last (ρ (Fin.last k)))) ≫ pcLast θ ψ c b =
      pcLast (θ.comp ρ) (ψ.comp ρ) c b := by
    refine Prod.ext ?_ ?_
    · change c.map _ ≫ c.map _ = c.map _
      rw [← c.map_comp]
      exact congrArg c.map (Subsingleton.elim _ _)
    · change b.map _ ≫ b.map _ = b.map _
      rw [← b.map_comp]
      exact congrArg b.map (Subsingleton.elim _ _)
  let x : (box F).obj ((pc θ ψ c b).obj (ρ (Fin.last k))) := w (pc (θ.comp ρ) (ψ.comp ρ) c b)
  exact ((congrArg (fun g ↦ mp (box F) g x) e).symm.trans (mp_comp (box F) _ _ x)).symm

theorem bisimplicial_action_first_factor {n p p' q : ℕ} (θ : Fin (p + 1) →o Fin (p' + 1)) (ζ : Fin (n + 1) →o Fin (p + 1))
    (ψ : Fin (n + 1) →o Fin (q + 1)) (w : Cn (box F) n) :
    a1 F θ (bi F ζ ψ w) = bi F (θ.comp ζ) ψ w := by
  funext c b
  let x : (box F).obj ((pc (θ.comp ζ) ψ c b).obj (Fin.last n)) := w (pc (θ.comp ζ) ψ c b)
  have e : pcLast ζ ψ (θ.monotone.functor ⋙ c) b ≫
      lh (c.map (homOfLE (Fin.le_last (θ (Fin.last p))))) (b.obj (Fin.last q)) =
      pcLast (θ.comp ζ) ψ c b := by
    refine Prod.ext ?_ ?_
    · exact (c.map_comp _ _).symm.trans (congrArg c.map (Subsingleton.elim _ _))
    · exact Category.comp_id _
  refine (map_left_eq F _ _).trans ?_
  exact ((congrArg (fun g ↦ mp (box F) g x) e).symm.trans (mp_comp (box F) _ _ x)).symm

theorem bisimplicial_action_second_factor {n p q q' : ℕ} (ψ' : Fin (q + 1) →o Fin (q' + 1)) (ζ : Fin (n + 1) →o Fin (p + 1))
    (ψ : Fin (n + 1) →o Fin (q + 1)) (w : Cn (box F) n) :
    a2 F ψ' (bi F ζ ψ w) = bi F ζ (ψ'.comp ψ) w := by
  funext c b
  let x : (box F).obj ((pc ζ (ψ'.comp ψ) c b).obj (Fin.last n)) := w (pc ζ (ψ'.comp ψ) c b)
  have e : pcLast ζ ψ c (ψ'.monotone.functor ⋙ b) ≫
      rh (c.obj (Fin.last p)) (b.map (homOfLE (Fin.le_last (ψ' (Fin.last q))))) =
      pcLast ζ (ψ'.comp ψ) c b := by
    refine Prod.ext ?_ ?_
    · exact Category.comp_id _
    · exact (b.map_comp _ _).symm.trans (congrArg b.map (Subsingleton.elim _ _))
  refine (map_right_eq F _ _).trans ?_
  exact ((congrArg (fun g ↦ mp (box F) g x) e).symm.trans (mp_comp (box F) _ _ x)).symm

theorem bi_boxL {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1)) (x : Cn F n)
    (c : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) :
    bi F θ ψ (pulln (boxL F) n x) c b = act F θ x c ⊗ₜ[R] 1 := by
  refine (mp_box_tmul F _ _ _).trans ?_
  exact congrArg (fun y ↦ act F θ x c ⊗ₜ[R] y) (map_one (mp F _))

theorem bi_boxR {n p q : ℕ} (θ : Fin (n + 1) →o Fin (p + 1)) (ψ : Fin (n + 1) →o Fin (q + 1)) (x : Cn F n)
    (c : Fin (p + 1) ⥤ C) (b : Fin (q + 1) ⥤ C) :
    bi F θ ψ (pulln (boxR F) n x) c b = 1 ⊗ₜ[R] act F ψ x b := by
  refine (mp_box_tmul F _ _ _).trans ?_
  exact congrArg (fun y ↦ y ⊗ₜ[R] act F ψ x b) (map_one (mp F _))

theorem act_const {p : ℕ} (x : Cn F 1) (hx : dn F 1 x = 0) (θ : Fin 2 →o Fin (p + 1)) (h : θ 0 = θ 1) :
    act F θ x = 0 := by
  have e0 : θ = (⟨fun _ ↦ θ 0, fun _ _ _ ↦ le_rfl⟩ : Fin 1 →o Fin (p + 1)).comp (cst 1 (0 : Fin 1)) := by
    ext i
    fin_cases i
    · rfl
    · exact congrArg _ h.symm
  have h3 : act F (cst 1 (0 : Fin 1)) x = 0 := by
    have c : ∀ i : Fin 3, (cst 2 (0 : Fin 1)).comp (Fin.succAboveOrderEmb i).toOrderHom = cst 1 (0 : Fin 1) :=
      fun i ↦ by ext j; simp [cst]
    have key : act F (cst 2 (0 : Fin 1)) (dn F 1 x) = act F (cst 1 (0 : Fin 1)) x := by
      simp only [dn, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, cof_eq]
      simp only [← act_comp, c]
      simp [Fin.sum_univ_succ]
    rw [← key, hx, map_zero]
  rw [e0, act_comp, h3, map_zero]

end Bi

end GlobalTheory.CompanionTheory.HopfLe
