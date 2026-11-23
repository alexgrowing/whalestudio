import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.LemmaKOfSteps
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SChain
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SPrism

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK
open scoped LinearAlgebra.Projectivization

noncomputable section

namespace UpperTheory.V.ZK.Trans

section Abstract

variable (A : Type) [CommRing A] {G H X Y M : Type} [Group G] [Group H] [CommGroup M]

private def term (a : G → X → X) (c : G → X → M) (x : X) {m : ℕ} (g : Fin m → G) : Fin m → M :=
  fun i => c (g i) (a (Fin.partialProd g i.castSucc) x)

private def tr [Fintype X] (a : G → X → X) (c : G → X → M) (m : ℕ) : Ch A G m →ₗ[A] Ch A M m :=
  Finsupp.linearCombination A fun g => ∑ x, Finsupp.single (term a c x g) 1

private structure IsCoc (a : G → X → X) (c : G → X → M) : Prop where
  a_one : ∀ x, a 1 x = x
  a_mul : ∀ g h x, a (g * h) x = a h (a g x)
  c_mul : ∀ g h x, c (g * h) x = c g x * c h (a g x)

variable {A}

private theorem tr_single [Fintype X] (a : G → X → X) (c : G → X → M) {m : ℕ} (g : Fin m → G) :
    tr A a c m (Finsupp.single g 1) = ∑ x, Finsupp.single (term a c x g) 1 := by
  simp [tr]

private theorem IsCoc.c_one {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (x : X) : c 1 x = 1 := by
  have := h.c_mul 1 1 x
  rw [one_mul, h.a_one] at this
  exact (mul_eq_left.1 this.symm)

private theorem IsCoc.term_eq {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (x : X) {m : ℕ} (g : Fin m → G)
    (i : Fin m) : term a c x g i = (c (Fin.partialProd g i.castSucc) x)⁻¹ * c (Fin.partialProd g i.succ) x := by
  rw [Fin.partialProd_succ, h.c_mul, inv_mul_cancel_left]; rfl

private theorem IsCoc.pp {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (x : X) {m : ℕ} (g : Fin m → G)
    (i : Fin (m + 1)) : Fin.partialProd (term a c x g) i = c (Fin.partialProd g i) x := by
  induction i using Fin.induction with
  | zero => simp [h.c_one]
  | succ i ih => rw [Fin.partialProd_succ, ih, h.term_eq, mul_inv_cancel_left]

private theorem IsCoc.contract {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (x : X) {m : ℕ}
    (g : Fin (m + 1) → G) (j : Fin (m + 1)) :
    term a c x (Fin.contractNth j (· * ·) g) = Fin.contractNth j (· * ·) (term a c x g) := by
  funext i
  rw [← Fin.inv_partialProd_mul_eq_contractNth, h.pp, h.pp, h.term_eq, Fin.partialProd_contractNth]
  simp only [Function.comp_apply, Fin.succ_succAbove_succ]

private theorem IsCoc.tail {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (x : X) {m : ℕ}
    (g : Fin (m + 1) → G) :
    (fun i : Fin m => term a c x g i.succ) = term a c (a (g 0) x) (fun i => g i.succ) := by
  funext i
  simp only [term]
  rw [← Fin.succ_castSucc, Fin.partialProd_succ', h.a_mul]
  rfl

private def IsCoc.perm {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (g : G) : X ≃ X where
  toFun := a g
  invFun := a g⁻¹
  left_inv x := by rw [← h.a_mul, mul_inv_cancel, h.a_one]
  right_inv x := by rw [← h.a_mul, inv_mul_cancel, h.a_one]

private theorem bd_single {m : ℕ} (g : Fin (m + 1) → G) : bd A G m (Finsupp.single g 1) =
    Finsupp.single (fun i => g i.succ) 1 +
      ∑ j : Fin (m + 1), ((-1 : A) ^ ((j : ℕ) + 1)) • Finsupp.single (Fin.contractNth j (· * ·) g) 1 := by
  simp only [bd, Finsupp.linearCombination_single, one_smul]

private theorem cm_single (f : G →* H) {m : ℕ} (g : Fin m → G) :
    cm A f m (Finsupp.single g 1) = Finsupp.single (fun i => f (g i)) 1 := by
  simp [cm]

private theorem ext1 {B : Type} [AddCommGroup B] [Module A B] {m : ℕ} {f f' : Ch A G m →ₗ[A] B}
    (h : ∀ g, f (Finsupp.single g 1) = f' (Finsupp.single g 1)) : f = f' :=
  Finsupp.lhom_ext' fun g => LinearMap.ext_ring (h g)

private theorem IsCoc.tr_bd [Fintype X] {a : G → X → X} {c : G → X → M} (h : IsCoc a c) (m : ℕ)
    (z : Ch A G (m + 1)) : bd A M m (tr A a c (m + 1) z) = tr A a c m (bd A G m z) := by
  refine LinearMap.congr_fun (ext1 (f := (bd A M m).comp (tr A a c (m + 1)))
    (f' := (tr A a c m).comp (bd A G m)) fun g => ?_) z
  simp only [LinearMap.comp_apply, tr_single, bd_single, map_sum, map_add, map_smul, Finset.sum_add_distrib,
    Finset.smul_sum, h.contract, h.tail]
  congr 1
  · exact Equiv.sum_comp (h.perm (g 0)) fun x => Finsupp.single (term a c x fun i => g i.succ) (1 : A)
  · exact Finset.sum_comm

private theorem IsCoc.tr_Bd [Fintype X] {a : G → X → X} {c : G → X → M} (h : IsCoc a c) {m : ℕ}
    {z : Ch A G m} (hz : Bd z) : Bd (tr A a c m z) := by
  obtain ⟨y, rfl⟩ := hz
  exact ⟨_, h.tr_bd m y⟩

private theorem pp_map (f : G →* H) {m : ℕ} (g : Fin m → G) (j : Fin (m + 1)) :
    Fin.partialProd (fun i => f (g i)) j = f (Fin.partialProd g j) := by
  induction j using Fin.induction with
  | zero => simp
  | succ i ih => rw [Fin.partialProd_succ, Fin.partialProd_succ, ih, map_mul]

private theorem tr_pull [Fintype X] [Fintype Y] (f : G →* H) (p : X → Y) {a : G → X → X} {c : G → X → M}
    {a' : H → Y → Y} {c' : H → Y → M} (ha : ∀ g x, p (a g x) = a' (f g) (p x))
    (hc : ∀ g x, c g x = c' (f g) (p x)) (hp : ∀ y, (Nat.card {x // p x = y} : A) = 1) (m : ℕ) (z : Ch A G m) :
    tr A a c m z = tr A a' c' m (cm A f m z) := by
  classical
  refine LinearMap.congr_fun (ext1 (f := tr A a c m) (f' := (tr A a' c' m).comp (cm A f m)) fun g => ?_) z
  simp only [LinearMap.comp_apply, tr_single, cm_single]
  have h1 : ∀ x, term a c x g = term a' c' (p x) fun i => f (g i) := fun x => by
    funext i
    simp only [term, pp_map, hc, ha]
  simp only [h1]
  rw [← Finset.sum_fiberwise Finset.univ p]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => Finsupp.single (term a' c' y fun i => f (g i)) (1 : A))
    fun x hx => by rw [(Finset.mem_filter.1 hx).2], Finset.sum_const, ← Nat.cast_smul_eq_nsmul A,
    ← Fintype.card_subtype, ← Nat.card_eq_fintype_card, hp, one_smul]

private theorem tr_sum [Fintype X] [Fintype Y] (a : G → X → X) (c : G → X → M) (a' : G → Y → Y) (c' : G → Y → M)
    (m : ℕ) (z : Ch A G m) :
    tr A (fun g => Sum.map (a g) (a' g)) (fun g => Sum.elim (c g) (c' g)) m z = tr A a c m z + tr A a' c' m z := by
  refine LinearMap.congr_fun (ext1 (f := tr A (fun g => Sum.map (a g) (a' g)) (fun g => Sum.elim (c g) (c' g)) m)
    (f' := tr A a c m + tr A a' c' m) fun g => ?_) z
  simp only [LinearMap.add_apply, tr_single, Fintype.sum_sum_type]
  rfl

private theorem card_id (y : X) : (Nat.card {x // id x = y} : A) = 1 := by simp

private theorem tr_cob [Fintype X] {a : G → X → X} {c c' : G → X → M} (h : IsCoc a c) (h' : IsCoc a c') (b : X → M)
    (hb : ∀ g x, c' g x = (b x)⁻¹ * c g x * b (a g x)) {m : ℕ} {z : Ch A G (m + 1)} (hz : Cyc z) :
    Bd (tr A a c' (m + 1) z - tr A a c (m + 1) z) := by
  letI : MulAction G X :=
    { smul := fun g x => a g⁻¹ x
      one_smul := fun x => show a 1⁻¹ x = x by rw [inv_one, h.a_one]
      mul_smul := fun g g' x => show a (g * g')⁻¹ x = a g⁻¹ (a g'⁻¹ x) by rw [mul_inv_rev, h.a_mul] }
  have hs : ∀ (g : G) (n : X → M) (x : X), (mulAutArrow g n) x = n (a g x) := fun g n x =>
    show n (a g⁻¹⁻¹ x) = _ by rw [inv_inv]
  let W := (X → M) ⋊[mulAutArrow] G
  let aW : W → X → X := fun w => a w.right
  let cW : W → X → M := fun w => w.left
  have hW : IsCoc aW cW := ⟨h.a_one, fun g g' x => h.a_mul _ _ x, fun g g' x => by
    simp only [cW, aW, W, SemidirectProduct.mul_left, Pi.mul_apply, hs]⟩
  let ρ : ∀ {d : G → X → M}, IsCoc a d → (G →* W) := fun {d} hd => MonoidHom.mk' (fun g => ⟨d g, g⟩) fun g g' => by
    refine SemidirectProduct.ext (funext fun x => ?_) rfl
    simp only [W, SemidirectProduct.mul_left, Pi.mul_apply, hs, hd.c_mul]
  have e : ∀ {d : G → X → M} (hd : IsCoc a d), tr A a d (m + 1) z = tr A aW cW (m + 1) (cm A (ρ hd) (m + 1) z) :=
    fun {d} hd => tr_pull (ρ hd) id (a := a) (c := d) (a' := aW) (c' := cW) (fun _ _ => rfl) (fun _ _ => rfl) card_id _ _
  let β : W := SemidirectProduct.inl b
  have e2 : ρ h' = (MulAut.conj β⁻¹).toMonoidHom.comp (ρ h) := by
    ext g : 1
    show (⟨c' g, g⟩ : W) = β⁻¹ * ⟨c g, g⟩ * β⁻¹⁻¹
    refine SemidirectProduct.ext (funext fun x => ?_) (by simp [β, W])
    simp [β, W, hs, hb, h.a_one]
  obtain ⟨-, s2, s3, -, -⟩ := sChain A
  rw [e h, e h', ← map_sub, e2, s3]
  refine hW.tr_Bd ⟨prism A β (m + 1) (cm A (ρ h) (m + 1) z), ?_⟩
  rw [← sPrism A W β m, s2, show bd A G m z = 0 from hz, map_zero, map_zero, add_zero]

end Abstract

section Lines

variable {k : Type} [Field k] {V W : Type} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
  {G : Type} [Group G] {A : Type} [CommRing A]

private def Homog (l : V → kˣ) : Prop := ∀ (u : kˣ) (v : V), v ≠ 0 → l (u • v) = u * l v

private theorem exists_homog (k V : Type) [Field k] [AddCommGroup V] [Module k V] : ∃ l : V → kˣ, Homog l := by
  classical
  have h : ∀ (v : V) (hv : v ≠ 0), ∃ u : kˣ, u • (Projectivization.mk k v hv).rep = v := fun v hv => by
    obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
    exact ⟨u⁻¹, by rw [← hu, inv_smul_smul]⟩
  choose l hl using h
  refine ⟨fun v => if hv : v = 0 then 1 else l v hv, fun u v hv => ?_⟩
  have huv : u • v ≠ 0 := (smul_ne_zero_iff_ne u).2 hv
  simp only [dif_neg hv, dif_neg huv]
  have e : Projectivization.mk k (u • v) huv = Projectivization.mk k v hv :=
    (Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨u, rfl⟩
  have h1 := hl _ huv
  rw [e] at h1
  have h2 : (u * l v hv) • (Projectivization.mk k v hv).rep = u • v := by rw [mul_smul, hl]
  apply Units.ext
  exact smul_left_injective k (Projectivization.rep_nonzero _) (h1.trans h2.symm)

private def lam (k V : Type) [Field k] [AddCommGroup V] [Module k V] : V → kˣ := (exists_homog k V).choose

private theorem lam_homog : Homog (lam k V) := (exists_homog k V).choose_spec

private def la (ρ : G →* (V ≃ₗ[k] V)) (g : G) (x : ℙ k V) : ℙ k V := (ρ g)⁻¹ • x

private def lc (ρ : G →* (V ≃ₗ[k] V)) (l : V → kˣ) (g : G) (x : ℙ k V) : kˣ := l x.rep / l ((ρ g)⁻¹ x.rep)

private theorem ne0 (e : V ≃ₗ[k] W) {v : V} (hv : v ≠ 0) : e v ≠ 0 := by simpa using hv

private theorem la_mk (ρ : G →* (V ≃ₗ[k] V)) (g : G) {v : V} (hv : v ≠ 0) :
    la ρ g (Projectivization.mk k v hv) = Projectivization.mk k ((ρ g)⁻¹ v) (ne0 _ hv) := rfl

private theorem quot_mk {l : V → kˣ} (hl : Homog l) {l' : W → kˣ} (hl' : Homog l') (e : V ≃ₗ[k] W) {v : V}
    (hv : v ≠ 0) : l (Projectivization.mk k v hv).rep / l' (e (Projectivization.mk k v hv).rep) = l v / l' (e v) := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← hu, show e (u • v) = u • e v by simp [Units.smul_def], hl _ _ hv, hl' _ _ (ne0 e hv), mul_div_mul_left_eq_div]

private theorem lc_mk (ρ : G →* (V ≃ₗ[k] V)) {l : V → kˣ} (hl : Homog l) (g : G) {v : V} (hv : v ≠ 0) :
    lc ρ l g (Projectivization.mk k v hv) = l v / l ((ρ g)⁻¹ v) := quot_mk hl hl _ hv

private theorem isCoc (ρ : G →* (V ≃ₗ[k] V)) {l : V → kˣ} (hl : Homog l) : IsCoc (la ρ) (lc ρ l) where
  a_one x := by simp [la]
  a_mul g h x := by simp only [la, map_mul, mul_inv_rev, mul_smul]
  c_mul g h x := by
    induction x using Projectivization.ind with
    | h v hv =>
      rw [la_mk, lc_mk ρ hl, lc_mk ρ hl, lc_mk ρ hl, map_mul, mul_inv_rev, LinearEquiv.mul_apply, div_mul_div_cancel]

private theorem indep [Fintype (ℙ k V)] (ρ : G →* (V ≃ₗ[k] V)) {l l' : V → kˣ} (hl : Homog l) (hl' : Homog l')
    {m : ℕ} {z : Ch A G (m + 1)} (hz : Cyc z) :
    Bd (tr A (la ρ) (lc ρ l') (m + 1) z - tr A (la ρ) (lc ρ l) (m + 1) z) := by
  refine tr_cob (isCoc ρ hl) (isCoc ρ hl') (fun x => l x.rep / l' (LinearEquiv.refl k V x.rep)) (fun g x => ?_) hz
  induction x using Projectivization.ind with
  | h v hv =>
    rw [la_mk, lc_mk ρ hl, lc_mk ρ hl', quot_mk hl hl', quot_mk hl hl']
    simp only [LinearEquiv.refl_apply, inv_div, div_mul_div_cancel]

private instance fin [Finite V] : Fintype (ℙ k V) :=
  @Fintype.ofFinite _ (Finite.of_injective _ fun x y (h : x.rep = y.rep) => by
    rw [← x.mk_rep, ← y.mk_rep]; congr 1)

private def theta (k : Type) [Field k] {m : ℕ} (t : Ch A kˣ m →ₗ[A] A) : Fam k A m := fun V _ _ _ =>
  t.comp (tr A (la (MonoidHom.id _)) (lc (MonoidHom.id _) (lam k V)) m)

private theorem theta_cm [Finite V] {m : ℕ} {t : Ch A kˣ (m + 1) →ₗ[A] A} (ht : ∀ z, Bd z → t z = 0)
    (ρ : G →* (V ≃ₗ[k] V)) {l : V → kˣ} (hl : Homog l) {z : Ch A G (m + 1)} (hz : Cyc z) :
    theta k t V (cm A ρ (m + 1) z) = t (tr A (la ρ) (lc ρ l) (m + 1) z) := by
  have h := ht _ (indep ρ hl lam_homog hz)
  rw [map_sub, sub_eq_zero] at h
  rw [← h, tr_pull ρ id (a := la ρ) (c := lc ρ (lam k V)) (a' := la (MonoidHom.id _)) (c' := lc (MonoidHom.id _) (lam k V))
    (fun _ _ => rfl) (fun _ _ => rfl) card_id]
  rfl

private theorem cm_id {m : ℕ} (z : Ch A G m) : cm A (MonoidHom.id G) m z = z :=
  LinearMap.congr_fun (ext1 (f := cm A (MonoidHom.id G) m) (f' := LinearMap.id) fun g => by
    rw [cm_single]; rfl) z

private theorem theta_iso [Finite V] [Finite W] {m : ℕ} {t : Ch A kˣ (m + 1) →ₗ[A] A} (ht : ∀ z, Bd z → t z = 0)
    (φ : V ≃ₗ[k] W) {z : Ch A (V ≃ₗ[k] V) (m + 1)} (hz : Cyc z) :
    theta k t W (cm A (cj φ) (m + 1) z) = theta k t V z := by
  have hl : Homog fun w : W => lam k V (φ.symm w) := fun u w hw => by
    simp only [show φ.symm (u • w) = u • φ.symm w by simp [Units.smul_def]]
    exact lam_homog _ _ (ne0 _ hw)
  rw [theta_cm ht _ hl hz, tr_pull (MonoidHom.id _) (Projectivization.map φ.symm.toLinearMap φ.symm.injective)
    (a' := la (MonoidHom.id _)) (c' := lc (MonoidHom.id _) (lam k V)), cm_id]
  · rfl
  · intro g x
    induction x using Projectivization.ind with
    | h v hv =>
      simp only [la_mk, Projectivization.map_mk]
      congr 1
      exact φ.symm_apply_apply _
  · intro g x
    induction x using Projectivization.ind with
    | h v hv =>
      rw [Projectivization.map_mk, lc_mk _ hl, lc_mk _ lam_homog]
      congr 2
      exact φ.symm_apply_apply _
  · intro y
    rw [Nat.card_eq_one_iff_exists.2, Nat.cast_one]
    refine ⟨⟨Projectivization.map φ.toLinearMap φ.injective y, ?_⟩, fun x => Subtype.ext ?_⟩
    · induction y using Projectivization.ind with
      | h v hv => simp [Projectivization.map_mk]
    · obtain ⟨x, rfl⟩ := x
      induction x using Projectivization.ind with
      | h v hv => simp [Projectivization.map_mk]

private theorem theta_one [Finite k] {m : ℕ} {t : Ch A kˣ (m + 1) →ₗ[A] A} (ht : ∀ z, Bd z → t z = 0)
    {z : Ch A kˣ (m + 1)} (hz : Cyc z) : theta k t k (cm A (scal k) (m + 1) z) = t z := by
  classical
  have hl : Homog fun v : k => if hv : v = 0 then (1 : kˣ) else Units.mk0 v hv := fun u v hv => by
    have huv : u • v ≠ 0 := (smul_ne_zero_iff_ne u).2 hv
    simp only [dif_neg hv, dif_neg huv]
    ext; simp [Units.smul_def]
  rw [theta_cm ht _ hl hz, tr_pull (MonoidHom.id _) (fun _ => ()) (a := la (scal k)) (a' := fun _ _ => ()) (c' := fun g _ => g)
    (fun _ _ => rfl), cm_id]
  · congr 1
    refine LinearMap.congr_fun (ext1 (f := tr A (fun (_ : kˣ) (_ : Unit) => ()) (fun g _ => g) (m + 1))
      (f' := LinearMap.id) fun g => ?_) z
    rw [tr_single, Fintype.sum_unique]; rfl
  · intro g x
    induction x using Projectivization.ind with
    | h v hv =>
      rw [lc_mk _ hl, ← map_inv, show scal k g⁻¹ v = g⁻¹ • v from rfl]
      have e := hl g⁻¹ v hv
      simp only at e
      rw [e, div_mul_cancel_right, inv_inv]
      rfl
  · intro y
    rw [Nat.card_eq_one_iff_exists.2, Nat.cast_one]
    refine ⟨⟨Projectivization.mk k 1 one_ne_zero, rfl⟩, fun x => Subtype.ext ?_⟩
    obtain ⟨x, -⟩ := x
    induction x using Projectivization.ind with
    | h v hv => exact (Projectivization.mk_eq_mk_iff' k _ _ _ _).2 ⟨v, by simp⟩

open Classical in
private def pr0 (v : V × W) (hv : v ≠ 0) : ℙ k V ⊕ ℙ k W :=
  if h : v.1 = 0 then Sum.inr (Projectivization.mk k v.2 fun h2 => hv (Prod.ext h h2))
  else Sum.inl (Projectivization.mk k v.1 h)

private theorem projection_smul_invariant (u : kˣ) (v : V × W) (hv : v ≠ 0) (huv : u • v ≠ 0) :
    pr0 (k := k) (u • v) huv = pr0 v hv := by
  unfold pr0
  by_cases h : v.1 = 0
  · rw [dif_pos h, dif_pos (by simp [h])]
    exact congrArg _ ((Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨u, rfl⟩)
  · rw [dif_neg h, dif_neg (show ¬(u • v).1 = 0 from (smul_ne_zero_iff_ne u).2 h)]
    exact congrArg _ ((Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨u, rfl⟩)

private def pr (x : ℙ k (V × W)) : ℙ k V ⊕ ℙ k W := pr0 x.rep x.rep_nonzero

private theorem pr_mk (v : V × W) (hv : v ≠ 0) : pr (Projectivization.mk k v hv) = pr0 v hv := by
  obtain ⟨u, hu⟩ := Projectivization.exists_smul_eq_mk_rep k v hv
  rw [← projection_smul_invariant u v hv ((smul_ne_zero_iff_ne u).2 hv), pr]
  congr 1
  exact hu.symm

private theorem pr_inl {v : V × W} (hv : v ≠ 0) (h : v.1 ≠ 0) :
    pr (Projectivization.mk k v hv) = Sum.inl (Projectivization.mk k v.1 h) := by rw [pr_mk, pr0, dif_neg h]

private theorem pr_inr {v : V × W} (hv : v ≠ 0) (h : v.1 = 0) (h2 : v.2 ≠ 0) :
    pr (Projectivization.mk k v hv) = Sum.inr (Projectivization.mk k v.2 h2) := by rw [pr_mk, pr0, dif_pos h]

private theorem card_inl (v : V) (hv : v ≠ 0) :
    Nat.card {x : ℙ k (V × W) // pr x = Sum.inl (Projectivization.mk k v hv)} = Nat.card W := by
  have h0 : ∀ w : W, (v, w) ≠ 0 := fun w h => hv (congrArg Prod.fst h)
  refine (Nat.card_eq_of_bijective (fun w => ⟨Projectivization.mk k (v, w) (h0 w), pr_inl _ hv⟩) ⟨?_, ?_⟩).symm
  · intro w w' h
    obtain ⟨a, ha⟩ := (Projectivization.mk_eq_mk_iff' k _ _ _ _).1 (congrArg Subtype.val h)
    obtain ⟨h1, h2⟩ := Prod.ext_iff.1 ha
    have : a = 1 := smul_left_injective k hv (h1.trans (one_smul k v).symm)
    simpa [this] using h2.symm
  · rintro ⟨x, hx⟩
    induction x using Projectivization.ind with
    | h y hy =>
      by_cases h : y.1 = 0
      · rw [pr_inr hy h fun h2 => hy (Prod.ext h h2)] at hx
        cases hx
      · rw [pr_inl hy h] at hx
        obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff k _ _ _ _).1 (Sum.inl_injective hx).symm
        exact ⟨u • y.2, Subtype.ext ((Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨u, Prod.ext hu rfl⟩)⟩

private theorem card_inr (w : W) (hw : w ≠ 0) :
    Nat.card {x : ℙ k (V × W) // pr x = Sum.inr (Projectivization.mk k w hw)} = 1 := by
  have h0 : ((0 : V), w) ≠ 0 := fun h => hw (congrArg Prod.snd h)
  refine Nat.card_eq_one_iff_exists.2 ⟨⟨Projectivization.mk k (0, w) h0, pr_inr _ rfl hw⟩, ?_⟩
  rintro ⟨x, hx⟩
  induction x using Projectivization.ind with
  | h y hy =>
    by_cases h : y.1 = 0
    · rw [pr_inr hy h fun h2 => hy (Prod.ext h h2)] at hx
      obtain ⟨u, hu⟩ := (Projectivization.mk_eq_mk_iff k _ _ _ _).1 (Sum.inr_injective hx)
      exact Subtype.ext ((Projectivization.mk_eq_mk_iff k _ _ _ _).2 ⟨u, Prod.ext (by simp [h]) hu⟩)
    · rw [pr_inl hy h] at hx
      cases hx

private theorem theta_add [Finite k] [Finite V] [Finite W] (hk : (Nat.card k : A) = 1) {m : ℕ}
    {t : Ch A kˣ (m + 1) →ₗ[A] A} (ht : ∀ z, Bd z → t z = 0)
    (ρ : G →* (V ≃ₗ[k] V)) (σ : G →* (W ≃ₗ[k] W)) {z : Ch A G (m + 1)} (hz : Cyc z) :
    theta k t (V × W) (cm A (sumRep ρ σ) (m + 1) z) =
      theta k t V (cm A ρ (m + 1) z) + theta k t W (cm A σ (m + 1) z) := by
  classical
  have hl : Homog fun y : V × W => if y.1 = 0 then lam k W y.2 else lam k V y.1 := fun u y hy => by
    by_cases h : y.1 = 0
    · simp only [if_pos h, if_pos (show (u • y).1 = 0 by simp [h])]
      exact lam_homog _ _ fun h2 => hy (Prod.ext h h2)
    · simp only [if_neg h, if_neg (show ¬(u • y).1 = 0 from (smul_ne_zero_iff_ne u).2 h)]
      exact lam_homog _ _ h
  have hs : ∀ g (y : V × W), (sumRep ρ σ g)⁻¹ y = ((ρ g)⁻¹ y.1, (σ g)⁻¹ y.2) := fun g y => rfl
  rw [theta_cm ht _ hl hz, theta_cm ht _ lam_homog hz, theta_cm ht _ lam_homog hz, ← map_add, ← tr_sum,
    tr_pull (MonoidHom.id _) pr (a' := fun g => Sum.map (la ρ g) (la σ g))
      (c' := fun g => Sum.elim (lc ρ (lam k V) g) (lc σ (lam k W) g)), cm_id]
  · intro g x
    induction x using Projectivization.ind with
    | h y hy =>
      by_cases h : y.1 = 0
      · have h2 : y.2 ≠ 0 := fun h2 => hy (Prod.ext h h2)
        rw [la_mk, pr_inr hy h h2, pr_inr _ (by simp [hs, h]) (ne0 (σ g)⁻¹ h2)]
        rfl
      · rw [la_mk, pr_inl hy h, pr_inl _ (ne0 (ρ g)⁻¹ h)]
        rfl
  · intro g x
    induction x using Projectivization.ind with
    | h y hy =>
      by_cases h : y.1 = 0
      · have h2 : y.2 ≠ 0 := fun h2 => hy (Prod.ext h h2)
        rw [lc_mk _ hl, pr_inr hy h h2, Sum.elim_inr, lc_mk _ lam_homog, hs]
        simp [h]
      · rw [lc_mk _ hl, pr_inl hy h, Sum.elim_inl, lc_mk _ lam_homog, hs]
        simp [h]
  · rintro (y | y)
    · induction y using Projectivization.ind with
      | h v hv => rw [card_inl, Module.natCard_eq_pow_finrank (K := k), Nat.cast_pow, hk, one_pow]
    · induction y using Projectivization.ind with
      | h v hv => rw [card_inr, Nat.cast_one]

private theorem main : STrans := fun k _ _ A _ hk m t ht =>
  ⟨theta k t, ⟨fun V _ _ _ z hz => ht _ ((isCoc _ lam_homog).tr_Bd hz), fun V W _ _ _ _ _ _ φ z hz => theta_iso ht φ hz,
    fun G V W _ _ _ _ _ _ _ ρ σ z hz => theta_add hk ht ρ σ hz⟩, fun z hz => theta_one ht hz⟩

end Lines

end UpperTheory.V.ZK.Trans

theorem UpperTheory.V.ZK.sTrans :
    UpperTheory.V.ZK.STrans :=
  UpperTheory.V.ZK.Trans.main

end
