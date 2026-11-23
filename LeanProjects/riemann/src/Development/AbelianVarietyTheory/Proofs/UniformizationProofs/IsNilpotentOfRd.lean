import Mathlib

set_option autoImplicit false

noncomputable section

open AddMonoidAlgebra

namespace GlobalTheory.CubeLift

variable {A : Type} [CommRing A] {X Y W : Type} [AddCommGroup X] [AddCommGroup Y] [AddCommGroup W]

abbrev mv (f : X →+ Y) : A[X] →+* A[Y] := mapDomainRingHom A f

theorem mv_single (f : X →+ Y) (a : X) (r : A) : mv f (single a r) = single (f a) r := by
  simp [mv]

theorem mv_mv (g : Y →+ W) (f : X →+ Y) (u : A[X]) : mv g (mv f u) = mv (g.comp f) u := by
  simp [mv, mapDomainRingHom_comp]

theorem mv_id (u : A[X]) : mv (AddMonoidHom.id X) u = u := by
  simp [mv, mapDomainRingHom_id]

def avg : A[X × Y] →+ A[Y] :=
  comapDomainAddMonoidHom (fun y : Y => ((0 : X), y)) fun _ _ h => congrArg Prod.snd h

theorem coeff_avg (u : A[X × Y]) (y : Y) : (avg u).coeff y = u.coeff (0, y) := rfl

open Classical in
theorem avg_single (p : X × Y) (r : A) : avg (single p r) = if p.1 = 0 then single p.2 r else 0 := by
  obtain ⟨a, b⟩ := p
  ext y
  rw [coeff_avg]
  by_cases h : a = 0 <;> simp [h, Finsupp.single_apply]

theorem avg_mv_fst (f : X × W →+ X × Y) (φ : W →+ Y) (h₁ : ∀ p, (f p).1 = p.1) (h₂ : ∀ w, (f (0, w)).2 = φ w)
    (u : A[X × W]) : avg (mv f u) = mv φ (avg u) := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single p r =>
    obtain ⟨a, b⟩ := p
    rw [mv_single, avg_single, avg_single, h₁]
    split_ifs with h
    · obtain rfl : a = 0 := h
      rw [h₂, mv_single]
    · simp

theorem avg_mv_inr (f : W →+ X × Y) (φ : W →+ Y) (h : ∀ w, f w = (0, φ w)) (u : A[W]) :
    avg (mv f u) = mv φ u := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | single p r => rw [mv_single, avg_single, h, mv_single, if_pos rfl]

theorem avg_mv_one (f : X →+ X × Y) (h : ∀ a, (f a).1 = a) (u : A[X]) :
    avg (mv f u) = single 0 (u.coeff 0) := by
  induction u using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb, coeff_add, Finsupp.add_apply, single_add]
  | single p r =>
    rw [mv_single, avg_single, h]
    split_ifs with hp
    · subst hp; simp
    · simp [hp]

abbrev tri (a b c : X →+ Y) : X × X × X →+ Y := a.coprod (b.coprod c)

theorem eq_of_cocycle (u : A[X × X × W]) (a b : X →+ Y) (w : W →+ Y)
    (h : ∀ (a b c : X →+ X × Y) (w : W →+ X × Y), mv ((a + b).coprod (c.coprod w)) u + mv (a.coprod (b.coprod w)) u =
      mv (a.coprod ((b + c).coprod w)) u + mv (b.coprod (c.coprod w)) u) :
    mv (b.coprod w) (avg u) + mv (a.coprod w) (avg u) =
      mv ((a + b).coprod w) (avg u) + mv (a.coprod (b.coprod w)) u := by
  have := congrArg avg (h (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b)
    ((AddMonoidHom.inr X Y).comp w))
  rw [map_add, map_add, avg_mv_fst _ (b.coprod w) (by simp) (by simp),
    avg_mv_fst _ (a.coprod w) (by simp) (by simp), avg_mv_fst _ ((a + b).coprod w) (by simp) (by simp),
    avg_mv_inr _ (a.coprod (b.coprod w)) (by simp)] at this
  exact this

theorem add_exists (u : A[X × X × X])
    (s₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri b a c) u)
    (s₂ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), mv (tri a b c) u = mv (tri a c b) u)
    (co : ∀ (Y : Type) [AddCommGroup Y] (a b c d : X →+ Y),
      mv (tri (a + b) c d) u + mv (tri a b d) u = mv (tri a (b + c) d) u + mv (tri b c d) u) (a b c : X →+ Y) :
    mv (tri a b c) u = mv (a + b + c) (avg (avg u)) + mv a (avg (avg u)) + mv b (avg (avg u)) + mv c (avg (avg u)) -
      mv (a + b) (avg (avg u)) - mv (a + c) (avg (avg u)) - mv (b + c) (avg (avg u)) := by
  have e₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), _ := fun Y _ a b c =>
    eq_of_cocycle u a b c (co _)
  have e₂ : ∀ (Y : Type) [AddCommGroup Y] (a b : X →+ Y),
      mv (a.coprod b) (avg u) = mv (b.coprod a) (avg u) := fun Y _ a b => by
    have := congrArg avg (s₂ _ (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b))
    rwa [avg_mv_fst _ (a.coprod b) (by simp) (by simp), avg_mv_fst _ (b.coprod a) (by simp) (by simp)] at this
  have e₃ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y),
      mv ((a + b).coprod c) (avg u) + mv (a.coprod b) (avg u) =
        mv (a.coprod (b + c)) (avg u) + mv (b.coprod c) (avg u) := fun Y _ a b c => by
    have p := e₁ Y a b c
    have q := e₁ Y b c a
    have r : mv (tri a b c) u = mv (tri b c a) u := (s₁ Y a b c).trans (s₂ Y b a c)
    linear_combination q - p - r + e₂ Y a b - e₂ Y c a - e₂ Y a (b + c)
  have e₄ : ∀ a b : X →+ Y, mv b (avg (avg u)) + mv a (avg (avg u)) =
      mv (a + b) (avg (avg u)) + mv (a.coprod b) (avg u) := fun a b => by
    have := congrArg avg (e₃ _ (.inl X Y) ((AddMonoidHom.inr X Y).comp a) ((AddMonoidHom.inr X Y).comp b))
    rwa [map_add, map_add, avg_mv_fst _ b (by simp) (by simp), avg_mv_fst _ a (by simp) (by simp),
      avg_mv_fst _ (a + b) (by simp) (by simp), avg_mv_inr _ (a.coprod b) (by simp)] at this
  linear_combination -e₁ Y a b c - e₄ b c - e₄ a c + e₄ (a + b) c

theorem add_unique (h : A[X]) (H : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y),
    mv (a + b + c) h + mv a h + mv b h + mv c h - mv (a + b) h - mv (a + c) h - mv (b + c) h = 0) : h = 0 := by
  have e₁ : ∀ (Y : Type) [AddCommGroup Y] (b c : X →+ Y), mv b h + mv c h = mv (b + c) h := fun Y _ b c => by
    have := congrArg avg (H _ (.inl X Y) ((AddMonoidHom.inr X Y).comp b) ((AddMonoidHom.inr X Y).comp c))
    simp only [map_add, map_sub, map_zero] at this
    rw [avg_mv_one _ (by simp), avg_mv_one _ (by simp), avg_mv_inr _ b (by simp), avg_mv_inr _ c (by simp),
      avg_mv_one _ (by simp), avg_mv_one _ (by simp), avg_mv_inr _ (b + c) (by simp)] at this
    linear_combination this
  have := congrArg avg (e₁ _ (.inl X X) (.inr X X))
  rw [map_add, avg_mv_one _ (by simp), avg_mv_inr _ (.id X) (by simp), avg_mv_one _ (by simp), mv_id] at this
  linear_combination this

abbrev rd (I : Ideal A) : A[X] →+* (A ⧸ I)[X] := mapRingHom X (Ideal.Quotient.mk I)

theorem rd_eq_zero {I : Ideal A} {u : A[X]} : rd I u = 0 ↔ ∀ x, u.coeff x ∈ I := by
  rw [← coeff_inj, Finsupp.ext_iff]
  simp [Ideal.Quotient.eq_zero_iff_mem]

theorem rd_mv (I : Ideal A) (f : X →+ Y) (u : A[X]) : rd I (mv f u) = mv f (rd I u) :=
  RingHom.congr_fun (mapRingHom_comp_mapDomainRingHom (Ideal.Quotient.mk I) f) u

theorem rd_avg (I : Ideal A) (u : A[X × Y]) : rd I (avg u) = avg (rd I u) := by
  ext y; simp [coeff_avg]

theorem rd_mul {I I' : Ideal A} {u v : A[X]} (hu : rd I u = 0) (hv : rd I' v = 0) : rd (I * I') (u * v) = 0 := by
  classical
  rw [rd_eq_zero] at *
  intro x
  rw [coeff_mul]
  refine Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ => ?_
  dsimp only
  split_ifs
  · exact Ideal.mul_mem_mul (hu a) (hv b)
  · exact zero_mem _

theorem rd_mono {I I' : Ideal A} (h : I ≤ I') {u : A[X]} (hu : rd I u = 0) : rd I' u = 0 :=
  rd_eq_zero.2 fun x => h (rd_eq_zero.1 hu x)

theorem eq_zero_of_rd {u : A[X]} (hu : rd ⊥ u = 0) : u = 0 := by
  ext x; exact rd_eq_zero.1 hu x

theorem isNilpotent_of_rd {I : Ideal A} (hI : IsNilpotent I) {u : A[X]} (hu : rd I u = 0) : IsNilpotent u := by
  obtain ⟨n, hn⟩ := hI
  have : ∀ k : ℕ, rd (I ^ k) (u ^ k) = 0 := fun k => by
    induction k with
    | zero => exact rd_eq_zero.2 fun x => by simp
    | succ k ih => rw [pow_succ, pow_succ]; exact rd_mul ih hu
  exact ⟨n, eq_zero_of_rd (rd_mono hn.le (this n))⟩

abbrev um (f : X →+ Y) : (A[X])ˣ →* (A[Y])ˣ := Units.map (mv f).toMonoidHom

theorem um_um (g : Y →+ W) (f : X →+ Y) (u : (A[X])ˣ) : um g (um f u) = um (g.comp f) u :=
  Units.ext (mv_mv g f u.val)

def cong (I : Ideal A) : Subgroup (A[X])ˣ := (Units.map (rd I).toMonoidHom).ker

theorem mem_cong {I : Ideal A} {u : (A[X])ˣ} : u ∈ cong I ↔ rd I u.val = 1 := Units.ext_iff

theorem mem_cong' {I : Ideal A} {u : (A[X])ˣ} : u ∈ cong I ↔ rd I (u.val - 1) = 0 := by
  rw [mem_cong, map_sub, map_one, sub_eq_zero]

theorem um_mem {I : Ideal A} (f : X →+ Y) {u : (A[X])ˣ} (hu : u ∈ cong I) : um f u ∈ cong I :=
  mem_cong.2 ((rd_mv I f u.val).trans (by rw [mem_cong.1 hu, map_one]))

def lin (I : Ideal A) (u : (A[X])ˣ) : (A ⧸ I * I)[X] := rd (I * I) (u.val - 1)

theorem lin_mul {I : Ideal A} {u v : (A[X])ˣ} (hu : u ∈ cong I) (hv : v ∈ cong I) :
    lin I (u * v) = lin I u + lin I v := by
  have := rd_mul (mem_cong'.1 hu) (mem_cong'.1 hv)
  simp only [lin, Units.val_mul, map_sub, map_mul, map_one] at this ⊢
  linear_combination this

theorem lin_div {I : Ideal A} {u v : (A[X])ˣ} (hu : u ∈ cong I) (hv : v ∈ cong I) :
    lin I (u / v) = lin I u - lin I v := by
  rw [eq_sub_iff_add_eq, ← lin_mul (div_mem hu hv) hv, div_mul_cancel]

theorem lin_um (I : Ideal A) (f : X →+ Y) (u : (A[X])ˣ) : lin I (um f u) = mv f (lin I u) := by
  rw [lin, lin, ← rd_mv, map_sub (mv f), map_one]; rfl

def del (g : (A[X])ˣ) (a b c : X →+ Y) : (A[Y])ˣ :=
  um (a + b + c) g * um a g * um b g * um c g / um (a + b) g / um (a + c) g / um (b + c) g

theorem um_del (f : Y →+ W) (g : (A[X])ˣ) (a b c : X →+ Y) :
    um f (del g a b c) = del g (f.comp a) (f.comp b) (f.comp c) := by
  simp only [del, map_mul, map_div, um_um, AddMonoidHom.comp_add]

theorem del_mul (g g' : (A[X])ˣ) (a b c : X →+ Y) : del (g * g') a b c = del g a b c * del g' a b c := by
  apply Additive.ofMul.injective
  simp only [del, map_mul, ofMul_mul, ofMul_div]
  abel

theorem del_mem {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) : del g a b c ∈ cong I :=
  div_mem (div_mem (div_mem (mul_mem (mul_mem (mul_mem (um_mem _ hg) (um_mem _ hg)) (um_mem _ hg)) (um_mem _ hg))
    (um_mem _ hg)) (um_mem _ hg)) (um_mem _ hg)

theorem lin_del {I : Ideal A} {g : (A[X])ˣ} (hg : g ∈ cong I) (a b c : X →+ Y) :
    lin I (del g a b c) = mv (a + b + c) (lin I g) + mv a (lin I g) + mv b (lin I g) + mv c (lin I g) -
      mv (a + b) (lin I g) - mv (a + c) (lin I g) - mv (b + c) (lin I g) := by
  have m : ∀ f : X →+ Y, um f g ∈ cong I := fun f => um_mem f hg
  have m₄ := mul_mem (mul_mem (mul_mem (m (a + b + c)) (m a)) (m b)) (m c)
  rw [del, lin_div (div_mem (div_mem m₄ (m _)) (m _)) (m _), lin_div (div_mem m₄ (m _)) (m _), lin_div m₄ (m _),
    lin_mul (mul_mem (mul_mem (m _) (m _)) (m _)) (m _), lin_mul (mul_mem (m _) (m _)) (m _), lin_mul (m _) (m _)]
  simp only [lin_um]

abbrev p₁ : X →+ X × X × X := .inl X (X × X)

abbrev p₂ : X →+ X × X × X := (AddMonoidHom.inr X (X × X)).comp (.inl X X)

abbrev p₃ : X →+ X × X × X := (AddMonoidHom.inr X (X × X)).comp (.inr X X)

theorem tri_p₁ (a b c : X →+ Y) : (tri a b c).comp p₁ = a := by ext; simp
theorem tri_p₂ (a b c : X →+ Y) : (tri a b c).comp p₂ = b := by ext; simp
theorem tri_p₃ (a b c : X →+ Y) : (tri a b c).comp p₃ = c := by ext; simp
theorem tri_p : tri (p₁ (X := X)) p₂ p₃ = .id _ := by ext <;> simp

theorem um_tri_del (g : (A[X])ˣ) (a b c : X →+ Y) : um (tri a b c) (del g p₁ p₂ p₃) = del g a b c := by
  rw [um_del, tri_p₁, tri_p₂, tri_p₃]

structure Cub (e : (A[X × X × X])ˣ) : Prop where
  s₁ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), um (tri a b c) e = um (tri b a c) e
  s₂ : ∀ (Y : Type) [AddCommGroup Y] (a b c : X →+ Y), um (tri a b c) e = um (tri a c b) e
  co : ∀ (Y : Type) [AddCommGroup Y] (a b c d : X →+ Y),
    um (tri (a + b) c d) e * um (tri a b d) e = um (tri a (b + c) d) e * um (tri b c d) e

theorem Cub.div_del {e : (A[X × X × X])ˣ} (he : Cub e) (g : (A[X])ˣ) : Cub (e / del g p₁ p₂ p₃) := by
  refine ⟨fun Y _ a b c => ?_, fun Y _ a b c => ?_, fun Y _ a b c d => ?_⟩
  · rw [map_div, map_div, um_tri_del, um_tri_del, he.s₁, del, del, add_comm b a]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  · rw [map_div, map_div, um_tri_del, um_tri_del, he.s₂, del, del, add_comm c b, add_right_comm a c b]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div]
    abel
  · have := congrArg Additive.ofMul (he.co Y a b c d)
    simp only [map_div, um_tri_del]
    simp only [del, ← add_assoc]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_div] at this ⊢
    linear_combination (norm := abel) this

theorem Cub.step {e : (A[X × X × X])ˣ} (he : Cub e) {I : Ideal A} (hI : IsNilpotent I) (h : e ∈ cong I) :
    ∃ g ∈ cong I, e / del g p₁ p₂ p₃ ∈ cong (I * I) := by
  have h₀ : rd I (avg (avg (e.val - 1))) = 0 := by rw [rd_avg, rd_avg, mem_cong'.1 h, map_zero, map_zero]
  obtain ⟨g, hg⟩ := (isNilpotent_of_rd hI h₀).isUnit_add_one
  have hg' : g ∈ cong I := mem_cong'.2 (by rw [hg, add_sub_cancel_right, h₀])
  have lg : lin I g = avg (avg (lin I e)) := by rw [lin, lin, hg, add_sub_cancel_right, rd_avg, rd_avg]
  refine ⟨g, hg', mem_cong'.2 ?_⟩
  have := add_exists (lin I e) (fun Y _ a b c => by rw [← lin_um, ← lin_um, he.s₁])
    (fun Y _ a b c => by rw [← lin_um, ← lin_um, he.s₂]) (fun Y _ a b c d => by
      simp only [← lin_um]
      rw [← lin_mul (um_mem _ h) (um_mem _ h), he.co, lin_mul (um_mem _ h) (um_mem _ h)]) p₁ p₂ p₃
  rw [tri_p, mv_id, ← lg, ← lin_del hg'] at this
  exact (lin_div h (del_mem hg' _ _ _)).trans (sub_eq_zero.2 this)

theorem cong_mono {I I' : Ideal A} (h : I ≤ I') {u : (A[X])ˣ} (hu : u ∈ cong I) : u ∈ cong I' :=
  mem_cong'.2 (rd_mono h (mem_cong'.1 hu))

theorem exists_cong_pow {J : Ideal A} (hJ : IsNilpotent J) :
    ∃ n : ℕ, ∀ u : (A[X])ˣ, u ∈ cong (J ^ (n + 1)) → u = 1 := by
  obtain ⟨n, hn⟩ := hJ
  have : J ^ (n + 1) ≤ ⊥ := by rw [pow_succ, hn]; simp
  exact ⟨n, fun u hu => Units.ext (sub_eq_zero.1 (eq_zero_of_rd (mem_cong'.1 (cong_mono this hu))))⟩

theorem pow_mul_pow_le (J : Ideal A) (k : ℕ) : J ^ (k + 1) * J ^ (k + 1) ≤ J ^ (k + 1 + 1) := by
  rw [← pow_add]; exact Ideal.pow_le_pow_right (by omega)

theorem del_one (a b c : X →+ Y) : del (1 : (A[X])ˣ) a b c = 1 := by simp only [del, map_one, mul_one, div_one]

theorem Cub.exists_del {e : (A[X × X × X])ˣ} (he : Cub e) {J : Ideal A} (hJ : IsNilpotent J) (h : e ∈ cong J) :
    ∃ g ∈ cong J, e = del g p₁ p₂ p₃ := by
  have ind : ∀ k : ℕ, ∃ g ∈ cong J, e / del g p₁ p₂ p₃ ∈ cong (J ^ (k + 1)) := fun k => by
    induction k with
    | zero => exact ⟨1, one_mem _, by rwa [del_one, div_one, zero_add, pow_one]⟩
    | succ k ih =>
      obtain ⟨g, hg, hu⟩ := ih
      obtain ⟨g', hg', hu'⟩ := (he.div_del g).step (hJ.pow_succ k) hu
      refine ⟨g * g', mul_mem hg (cong_mono (Ideal.pow_le_self (by omega)) hg'), ?_⟩
      rw [del_mul, ← div_div]
      exact cong_mono (pow_mul_pow_le J k) hu'
  obtain ⟨n, hn⟩ := exists_cong_pow (X := X × X × X) hJ
  obtain ⟨g, hg, e⟩ := ind n
  exact ⟨g, hg, div_eq_one.1 (hn _ e)⟩

theorem eq_one_of_del {g : (A[X])ˣ} {J : Ideal A} (hJ : IsNilpotent J) (h : g ∈ cong J)
    (hg : del g p₁ p₂ p₃ = 1) : g = 1 := by
  have ind : ∀ k : ℕ, g ∈ cong (J ^ (k + 1)) := fun k => by
    induction k with
    | zero => rwa [zero_add, pow_one]
    | succ k ih =>
      refine cong_mono (pow_mul_pow_le J k) (mem_cong'.2 (add_unique (lin _ g) fun Y _ a b c => ?_))
      rw [← lin_del ih, ← um_tri_del, hg, map_one, lin, Units.val_one, sub_self, map_zero]
  obtain ⟨n, hn⟩ := exists_cong_pow (X := X) hJ
  exact hn g (ind n)

end GlobalTheory.CubeLift
