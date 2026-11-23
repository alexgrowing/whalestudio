import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.NotAllMatchRankZero
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Ex
open scoped BigOperators

noncomputable section
namespace GlobalTheory.Ex.NumD.Hom
variable {O O' : Type} [CommRing O] [CommRing O'] {f : O →+* O'} {N : NumD O} {N' : NumD O'} (I : NumD.Hom f N N')

local notation "F" => Units.map (RingHom.toMonoidHom f)

theorem cubN_eq (k : ℕ) (m x : N.A) :
    cubN N'.θ k 1 (I.φ m) (I.φ x) * I.h (m ^ k) * I.h x * I.h (m * x) ^ k =
      F (cubN N.θ k 1 m x) * I.h (m ^ k * x) * I.h m ^ k * I.h x ^ k := by
  induction k with
  | zero => simp [cubN, I.h_one]
  | succ k ih =>
    have a := I.θ_eq (m ^ k) m x
    simp only [cubN, Finset.prod_range_succ, one_mul, map_mul] at ih ⊢
    rw [← pow_succ, map_pow] at a
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace ih := congrArg Additive.ofMul ih
    rw [pow_succ (I.h m), pow_succ (I.h x), pow_succ (I.h (m * x))]
    simp only [ofMul_mul] at a ih ⊢
    linear_combination (norm := abel) a + ih

theorem dbl_eq (x : N.A) :
    dbl N'.θ N'.σ (I.φ x) * I.h (x * x) = F (dbl N.θ N.σ x) * I.h x ^ 4 := by
  have a := I.θ_eq x x⁻¹ x
  have b := I.σ_eq x
  rw [mul_inv_cancel, inv_mul_cancel, I.h_one, one_mul, map_inv, mul_one, mul_one] at a
  simp only [dbl, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ⊢
  linear_combination (norm := abel) a - b

theorem mulq_eq (n : ℕ) (x : N.A) :
    mulq N'.θ N'.σ n (I.φ x) * I.h x ^ (n ^ 2) = F (mulq N.θ N.σ n x) * I.h (x ^ n) := by
  induction n with
  | zero => simp [mulq, I.h_one]
  | succ n ih =>
    have a := I.cubN_eq n x x
    have b := I.dbl_eq x
    rw [← pow_succ] at a
    simp only [mulq, Finset.prod_range_succ, map_mul, map_div, map_pow] at ih ⊢
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    replace ih := congrArg Additive.ofMul ih
    simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b ih ⊢
    linear_combination (norm := module) a + ih - n • b

def img (g : N.Gt) : N'.Gt :=
  ⟨I.φ g.b, fun χ => F (g.s (I.e.symm χ)) * I.h (N.c (I.e.symm χ)) * I.h g.b / I.h (N.c (I.e.symm χ) * g.b),
    fun χ χ' => by
      obtain ⟨χ, rfl⟩ := I.e.surjective χ
      obtain ⟨χ', rfl⟩ := I.e.surjective χ'
      rw [← map_add]
      simp only [AddEquiv.symm_apply_apply]
      rw [I.c_eq, I.c_eq, N.c_add]
      have a := I.θ_eq (N.c χ) (N.c χ') g.b
      have b := congrArg F (g.mult χ χ')
      simp only [map_mul] at b
      apply Additive.ofMul.injective
      replace a := congrArg Additive.ofMul a
      replace b := congrArg Additive.ofMul b
      simp only [ofMul_mul, ofMul_div] at a b ⊢
      linear_combination (norm := abel) a + b⟩

theorem rel_img (g : N.Gt) : I.Rel g (I.img g) :=
  ⟨rfl, fun χ => by simp only [img, AddEquiv.symm_apply_apply, div_mul_cancel]⟩

theorem rel_iff (g : N.Gt) (g' : N'.Gt) : I.Rel g g' ↔ g' = I.img g := by
  refine ⟨fun h => Gt.ext h.1 (funext fun χ => ?_), fun h => h ▸ I.rel_img g⟩
  obtain ⟨χ, rfl⟩ := I.e.surjective χ
  exact mul_right_cancel ((h.2 χ).trans ((I.rel_img g).2 χ).symm)

theorem rel_existsUnique (g : N.Gt) : ∃! g', I.Rel g g' :=
  ⟨I.img g, I.rel_img g, fun g' h => (I.rel_iff g g').1 h⟩

variable {I} in

theorem Rel.mul {g h : N.Gt} {g' h' : N'.Gt} (hg : I.Rel g g') (hh : I.Rel h h') : I.Rel (g * h) (g' * h') := by
  refine ⟨by rw [Gt.mul_b, Gt.mul_b, hg.1, hh.1, map_mul], fun χ => ?_⟩
  have a := I.θ_eq (N.c χ) g.b h.b
  have b := hg.2 χ
  have c := hh.2 χ
  rw [Gt.mul_s, Gt.mul_s, Gt.mul_b, hg.1, hh.1, I.c_eq, ← mul_assoc, map_div, map_mul]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div] at a b c ⊢
  linear_combination (norm := abel) b + c - a

theorem rel_one : I.Rel 1 1 :=
  ⟨by simp, fun χ => by simp [I.h_one]⟩

variable {I} in

theorem Rel.pow {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') (n : ℕ) : I.Rel (g ^ n) (g' ^ n) := by
  induction n with
  | zero => simpa using I.rel_one
  | succ n ih => rw [pow_succ, pow_succ]; exact ih.mul hg

theorem rel_io (y : N.X) : I.Rel (N.io y) (N'.io (I.e y)) := by
  refine ⟨I.c_eq y, fun χ => ?_⟩
  have a := I.ψ_eq (y + χ)
  have b := I.ψ_eq y
  have c := I.ψ_eq χ
  rw [N.c_add, map_add, mul_comm (N.c y)] at a
  simp only [io_s, io_b, τ, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  simp only [ofMul_mul, ofMul_div] at a b c ⊢
  linear_combination (norm := abel) a - b - c

private theorem cb {k : ℕ} (p : N.QT k) : N.c p.1.1.toAdd = p.1.2.b ^ k := by
  have h : p.1.2 ^ k = N.io p.1.1.toAdd := p.2
  rw [← Gt.pow_b, h, io_b]

theorem s_cubN_eq {k : ℕ} (q : N.QT k) {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') :
    g'.s (I.e q.1.1.toAdd) * cubN N'.θ k 1 (I.φ q.1.2.b) (I.φ g.b) * I.h (q.1.2.b * g.b) ^ k =
      F (g.s q.1.1.toAdd * cubN N.θ k 1 q.1.2.b g.b) * I.h q.1.2.b ^ k * I.h g.b ^ k := by
  have a := hg.2 q.1.1.toAdd
  have b := I.cubN_eq k q.1.2.b g.b
  rw [cb] at a
  rw [map_mul]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul] at a b ⊢
  linear_combination (norm := abel) a + b

theorem wp_eq {k : ℕ} (p q : N.QT k) (p' q' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (eq : q'.1.1.toAdd = I.e q.1.1.toAdd) (hq : I.Rel q.1.2 q'.1.2) :
    N'.wp p' q' = F (N.wp p q) := by
  have a := I.s_cubN_eq q hp
  have b := I.s_cubN_eq p hq
  rw [mul_comm p.1.2.b] at b
  simp only [wp, tk, ep, eq, hp.1, hq.1, map_div]
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  simp only [ofMul_mul, ofMul_div] at a b ⊢
  linear_combination (norm := abel) a - b

theorem wQ_eq {k : ℕ} (hk : Odd k) (p : N.QT k) (p' : N'.QT k) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) : N'.wQ p' * I.h p.1.2.b ^ k = F (N.wQ p) := by
  have a := I.s_cubN_eq p hp
  have b := I.dbl_eq p.1.2.b
  have c := I.mulq_eq k p.1.2.b
  have d := I.ψ_eq p.1.1.toAdd
  rw [cb] at d
  obtain ⟨j, rfl⟩ := hk
  have e : (2 * j + 1 - 1) / 2 = j := by omega
  simp only [wQ, NumB.wS, ep, hp.1, map_div, map_mul, map_pow, e] at a ⊢
  apply Additive.ofMul.injective
  replace a := congrArg Additive.ofMul a
  replace b := congrArg Additive.ofMul b
  replace c := congrArg Additive.ofMul c
  replace d := congrArg Additive.ofMul d
  simp only [ofMul_mul, ofMul_div, ofMul_pow] at a b c d ⊢
  linear_combination (norm := module) d + c - j • a + (j * (2 * j + 1)) • b

variable {I} in

theorem Rel.vt_eq {g : N.Gt} {g' : N'.Gt} (hg : I.Rel g g') (χ : N.X) :
    N'.vt g' (I.e χ) = (I.lam * I.h g.b : O'ˣ) * f (N.vt g χ) := by
  have a := hg.2 χ
  have d := I.ψ_eq χ
  have key : N'.ψ (I.e χ) * g'.s (I.e χ) * (I.lam * I.h (N.c χ * g.b)) = I.lam * I.h g.b * F (N.ψ χ * g.s χ) := by
    rw [map_mul]
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace d := congrArg Additive.ofMul d
    simp only [ofMul_mul] at a d ⊢
    linear_combination (norm := abel) a + d
  rw [vt, vt, I.c_eq, hg.1, ← map_mul, I.th_eq, ← mul_assoc, ← Units.val_mul, key, map_mul f, Units.val_mul,
    mul_assoc]
  rfl

theorem txT_eq {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (χ : N.X) : N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) := by
  have a := I.wQ_eq hm.pow p p' ep hp
  have b := I.mulq_eq m p.1.2.b
  have key : N'.wQ p' / mulq N'.θ N'.σ m (I.φ p.1.2.b) * (I.lam * I.h (p.1.2.b ^ m)) =
      I.lam * F (N.wQ p / mulq N.θ N.σ m p.1.2.b) := by
    rw [map_div]
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    simp only [ofMul_mul, ofMul_div] at a b ⊢
    linear_combination (norm := abel) a - b
  rw [txT, txT, (hp.pow m).vt_eq, hp.1, Gt.pow_b, ← mul_assoc, ← Units.val_mul, key, map_mul f, Units.val_mul,
    mul_assoc]
  rfl

theorem evT_eq {m : ℕ} (hm : Odd m) (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)) (ep : p'.1.1.toAdd = I.e p.1.1.toAdd)
    (hp : I.Rel p.1.2 p'.1.2) (χ : N.X) (h : N.Gt) (h' : N'.Gt) (hh : I.Rel h h') :
    N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) := by
  have a := I.wQ_eq hm.pow p p' ep hp
  have b := I.mulq_eq m (h.b * p.1.2.b)
  have c := I.s_cubN_eq p hh
  rw [mul_comm p.1.2.b] at c
  have key : h'.s (I.e p.1.1.toAdd) * cubN N'.θ (m ^ 2) 1 (I.φ p.1.2.b) (I.φ h.b) * N'.wQ p' /
      mulq N'.θ N'.σ m (I.φ (h.b * p.1.2.b)) * (I.lam * I.h ((h.b * p.1.2.b) ^ m)) =
      I.lam * I.h h.b ^ (m ^ 2) * F (h.s p.1.1.toAdd * cubN N.θ (m ^ 2) 1 p.1.2.b h.b * N.wQ p /
        mulq N.θ N.σ m (h.b * p.1.2.b)) := by
    rw [map_div, map_mul F]
    apply Additive.ofMul.injective
    replace a := congrArg Additive.ofMul a
    replace b := congrArg Additive.ofMul b
    replace c := congrArg Additive.ofMul c
    simp only [ofMul_mul, ofMul_div] at a b c ⊢
    linear_combination (norm := abel) a - b + c
  rw [evT, evT, ((hh.mul hp).pow m).vt_eq, hp.1, hh.1, ep, ← map_mul, Gt.pow_b, Gt.mul_b, ← mul_assoc,
    ← Units.val_mul, key, map_mul f, Units.val_mul, mul_assoc]
  rfl

def ofIso {M M' : NumD O} (J : NumD.Iso M M') : NumD.Hom (RingHom.id O) M M' where
  φ := J.φ.toMonoidHom
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq

theorem ofIso_rel {M M' : NumD O} (J : NumD.Iso M M') (g : M.Gt) (g' : M'.Gt) :
    (ofIso J).Rel g g' ↔ J.Rel g g' := Iff.rfl

def isoOfBijective {M M' : NumD O} (J : NumD.Hom (RingHom.id O) M M') (hJ : Function.Bijective J.φ) :
    NumD.Iso M M' where
  φ := MulEquiv.ofBijective J.φ hJ
  h := J.h
  h_one := J.h_one
  θ_eq := J.θ_eq
  σ_eq := J.σ_eq
  lam := J.lam
  th_eq := J.th_eq
  e := J.e
  c_eq := J.c_eq
  ψ_eq := J.ψ_eq

theorem isoOfBijective_rel {M M' : NumD O} (J : NumD.Hom (RingHom.id O) M M') (hJ : Function.Bijective J.φ)
    (g : M.Gt) (g' : M'.Gt) : (J.isoOfBijective hJ).Rel g g' ↔ J.Rel g g' := Iff.rfl

end GlobalTheory.Ex.NumD.Hom

theorem GlobalTheory.Ex.NumD.hom_transport : ∀ (O O' : Type) [CommRing O] [CommRing O'] (f : O →+* O') (N : NumD O) (N' : NumD O') (I : NumD.Hom f N N'), (∀ g, ∃! g', I.Rel g g') ∧ (∀ g h g' h', I.Rel g g' → I.Rel h h' → I.Rel (g * h) (g' * h')) ∧ (∀ y, I.Rel (N.io y) (N'.io (I.e y))) ∧ (∀ k (p q : N.QT k) (p' q' : N'.QT k), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → q'.1.1.toAdd = I.e q.1.1.toAdd → I.Rel q.1.2 q'.1.2 → N'.wp p' q' = Units.map f.toMonoidHom (N.wp p q)) ∧ ∀ m, Odd m → ∀ (p : N.QT (m ^ 2)) (p' : N'.QT (m ^ 2)), p'.1.1.toAdd = I.e p.1.1.toAdd → I.Rel p.1.2 p'.1.2 → ∀ χ, N'.txT m p' (I.e χ) = I.lam * f (N.txT m p χ) ∧ ∀ h h', I.Rel h h' → N'.evT m p' h' (I.e χ) = (I.lam * I.h h.b ^ (m ^ 2) : O'ˣ) * f (N.evT m p h χ) :=
  fun _ _ _ _ _ _ _ I => ⟨I.rel_existsUnique, fun _ _ _ _ hg hh => hg.mul hh, I.rel_io,
    fun _ p q p' q' => I.wp_eq p q p' q',
    fun _ hm p p' ep hp χ => ⟨I.txT_eq hm p p' ep hp χ, I.evT_eq hm p p' ep hp χ⟩⟩
end
