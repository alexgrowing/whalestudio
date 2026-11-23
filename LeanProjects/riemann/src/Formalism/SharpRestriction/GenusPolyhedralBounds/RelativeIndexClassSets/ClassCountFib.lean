import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ClassCountStmt

noncomputable section

namespace Formalism.MainNotions.Gaps.CC.Fib

open MulAction

variable {G : Type*} [Group G]

def Gam (Γ K : Subgroup G) (g : G) : Subgroup G :=
  Γ ⊓ K.comap (MulAut.conj g⁻¹).toMonoidHom

theorem mem_Gam {Γ K : Subgroup G} {g x : G} : x ∈ Gam Γ K g ↔ x ∈ Γ ∧ g⁻¹ * x * g ∈ K := by
  simp [Gam, Subgroup.mem_inf, Subgroup.mem_comap, MulAut.conj_apply]

theorem Gam_eq_map (Γ K : Subgroup G) (g : G) :
    Gam Γ K g = Γ ⊓ K.map (MulAut.conj g).toMonoidHom := by
  ext x
  rw [mem_Gam, Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hx, hk⟩
    refine ⟨hx, _, hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  · rintro ⟨hx, k, hk, rfl⟩
    refine ⟨hx, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    convert hk using 1
    group

theorem Gam_mono {Γ K U : Subgroup G} (h : U ≤ K) (g : G) : Gam Γ U g ≤ Gam Γ K g := fun _ hx => mem_Gam.2 ⟨(mem_Gam.1 hx).1, h (mem_Gam.1 hx).2⟩

def GamEquivSet (Γ K : Subgroup G) (g : G) : Gam Γ K g ≃ {γ : Γ | g⁻¹ * (γ : G) * g ∈ K} where
  toFun x := ⟨⟨x.1, (mem_Gam.1 x.2).1⟩, (mem_Gam.1 x.2).2⟩
  invFun y := ⟨y.1.1, mem_Gam.2 ⟨y.1.2, y.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

def GamCongr {Γ U : Subgroup G} {x x' h u : G} (hh : h ∈ Γ) (hu : u ∈ U) (e : x' = h * x * u) :
    Gam Γ U x ≃* Gam Γ U x' where
  toFun y := ⟨h * y * h⁻¹, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem hh (mem_Gam.1 y.2).1) (Γ.inv_mem hh), by
    have := U.mul_mem (U.mul_mem (U.inv_mem hu) (mem_Gam.1 y.2).2) hu
    rw [e]; convert this using 1; group⟩⟩
  invFun y := ⟨h⁻¹ * y * h, mem_Gam.2 ⟨Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hh) (mem_Gam.1 y.2).1) hh, by
    have := U.mul_mem (U.mul_mem hu (mem_Gam.1 y.2).2) (U.inv_mem hu)
    subst e; convert this using 1; group⟩⟩
  left_inv y := by ext; simp [mul_assoc]
  right_inv y := by ext; simp [mul_assoc]
  map_mul' y z := by ext; simp [mul_assoc]

def GamCongrMk {Γ U : Subgroup G} {x x' : G} (e : DoubleCoset.mk Γ U x = DoubleCoset.mk Γ U x') :
    Gam Γ U x ≃* Gam Γ U x' :=
  have h := (DoubleCoset.eq Γ U x x').1 e
  GamCongr h.choose_spec.1 h.choose_spec.2.choose_spec.1 h.choose_spec.2.choose_spec.2

def toK (Γ K : Subgroup G) (g : G) : Gam Γ K g →* K where
  toFun x := ⟨g⁻¹ * x * g, (mem_Gam.1 x.2).2⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]

@[simp] theorem toK_coe (Γ K : Subgroup G) (g : G) (x : Gam Γ K g) : (toK Γ K g x : G) = g⁻¹ * x * g := rfl

theorem toK_injective (Γ K : Subgroup G) (g : G) : Function.Injective (toK Γ K g) := by
  intro a b hab
  apply Subtype.ext
  have := congrArg (fun k : K => (k : G)) hab
  simpa using this

instance actK (Γ K U : Subgroup G) (g : G) : MulAction (Gam Γ K g) (K ⧸ U.subgroupOf K) :=
  MulAction.compHom _ (toK Γ K g)

theorem smul_mk (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (k : K) :
    x • (k : K ⧸ U.subgroupOf K) = ((toK Γ K g x * k : K) : K ⧸ U.subgroupOf K) := rfl

theorem mk_eq_iff {K U : Subgroup G} {k k' : K} :
    (k : K ⧸ U.subgroupOf K) = (k' : K ⧸ U.subgroupOf K) ↔ (k : G)⁻¹ * k' ∈ U := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  simp

def stabEquiv {Γ K U : Subgroup G} (hUK : U ≤ K) (g : G) (k : K) :
    stabilizer (Gam Γ K g) (k : K ⧸ U.subgroupOf K) ≃* Gam Γ U (g * k) where
  toFun x := ⟨x.1.1, mem_Gam.2 ⟨(mem_Gam.1 x.1.2).1, by
    have h := x.2
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff] at h
    simpa [mul_assoc] using h⟩⟩
  invFun y := ⟨⟨y.1, mem_Gam.2 ⟨(mem_Gam.1 y.2).1, by
      have h := K.mul_mem (K.mul_mem k.2 (hUK (mem_Gam.1 y.2).2)) (K.inv_mem k.2)
      simpa [mul_assoc] using h⟩⟩, by
    rw [mem_stabilizer_iff, smul_mk, eq_comm, mk_eq_iff]
    simpa [mul_assoc] using (mem_Gam.1 y.2).2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem stabEquiv_coe {Γ K U : Subgroup G} (hUK : U ≤ K) (g : G) (k : K)
    (x : stabilizer (Gam Γ K g) (k : K ⧸ U.subgroupOf K)) : (stabEquiv hUK g k x : G) = x.1.1 := rfl

def toCls (Γ K U : Subgroup G) (g : G) : K ⧸ U.subgroupOf K → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (fun k : K => DoubleCoset.mk Γ U (g * k)) (by
    intro a b h
    have h' : (a : G)⁻¹ * b ∈ U := by
      have := QuotientGroup.leftRel_apply.1 h
      simpa [Subgroup.mem_subgroupOf] using this
    exact (DoubleCoset.eq Γ U _ _).2 ⟨1, Γ.one_mem, _, h', by simp [mul_assoc]⟩)

@[simp] theorem toCls_mk (Γ K U : Subgroup G) (g : G) (k : K) :
    toCls Γ K U g (k : K ⧸ U.subgroupOf K) = DoubleCoset.mk Γ U (g * k) := rfl

theorem toCls_smul (Γ K U : Subgroup G) (g : G) (x : Gam Γ K g) (y : K ⧸ U.subgroupOf K) :
    toCls Γ K U g (x • y) = toCls Γ K U g y := by
  induction y using QuotientGroup.induction_on with
  | H k =>
    rw [smul_mk, toCls_mk, toCls_mk]
    refine (DoubleCoset.eq _ _ _ _).2 ⟨(x : G)⁻¹, Γ.inv_mem (mem_Gam.1 x.2).1, 1, U.one_mem, ?_⟩
    simp only [Subgroup.coe_mul, toK_coe]
    group

def orbToCls (Γ K U : Subgroup G) (g : G) :
    orbitRel.Quotient (Gam Γ K g) (K ⧸ U.subgroupOf K) → DoubleCoset.Quotient (Γ : Set G) U :=
  Quotient.lift (toCls Γ K U g) (by
    rintro a b ⟨x, rfl⟩
    exact toCls_smul Γ K U g x b)

@[simp] theorem orbToCls_mk (Γ K U : Subgroup G) (g : G) (y : K ⧸ U.subgroupOf K) :
    orbToCls Γ K U g (Quotient.mk'' y) = toCls Γ K U g y := rfl

def total (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G) :
    (Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)) →
      DoubleCoset.Quotient (Γ : Set G) U :=
  fun p => orbToCls Γ K U (rep p.1) p.2

theorem total_surjective (Γ K U : Subgroup G) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Surjective (total Γ K U rep) := by
  intro q
  obtain ⟨h, hh, k, hk, hx⟩ := (DoubleCoset.eq Γ K _ _).1 (hrep (DoubleCoset.mk Γ K (Quotient.out q)))
  refine ⟨⟨DoubleCoset.mk Γ K (Quotient.out q), Quotient.mk'' ((⟨k, hk⟩ : K) : K ⧸ U.subgroupOf K)⟩, ?_⟩
  show orbToCls Γ K U _ (Quotient.mk'' _) = q
  rw [orbToCls_mk, toCls_mk]
  conv_rhs => rw [← DoubleCoset.out_eq' Γ U q]
  refine (DoubleCoset.eq _ _ _ _).2 ⟨h, hh, 1, U.one_mem, ?_⟩
  rw [mul_one, ← mul_assoc]
  exact hx

theorem total_injective {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) : Function.Injective (total Γ K U rep) := by
  rintro ⟨c, o⟩ ⟨c', o'⟩ heq
  induction o using Quotient.inductionOn' with
  | h y =>
  induction o' using Quotient.inductionOn' with
  | h y' =>
  induction y using QuotientGroup.induction_on with
  | H k =>
  induction y' using QuotientGroup.induction_on with
  | H k' =>
  have heq' : DoubleCoset.mk Γ U (rep c * k) = DoubleCoset.mk Γ U (rep c' * k') := heq
  obtain ⟨h, hh, u, hu, he⟩ := (DoubleCoset.eq Γ U _ _).1 heq'
  have hcc : c = c' := by
    rw [← hrep c, ← hrep c']
    refine (DoubleCoset.eq Γ K _ _).2 ⟨h, hh, (k : G) * u * (k' : G)⁻¹,
      K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2), ?_⟩
    rw [eq_mul_inv_of_mul_eq he]
    group
  subst hcc
  have e1 : h = rep c * k' * u⁻¹ * (k : G)⁻¹ * (rep c)⁻¹ := by
    rw [he]
    group
  have hx : h⁻¹ ∈ Gam Γ K (rep c) := by
    refine mem_Gam.2 ⟨Γ.inv_mem hh, ?_⟩
    have : (rep c)⁻¹ * h⁻¹ * rep c = (k : G) * u * (k' : G)⁻¹ := by
      rw [e1]
      group
    rw [this]
    exact K.mul_mem (K.mul_mem k.2 (hUK hu)) (K.inv_mem k'.2)
  simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
  refine Quotient.sound ⟨⟨h⁻¹, hx⟩, ?_⟩
  show (⟨h⁻¹, hx⟩ : Gam Γ K (rep c)) • ((k' : K) : K ⧸ U.subgroupOf K) = ((k : K) : K ⧸ U.subgroupOf K)
  rw [smul_mk, mk_eq_iff]
  simp only [Subgroup.coe_mul, toK_coe]
  rw [e1]
  convert U.inv_mem hu using 1
  group

def fibRep {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K, orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K) :=
  (Equiv.ofBijective (total Γ K U rep) ⟨total_injective hUK rep hrep, total_surjective Γ K U rep hrep⟩).symm

theorem fibRep_symm_mk {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (c : DoubleCoset.Quotient (Γ : Set G) K) (k : K) :
    (fibRep hUK rep hrep).symm ⟨c, Quotient.mk'' (k : K ⧸ U.subgroupOf K)⟩ = DoubleCoset.mk Γ U (rep c * k) := rfl

theorem fibRep_mk {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (c : DoubleCoset.Quotient (Γ : Set G) K) (k : K) :
    fibRep hUK rep hrep (DoubleCoset.mk Γ U (rep c * k)) = ⟨c, Quotient.mk'' (k : K ⧸ U.subgroupOf K)⟩ := by
  rw [← fibRep_symm_mk hUK rep hrep c k, Equiv.apply_symm_apply]

theorem fibRep_fst {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (x : G) :
    (fibRep hUK rep hrep (DoubleCoset.mk Γ U x)).1 = DoubleCoset.mk Γ K x := by
  have hp := (fibRep hUK rep hrep).symm_apply_apply (DoubleCoset.mk Γ U x)
  generalize fibRep hUK rep hrep (DoubleCoset.mk Γ U x) = p at hp ⊢
  obtain ⟨c, o⟩ := p
  induction o using Quotient.inductionOn' with
  | h y =>
  induction y using QuotientGroup.induction_on with
  | H k =>
  rw [fibRep_symm_mk] at hp
  obtain ⟨h, hh, u, hu, he⟩ := (DoubleCoset.eq Γ U _ _).1 hp
  show c = DoubleCoset.mk Γ K x
  rw [← hrep c]
  refine (DoubleCoset.eq Γ K _ _).2 ⟨h, hh, (k : G) * u, K.mul_mem k.2 (hUK hu), ?_⟩
  rw [he]
  group

def fib {Γ K U : Subgroup G} (hUK : U ≤ K) :
    DoubleCoset.Quotient (Γ : Set G) U ≃
      Σ c : DoubleCoset.Quotient (Γ : Set G) K,
        orbitRel.Quotient (Gam Γ K (Quotient.out c)) (K ⧸ U.subgroupOf K) :=
  fibRep hUK Quotient.out (DoubleCoset.out_eq' Γ K)

def stabEquivCls {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) (c : DoubleCoset.Quotient (Γ : Set G) K)
    (y : K ⧸ U.subgroupOf K) :
    stabilizer (Gam Γ K (rep c)) y ≃*
      Gam Γ U (Quotient.out ((fibRep hUK rep hrep).symm ⟨c, Quotient.mk'' y⟩)) :=
  ((MulEquiv.subgroupCongr (by rw [QuotientGroup.out_eq'])).trans (stabEquiv hUK (rep c) (Quotient.out y))).trans
    (GamCongrMk (by rw [DoubleCoset.out_eq', ← fibRep_symm_mk hUK rep hrep, QuotientGroup.out_eq']))

theorem Gam_eq_bot_iff {Γ U : Subgroup G} {x : G} :
    Gam Γ U x = ⊥ ↔ ∀ γ ∈ Γ, x⁻¹ * γ * x ∈ U → γ = 1 := by
  simp only [Subgroup.eq_bot_iff_forall, mem_Gam, and_imp]

theorem stabilizer_eq_bot {Γ K U : Subgroup G} (hUK : U ≤ K) (g : G)
    (htriv : ∀ k : K, Gam Γ U (g * k) = ⊥) (y : K ⧸ U.subgroupOf K) :
    stabilizer (Gam Γ K g) y = ⊥ := by
  induction y using QuotientGroup.induction_on with
  | H k =>
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have h1 := mem_Gam.1 (stabEquiv hUK g k ⟨x, hx⟩).2
  rw [stabEquiv_coe] at h1
  exact Subtype.ext (Gam_eq_bot_iff.1 (htriv k) _ h1.1 h1.2)

theorem sum_inv_card_stabilizer (H X : Type*) [Group H] [MulAction H X] [Finite H] [Finite X]
    [Fintype (orbitRel.Quotient H X)] :
    ∑ ω : orbitRel.Quotient H X, ((Nat.card (stabilizer H (Quotient.out ω)) : ℝ))⁻¹ =
      (Nat.card X : ℝ) / Nat.card H := by
  classical
  have hX : (Nat.card X : ℝ) =
      ∑ ω : orbitRel.Quotient H X, (Nat.card (orbit H (Quotient.out ω)) : ℝ) := by
    rw [Nat.card_congr (MulAction.selfEquivSigmaOrbits H X), Nat.card_sigma]
    push_cast
    rfl
  rw [hX, Finset.sum_div]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hmul := Subgroup.card_mul_index (stabilizer H (Quotient.out ω))
  rw [MulAction.index_stabilizer, ← Nat.card_coe_set_eq] at hmul
  have hs : (0 : ℝ) < Nat.card (stabilizer H (Quotient.out ω)) := by exact_mod_cast Nat.card_pos
  haveI : Nonempty (orbit H (Quotient.out ω)) := ⟨⟨_, mem_orbit_self _⟩⟩
  have ho : (0 : ℝ) < Nat.card (orbit H (Quotient.out ω)) := by exact_mod_cast Nat.card_pos
  rw [← hmul]
  push_cast
  field_simp

theorem card_orbits_of_free (H X : Type*) [Group H] [MulAction H X] [Finite H] [Finite X]
    (hfree : ∀ x : X, stabilizer H x = ⊥) :
    (Nat.card (orbitRel.Quotient H X) : ℝ) = (Nat.card X : ℝ) / Nat.card H := by
  classical
  haveI : Fintype (orbitRel.Quotient H X) := Fintype.ofFinite _
  have h := sum_inv_card_stabilizer H X
  simp only [hfree, Subgroup.card_bot, Nat.cast_one, inv_one, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one] at h
  rw [← h, Nat.card_eq_fintype_card]

theorem card_clsRep {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) [Fintype (DoubleCoset.Quotient (Γ : Set G) K)]
    [Finite (K ⧸ U.subgroupOf K)] (hfin : ∀ c, Finite (Gam Γ K (rep c))) (htriv : ∀ x : G, Gam Γ U x = ⊥) :
    (Nat.card (DoubleCoset.Quotient (Γ : Set G) U) : ℝ) =
      ∑ c, (Nat.card (K ⧸ U.subgroupOf K) : ℝ) / Nat.card (Gam Γ K (rep c)) := by
  rw [Nat.card_congr (fibRep hUK rep hrep), Nat.card_sigma]
  push_cast
  refine Finset.sum_congr rfl fun c _ => ?_
  haveI := hfin c
  exact card_orbits_of_free _ _ (stabilizer_eq_bot hUK (rep c) (fun k => htriv _))

theorem card_clsRep_mass {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) [Fintype (DoubleCoset.Quotient (Γ : Set G) K)]
    [Finite (K ⧸ U.subgroupOf K)] (hfin : ∀ c, Finite (Gam Γ K (rep c))) (htriv : ∀ x : G, Gam Γ U x = ⊥) :
    (Nat.card (DoubleCoset.Quotient (Γ : Set G) U) : ℝ) =
      (∑ c, ((Nat.card (Gam Γ K (rep c)) : ℝ))⁻¹) * Nat.card (K ⧸ U.subgroupOf K) := by
  rw [card_clsRep hUK rep hrep hfin htriv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [div_eq_mul_inv, mul_comm]

theorem card_cls {Γ K U : Subgroup G} (hUK : U ≤ K) [Fintype (DoubleCoset.Quotient (Γ : Set G) K)]
    [Finite (K ⧸ U.subgroupOf K)] (hfin : ∀ g : G, Finite (Gam Γ K g)) (htriv : ∀ x : G, Gam Γ U x = ⊥) :
    (Nat.card (DoubleCoset.Quotient (Γ : Set G) U) : ℝ) =
      ∑ c : DoubleCoset.Quotient (Γ : Set G) K,
        (Nat.card (K ⧸ U.subgroupOf K) : ℝ) / Nat.card (Gam Γ K (Quotient.out c)) := card_clsRep hUK Quotient.out (DoubleCoset.out_eq' Γ K) (fun c => hfin _) htriv

theorem finite_cls {Γ K U : Subgroup G} (hUK : U ≤ K) [Finite (DoubleCoset.Quotient (Γ : Set G) K)]
    [Finite (K ⧸ U.subgroupOf K)] : Finite (DoubleCoset.Quotient (Γ : Set G) U) := by
  exact Finite.of_equiv _ (fib hUK).symm

theorem mass_clsRep {Γ K U : Subgroup G} (hUK : U ≤ K) (rep : DoubleCoset.Quotient (Γ : Set G) K → G)
    (hrep : ∀ c, DoubleCoset.mk Γ K (rep c) = c) [Fintype (DoubleCoset.Quotient (Γ : Set G) K)]
    [Fintype (DoubleCoset.Quotient (Γ : Set G) U)]
    [Finite (K ⧸ U.subgroupOf K)] (hfin : ∀ c, Finite (Gam Γ K (rep c))) :
    ∑ q : DoubleCoset.Quotient (Γ : Set G) U, ((Nat.card (Gam Γ U (Quotient.out q)) : ℝ))⁻¹ =
      (∑ c, ((Nat.card (Gam Γ K (rep c)) : ℝ))⁻¹) * Nat.card (K ⧸ U.subgroupOf K) := by
  classical
  haveI : ∀ c : DoubleCoset.Quotient (Γ : Set G) K,
      Fintype (orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)) := fun c => Fintype.ofFinite _
  rw [← Equiv.sum_comp (fibRep hUK rep hrep).symm, Fintype.sum_sigma, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  haveI := hfin c
  rw [inv_mul_eq_div, ← sum_inv_card_stabilizer (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have e := stabEquivCls hUK rep hrep c (Quotient.out ω)
  have hω : (Quotient.mk'' (Quotient.out ω) : orbitRel.Quotient (Gam Γ K (rep c)) (K ⧸ U.subgroupOf K)) = ω :=
    Quotient.out_eq ω
  rw [hω] at e
  rw [Nat.card_congr e.toEquiv]

open Formalism.UG in
theorem fibCount : FibCount := by
  unfold Formalism.MainNotions.Gaps.CC.FibCount
  intro G _ Γ U K hUK hidx hfinK hstab htriv s hs
  classical
  haveI : Fintype (ClassSet Γ K) := Fintype.ofFinite _
  haveI : (U.subgroupOf K).FiniteIndex := ⟨hidx⟩
  have hfin : ∀ c, Finite (Gam Γ K (s c)) := fun c =>
    @Finite.of_equiv _ _ (hstab (s c)) (GamEquivSet Γ K (s c)).symm
  have htriv' : ∀ x : G, Gam Γ U x = ⊥ := fun x =>
    Gam_eq_bot_iff.2 fun γ hγ hU => Subtype.ext_iff.1 (htriv x ⟨γ, hγ⟩ hU)
  rw [card_clsRep_mass hUK s hs hfin htriv', finsum_eq_sum_of_fintype, mul_comm]
  congr 1
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Nat.card_congr (GamEquivSet Γ K (s c))]
  rfl

end Formalism.MainNotions.Gaps.CC.Fib
