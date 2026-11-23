import Development.WeilBound.CoreStatements.SesquilinearFractions.GOntoA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder

set_option maxHeartbeats 100000

noncomputable section

namespace PositivityTheory.Xgf.OntoKer

def trHom {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) : (Over.mk a ⟶ G) ≃* (Over.mk b ⟶ G) where
  toFun x := (Over.homMk (𝟙 X) (by simp [h]) : Over.mk b ⟶ Over.mk a) ≫ x
  invFun y := (Over.homMk (𝟙 X) (by simp [h]) : Over.mk a ⟶ Over.mk b) ≫ y
  left_inv x := Over.OverMorphism.ext (by simp)
  right_inv y := Over.OverMorphism.ext (by simp)
  map_mul' x y := MonObj.comp_mul _ x y

theorem trHom_left {S X : Scheme.{0}} {G : Over S} [GrpObj G] {a b : X ⟶ S} (h : a = b) (x : Over.mk a ⟶ G) :
    (trHom h x).left = x.left := by
  show ((Over.homMk (𝟙 X) (by simp [h]) : Over.mk b ⟶ Over.mk a) ≫ x).left = x.left
  simp

theorem map_sum_prod {V M : Type} [AddCommGroup V] [Group M] (e : V → M) (he : ∀ z w, e (z + w) = e z * e w) {n : ℕ}
    (v : Fin n → V) : e (∑ k, v k) = (List.ofFn fun k => e (v k)).prod := by
  let F : Multiplicative V →* M := MonoidHom.mk' (fun z => e z.toAdd) fun z w => he _ _
  have := map_list_prod F (List.ofFn fun k => Multiplicative.ofAdd (v k))
  rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
  exact this

theorem pushHom_bij {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') : Function.Bijective (pushHom h T) :=
  ⟨fun x y e => Over.OverMorphism.ext (h.1.hom_ext (congrArg (fun z => z.left) e) (by rw [Over.w, Over.w])),
    fun y => ⟨Over.homMk (h.1.lift y.left T.hom (Over.w y)) (h.1.lift_snd _ _ _),
      Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩⟩

section Main

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty} {i : Fin FU.n}
  {Z : ∀ b : Bool, Curve0 H (sgnRt H b)} {P : (FU.Di i).La →+ (Fin g → ℂ)} {hP : IsPeriod (FU.Di i) ty P}
  (X : CMPack Z c FU i hP)

abbrev sC : Sp ℂ ⟶ Sp (𝓞 X.K) := spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))

abbrev TK : Over (Sp X.K) := Over.mk (spMap (algebraMap X.K ℂ))

theorem hs : (TK X).hom ≫ spMap (algebraMap (𝓞 X.K) X.K) = sC X := GlobalTheory.spMap_comp_spMap _ _

def Φ : (TK X ⟶ X.t.G) →* (Over.mk (sC X) ⟶ X.B.t.G) :=
  (trHom (hs X)).toMonoidHom.comp (pushHom X.m'.cart (TK X))

def Ψ : (TK X ⟶ X.t.G) →* (Over.mk (FU.u i P) ⟶ Xo.univ.t.G) :=
  (trHom X.pt).toMonoidHom.comp (pushHom X.m.cart (TK X))

theorem Φ_left (x : TK X ⟶ X.t.G) : (Φ X x).left = x.left ≫ X.m'.φ :=
  trHom_left (hs X) (pushHom X.m'.cart (TK X) x)

theorem Ψ_left (x : TK X ⟶ X.t.G) : (Ψ X x).left = x.left ≫ X.m.φ :=
  trHom_left X.pt (pushHom X.m.cart (TK X) x)

theorem Φ_bij : Function.Bijective (Φ X) :=
  (MulEquiv.bijective (trHom (hs X))).comp (pushHom_bij X.m'.cart (TK X))

theorem Ψ_inj : Function.Injective (Ψ X) :=
  (MulEquiv.injective (trHom X.pt)).comp (pushHom_bij X.m.cart (TK X)).1

theorem hw (b : Bool) (w : Fin (Z b).C'.P.g → ℂ) :
    ((Z b).u.ex w).left ≫ X.π b ≫ (X.C b).P.A.hom = sC X := by
  rw [(X.map' b).2.1.2.1.1.w, ← Category.assoc, Over.w ((Z b).u.ex w)]
  simp

def qC (b : Bool) (z : ℂ) : Over.mk (sC X) ⟶ (X.C b).P.A :=
  Over.homMk (((Z b).u.ex (fun _ => (Z b).c * z)).left ≫ X.π b) (by rw [Category.assoc]; exact hw X b _)

theorem tie_pt (b : Bool) (a : PureType.lat hP (sgnRt H b)) (z : ℂ) (x : TK X ⟶ X.t.G)
    (hx : Φ X x = qC X b z ≫ X.ψ b a) : Ψ X x = FU.ex i P (z • P a) := by
  refine Over.OverMorphism.ext ?_
  rw [Ψ_left]
  refine X.tie b a z x.left (Over.w x) ?_
  have e := congrArg (fun q => q.left) hx
  simp only [Φ_left, Over.comp_left, qC, Over.homMk_left] at e
  rw [e, Category.assoc]

theorem onto (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (hN0 : 0 < N)
    (hN : ∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La)))
    (y : Over.mk (sC X) ⟶ X.B.t.G) :
    ∃ x : ∀ k, Over.mk (sC X) ⟶ (X.C (b k)).P.A, y = (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod := by
  obtain ⟨x0, rfl⟩ := (Φ_bij X).2 y
  obtain ⟨z0, hz0⟩ := FU.ex_onto i P hP (Ψ X x0)
  obtain ⟨cc, hcc⟩ := exists_coeffs hP b a N hN0 hN z0
  choose xk hxk using fun k => (Φ_bij X).2 (qC X (b k) (cc k) ≫ X.ψ (b k) (a k))
  refine ⟨fun k => qC X (b k) (cc k), ?_⟩
  have e1 : x0 = (List.ofFn xk).prod := by
    apply Ψ_inj X
    rw [map_list_prod, List.map_ofFn, ← hz0, hcc, map_sum_prod (FU.ex i P) (FU.ex_add i P hP)]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    exact (tie_pt X (b k) (a k) (cc k) (xk k) (hxk k)).symm
  rw [e1, map_list_prod, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.2 (funext hxk)

def quadRing : Subring ℂ where
  carrier := {z | ∃ m n : ℤ, z = m + n * ((1 + Complex.I * Real.sqrt H.d) / 2)}
  mul_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    have hd := H.d_mod
    obtain ⟨e, he⟩ : ∃ e : ℕ, 1 + H.d = 4 * e := ⟨(1 + H.d) / 4, by omega⟩
    have hs : (Real.sqrt H.d : ℂ) ^ 2 = H.d := by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
    refine ⟨m * m' - n * n' * e, m * n' + m' * n + n * n', ?_⟩
    have he' : (1 : ℂ) + H.d = 4 * e := by exact_mod_cast he
    push_cast
    have hI : Complex.I ^ 2 = -1 := Complex.I_sq
    linear_combination (n * n' : ℂ) * (Complex.I ^ 2 / 4 * hs + (H.d : ℂ) / 4 * hI - 1 / 4 * he')
  one_mem' := ⟨1, 0, by simp⟩
  add_mem' := by
    rintro _ _ ⟨m, n, rfl⟩ ⟨m', n', rfl⟩
    exact ⟨m + m', n + n', by push_cast; ring⟩
  zero_mem' := ⟨0, 0, by simp⟩
  neg_mem' := by
    rintro _ ⟨m, n, rfl⟩
    exact ⟨-m, -n, by push_cast; ring⟩

theorem sq_rt {ρ : ℂ} (h : ρ ^ 2 = -(H.d : ℂ)) : ρ = Complex.I * Real.sqrt H.d ∨ ρ = -(Complex.I * Real.sqrt H.d) := by
  have hs : (Complex.I * Real.sqrt H.d) ^ 2 = -(H.d : ℂ) := by
    rw [mul_pow, Complex.I_sq, ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; simp
  exact sq_eq_sq_iff_eq_or_eq_neg.1 (h.trans hs.symm)

theorem half_mem (b : Bool) : (1 + sgnRt H b) / 2 ∈ quadRing (H := H) := by
  have h0 : (sgnRt H b) ^ 2 = -(H.d : ℂ) := by
    unfold sgnRt; split_ifs <;> simp [H.sqrt_neg_disc_sq]
  rcases sq_rt (H := H) h0 with h | h
  · exact ⟨0, 1, by rw [h]; simp⟩
  · exact ⟨1, -1, by rw [h]; push_cast; ring⟩

theorem kap_mem (b : Bool) (α : OK H) : kap ty H b α ∈ quadRing (H := H) := by
  unfold kap
  split_ifs with h
  · set j := h.choose
    have hj : ty j (H.rt : E) = sgnRt H b := h.choose_spec
    let f : 𝓞 E →+* ℂ := (ty j).comp (algebraMap (𝓞 E) E)
    have hw : f H.w0 = (1 + sgnRt H b) / 2 := by
      have e := congrArg f H.two_weight_eq_one_add_root
      simp only [map_mul, map_add, map_one, map_ofNat] at e
      have : f H.rt = sgnRt H b := hj
      rw [this] at e
      field_simp
      linear_combination e
    have hle : OK H ≤ (subalgebraOfSubring (quadRing (H := H))).comap f.toIntAlgHom := by
      rw [OK, Algebra.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      show f H.w0 ∈ quadRing (H := H)
      rw [hw]
      exact half_mem b
    exact hle α.2
  · exact (quadRing (H := H)).zero_mem

theorem hπ (b : Bool) : IsGrpPullback (Z b).C'.P.A (X.C b).P.A (sC X) (X.π b) := (X.map' b).2.1.2.1

theorem h1 : (𝟙_ (Over (Sp ℂ))).hom ≫ sC X = sC X := by simp

theorem qC_eq (b : Bool) (z : ℂ) :
    qC X b z = trHom (h1 X) (pushHom (hπ X b) (𝟙_ (Over (Sp ℂ))) ((Z b).u.ex (fun _ => (Z b).c * z))) := by
  refine Over.OverMorphism.ext ?_
  rw [trHom_left]
  rfl

theorem qC_add (b : Bool) (z z' : ℂ) : qC X b (z + z') = qC X b z * qC X b z' := by
  rw [qC_eq, qC_eq, qC_eq, ← map_mul, ← map_mul, ← (Z b).u.ex_add]
  congr 3
  funext _
  simp only [Pi.add_apply]
  ring

theorem qC_zero (b : Bool) : qC X b 0 = 1 := by
  have := qC_add X b 0 0
  rw [add_zero] at this
  exact (mul_eq_left.1 this.symm)

theorem qC_npow (b : Bool) (z : ℂ) : ∀ n : ℕ, qC X b ((n : ℂ) * z) = qC X b z ^ n
  | 0 => by simp [qC_zero]
  | n + 1 => by
    rw [pow_succ, ← qC_npow b z n, ← qC_add]
    congr 1
    push_cast
    ring

theorem qC_one_of (b : Bool) (z : ℂ) (h : (fun _ => (Z b).c * z) ∈ (Z b).u.Λ) : qC X b z = 1 := by
  rw [qC_eq, ((Z b).u.ker _).2 h, map_one, map_one]

theorem qC_onto (b : Bool) (x : Over.mk (sC X) ⟶ (X.C b).P.A) : ∃ z, x = qC X b z := by
  obtain ⟨w', hw'⟩ := (pushHom_bij (hπ X b) (𝟙_ (Over (Sp ℂ)))).2 ((trHom (h1 X)).symm x)
  obtain ⟨w, rfl⟩ := (Z b).u.ex_onto w'
  have hg : (Z b).C'.P.g = 1 := (Z b).C'.dim
  let j0 : Fin (Z b).C'.P.g := ⟨0, by rw [hg]; exact Nat.one_pos⟩
  refine ⟨w j0 / (Z b).c, ?_⟩
  have hw : (fun _ => (Z b).c * (w j0 / (Z b).c)) = w := by
    funext j
    have : j = j0 := Fin.ext (by have h2 : j.1 < 1 := hg ▸ j.2; show j.1 = 0; omega)
    rw [this, mul_div_cancel₀ _ (Z b).c_ne]
  rw [qC_eq, hw, hw', MulEquiv.apply_symm_apply]

theorem ker_pow (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))) (hN0 : 0 < N)
    (hN : ∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La)))
    (x : ∀ k, Over.mk (sC X) ⟶ (X.C (b k)).P.A) (hx : (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod = 1) :
    ∀ k, x k ^ N = 1 := by
  choose sk hsk using fun k => qC_onto X (b k) (x k)
  choose xk hxk using fun k => (Φ_bij X).2 (x k ≫ X.ψ (b k) (a k))
  have e1 : (List.ofFn xk).prod = 1 := by
    apply (Φ_bij X).1
    rw [map_list_prod, List.map_ofFn, map_one, ← hx]
    congr 1
    exact List.ofFn_inj.2 (funext hxk)
  have e2 : FU.ex i P (∑ k, sk k • P (a k)) = 1 := by
    rw [map_sum_prod (FU.ex i P) (FU.ex_add i P hP), ← map_one (Ψ X), ← e1, map_list_prod, List.map_ofFn]
    congr 1
    refine List.ofFn_inj.2 (funext fun k => ?_)
    exact (tie_pt X (b k) (a k) (sk k) (xk k) (by rw [hxk k, hsk k])).symm
  obtain ⟨y, hy⟩ := (FU.ex_ker i P hP _).1 e2
  obtain ⟨α, hα⟩ := coeff_of_period hP b a N hN0 hN sk y hy.symm
  intro k
  rw [hsk k, ← qC_npow, hα k]
  obtain ⟨m, n, hmn⟩ := kap_mem (ty := ty) (b k) (α k)
  exact qC_one_of X (b k) _ (((Z (b k)).lat _).2 ⟨m, n, by rw [hmn]⟩)

end Main

end PositivityTheory.Xgf.OntoKer

open PositivityTheory.Xgf.OntoKer in
theorem PositivityTheory.Xgf.cm_pack_torsion_points : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (X : CMPack Z c FU i hP) (N : ℕ) (b : Fin g → Bool) (a : ∀ k, PureType.lat hP (sgnRt H (b k))), 0 < N → (∀ y : (FU.Di i).La, N • y ∈ Submodule.span (OK H) (Set.range fun k => (a k : (FU.Di i).La))) → (∀ y : Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ X.B.t.G, ∃ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, y = (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod) ∧ ∀ x : ∀ k, Over.mk (spMap ((algebraMap X.K ℂ).comp (algebraMap (𝓞 X.K) X.K))) ⟶ (X.C (b k)).P.A, (List.ofFn fun k => x k ≫ X.ψ (b k) (a k)).prod = 1 → ∀ k, x k ^ N = 1 := by
  intro E _ _ _ H D l Xo c g ty FU i Z P hP X N b a hN0 hN
  exact ⟨onto X N b a hN0 hN, ker_pow X N b a hN0 hN⟩

end
