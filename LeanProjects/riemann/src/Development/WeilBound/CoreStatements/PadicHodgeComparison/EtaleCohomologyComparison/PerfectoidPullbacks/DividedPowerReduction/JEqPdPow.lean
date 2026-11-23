import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.ZariskiEtaleLifting.SubThickRees
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.GrSplit
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SheafFiltrationProperty

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

variable {O : Type} [CommRing O] {A : Type} [CommRing A] [Algebra O A] {I : Ideal A} {γ : DividedPowers I}
  {R : Type} [CommRing R] {I' : Ideal R} {γ' : DividedPowers I'} {κ' : O →+* R ⧸ I'} {l n : ℕ}

structure RedIn (γ' : DividedPowers I') (κ' : O →+* R ⧸ I') (γ : DividedPowers I) (l n : ℕ) where
  hl : l ≠ 0
  ρ : R →+* A ⧸ Ideal.span {(l : A) ^ n}
  mem : ∀ x ∈ I', ∃ y ∈ I, ρ x = Ideal.Quotient.mk _ y
  dp : ∀ (k : ℕ), ∀ x ∈ I', ∀ y ∈ I, ρ x = Ideal.Quotient.mk _ y → ρ (γ'.dpow k x) = Ideal.Quotient.mk _ (γ.dpow k y)
  hκ : ∀ (a : O) (r : R), κ' a = Ideal.Quotient.mk _ r → ∃ y ∈ I, ρ r = Ideal.Quotient.mk _ (algebraMap O A a + y)

variable {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of O)} {s : ℕ}

section Obj
variable (T : Thick (nlFun γ 0 X q (κA O I)))

abbrev lnT (l n : ℕ) : Ideal T.B := Ideal.span {(l : T.B) ^ n}

theorem J_eq_pdPow : T.J = T.pdPow 1 := ((GlobalTheory.CompanionTheory.DPFil.isFil_sFil (⊤ : ObjectProperty _)).one ⟨T, trivial⟩).symm

theorem subDP (h : TF l s T) (n : ℕ) : IsSubDPIdeal T.δ (lnT T l n ⊓ T.J) := by
  refine ⟨inf_le_right, fun k hk x ⟨hxl, hx⟩ => ⟨?_, T.δ.dpow_mem hk hx⟩⟩
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton'.1 hxl
  have hy : ∀ (m : ℕ) (y : T.B), y * (l : T.B) ^ m ∈ T.J → y ∈ T.J := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro y hy
      refine ih y ?_
      rw [J_eq_pdPow] at hy ⊢
      exact h.2 1 _ (by rwa [pow_succ, ← mul_assoc, mul_comm] at hy)
  rw [mul_comm, T.δ.dpow_mul (hy n y hx)]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self _) _ (Nat.pos_of_ne_zero hk))

def redδ (h : TF l s T) (n : ℕ) : DividedPowers (T.J.map (Ideal.Quotient.mk (lnT T l n))) :=
  DividedPowers.Quotient.dividedPowers T.δ (subDP T h n)

theorem redδ_dp (h : TF l s T) (n : ℕ) : IsDPMorphism T.δ (redδ T h n) (Ideal.Quotient.mk (lnT T l n)) :=
  DividedPowers.Quotient.isDPMorphism T.δ (subDP T h n)

def iBar (l n : ℕ) : A ⧸ Ideal.span {(l : A) ^ n} →+* T.B ⧸ lnT T l n :=
  Ideal.quotientMap _ T.i (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton_self _)

def qBar (l n : ℕ) : T.B ⧸ T.J →+* (T.B ⧸ lnT T l n) ⧸ T.J.map (Ideal.Quotient.mk (lnT T l n)) :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) Ideal.le_comap_map

variable (d : RedIn γ' κ' γ l n)

theorem red_compat (h : TF l s T) : IsDPMorphism γ' (redδ T h n) ((iBar T l n).comp d.ρ) := by
  refine ⟨Ideal.map_le_iff_le_comap.2 fun x hx => ?_, fun {k} x hx => ?_⟩
  · obtain ⟨y, hy, e⟩ := d.mem x hx
    change iBar T l n (d.ρ x) ∈ T.J.map (Ideal.Quotient.mk (lnT T l n))
    rw [e]
    exact Ideal.mem_map_of_mem _ (T.i_mem hy)
  · obtain ⟨y, hy, e⟩ := d.mem x hx
    change (redδ T h n).dpow k (iBar T l n (d.ρ x)) = iBar T l n (d.ρ _)
    rw [d.dp k x hx y hy e, e]
    exact ((redδ_dp T h n).2 _ (T.i_mem hy)).trans (congrArg _ (T.dpow_i k hy))

def ψBar (h : TF l s T) : R ⧸ I' →+* (T.B ⧸ lnT T l n) ⧸ T.J.map (Ideal.Quotient.mk (lnT T l n)) :=
  Ideal.quotientMap _ ((iBar T l n).comp d.ρ) (Ideal.map_le_iff_le_comap.1 (red_compat T d h).1)

theorem ψBar_κ (h : TF l s T) : (ψBar T d h).comp κ' = (qBar T l n).comp ((show PtOver X q _ _ from T.y).1.1.comp (κA O I)) := by
  ext a
  obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (κ' a)
  obtain ⟨y, hy, e⟩ := d.hκ a r hr.symm
  have h1 : (show PtOver X q _ _ from T.y).1.1 (κA O I a) = Ideal.Quotient.mk T.J (T.i (algebraMap O A a)) := T.w _
  rw [RingHom.comp_apply, ← hr, RingHom.comp_apply, RingHom.comp_apply, h1]
  change Ideal.Quotient.mk _ (iBar T l n (d.ρ r)) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ _)
  rw [e]
  refine Ideal.Quotient.eq.2 ?_
  change Ideal.Quotient.mk _ (T.i _) - _ ∈ _
  rw [← map_sub, map_add, add_sub_cancel_left]
  exact Ideal.mem_map_of_mem _ (T.i_mem hy)

def redObj (h : TF l s T) : Thick (nlFun γ' l X q κ') :=
  mkT (T.B ⧸ lnT T l n) ((iBar T l n).comp d.ρ) (T.J.map (Ideal.Quotient.mk _)) (redδ T h n)
    ⟨fun _ => ⟨n, by
      rw [← map_natCast (Ideal.Quotient.mk (lnT T l n)), ← map_pow, Ideal.Quotient.eq_zero_iff_mem]
      exact Ideal.mem_span_singleton_self _⟩, fun h0 => absurd h0 d.hl⟩
    (red_compat T d h)
    ⟨(ψBar T d h, Spec.map (CommRingCat.ofHom (qBar T l n)) ≫ pt T), by
      have h2 : pt T ≫ q = _ := (show PtOver X q _ _ from T.y).2
      rw [Category.assoc, h2, ← Spec.map_comp, ψBar_κ]; rfl⟩
    fun _ => rfl

end Obj

def lnMap {B B' : Type} [CommRing B] [CommRing B'] (φ : B →+* B') (l : ℕ) {n m : ℕ} (h : m ≤ n) :
    B ⧸ Ideal.span {(l : B) ^ n} →+* B' ⧸ Ideal.span {(l : B') ^ m} :=
  Ideal.quotientMap _ φ (by
    rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, map_pow, map_natCast]
    exact Ideal.mem_span_singleton.2 (pow_dvd_pow _ h))

variable (d : RedIn γ' κ' γ l n)

theorem red_dp {T T' : Thick (nlFun γ 0 X q (κA O I))} (h : TF l s T) (h' : TF l s T') (f : T ⟶ T') :
    IsDPMorphism (redδ T h n) (redδ T' h' n) (lnMap f.φ l le_rfl) := by
  refine ⟨Ideal.map_le_iff_le_comap.2 (Ideal.map_le_iff_le_comap.2 fun x hx => Ideal.mem_map_of_mem (Ideal.Quotient.mk _) (f.hle hx)),
    fun {k} x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hx
  rw [(redδ_dp T h n).2 y hy]
  exact ((redδ_dp T' h' n).2 _ (f.hle hy)).trans (congrArg _ (f.dp.2 y hy))

def redHom {T T' : Thick (nlFun γ 0 X q (κA O I))} (h : TF l s T) (h' : TF l s T') (f : T ⟶ T') : redObj T d h ⟶ redObj T' d h' :=
  mkH (lnMap f.φ l le_rfl) (fun r => by
      obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d.ρ r)
      change lnMap f.φ l le_rfl (iBar T l n (d.ρ r)) = iBar T' l n (d.ρ r)
      rw [← ha]
      exact congrArg (Ideal.Quotient.mk _) (f.comm a))
    (red_dp h h' f) (Ideal.map_le_iff_le_comap.1 (red_dp h h' f).1) (by
      refine Subtype.ext (Prod.ext ?_ ?_)
      · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun r => ?_)
        obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (d.ρ r)
        change Ideal.Quotient.mk _ (lnMap f.φ l le_rfl (iBar T l n (d.ρ r))) = Ideal.Quotient.mk _ (iBar T' l n (d.ρ r))
        rw [← ha]
        exact congrArg (fun z => Ideal.Quotient.mk _ (Ideal.Quotient.mk _ z)) (f.comm a)
      · have e : pt T' = Spec.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) ≫ pt T :=
          (congrArg (fun z : PtOver X q _ _ => z.1.2) f.pt).symm
        change Spec.map _ ≫ Spec.map _ ≫ pt T = Spec.map _ ≫ pt T'
        rw [e, ← Category.assoc, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
        congr 2
        exact CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)))

variable (q s) (𝒱 : Set X.Opens)

def redG : (TS γ q l s 𝒱).FullSubcategory ⥤ Thick (nlFun γ' l X q κ') where
  obj T := redObj T.obj d T.property.1
  map {T T'} f := redHom d T.property.1 T'.property.1 f.hom
  map_id T := hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))
  map_comp f g := hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl))

theorem ln_le (r : Option ℤ) (T : (TS γ q l s 𝒱).FullSubcategory) : lnT T.obj l n ≤ (stdI (TS γ q l s 𝒱) r ((l : A) ^ n)).S T :=
  le_trans (Ideal.span_singleton_le_span_singleton.2 (dvd_of_eq (show T.obj.i ((l : A) ^ n) = _ by rw [map_pow, map_natCast])))
    le_sup_right

variable {Λ : Type} [CommRing Λ] (c : Λ →+* R) (lam : Λ →+* A) (hc : ∀ a, d.ρ (c a) = Ideal.Quotient.mk _ (lam a))

def redMor (r : Option ℤ) :
    CH.Mor (B.OM (nlFun γ' l X q κ') c) (sq (IdF.top (sP (TS γ q l s 𝒱)).A) (stdI (TS γ q l s 𝒱) r ((l : A) ^ n))) lam where
  G := redG q s d 𝒱
  τ T :=
    { toFun := fun x => ⟨Ideal.Quotient.factor (ln_le q s 𝒱 r T) x, by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
        exact Ideal.mem_map_of_mem _ trivial⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun a x => Subtype.ext (by
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT T.obj l n) x
        change Ideal.Quotient.factor (ln_le q s 𝒱 r T) (iBar T.obj l n (d.ρ (c a)) * Ideal.Quotient.mk _ y) = _
        rw [hc]; rfl) }
  nat φ x := by
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective (I := lnT _ l n) x
    rfl

end CrystallineSemistableComparison.Pb
