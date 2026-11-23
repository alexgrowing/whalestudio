import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalSystemQuotients.ModFSW
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.Coords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb.LsQ

open CrystallineSemistableComparison.Ls CrystallineSemistableComparison.Pb.LsG

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] [PerfectRing k l] {O : Type} [CommRing O]
  {F : B.Fn O} {ρ : O →+* k}

abbrev lI {m : ℕ} (n : ℕ) (T : Thick (Wc.L l F ρ m)) : Ideal T.B :=
  Ideal.span {T.i (Ideal.Quotient.mk _ ((l : WittVector l k) ^ n))}

theorem lI_le {n : ℕ} (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) : lI n T ≤ T.J := by
  rw [Ideal.span_le, Set.singleton_subset_iff]
  exact T.i_mem (Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton.2 (dvd_pow_self _ hn)))

private theorem exists_factorial_mul_eq_pow_pow_in_span {n j : ℕ} (hn : n ≠ 0) (hj : j ≠ 0) :
    ∃ y ∈ Ideal.span {(l : WittVector l k) ^ n},
      (j.factorial : WittVector l k) * y = ((l : WittVector l k) ^ n) ^ j := by
  have hl : l.Prime := Fact.out
  obtain ⟨e, u, hu, hfac⟩ := Nat.exists_eq_pow_mul_and_not_dvd (Nat.factorial_ne_zero j) l hl.one_lt.ne'
  have he : e < j := by
    have h1 : e ≤ padicValNat l j.factorial :=
      (padicValNat_dvd_iff_le (Nat.factorial_ne_zero j)).1 ⟨u, hfac⟩
    have h2 := sub_one_mul_padicValNat_factorial_lt_of_ne_zero l hj
    have h3 : 1 ≤ l - 1 := by
      have := hl.two_le
      omega
    have h4 : padicValNat l j.factorial ≤ (l - 1) * padicValNat l j.factorial :=
      Nat.le_mul_of_pos_left _ h3
    omega
  have hunit : IsUnit (u : WittVector l k) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    rw [← WittVector.constantCoeff_apply, map_natCast]
    intro h0
    exact hu ((CharP.cast_eq_zero_iff k l u).1 h0)
  obtain ⟨j', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  have hm1 : n * (j' + 1) = n * j' + n := by ring
  have hm2 : j' ≤ n * j' := Nat.le_mul_of_pos_left j' hnpos
  have hsum : e + (n * (j' + 1) - e - n) + n = n * (j' + 1) := by omega
  refine ⟨(↑(hunit.unit⁻¹) : WittVector l k) * (l : WittVector l k) ^ (n * (j' + 1) - e - n) *
      (l : WittVector l k) ^ n, Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _), ?_⟩
  rw [hfac, Nat.cast_mul, Nat.cast_pow]
  have hu1 : (u : WittVector l k) * ↑(hunit.unit⁻¹) = 1 := hunit.mul_val_inv
  calc (l : WittVector l k) ^ e * (u : WittVector l k) *
        ((↑(hunit.unit⁻¹) : WittVector l k) * (l : WittVector l k) ^ (n * (j' + 1) - e - n) *
          (l : WittVector l k) ^ n)
      = ((u : WittVector l k) * ↑(hunit.unit⁻¹)) * ((l : WittVector l k) ^ e *
          (l : WittVector l k) ^ (n * (j' + 1) - e - n) * (l : WittVector l k) ^ n) := by ring
    _ = (l : WittVector l k) ^ (e + (n * (j' + 1) - e - n) + n) := by
        rw [hu1, one_mul, ← pow_add, ← pow_add]
    _ = ((l : WittVector l k) ^ n) ^ (j' + 1) := by
        rw [← pow_mul, hsum]

theorem subPd {n : ℕ} (hn : n ≠ 0) (T : Thick (Wc.L l F ρ (n + 1))) : IsSubDPIdeal T.δ (lI n T ⊓ T.J) := by
  rw [inf_eq_left.2 (lI_le hn T)]
  refine (DividedPowers.span_isSubDPIdeal_iff ?_).2 ?_
  · rw [Set.singleton_subset_iff]
    exact lI_le hn T (Ideal.mem_span_singleton_self _)
  · intro j hj s hs
    rw [Set.mem_singleton_iff] at hs
    subst hs
    have hmem : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) ((l : WittVector l k) ^ n) ∈
        Wc.Im l k (n + 1) :=
      Ideal.mem_map_of_mem _ (Ideal.mem_span_singleton.2 (dvd_pow_self _ hn))
    rw [T.dpow_i j hmem]
    obtain ⟨y, hy, hyeq⟩ := exists_factorial_mul_eq_pow_pow_in_span (l := l) (k := k) hn hj
    have hpd := (CrystallineSemistableComparison.Wc.isPd l k (n + 1)).2 j ((l : WittVector l k) ^ n) y
      (Ideal.mem_span_singleton.2 (dvd_pow_self _ hn)) hyeq
    have hpd' : (Wc.bs l k (n + 1)).γ.dpow j
        (Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) ((l : WittVector l k) ^ n)) =
        Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) y := hpd
    rw [hpd']
    obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hy
    rw [map_mul, map_mul]
    exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

section Q

variable {n : ℕ} (hn : n ≠ 0)

theorem lI_mem (T : Thick (Wc.L l F ρ (n + 1))) (w : WittVector l k) (hw : w ∈ Ideal.span {(l : WittVector l k) ^ n}) :
    T.i (Ideal.Quotient.mk _ w) ∈ lI n T := by
  obtain ⟨a, rfl⟩ := Ideal.mem_span_singleton'.1 hw
  rw [map_mul, map_mul]
  exact Ideal.mul_mem_left _ _ (Ideal.mem_span_singleton_self _)

def qi (T : Thick (Wc.L l F ρ (n + 1))) : Wc.Wm l k n →+* T.B ⧸ lI n T :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk (lI n T)).comp (T.i.comp (Ideal.Quotient.mk _))) fun w hw =>
    Ideal.Quotient.eq_zero_iff_mem.2 (lI_mem T w hw)

theorem qi_mk (T : Thick (Wc.L l F ρ (n + 1))) (w : WittVector l k) :
    qi T (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ (T.i (Ideal.Quotient.mk _ w)) := rfl

omit [PerfectRing k l] [CharP k l] in
theorem red_mk' (w : WittVector l k) : Wc.red l k n (Ideal.Quotient.mk _ w) = Ideal.Quotient.mk _ w := by
  exact CrystallineSemistableComparison.Wc.red_mk l k n w

theorem qi_red (T : Thick (Wc.L l F ρ (n + 1))) (r : Wc.Wm l k (n + 1)) :
    qi T (Wc.red l k n r) = Ideal.Quotient.mk _ (T.i r) := by
  obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
  rw [red_mk', qi_mk]

def qe (T : Thick (Wc.L l F ρ (n + 1))) : T.B ⧸ T.J →+* (T.B ⧸ lI n T) ⧸ T.J.map (Ideal.Quotient.mk (lI n T)) :=
  Ideal.quotientMap _ (Ideal.Quotient.mk _) Ideal.le_comap_map

def qy (T : Thick (Wc.L l F ρ (n + 1))) :
    Wc.Wm l k n ⧸ Wc.Im l k n →+* (T.B ⧸ lI n T) ⧸ T.J.map (Ideal.Quotient.mk (lI n T)) :=
  Ideal.Quotient.lift _ ((Ideal.Quotient.mk _).comp (qi T)) fun a ha => by
    rw [RingHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem]
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
    rw [← red_mk', qi_red]
    exact Ideal.mem_map_of_mem _ (T.i_mem (Ideal.mem_map_of_mem _ hb))

theorem qy_res (T : Thick (Wc.L l F ρ (n + 1))) (c : k) :
    qy T (Wc.res l k n c) = qe T (T.y.1.1 (Wc.res l k (n + 1) c)) := by
  have hx : WittVector.constantCoeff (WittVector.teichmuller l c) = c := by
    rw [WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero]
  rw [← hx, CrystallineSemistableComparison.Wc.res_coeff, CrystallineSemistableComparison.Wc.res_coeff]
  show Ideal.Quotient.mk _ (qi T (Ideal.Quotient.mk _ (WittVector.teichmuller l c))) = _
  rw [qi_mk]
  rw [show T.y.1.1 (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (WittVector.teichmuller l c))) =
      Ideal.Quotient.mk T.J (T.i (Ideal.Quotient.mk _ (WittVector.teichmuller l c))) from T.w _]
  rfl

def qT (T : Thick (Wc.L l F ρ (n + 1))) : Thick (Wc.L l F ρ n) where
  B := T.B ⧸ lI n T
  i := qi T
  J := T.J.map (Ideal.Quotient.mk _)
  δ := DividedPowers.Quotient.dividedPowers T.δ (subPd hn T)
  adm := ⟨fun h => by
      have := (T.adm.1 h).map (Ideal.Quotient.mk (lI n T))
      rwa [map_natCast] at this,
    fun h => absurd h (Fact.out : l.Prime).ne_zero⟩
  compat := by
    refine ⟨?_, fun a ha => ?_⟩
    · rw [Ideal.map_le_iff_le_comap]
      intro a ha
      obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
      rw [Ideal.mem_comap, ← red_mk', qi_red]
      exact Ideal.mem_map_of_mem _ (T.i_mem (Ideal.mem_map_of_mem _ hb))
    · obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
      have hb' : Ideal.Quotient.mk (Ideal.span {(l : WittVector l k) ^ (n + 1)}) b ∈ Wc.Im l k (n + 1) :=
        Ideal.mem_map_of_mem _ hb
      change (DividedPowers.Quotient.dividedPowers T.δ (subPd hn T)).dpow _ (qi T _) = qi T ((Wc.pd l k n).dpow _ _)
      rw [← red_mk', (Wc.dp_red l k n).2 _ hb', qi_red, qi_red,
        DividedPowers.Quotient.dpow_apply T.δ (subPd hn T) (T.i_mem hb'), T.dpow_i _ hb']
  α := ()
  y := ⟨(qy T, F.Pt.map (CommRingCat.ofHom (qe T)) T.y.1.2), by
    have h := F.ov_map (CommRingCat.ofHom (qe T)) T.y.2
    convert h using 1
    ext c
    exact qy_res T (ρ c)⟩
  inα := trivial
  w _ := rfl
  x j := j.elim
  v j := j.elim
  s := 1
  hx j := j.elim
  hs := by
    change ∏ j : Empty, _ = _
    rw [Finset.univ_eq_empty, Finset.prod_empty]
    simp
  hv := by
    change _ = ∏ j : Empty, _
    rw [Finset.univ_eq_empty, Finset.prod_empty, map_one]

theorem lI_map {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') : lI n T ≤ (lI n T').comap f.φ := by
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, Ideal.mem_comap, f.comm]
  exact Ideal.mem_span_singleton_self _

def qφ {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') : T.B ⧸ lI n T →+* T'.B ⧸ lI n T' :=
  Ideal.quotientMap _ f.φ (lI_map f)

theorem qφ_le {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') :
    T.J.map (Ideal.Quotient.mk (lI n T)) ≤ (T'.J.map (Ideal.Quotient.mk (lI n T'))).comap (qφ f) := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  rw [Ideal.mem_comap, Ideal.mem_comap]
  exact Ideal.mem_map_of_mem _ (f.hle ha)

theorem qpt {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') :
    F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap _ (qφ f) (qφ_le f))) (F.Pt.map (CommRingCat.ofHom (qe T)) T.y.1.2) =
      F.Pt.map (CommRingCat.ofHom (qe T')) T'.y.1.2 := by
  have hpt : F.Pt.map (CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle)) T.y.1.2 = T'.y.1.2 :=
    congrArg (fun z => z.1.2) f.pt
  have hcomp : CommRingCat.ofHom (qe T) ≫ CommRingCat.ofHom (Ideal.quotientMap _ (qφ f) (qφ_le f)) =
      CommRingCat.ofHom (Ideal.quotientMap T'.J f.φ f.hle) ≫ CommRingCat.ofHom (qe T') :=
    CommRingCat.hom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun b => rfl))
  rw [← hpt, ← FunctorToTypes.map_comp_apply, ← FunctorToTypes.map_comp_apply, hcomp]

def qmap {T T' : Thick (Wc.L l F ρ (n + 1))} (f : T ⟶ T') : qT hn T ⟶ qT hn T' where
  φ := qφ f
  u j := j.elim
  comm r := by
    obtain ⟨w, rfl⟩ := Ideal.Quotient.mk_surjective r
    change Ideal.Quotient.mk _ (f.φ (T.i _)) = Ideal.Quotient.mk _ (T'.i _)
    rw [f.comm]
  dp := ⟨Ideal.map_le_iff_le_comap.2 (qφ_le f), fun a ha => by
    obtain ⟨b, hb, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 ha
    change (DividedPowers.Quotient.dividedPowers T'.δ (subPd hn T')).dpow _ (Ideal.Quotient.mk _ (f.φ b)) =
      qφ f ((DividedPowers.Quotient.dividedPowers T.δ (subPd hn T)).dpow _ (Ideal.Quotient.mk _ b))
    rw [DividedPowers.Quotient.dpow_apply _ _ hb, DividedPowers.Quotient.dpow_apply _ _ (show f.φ b ∈ T'.J from f.hle hb), f.dp.2 b hb]
    rfl⟩
  hle := qφ_le f
  pt := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · refine Ideal.Quotient.ringHom_ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun w => ?_))
      change Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (f.φ (T.i _))) = Ideal.Quotient.mk _ (Ideal.Quotient.mk _ (T'.i _))
      rw [f.comm]
    · exact qpt f
  hx j := j.elim
  hs := by
    change (1 : (T'.B ⧸ lI n T')ˣ) = (∏ j : Empty, _) * Units.map (qφ f).toMonoidHom 1
    rw [Finset.univ_eq_empty, Finset.prod_empty, map_one, one_mul]
  hv j := j.elim

def qF : Thick (Wc.L l F ρ (n + 1)) ⥤ Thick (Wc.L l F ρ n) where
  obj := qT hn
  map := qmap hn
  map_id _ := Thick.Hom.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) (funext fun j => j.elim)
  map_comp _ _ := Thick.Hom.ext (Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)) (funext fun j => j.elim)

end Q

section Cmp

variable {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (A : C ⥤ CommAlgCat.{0} R) (l n : ℕ)

def qM : CH.Mor (CH.modF A) (sq (IdF.top A) (IdF.span A ((l : R) ^ n))) (RingHom.id R) where
  G := 𝟭 C
  τ T := { toFun := fun x => sqMk (IdF.top A) (IdF.span A ((l : R) ^ n)) (show A.obj T from x) trivial
           map_add' := fun x y => Subtype.ext (map_add (Ideal.Quotient.mk _) (show A.obj T from x) y)
           map_smul' := fun r x => Subtype.ext (by
             change Ideal.Quotient.mkₐ R _ (r • (show A.obj T from x)) = r • Ideal.Quotient.mkₐ R _ (show A.obj T from x)
             rw [map_smul]) }
  nat _ _ := rfl

def cmpq : Cx.Hom (quo l (CH.cx (CH.modF A)) n) (CH.cx (sq (IdF.top A) (IdF.span A ((l : R) ^ n)))) (RingHom.id R) where
  f i := Submodule.liftQ _ ((qM A l n).pullC i) (by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker]
    funext s
    refine Subtype.ext (Ideal.Quotient.eq_zero_iff_mem.2 ?_)
    change (((l : R) ^ n) • (show A.obj _ from y (s ⋙ 𝟭 C))) ∈ Ideal.span _
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
  comm i x := by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    exact (qM A l n).d_pullC i y

theorem cmpq_mk (i : ℕ) (y : CH.Cn (CH.modF A) i) :
    (cmpq A l n).f i (Submodule.Quotient.mk y) = (qM A l n).pullC i y := rfl

end Cmp

end CrystallineSemistableComparison.Pb.LsQ

end
