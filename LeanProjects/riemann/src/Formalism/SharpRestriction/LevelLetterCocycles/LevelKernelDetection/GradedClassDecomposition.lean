import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.LevBMemFil
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.KerEqOfSpan

noncomputable section

namespace Formalism.MainNotions.N.Ln03.K8

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G TensorProduct

section Gr

variable {LL D : Type} [Field LL] [AddCommGroup D] [Module LL D]

def singleCoeffElement (F : ℤ → Submodule LL D) (k : ℤ) (w : D) (hw : w ∈ F (-k)) :
    ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) :=
  ⟨Pi.single k w, Submodule.mem_pi.2 fun j _ => by
    by_cases hj : j = k
    · subst hj
      simpa using hw
    · rw [Pi.single_eq_of_ne hj]
      exact zero_mem _⟩

def singleCoeffClass (F : ℤ → Submodule LL D) (k : ℤ) (w : D) (hw : w ∈ F (-k)) : GrQ F :=
  Submodule.Quotient.mk (singleCoeffElement F k w hw)

theorem graded_class_decomposition (F : ℤ → Submodule LL D)
    (g : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k))) (a b : ℤ)
    (ha : ∀ j < a, (g : ℤ → D) j ∈ F (1 - j)) (hb : ∀ j ≥ b, (g : ℤ → D) j ∈ F (1 - j)) :
    (Submodule.Quotient.mk g : GrQ F) =
      ∑ j ∈ Finset.Ico a b, singleCoeffClass F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)) := by
  have e : ∑ j ∈ Finset.Ico a b, singleCoeffClass F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)) =
      Submodule.mkQ _ (∑ j ∈ Finset.Ico a b,
        singleCoeffElement F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j))) := by
    rw [map_sum]
    rfl
  rw [e, Submodule.mkQ_apply, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_pi]
  intro i _
  have e2 : ((Submodule.pi Set.univ fun k : ℤ => F (-k)).subtype (g - ∑ j ∈ Finset.Ico a b,
      singleCoeffElement F j ((g : ℤ → D) j) (Submodule.mem_pi.1 g.2 j (Set.mem_univ j)))) i =
      (g : ℤ → D) i - ∑ j ∈ Finset.Ico a b, (Pi.single j ((g : ℤ → D) j) : ℤ → D) i := by
    simp only [Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_sum, Pi.sub_apply, Finset.sum_apply]
    rfl
  rw [e2, Finset.sum_pi_single]
  by_cases hi : i ∈ Finset.Ico a b
  · rw [if_pos hi, sub_self]
    exact zero_mem _
  · rw [if_neg hi, sub_zero]
    rw [Finset.mem_Ico, not_and_or, not_le, not_lt] at hi
    rcases hi with hi | hi
    · exact ha i hi
    · exact hb i hi

end Gr

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {Lb : LevB W} {hR : Ring9 W} {uZ : ℤ_[PD.p]ˣ} {ιZ : ℤ_[PD.p] →+* O}
    {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n}

def classAtRoot (c : ZMod n) (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (ζ : Rs LL PD.p s) : ↥(W.N T) →+ GrQ (FilD W T c s) where
  toFun x := Submodule.Quotient.mk
    ⟨fun k => (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c), fun k _ => levB_mem_fil hP4 hcrys hLb s ζ x k⟩
  map_zero' := by
    rw [← Submodule.Quotient.mk_zero]
    congr 1
    apply Subtype.ext
    funext k
    apply Subtype.ext
    simp
  map_add' x y := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    apply Subtype.ext
    funext k
    apply Subtype.ext
    simp

theorem classes_span_top (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s) :
    Submodule.span LL (Set.range (classAtRoot c hP4 hcrys hLb s ζ)) = ⊤ := by
  set F := FilD W T c s with hFdef
  set U := Submodule.span LL (Set.range (classAtRoot c hP4 hcrys hLb s ζ)) with hU
  obtain ⟨hanti, ⟨lo, hlo⟩, ⟨hi, hhi⟩⟩ := hfilt
  have hprim : IsPrimitiveRoot (ζ : LL) (PD.p ^ (s + 1)) :=
    (mem_primitiveRoots (pow_pos PD.hp.pos _)).1 ζ.2
  have htop : ∀ j : ℤ, 1 - lo ≤ j → F (1 - j) = ⊤ := by
    intro j hj
    exact eq_top_iff.2 (hlo ▸ hanti (by omega))
  have hbot : ∀ j : ℤ, j < -hi → F (-j) = ⊥ := by
    intro j hj
    exact eq_bot_iff.2 (hhi ▸ hanti (by omega))

  have hsingle : ∀ (m : ℕ) (k : ℤ), (1 - lo - k).toNat = m → ∀ (w : Dc W T c) (hw : w ∈ F (-k)),
      singleCoeffClass F k w hw ∈ U := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
    intro k hk w hw
    by_cases hK : 1 - lo ≤ k
    · have h0 : singleCoeffClass F k w hw = 0 := by
        unfold singleCoeffClass
        rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap, Submodule.mem_pi]
        intro j _
        show (Pi.single k w : ℤ → Dc W T c) j ∈ F (1 - j)
        by_cases hj : j = k
        · subst hj
          rw [htop j hK]
          exact Submodule.mem_top
        · rw [Pi.single_eq_of_ne hj]
          exact zero_mem _
      rw [h0]
      exact zero_mem _
    · rw [not_le] at hK
      obtain ⟨x, a, ha0, hlow, hk0⟩ := (hP4 T hcrys c s ζ hprim).2 k
        (ιV PD (LL := LL) (V := T.V) (w : T.V ⊗[Qp] B)) hw
      let gx : ↥(Submodule.pi Set.univ fun k : ℤ => F (-k)) :=
        ⟨fun k => (⟨Lb.levB T c ζ x k, Lb.mem T c ζ x k⟩ : Dc W T c),
          fun k _ => levB_mem_fil hP4 hcrys hLb s ζ x k⟩
      let h := a • gx - singleCoeffElement F k w hw
      have hcls : (Submodule.Quotient.mk h : GrQ F) =
          a • classAtRoot c hP4 hcrys hLb s ζ x - singleCoeffClass F k w hw := by
        rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_smul]
        rfl
      have hval : ∀ j, ((h : ℤ → Dc W T c) j : T.V ⊗[Qp] B) =
          a • Lb.levB T c ζ x j - ((Pi.single k w : ℤ → Dc W T c) j : T.V ⊗[Qp] B) := by
        intro j
        rfl
      have hlowh : ∀ j < k + 1, (h : ℤ → Dc W T c) j ∈ F (1 - j) := by
        intro j hj
        show ιV PD (LL := LL) (V := T.V) (((h : ℤ → Dc W T c) j : T.V ⊗[Qp] B)) ∈ FilLev W T c s (1 - j)
        rw [hval, map_sub, map_smul, ← hLb]
        by_cases hjk : j = k
        · subst hjk
          rw [Pi.single_eq_same, ← neg_add_eq_sub]
          exact hk0
        · rw [Pi.single_eq_of_ne hjk, ZeroMemClass.coe_zero, map_zero, sub_zero, ← neg_add_eq_sub]
          exact hlow j (by omega)
      have hhigh : ∀ j ≥ 1 - lo, (h : ℤ → Dc W T c) j ∈ F (1 - j) := by
        intro j hj
        rw [htop j hj]
        exact Submodule.mem_top
      have hdec := graded_class_decomposition F h (k + 1) (1 - lo) hlowh hhigh
      have hsk : singleCoeffClass F k w hw = a • classAtRoot c hP4 hcrys hLb s ζ x -
          Submodule.Quotient.mk h := by
        rw [hcls]
        abel
      rw [hsk]
      refine sub_mem (Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, rfl⟩)) ?_
      rw [hdec]
      refine Submodule.sum_mem _ fun j hj => ?_
      rw [Finset.mem_Ico] at hj
      exact ih (1 - lo - j).toNat (by omega) j rfl _ _
  rw [eq_top_iff]
  intro q _
  obtain ⟨g, rfl⟩ := Submodule.Quotient.mk_surjective _ q
  have hlow' : ∀ j < -hi, (g : ℤ → Dc W T c) j ∈ F (1 - j) := by
    intro j hj
    have h0 : (g : ℤ → Dc W T c) j ∈ F (-j) := Submodule.mem_pi.1 g.2 j (Set.mem_univ j)
    rw [hbot j hj, Submodule.mem_bot] at h0
    rw [h0]
    exact zero_mem _
  have hhigh' : ∀ j ≥ 1 - lo, (g : ℤ → Dc W T c) j ∈ F (1 - j) := by
    intro j hj
    rw [htop j hj]
    exact Submodule.mem_top
  rw [graded_class_decomposition F g (-hi) (1 - lo) hlow' hhigh']
  exact Submodule.sum_mem _ fun j _ => hsingle _ j rfl _ _

theorem classAtRoot_smul (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s) (a : LetA O n) (x : ↥(W.N T)) :
    classAtRoot c hP4 hcrys hLb s ζ (a • x) =
      PowerSeries.constantCoeff (W.lev c ζ a) • classAtRoot c hP4 hcrys hLb s ζ x := by
  show Submodule.Quotient.mk _ = _ • Submodule.Quotient.mk _
  rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, Submodule.mem_comap, Submodule.mem_pi]
  intro k _
  show ιV PD (LL := LL) (V := T.V) (Lb.levB T c ζ (a • x) k -
      PowerSeries.constantCoeff (W.lev c ζ a) • Lb.levB T c ζ x k) ∈ FilLev W T c s (1 - k)
  rw [map_sub, LinearMap.map_smul (ιV PD (LL := LL) (V := T.V)), ← hLb, ← hLb, W.levN_smul]
  obtain ⟨m, hm⟩ := W.levN_supp T c ζ x
  have hsupp : Function.support (fun j : ℕ => PowerSeries.coeff j (W.lev c ζ a) • W.levN T c ζ x (k - j)) ⊆
      ↑(Finset.range ((k - m).toNat + 1)) := by
    intro j hj
    rw [Finset.coe_range, Set.mem_Iio]
    by_contra hlt
    apply hj
    show PowerSeries.coeff j (W.lev c ζ a) • W.levN T c ζ x (k - j) = 0
    rw [hm (k - j) (by omega), smul_zero]
  rw [finsum_eq_sum_of_support_subset _ hsupp, Finset.sum_range_succ',
    PowerSeries.coeff_zero_eq_constantCoeff_apply, Nat.cast_zero, sub_zero, add_sub_cancel_right]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hLb]
  refine Submodule.smul_mem _ _ ?_
  have h1 := levB_mem_fil (c := c) hP4 hcrys hLb s ζ x (k - ((j + 1 : ℕ) : ℤ))
  exact hfilt.1 (show 1 - k ≤ -(k - ((j + 1 : ℕ) : ℤ)) by push_cast; omega) h1

theorem level_idempotent_eq_one (ζ : LL) : W.lev c ζ (letE c : LetA O n) = 1 := by
  have h := W.lev_letter c ζ (1 - letE c) (by simp [letE])
  rw [map_sub, map_one, sub_eq_zero] at h
  exact h.symm

theorem coord_t_finset_sum {κ' : Type} (t : Finset κ') (f : κ' → C.V) :
    C.t c (∑ i ∈ t, f i) = ∑ i ∈ t, C.t c (f i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [Coord.t_zero]
  | insert i t hi ih => rw [Finset.sum_insert hi, Finset.sum_insert hi, C.t_add, ih]

theorem span_classes (hP4 : LevelMapHodgeFiltration W) (hcrys : IsCrys PD T.ρ)
    (hLb : ∀ (i : ZMod n) (ζ : LL) (x : ↥(W.N T)) (k : ℤ),
      W.levN T i ζ x k = ιV PD (LL := LL) (V := T.V) (Lb.levB T i ζ x k))
    (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (s : ℕ) (hfilt : IsFilt (FilD W T c s)) (ζ : Rs LL PD.p s)
    {r : ℕ} (e : Fin r → C.V) (he : ∀ j, e j ∈ (latOf C).N c)
    (hspan : Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N c) :
    Submodule.span LL (Set.range fun j => (Submodule.Quotient.mk
      ⟨fun k => (⟨Lb.levB T c ζ ⟨C.t c (e j), he j⟩ k, Lb.mem T c ζ ⟨C.t c (e j), he j⟩ k⟩ : Dc W T c),
        fun k _ => levB_mem_fil hP4 hcrys hLb s ζ _ k⟩ : GrQ (FilD W T c s))) = ⊤ := by
  set cls := classAtRoot c hP4 hcrys hLb s ζ with hcls
  have hfun : (fun j => (Submodule.Quotient.mk
      ⟨fun k => (⟨Lb.levB T c ζ ⟨C.t c (e j), he j⟩ k, Lb.mem T c ζ ⟨C.t c (e j), he j⟩ k⟩ : Dc W T c),
        fun k _ => levB_mem_fil hP4 hcrys hLb s ζ _ k⟩ : GrQ (FilD W T c s))) =
      fun j => cls ⟨C.t c (e j), he j⟩ := rfl
  rw [hfun, eq_top_iff, ← classes_span_top hP4 hcrys hLb s hfilt ζ, Submodule.span_le]
  set U := Submodule.span LL (Set.range fun j => cls ⟨C.t c (e j), he j⟩) with hU
  have hsm : ∀ (a : LetA O n) (x : ↥(W.N T)), cls (a • x) = PowerSeries.constantCoeff (W.lev c ζ a) • cls x :=
    fun a x => classAtRoot_smul hP4 hcrys hLb s hfilt ζ a x
  obtain ⟨⟨r', b, hbΔ, huniq, -⟩, -⟩ := hmod

  have hb : ∀ j, ∃ y : ↥(W.N T), (y : W.DD T) = (letE c : LetA O n) • b j ∧ cls y ∈ U := by
    intro j
    have hN : (letE c : LetA O n) • b j ∈ W.N T := (W.N T).smul_mem _ (hbΔ j).1
    obtain ⟨e', he'⟩ := C.t_surj c ((letE c : LetA O n) • b j)
      (by rw [smul_smul, letE_mul_self])
      (fun δ hδ => by rw [γD_smulA, γA_letE, (hbΔ j).2 δ hδ])
    have he'N : e' ∈ (latOf C).N c := by
      show C.t c e' ∈ W.N T
      rw [he']
      exact hN
    rw [← hspan] at he'N
    obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 he'N
    have hy : (⟨(letE c : LetA O n) • b j, hN⟩ : ↥(W.N T)) =
        ∑ i, (baseIdOf hR).d (β i) • (⟨C.t c (e i), he i⟩ : ↥(W.N T)) := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [Submodule.coe_smul]
      rw [← he', ← hβ, coord_t_finset_sum]
      exact Finset.sum_congr rfl fun i _ => C.t_smul c (β i) (e i)
    refine ⟨⟨_, hN⟩, rfl, ?_⟩
    rw [hy, map_sum]
    refine Submodule.sum_mem _ fun i _ => ?_
    rw [hsm]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  choose y hy hyU using hb
  rintro _ ⟨x, rfl⟩
  obtain ⟨α, hα⟩ := (huniq x x.2).exists
  have hx : (letE c : LetA O n) • x = ∑ j, α j • y j := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    simp only [Submodule.coe_smul]
    rw [hα, Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hy j, smul_comm]
  have hx1 : cls x = cls ((letE c : LetA O n) • x) := by
    rw [hsm, level_idempotent_eq_one, map_one, one_smul]
  show cls x ∈ U
  rw [hx1, hx, map_sum]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [hsm]
  exact Submodule.smul_mem _ _ (hyU j)

end Formalism.MainNotions.N.Ln03.K8

end
