import Formalism.SharpRestriction.LevelLetterCocycles.CoordHomMapTrace
import Formalism.SharpRestriction.LevelLetterCocycles.ExponentWindowSubsetShort
import Formalism.SharpRestriction.LevelLetterCocycles.DeltaInvariantLattices
import Lemmata.FirstBlockLemmaI.Imports
import Lemmata.GeneralBFactRightForm.Imports

noncomputable section

namespace Formalism.MainNotions.WachCoordinates.Br

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR}
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {I : BaseId W} {T : LocLat G Qp LL O}

abbrev RingA (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations W 1 (PD.p - 1) W.π₀ (fun _ => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O))

theorem delta_invariants_ring_and_module (hs : W.s = 1) (hp : PD.p ≠ 2) (hK : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T) : RingA W ∧ Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀ :=
  (h9 hs hp).2.2 hK

theorem mem_sm {V : Type} [AddCommGroup V] [Module (PowerSeries O) V] (a : PowerSeries O)
    (S : Submodule (PowerSeries O) V) (x : V) : x ∈ Formalism.ExponentWindows.E.sm a S ↔ ∃ y ∈ S, a • y = x :=
  Iff.rfl

theorem Q_eq_q (hs : W.s = 1) : W.Q = W.q := by
  unfold LocWach.Q
  rw [hs]
  simp

theorem Eat_q :
    Formalism.MainNotions.DeltaInvariantLattices.Eat (fun _ : ZMod n => Polynomial.X + Polynomial.C ((PD.p : ℕ) : O)) W.π₀ = qP W := by
  funext i
  simp [Formalism.MainNotions.DeltaInvariantLattices.Eat, qP, LocWach.π₀]

theorem qP_pow_mem (hs : W.s = 1) (hR : RingA W) (S : Submodule (LetA O n) (W.DD T)) {x : W.DD T}
    {k : ℕ} (h : W.Q ^ k • x ∈ S) : qP W ^ k • x ∈ S := by
  obtain ⟨w, hw⟩ := hR.2.2.2.2.1
  rw [Eat_q] at hw
  have e : qP W ^ k • x = ((w⁻¹ : (LetA O n)ˣ) : LetA O n) ^ k • (W.Q ^ k • x) := by
    rw [smul_smul, Q_eq_q hs, hw, ← mul_pow, ← mul_assoc, Units.inv_mul, one_mul]
  rw [e]
  exact S.smul_mem _ h

theorem Coord.t_sum (C : Coord W I T) (i : ZMod n) {κ : Type} (s : Finset κ) (f : κ → C.V) :
    C.t i (∑ j ∈ s, f j) = ∑ j ∈ s, C.t i (f j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [C.t_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, C.t_add, ih]

theorem t_mem_NΔ (C : Coord W I T) (i : ZMod n) {x : C.V} (hx : x ∈ (latOf C).N i) :
    C.t i x ∈ W.NΔ T := ⟨hx, fun δ hδ => C.t_Δ i x δ hδ⟩

theorem t_mem_Nl (C : Coord W I T) (i : ZMod n) {x : C.V} (hx : x ∈ (latOf C).N i) :
    C.t i x ∈ W.Nl T i := ⟨C.t i x, hx, C.t_letter i x⟩

theorem exists_t_letE (C : Coord W I T) (i : ZMod n) {b : W.DD T} (hb : b ∈ W.NΔ T) :
    ∃ y : C.V, y ∈ (latOf C).N i ∧ C.t i y = (letE i : LetA O n) • b := by
  obtain ⟨y, hy⟩ := C.t_surj i ((letE i : LetA O n) • b) (by rw [smul_smul, letE_mul_self])
    (fun δ hδ => by rw [γD_smulA, γA_letE, hb.2 δ hδ])
  exact ⟨y, by rw [mem_N, hy]; exact (W.N T).smul_mem _ hb.1, hy⟩

theorem mul_letE_eq (a : LetA O n) (i : ZMod n) (f : PowerSeries O) (h : I.ι f = a i) :
    a * letE i = I.d f * letE i := by
  funext k
  by_cases hk : k = i
  · subst hk; simp [letE, h]
  · simp [letE, hk]

theorem exists_ι_of_AΔ (hFull : I.Full) {a : LetA O n} (ha : a ∈ W.AΔ) (i : ZMod n) :
    ∃ f : PowerSeries O, I.ι f = a i :=
  hFull (a i) fun δ hδ => congrFun (ha δ hδ) i

theorem gamma_sub_one_in_coordinates (hs : W.s = 1) (hp : PD.p ≠ 2) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T) :
    (latOf C).P9 := by
  intro i x hx
  have hg : W.gamK = W.gam := W.gamK_eq_one hs hp
  obtain ⟨x', hx', he⟩ := hmod.2 _ (t_mem_NΔ C i hx)
  obtain ⟨y, hyN, hy⟩ := exists_t_letE C i hx'
  refine (mem_sm _ _ _).2 ⟨y, hyN, C.t_inj i ?_⟩
  have h1 : C.t i ((latOf C).γ i x - x) = W.π₀ • x' := by
    rw [C.t_sub, t_γ, hg]
    exact he
  have h2 := C.t_letter i ((latOf C).γ i x - x)
  rw [h1] at h2
  rw [C.t_smul, hy, I.d_X, h1, smul_comm, h2]

theorem first_comparison_in_coordinates (hs : W.s = 1) (hR : RingA W) {M h : ZMod n → ℕ} (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h)
    (C : Coord W I T) (i : ZMod n) (m : ℕ) (hm : M i ≤ m) : (latOf C).P5M i m := by
  intro x hx
  rw [mem_N, C.t_smul, map_pow, I.d_q, t_φ]
  have h1 := qP_pow_mem hs hR (W.N T) (h5.1 i _ (t_mem_Nl C (i - 1) hx))
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [pow_add, mul_comm, mul_smul]
  exact (W.N T).smul_mem _ h1

theorem extension_lattice_intersection {C : Coord W I T} {C₀ : Coord W I W.one} (R : RealExt C C₀) (hE : R.Exact)
    (hses : IsSESLat (Qp := Qp) R.ι R.π) (h6 : Formalism.MainNotions.DeltaInvariantLattices.wachShortExact W R.ι R.π) : (R.ext hE).P6 := by
  intro i u hu
  refine (h6 hses).2.2.2.1 (C.t i u) ?_
  rw [← R.hι.coord_hom_map_trace]
  exact hu

theorem free_uniform (hInj : I.Inj) (hFull : I.Full) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀)
    (C : Coord W I T) : ∃ r : ℕ, ∀ i, ∃ e : Fin r → C.V, LinearIndependent (PowerSeries O) e ∧
      Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N i := by
  obtain ⟨⟨r, b, hb, huniq, hspan⟩, -⟩ := hmod
  refine ⟨r, fun i => ?_⟩
  choose e heN he using fun j => exists_t_letE C i (hb j)
  have hsum : ∀ f : Fin r → PowerSeries O,
      C.t i (∑ j, f j • e j) = ∑ j, (I.d (f j) * letE i) • b j := by
    intro f
    rw [C.t_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [C.t_smul, he, smul_smul]
  refine ⟨e, Fintype.linearIndependent_iff.2 fun f hf j => ?_, le_antisymm ?_ ?_⟩
  · have h0 : (0 : W.DD T) = ∑ j, (I.d (f j) * letE i) • b j := by
      rw [← hsum, hf, C.t_zero]
    have h0' : (0 : W.DD T) = ∑ j, ((0 : Fin r → LetA O n) j) • b j := by simp
    have := (huniq 0 (W.N T).zero_mem).unique h0 h0'
    have h1 := congrFun (congrFun this j) i
    have h2 : I.ι (f j) = 0 := by simpa [letE] using h1
    exact hInj (by rw [h2, map_zero])
  · rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact heN j
  · intro x hx
    obtain ⟨a, ha, hxa⟩ := hspan _ (t_mem_NΔ C i hx)
    choose f hf using fun j => exists_ι_of_AΔ hFull (ha j) i
    have hx' : x = ∑ j, f j • e j := by
      apply C.t_inj i
      rw [hsum, ← C.t_letter i x, hxa, Finset.smul_sum]
      exact Finset.sum_congr rfl fun j _ => by rw [smul_smul, mul_comm, mul_letE_eq (a j) i (f j) (hf j)]
    rw [hx']
    exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem free_of (hInj : I.Inj) (hFull : I.Full) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) (C : Coord W I T)
    (i : ZMod n) : (latOf C).Free i := by
  obtain ⟨r, h⟩ := free_uniform hInj hFull hmod C
  obtain ⟨e, h1, h2⟩ := h i
  exact ⟨r, e, h1, h2⟩

theorem jumpsLet_of {M h : ZMod n → ℕ}
    (H : ∀ i, JumpsAtE PD T W.emb i (Set.Icc (-(M i : ℤ)) (h i))) : Formalism.MainNotions.DeltaInvariantLattices.JumpsLet W T M h :=
  fun τ i hτ => H i τ hτ

theorem γA_mul (g h : W.Gam) (a : LetA O n) : W.γA (g * h) a = W.γA g (W.γA h a) := by
  funext k
  simp [LocWach.γA, letγ, map_mul]

theorem mem_DelF_mul {δ' : W.Gam} (hδ' : δ' ∈ W.DelF) (δ : W.Gam) :
    δ ∈ W.DelF ↔ δ' * δ ∈ W.DelF := by
  obtain ⟨a, ha, ha1⟩ := (W.DelF_def δ').1 hδ'
  constructor
  · intro hδ
    obtain ⟨b, hb, hb1⟩ := (W.DelF_def δ).1 hδ
    refine (W.DelF_def _).2 ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    rw [mul_pow, pow_mul, ha1, one_pow, one_mul, mul_comm a b, pow_mul, hb1, one_pow]
  · intro hδ
    obtain ⟨c, hc, hc1⟩ := (W.DelF_def _).1 hδ
    refine (W.DelF_def _).2 ⟨a * c, Nat.mul_pos ha hc, ?_⟩
    have h1 : (δ' * δ) ^ (a * c) = 1 := by rw [mul_comm a c, pow_mul, hc1, one_pow]
    rwa [mul_pow, pow_mul, ha1, one_pow, one_mul] at h1

theorem sum_γA_mem (c : LetA O n) : ∑ δ ∈ W.DelF, W.γA δ c ∈ W.AΔ := by
  intro δ' hδ'
  rw [map_sum]
  refine Finset.sum_equiv (Equiv.mulLeft δ') (fun δ => ?_) (fun δ _ => ?_)
  · exact mem_DelF_mul hδ' δ
  · rw [← γA_mul]
    rfl

theorem average (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) {r : ℕ} (c : Fin r → LetA O n)
    (w : Fin r → W.DD T) (hw : ∀ j, ∀ δ ∈ W.DelF, W.γD T δ (w j) = w j) {z : W.DD T}
    (hz : ∀ δ ∈ W.DelF, W.γD T δ z = z) (h : z = ∑ j, c j • w j) :
    ∃ d : Fin r → LetA O n, (∀ j, d j ∈ W.AΔ) ∧ z = ∑ j, d j • w j := by
  obtain ⟨u, hu⟩ := hΔ
  refine ⟨fun j => ((u⁻¹ : Oˣ) : O) • ∑ δ ∈ W.DelF, W.γA δ (c j),
    fun j => W.AΔ.smul_mem (sum_γA_mem (c j)) _, ?_⟩
  have h1 : ∀ δ ∈ W.DelF, z = ∑ j, W.γA δ (c j) • w j := by
    intro δ hδ
    rw [← hz δ hδ, h, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [γD_smulA, hw j δ hδ]
  have h2 : ((W.DelF.card : ℕ) : O) • z = ∑ j, (∑ δ ∈ W.DelF, W.γA δ (c j)) • w j := by
    simp only [Finset.sum_smul]
    rw [Finset.sum_comm, ← Finset.sum_congr rfl h1, Finset.sum_const, Nat.cast_smul_eq_nsmul]
  have h3 : z = ((u⁻¹ : Oˣ) : O) • (((W.DelF.card : ℕ) : O) • z) := by
    rw [smul_smul, ← hu, Units.inv_mul, one_smul]
  rw [h3, h2, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_assoc]

theorem φspan_le {r : ℕ} (b : Fin r → W.DD T)
    (hb : ∀ x ∈ W.N T, ∃ a : Fin r → LetA O n, x = ∑ j, a j • b j) (i : ZMod n) :
    Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) ≤
      Submodule.span (LetA O n) (Set.range fun j => W.φD T ((letE (i - 1) : LetA O n) • b j)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
  obtain ⟨a, ha⟩ := hb x hx
  have e : W.φD T (((letE (i - 1) : LetA O n) • (LinearMap.id : W.DD T →ₗ[LetA O n] W.DD T)) x) =
      ∑ j, W.φA (a j) • W.φD T ((letE (i - 1) : LetA O n) • b j) := by
    rw [LinearMap.smul_apply, LinearMap.id_apply, ha, Finset.smul_sum, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [smul_comm, φD_smulA]
  rw [SetLike.mem_coe, e]
  exact Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)

theorem second_comparison_in_coordinates (hs : W.s = 1) (hR : RingA W) (hFull : I.Full)
    (hΔ : IsUnit ((W.DelF.card : ℕ) : O)) (hmod : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T W.π₀) {M h : ZMod n → ℕ}
    (h5 : Formalism.MainNotions.DeltaInvariantLattices.p5 W T M h) (C : Coord W I T) (i : ZMod n) (m : ℕ) (hm : h i ≤ m) :
    (latOf C).FrobeniusCobounded i m := by
  intro x hx
  obtain ⟨⟨r, b, hb, huniq, -⟩, -⟩ := hmod
  choose e heN he using fun j => exists_t_letE C (i - 1) (hb j)

  have h1 := qP_pow_mem hs hR _ (h5.2.1 i _ (t_mem_Nl C i hx))
  have h2 : qP W ^ m • C.t i x ∈ Formalism.MainNotions.DeltaInvariantLattices.φspan W T (W.Nl T (i - 1)) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
    rw [pow_add, mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ h1
  have h3 := φspan_le b (fun x hx => (huniq x hx).exists) i h2
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun (LetA O n)).1 h3
  have hz : C.t i (I.Bs.q ^ m • x) = qP W ^ m • C.t i x := by rw [C.t_smul, map_pow, I.d_q]
  have hw : ∀ j, W.φD T ((letE (i - 1) : LetA O n) • b j) = C.t i ((latOf C).φ i (e j)) := by
    intro j
    rw [t_φ, he]
  simp only [hw] at hc
  obtain ⟨d, hd, hzd⟩ := average hΔ c (fun j => C.t i ((latOf C).φ i (e j)))
    (fun j δ hδ => C.t_Δ i _ δ hδ) (fun δ hδ => C.t_Δ i (I.Bs.q ^ m • x) δ hδ) (by rw [hz, hc])
  choose f hf using fun j => exists_ι_of_AΔ hFull (hd j) i
  have hx' : I.Bs.q ^ m • x = ∑ j, f j • (latOf C).φ i (e j) := by
    apply C.t_inj i
    rw [C.t_sum, hzd]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [C.t_smul, ← C.t_letter i ((latOf C).φ i (e j)), smul_smul, smul_smul,
      mul_letE_eq (d j) i (f j) (hf j)]
  rw [hx']
  exact Submodule.sum_mem _ fun j _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨e j, heN j, rfl⟩)

theorem card_DelF (hs : W.s = 1) (hp : PD.p ≠ 2) (hK : Module.finrank K₀ K = 1)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.p9 W T) : W.DelF.card = PD.p - 1 := by
  rw [(h9 hs hp).1, hK, Nat.div_one]

theorem inv_of_isUnit (C : Coord W I T) (a : PowerSeries O)
    (hu : IsUnit (algebraMap (LetA O n) W.EE (I.d a))) : (latOf C).Inv a := by
  have hcancel : ∀ x y : W.DD T, I.d a • x = I.d a • y → x = y := by
    intro x y h
    rw [← algebraMap_smul W.EE (I.d a) x, ← algebraMap_smul W.EE (I.d a) y] at h
    exact hu.smul_left_cancel.1 h
  constructor
  · intro x y h
    apply C.t_inj 0
    apply hcancel
    rw [← C.t_smul, ← C.t_smul]
    exact congrArg _ h
  · intro x
    obtain ⟨u, hu'⟩ := hu
    have hay : I.d a • (((u⁻¹ : W.EEˣ) : W.EE) • C.t 0 x) = C.t 0 x := by
      rw [← algebraMap_smul W.EE (I.d a), ← hu', smul_smul, Units.mul_inv, one_smul]
    obtain ⟨z, hz⟩ := C.t_surj 0 (((u⁻¹ : W.EEˣ) : W.EE) • C.t 0 x)
      (by
        apply hcancel
        rw [smul_comm, hay, C.t_letter])
      (by
        intro δ hδ
        apply hcancel
        have h1 : W.γD T δ (I.d a • (((u⁻¹ : W.EEˣ) : W.EE) • C.t 0 x)) =
            I.d a • W.γD T δ (((u⁻¹ : W.EEˣ) : W.EE) • C.t 0 x) := by
          rw [γD_smulA, I.γA_Δ δ hδ]
        rw [← h1, hay, C.t_Δ 0 x δ hδ])
    exact ⟨z, C.t_inj 0 (by rw [C.t_smul, hz, hay])⟩

theorem isUnit_π₀ (hR : RingA W) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  obtain ⟨w, hw⟩ := hR.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

theorem invX_of (hR : RingA W) (C : Coord W I T) : (latOf C).Inv PowerSeries.X :=
  inv_of_isUnit C _ (by rw [I.d_X]; exact isUnit_π₀ hR)

theorem isUnit_add_of_mem_jacobson {R : Type} [CommRing R] {u z : R} (hu : IsUnit u)
    (hz : z ∈ (⊥ : Ideal R).jacobson) : IsUnit (u + z) := by
  first | exact Bl.FirstBlockLemmaI.goal1 .. | (apply Bl.FirstBlockLemmaI.goal1 <;> assumption) | (intros; apply Bl.FirstBlockLemmaI.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaI.goal1 <;> assumption) | (intros; apply @Bl.FirstBlockLemmaI.goal1 <;> assumption) | (apply @Bl.FirstBlockLemmaI.goal1 <;> first | assumption | infer_instance) | exact @Bl.FirstBlockLemmaI.goal1 R ‹_› u z hu hz | exact @Bl.FirstBlockLemmaI.goal1 R ‹_› u z hu | exact @Bl.FirstBlockLemmaI.goal1 R ‹_› u z | exact @Bl.FirstBlockLemmaI.goal1 R ‹_› u | exact @Bl.FirstBlockLemmaI.goal1 R ‹_› | exact @Bl.FirstBlockLemmaI.goal1 R

theorem isUnit_pS (hR : RingA W) (hT : ToolsAlg W) (s : ℕ) :
    IsUnit (algebraMap (LetA O n) W.EE (pS W s)) := by
  have := W.EE_complete
  obtain ⟨u, P, hu, hmon, hdeg, hdiv, he⟩ := hT.2.1 s
  rw [he, map_mul]
  refine (hu.map _).mul ?_
  rw [← Polynomial.aeval_algebraMap_apply W.EE W.π₀ P, Polynomial.aeval_eq_sum_range,
    Finset.sum_range_succ, hmon.coeff_natDegree, one_smul, add_comm]
  refine isUnit_add_of_mem_jacobson ((isUnit_π₀ hR).pow _)
    (IsAdicComplete.le_jacobson_bot (Ideal.span {((PD.p : ℕ) : W.EE)}) ?_)
  refine Ideal.sum_mem _ fun k hk => ?_
  obtain ⟨c, hc⟩ := hdiv k (by rw [← hdeg]; exact Finset.mem_range.1 hk)
  rw [hc, mul_smul, Algebra.smul_def, map_natCast]
  exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)

theorem invP_of (hR : RingA W) (hT : ToolsAlg W) (C : Coord W I T) (s : ℕ) :
    (latOf C).Inv (I.Bs.p s) :=
  inv_of_isUnit C _ (by rw [I.d_p]; exact isUnit_pS hR hT s)

theorem p_regular_EE [IsDomain O] (hp0 : ((PD.p : ℕ) : O) ≠ 0) (x : W.EE)
    (hx : ((PD.p : ℕ) : W.EE) * x = 0) : x = 0 := by
  have := W.EE_complete
  have hp' : ((PD.p : ℕ) : PowerSeries O) ≠ 0 := by
    intro h
    apply hp0
    have := congrArg PowerSeries.constantCoeff h
    simpa using this
  have key : ∀ k : ℕ, x ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
    intro k
    obtain ⟨a, m, ham⟩ := W.EE_dense x k
    have h1 : algebraMap (LetA O n) W.EE (((PD.p : ℕ) : LetA O n) * a) ∈
        Ideal.span {((PD.p : ℕ) : W.EE) ^ (k + 1)} := by
      obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 ham
      rw [Ideal.mem_span_singleton']
      refine ⟨-y, ?_⟩
      have e : algebraMap (LetA O n) W.EE a =
          x * algebraMap (LetA O n) W.EE (letπ ^ m) - y * ((PD.p : ℕ) : W.EE) ^ k := by
        rw [hy]; ring
      rw [map_mul, map_natCast, e, mul_sub, ← mul_assoc, hx, zero_mul]
      ring
    obtain ⟨b, hb⟩ := W.EE_sat _ _ h1
    have h2 : a = ((PD.p : ℕ) : LetA O n) ^ k * b := by
      funext i
      have h3 := congrFun hb i
      simp only [Pi.mul_apply, Pi.pow_apply, Pi.natCast_apply] at h3 ⊢
      apply mul_left_cancel₀ hp'
      rw [h3]
      ring
    have h4 : algebraMap (LetA O n) W.EE a ∈ Ideal.span {((PD.p : ℕ) : W.EE) ^ k} := by
      rw [h2, map_mul, map_pow, map_natCast]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _)
    have h5 := Ideal.add_mem _ ham h4
    rw [sub_add_cancel, map_pow] at h5
    exact (Ideal.mul_unit_mem_iff_mem _ (W.EE_π.pow m)).1 h5
  refine IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {((PD.p : ℕ) : W.EE)}) W.EE) x
    fun k => ?_
  rw [SModEq.zero, Ideal.span_singleton_pow, smul_eq_mul, Ideal.mul_top]
  exact key k

theorem ltors_of [IsDomain O] (hp0 : ((PD.p : ℕ) : O) ≠ 0) (C : Coord W I T) : (latOf C).LTors := by
  intro x hx
  apply C.t_inj 0
  rw [C.t_zero]
  have h1 : ((PD.p : ℕ) : W.EE) • C.t 0 x = 0 := by
    have h := congrArg (C.t 0) hx
    rw [C.t_smul, C.t_zero, Formalism.ExponentWindows.E.Base.lc, I.d_C, I.ℓ_eq, algebraMap_smul,
      ← algebraMap_smul W.EE, map_natCast] at h
    exact h
  have := (W.DD_free T).1
  apply (Module.Free.chooseBasis W.EE (W.DD T)).repr.injective
  ext k
  have h2 := congrArg (fun y => (Module.Free.chooseBasis W.EE (W.DD T)).repr y k) h1
  simp only [map_smul, Finsupp.smul_apply, smul_eq_mul, map_zero, Finsupp.zero_apply] at h2
  rw [map_zero, Finsupp.zero_apply]
  exact p_regular_EE hp0 _ h2

section Abstract

theorem linIndep_of_mutual {R V : Type} [CommRing R] [IsDomain R] [AddCommGroup V] [Module R V]
    {r : ℕ} (e w : Fin r → V) (he : LinearIndependent R e) {α β : R} (hα : α ≠ 0) (hβ : β ≠ 0)
    (h1 : ∀ a, β • w a ∈ Submodule.span R (Set.range e))
    (h2 : ∀ l, α • e l ∈ Submodule.span R (Set.range w)) : LinearIndependent R w := by
  first | exact Bl.general_b_fact_right_form.goal1 .. | (apply Bl.general_b_fact_right_form.goal1 <;> assumption) | (intros; apply Bl.general_b_fact_right_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_form.goal1 <;> assumption) | (intros; apply @Bl.general_b_fact_right_form.goal1 <;> assumption) | (apply @Bl.general_b_fact_right_form.goal1 <;> first | assumption | infer_instance) | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α β hα hβ h1 h2 | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α β hα hβ h1 | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α β hα hβ | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α β hα | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α β | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he α | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w he | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e w | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r e | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› r | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› ‹_› | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› ‹_› | exact @Bl.general_b_fact_right_form.goal1 R V ‹_› | exact @Bl.general_b_fact_right_form.goal1 R V | exact @Bl.general_b_fact_right_form.goal1 R

variable {O' : Type} [CommRing O'] {B' : Formalism.ExponentWindows.E.Base O'} {n' : ℕ} {V : Type} [AddCommGroup V]
  [Module (PowerSeries O') V]

def Pp (B' : Formalism.ExponentWindows.E.Base O') : Submonoid (PowerSeries O') := Submonoid.closure (Set.range B'.p)

theorem Pp_ne_zero [IsDomain O'] (hp : ∀ s, B'.p s ≠ 0) {a : PowerSeries O'} (ha : a ∈ Pp B') :
    a ≠ 0 := by
  induction ha using Submonoid.closure_induction with
  | mem x hx => obtain ⟨s, rfl⟩ := hx; exact hp s
  | one => exact one_ne_zero
  | mul x y _ _ hx hy => exact mul_ne_zero hx hy

theorem Pp_φ {a : PowerSeries O'} (ha : a ∈ Pp B') : B'.φ a ∈ Pp B' := by
  induction ha using Submonoid.closure_induction with
  | mem x hx =>
    obtain ⟨s, rfl⟩ := hx
    exact Submonoid.subset_closure ⟨s + 1, by
      simp only [Formalism.ExponentWindows.E.Base.p, Function.iterate_succ_apply']⟩
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy

theorem q_mem_Pp : B'.q ∈ Pp B' := Submonoid.subset_closure ⟨0, rfl⟩

theorem pull_mutual (L : Formalism.ExponentWindows.E.Lat B' n' V) (m h : ZMod n' → ℕ) (hM : ∀ i, L.P5M i (m i))
    (hh : ∀ i, L.FrobeniusCobounded i (h i)) (c : ZMod n') {r : ℕ} (e : Fin r → V)
    (he : Submodule.span (PowerSeries O') (Set.range e) = L.N c) (k : ℕ) :
    ∃ α ∈ Pp B', ∃ β ∈ Pp B', (∀ a, β • L.phiIt c k (e a) ∈ L.N (c + ((k : ℕ) : ZMod n'))) ∧
      ∀ x ∈ L.N (c + ((k : ℕ) : ZMod n')),
        α • x ∈ Submodule.span (PowerSeries O') (Set.range fun a => L.phiIt c k (e a)) := by
  induction k with
  | zero =>
    have h0 : c + ((0 : ℕ) : ZMod n') = c := by simp
    refine ⟨1, one_mem _, 1, one_mem _, fun a => ?_, fun x hx => ?_⟩
    · rw [h0, one_smul, ← he]
      exact Submodule.subset_span ⟨a, rfl⟩
    · rw [h0, ← he] at hx
      rw [one_smul]
      exact hx
  | succ k ih =>
    obtain ⟨α, hα, β, hβ, h1, h2⟩ := ih
    have hi : c + ((k + 1 : ℕ) : ZMod n') - 1 = c + ((k : ℕ) : ZMod n') := by
      push_cast
      ring
    refine ⟨B'.φ α * B'.q ^ h (c + ((k + 1 : ℕ) : ZMod n')), mul_mem (Pp_φ hα) (pow_mem q_mem_Pp _),
      B'.q ^ m (c + ((k + 1 : ℕ) : ZMod n')) * B'.φ β, mul_mem (pow_mem q_mem_Pp _) (Pp_φ hβ),
      fun a => ?_, fun x hx => ?_⟩
    · have h3 := hM (c + ((k + 1 : ℕ) : ZMod n')) (β • L.phiIt c k (e a)) (by rw [hi]; exact h1 a)
      rw [L.φ_semi, smul_smul] at h3
      exact h3
    · have h4 : Submodule.span (PowerSeries O')
          (L.φ (c + ((k + 1 : ℕ) : ZMod n')) '' (L.N (c + ((k + 1 : ℕ) : ZMod n') - 1) : Set V)) ≤
          (Submodule.span (PowerSeries O') (Set.range fun a => L.phiIt c (k + 1) (e a))).comap
            (LinearMap.lsmul (PowerSeries O') V (B'.φ α)) := by
        refine Submodule.span_le.2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rw [SetLike.mem_coe, hi] at hy
        obtain ⟨cf, hcf⟩ := (Submodule.mem_span_range_iff_exists_fun (PowerSeries O')).1 (h2 y hy)
        rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.lsmul_apply, ← L.φ_semi, ← hcf, map_sum]
        refine Submodule.sum_mem _ fun a _ => ?_
        rw [L.φ_semi]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
      have h5 := h4 (hh _ x hx)
      rw [Submodule.mem_comap, LinearMap.lsmul_apply, smul_smul] at h5
      exact h5

theorem pullback_free_of_comparison [IsDomain O'] (L : Formalism.ExponentWindows.E.Lat B' n' V) (hp : ∀ s, B'.p s ≠ 0) {r : ℕ}
    (hfree : ∀ i, ∃ e : Fin r → V, LinearIndependent (PowerSeries O') e ∧
      Submodule.span (PowerSeries O') (Set.range e) = L.N i)
    (m h : ZMod n' → ℕ) (hM : ∀ i, L.P5M i (m i)) (hh : ∀ i, L.FrobeniusCobounded i (h i)) (c : ZMod n') (k : ℕ) :
    L.PullFree c k := by
  obtain ⟨e, -, he⟩ := hfree c
  obtain ⟨e', hli, he'⟩ := hfree (c + ((k : ℕ) : ZMod n'))
  obtain ⟨α, hα, β, hβ, h1, h2⟩ := pull_mutual L m h hM hh c e he k
  refine ⟨r, e, he, linIndep_of_mutual e' _ hli (Pp_ne_zero hp hα) (Pp_ne_zero hp hβ)
    (fun a => by rw [he']; exact h1 a)
    (fun l => h2 _ (by rw [← he']; exact Submodule.subset_span ⟨l, rfl⟩))⟩

end Abstract

theorem p_ne_zero [Nontrivial O] (hR : RingA W) (hT : ToolsAlg W) (I : BaseId W) (s : ℕ) :
    I.Bs.p s ≠ 0 := by
  intro h0
  have h1 := isUnit_pS hR hT s
  rw [← I.d_p, h0, map_zero, map_zero] at h1
  have : Nontrivial W.EE := W.EE_inj.nontrivial
  exact not_isUnit_zero h1

theorem cardΔ_of [IsLocalRing O] (hnu : ¬ IsUnit ((PD.p : ℕ) : O)) (hcard : W.DelF.card = PD.p - 1) :
    IsUnit ((W.DelF.card : ℕ) : O) := by
  have h1 : 1 ≤ PD.p := PD.hp.one_lt.le
  have h2 : IsUnit (1 - ((PD.p : ℕ) : O)) := IsLocalRing.isUnit_one_sub_self_of_mem_nonunits _ hnu
  rw [hcard, Nat.cast_sub h1, Nat.cast_one, ← neg_sub]
  exact h2.neg

structure LocalWachInputs (W : LocWach PD LL O v n) (I : BaseId W) : Prop where

  s_one : W.s = 1

  p_ne_two : PD.p ≠ 2

  unram : Module.finrank K₀ K = 1

  P9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W

  P5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W

  P6 : Formalism.MainNotions.DeltaInvariantLattices.WachSaturationExactness W

  tools : ToolsAlg W

  p_ne_zero : ((PD.p : ℕ) : O) ≠ 0

  cardΔ : IsUnit ((W.DelF.card : ℕ) : O)

  inj : I.Inj

  full : I.Full

theorem lat_items [IsDomain O] (Q : LocalWachInputs W I) (hcrys : IsCrys PD T.ρ) {M h : ZMod n → ℕ}
    (hJ : ∀ i, JumpsAtE PD T W.emb i (Set.Icc (-(M i : ℤ)) (h i))) (C : Coord W I T) :
    (latOf C).P9 ∧ (∀ i m, M i ≤ m → (latOf C).P5M i m) ∧ (∀ i m, h i ≤ m → (latOf C).FrobeniusCobounded i m) ∧
      (∀ i, (latOf C).Free i) ∧ (∀ c k, (latOf C).PullFree c k) ∧ (latOf C).LTors ∧
      (latOf C).Inv PowerSeries.X ∧ ∀ s, (latOf C).Inv (I.Bs.p s) := by
  obtain ⟨hR, hmod⟩ := delta_invariants_ring_and_module Q.s_one Q.p_ne_two Q.unram (Q.P9 T hcrys)
  have h5 := Q.P5 T M h hcrys (jumpsLet_of hJ)
  have hM : ∀ i m, M i ≤ m → (latOf C).P5M i m := fun i m hm => first_comparison_in_coordinates Q.s_one hR h5 C i m hm
  have hh : ∀ i m, h i ≤ m → (latOf C).FrobeniusCobounded i m := fun i m hm =>
    second_comparison_in_coordinates Q.s_one hR Q.full Q.cardΔ hmod h5 C i m hm
  obtain ⟨r, hfree⟩ := free_uniform Q.inj Q.full hmod C
  exact ⟨gamma_sub_one_in_coordinates Q.s_one Q.p_ne_two hmod C, hM, hh, fun i => free_of Q.inj Q.full hmod C i,
    fun c k => pullback_free_of_comparison (latOf C) (p_ne_zero hR Q.tools I) hfree M h
      (fun i => hM i _ le_rfl) (fun i => hh i _ le_rfl) c k,
    ltors_of Q.p_ne_zero C, invX_of hR C, fun s => invP_of hR Q.tools C s⟩

def boxM (Gp S η : ℕ) (ty : ZMod n → LT) (i : ZMod n) : ℕ :=
  match ty i with
  | .thin => Gp
  | .up _ => η
  | .down b => b + S

def boxH (Gp S η : ℕ) (ty : ZMod n → LT) (i : ZMod n) : ℕ :=
  Formalism.ExponentWindows.E.hJ Gp S η (kdOf ty i) (bbOf ty i)

theorem win_sub_box {g Gp S η h : ℕ} {ty : ZMod n → LT} (hη : η ≤ g) (hS : SizesOK g S h ty)
    (i : ZMod n) : (ty i).win Gp S η ∪ {0} ⊆
      Set.Icc (-(boxM Gp S η ty i : ℤ)) (boxH Gp S η ty i) := by
  intro a ha
  have hi := hS i
  unfold boxM boxH kdOf bbOf
  cases hty : ty i with
  | thin =>
    rw [hty] at ha
    simp only [LT.win, Formalism.ExponentWindows.E.hJ, Set.mem_union, Set.mem_Icc, Set.mem_singleton_iff] at ha ⊢
    omega
  | up b =>
    rw [hty] at ha hi
    simp only [LT.win, LT.ok, LT.size, Formalism.ExponentWindows.E.hJ, Set.mem_union, Set.mem_Icc,
      Set.mem_singleton_iff, reduceCtorEq, or_false] at ha hi ⊢
    push_cast
    omega
  | down b =>
    rw [hty] at ha hi
    simp only [LT.win, LT.ok, LT.size, Formalism.ExponentWindows.E.hJ, Set.mem_union, Set.mem_Icc,
      Set.mem_singleton_iff, reduceCtorEq, or_false] at ha hi ⊢
    push_cast
    omega

theorem boxM_le {g Gp S η h : ℕ} {ty : ZMod n → LT} (hG : Gp ≤ g) (hη : η ≤ g) (hg : g ≤ h)
    (hS : SizesOK g S h ty) (i : ZMod n) : boxM Gp S η ty i ≤ h := by
  have hi := hS i
  unfold boxM
  cases hty : ty i with
  | thin => simp only; omega
  | up b => simp only; omega
  | down b =>
    rw [hty] at hi
    simp only [LT.ok, LT.size, reduceCtorEq, or_false] at hi ⊢
    omega

theorem boxM_thin {Gp S η : ℕ} {ty : ZMod n → LT} {i : ZMod n} (h : ty i = LT.thin) :
    boxM Gp S η ty i = Gp := by
  unfold boxM
  rw [h]

theorem boxH_le_HArc (g Gp S η : ℕ) (ty : ZMod n → LT) (c : ZMod n) (s : ℕ) :
    boxH Gp S η ty (c - (s : ZMod n)) ≤ Formalism.ExponentWindows.E.HArc g Gp S η (kdOf ty) (bbOf ty) c s := by
  unfold boxH Formalism.ExponentWindows.E.HArc Formalism.ExponentWindows.E.kindAt Formalism.ExponentWindows.E.sizeAt
  cases kdOf ty (c - (s : ZMod n)) <;> simp only [Formalism.ExponentWindows.E.hJ, Formalism.ExponentWindows.G.HK] <;> omega

theorem jumpsAtE_mono {i : ZMod n} {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {A A' : Set ℤ}
    (h : JumpsAtE PD T emb i A) (hA : A ⊆ A') : JumpsAtE PD T emb i A' :=
  fun τ hτ a ha => hA (h τ hτ a ha)

theorem box_of_kind {g Gp S η h : ℕ} {ty : ZMod n → LT} (hη : η ≤ g) (hS : SizesOK g S h ty)
    (hK : ∀ i, JumpsAtE PD T W.emb i ((ty i).win Gp S η ∪ {0})) (i : ZMod n) :
    JumpsAtE PD T W.emb i (Set.Icc (-(boxM Gp S η ty i : ℤ)) (boxH Gp S η ty i)) :=
  jumpsAtE_mono (hK i) (win_sub_box hη hS i)

theorem finalLat_of [IsDomain O] (Q : LocalWachInputs W I) (hcrys : IsCrys PD T.ρ) {j Gp S η h : ℕ}
    {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) (hg : gPar Gp S η ≤ h) (hS : SizesOK (gPar Gp S η) S h ty)
    (hK : ∀ i, JumpsAtE PD T W.emb i ((ty i).win Gp S η ∪ {0})) (C : Coord W I T) :
    Formalism.ExponentWindows.E.FinalLat (latOf C) (cutsOf hC) (kdOf ty) (bbOf ty) j Gp S η h := by
  obtain ⟨h9, hM, hh, hfree, hpull, hlt, hX, hP⟩ :=
    lat_items Q hcrys (box_of_kind (η_le_gPar Gp S η) hS hK) C
  exact
    { prim :=
        { p9 := h9
          p5M := fun i => hM i h (boxM_le (G_le_gPar Gp S η) (η_le_gPar Gp S η) hg hS i)
          frobeniusBounded_after := fun c hc k h1 h2 => hM _ Gp (boxM_thin (hC.2.2.2.2 c hc k h1 h2)).le
          pullFree := fun c _ => hpull c j
          free := hfree
          ltors := hlt }
      invX := hX
      invP := hP
      p5h := fun i => hh i _ le_rfl }

theorem kind_quot {T₁ T₂ : LocLat G Qp LL O} (hH : HodgeExact PD LL O) (F : LatHom T₁.L T₂.L)
    (h₁ : CrysLat PD T₁) (h₂ : CrysLat PD T₂) (hon : F.Onto) {i : ZMod n}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {A : Set ℤ} (h : JumpsAtE PD T₁ emb i A) :
    JumpsAtE PD T₂ emb i A :=
  fun τ hτ a ha => h τ hτ a (hH.1 T₁ T₂ F h₁ h₂ hon τ a ha)

theorem jumps_ext (hH : HodgeExact PD LL O) {Y : LocLat G Qp LL O} (ι : LatHom T.L Y.L)
    (π : LatHom Y.L W.one.L) (hses : IsSESLat (Qp := Qp) ι π) (hY : CrysLat PD Y) {i : ZMod n}
    {emb : ZMod n → (K₀ →ₐ[Qp] LL)} {A : Set ℤ} (h : JumpsAtE PD T emb i A) :
    JumpsAtE PD Y emb i (A ∪ {0}) := by
  intro τ hτ a ha
  rcases ((hH.2.1 T Y W.one ι π hses hY).2.2 τ a).1 ha with h1 | h1
  · exact Or.inl (h τ hτ a h1)
  · exact Or.inr (hH.2.2 W.one W.one_triv τ a h1)

theorem primExt_of [IsDomain O] (Q : LocalWachInputs W I) (hH : HodgeExact PD LL O) {j Gp S η h rr : ℕ}
    {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (hC : CutsOK n j ty cuts arcLen) (hS : SizesOK (gPar Gp S η) S h ty)
    (hK : ∀ i, JumpsAtE PD T W.emb i ((ty i).win Gp S η))
    {C : Coord W I T} {C₀ : Coord W I W.one} (R : RealExt C C₀) (hE : R.Exact)
    (hses : IsSESLat (Qp := Qp) R.ι R.π) (hY : CrysLat PD R.Y) (e₀ : C₀.V)
    (hlift : ∀ c ∈ cuts, (R.ext hE).Lift e₀ c rr) :
    Formalism.ExponentWindows.E.PrimExt (R.ext hE) e₀ (cutsOf hC) j Gp rr
      (Formalism.ExponentWindows.E.HArc (gPar Gp S η) Gp S η (kdOf ty) (bbOf ty)) := by
  obtain ⟨hT, hO1, -⟩ := hH.2.1 T R.Y W.one R.ι R.π hses hY
  obtain ⟨h9, hM, hh, -, hpull, -, -, -⟩ := lat_items Q hY.2.2.2
    (box_of_kind (η_le_gPar Gp S η) hS fun i => jumps_ext hH R.ι R.π hses hY (hK i)) R.CY
  exact
    { lift := hlift
      p9 := h9
      p6 := extension_lattice_intersection R hE hses (Q.P6.2.2 T R.Y W.one R.ι R.π hT.2.2.2 hY.2.2.2 hO1.2.2.2)
      frobeniusBounded_after := fun c hc k h1 h2 => hM _ Gp (boxM_thin (hC.2.2.2.2 c hc k h1 h2)).le
      frobeniusCobounded_arc := fun c _ s _ => hh _ _ (boxH_le_HArc _ Gp S η ty c s)
      pullFree := fun c _ => hpull c j }

def UnitGen (W : LocWach PD LL O v n) (e : W.DD W.one) : Prop :=
  W.N W.one = Submodule.span (LetA O n) {e} ∧ W.φD W.one e = e ∧ (∀ g, W.γD W.one g e = e) ∧
    ∀ a : LetA O n, a • e = 0 → a = 0

theorem primUnit_of (hInj : I.Inj) (hFull : I.Full) {e : W.DD W.one} (he : UnitGen W e)
    (C₀ : Coord W I W.one) (e₀ : C₀.V) (he₀ : ∀ i, C₀.t i e₀ = (letE i : LetA O n) • e) :
    Formalism.ExponentWindows.E.PrimUnit (latOf C₀) e₀ := by
  obtain ⟨hN, hφ, hγ, hfree⟩ := he
  refine ⟨fun i => C₀.t_inj i ?_, fun i => C₀.t_inj i ?_, fun i => le_antisymm ?_ ?_, fun a ha => ?_⟩
  · rw [t_φ, he₀, he₀, φD_smulA, φA_letE, hφ]
  · rw [t_γ, he₀, γD_smulA, γA_letE, hγ]
  · intro x hx
    have hx' : C₀.t i x ∈ Submodule.span (LetA O n) {e} := by rw [← hN]; exact hx
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hx'
    have haΔ : a ∈ W.AΔ := by
      intro δ hδ
      have h1 := C₀.t_Δ i x δ hδ
      rw [← ha, γD_smulA, hγ, ← sub_eq_zero, ← sub_smul] at h1
      exact sub_eq_zero.1 (hfree _ h1)
    obtain ⟨f, hf⟩ := exists_ι_of_AΔ hFull haΔ i
    have hx2 : x = f • e₀ := by
      apply C₀.t_inj i
      rw [C₀.t_smul, he₀, smul_smul, ← mul_letE_eq a i f hf, ← C₀.t_letter i x, ← ha, smul_smul,
        mul_comm]
    rw [hx2]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · rw [Submodule.span_singleton_le_iff_mem, mem_N, he₀, hN]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)
  · have h1 := congrArg (C₀.t 0) ha
    rw [C₀.t_smul, C₀.t_zero, he₀, smul_smul] at h1
    have h2 := congrFun (hfree _ h1) 0
    have h3 : I.ι a = 0 := by simpa [letE] using h2
    exact hInj (by rw [h3, map_zero])

theorem unram_of (h : Function.Bijective (algebraMap K₀ K)) : Module.finrank K₀ K = 1 := by
  rw [← (AlgEquiv.ofBijective (Algebra.ofId K₀ K) h).toLinearEquiv.finrank_eq, Module.finrank_self]

theorem p_ne_zero_of (W : LocWach PD LL O v n) : ((PD.p : ℕ) : O) ≠ 0 := by
  intro h
  have h1 : ((PD.p : ℕ) : LL) = 0 := by
    rw [← map_natCast (algebraMap O LL), h, map_zero]
  have h2 := W.v_l
  rw [h1, AddValuation.map_zero] at h2
  exact WithTop.top_ne_one h2

end Formalism.MainNotions.WachCoordinates.Br
