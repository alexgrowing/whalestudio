import Formalism.SharpRestriction.LevelLetterCocycles.UniversalGeneralOfRestriction
import Formalism.SharpRestriction.LevelLetterCocycles.EvaluationAtUniformizerPower
import Formalism.SharpRestriction.LevelLetterCocycles.DualLemmaOfDeterminant
import Formalism.SharpRestriction.LevelLetterCocycles.DvOZeroHigh
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.RkMultVNonneg
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientImageDivisibility.FilDimOf

noncomputable section

open Classical Module Submodule

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.AdB

section Chain

variable {O : Type*} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O]
variable {ι M : Type*} [Fintype ι] [AddCommGroup M] [Module O M]

theorem canon (b : Basis ι O M) (P : Submodule O M) (T : Set ι) (h : P = span O (b '' T)) :
    P = span O (b '' {i | b i ∈ P}) := by
  have hT : T ⊆ {i | b i ∈ P} := fun i hi => by
    show b i ∈ P
    rw [h]; exact subset_span ⟨i, hi, rfl⟩
  apply le_antisymm
  · calc P = span O (b '' T) := h
      _ ≤ span O (b '' {i | b i ∈ P}) := span_mono (Set.image_mono hT)
  · rw [span_le]; rintro _ ⟨i, hi, rfl⟩; exact hi

theorem refine (b : Basis ι O M) (S : Set ι) (P : Submodule O M) (hP : P ≤ span O (b '' S))
    (hsat : Formalism.MainNotions.UnusedSlot80.UnivF.Sat P) :
    ∃ b' : Basis ι O M, (∀ i ∉ S, b' i = b i) ∧ span O (b' '' S) = span O (b '' S) ∧
      P = span O (b' '' {i | b' i ∈ P}) := by
  set Q := span O (b '' S) with hQdef
  have hli : LinearIndependent O (fun i : S => b i) :=
    b.linearIndependent.comp (fun i : S => (i : ι)) Subtype.val_injective
  have hQ : span O (Set.range fun i : S => b i) = Q := by rw [hQdef, Set.image_eq_range]
  let bQ : Basis S O Q := (Basis.span hli).map (LinearEquiv.ofEq _ _ hQ)
  let P' : Submodule O Q := P.comap Q.subtype
  have hP' : Formalism.MainNotions.UnusedSlot80.UnivF.Sat P' := by
    intro a x ha hx
    exact hsat a x ha (by simpa [P'] using hx)
  obtain ⟨c, S'', hS''⟩ := Formalism.MainNotions.UnusedSlot80.UnivF.adapted bQ P' hP'
  let f : ι → M := fun i => if h : i ∈ S then ((c ⟨i, h⟩ : Q) : M) else b i
  have hcQ : ∀ y ∈ Q, ∀ i ∉ S, b.repr y i = 0 := by
    intro y hy i hi
    rw [hQdef, Basis.mem_span_image] at hy
    by_contra h
    exact hi (hy (Finsupp.mem_support_iff.2 h))
  have hfQ : ∀ i ∈ S, f i ∈ Q := fun i hi => by simp only [f, dif_pos hi]; exact (c _).2
  have hli' : LinearIndependent O f := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have hout : ∀ i ∉ S, g i = 0 := by
      intro i₀ hi₀
      have h1 := congrArg (fun y => b.repr y i₀) hg
      simp only [map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
        map_zero, Finsupp.coe_zero, Pi.zero_apply] at h1
      rw [Finset.sum_eq_single i₀] at h1
      · simpa [f, dif_neg hi₀, Basis.repr_self] using h1
      · intro i _ hii
        by_cases hiS : i ∈ S
        · rw [hcQ _ (hfQ i hiS) i₀ hi₀, smul_zero]
        · simp [f, dif_neg hiS, Basis.repr_self, hii]
      · simp
    have e : ∑ i, g i • f i = ∑ j : S, g j • ((c j : Q) : M) := by
      rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun i => i ∈ S),
        Finset.sum_eq_zero (s := Finset.univ.filter (fun i => ¬ i ∈ S))
          (fun i hi => by rw [hout i (Finset.mem_filter.1 hi).2, zero_smul]), add_zero,
        Finset.sum_subtype (Finset.univ.filter (fun i => i ∈ S)) (p := fun i => i ∈ S) (by simp)]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [f, dif_pos j.2]
    have hin : ∑ j : S, g j • c j = 0 := by
      apply Subtype.ext
      rw [Submodule.coe_sum, Submodule.coe_zero]
      simp only [Submodule.coe_smul]
      rw [← e, hg]
    have hc := Fintype.linearIndependent_iff.1 c.linearIndependent _ hin
    intro i
    by_cases hiS : i ∈ S
    · exact hc ⟨i, hiS⟩
    · exact hout i hiS
  have hsp : ⊤ ≤ span O (Set.range f) := by
    rw [← b.span_eq, span_le]
    rintro _ ⟨i, rfl⟩
    by_cases hiS : i ∈ S
    · have hbQ : b i ∈ Q := subset_span ⟨i, hiS, rfl⟩
      have h1 : (⟨b i, hbQ⟩ : Q) ∈ span O (Set.range c) := by rw [c.span_eq]; trivial
      have h2 := Submodule.mem_map_of_mem (f := Q.subtype) h1
      rw [Submodule.map_span] at h2
      refine span_mono ?_ h2
      rintro _ ⟨y, ⟨j, rfl⟩, rfl⟩
      exact ⟨j.1, by simp [f, dif_pos j.2]⟩
    · exact subset_span ⟨i, by simp [f, dif_neg hiS]⟩
  let b' := Basis.mk hli' hsp
  have hb' : ∀ i, b' i = f i := Basis.mk_apply hli' hsp
  have hP2 : P = span O (b' '' (Subtype.val '' (S'' : Set S))) := by
    have hPQ : P = map Q.subtype P' := by
      show P = map Q.subtype (comap Q.subtype P)
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hP]
    rw [hPQ, hS'', Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨j.1, ⟨j, hj, rfl⟩, by rw [hb']; simp [f, dif_pos j.2]⟩
    · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
      exact ⟨c j, ⟨j, hj, rfl⟩, by rw [hb']; simp [f, dif_pos j.2]⟩
  refine ⟨b', fun i hi => by rw [hb']; simp [f, dif_neg hi], ?_, canon b' P _ hP2⟩
  have himg : b' '' S = Q.subtype '' Set.range c := by
    ext x
    constructor
    · rintro ⟨i, hi, rfl⟩
      exact ⟨c ⟨i, hi⟩, ⟨_, rfl⟩, by rw [hb']; simp [f, dif_pos hi]⟩
    · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
      exact ⟨j.1, j.2, by rw [hb']; simp [f, dif_pos j.2]⟩
  rw [himg, ← Submodule.map_span, c.span_eq, Submodule.map_subtype_top]

theorem chain (b : Basis ι O M) (F : ℕ → Submodule O M) (hF : ∀ k, F (k + 1) ≤ F k)
    (hsat : ∀ k, Formalism.MainNotions.UnusedSlot80.UnivF.Sat (F k)) (K : ℕ) :
    ∃ b' : Basis ι O M, ∀ k ≤ K, F k = span O (b' '' {i | b' i ∈ F k}) := by
  have hanti : Antitone F := antitone_nat_of_succ_le hF
  induction K with
  | zero =>
    obtain ⟨b', S, hS⟩ := Formalism.MainNotions.UnusedSlot80.UnivF.adapted b (F 0) (hsat 0)
    refine ⟨b', fun k hk => ?_⟩
    obtain rfl : k = 0 := by omega
    exact canon b' _ _ hS
  | succ K ih =>
    obtain ⟨b', hb'⟩ := ih
    obtain ⟨b'', hout, hspan, hP⟩ := refine b' {i | b' i ∈ F K} (F (K + 1))
      (by rw [← hb' K le_rfl]; exact hF K) (hsat _)
    refine ⟨b'', fun k hk => ?_⟩
    rcases Nat.lt_or_ge k (K + 1) with hlt | hge
    · have hkK : k ≤ K := by omega
      have hsub : {i | b' i ∈ F K} ⊆ {i | b' i ∈ F k} := fun i hi => hanti hkK hi
      have hD : b'' '' ({i | b' i ∈ F k} \ {i | b' i ∈ F K}) =
          b' '' ({i | b' i ∈ F k} \ {i | b' i ∈ F K}) :=
        Set.image_congr (fun i hi => hout i hi.2)
      have e1 : span O (b'' '' {i | b' i ∈ F k}) = span O (b' '' {i | b' i ∈ F k}) := by
        rw [← Set.union_sdiff_cancel hsub, Set.image_union, Set.image_union, span_union, span_union,
          hspan, hD]
      apply canon b'' (F k) {i | b' i ∈ F k}
      rw [e1]; exact hb' k hkK
    · obtain rfl : k = K + 1 := by omega
      exact hP

end Chain

section Count

variable {O LL : Type*} [CommRing O] [IsDomain O] [Field LL] [Algebra O LL] [IsFractionRing O LL]
variable {ι : Type*} [Fintype ι]

def toLLι : (ι → O) →ₗ[O] (ι → LL) :=
  LinearMap.pi fun k => (Algebra.linearMap O LL).comp (LinearMap.proj k)

theorem toLLι_apply (z : ι → O) (k : ι) : toLLι (LL := LL) z k = algebraMap O LL (z k) := rfl

theorem toLLι_inj : Function.Injective (toLLι (O := O) (LL := LL) (ι := ι)) := fun _ _ h =>
  funext fun k => IsFractionRing.injective O LL (congrFun h k)

def FF (G : Submodule LL (ι → LL)) : Submodule O (ι → O) :=
  (G.restrictScalars O).comap toLLι

theorem mem_FF (G : Submodule LL (ι → LL)) (z : ι → O) : z ∈ FF G ↔ toLLι z ∈ G := Iff.rfl

theorem clearι (y : ι → LL) : ∃ (a : O) (z : ι → O), a ≠ 0 ∧ toLLι z = a • y := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) Finset.univ y
  choose z hz using fun j => hb j (Finset.mem_univ j)
  refine ⟨b, z, nonZeroDivisors.ne_zero b.2, funext fun j => ?_⟩
  rw [toLLι_apply, hz j]
  rfl

theorem mem_of_smulι (P : Submodule LL (ι → LL)) {a : O} (ha : a ≠ 0) {y : ι → LL}
    (h : a • y ∈ P) : y ∈ P := by
  have hane : algebraMap O LL a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O LL)).2 ha
  have h2 : algebraMap O LL a • y ∈ P := by rw [algebraMap_smul]; exact h
  have h3 := P.smul_mem (algebraMap O LL a)⁻¹ h2
  rwa [smul_smul, inv_mul_cancel₀ hane, one_smul] at h3

theorem FF_sat (G : Submodule LL (ι → LL)) : Formalism.MainNotions.UnusedSlot80.UnivF.Sat (FF (O := O) G) := by
  intro a z ha hz
  rw [mem_FF, map_smul] at hz
  exact mem_of_smulι G ha hz

theorem FF_mono {G G' : Submodule LL (ι → LL)} (h : G ≤ G') : FF (O := O) G ≤ FF G' :=
  fun _ hz => h hz

theorem card_FF (G : Submodule LL (ι → LL)) (b' : Basis ι O (ι → O))
    (h : FF G = span O (b' '' {i | b' i ∈ FF G})) :
    finrank LL G = (Finset.univ.filter fun i => b' i ∈ FF (O := O) G).card := by
  let g : (Finset.univ.filter fun i => b' i ∈ FF (O := O) G) → (ι → LL) := fun j => toLLι (b' j)
  have hliO : LinearIndependent O g := by
    have h1 := b'.linearIndependent.comp (fun j : (Finset.univ.filter fun i => b' i ∈ FF (O := O) G) => (j : ι))
      Subtype.val_injective
    have h2 := h1.map' (toLLι (O := O) (LL := LL) (ι := ι)) (LinearMap.ker_eq_bot.2 toLLι_inj)
    exact h2
  have hli : LinearIndependent LL g := (LinearIndependent.iff_fractionRing O LL).1 hliO
  have hspan : span LL (Set.range g) = G := by
    apply le_antisymm
    · rw [span_le]
      rintro _ ⟨j, rfl⟩
      exact (Finset.mem_filter.1 j.2).2
    · intro y hy
      obtain ⟨a, z, ha, hz⟩ := clearι (O := O) y
      have hzF : z ∈ FF G := by
        rw [mem_FF, hz]; exact (G.restrictScalars O).smul_mem a hy
      rw [h] at hzF
      have h2 : toLLι (LL := LL) z ∈ span O (toLLι (LL := LL) '' (b' '' {i | b' i ∈ FF G})) := by
        rw [← Submodule.map_span]; exact mem_map_of_mem hzF
      have h3 : toLLι (LL := LL) '' (b' '' {i | b' i ∈ FF G}) ⊆ Set.range g := by
        rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
        exact ⟨⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩, rfl⟩
      have h4 : a • y ∈ span LL (Set.range g) := by
        rw [← hz]; exact span_le_restrictScalars O LL _ (span_mono h3 h2)
      exact mem_of_smulι _ ha h4
  calc finrank LL G = finrank LL (span LL (Set.range g)) := by rw [hspan]
    _ = Fintype.card _ := finrank_span_eq_card hli
    _ = _ := Fintype.card_coe _

end Count

end Formalism.MainNotions.RamifiedCoefficientChains.S9.AdB

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.AdL

open Module Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem frame_of_isBas (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n) {d : ℕ}
    (e : Fin d → W.DD T) (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T c e) : Formalism.MainNotions.LiftingTheory.IsFrameΔ W T c e := by
  have hl : ∀ m, (letE c : LetA O n) • e m = e m := fun m => (he.1 m).2.1
  have hNl : ∀ x, x ∈ W.N T → (letE c : LetA O n) • x = x → x ∈ W.Nl T c := fun x hx hxl =>
    ⟨x, hx, by rw [LinearMap.smul_apply, LinearMap.id_apply]; exact hxl⟩
  refine ⟨fun m => ⟨⟨(he.1 m).1, (he.1 m).2.2⟩, hNl _ (he.1 m).1 (hl m)⟩, fun x hx => ?_⟩
  obtain ⟨⟨hxN, hxΔ⟩, hxl⟩ := hx
  have hxl' : (letE c : LetA O n) • x = x := by
    obtain ⟨y, -, rfl⟩ := hxl
    rw [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self']
  obtain ⟨f, hf, hfu⟩ := he.2 x hxN ⟨hxl', hxΔ⟩
  have hletΔ : (letE c : LetA O n) ∈ W.AΔ := fun δ _ => Formalism.MainNotions.RamifiedCoefficientChains.S9.NinQ.γA_letE W δ c
  refine ⟨fun m => letE c * Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f m),
    ⟨fun m => ⟨W.AΔ.mul_mem hletΔ (Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_mem_invariants W hR _),
      by rw [← mul_assoc, Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.letE_mul_self']⟩, ?_⟩, ?_⟩
  · rw [hf]
    refine Finset.sum_congr rfl fun m _ => ?_
    dsimp only
    rw [mul_comm, ← smul_smul, hl m]
  · rintro a ⟨ha, hxa⟩
    have hg : ∀ m, ∃ g : PowerSeries O, a m * letE c = Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W g * letE c :=
      fun m => Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.invariant_letter_eq_evaluation W hR (ha m).1 c
    choose g hg using hg
    have hx2 : x = ∑ m, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (g m) • e m := by
      rw [hxa]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [← (ha m).2, mul_comm, hg m, ← smul_smul, hl m]
    have hgf := hfu g hx2
    funext m
    rw [← (ha m).2, mul_comm, hg m, hgf, mul_comm]

theorem isBas_change (hR : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W) (T : LocLat G Qp LL O) (c : ZMod n) {r : ℕ}
    (e : Fin r → W.DD T) (he : Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T c e) (Bs : Basis (Fin r) O (Fin r → O)) :
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.IsBas W T c (fun t => ∑ k, Bs t k • e k) := by
  let C : Fin r → Fin r → O := fun k t => Bs.repr (Pi.single k 1) t
  have hCB : ∀ k k'', ∑ t, C k t * Bs t k'' = if k = k'' then 1 else 0 := by
    intro k k''
    have h1 := congrFun (Bs.sum_repr (Pi.single k 1)) k''
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h1
    rw [h1, Pi.single_apply]
    by_cases h : k = k'' <;> simp [h, eq_comm]
  have hBC : ∀ t t'', ∑ k, Bs t k * C k t'' = if t = t'' then 1 else 0 := by
    intro t t''
    have h1 : Bs t = ∑ k, Bs t k • (Pi.single k (1 : O) : Fin r → O) := by
      ext k'
      simp [Finset.sum_apply, Pi.single_apply]
    have h2 := congrArg (fun y => Bs.repr y t'') h1
    simp only [Basis.repr_self, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul, Finsupp.single_apply] at h2
    rw [← h2]
  let e' : Fin r → W.DD T := fun t => ∑ k, Bs t k • e k
  have htr : ∀ f : Fin r → PowerSeries O, ∑ t, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (f t) • e' t =
      ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (∑ t, f t * algebraMap O (PowerSeries O) (Bs t k)) • e k := fun f =>
    Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.transfer W hR T c e (fun k => (he.1 k).2.1) e'
      (fun t k => algebraMap O (LetA O n) (Bs t k)) (fun t => by simp only [e', algebraMap_smul])
      (fun t k => algebraMap O (PowerSeries O) (Bs t k))
      (fun t k => by rw [Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.evaluation_eq_homomorphism W hR, AlgHom.commutes]) f
  refine ⟨fun t => ⟨?_, ?_, ?_⟩, fun x hx hxD => ?_⟩
  · exact Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (he.1 k).1
  · show (letE c : LetA O n) • ∑ k, Bs t k • e k = ∑ k, Bs t k • e k
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [smul_comm, (he.1 k).2.1]
  · intro δ hδ
    show W.γD T δ (∑ k, Bs t k • e k) = ∑ k, Bs t k • e k
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul, (he.1 k).2.2 δ hδ]
  · obtain ⟨f, hf, hfu⟩ := he.2 x hx hxD
    refine ⟨fun t => ∑ k, f k * algebraMap O (PowerSeries O) (C k t), ?_, fun a ha => ?_⟩
    · show x = ∑ t, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (∑ k, f k * algebraMap O (PowerSeries O) (C k t)) • e' t
      rw [htr, hf]
      refine Finset.sum_congr rfl fun k _ => ?_
      congr 2
      have e1 : ∑ t, (∑ k', f k' * algebraMap O (PowerSeries O) (C k' t)) *
          algebraMap O (PowerSeries O) (Bs t k) =
          ∑ k', f k' * algebraMap O (PowerSeries O) (∑ t, C k' t * Bs t k) := by
        simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [e1]
      simp [hCB]
    · have hf' : x = ∑ k, Formalism.MainNotions.RamifiedCoefficientChains.Sh.at0 W (∑ t, a t * algebraMap O (PowerSeries O) (Bs t k)) • e k := by
        rw [ha]; exact htr a
      have hfa := hfu _ hf'
      funext t''
      rw [← hfa]
      have e1 : ∑ k, (∑ t, a t * algebraMap O (PowerSeries O) (Bs t k)) *
          algebraMap O (PowerSeries O) (C k t'') =
          ∑ t, a t * algebraMap O (PowerSeries O) (∑ k, Bs t k * C k t'') := by
        simp only [Finset.sum_mul, map_sum, map_mul, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
      rw [e1]
      simp [hBC]

theorem cmpD_sumO (T : LocLat G Qp LL O) {r : ℕ} (z : Fin r → O) (e : Fin r → W.DD T)
    (he : ∀ k, e k ∈ W.N T) :
    Formalism.MainNotions.ArcLiftingSetup.cmpD W T (∑ k, z k • e k) = ∑ k, algebraMap O LL (z k) • Formalism.MainNotions.ArcLiftingSetup.cmpD W T (e k) := by
  have hmem : ∑ k, z k • e k ∈ W.N T := Submodule.sum_mem _ fun k _ => Submodule.smul_of_tower_mem _ _ (he k)
  rw [Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T hmem]
  have e1 : (⟨∑ k, z k • e k, hmem⟩ : W.N T) = ∑ k, z k • (⟨e k, he k⟩ : W.N T) := by
    apply Subtype.ext
    simp
  rw [e1, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [W.cmp_smul, Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T (he k)]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.AdL

noncomputable section

open Classical

namespace Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM

open Module Submodule Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.RamifiedCoefficientChains Formalism.MainNotions.RamifiedCoefficientChains.S9 Formalism.MainNotions.RamifiedCoefficientChains.S9.ShB TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n]
    (W : LocWach PD LL O v n)

theorem filLev_anti (T : LocLat G Qp LL O) (i : ZMod n) :
    Antitone fun a : ℤ => Formalism.MainNotions.WachCoordinates.FilLev W T i 0 a := by
  intro a b hab
  exact Submodule.map_mono (Submodule.map_mono
    (inf_le_inf_right _ fun x hx => Formalism.MainNotions.UnusedSlot80.LevR.filCris_anti T.ρ hab hx))

theorem filLev_zero_high (hbij : Function.Bijective (algebraMap K₀ K)) (T : LocLat G Qp LL O)
    (i : ZMod n) (H : ℕ)
    (hJ : ∀ τ : K →ₐ[Qp] LL, Formalism.MainNotions.LiftingTheory.Over W τ i → ∀ a, IsJumpV PD T.ρ τ a → a ≤ (H : ℤ))
    (u : ℤ) (hu : (H : ℤ) < u) : Formalism.MainNotions.WachCoordinates.FilLev W T i 0 u = ⊥ := by
  rw [eq_bot_iff]
  rintro z ⟨y, ⟨x, ⟨hxF, hxD⟩, rfl⟩, rfl⟩
  obtain ⟨τ, hτ, hover⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hbij i
  have hx0 := Formalism.MainNotions.UnusedSlot80.LevC.fil_high W T i τ hover hbij.2 H (hJ τ hτ) u hu (by simpa using hxD) hxF
  simp [hx0]

theorem ring_clauses_at_uniformizer (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W) (T : LocLat G Qp LL O)
    (hT : IsCrys PD T.ρ) : Formalism.MainNotions.RamifiedCoefficientChains.Sh.BT.Ring9 W := by
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T hT hA.2.1 hA.2.2
  obtain ⟨hring, -⟩ := h9' hfin1
  exact hring

theorem adaptBas_of (hE : Formalism.MainNotions.RamifiedCoefficientChains.DcrisExactStrict PD LL) (hC : Formalism.MainNotions.RamifiedCoefficientChains.CrysSubQuot PD LL)
    (hQ : Formalism.MainNotions.RamifiedCoefficientChains.DdREqDcris PD LL) (h3 : Formalism.MainNotions.DeltaInvariantLattices.P3W W) (h5 : Formalism.MainNotions.DeltaInvariantLattices.P5W W)
    (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hV : Formalism.MainNotions.WachCoordinates.Br.ValRing (LL := LL) O v) : AdaptBas W := by
  intro d T₁ T₂ F b S η m hS i hi
  have hie : (i.val + d) % 2 = 0 := (Finset.mem_filter.1 hi).2
  have hCA : Formalism.MainNotions.LiftingTheory.CaseA W := hS.1
  have hT : IsCrys PD T₂.ρ := hS.2.2.2.2.2.1.2.1
  obtain ⟨hdom, hdvr, hfr⟩ := hS.2.2.2.1
  have := hdom; have := hdvr; have := hfr
  have hR9 := ring_clauses_at_uniformizer W h9 hCA T₂ hT
  have hηb := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_eta_lt W hS i

  obtain ⟨e, he⟩ := (Formalism.MainNotions.RamifiedCoefficientChains.Sh.basTool_of W h9 hCA T₂ hT (i - 1)).1
  have hfr' := AdL.frame_of_isBas W hR9 T₂ (i - 1) e he
  have hfin1 : finrank K₀ K = 1 := by
    have := (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hCA.1).finrank_eq
    rw [Module.finrank_self] at this
    exact this.symm
  obtain ⟨-, -, h9'⟩ := h9 T₂ hT hCA.2.1 hCA.2.2
  have hmod := (h9' hfin1).2
  obtain ⟨hli0, hsp0⟩ := Formalism.MainNotions.UnusedSlot80.ArcF.frame_basis W hCA.2.1 hV T₂ (h3 T₂ hT)
    (h5 T₂ _ _ hT (Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumpsLet₂ W hE hC hQ hS)) hmod (i - 1) 1 e hfr'
  let w : Fin (finrank LL T₂.V) → T₂.V ⊗[Qp] BdR := fun k =>
    ιV PD (LL := LL) (V := T₂.V) (Formalism.MainNotions.ArcLiftingSetup.dv W T₂ 1 e (Pi.single k 1))
  have hliw : LinearIndependent LL w :=
    hli0.map' (ιV PD (LL := LL) (V := T₂.V)) (LinearMap.ker_eq_bot.2 Formalism.MainNotions.UnusedSlot80.LevR.ιV_inj)
  let Ψ := Fintype.linearCombination LL w
  have hΨ : ∀ y, Ψ y = ∑ k, y k • w k := fun y => Fintype.linearCombination_apply LL w y
  have hΨinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    funext k
    exact Fintype.linearIndependent_iff.1 hliw y (by rw [← hΨ]; exact hy) k
  have hFilR : ∀ u, Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 u ≤ LinearMap.range Ψ := by
    intro u z hz
    obtain ⟨y, ⟨x, ⟨-, hxD⟩, rfl⟩, rfl⟩ := hz
    have hxD' : x ∈ DcrisL PD T₂.ρ (W.emb (i - 1 + ((1 : ℕ) : ZMod n))) := by
      rw [show i - 1 + ((1 : ℕ) : ZMod n) = i by push_cast; ring]; simpa using hxD
    rw [← hsp0, mem_span_range_iff_exists_fun] at hxD'
    obtain ⟨c, hc⟩ := hxD'
    refine ⟨c, ?_⟩
    rw [hΨ]
    simp only [w, ← map_smul, ← map_sum, hc]
    simp

  let Gs : ℤ → Submodule LL (Fin (finrank LL T₂.V) → LL) := fun u => (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 u).comap Ψ
  have hGfin : ∀ u, finrank LL (Gs u) = finrank LL (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 u) := by
    intro u
    have hmap : (Gs u).map Ψ = Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 u := by
      rw [Submodule.map_comap_eq, inf_eq_right.2 (hFilR u)]
    rw [← hmap]
    exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective Ψ hΨinj (Gs u))
  have hGanti : Antitone Gs := fun a b hab => Submodule.comap_mono (filLev_anti W T₂ i hab)

  let Fch : ℕ → Submodule O (Fin (finrank LL T₂.V) → O) := fun k => AdB.FF (O := O) (Gs (-(η : ℤ) + k))
  obtain ⟨b', hb'⟩ := AdB.chain (Pi.basisFun O (Fin (finrank LL T₂.V))) Fch
    (fun k => AdB.FF_mono (hGanti (by push_cast; omega))) (fun k => AdB.FF_sat _) (2 * η + 1)
  let Sset : ℤ → Finset (Fin (finrank LL T₂.V)) := fun u =>
    Finset.univ.filter fun j => b' j ∈ AdB.FF (O := O) (Gs u)
  have hcard : ∀ u : ℤ, -(η : ℤ) ≤ u → u ≤ η + 1 →
      (Sset u).card = finrank LL (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 u) := by
    intro u h1 h2
    obtain ⟨k, rfl⟩ : ∃ k : ℕ, u = -(η : ℤ) + k := ⟨(u + η).toNat, by omega⟩
    rw [← hGfin]
    exact (AdB.card_FF (Gs _) b' (hb' k (by omega))).symm
  have hSanti : ∀ u u', u ≤ u' → Sset u' ⊆ Sset u := fun u u' h j hj => by
    simp only [Sset, Finset.mem_filter] at hj ⊢
    exact ⟨hj.1, AdB.FF_mono (hGanti h) hj.2⟩

  have hbot : Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 ((η : ℤ) + 1) = ⊥ := by
    refine filLev_zero_high W hCA.1 T₂ i η (fun τ hτ a ha => ?_) _ (by omega)
    have hw := Formalism.MainNotions.N.Pv.LocalLengthBound.rk_jumps₂ W hE hC hQ hS i τ hτ a ha
    unfold JumpWinS at hw
    rw [if_pos hie] at hw
    simp only [Set.mem_union, Set.mem_Icc] at hw
    push_cast at hw
    omega
  have hFF_top : ∀ j, j ∉ Sset ((η : ℤ) + 1) := by
    intro j hj
    have hj' := (Finset.mem_filter.1 hj).2
    rw [AdB.mem_FF] at hj'
    have h0 : Ψ (AdB.toLLι (LL := LL) (b' j)) ∈ (⊥ : Submodule LL (T₂.V ⊗[Qp] BdR)) := by
      rw [← hbot]; exact hj'
    rw [Submodule.mem_bot] at h0
    have h1 : AdB.toLLι (LL := LL) (b' j) = AdB.toLLι (LL := LL) (0 : Fin (finrank LL T₂.V) → O) := by
      rw [map_zero]; exact hΨinj (h0.trans (map_zero Ψ).symm)
    exact b'.ne_zero j (AdB.toLLι_inj h1)

  let L := Sset (-(η : ℤ))
  have hmr : L.card ≤ finrank LL T₂.V := by
    simpa using Finset.card_le_univ L
  let lev : Fin (finrank LL T₂.V) → ℤ := fun j =>
    if h : ((Finset.Icc (-(η : ℤ)) η).filter fun u => j ∈ Sset u).Nonempty then
      ((Finset.Icc (-(η : ℤ)) η).filter fun u => j ∈ Sset u).max' h else -(η : ℤ)
  have hlev : ∀ j ∈ L, (-(η : ℤ) ≤ lev j ∧ lev j ≤ η) ∧
      ∀ u, -(η : ℤ) ≤ u → u ≤ η + 1 → (j ∈ Sset u ↔ u ≤ lev j) := by
    intro j hj
    have hne : ((Finset.Icc (-(η : ℤ)) η).filter fun u => j ∈ Sset u).Nonempty :=
      ⟨-(η : ℤ), Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨le_rfl, by omega⟩, hj⟩⟩
    have hl : lev j = ((Finset.Icc (-(η : ℤ)) η).filter fun u => j ∈ Sset u).max' hne := dif_pos hne
    have hmem := Finset.max'_mem _ hne
    rw [hl]
    obtain ⟨hIcc, hjS⟩ := Finset.mem_filter.1 hmem
    refine ⟨Finset.mem_Icc.1 hIcc, fun u hu1 hu2 => ⟨fun hju => ?_, fun hle => hSanti _ _ hle hjS⟩⟩
    by_cases hu : u ≤ η
    · exact Finset.le_max' _ u (Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hu1, hu⟩, hju⟩)
    · exfalso
      obtain rfl : u = (η : ℤ) + 1 := by omega
      exact hFF_top j hju

  have hLc : Lᶜ.card = finrank LL T₂.V - L.card := by rw [Finset.card_compl, Fintype.card_fin]
  let eL := L.orderEmbOfFin (rfl : L.card = L.card)
  let eC := Lᶜ.orderEmbOfFin hLc
  let fσ : Fin (finrank LL T₂.V) → Fin (finrank LL T₂.V) := fun t =>
    if h : (t : ℕ) < L.card then eL ⟨t, h⟩ else eC ⟨t - L.card, by have := t.2; omega⟩
  have hfσinj : Function.Injective fσ := by
    intro t t' h
    simp only [fσ] at h
    split_ifs at h with h1 h2 h2
    · have h3 := eL.injective h
      ext; simpa using congrArg Fin.val h3
    · exfalso
      have h3 := L.orderEmbOfFin_mem rfl ⟨t, h1⟩
      have h4 := Lᶜ.orderEmbOfFin_mem hLc ⟨t' - L.card, by have := t'.2; omega⟩
      rw [← h] at h4
      exact (Finset.mem_compl.1 h4) h3
    · exfalso
      have h3 := Lᶜ.orderEmbOfFin_mem hLc ⟨t - L.card, by have := t.2; omega⟩
      have h4 := L.orderEmbOfFin_mem rfl ⟨t', h2⟩
      rw [h] at h3
      exact (Finset.mem_compl.1 h3) h4
    · have h3 := eC.injective h
      have h4 := congrArg Fin.val h3
      simp only at h4
      ext; omega
  let σ := Equiv.ofBijective fσ (Finite.injective_iff_bijective.1 hfσinj)
  let b'' := b'.reindex σ.symm
  have hb'' : ∀ t, b'' t = b' (fσ t) := fun t => by
    simp [b'', Basis.reindex_apply, σ]
  have hσL : ∀ j : Fin L.card, fσ (Fin.castLE hmr j) = eL j := fun j => by
    simp [fσ, j.2]
  have hLj : ∀ j : Fin L.card, eL j ∈ L := fun j => L.orderEmbOfFin_mem rfl j
  refine ⟨fun t => ∑ k, b'' t k • e k, L.card, fun j => lev (eL j),
    AdL.isBas_change W hR9 T₂ (i - 1) e he b'', ?_, hmr, fun j => (hlev _ (hLj j)).1, ?_, ?_⟩
  ·
    obtain ⟨τ, hτ, -⟩ := Formalism.MainNotions.UnusedSlot80.LevC.tau_over W hCA.1 i
    have hFD := (Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ hCA T₂ hT i τ hτ).2 (-(η : ℤ)) ((η : ℤ) + 1) (by omega)
    rw [hbot, finrank_bot, Finset.Ico_add_one_right_eq_Icc] at hFD
    have hm := hS.2.2.2.2.2.2.2.1 i τ hτ
    have hc := hcard (-(η : ℤ)) le_rfl (by omega)
    have : (L.card : ℤ) ≤ m := by
      show ((Sset (-(η : ℤ))).card : ℤ) ≤ m
      rw [hc]; push_cast at hFD; linarith
    exact_mod_cast this
  ·
    intro j hj
    have he' : (∑ k, b'' (Fin.castLE hmr j) k • e k) = ∑ k, b'' (Fin.castLE hmr j) k • e k := rfl
    have hv : ιV PD (LL := LL) (V := T₂.V) (φVB PD (LL := LL) (V := T₂.V) (W.cmp T₂ ⟨_, hj⟩)) =
        Ψ (AdB.toLLι (LL := LL) (b'' (Fin.castLE hmr j))) := by
      rw [← Formalism.MainNotions.UnusedSlot80.ArcF.cmpD_of_mem W T₂ hj, AdL.cmpD_sumO W T₂ _ e (fun k => (he.1 k).1), hΨ,
        map_sum, map_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_smul, map_smul, AdB.toLLι_apply]
      simp only [w, Formalism.MainNotions.UnusedSlot80.ArcF.dv_single, pow_one]
    rw [hv]
    have hmemS : eL j ∈ Sset (lev (eL j)) :=
      ((hlev _ (hLj j)).2 (lev (eL j)) (hlev _ (hLj j)).1.1 (by have := (hlev _ (hLj j)).1.2; omega)).2 le_rfl
    have hFFm : b'' (Fin.castLE hmr j) ∈ AdB.FF (O := O) (Gs (lev (eL j))) := by
      rw [hb'', hσL]; exact (Finset.mem_filter.1 hmemS).2
    exact hFFm
  ·
    intro τ hτ
    have hFDτ := (Formalism.MainNotions.N.Pv.LocalLengthBound.filDim_of W hQ hCA T₂ hT i τ hτ).2
    have hmult : ∀ x : ℤ, multV PD T₂.ρ τ x =
        (finrank LL (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 x) : ℤ) - finrank LL (Formalism.MainNotions.WachCoordinates.FilLev W T₂ i 0 (x + 1)) := by
      intro x
      rw [hFDτ x (x + 1) (by omega), Finset.Ico_add_one_right_eq_Icc, Finset.Icc_self, Finset.sum_singleton]
    have hsumL : ∑ j : Fin L.card, (((b i + S : ℕ) : ℤ) + lev (eL j)) =
        ∑ x ∈ L, (((b i + S : ℕ) : ℤ) + lev x) := by
      have h1 := Finset.sum_map (Finset.univ : Finset (Fin L.card)) eL.toEmbedding
        (fun x => (((b i + S : ℕ) : ℤ) + lev x))
      have h2 : (Finset.univ : Finset (Fin L.card)).map eL.toEmbedding = L :=
        Finset.map_orderEmbOfFin_univ L rfl
      rw [h2] at h1
      exact h1.symm
    have hmaps : ∀ x ∈ L, lev x ∈ Finset.Icc (-(η : ℤ)) η := fun x hx => Finset.mem_Icc.2 (hlev x hx).1
    rw [hsumL, ← Finset.sum_fiberwise_of_maps_to hmaps]
    unfold Formalism.MainNotions.RamifiedCoefficientChains.S9.Cut.lowSum
    apply le_of_eq
    refine Finset.sum_congr rfl fun x hx => ?_
    obtain ⟨hx1, hx2⟩ := Finset.mem_Icc.1 hx
    rw [Finset.sum_congr rfl (fun y hy => by rw [(Finset.mem_filter.1 hy).2]), Finset.sum_const, nsmul_eq_mul]
    have hfib : L.filter (fun y => lev y = x) = Sset x \ Sset (x + 1) := by
      ext y
      simp only [Finset.mem_filter, Finset.mem_sdiff]
      constructor
      · rintro ⟨hyL, hyx⟩
        refine ⟨((hlev y hyL).2 x hx1 (by omega)).2 (le_of_eq hyx.symm), fun h => ?_⟩
        have := ((hlev y hyL).2 (x + 1) (by omega) (by omega)).1 h
        omega
      · rintro ⟨hyx, hyx1⟩
        have hyL : y ∈ L := hSanti _ _ hx1 hyx
        refine ⟨hyL, ?_⟩
        have a1 := ((hlev y hyL).2 x hx1 (by omega)).1 hyx
        have a2 : ¬ (x + 1 ≤ lev y) := fun h => hyx1 (((hlev y hyL).2 (x + 1) (by omega) (by omega)).2 h)
        omega
    rw [hfib, Finset.card_sdiff_of_subset (hSanti _ _ (by omega)),
      Nat.cast_sub (Finset.card_le_card (hSanti _ _ (by omega))), hcard x hx1 (by omega),
      hcard (x + 1) (by omega) (by omega), hmult x]

end Formalism.MainNotions.RamifiedCoefficientChains.S9.AdM
