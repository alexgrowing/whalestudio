import Formalism.SharpRestriction.LevelLetterCocycles.FinalLevelsOf
import Formalism.SharpRestriction.LevelLetterCocycles.LevelKernelDetection.PfLvBasisCmp

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.MainNotions.WachCoordinates Formalism.MainNotions.WachCoordinates.Br Formalism.ExponentWindows Formalism.ExponentWindows.G Formalism.MainNotions.N.Ln03 TensorProduct

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL : Type} [Field LL] [Algebra Qp LL]
    {O : Type} [CommRing O] [Algebra O LL] [TopologicalSpace LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ} [NeZero n] {W : LocWach PD LL O v n}
    {hR : Ring9 W}

theorem span_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {r : ℕ} {e : Fin r → C.V}
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) :
    Submodule.span (PowerSeries O) (Set.range e) = (latOf C).N (c - (ell : ZMod n)) := by
  have h : e = ((latOf C).N (c - (ell : ZMod n))).subtype ∘ hBasis := funext fun k => (hBasis_e k).symm
  rw [h, Set.range_comp, Submodule.span_image, hBasis.span_eq, Submodule.map_top,
    Submodule.range_subtype]

theorem ind_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {r : ℕ} {e : Fin r → C.V}
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) :
    LinearIndependent (PowerSeries O) e := by
  have h : e = ((latOf C).N (c - (ell : ZMod n))).subtype ∘ hBasis := funext fun k => (hBasis_e k).symm
  rw [h]
  exact hBasis.linearIndependent.map' _ (Submodule.ker_subtype _)

section abelian₂

variable {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {i : ZMod n} {r : ℕ} {e : Fin r → C.V}

theorem lvBasis_e_mem (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (k : Fin r) : C.t i (e k) ∈ W.N T := by
  rw [← hBasis_e k]
  exact (hBasis k).2

theorem lvBasis_t_sum (x : Fin r → C.V) : C.t i (∑ l, x l) = ∑ l, C.t i (x l) := by
  have h : ∀ y, C.t i y = ((DDl W T i).subtype.comp (C.θ i).toAddMonoidHom) y := fun _ => rfl
  simp only [h, map_sum]

theorem lvBasis_cmp_sum {m : ℕ} (f : Fin m → W.DD T) (hf : ∀ l, f l ∈ W.N T) (hs : ∑ l, f l ∈ W.N T) :
    W.cmp T ⟨∑ l, f l, hs⟩ = ∑ l, W.cmp T ⟨f l, hf l⟩ := by
  have h : (⟨∑ l, f l, hs⟩ : ↥(W.N T)) = ∑ l, ⟨f l, hf l⟩ := Subtype.ext (by simp)
  rw [h, map_sum]

theorem lvBasis_smul_letter {a a' : LetA O n} (h : a i = a' i) {x : W.DD T}
    (hx : (letE i : LetA O n) • x = x) : a • x = a' • x := by
  have e : a * letE i = a' * letE i := by
    funext m
    by_cases hm : m = i
    · subst hm
      simp [letE, h]
    · simp [letE, hm]
  rw [← hx, smul_smul, smul_smul, e]

theorem lvBasis_expand (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) {w : W.DD T} (hw : w ∈ W.N T)
    (hwl : (letE i : LetA O n) • w = w) (hwΔ : ∀ δ ∈ W.DelF, W.γD T δ w = w) :
    ∃ g : Fin r → PowerSeries O, w = ∑ l, (baseIdOf hR).d (g l) • C.t i (e l) := by
  obtain ⟨z, hz⟩ := C.t_surj i w hwl hwΔ
  have hzN : z ∈ (latOf C).N i := by
    show C.t i z ∈ W.N T
    rw [hz]
    exact hw
  refine ⟨fun l => hBasis.repr ⟨z, hzN⟩ l, ?_⟩
  have hz' : ∑ l, hBasis.repr ⟨z, hzN⟩ l • e l = z := by
    have h := congrArg Subtype.val (hBasis.sum_repr ⟨z, hzN⟩)
    simpa only [Submodule.coe_sum, Submodule.coe_smul, hBasis_e] using h
  rw [← hz]
  conv_lhs => rw [← hz']
  rw [lvBasis_t_sum]
  exact Finset.sum_congr rfl fun l _ => C.t_smul i _ _

theorem lvBasis_regroup {m : ℕ} (b : Fin m → W.DD T) (g : Fin m → Fin r → PowerSeries O)
    (hg : ∀ j, (letE i : LetA O n) • b j = ∑ l, (baseIdOf hR).d (g j l) • C.t i (e l))
    (α : Fin m → LetA O n) :
    (letE i : LetA O n) • ∑ j, α j • b j =
      ∑ l, (∑ j, α j * (baseIdOf hR).d (g j l)) • C.t i (e l) := by
  simp only [Finset.smul_sum, smul_comm (letE i : LetA O n) (α _), hg, smul_smul, Finset.sum_smul]
  exact Finset.sum_comm

theorem lvBasis_cmp_e_letter (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (k : Fin r) :
    W.cmp T ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩ ∈ DcrisL PD T.ρ (W.emb i) := by
  have e1 : ((letE i : LetA O n) • (⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩ : ↥(W.N T))) =
      ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩ := Subtype.ext (C.t_letter i (e k))
  rw [← e1]
  exact W.cmp_letter T i _

theorem lvBasis_letter_le {π' : LetA O n} (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) {d : T.V ⊗[Qp] B} (hd : d ∈ DcrisL PD T.ρ (W.emb i)) :
    d ∈ Submodule.span LL
      (Set.range fun k => W.cmp T ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩) := by
  obtain ⟨⟨m, b, hbN, huniq, -⟩, -⟩ := hP9
  have hb : ∀ j, ∃ g : Fin r → PowerSeries O,
      (letE i : LetA O n) • b j = ∑ l, (baseIdOf hR).d (g l) • C.t i (e l) := fun j =>
    lvBasis_expand hBasis hBasis_e ((W.N T).smul_mem _ (hbN j).1) (lvBasis_letE_idem i _)
      (fun δ hδ => by rw [γD_smulA W, γA_letE W, (hbN j).2 δ hδ])
  choose g hg using hb
  have hm := lvBasis_e_mem hBasis hBasis_e
  refine Submodule.span_le.2 ?_ (lvBasis_letter_span hP3.2.1 i hd)
  rintro _ ⟨x, rfl⟩
  obtain ⟨α, hα, -⟩ := huniq _ x.2
  have hy : (letE i : LetA O n) • (x : W.DD T) =
      ∑ l, (∑ j, α j * (baseIdOf hR).d (g j l)) • C.t i (e l) := by
    rw [hα]
    exact lvBasis_regroup b g hg α
  have hmem : ∀ l, (∑ j, α j * (baseIdOf hR).d (g j l)) • C.t i (e l) ∈ W.N T :=
    fun l => (W.N T).smul_mem _ (hm l)
  have e0 : W.cmp T ((letE i : LetA O n) • x) =
      W.cmp T ⟨(letE i : LetA O n) • (x : W.DD T), (W.N T).smul_mem _ x.2⟩ := rfl
  dsimp only
  rw [SetLike.mem_coe, e0, lvBasis_cmp_congr _ (Submodule.sum_mem _ fun l _ => hmem l) hy,
    lvBasis_cmp_sum _ hmem]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [lvBasis_cmp_smul_letter (hm l) i (C.t_letter i (e l))]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨l, rfl⟩)

theorem lvBasis_kernel {π' : LetA O n} (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (o : Fin r → O)
    (h0 : ∑ k, algebraMap O LL (o k) • W.cmp T ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩ = 0) :
    ∀ l, o l = 0 := by
  obtain ⟨⟨m, b, hbN, huniq, hΔ⟩, -⟩ := hP9
  have hm := lvBasis_e_mem hBasis hBasis_e
  have hoN : ∀ k, o k • C.t i (e k) ∈ W.N T := fun k => (W.N T).smul_of_tower_mem (o k) (hm k)
  have hwN : ∑ k, o k • C.t i (e k) ∈ W.N T := Submodule.sum_mem _ fun k _ => hoN k
  have hcw : W.cmp T ⟨_, hwN⟩ = 0 := by
    rw [lvBasis_cmp_sum _ hoN, ← h0]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← W.cmp_smul]
    rfl
  obtain ⟨y, hyN, hy⟩ := Submodule.mem_map.1 (hP3.1 ⟨_, hwN⟩ hcw)
  have hy' : (letπ : LetA O n) • y = ∑ k, o k • C.t i (e k) := hy
  have hxΔ : ∀ k, ∃ a : Fin m → LetA O n, (∀ j, Formalism.MainNotions.DeltaInvariantLattices.InAΔ W (a j)) ∧
      C.t i (e k) = ∑ j, a j • b j := fun k => hΔ _ ⟨hm k, fun δ hδ => C.t_Δ i (e k) δ hδ⟩
  choose β hβΔ hβ using hxΔ
  obtain ⟨αy, hαy, -⟩ := huniq y hyN
  obtain ⟨αw, -, huw⟩ := huniq _ hwN
  have hw1 : ∑ k, o k • C.t i (e k) = ∑ j, (∑ k, o k • β k j) • b j := by
    simp only [hβ, Finset.smul_sum, ← smul_assoc, Finset.sum_smul]
    exact Finset.sum_comm
  have hw2 : ∑ k, o k • C.t i (e k) = ∑ j, ((letπ : LetA O n) * αy j) • b j := by
    rw [← hy', hαy, Finset.smul_sum]
    simp only [smul_smul]
  have hcoef : ∀ j, ∑ k, o k * PowerSeries.constantCoeff (β k j i) = 0 := by
    intro j
    have h1 := congrFun (congrFun ((huw _ hw1).trans (huw _ hw2).symm) j) i
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, letπ] at h1
    have h2 := congrArg PowerSeries.constantCoeff h1
    simpa [map_sum, PowerSeries.smul_eq_C_mul] using h2
  have hG : ∀ j, ∃ g : Fin r → PowerSeries O,
      (letE i : LetA O n) • b j = ∑ l, (baseIdOf hR).d (g l) • C.t i (e l) := fun j =>
    lvBasis_expand hBasis hBasis_e ((W.N T).smul_mem _ (hbN j).1) (lvBasis_letE_idem i _)
      (fun δ hδ => by rw [γD_smulA W, γA_letE W, (hbN j).2 δ hδ])
  choose g hg using hG
  have hid : ∀ k l, ∑ j, PowerSeries.constantCoeff (β k j i) * PowerSeries.constantCoeff (g j l) =
      if k = l then 1 else 0 := by
    intro k l
    have hc : ∀ l', (∑ j, β k j * (baseIdOf hR).d (g j l')) ∈ W.AΔ := fun l' =>
      Subalgebra.sum_mem _ fun j _ =>
        Subalgebra.mul_mem _ (hβΔ k j) (diag_mem_AΔ (ιOf_inv hR (g j l')))
    have hinv : ∀ l', Inv1 W ((∑ j, β k j * (baseIdOf hR).d (g j l')) i) := by
      intro l' δ hδ
      have hA : ∀ δ ∈ W.DelF, W.γA δ (∑ j, β k j * (baseIdOf hR).d (g j l')) =
          ∑ j, β k j * (baseIdOf hR).d (g j l') := hc l'
      have h := congrFun (hA δ hδ) i
      simpa [LocWach.γA, letγ] using h
    choose h hh using fun l' => ιOf_full hR _ (hinv l')
    have hx : C.t i (e k) = C.t i (∑ l', h l' • e l') := by
      rw [lvBasis_t_sum]
      conv_lhs => rw [← C.t_letter i (e k), hβ k, lvBasis_regroup b g hg (β k)]
      refine Finset.sum_congr rfl fun l' _ => ?_
      rw [C.t_smul]
      refine lvBasis_smul_letter ?_ (C.t_letter i (e l'))
      rw [← hh l']
      rfl
    have he : hBasis k = ∑ l', h l' • hBasis l' := by
      apply Subtype.ext
      simp only [Submodule.coe_sum, Submodule.coe_smul, hBasis_e]
      exact C.t_inj i hx
    have hrep := congrArg (fun z => hBasis.repr z l) he
    simp only [hBasis.repr_self, hBasis.repr_sum_self] at hrep
    have hcc : PowerSeries.constantCoeff ((∑ j, β k j * (baseIdOf hR).d (g j l)) i) =
        if k = l then 1 else 0 := by
      rw [← hh l, ιOf_const, ← hrep, Finsupp.single_apply]
      split_ifs <;> simp
    rw [← hcc]
    simp only [Finset.sum_apply, Pi.mul_apply, map_sum, map_mul, BaseId.d_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show (baseIdOf hR).ι = ιOf hR from rfl, ιOf_const]
  intro l
  calc o l = ∑ k, o k * (if k = l then 1 else 0) := by simp
    _ = ∑ k, o k * ∑ j, PowerSeries.constantCoeff (β k j i) * PowerSeries.constantCoeff (g j l) := by
        simp only [hid]
    _ = ∑ j, (∑ k, o k * PowerSeries.constantCoeff (β k j i)) * PowerSeries.constantCoeff (g j l) := by
        simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
        exact Finset.sum_comm
    _ = 0 := by simp [hcoef]

theorem lvBasis_cmp_ind {π' : LetA O n} (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hFrac : ∀ a : LL, ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N i))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) :
    LinearIndependent LL (fun k => W.cmp T ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro a ha k
  choose y o hy0 hyo using fun k => hFrac (a k)
  have hY : algebraMap O LL (∏ l, y l) ≠ 0 := by
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.2 fun l _ => hy0 l
  have hYa : ∀ k, algebraMap O LL (∏ l, y l) * a k =
      algebraMap O LL (o k * ∏ l ∈ Finset.univ.erase k, y l) := by
    intro k
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k), map_mul, map_mul, ← hyo k]
    ring
  have h0 : ∑ k, algebraMap O LL (o k * ∏ l ∈ Finset.univ.erase k, y l) •
      W.cmp T ⟨C.t i (e k), lvBasis_e_mem hBasis hBasis_e k⟩ = 0 := by
    simp only [← hYa, mul_smul, ← Finset.smul_sum, ha, smul_zero]
  have h1 := hYa k
  rw [lvBasis_kernel hP3 hP9 hBasis hBasis_e _ h0 k, map_zero] at h1
  exact (mul_eq_zero.1 h1).resolve_left hY

theorem lvBasis_lamOf_val {c : ZMod n} {ell : ℕ}
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (k : Fin r) :
    ((lamOf C c ell e k : Dc W T c) : T.V ⊗[Qp] B) =
      ((φVB PD (LL := LL) (V := T.V)) ^ ell) (W.cmp T ⟨_, lvBasis_e_mem hBasis hBasis_e k⟩) := by
  have h' := lvBasis_φpow_letter _ ell (lvBasis_cmp_e_letter hBasis hBasis_e k)
  rw [sub_add_cancel] at h'
  unfold lamOf
  rw [dif_pos (lvBasis_e_mem hBasis hBasis_e k), dif_pos h']

end abelian₂

theorem lamInd_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {r : ℕ} {e : Fin r → C.V} {lam : Fin r → Dc W T c} {π' : LetA O n}
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hFrac : ∀ a : LL, ∃ y o : O, algebraMap O LL y ≠ 0 ∧ algebraMap O LL y * a = algebraMap O LL o)
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hLam : lam = lamOf C c ell e) :
    LinearIndependent LL lam := by
  subst hLam
  apply LinearIndependent.of_comp (DcrisL PD T.ρ (W.emb c)).subtype
  have hval : ⇑(DcrisL PD T.ρ (W.emb c)).subtype ∘ lamOf C c ell e =
      ⇑((φVB PD (LL := LL) (V := T.V)) ^ ell) ∘
        fun k => W.cmp T ⟨_, lvBasis_e_mem hBasis hBasis_e k⟩ :=
    funext fun k => lvBasis_lamOf_val hBasis hBasis_e k
  rw [hval]
  exact (lvBasis_cmp_ind hP3 hP9 hFrac hBasis hBasis_e).map' _
    (LinearMap.ker_eq_bot.2 (lvBasis_φpow_inj PD (LL := LL) (V := T.V) ell))

theorem lamSpan_holds {T : LocLat G Qp LL O} {C : Coord W (baseIdOf hR) T} {c : ZMod n} {ell : ℕ}
    {r : ℕ} {e : Fin r → C.V} {lam : Fin r → Dc W T c} {π' : LetA O n}
    (hP3 : Formalism.MainNotions.DeltaInvariantLattices.p3 W T) (hP9 : Formalism.MainNotions.DeltaInvariantLattices.wachModuleOverLetters W T π')
    (hBasis : Module.Basis (Fin r) (PowerSeries O) ↥((latOf C).N (c - (ell : ZMod n))))
    (hBasis_e : ∀ k, (hBasis k : C.V) = e k) (hLam : lam = lamOf C c ell e) :
    Submodule.span LL (Set.range lam) = ⊤ := by
  subst hLam
  rw [Submodule.eq_top_iff']
  intro x
  obtain ⟨d', hd', hdx⟩ := lvBasis_φpow_pre hP3.2.1 hP3.2.2 c ell x.2
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun LL).1
    (lvBasis_letter_le hP3 hP9 hBasis hBasis_e hd')
  have hx : x = ∑ k, a k • lamOf C c ell e k := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul, lvBasis_lamOf_val hBasis hBasis_e]
    rw [← hdx, ← ha, map_sum]
    simp only [map_smul]
  rw [hx]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩)

end Formalism.MainNotions.N.Ln03.Pf
