import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.Monomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace Br

section Rename₂

variable {K : Type} [Field K] {σ τ : Type} (f : σ → τ) (hf : Function.Injective f)

include hf in
theorem fact_mapDomain (α : σ →₀ ℕ) : fact (α.mapDomain f) = fact α := by
  unfold fact
  exact Finsupp.prod_mapDomain_index_inj hf

include hf in
theorem fock_rename (F G : MvPolynomial σ K) : fock (rename f F) (rename f G) = fock F G := by
  classical
  unfold fock
  rw [support_rename_of_injective hf, Finset.sum_image]
  · refine Finset.sum_congr rfl fun α _ => ?_
    rw [coeff_rename_mapDomain f hf, coeff_rename_mapDomain f hf, fact_mapDomain f hf]
  · intro a _ b _ h
    exact Finsupp.mapDomain_injective hf h

include hf in
theorem vBB_rename (v : AddValuation K (WithTop ℚ)) (F : MvPolynomial σ K) : vBB v (rename f F) = vBB v F := by
  classical
  unfold vBB
  rw [support_rename_of_injective hf, Finset.inf_image]
  refine Finset.inf_congr rfl fun α _ => ?_
  simp only [Function.comp_apply, coeff_rename_mapDomain f hf, fact_mapDomain f hf]

end Rename₂

section Ren2

variable {K : Type} [Field K] {L L' : Type} {r : ℕ}

theorem mapDomain_prod_apply (g : L → L') (hg : Function.Injective g) (α : L × Fin r →₀ ℕ) (i : L) (a : Fin r) :
    (α.mapDomain (Prod.map g (id : Fin r → Fin r))) (g i, a) = α (i, a) := by
  have hinj : Function.Injective (Prod.map g (id : Fin r → Fin r)) := fun x y h => Prod.ext (hg (congrArg Prod.fst h)) (by have h2 := congrArg Prod.snd h; exact h2)
  exact Finsupp.mapDomain_apply hinj α (i, a)

theorem PolK_rename (g : L ≃ L') (d' : L' → ℕ) (F : MvPolynomial (L × Fin r) K) :
    rename (Prod.map g (id : Fin r → Fin r)) F ∈ PolK K r d' ↔ F ∈ PolK K r (d' ∘ g) := by
  classical
  have hinj : Function.Injective (Prod.map g (id : Fin r → Fin r)) := fun x y h => Prod.ext (g.injective (congrArg Prod.fst h)) (by have h2 := congrArg Prod.snd h; exact h2)
  simp only [PolK, mem_restrictSupport_iff, support_rename_of_injective hinj, Finset.coe_image,
    Set.image_subset_iff]
  constructor
  · intro h α hα i
    have := h hα (g i)
    simpa [mapDomain_prod_apply _ g.injective] using this
  · intro h β hβ i'
    obtain ⟨i, rfl⟩ := g.surjective i'
    have := h hβ i
    simpa [mapDomain_prod_apply _ g.injective] using this

theorem valS_transport [DecidableEq L'] [NeZero r] (g : L → L') (hg : Function.Injective g) (sg' : L' → Bool)
    (S' : Finset L') (LL : G.Letters L) (S : Set L) (h1 : ∀ i, LL.vec i = sg' (g i)) (h2 : ∀ i, i ∈ S ↔ g i ∈ S')
    (F : MvPolynomial (L × Fin r) K) :
    valS sg' S' (rename (Prod.map g id) F) = G.valS LL S F := by
  classical
  rw [valS_rename g hg, valS_eq]
  have e1 : (⟨sg' ∘ g⟩ : G.Letters L) = LL := by
    cases LL; simp only [G.Letters.mk.injEq]; funext i; exact (h1 i).symm
  have e2 : (↑(S'.preimage g hg.injOn) : Set L) = S := by
    ext i; simp [h2]
  rw [e1, e2]

end Ren2

section Data

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {r J : ℕ} [NeZero J]

abbrev zE (J : ℕ) [NeZero J] : Fin J ≃+* ZMod J := ZMod.finEquiv J

variable (Dt : PlaneGramData.SignedChainData p O r J)

def eO : PlaneGramData.TL J Dt.nL r ≃ ((Σ j : ZMod J, Fin (Dt.nL j)) ⊕ (Fin J × Fin r)) where
  toFun x := match x with
    | ⟨j, Sum.inl l⟩ => Sum.inl ⟨j, l⟩
    | ⟨j, Sum.inr m⟩ => Sum.inr ((zE J).symm j, m)
  invFun y := match y with
    | Sum.inl b => ⟨b.1, Sum.inl b.2⟩
    | Sum.inr t => ⟨zE J t.1, Sum.inr t.2⟩
  left_inv := by
    rintro ⟨j, l | m⟩
    · rfl
    · show (⟨zE J ((zE J).symm j), Sum.inr m⟩ : PlaneGramData.TL J Dt.nL r) = ⟨j, Sum.inr m⟩
      rw [RingEquiv.apply_symm_apply]
  right_inv := by rintro (⟨j, l⟩ | ⟨j, m⟩) <;> simp

open Classical in

abbrev toData : TwistData (G.KK O) where
  r := r
  J := J
  Lb := Σ j : ZMod J, Fin (Dt.nL j)
  seg b := (zE J).symm b.1
  sgn b := Dt.sgn b.1 b.2
  dB b := Dt.d ⟨b.1, Sum.inl b.2⟩
  dT t := Dt.d ⟨zE J t.1, Sum.inr t.2⟩
  g t := Dt.gP (zE J t.1) t.2
  nch j := Dt.nch (zE J j)
  chain j i := univ.filter fun b => ∃ l, b = ⟨zE J j, l⟩ ∧ Sum.inl l ∈ Dt.chain (zE J j) i
  th j i := Dt.th (zE J j) i
  sl j i := Dt.sl (zE J j) i
  thl j m := Dt.thL (zE J j) m
  c := ⌈Dt.c⌉₊
  ga α := algebraMap O (G.KK O) (Dt.ga (α.mapDomain (Prod.map (eO Dt).symm id)))

def fM : PlaneGramData.ML J Dt.nL r → (toData Dt).ML
  | PlaneGramData.ML.ll j l => Sum.inl ⟨j, l⟩
  | PlaneGramData.ML.lab j m => Sum.inr (Sum.inl ((zE J).symm j, m))
  | PlaneGramData.ML.wc j m => Sum.inr (Sum.inr (Sum.inl ((zE J).symm j, m)))
  | PlaneGramData.ML.tp j m _ => Sum.inr (Sum.inr (Sum.inr ((zE J).symm j, m)))

theorem fM_injective : Function.Injective (fM Dt) := by
  intro x y h
  cases x <;> cases y <;> simp_all [fM]

def gO : PlaneGramData.TL J Dt.nL r ≃ (toData Dt).OL := eO Dt

theorem zE_nxt (j : Fin J) : zE J ((toData Dt).nxt j) = zE J j + 1 := by
  have h : (toData Dt).nxt j = j + 1 := by
    apply Fin.ext
    show (j.val + 1) % J = _
    rw [Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [h, map_add, map_one]

theorem zE_prv (j : Fin J) : zE J ((toData Dt).aux₃ j) = zE J j - 1 := by
  have h : (toData Dt).aux₃ j = j - 1 := by
    apply Fin.ext
    rw [Fin.coe_sub, Fin.val_one']
    show (j.val + J - 1) % J = (J - 1 % J + j.val) % J
    rcases Nat.lt_or_ge 1 J with hJ | hJ
    · rw [Nat.mod_eq_of_lt hJ]
      congr 1
      omega
    · have h1 : J = 1 := by have := NeZero.ne J; omega
      subst h1
      simp
  rw [h, map_sub, map_one]

theorem sg_O (x : PlaneGramData.TL J Dt.nL r) : Dt.trueLet.vec x = (toData Dt).osg (gO Dt x) := by
  rcases x with ⟨j, l | m⟩ <;> rfl

theorem sg_M (x : PlaneGramData.ML J Dt.nL r) : Dt.modelLet.vec x = (toData Dt).msg (fM Dt x) := by
  cases x <;> rfl

theorem mem_chain (j : Fin J) (i : Fin (Dt.nch (zE J j))) (x : PlaneGramData.ML J Dt.nL r) :
    x ∈ Dt.chainML (zE J j) i ↔ fM Dt x ∈ (toData Dt).chainSet j i := by
  cases x with
  | ll k l =>
    show _ ↔ (Sum.inl ⟨k, l⟩ : (toData Dt).ML) ∈ (toData Dt).chainSet j i
    simp only [PlaneGramData.SignedChainData.chainML, TwistData.chainSet, TwistData.wSet, TwistData.mb, TwistData.mw, Set.mem_image,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y | y, hy, h⟩
      · have h' : PlaneGramData.ML.ll (zE J j) y = PlaneGramData.ML.ll k l := h
        obtain ⟨hk, hl⟩ := PlaneGramData.ML.ll.inj h'
        subst hk
        cases hl
        exact Or.inl ⟨_, ⟨_, rfl, hy⟩, rfl⟩
      · simp [PlaneGramData.SignedChainData.levToML] at h
    · rintro (⟨b, ⟨l', hb, hl'⟩, h⟩ | ⟨a, h⟩)
      · subst hb
        have h2 : (⟨zE J j, l'⟩ : Σ k, Fin (Dt.nL k)) = ⟨k, l⟩ := Sum.inl_injective h
        cases h2
        exact ⟨Sum.inl l', hl', rfl⟩
      · cases h
  | lab k m' =>
    show _ ↔ (Sum.inr (Sum.inl ((zE J).symm k, m')) : (toData Dt).ML) ∈ (toData Dt).chainSet j i
    simp only [PlaneGramData.SignedChainData.chainML, TwistData.chainSet, TwistData.wSet, TwistData.mb, TwistData.mw, Set.mem_image,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y | y, hy, h⟩ <;> simp [PlaneGramData.SignedChainData.levToML] at h
    · rintro (⟨b, -, h⟩ | ⟨a, h⟩) <;> cases h
  | wc k m' =>
    show _ ↔ (Sum.inr (Sum.inr (Sum.inl ((zE J).symm k, m'))) : (toData Dt).ML) ∈ (toData Dt).chainSet j i
    simp only [PlaneGramData.SignedChainData.chainML, TwistData.chainSet, TwistData.wSet, TwistData.mb, TwistData.mw, Set.mem_image,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y | y, hy, h⟩
      · simp [PlaneGramData.SignedChainData.levToML] at h
      · have h' : PlaneGramData.ML.wc (zE J j - 1) y = PlaneGramData.ML.wc k m' := h
        obtain ⟨hk, rfl⟩ := PlaneGramData.ML.wc.inj h'
        refine Or.inr ⟨y, ?_⟩
        rw [← hk, ← zE_prv Dt j, RingEquiv.symm_apply_apply]
    · rintro (⟨b, -, h⟩ | ⟨a, h⟩)
      · cases h
      · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        refine ⟨Sum.inr m', Dt.chain_w _ _ m', ?_⟩
        show PlaneGramData.ML.wc (zE J j - 1) m' = PlaneGramData.ML.wc k m'
        rw [← zE_prv Dt j, h.1, RingEquiv.apply_symm_apply]
  | tp k m' hm' =>
    show _ ↔ (Sum.inr (Sum.inr (Sum.inr ((zE J).symm k, m'))) : (toData Dt).ML) ∈ (toData Dt).chainSet j i
    simp only [PlaneGramData.SignedChainData.chainML, TwistData.chainSet, TwistData.wSet, TwistData.mb, TwistData.mw, Set.mem_image,
      Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨y | y, hy, h⟩ <;> simp [PlaneGramData.SignedChainData.levToML] at h
    · rintro (⟨b, -, h⟩ | ⟨a, h⟩) <;> cases h

theorem mem_T (j : Fin J) (m : Fin r) (x : PlaneGramData.TL J Dt.nL r) :
    x ∈ Dt.TSet (zE J j) m ↔ gO Dt x ∈ (toData Dt).Tset j m := by
  simp only [PlaneGramData.SignedChainData.TSet, Set.mem_union, Set.mem_setOf_eq]
  rcases x with ⟨k, l | m''⟩
  · show _ ↔ (Sum.inl ⟨k, l⟩ : (toData Dt).OL) ∈ (toData Dt).Tset j m
    simp only [TwistData.Tset, TwistData.LLj, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨l', h⟩ | ⟨m', -, h⟩)
      · have hk : k = zE J j := congrArg Sigma.fst h
        refine Or.inl ⟨⟨k, l⟩, ?_, rfl⟩
        show (zE J).symm k = j
        rw [hk, RingEquiv.symm_apply_apply]
      · exact absurd (congrArg (fun s => s.2.isLeft) h) (by simp)
    · rintro (⟨b, hb, hb'⟩ | ⟨m', -, hm'⟩)
      · have hb2 : b = ⟨k, l⟩ := Sum.inl_injective hb'
        subst hb2
        have hk : k = zE J j := by
          have : (zE J).symm k = j := hb
          rw [← this, RingEquiv.apply_symm_apply]
        subst hk
        exact Or.inl ⟨l, rfl⟩
      · exact absurd hm' (by simp)
  · show _ ↔ (Sum.inr ((zE J).symm k, m'') : (toData Dt).OL) ∈ (toData Dt).Tset j m
    simp only [TwistData.Tset, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
      Finset.mem_univ, true_and]
    constructor
    · rintro (⟨l', h⟩ | ⟨m', hm, h⟩)
      · exact absurd (congrArg (fun s => s.2.isLeft) h) (by simp)
      · have hk : k = zE J j := congrArg Sigma.fst h
        subst hk
        have hm2 : m'' = m' := by
          have := h
          simp only [Sigma.mk.injEq, heq_eq_eq, Sum.inr.injEq, true_and] at this
          exact this
        subst hm2
        refine Or.inr ⟨m'', hm, ?_⟩
        rw [RingEquiv.symm_apply_apply]
    · rintro (⟨b, -, hb⟩ | ⟨m', hm, hm'⟩)
      · exact absurd hb (by simp)
      · have h2 : j = (zE J).symm k ∧ m' = m'' := by simpa using hm'
        obtain ⟨rfl, rfl⟩ := h2
        refine Or.inr ⟨m', hm, ?_⟩
        rw [RingEquiv.apply_symm_apply]

theorem mem_link (j : Fin J) (m : Fin r) (x : PlaneGramData.ML J Dt.nL r) :
    x ∈ Dt.linkML (zE J j) m ↔ fM Dt x ∈ (toData Dt).Yset j m := by
  cases x with
  | ll k l =>
    show _ ↔ (Sum.inl ⟨k, l⟩ : (toData Dt).ML) ∈ (toData Dt).Yset j m
    simp only [TwistData.Yset, TwistData.wSet, TwistData.LLj, TwistData.mb, TwistData.mw, TwistData.mtp, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [PlaneGramData.SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m1, h1, h2, h⟩)
      · cases h
      · have hk : k = zE J j := (PlaneGramData.ML.ll.inj h).1
        refine Or.inl (Or.inr ⟨⟨k, l⟩, ?_, rfl⟩)
        show (zE J).symm k = j
        rw [hk, RingEquiv.symm_apply_apply]
      · cases h
    · rintro ((⟨a, h⟩ | ⟨b, hb, h⟩) | ⟨a, -, h⟩)
      · cases h
      · have hb2 : b = ⟨k, l⟩ := Sum.inl_injective h
        subst hb2
        have hk : k = zE J j := by
          have : (zE J).symm k = j := hb
          rw [← this, RingEquiv.apply_symm_apply]
        subst hk
        exact Or.inl (Or.inr ⟨l, rfl⟩)
      · cases h
  | lab k m' =>
    show _ ↔ (Sum.inr (Sum.inl ((zE J).symm k, m')) : (toData Dt).ML) ∈ (toData Dt).Yset j m
    simp only [TwistData.Yset, TwistData.wSet, TwistData.LLj, TwistData.mb, TwistData.mw, TwistData.mtp, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [PlaneGramData.SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m1, h1, h2, h⟩) <;> cases h
    · rintro ((⟨a, h⟩ | ⟨b, hb, h⟩) | ⟨a, -, h⟩) <;> cases h
  | wc k m' =>
    show _ ↔ (Sum.inr (Sum.inr (Sum.inl ((zE J).symm k, m'))) : (toData Dt).ML) ∈ (toData Dt).Yset j m
    simp only [TwistData.Yset, TwistData.wSet, TwistData.LLj, TwistData.mb, TwistData.mw, TwistData.mtp, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [PlaneGramData.SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m1, h1, h2, h⟩)
      · obtain ⟨hk, rfl⟩ := PlaneGramData.ML.wc.inj h
        refine Or.inl (Or.inl ⟨m', ?_⟩)
        rw [hk, ← zE_prv Dt j, RingEquiv.symm_apply_apply]
      · cases h
      · cases h
    · rintro ((⟨a, h⟩ | ⟨b, hb, h⟩) | ⟨a, -, h⟩)
      · simp only [Sum.inr.injEq, Sum.inl.injEq, Prod.mk.injEq] at h
        refine Or.inl (Or.inl ⟨m', ?_⟩)
        rw [← zE_prv Dt j, h.1, RingEquiv.apply_symm_apply]
      · cases h
      · cases h
  | tp k m' hm' =>
    show _ ↔ (Sum.inr (Sum.inr (Sum.inr ((zE J).symm k, m'))) : (toData Dt).ML) ∈ (toData Dt).Yset j m
    simp only [TwistData.Yset, TwistData.wSet, TwistData.LLj, TwistData.mb, TwistData.mw, TwistData.mtp, Finset.mem_union,
      Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    simp only [PlaneGramData.SignedChainData.linkML, Set.mem_union, Set.mem_setOf_eq]
    constructor
    · rintro ((⟨m'', h⟩ | ⟨l', h⟩) | ⟨m1, h1, h2, h⟩)
      · cases h
      · cases h
      · obtain ⟨hk, rfl⟩ := PlaneGramData.ML.tp.inj h
        refine Or.inr ⟨m', h2, ?_⟩
        rw [hk, RingEquiv.symm_apply_apply]
    · rintro ((⟨a, h⟩ | ⟨b, hb, h⟩) | ⟨a, ha, h⟩)
      · cases h
      · cases h
      · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
        obtain ⟨h1, rfl⟩ := h
        refine Or.inr ⟨a, hm', ha, ?_⟩
        rw [h1, RingEquiv.apply_symm_apply]

theorem gO_inj : Function.Injective (Prod.map (gO Dt) (id : Fin r → Fin r)) := fun x y h => Prod.ext ((gO Dt).injective (congrArg Prod.fst h)) (by have h2 := congrArg Prod.snd h; exact h2)

theorem fM_inj : Function.Injective (Prod.map (fM Dt) (id : Fin r → Fin r)) := fun x y h => Prod.ext (fM_injective Dt (congrArg Prod.fst h)) (by have h2 := congrArg Prod.snd h; exact h2)

theorem md_apply (mo : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) (y : (toData Dt).OL) (a : Fin r) :
    (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))) (y, a) = mo ((gO Dt).symm y, a) := by
  have hinj : Function.Injective (Prod.map (gO Dt) (id : Fin r → Fin r)) := gO_inj Dt
  have := Finsupp.mapDomain_apply hinj mo ((gO Dt).symm y, a)
  simpa using this

theorem ph_comm (Gm : MvPolynomial (PlaneGramData.ML J Dt.nL r × Fin r) (G.KK O)) :
    (toData Dt).ph p (rename (Prod.map (fM Dt) id) Gm) = rename (Prod.map (gO Dt) id) (Dt.ph Gm) := by
  have key : ((toData Dt).ph p).comp (rename (Prod.map (fM Dt) id)) =
      (rename (Prod.map (gO Dt) id)).comp Dt.ph := by
    apply MvPolynomial.algHom_ext
    rintro ⟨x, a⟩
    cases x <;> simp [TwistData.ph, PlaneGramData.SignedChainData.ph, fM, gO, eO, TwistData.P, PlaneGramData.SignedChainData.P]
  exact DFunLike.congr_fun key Gm

theorem ga_md (mo : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) :
    (toData Dt).ga (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))) = algebraMap O (G.KK O) (Dt.ga mo) := by
  show algebraMap O (G.KK O) (Dt.ga ((mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))).mapDomain
    (Prod.map (eO Dt).symm id))) = _
  rw [← Finsupp.mapDomain_comp]
  have hc : (Prod.map (eO Dt).symm (id : Fin r → Fin r)) ∘ (Prod.map (gO Dt) id) = id := by
    funext x
    exact Prod.ext ((eO Dt).symm_apply_apply x.1) rfl
  rw [hc, Finsupp.mapDomain_id]

theorem gaAct_comm (H : MvPolynomial (PlaneGramData.TL J Dt.nL r × Fin r) (G.KK O)) :
    (toData Dt).gaAct (rename (Prod.map (gO Dt) id) H) =
      rename (Prod.map (gO Dt) id)
        (∑ mo ∈ H.support, monomial mo (algebraMap O (G.KK O) (Dt.ga mo) * H.coeff mo)) := by
  classical
  unfold TwistData.gaAct
  rw [support_rename_of_injective (gO_inj Dt),
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective (gO_inj Dt) h), map_sum]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [rename_monomial, ga_md, coeff_rename_mapDomain _ (gO_inj Dt)]

theorem fock_rename_gaAct_rename_eq_Bform (F H : MvPolynomial (PlaneGramData.TL J Dt.nL r × Fin r) (G.KK O)) :
    fock (rename (Prod.map (gO Dt) id) F) ((toData Dt).gaAct (rename (Prod.map (gO Dt) id) H)) = Dt.Bform F H := by
  rw [gaAct_comm]
  exact fock_rename (Prod.map (gO Dt) id) (gO_inj Dt) F _

theorem inClass_iff (ρ : (toData Dt).Tau → Fin r → ℕ) (mo : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) :
    (toData Dt).InClass p ρ (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))) ↔
      Dt.digOK (fun x => ρ ((zE J).symm x.1.1, x.1.2) x.2) mo := by
  constructor
  · intro H j m a
    obtain ⟨j0, rfl⟩ := (zE J).surjective j
    have := H (j0, m) a
    rw [md_apply] at this
    simpa [gO, eO, TwistData.P, PlaneGramData.SignedChainData.P] using this
  · rintro H ⟨j', m⟩ a
    have := H (zE J j') m a
    rw [md_apply]
    simpa [gO, eO, TwistData.P, PlaneGramData.SignedChainData.P] using this

theorem sum_single_inj {α β : Type} [DecidableEq α] (u : α → β) (hu : Function.Injective u) (s : Finset α) (e : α → ℕ) :
    (∀ v0, (∑ v ∈ s, Finsupp.single (u v) (e v)) (u v0) = if v0 ∈ s then e v0 else 0) ∧
      ∀ x, x ∉ Set.range u → (∑ v ∈ s, Finsupp.single (u v) (e v)) x = 0 := by
  classical
  refine ⟨fun v0 => ?_, fun x hx => ?_⟩
  · simp [Finsupp.finset_sum_apply, Finsupp.single_apply, hu.eq_iff]
  · simp only [Finsupp.finset_sum_apply, Finsupp.single_apply]
    exact Finset.sum_eq_zero fun v _ => if_neg fun h => hx ⟨v, h⟩

theorem liftVar_inj : Function.Injective Dt.liftVar := by
  rintro ⟨⟨j, l | m⟩, a⟩ ⟨⟨j', l' | m'⟩, a'⟩ h
  · simp only [PlaneGramData.SignedChainData.liftVar, Prod.mk.injEq, PlaneGramData.ML.ll.injEq] at h
    obtain ⟨⟨rfl, h2⟩, rfl⟩ := h
    cases h2
    rfl
  · simp [PlaneGramData.SignedChainData.liftVar] at h
  · simp [PlaneGramData.SignedChainData.liftVar] at h
  · simp only [PlaneGramData.SignedChainData.liftVar, Prod.mk.injEq, PlaneGramData.ML.wc.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    rfl

theorem lift_mono (mo : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) :
    rename (Prod.map (fM Dt) id) (∏ v ∈ mo.support, X (Dt.liftVar v) ^ Dt.liftExp mo v) =
      monomial ((toData Dt).liftE p (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r)))) (1 : G.KK O) := by
  classical
  obtain ⟨h1, h2⟩ := sum_single_inj (fun v => Prod.map (fM Dt) (id : Fin r → Fin r) (Dt.liftVar v))
    (fun x y h => liftVar_inj Dt (fM_inj Dt h)) mo.support (Dt.liftExp mo)
  beta_reduce at h1 h2
  rw [map_prod]
  simp only [map_pow, rename_X]
  simp only [X_pow_eq_monomial]
  rw [← monomial_sum_one]
  refine congrArg (fun s => (monomial s) (1 : G.KK O)) ?_
  ext v
  obtain ⟨x, a⟩ := v
  rcases x with b | t | t | t
  · obtain ⟨j, l⟩ := b
    refine (h1 (⟨j, Sum.inl l⟩, a)).trans ?_
    show _ = (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))) (Sum.inl ⟨j, l⟩, a)
    rw [md_apply]
    show _ = mo (⟨j, Sum.inl l⟩, a)
    split_ifs with hs
    · rfl
    · exact (by simpa using hs : mo (⟨j, Sum.inl l⟩, a) = 0).symm
  · have hx : ((Sum.inr (Sum.inl t) : (toData Dt).ML), a) ∉ Set.range (fun v => Prod.map (fM Dt) (id : Fin r → Fin r) (Dt.liftVar v)) := by
      rintro ⟨⟨⟨j, l | m⟩, b⟩, h⟩ <;> simp [PlaneGramData.SignedChainData.liftVar, fM] at h
    rw [h2 _ hx]
    rfl
  · obtain ⟨j, m⟩ := t
    conv_lhs => rw [show ((Sum.inr (Sum.inr (Sum.inl (j, m))) : (toData Dt).ML), a) =
      Prod.map (fM Dt) (id : Fin r → Fin r) (Dt.liftVar (⟨zE J j, Sum.inr m⟩, a)) by
        simp [PlaneGramData.SignedChainData.liftVar, fM]]
    rw [h1]
    show _ = (mo.mapDomain (Prod.map (gO Dt) (id : Fin r → Fin r))) (Sum.inr (j, m), a) / (toData Dt).P p (j, m)
    rw [md_apply]
    show _ = mo (⟨zE J j, Sum.inr m⟩, a) / p ^ Dt.gP (zE J j) m
    split_ifs with hs
    · rfl
    · rw [(by simpa using hs : mo (⟨zE J j, Sum.inr m⟩, a) = 0)]
      simp
  · have hx : ((Sum.inr (Sum.inr (Sum.inr t)) : (toData Dt).ML), a) ∉ Set.range (fun v => Prod.map (fM Dt) (id : Fin r → Fin r) (Dt.liftVar v)) := by
      rintro ⟨⟨⟨j, l | m⟩, b⟩, h⟩ <;> simp [PlaneGramData.SignedChainData.liftVar, fM] at h
    rw [h2 _ hx]
    rfl

theorem digit_comm (ρ : (toData Dt).Tau → Fin r → ℕ) (F : MvPolynomial (PlaneGramData.TL J Dt.nL r × Fin r) (G.KK O)) :
    (toData Dt).digitPart p ρ (rename (Prod.map (gO Dt) id) F) =
      rename (Prod.map (fM Dt) id) (Dt.Fdig (fun x => ρ ((zE J).symm x.1.1, x.1.2) x.2) F) := by
  classical
  unfold TwistData.digitPart PlaneGramData.SignedChainData.Fdig
  rw [support_rename_of_injective (gO_inj Dt),
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective (gO_inj Dt) h), map_sum,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun mo _ => ?_
  rw [coeff_rename_mapDomain _ (gO_inj Dt)]
  by_cases hd : Dt.digOK (fun x => ρ ((zE J).symm x.1.1, x.1.2) x.2) mo
  · rw [if_pos ((inClass_iff Dt ρ mo).2 hd), if_pos hd, map_mul, rename_C, lift_mono,
      C_mul_monomial, mul_one]
  · rw [if_neg (fun h => hd ((inClass_iff Dt ρ mo).1 h)), if_neg hd]

theorem dO_gO (x : PlaneGramData.TL J Dt.nL r) : (toData Dt).dO (gO Dt x) = Dt.d x := by
  rcases x with ⟨j, l | m⟩
  · rfl
  · show Dt.d ⟨zE J ((zE J).symm j), Sum.inr m⟩ = Dt.d ⟨j, Sum.inr m⟩
    rw [RingEquiv.apply_symm_apply]

theorem totDeg_eq : (toData Dt).totDeg = ∑ x, Dt.d x := by
  unfold TwistData.totDeg
  exact (Fintype.sum_equiv (gO Dt) (fun x => Dt.d x) (toData Dt).dO (fun x => (dO_gO Dt x).symm)).symm

theorem eC_eq (C0 : ℝ) : (toData Dt).eC p C0 = Dt.eP := by
  unfold TwistData.eC PlaneGramData.SignedChainData.eP
  rw [totDeg_eq]
  rfl

theorem Dm_eq (C0 : ℝ) : (toData Dt).Dm p C0 = Dt.Dm := by
  unfold TwistData.Dm PlaneGramData.SignedChainData.Dm
  rw [eC_eq, ← Finset.sum_mul, Nat.cast_sum]
  congr 1
  exact Fintype.sum_equiv (zE J).toEquiv _ _ (fun j => rfl)

theorem Dl_eq (C0 : ℝ) : (toData Dt).Dl p C0 = Dt.Dl := by
  unfold TwistData.Dl PlaneGramData.SignedChainData.Dl
  rw [eC_eq]

theorem kapD_eq : (toData Dt).kapD p = Dt.kp := by
  unfold TwistData.kapD PlaneGramData.SignedChainData.kp
  exact (Fintype.sum_equiv (gO Dt) (fun x => (r : ℝ) * lg p r (Dt.d x))
    (fun y => (r : ℝ) * lg p r ((toData Dt).dO y))
    (fun x => congrArg (fun n => (r : ℝ) * lg p r n) (dO_gO Dt x).symm)).symm

theorem normShift_eq (hp : p.Prime) (S : G.UniformizedDVR p O) : (toData Dt).n0 (vQ p S) = Dt.n0 := by
  unfold TwistData.n0 PlaneGramData.SignedChainData.n0
  have e : (∏ i : (toData Dt).OL, ((toData Dt).dO i).factorial) = ∏ x, (Dt.d x).factorial := by
    rw [← Equiv.prod_comp (gO Dt)]
    exact Finset.prod_congr rfl fun x _ => by rw [dO_gO]
  rw [e, vQ_nat hp S _ (Finset.prod_ne_zero_iff.mpr fun x _ => Nat.factorial_ne_zero _), WithTop.untopD_coe,
    Rat.cast_natCast]

theorem dLL_eq (j : Fin J) : (toData Dt).dLL j = Dt.dLL (zE J j) := by
  unfold TwistData.dLL TwistData.LLj PlaneGramData.SignedChainData.dLL
  rw [Finset.sum_filter, Fintype.sum_sigma, Finset.sum_eq_single (zE J j)]
  · refine Finset.sum_congr rfl fun l _ => ?_
    rw [if_pos]
    show (zE J).symm (zE J j) = j
    exact RingEquiv.symm_apply_apply _ _
  · intro k _ hk
    refine Finset.sum_eq_zero fun l _ => ?_
    rw [if_neg]
    intro h
    apply hk
    have h' : (zE J).symm k = j := h
    rw [← h', RingEquiv.apply_symm_apply]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem vQ_unit (S : G.UniformizedDVR p O) (u : O) (hu : IsUnit u) : vQ p S (algebraMap O (G.KK O) u) = 0 := by
  have hx : algebraMap O (G.KK O) u ≠ 0 := by
    rw [Ne, map_eq_zero_iff _ (IsFractionRing.injective O (G.KK O))]
    exact hu.ne_zero
  have hs := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) (algebraMap O (G.KK O) u))
  rw [← map_mul] at hs
  have h1 := IsFractionRing.injective O (G.KK O) hs
  have key : G.ordW (algebraMap O (G.KK O) u) = 0 := by
    unfold G.ordW
    rw [if_neg hx]
    simp only
    rw [← h1, IsDiscreteValuationRing.addVal_mul, ← hu.unit_spec,
      IsDiscreteValuationRing.addVal_eq_zero_of_unit, zero_add, sub_self]
    rfl
  unfold vQ
  rw [AddValuation.of_apply]
  unfold G.vK
  rw [key]
  simp

def eE : (PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) ≃ ((toData Dt).OL × Fin r → ℕ) :=
  (Finsupp.domCongr (Equiv.prodCongr (gO Dt) (Equiv.refl (Fin r)))).toEquiv.trans Finsupp.equivFunOnFinite

theorem eE_apply (m : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) (v : PlaneGramData.TL J Dt.nL r × Fin r) :
    eE Dt m (gO Dt v.1, v.2) = m v := by
  simp [eE]

theorem binom_comm (lam : (PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) →₀ O) (α : (toData Dt).OL × Fin r →₀ ℕ) :
    binomComb (lam.support.map (eE Dt).toEmbedding)
        (fun m' => algebraMap O (G.KK O) (lam ((eE Dt).symm m'))) (fun x => α x) =
      PlaneGramData.binomCombF (K := G.KK O) lam (α.mapDomain (Prod.map (eO Dt).symm id)) := by
  classical
  unfold binomComb PlaneGramData.binomCombF
  rw [Finset.sum_map]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.symm_apply_apply]
  congr 1
  have hinj : Function.Injective (Prod.map (eO Dt).symm (id : Fin r → Fin r)) := fun x y h =>
    Prod.ext ((eO Dt).symm.injective (congrArg Prod.fst h)) (by have h2 := congrArg Prod.snd h; exact h2)
  have hα : ∀ v : PlaneGramData.TL J Dt.nL r × Fin r,
      (α.mapDomain (Prod.map (eO Dt).symm id)) v = α (gO Dt v.1, v.2) := by
    intro v
    have := Finsupp.mapDomain_apply hinj α (gO Dt v.1, v.2)
    simpa [gO] using this
  have hsub : ∏ v ∈ m.support, ((((α.mapDomain (Prod.map (eO Dt).symm id)) v).choose (m v) : ℕ) : G.KK O) =
      ∏ v, ((((α.mapDomain (Prod.map (eO Dt).symm id)) v).choose (m v) : ℕ) : G.KK O) :=
    Finset.prod_subset (Finset.subset_univ _) (fun v _ hv => by
      have h0 : m v = 0 := by simpa using hv
      rw [h0, Nat.choose_zero_right, Nat.cast_one])
  rw [hsub]
  refine (Fintype.prod_equiv (Equiv.prodCongr (gO Dt) (Equiv.refl (Fin r))) _ _ (fun v => ?_)).symm
  rw [hα]
  show _ = (((α (gO Dt v.1, v.2)).choose (eE Dt m (gO Dt v.1, v.2)) : ℕ) : G.KK O)
  rw [eE_apply]

theorem sum_eE (m : PlaneGramData.TL J Dt.nL r × Fin r →₀ ℕ) : ∑ x, eE Dt m x = m.sum fun _ e => e := by
  rw [Finsupp.sum_fintype _ _ (fun _ => rfl)]
  exact (Fintype.sum_equiv (Equiv.prodCongr (gO Dt) (Equiv.refl (Fin r))) (fun v => m v)
    (fun x => eE Dt m x) (fun v => (eE_apply Dt m v).symm)).symm

theorem gaOK_toData (S : G.UniformizedDVR p O) : (toData Dt).GaOK (vQ p S) p := by
  have hc1 : 1 ≤ ⌈Dt.c⌉₊ := Nat.one_le_ceil_iff.mpr (lt_of_lt_of_le one_pos Dt.one_le_c)
  refine ⟨fun α => vQ_unit S _ (Dt.ga_unit _), ?_⟩
  intro ε hε
  obtain ⟨lam, hdeg, happ⟩ := Dt.ga_dig ⌈Dt.c⌉₊ hc1 (decide (ε = 1))
  refine ⟨lam.support.map (eE Dt).toEmbedding, fun m' => algebraMap O (G.KK O) (lam ((eE Dt).symm m')), ?_, ?_⟩
  · intro m' hm'
    obtain ⟨m, hm, rfl⟩ := Finset.mem_map.mp hm'
    refine ⟨(vQ_nonneg_iff S _).mpr ⟨_, rfl⟩, ?_⟩
    simp only [Equiv.coe_toEmbedding]
    rw [sum_eE]
    exact hdeg m hm
  · intro α
    rw [binom_comm]
    have := (geQ_nat_iff S _ _).mp (happ (α.mapDomain (Prod.map (eO Dt).symm id)))
    rcases hε with rfl | rfl
    · simpa using this
    · simpa using this

theorem valid_toData [NeZero r] (S : G.UniformizedDVR p O) : (toData Dt).Valid (vQ p S) p := by
  refine ⟨Nat.pos_of_ne_zero (NeZero.ne r), Nat.pos_of_ne_zero (NeZero.ne J),
    Nat.ceil_pos.mpr (by linarith [Dt.one_le_c]), ?_, ?_, fun j m h => Dt.thL_pos (zE J j) m h,
    gaOK_toData Dt S⟩
  · intro j i b hb
    simp only [TwistData.LLj, Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
    obtain ⟨l, rfl, -⟩ := hb
    exact RingEquiv.symm_apply_apply _ _
  · intro j i i' hii'
    have hs := Dt.chain_mono (zE J j) hii'
    have hsub : (toData Dt).chain j i ⊆ (toData Dt).chain j i' := by
      intro b hb
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb ⊢
      obtain ⟨l, hbl, hl⟩ := hb
      exact ⟨l, hbl, hs.1 hl⟩
    rw [Finset.ssubset_iff_of_subset hsub]
    obtain ⟨x, hx', hx⟩ := Set.exists_of_ssubset hs
    rcases x with l | m
    · refine ⟨⟨zE J j, l⟩, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨l, rfl, hx'⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        rintro ⟨l', hl', hl⟩
        have hh := (Sigma.mk.inj_iff.mp hl').2
        cases eq_of_heq hh
        exact hx hl
    · exact absurd (Dt.chain_w _ _ m) hx

theorem natCeil_le_two_mul_of_one_le (x : ℝ) (hx : 1 ≤ x) : ((⌈x⌉₊ : ℕ) : ℝ) ≤ 2 * x := by
  have := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ x)
  linarith

theorem hypH_toData {CH : ℝ} (hCH : 26 ≤ CH) (h : Dt.Hyp CH) : (toData Dt).HypH p 13 := by
  intro j m i
  have key : ∀ (k : ZMod J) (_hk : k = zE J j + 1) (i : Fin (Dt.nch k)),
      (r : ℝ) * (Dt.dLL (zE J j) : ℝ) / (Dt.P (zE J j) m : ℝ) + 13 * (r : ℝ) * (⌈Dt.c⌉₊ : ℝ) ≤ Dt.sl k i := by
    rintro k rfl i
    have h1 := h (zE J j) m i
    have hc := natCeil_le_two_mul_of_one_le Dt.c Dt.one_le_c
    have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
    have hc0 : (0 : ℝ) ≤ Dt.c := by linarith [Dt.one_le_c]
    have e1 : (r : ℝ) * (⌈Dt.c⌉₊ : ℝ) ≤ r * (2 * Dt.c) := mul_le_mul_of_nonneg_left hc hr
    have e2 : (26 : ℝ) * (r * Dt.c) ≤ CH * (r * Dt.c) := mul_le_mul_of_nonneg_right hCH (mul_nonneg hr hc0)
    nlinarith
  have := key (zE J ((toData Dt).nxt j)) (zE_nxt Dt j) i
  rw [dLL_eq]
  exact this

theorem hc_toData (h : 4 * (Dt.Dm + Dt.Dl + 3 * Dt.kp) < Dt.c) : (toData Dt).Hc p 1 := by
  unfold TwistData.Hc
  rw [Dm_eq, Dl_eq, kapD_eq]
  exact lt_of_lt_of_le h (Nat.le_ceil _)

theorem inXX_toData [NeZero r] (F : MvPolynomial (PlaneGramData.TL J Dt.nL r × Fin r) (G.KK O)) (h : Dt.XX F) :
    (toData Dt).InXX p (rename (Prod.map (gO Dt) id) F) := by
  obtain ⟨hP, hD, hT⟩ := h
  have hgeZ : ∀ (x : WithTop ℤ) (t : ℝ), PlaneGramData.geZ x t → ((t : ℝ) : WithTop ℝ) ≤ toR x := by
    intro x t hx
    induction x using WithTop.recTopCoe with
    | top => simp [toR]
    | coe k =>
      have := hx k rfl
      simp only [toR, WithTop.map_coe]
      exact WithTop.coe_le_coe.mpr this
  refine ⟨?_, ?_, ?_⟩
  · have e : (toData Dt).dO ∘ (gO Dt) = Dt.d := funext (dO_gO Dt)
    rw [PolK_rename (gO Dt) (toData Dt).dO F, e]
    exact hP
  · intro ρ j i
    rw [digit_comm, valS_transport (fM Dt) (fM_injective Dt) (toData Dt).msg ((toData Dt).chainSet j i)
      Dt.modelLet (Dt.chainML (zE J j) i) (sg_M Dt) (fun x => mem_chain Dt j i x)]
    exact hgeZ _ _ (hD _ (zE J j) i)
  · intro j m hm
    rw [valS_transport (gO Dt) (gO Dt).injective (toData Dt).osg ((toData Dt).Tset j m) Dt.trueLet
      (Dt.TSet (zE J j) m) (sg_O Dt) (fun x => mem_T Dt j m x)]
    exact hgeZ _ _ (hT (zE J j) m hm)

theorem exists_pre (G' : MvPolynomial ((toData Dt).ML × Fin r) (G.KK O)) (h : (toData Dt).RRvars G') :
    ∃ G0, rename (Prod.map (fM Dt) id) G0 = G' := by
  classical
  refine exists_rename_eq_of_vars_subset_range G' (Prod.map (fM Dt) id) (fM_inj Dt) ?_
  intro v hv
  rw [Finset.mem_coe, mem_vars] at hv
  obtain ⟨α, hα, hvα⟩ := hv
  rw [Finsupp.mem_support_iff] at hvα
  obtain ⟨x, a⟩ := v
  rcases x with ⟨k, l⟩ | ⟨j, m⟩ | ⟨j, m⟩ | ⟨j, m⟩
  · exact ⟨(PlaneGramData.ML.ll k l, a), rfl⟩
  · exact ⟨(PlaneGramData.ML.lab (zE J j) m, a), by simp [fM]⟩
  · exact ⟨(PlaneGramData.ML.wc (zE J j) m, a), by simp [fM]⟩
  · by_cases hm : 1 ≤ m.val
    · exact ⟨(PlaneGramData.ML.tp (zE J j) m hm, a), by simp [fM]⟩
    · exact absurd (h α hα j m (by omega) a) hvα

theorem phDeg_mem (G0 : MvPolynomial (PlaneGramData.ML J Dt.nL r × Fin r) (G.KK O))
    (h : (toData Dt).PhDeg p (rename (Prod.map (fM Dt) id) G0)) (mo) (hmo : mo ∈ G0.support) :
    Dt.ph (monomial mo 1) ∈ G.Pol (G.KK O) r Dt.d := by
  classical
  have hs : mo.mapDomain (Prod.map (fM Dt) (id : Fin r → Fin r)) ∈ (rename (Prod.map (fM Dt) id) G0).support := by
    rw [support_rename_of_injective (fM_inj Dt)]
    exact Finset.mem_image_of_mem _ hmo
  obtain ⟨h1, h2⟩ := h _ hs
  have e : (toData Dt).dO ∘ (gO Dt) = Dt.d := funext (dO_gO Dt)
  rw [← e, ← PolK_eq, ← PolK_rename (gO Dt), ← ph_comm, rename_monomial, TwistData.ph_monomial, mem_PolK_iff]
  intro β hβ i
  have hβ' := support_monomial_subset hβ
  rw [Finset.mem_singleton] at hβ'
  subst hβ'
  rcases i with b | t
  · simp only [ldeg, TwistData.phE_apply_inl]
    exact h1 b
  · simp only [ldeg, TwistData.phE_apply_inr]
    exact h2 t

instance kkCharZero_data [CharZero O] : CharZero (G.KK O) :=
  charZero_of_injective_algebraMap (IsFractionRing.injective O (G.KK O))

end Data

theorem plane_gram_of_theorem_at {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (S : G.UniformizedDVR p O) {n' : ℕ} (hG : G.AdmissibleDVR p n' O) (hT : LiftBoundUniform (G.KK O) (vQ p S) p 1)
    {CH : ℝ} (hCH : 26 ≤ CH) : PlaneGramData.ProjectionDerivativeEstimate p O CH 2 24 60 := by
  intro r _ J _ Dt hH hc F hXX hF0
  have hp := hG.prime
  have h0 : vBB (vQ p S) (rename (Prod.map (gO Dt) id) F) = 0 := by
    rw [vBB_rename _ (gO_inj Dt)]; exact (vBB_zero_iff hp S F).mp hF0
  obtain ⟨G', R', ⟨⟨hGi, hGv⟩, hGc, hGl⟩, -, hRv, -, hRc, hGd, hRd, hBB, hB⟩ :=
    hT (dvrHyp S hG) (toData Dt) (valid_toData Dt S) (hypH_toData Dt hCH hH) (hc_toData Dt hc) _
      (inXX_toData Dt F hXX) h0
  obtain ⟨G0, rfl⟩ := exists_pre Dt G' hGv
  obtain ⟨R0, rfl⟩ := exists_pre Dt R' hRv
  have h2c := natCeil_le_two_mul_of_one_le Dt.c Dt.one_le_c
  have hcc : Dt.c ≤ ((⌈Dt.c⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hE : (toData Dt).E p 1 2 = Dt.EE 2 := by
    unfold TwistData.E PlaneGramData.SignedChainData.EE
    rw [Dm_eq, Dl_eq, kapD_eq]
  rw [← map_add, ph_comm] at hBB hB
  refine ⟨G0, R0, ?_, ⟨?_, ?_⟩, ?_, ?_, ?_, ?_⟩
  · intro mo
    rw [geQ_iff S]
    have := hGi (mo.mapDomain (Prod.map (fM Dt) id))
    rw [coeff_rename_mapDomain _ (fM_inj Dt)] at this
    have h3 := (geQ_nat_iff S (G0.coeff mo) 0).mpr (by simpa using this)
    rw [geQ_iff S] at h3
    simpa using h3
  · intro j i
    obtain ⟨j, rfl⟩ := (zE J).surjective j
    have := hGc j i
    rw [valS_transport (fM Dt) (fM_injective Dt) _ _ Dt.modelLet (Dt.chainML (zE J j) i) (sg_M Dt)
      (mem_chain Dt j i), ← geZ_iff] at this
    intro k hk
    refine le_trans ?_ (this k hk)
    show Dt.th (zE J j) i - Dt.sl (zE J j) i - 24 * Dt.c ≤
      Dt.th (zE J j) i - Dt.sl (zE J j) i - 12 * ((⌈Dt.c⌉₊ : ℕ) : ℝ)
    linarith
  · intro j m hm
    obtain ⟨j, rfl⟩ := (zE J).surjective j
    have := hGl j m hm
    rw [valS_transport (fM Dt) (fM_injective Dt) _ _ Dt.modelLet (Dt.linkML (zE J j) m) (sg_M Dt)
      (mem_link Dt j m), ← geZ_iff] at this
    intro k hk
    refine le_trans ?_ (this k hk)
    show Dt.thL (zE J j) m - 60 * Dt.c ≤ Dt.thL (zE J j) m - 30 * ((⌈Dt.c⌉₊ : ℕ) : ℝ)
    linarith
  · intro mo
    rw [geQ_iff S]
    have := hRc (mo.mapDomain (Prod.map (fM Dt) id))
    rw [coeff_rename_mapDomain _ (fM_inj Dt), hE] at this
    refine le_trans (WithTop.coe_le_coe.mpr ?_) this
    show Dt.c - Dt.EE 2 ≤ ((⌈Dt.c⌉₊ : ℕ) : ℝ) - Dt.EE 2
    linarith
  · intro mo hmo
    simp only [Finset.mem_union] at hmo
    rcases hmo with h | h
    · exact phDeg_mem Dt G0 hGd mo h
    · exact phDeg_mem Dt R0 hRd mo h
  · rw [geQ_vBB_iff hp S]
    rw [vBB_rename _ (gO_inj Dt), normShift_eq Dt hp S, kapD_eq] at hBB
    exact hBB
  · rw [leQ_iff S]
    rw [fock_rename_gaAct_rename_eq_Bform, normShift_eq Dt hp S, kapD_eq, hE] at hB
    by_cases htop : vR (vQ p S) (Dt.Bform F (Dt.ph (G0 + R0))) = ⊤
    · rw [htop, top_add] at hB
      exact absurd hB (WithTop.not_top_le_coe _)
    · obtain ⟨x, hx⟩ := WithTop.ne_top_iff_exists.mp htop
      rw [← hx] at hB ⊢
      rw [← WithTop.coe_add, WithTop.coe_le_coe] at hB
      rw [WithTop.coe_le_coe]
      linarith

end Br

end Formalism.MainNotions.PlaneGram
