import Formalism.SharpRestriction.GrowthBounds.ChartComparison

noncomputable section

namespace Formalism.MainNotions.G.CmpJ.PCard

open Formalism.BasicNotions Formalism.MainNotions.G Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.Forms NumberField Module

theorem fin_fac {R ι : Type} [CommRing R] [DecidableEq ι] {φ : ι → Type} [∀ b, AddCommGroup (φ b)] [∀ b, Module R (φ b)]
    [Module.Finite R (∀ b, φ b)] (b : ι) : Module.Finite R (φ b) :=
  Module.Finite.of_surjective (LinearMap.proj (R := R) (φ := φ) b) fun y => ⟨Pi.single b y, by simp⟩

section Loc

variable {p : ℕ} (G : GAtP p)

theorem mem_M {x : G.Fn} : x ∈ G.M ↔ ∀ a, x a ∈ (G.lev a).funMod G.P.HtupW := by
  simp [GAtP.M, GAtP.funMod, Submodule.mem_pi]

def eM : G.M ≃ₗ[G.O] ((a : G.comp) → (G.lev a).funMod G.P.HtupW) where
  toFun x a := ⟨x.1 a, (mem_M G).1 x.2 a⟩
  invFun y := ⟨fun a => (y a).1, (mem_M G).2 fun a => (y a).2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

theorem noZero_Xsp [IsFractionRing G.O G.Kf] : NoZeroSMulDivisors G.O G.P.Xsp := by
  refine ⟨fun {c x} hx => ?_⟩
  by_cases hc : c = 0
  · exact Or.inl hc
  refine Or.inr (MvPolynomial.ext _ _ fun m => ?_)
  have h1 := congrArg (MvPolynomial.coeff m) hx
  rw [MvPolynomial.coeff_smul, MvPolynomial.coeff_zero, Algebra.smul_def] at h1
  rw [MvPolynomial.coeff_zero]
  exact (mul_eq_zero.1 h1).resolve_left fun h0 => hc (IsFractionRing.injective G.O G.Kf (by rw [h0, map_zero]))

theorem noZero_fac [IsFractionRing G.O G.Kf] (a : G.comp) : NoZeroSMulDivisors G.O ((G.lev a).funMod G.P.HtupW) := by
  have := noZero_Xsp G
  refine ⟨fun {c x} hx => ?_⟩
  have h1 : c • (x : G.P.Tup → G.P.Xsp) = 0 := by rw [← Submodule.coe_smul, hx, Submodule.coe_zero]
  rcases smul_eq_zero.1 h1 with h | h
  · exact Or.inl h
  · exact Or.inr (Subtype.ext h)

theorem finite_fac [Module.Finite G.O G.M] (a : G.comp) : Module.Finite G.O ((G.lev a).funMod G.P.HtupW) := by
  classical
  have : Module.Finite G.O ((b : G.comp) → (G.lev b).funMod G.P.HtupW) := Module.Finite.equiv (eM G)
  exact fin_fac (R := G.O) (φ := fun b => (G.lev b).funMod G.P.HtupW) a

theorem finrank_M [IsFractionRing G.O G.Kf] (hf : ∀ a, Module.Finite G.O ((G.lev a).funMod G.P.HtupW)) :
    finrank G.O G.M = ∑ a, finrank G.O ((G.lev a).funMod G.P.HtupW) := by
  have := hf
  have := noZero_fac G
  have : ∀ a, Module.Free G.O ((G.lev a).funMod G.P.HtupW) := fun a => Module.free_of_finite_type_torsion_free'
  rw [(eM G).finrank_eq, Module.finrank_pi_fintype]

theorem finrank_M_sigma [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] {Ch : Type} (cmpt : Ch → Type) [∀ β, Fintype (cmpt β)]
    (eC : (Σ β, cmpt β) ≃ G.comp) (s : Finset Ch) (hs : ∀ β (_ : cmpt β), β ∈ s) :
    finrank G.O G.M = ∑ β ∈ s, finrank G.O (gatCh G fun a : cmpt β => eC ⟨β, a⟩).M := by
  classical
  let _ : Fintype (Σ β, cmpt β) := Fintype.ofEquiv G.comp eC.symm
  have hf := finite_fac G
  rw [finrank_M G hf]
  have e1 : ∑ a, finrank G.O ((G.lev a).funMod G.P.HtupW) =
      ∑ q : (Σ β, cmpt β), finrank G.O ((G.lev (eC q)).funMod G.P.HtupW) :=
    (Fintype.sum_equiv eC _ _ fun _ => rfl).symm
  have e2 : (Finset.univ : Finset (Σ β, cmpt β)) = s.sigma fun _ => Finset.univ := by
    ext ⟨β, a⟩
    simp [hs β a]
  rw [e1, e2, Finset.sum_sigma]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [finrank_M (gatCh G fun a : cmpt β => eC ⟨β, a⟩) fun a => hf _]

end Loc

section Forms

variable {D : D7} {u : D.what₂.Word} {C : ColumnChain D.R D.what₂.Tau (D.hcW u)} {A : ColumnsAtT D.R C} {P : PeriodMap D.R C}
  {M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P} {p : ℕ} {i : ℕ} {hi : i ≤ D.R.m} {G : GAtP p}

theorem card_eq_finrank (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (i : ℕ) :
    Fintype.card (M.lat i).ι = finrank ℂ (M.Fi i) := by
  rw [← (M.emb_basis i).2]
  exact (finrank_span_eq_card (M.emb_basis i).1).symm

theorem fin_Fi (M : MemberForms D.what₂.LL D.what₂.embLL D.what₂.places D.what₂.Tau (D.hcW u) C A P) (i : ℕ) :
    FiniteDimensional ℂ (M.Fi i) := by
  rw [← (M.emb_basis i).2]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range _)

open Classical in

def chs (S : StepIn M i hi G) : Finset S.Ch :=
  Finset.univ.image S.chOf ∪ Finset.univ.image fun a : G.comp => (S.eC.symm a).1

open Classical in
theorem chOf_mem (S : StepIn M i hi G) (c : C.cls i) : S.chOf c ∈ chs S :=
  Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ c))

open Classical in
theorem cmpt_mem (S : StepIn M i hi G) (β : S.Ch) (a : S.cmpt β) : β ∈ chs S :=
  Finset.mem_union_right _ (Finset.mem_image.2 ⟨S.eC ⟨β, a⟩, Finset.mem_univ _, by rw [Equiv.symm_apply_apply]⟩)

abbrev FiB (S : StepIn M i hi G) (β : S.Ch) := FiC (S.K β).lev (embT D) (lamTG M i) (S.K β).y

def eF (S : StepIn M i hi G) : M.Fi i ≃ₗ[ℂ] ((β : chs S) → FiB S β.1) where
  toFun φ β := ⟨fun c z => φ.1 c.1 (S.eY.symm z), (S.val.Fi φ.1).1 φ.2 β.1⟩
  invFun ψ := ⟨fun c y => (ψ ⟨S.chOf c, chOf_mem S c⟩).1 ⟨c, rfl⟩ (S.eY y), (S.val.Fi _).2 fun β => by
    by_cases hβ : β ∈ chs S
    · convert (ψ ⟨β, hβ⟩).2 using 1
      funext c z
      rcases c with ⟨c, hc⟩
      subst hc
      simp
    · have : IsEmpty {c // S.chOf c = β} := ⟨fun ⟨c, hc⟩ => hβ (hc ▸ chOf_mem S c)⟩
      convert Submodule.zero_mem _ using 1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv φ := by
    apply Subtype.ext
    funext c y
    simp
  right_inv ψ := by
    funext ⟨β, hβ⟩
    apply Subtype.ext
    funext c z
    rcases c with ⟨c, hc⟩
    change S.chOf c = β at hc
    subst hc
    simp

theorem finrank_Fi (S : StepIn M i hi G) : finrank ℂ (M.Fi i) = ∑ β ∈ chs S, finrank ℂ (FiB S β) := by
  classical
  have := fin_Fi M i
  have : Module.Finite ℂ ((β : chs S) → FiB S β.1) := Module.Finite.equiv (eF S)
  have : ∀ β : chs S, Module.Finite ℂ (FiB S β.1) := fun β => fin_fac (R := ℂ) (φ := fun β : chs S => FiB S β.1) β
  rw [(eF S).finrank_eq, Module.finrank_pi_fintype, Finset.sum_coe_sort (chs S) fun β => finrank ℂ (FiB S β)]

def ChartRank (S : StepIn M i hi G) : Prop :=
  ∀ β, finrank ℂ (FiB S β) = finrank G.O (gatCh G fun a : S.cmpt β => S.eC ⟨β, a⟩).M

theorem card_of [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] (S : StepIn M i hi G) (hR : ChartRank S) :
    Fintype.card (M.lat i).ι = finrank G.O G.M := by
  rw [card_eq_finrank, finrank_Fi S, finrank_M_sigma G S.cmpt S.eC (chs S) (cmpt_mem S)]
  exact Finset.sum_congr rfl fun β _ => hR β

theorem card_le [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (w : D.what₂.places.Pl) (hw : S.okW w) (hloc : S.ValIntJ e w) :
    Fintype.card (M.lat i).ι ≤ finrank G.O G.M := by
  have hli := StepIn.cmpJ_li (S := S) e H hS
  have hmem := fun a => StepIn.cmpJ_mem_span (S := S) e H hS w hw hloc ((M.lat i).b a)
  have hli' : LinearIndependent G.Kf fun a => (⟨_, hmem a⟩ : Submodule.span G.Kf (G.M : Set G.Fn)) :=
    LinearIndependent.of_comp (Submodule.span G.Kf (G.M : Set G.Fn)).subtype hli
  have h1 := hli'.cardinal_le_rank
  have h2 := Formalism.L2.G.finrank_span_le (Kf := G.Kf) G.M
  rw [Cardinal.mk_fintype] at h1
  exact_mod_cast h1.trans h2

def ChartRankGe (S : StepIn M i hi G) : Prop :=
  ∀ β, finrank G.O (gatCh G fun a : S.cmpt β => S.eC ⟨β, a⟩).M ≤ finrank ℂ (FiB S β)

theorem finrank_M_le [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] (S : StepIn M i hi G) (hR : ChartRankGe S) :
    finrank G.O G.M ≤ Fintype.card (M.lat i).ι := by
  rw [card_eq_finrank, finrank_Fi S, finrank_M_sigma G S.cmpt S.eC (chs S) (cmpt_mem S)]
  exact Finset.sum_le_sum fun β _ => hR β

theorem card_of_ge [IsFractionRing G.O G.Kf] [Module.Finite G.O G.M] (S : StepIn M i hi G) (e : D.what₂.LL →+* G.Kf)
    (H : ∀ β, S.Core e β) (hS : BlockRationalityField) (w : D.what₂.places.Pl) (hw : S.okW w) (hloc : S.ValIntJ e w) (hR : ChartRankGe S) :
    Fintype.card (M.lat i).ι = finrank G.O G.M :=
  le_antisymm (card_le S e H hS w hw hloc) (finrank_M_le S hR)

end Forms

variable {D : D7} {Tw : TwForms D} {u : D.what₂.Word} {μ : D.what₂.Tup} {w : D.what₂.places.Pl}
  {h : GIdx D.host (D.mem u).A.T (D.what₂.places.resChar w)} {Fl : Fills (D.gat u w h)} {Lv : Levels Fl}

theorem card_of_charts (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (hR : ∀ j hj, ChartRank (I.at' j hj).st) (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    Fintype.card ((I.at' j hj).M.lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M := by
  have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
  have : Module.Finite (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).M := mfin_of Gt u w h Lv (j + 1) (hfin j hj)
  exact card_of (I.at' j hj).st (hR j hj)

theorem card_of_charts_ge (c : LatCmp D) (I : CmpJIn Tw u μ w h Lv) (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses) (hR : ∀ j hj, ChartRankGe (I.at' j hj).st)
    (j : ℕ) (hj : j + 1 ≤ D.R.m) :
    Fintype.card ((I.at' j hj).M.lat (j + 1)).ι = Module.finrank (D.gat u w h).O (gatJ Lv (j + 1)).M := by
  have : IsFractionRing (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).Kf := ((D.gat u w h).P.setting (plc Gt u w h)).frac_O
  have : Module.Finite (gatJ Lv (j + 1)).O (gatJ Lv (j + 1)).M := mfin_of Gt u w h Lv (j + 1) (hfin j hj)
  exact card_of_ge (I.at' j hj).st (c.embW u w h) (core j hj) hS w (ok j hj)
    (StepIn.valIntJ_of (S := (I.at' j hj).st) (c.embW u w h) w (twUnit j hj) (valIntN j hj)) (hR j hj)

theorem cmpJHyp_of_ge (c : LatCmp D) {I : CmpJIn Tw u μ w h Lv} (Gt : GatTies D) (hS : BlockRationalityField)
    (core : ∀ j hj β, (I.at' j hj).st.Core (c.embW u w h) β) (ok : ∀ j hj, (I.at' j hj).st.okW w)
    (twUnit : ∀ j hj β, (I.at' j hj).st.TwUnit w β) (valIntN : ∀ j hj, (I.at' j hj).st.ValIntN (c.embW u w h) w)
    (iwF : ∀ j hj β, (I.at' j hj).st.IwF β) (hfin : ∀ j, j + 1 ≤ D.R.m → (gatJ Lv (j + 1)).FinClasses)
    (hR : ∀ j hj, ChartRankGe (I.at' j hj).st) : CmpJHyp c I :=
  ⟨core, ok, twUnit, valIntN, iwF, hfin, card_of_charts_ge c I Gt hS core ok twUnit valIntN hfin hR⟩

end Formalism.MainNotions.G.CmpJ.PCard

end
