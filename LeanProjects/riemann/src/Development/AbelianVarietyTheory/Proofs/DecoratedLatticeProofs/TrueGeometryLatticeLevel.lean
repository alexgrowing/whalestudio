import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Live
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepIndexLeS
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryFiniteAdelicGroupSplitFinitePlaceSet
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IdempotentMulEntryEqZeroOfCutInverse
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryTwistLocalData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TrueGeometryLatticeOpenStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StepData GlobalTheory.SplitWeil

noncomputable section
namespace GlobalTheory.LevOnto

theorem list_prod_map_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) (k : Fin n) :
    ∀ l : List (Fin n), l.Nodup → ((l.map fun i => Pi.mulSingle i (x i) k).prod = if k ∈ l then x k else 1)
  | [], _ => by simp
  | b :: l, hl => by
    rw [List.nodup_cons] at hl
    rw [List.map_cons, List.prod_cons, list_prod_map_mulSingle x k l hl.2]
    by_cases hb : b = k
    · subst hb
      simp [hl.1]
    · rw [Pi.mulSingle_eq_of_ne (Ne.symm hb), one_mul]
      simp [List.mem_cons, Ne.symm hb]

theorem list_prod_mulSingle {n : ℕ} {G : Fin n → Type*} [∀ i, Monoid (G i)] (x : ∀ i, G i) :
    ((List.finRange n).map fun i => Pi.mulSingle i (x i)).prod = x := by
  funext k
  rw [Pi.list_prod_apply, List.map_map]
  have := list_prod_map_mulSingle x k (List.finRange n) (List.nodup_finRange n)
  simpa [Function.comp_def] using this

theorem map_pr_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k']
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : (mt V g).map q'.pr = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  obtain ⟨ε', hε', hE'⟩ := q'.above
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε] at hE
  rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε'] at hE'
  have hsp := q'.split
  have h0 : q'.e * (q.e + cA D q.e) = 0 := by
    have h1 : q'.e = q'.e * (q'.e + cA D q'.e) := by rw [mul_add, hsp.1, hsp.2.1, add_zero]
    rw [h1, mul_assoc, hE', hE, ← map_mul, GlobalTheory.LocWeil.PlaceIdem.eFin_mul_eFin _ (Ne.symm hv), map_zero, mul_zero]
  have hpr : q'.pr (q.e + cA D q.e) = 0 := by
    rw [← q'.pr_sec (q'.pr _), q'.sec_pr, h0, map_zero]
  ext a b
  rw [Matrix.map_apply]
  have h2 : mt V g a b = (mt V g - 1) a b + (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) a b := by
    rw [Matrix.sub_apply, sub_add_cancel]
  rw [h2, map_add, ← hg a b, map_mul, hpr, zero_mul, zero_add]
  by_cases hab : a = b <;> simp [Matrix.one_apply, hab]

theorem locHom_eq_one {D : D7} {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [Field k'] [ValuativeRel k'] [TopologicalSpace k'] [IsNonarchimedeanLocalField k'] {Y : Type} [Fintype Y] [DecidableEq Y]
    (q : GlobalTheory.FinPl.SplitPt D k) (q' : GlobalTheory.FinPl.SplitPt D k') (V : HSp D) (F : Frame k' V.rank Y) (g : GA D V)
    (hg : SuppAt q.e V g) (hv : q.v ≠ q'.v) : GlobalTheory.LevIdx.locHom q' V F g = 1 := by
  refine ((GlobalTheory.LevIdx.eq_locHom_iff q' V F g 1).1 ?_).symm
  rw [map_pr_eq_one q q' V g hg hv, Units.val_one, Matrix.mul_one, F.βγ]

variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

theorem same_pl (hW : AllTrue W) (ha : a.Is) (hTr : a.True) {t t₂ : W.P.T} (J : QJ a t) (hJ : J.Reads) (J₂ : QJ a t₂)
    (hJ₂ : J₂.Reads) (i : Fin J.r) (i₂ : Fin J₂.r) (h : (J.G i).q.v = (J₂.G i₂).q.v) : J.pl i = J₂.pl i₂ := by
  have h1 := (GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t J hJ).2 i
  have h2 := (GlobalTheory.Fam.QJPlaces.places_under W hW u a ha hTr t₂ J₂ hJ₂).2 i₂
  exact hW.pk.sel _ _ ⟨t, J.mem i⟩ ⟨t₂, J₂.mem i₂⟩ (h1.symm.trans (h.trans h2))

theorem locHom_gl (j : ℕ) {PP} (h₁ h₂ : QAll W PP) (hj₁ : j ≤ (a.Q PP h₁).s + 1) (hj₂ : j ≤ (a.Q PP h₂).s + 1)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (a.Q PP h₂).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, (mt _ (gl y)).map (a.Q PP h₂).q.pr = ((a.Q PP h₂).FX j hj₂).β * y.val * ((a.Q PP h₂).FX j hj₂).γ) (y) :
    GlobalTheory.LevIdx.locHom (a.Q PP h₁).q _ ((a.Q PP h₁).FX j hj₁) (gl y) = y :=
  ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 (hgl y)).symm

end GlobalTheory.LevOnto
end

namespace GlobalTheory.LevOnto
variable {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : B.Word} {a : GeoAll W u}

theorem mem_relax (hW : AllTrue W) (ha : a.Is) (hTr : a.True) (j : ℕ) (hj : j + 2 ≤ B.R.m) {t t₂ : W.P.T} (J : QJ a t) (hJ : J.Reads)
    (α : J.Ch j) (J₂ : QJ a t₂) (hJ₂ : J₂.Reads) (i : Fin J₂.r)
    (gl : GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J₂.G i).k →* GA (I.rec7 l Z) ((I.rec7 l Z).sp.X j))
    (hgl : ∀ y, SuppAt (J₂.G i).q.e _ (gl y) ∧ (mt _ (gl y)).map (J₂.G i).q.pr =
      ((J₂.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J₂ i hj; omega)).β * y.val * ((J₂.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J₂ i hj; omega)).γ)
    (y) (hy : y ∈ KO (J₂.G i).k (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j)) : gl y ∈ GlobalTheory.LevProd.relax J j hj α := by
  have hAt : ∀ P : GlobalTheory.FinPl.Pl (I.rec7 l Z) → Prop, P (J₂.G i).q.v → gl y ∈ GlobalTheory.FinPl.grpAt _ P :=
    GlobalTheory.SuppGrp.mem_grpAt_of_suppAt _ _ _ _ _ (hgl y).1
  refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨?_, GlobalTheory.FinPl.SetCut.grpAt_le_GfC _ _ (hAt (· = (J₂.G i).q.v) rfl)⟩, ?_⟩
  · by_cases hv : GlobalTheory.LevProd.twAt J (J₂.G i).q.v
    · exact Subgroup.mem_sup_right (hAt _ hv)
    · exact Subgroup.mem_sup_left (GlobalTheory.T.true_geometry_lattice_open W hW u a ha hTr j hj t J hJ α t₂ J₂ hJ₂ i hv gl hgl y hy)
  · rw [Subgroup.mem_comap, Subgroup.mem_pi]
    intro i' _
    show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl y) ∈ KO (J.G i').k _
    by_cases hv : (J.G i').q.v = (J₂.G i).q.v
    · have e := same_pl hW ha hTr J hJ J₂ hJ₂ i' i hv
      have key : ∀ P (hP : P ∈ (pk W).Q t) (hj₁ : j ≤ (a.Q P ⟨t, hP⟩).s + 1), P = J₂.pl i →
          GlobalTheory.LevIdx.locHom (a.Q P ⟨t, hP⟩).q _ ((a.Q P ⟨t, hP⟩).FX j hj₁) (gl y) ∈ KO (a.Q P ⟨t, hP⟩).k
            (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) := by
        rintro P hP hj₁ rfl
        rw [locHom_gl j _ _ hj₁ _ gl (fun y => (hgl y).2) y]
        exact hy
      exact key _ (J.mem i') _ e
    · rw [locHom_eq_one (J₂.G i).q (J.G i').q _ _ (gl y) (hgl y).1 (Ne.symm hv)]
      exact one_mem _

theorem onto : ∀ {B : GlobalTheory.Mem.Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ (u : B.Word) (a : GeoAll W u), a.Is → a.True → ∀ j (hj : j + 2 ≤ B.R.m), ∀ t (J : QJ a t), J.Reads → J.Ch j → ∀ x : (i : Fin J.r) → GL (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) (J.G i).k, (∀ i, x i ∈ KO (J.G i).k _) → ∃ g ∈ GlobalTheory.LevProd.Up a j hj, GlobalTheory.LevProd.phi J j hj g = x := by
  intro B X I l Z L hT Gi Gl Kc Yd cX ex W hW u a ha hTr j hj t J hJ α x hx
  have hex : ∃ t, ∃ J : QJ a t, J.Reads ∧ Nonempty (J.Ch j) := ⟨t, J, hJ, ⟨α⟩⟩
  have hUp : GlobalTheory.LevProd.Up a j hj = GlobalTheory.LevProd.relax hex.choose_spec.choose j hj hex.choose_spec.choose_spec.2.some := by
    unfold GlobalTheory.LevProd.Up
    rw [dif_pos hex]
  have hJ₀ : hex.choose_spec.choose.Reads := hex.choose_spec.choose_spec.1
  have hgl := fun i : Fin J.r => GlobalTheory.LocEmb.exists_gl _ _ (J.G i).q ((I.rec7 l Z).sp.X j)
    (XIx (Fin (I.rec7 l Z).R.k) (Fin (I.rec7 l Z).R.t) j) ((J.G i).FX j (by have := GlobalTheory.LevProd.step_index_le_s J i hj; omega))
  choose gl _ hglp _ using hgl
  refine ⟨((List.finRange J.r).map fun i => gl i (x i)).prod, ?_, ?_⟩
  · rw [hUp]
    apply Subgroup.list_prod_mem
    intro g hg
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact mem_relax hW ha hTr j hj _ hJ₀ _ J hJ i (gl i) (hglp i) (x i) (hx i)
  · rw [map_list_prod, List.map_map]
    have hphi : ∀ i, GlobalTheory.LevProd.phi J j hj (gl i (x i)) = Pi.mulSingle i (x i) := by
      intro i
      funext i'
      show GlobalTheory.LevIdx.locHom (J.G i').q _ ((J.G i').FX j _) (gl i (x i)) = _
      by_cases h : i' = i
      · subst h
        rw [Pi.mulSingle_eq_same]
        exact ((GlobalTheory.LevIdx.eq_locHom_iff _ _ _ _ _).1 ((hglp i' (x i')).2)).symm
      · rw [Pi.mulSingle_eq_of_ne h]
        refine locHom_eq_one (J.G i).q (J.G i').q _ _ _ (hglp i (x i)).1 fun hv => h ?_
        exact hJ.inj (same_pl hW ha hTr J hJ J hJ i' i hv.symm)
    simp only [Function.comp_def, hphi]
    exact list_prod_mulSingle x

end GlobalTheory.LevOnto
