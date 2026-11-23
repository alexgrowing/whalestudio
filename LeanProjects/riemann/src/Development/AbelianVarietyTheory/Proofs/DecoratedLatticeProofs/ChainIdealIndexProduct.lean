import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.VolumeSeeSawTupleLevelEqSphericalDivIndexStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemIntegralGLSplitPlaceOfCarriesLatticeCompletioStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LatticeReductionEqOneOfLocalComponentOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsContinuousLocalGLEmbeddingSplitPlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportedSubgroupOfSuppAtSplitPlaceMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdLocalParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LevelHyperspecialTrivialCharacterSplitsOffPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsCompactParahoricLevelAndContainsLifts
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LevelCharactersRamificationLevelPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSelfDualCoordLatticeOfSelfDualFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.StepConst

variable {D : D7}

theorem local_part {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) (V : HSp D) (g : GA D V) :
    ∃ c : GA D V, SuppAt q.e V c ∧ (mt V c).map q.pr = (mt V g).map q.pr ∧
      GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (g * c⁻¹) = 1 := by
  obtain ⟨ε, hε, hE⟩ := q.above
  have hεε : ε * ε = ε := by rw [GlobalTheory.SplitCut.eFin_of_placeIdem hε, GlobalTheory.SplitCut.eFin_idem]
  have hEE : (q.e + cA D q.e) * (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, ← map_mul, hεε]
  have hEc : cA D (q.e + cA D q.e) = q.e + cA D q.e := by rw [hE, GlobalTheory.SplitCut.cA_algebraMap]
  have h1 : GlobalTheory.FinPl.compAt D q.v (q.e + cA D q.e) = 1 := by
    obtain ⟨α, rfl, a1, -⟩ := hε
    rw [hE]
    change evalV D.host.F q.v α ⊗ₜ[D.host.F] (1 : D.host.E) = 1
    rw [a1]
    rfl
  obtain ⟨c, hc⟩ := GlobalTheory.SplitCut.cut_exists V g _ hEE hEc
  refine ⟨c, fun i j => ?_, ?_, ?_⟩
  · rw [hc]
    exact GlobalTheory.SplitCut.idempotent_mul_cut_sub_one_entry _ hEE _ i j
  · rw [hc, GlobalTheory.GfCut.map_idem, GlobalTheory.LevelCut.pr_sum, one_smul, sub_self, zero_smul, add_zero]
  · rw [GlobalTheory.FinPl.KOpen.proj_eq_one_iff, ← GlobalTheory.FinPl.KOpen.map_eq_one_iff, GlobalTheory.SplitCut.mt_mul, Matrix.map_mul]
    have h2 : (mt V g).map (GlobalTheory.FinPl.compAt D q.v) = (mt V c).map (GlobalTheory.FinPl.compAt D q.v) := by
      rw [hc, GlobalTheory.GfCut.map_idem, h1, one_smul, sub_self, zero_smul, add_zero]
    rw [h2, ← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, mul_inv_cancel, GlobalTheory.SplitCut.mt_one,
      Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]

theorem moves_of_St {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    {h : GA D V} (hh : finE V h ∈ St β) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves V h Λ Λ P :=
  GlobalTheory.FinPl.KOpen.moves_of_levelOpen V Λ hΛ P (GlobalTheory.AdelicU.mem_levelOpen.2
    ((GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ h).1 hh))

theorem mem_levG_of_inK {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {κ : GA D V} (hκ : GlobalTheory.FinPl.InK V Λ P κ) :
    κ ∈ levG V β L := by
  have hS : finE V κ ∈ St β := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ κ).2
    (GlobalTheory.AdelicU.mem_levelOpen.1 (GlobalTheory.FinPl.KOpen.levelOpen_of_inK V Λ hΛ P hκ))
  obtain ⟨hf, h1⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V P κ).1 hκ.1
  exact ⟨hf, GlobalTheory.LevSplit.mem_lev_of_red _ _ β L _ (GlobalTheory.LevSplit.finE_mem_UA V κ) hS fun PP h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β κ PP hS (h1 _ (hP PP h))⟩

theorem mem_levG_iff_base {V : HSp D} (β : GL (Fin V.rank) (Lev.EAf D)) {r t j : ℕ} (hr : r ≤ V.rank) (Pg Q Q₀ : Finset (Pl D.host.E))
    (P : LevelP Pg r ℂ) (χ : ℕ → ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (ξ ξ₀ : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (h₀ : Q₀ = ∅)
    (h : GA D V) : h ∈ levG V β (datY _ r t j hr Pg Q P χ ξ Frm.B) ↔ h ∈ levG V β (datY _ r t j hr Pg Q₀ P χ ξ₀ Frm.B) ∧
      ∀ PP ∈ Q, redFn β PP (finE V h) ∈ blockTri (blk2 r) := by
  subst h₀
  constructor
  · rintro ⟨hf, h1, h2⟩
    obtain ⟨a1, a2, a3, a4⟩ := mem_parLev.1 h1
    exact ⟨⟨hf, mem_parLev.2 ⟨a1, a2, a3, fun PP hP => absurd hP (Finset.notMem_empty _)⟩, h2⟩, a4⟩
  · rintro ⟨⟨hf, h1, h2⟩, a4⟩
    obtain ⟨a1, a2, a3, -⟩ := mem_parLev.1 h1
    exact ⟨hf, mem_parLev.2 ⟨a1, a2, a3, a4⟩, h2⟩

theorem red_iff_local {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y)
    (J : Subgroup (GL Y k)) {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {PP : Pl D.host.E} (hPP : PP ∈ L.Q) (hv : q.v = PP.under (𝓞 D.host.F))
    (hg : ∀ PP' ∈ L.Pg, PP'.under (𝓞 D.host.F) ≠ q.v) (hq : ∀ PP' ∈ L.Q, PP'.under (𝓞 D.host.F) = q.v → PP' = PP)
    {b : GA D V} (hb : b ∈ GfC V) (hm : GlobalTheory.FinPl.Moves V b Λ N (· = q.v)) (hN : IntIn q V Fr N)
    (hJ : ∀ x ∈ KO k Y, ∀ c, (ofSplit q).IsLoc Fr c x → (b⁻¹ * c * b ∈ levG V β L ↔ x ∈ J))
    {g : GA D V} (hS : finE V (b⁻¹ * g * b) ∈ St β) {x : GL Y k} (hx : (mt V g).map q.pr = Fr.β * x.val * Fr.γ) :
    redFn β PP (finE V (b⁻¹ * g * b)) ∈ blockTri (blk2 L.r) ↔ x ∈ J := by
  have hxK : x ∈ KO k Y := GlobalTheory.T.mem_integralGL_split_place_of_carries_latticeCompletion q V Fr N (· = q.v) rfl hN g
    ((GlobalTheory.StMoves.moves_conj_iff g hm).1 (moves_of_St hβ hΛ hS _)) x hx
  obtain ⟨c, c1, c2, c3⟩ := local_part q V g
  rw [← hJ x hxK c ⟨c1, c2.trans hx⟩]
  obtain ⟨cf, c4⟩ := (GlobalTheory.FinPl.KOpen.mem_grpAt_iff V _ c).1
    (GlobalTheory.SuppGrp.mem_grpAt_of_suppAt D k q V c c1 (· = q.v) rfl)
  have p1 : ∀ u, u ≠ q.v → GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram u (b⁻¹ * c * b) = 1 := fun u hu => by
    rw [map_mul, map_mul, c4 u hu, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have p2 : GlobalTheory.AdelicU.proj D.sp.cm.sig V.gram q.v (b⁻¹ * (g * c⁻¹) * b) = 1 := by
    rw [map_mul, map_mul, c3, mul_one, ← map_mul, inv_mul_cancel, map_one]
  have e : b⁻¹ * g * b = (b⁻¹ * (g * c⁻¹) * b) * (b⁻¹ * c * b) := by group
  have hSc : finE V (b⁻¹ * c * b) ∈ St β := by
    refine (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).2 fun u => ?_
    by_cases hu : u = q.v
    · have := (GlobalTheory.ChainOnto.LStab.finE_mem_St_iff_stabLoc D V β Λ hβ _).1 hS u
      rw [e, map_mul, hu, p2, one_mul] at this
      rw [hu]
      exact this
    · rw [p1 u hu]
      exact one_mem _
  have hSd : finE V (b⁻¹ * (g * c⁻¹) * b) ∈ St β := by
    have := mul_mem hS (inv_mem hSc)
    rw [e, map_mul, mul_inv_cancel_right] at this
    exact this
  have r1 : redFn β PP (finE V (b⁻¹ * g * b)) = redFn β PP (finE V (b⁻¹ * c * b)) := by
    rw [e, map_mul, redFn_mul hSd hSc, GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP hSd (hv ▸ p2), one_mul]
  have r2 : ∀ PP' : Pl D.host.E, PP'.under (𝓞 D.host.F) ≠ q.v → redFn β PP' (finE V (b⁻¹ * c * b)) = 1 := fun PP' h =>
    GlobalTheory.ChainOnto.RedOne.redFn_eq_one D V β _ PP' hSc (p1 _ h)
  rw [r1]
  refine ⟨fun h => ⟨(GfC V).mul_mem ((GfC V).mul_mem ((GfC V).inv_mem hb) cf) hb, mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA V _, hSc, fun PP' h' => ?_,
    fun PP' h' => ?_⟩, ?_⟩, fun h => parLev_q h.2.1 hPP⟩
  · rw [r2 PP' (hg PP' h')]
    exact one_mem _
  · by_cases h'' : PP'.under (𝓞 D.host.F) = q.v
    · rw [hq PP' h' h'']
      exact h
    · rw [r2 PP' h'']
      exact one_mem _
  · have : rTup β L (finE V (b⁻¹ * c * b)) = 1 := by
      funext PP'
      show upperLeftBlock L.hr (redFn β PP'.1 _) = 1
      rw [r2 PP'.1 (hg _ PP'.2)]
      exact blockDiagonalExtendByOnePrimeField_one _ _
    rw [this]
    exact one_mem _

def moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) : Subgroup (GA D V) := K.comap (MulAut.conj b⁻¹).toMonoidHom

theorem mem_moved {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) (g : GA D V) : g ∈ moved b K ↔ b⁻¹ * g * b ∈ K := by
  simp [moved]

theorem moved_set {V : HSp D} (b : GA D V) (K : Subgroup (GA D V)) :
    {g : GfC V | b * g.1 * b⁻¹ ∈ moved b K} = {k : GfC V | k.1 ∈ (K : Set (GA D V))} := by
  ext g
  simp [mem_moved, mul_assoc]

theorem moved_level {V : HSp D} {β : GL (Fin V.rank) (Lev.EAf D)} {Λ N : GlobalTheory.FinPl.Lat V} (hβ : IsFrame β Λ) (hΛ : Λ.FG)
    (L : LevDat D.host.E ℂ V.rank) {P : GlobalTheory.FinPl.Pl D → Prop}
    (hP : ∀ PP, PP ∈ L.Pg ∨ PP ∈ L.Q → ¬ P (PP.under (𝓞 D.host.F))) {b : GA D V} (hb : b ∈ GfC V)
    (hm : GlobalTheory.FinPl.Moves V b Λ N P) :
    moved b (levG V β L) ≤ GfC V ∧ IsCompact (moved b (levG V β L) : Set (GA D V)) ∧
      IsOpen (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) ∧
      (∀ κ, GlobalTheory.FinPl.InK V N P κ → κ ∈ moved b (levG V β L)) ∧ ∀ g ∈ moved b (levG V β L), GlobalTheory.FinPl.Moves V g N N P := by
  refine ⟨fun g hg => ?_, ?_, ?_, fun κ hκ => ?_, fun g hg => ?_⟩
  · have h1 : b⁻¹ * g * b ∈ GfC V := ((mem_moved _ _ g).1 hg).1
    have e : g = b * (b⁻¹ * g * b) * b⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hb h1) (inv_mem hb)
  · have e : (moved b (levG V β L) : Set (GA D V)) = (fun x => b * x * b⁻¹) '' (levG V β L : Set (GA D V)) := by
      ext g
      constructor
      · intro hg
        exact ⟨b⁻¹ * g * b, (mem_moved _ _ g).1 hg, by group⟩
      · rintro ⟨k, hk, rfl⟩
        refine (mem_moved _ _ _).2 ?_
        have e2 : b⁻¹ * (b * k * b⁻¹) * b = k := by group
        rw [e2]
        exact hk
    rw [e]
    exact (GlobalTheory.ParahoricCompact.isCompact_levG V β L).image (by fun_prop)
  · have e : (((moved b (levG V β L)).subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) =
        (fun x : GfC V => (⟨b, hb⟩ : GfC V)⁻¹ * x * ⟨b, hb⟩) ⁻¹' {g : GfC V | (g : GA D V) ∈ levG V β L} := by
      ext x
      exact mem_moved b (levG V β L) x.1
    rw [e]
    exact (GlobalTheory.LevelOpen.isOpen_levG V β L).preimage (by fun_prop)
  · have hn : (GlobalTheory.FinPl.grpAt V P).Normal := MonoidHom.normal_ker _
    refine (mem_moved _ _ κ).2 (mem_levG_of_inK hβ hΛ L hP ⟨?_, (GlobalTheory.StMoves.moves_conj_iff κ hm).2 hκ.2⟩)
    have := hn.conj_mem κ hκ.1 b⁻¹
    rwa [inv_inv] at this
  · exact (GlobalTheory.StMoves.moves_conj_iff g hm).1
      (moves_of_St hβ hΛ (parLev_St (lev_le_parLev ((mem_moved _ _ g).1 hg).2)) P)

theorem exists_mat {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (q : GlobalTheory.FinPl.SplitPt D k) {V : HSp D} {Y : Type} [Fintype Y] [DecidableEq Y] (Fr : GlobalTheory.LocMod.Frame k V.rank Y) (g : GA D V) :
    ∃ x : GL Y k, (mt V g).map q.pr = Fr.β * x.val * Fr.γ := by
  have hm : ∀ a a' : GA D V, a * a' = 1 → (mt V a).map q.pr * (mt V a').map q.pr = 1 := fun a a' ha => by
    rw [← Matrix.map_mul, ← GlobalTheory.SplitCut.mt_mul, ha, GlobalTheory.SplitCut.mt_one, Matrix.map_one _ (RingHom.map_zero _) (RingHom.map_one _)]
  exact GlobalTheory.LevelCut.exists_coord Fr _ _ (hm g g⁻¹ (mul_inv_cancel g)) (hm g⁻¹ g (inv_mul_cancel g))

theorem under_ne {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) (t : T) {PP PP' : Pl D.host.E} (hQ : PP ∈ L.Q t) (hg : PP' ∈ L.Pg) :
    PP'.under (𝓞 D.host.F) ≠ PP.under (𝓞 D.host.F) := by
  intro e
  obtain ⟨p, hp, hm, hne⟩ := GlobalTheory.LevelRamif.exists_prime_mem (h.Q_pl t) hQ
  obtain ⟨k, hk⟩ := (h.Pg PP').1 hg
  have key : ∀ (R : Pl D.host.E) (n : ℕ), (n : 𝓞 D.host.E) ∈ R.asIdeal ↔ (n : 𝓞 D.host.F) ∈ (R.under (𝓞 D.host.F)).asIdeal :=
    fun R n => by
      show _ ↔ algebraMap (𝓞 D.host.F) (𝓞 D.host.E) n ∈ R.asIdeal
      rw [map_natCast]
  exact GlobalTheory.LevelRamif.not_two_primes PP' hp (D.host.g_prime k) (hne k) ((key _ _).2 (e ▸ (key _ _).1 hm))
    (GlobalTheory.LevelRamif.typePrime_mem hk)

theorem base_empty {T : Type} {L : LevCh D T} {t₀ : T} (h : L.Is t₀) : L.Q t₀ = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hP => (h.Q_ram _ PP).2 (Or.inl hP) fun x _ => ?_
  rw [h.xi_base]
  rfl

theorem cI_mul_idx : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ t (w : VTup (f.t t)) (F : GlobalTheory.QPl.QFam v (f.t t)), F.Pins w → QLev f F → ∀ j, j < D.R.m → (f.t t).cI j * ∏ i, ((F.Q i).idx (j + 1) : ℂ) = (f.t W.P.A3.A.μ0).cI j := by
  intro D L hT Gi Gl Kc Yd cX ex W u f _ hRow v hv hVT t w F hPins hQL j hj
  have hL : (pk W).toLevCh.Is W.P.A3.A.μ0 := W.Q.charW.base.lev
  have hQ0 := base_empty hL
  obtain ⟨pl, hpl⟩ := hQL.places
  have hq : ∀ i, ∀ PP' ∈ (pk W).Q t, PP'.under (𝓞 D.host.F) = (F.Q i).q.v → PP' = (pl i).1 := fun i PP' h e => by
    have e1 := (hpl (pl.symm ⟨PP', h⟩)).2
    rw [Equiv.apply_symm_apply] at e1
    have e2 : pl.symm ⟨PP', h⟩ = i := hPins.inj (e1.trans e)
    rw [← e2, Equiv.apply_symm_apply]
  have hg : ∀ i, ∀ PP' ∈ (pk W).Pg, PP'.under (𝓞 D.host.F) ≠ (F.Q i).q.v := fun i PP' h => by
    rw [(hpl i).2]
    exact under_ne hL t (pl i).2 h
  have hgP : ∀ i, (F.Q i).q.v ∉ v.gP := fun i h => by
    obtain ⟨PP, h1, h2⟩ := (hVT.gP _).1 h
    exact hg i PP h1 h2.symm
  have hP : ∀ PP : Pl D.host.E, PP ∈ (pk W).Pg ∨ PP ∈ (pk W).Q W.P.A3.A.μ0 → ¬ PP.under (𝓞 D.host.F) ∈ w.Q := by
    rintro PP (h | h) h'
    · obtain ⟨i, hi⟩ := (hPins.places _).1 h'
      exact hg i PP h hi.symm
    · rw [hQ0] at h
      exact absurd h (Finset.notMem_empty _)
  have key : GlobalTheory.Fam.volLev (pk W) f.g t j * ∏ i, ((F.Q i).idx (j + 1) : ℝ) = GlobalTheory.Fam.volLev (pk W) f.g W.P.A3.A.μ0 j := by
    unfold GlobalTheory.Fam.volLev
    split_ifs with h1
    · generalize j + 1 = J at h1
      have hb : f.g.b J ∈ GfC (Yc D J) := by rw [← hVT.b J]; exact hv.b J
      have hΛ : ((pk W).ΛY J).FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ (hL.βY J h1)).1.fg
      have hβ : IsFrame ((pk W).βY J) ((pk W).ΛY J) := (hL.βY J h1).choose_spec.1
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := Yc D J) (N := v.N J) (P := (· ∈ w.Q)) hβ hΛ ((pk W).datYt W.P.A3.A.μ0 J (pk W).triv) hP hb
        (hVT.moves J h1 _ fun p hp => by
          obtain ⟨i, rfl⟩ := (hPins.places _).1 hp
          exact hgP i)
      have loc : ∀ i d hd (g : GA D (Yc D J)), finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J) ∈ St ((pk W).βY J) → ∀ x,
          (mt _ g).map (F.Q i).q.pr = ((F.Q i).FY J d hd).β * x.val * ((F.Q i).FY J d hd).γ →
          (redFn ((pk W).βY J) (pl i).1 (finE (Yc D J) ((f.g.b J)⁻¹ * g * f.g.b J)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ ((F.Q i).T.lev J d hd).J) := fun i d hd g hS x hx => by
        refine red_iff_local (N := v.N J) (F.Q i).q ((F.Q i).FY J d hd) _ hβ hΛ ((pk W).datYt t J (lvP W)) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hVT.moves J h1 _ fun p hp => hp ▸ hgP i) ((F.Q i).latY J d hd) (fun y hy c hc => ?_) hS hx
        obtain ⟨gl, -, -, hu⟩ := GlobalTheory.LocEmb.exists_gl D _ (F.Q i).q (Yc D J) _ ((F.Q i).FY J d hd)
        have e : c = (F.Q i).gl J d hd y :=
          (hu c y hc.1 hc.2).trans (hu _ y ((F.Q i).gl_loc J d hd y).1 ((F.Q i).gl_loc J d hd y).2).symm
        rw [e]
        exact (hQL.mid i J d hd h1 y hy).1
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).1 J h1 (hv.sd J h1) (f.g.μf J) (hRow.meas.μf J) _
        (moved (f.g.b J) (levG (Yc D J) ((pk W).βY J) ((pk W).datYt t J (pk W).triv))) (f.g.b J) hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((pk W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i d hd x hx => (loc i d hd g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          have hs := (F.Q i).hs
          have hd : J + ((F.Q i).s + 1 - J) = (F.Q i).s + 1 := by omega
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q ((F.Q i).FY J _ hd) g
          have := (loc i _ hd g hS x hx).2 (H i _ hd x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set (f.g.b J) (levG (Yc D J) ((pk W).βY J) ((pk W).datYt t J (pk W).triv))
      have e2 := moved_set (f.g.b J) (levG (Yc D J) ((pk W).βY J) ((pk W).datYt W.P.A3.A.μ0 J (pk W).triv))
      rw [e1, e2] at hA
      exact hA
    · have hjm : j + 1 = D.R.m := by omega
      rw [hjm]
      have hb : f.g.bT ∈ GfC D.sp.X' := by rw [← hVT.bT.1]; exact hv.bT
      have hΛ : (pk W).ΛX.FG := (GlobalTheory.SDFrameLattice.isSelfDualC_of_isSDFrame D _ _ _ _ hL.βX).1.fg
      have hβ : IsFrame (pk W).βX (pk W).ΛX := hL.βX.choose_spec.1
      have hm : ∀ P, GlobalTheory.FinPl.Moves D.sp.X' f.g.bT (pk W).ΛX v.NT P := fun P => by
        rw [hVT.bT.2]
        exact hVT.movesT P
      obtain ⟨a1, a2, a3, a4, a5⟩ := moved_level (V := D.sp.X') (N := v.NT) (P := (· ∈ w.Q)) hβ hΛ ((pk W).datXt W.P.A3.A.μ0) hP hb (hm _)
      have loc : ∀ i (g : GA D D.sp.X'), finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT) ∈ St (pk W).βX → ∀ x : GL (F.Q i).Z (F.Q i).k,
          (mt _ g).map (F.Q i).q.pr = (F.Q i).FT.β * x.val * (F.Q i).FT.γ →
          (redFn (pk W).βX (pl i).1 (finE D.sp.X' (f.g.bT⁻¹ * g * f.g.bT)) ∈ blockTri (blk2 D.R.r) ↔
            x ∈ (F.Q i).T.levTop.J) := fun i g hS x hx =>
        red_iff_local (N := v.NT) (F.Q i).q (F.Q i).FT _ hβ hΛ (datXP (pk W) (lvP W) t) (pl i).2 (hpl i).2
          (hg i) (hq i) hb (hm _) (F.Q i).latT (hQL.top i) hS hx
      have hA := (GlobalTheory.T.volume_seeSaw_tuple_level_eq_spherical_div_index D f.c v (f.t t) w F hPins).2 hv.sdT (fun i => (F.Q i).openT) f.g.μT hRow.meas.μT _
        (moved f.g.bT (levG D.sp.X' (pk W).βX ((pk W).datXt t))) f.g.bT hb a1 a2 a3 a4 a5 fun g => by
          refine (mem_moved _ _ g).trans ((mem_levG_iff_base _ _ _ _ _ _ _ _ ((pk W).xiR W.P.A3.A.μ0) hQ0 _).trans
            ((and_congr_right fun h0 => ?_).trans (and_congr_left' (mem_moved _ _ g).symm)))
          have hS := parLev_St (lev_le_parLev h0.2)
          refine ⟨fun H i x hx => (loc i g hS x hx).1 (H _ (pl i).2), fun H PP hPP => ?_⟩
          obtain ⟨i, hi⟩ := pl.surjective ⟨PP, hPP⟩
          obtain ⟨x, hx⟩ := exists_mat (F.Q i).q (F.Q i).FT g
          have := (loc i g hS x hx).2 (H i x hx)
          rw [hi] at this
          exact this
      have e1 := moved_set f.g.bT (levG D.sp.X' (pk W).βX ((pk W).datXt t))
      have e2 := moved_set f.g.bT (levG D.sp.X' (pk W).βX ((pk W).datXt W.P.A3.A.μ0))
      rw [e1, e2] at hA
      exact hA
  show cIOf (pk W) (lvP W) f.g t j * _ = cIOf (pk W) (lvP W) f.g W.P.A3.A.μ0 j
  unfold cIOf
  rw [← key]
  push_cast
  ring

end GlobalTheory.StepConst

end
