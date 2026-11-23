import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Framed
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevTrue
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.OnFramesRdApply
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.RatioOKOfRootOfUnity
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ChainParSucc
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LineVectorBesselExistenceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsGeometricMeasureVolumeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsKFinOfMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AllTrueFamilyGeometryColumnStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentVectorRelationStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSymmetricDataAtTypePlacesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLevelData
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentPlacesCharacterizedStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocalComponentAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FixLevCompactOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SymRead

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.MiTop GlobalTheory.Fam GlobalTheory.Mem.Col2 ValuativeRel IsLocalRing
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GeoExists

section Transport

variable {D : D7} {c : Comm D} {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type}

theorem shape_upd {v : VCom c} {o : GlobalTheory.SeeSaw.TDat c k ι} (h : ShapeOff v o) (b Ψ ΨT JG eG eGT dG) :
    ShapeOff { v with b := b, Ψ := Ψ, ΨT := ΨT, JG := JG, eG := eG, eGT := eGT, dG := dG } o :=
  ⟨⟨h.pre.nodup, h.pre.all, h.pre.inj, h.pre.tP, h.pre.char, h.pre.latT, h.pre.line, h.pre.tau, h.pre.lam, h.pre.normT, h.pre.topT⟩,
    fun x => ⟨(h.good x).bf, (h.good x).fb⟩, fun x hx => ⟨(h.split x hx).core, (h.split x hx).top⟩, h.glued, h.rep, h.ram⟩

theorem moves_one (S : HSp D) (L : GlobalTheory.FinPl.Lat S) (P : GlobalTheory.FinPl.Pl D → Prop) : GlobalTheory.FinPl.Moves S 1 L L P := fun y _ => by
  have e : Formalism.L2.Theta.mt S 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [e, Matrix.one_mulVec]

theorem exists_places (D : D7) (T : ℕ) (hT : T ≠ 0) : ∃ s : Finset (GlobalTheory.FinPl.Pl D), ∀ p, p ∈ s ↔ ((T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal := by
  have h0 : Ideal.span {((T : ℕ) : 𝓞 D.host.F)} ≠ 0 := by
    simpa [Ideal.span_singleton_eq_bot] using hT
  refine ⟨(Ideal.finite_factors h0).toFinset, fun p => ?_⟩
  rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]

end Transport

section Gen

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Yd : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Yd cX} {W : RealPack ex} {u : D.what₂.Word}

theorem meas_upd {a : XGeo D} {y : YRat a} {m : YMeas y} {b} (h : GeoMeas (pk W) (mkGeo m b)) (b') : GeoMeas (pk W) (mkGeo m b') :=
  ⟨h.μf, h.μT, h.ρJ, h.ρB, h.κ, h.vol, h.volT⟩

theorem tie_upd {f : FamCh W u} {v : VCom f.c} (h : VTie f v) (JG eG eGT dG) :
    VTie f { v with JG := JG, eG := eG, eGT := eGT, dG := dG } :=
  ⟨h.b, h.bT, h.gP, h.tP, h.moves, h.movesT, h.Ψ, h.ΨT, h.nz⟩

theorem selfDual_top (h : PkHyp W) : IsSelfDualC D.sp.X' (pk W).ΛX := by
  obtain ⟨c, hc⟩ := h.bot.hyp.2.2.2.1.lev.βX
  exact GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hc

def xOf (A : GeoAll W u) : XGeo D := ⟨A.g.x, A.g.vac, A.g.Lz, A.g.oT, A.o.ζ₀, A.g.bT, A.g.LT⟩

set_option maxHeartbeats 2000000 in

theorem core (hD : GlobalTheory.Published.DiscreteSeriesCover) (hH : GlobalTheory.Published.HarishChandraModules) (hPk : PkHyp W)
    (hTy : GlobalTheory.Core.Mi.IsTypePlaces (pk W).Pg) (hT0 : ((D.mem u).A.T : ℕ) ≠ 0)
    (hGT : ∀ PP ∈ (pk W).Pg, (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) (hQG : ∀ PP, QAll W PP → PP ∉ (pk W).Pg)
    (jj : SmT (pk W).MX →ₗ[ℂ] (Formalism.L2.Forms.FrP D → ℂ)) (hjj : TopReadAt W u jj 1)
    (a : XGeo D) (c₀ : ℕ → ℂ) (hx : ∀ j, j ≤ D.R.m → (a.x j).Is) (hbT : a.bT = 1) (hLT : a.LT = (pk W).ΛX)
    (hline : IsLineVec a.Lz a.ζ₀) (hn : star a.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ a.ζ₀ = (((D.mem u).A.T : ℕ) : D.host.E))
    (horth : ∀ n (h : n = D.R.m) (x : GlobalTheory.FinPl.Pl D), (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∉ x.asIdeal →
      ∃ LZ : GlobalTheory.FinPl.Lat a.Lz, IsSelfDualC _ LZ ∧ GlobalTheory.FinPl.OrthAt (a.oT n h) (a.x n).L a.LT LZ x)
    (hloc : ∀ PP, PP ∈ (pk W).Pg ∨ QAll W PP → ∃ s : LocX a (pk W).βX PP,
      (∀ j hj, IsStdFr GlobalTheory.SymBridge.xPos (s.FX j hj)) ∧ IsStdFr GlobalTheory.SymBridge.zPos s.FT)
    (R : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ι : Type)
      (p : ι → GlobalTheory.FinPl.SplitPt D k), (∀ j i, GlobalTheory.FinPl.Frame (p i) (D.sp.X j) (Fin (D.sp.X j).rank)) →
        (∀ j, ι → GlobalTheory.LatPair.Pair k (Fin (D.sp.X j).rank)) → Prop)
    (hpre : ∀ (y : YRat a) (m : YMeas y) (b) (v : VCom (commOf (pk W) u (mkGeo m b))), v.NT = (pk W).ΛX →
      (∀ p, p ∈ v.tP ↔ (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ p.asIdeal) → v.τ = y.τ → y.Tau (-D.host.xi0 ^ (D.R.m / 2)) →
      ∃ (k : Type) (_ : Field k) (_ : ValuativeRel k) (_ : TopologicalSpace k) (_ : IsNonarchimedeanLocalField k) (ι : Type)
        (o : GlobalTheory.SeeSaw.TDat (commOf (pk W) u (mkGeo m b)) k ι), PreT v o ∧ o.ζ₀ = a.ζ₀ ∧ R k ι o.p o.β o.Q) :
    ∃ A : GeoAll W u, A.Is ∧ A.c₀ = c₀ ∧ xOf A = a ∧ Framed A.d.B ∧ R A.k A.ι A.o.p A.o.β A.o.Q := by
  obtain ⟨y, Bt, h0, hτ, hlev, had, hfr, -, hz⟩ := GlobalTheory.T.line_vector_bessel_existence W u hPk a hline hn
  obtain ⟨m, hm₀, hlast⟩ := GlobalTheory.T.exists_geometric_measure_volume W u hPk a y (fun _ => 1) hx
  have hc₀ := GlobalTheory.Fam.commOf_is hD hH W u hPk _ hm₀ hx
  obtain ⟨tP, htP⟩ := exists_places D _ hT0
  obtain ⟨gP, hgP⟩ : ∃ s : Finset (GlobalTheory.FinPl.Pl D), ∀ p, p ∈ s ↔ ∃ PP ∈ (pk W).Pg, p = PP.under (𝓞 D.host.F) :=
    ⟨(pk W).Pg.image fun PP => PP.under (𝓞 D.host.F), fun p => by simp only [Finset.mem_image, eq_comm]⟩
  have hdisj : Disjoint gP tP := Finset.disjoint_left.2 fun p h1 h2 => by
    obtain ⟨PP, hP, rfl⟩ := (hgP p).1 h1
    refine hGT PP hP ?_
    have h3 : algebraMap (𝓞 D.host.F) (𝓞 D.host.E) ((D.mem u).A.T : ℕ) ∈ PP.asIdeal := (htP _).1 h2
    rwa [map_natCast] at h3
  have hsd : IsSelfDualC D.sp.X' a.LT := hLT ▸ selfDual_top hPk
  let v₀ : VCom (commOf (pk W) u (mkGeo m fun _ => 1)) :=
    { gP := gP, tP := tP, N := fun _ => ⊥, NT := a.LT, b := fun _ => 1, bT := a.bT, Ψ := 0, ΨT := fun _ _ => 0, τ := y.τ, JG := fun _ => ⊥,
      eG := 0, eGT := fun _ _ => 0, dG := 0, cG := 0, RamAd := fun _ => ∅, Sad := fun _ => id, dT := 0,
      op := fun _ => ⟨0, Fin.elim0, Fin.elim0⟩ }
  obtain ⟨k, _, _, _, _, ι, o, hP, hζ, hR⟩ := hpre y m _ v₀ hLT htP rfl hτ
  choose l hlX hlT using hloc
  obtain ⟨S, hS⟩ := GlobalTheory.T.exists_symmetric_data_at_type_places W u hPk hTy a fun PP => l PP.1 (Or.inl PP.2)
  obtain ⟨bas, hb1, hb2⟩ : ∃ bas : ∀ PP h j c, j + c = (l PP h).s + 1 → GL (XIx (Fin D.R.k) (Fin D.R.t) j ⊕ Fin c) (l PP h).k,
      (∀ PP h, PP ∉ (pk W).Pg → bas PP h = fun _ _ _ => 1) ∧
      ∀ PP : (pk W).Pg, bas PP.1 (Or.inl PP.2) = fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc :=
    ⟨fun PP h => if hp : PP ∈ (pk W).Pg then fun j c hc => ((S ⟨PP, hp⟩).T (Fin D.R.t)).bas j c hc else fun _ _ _ => 1,
      fun PP h hp => dif_neg hp, fun PP => dif_pos PP.2⟩
  obtain ⟨N, b, dT, M, β₀, hsh, hb, hN, hY⟩ := GlobalTheory.T.local_component_vector_relation W u hPk a y m _ k ι v₀ o l bas hc₀ hτ hn rfl rfl hζ hsd hgP htP hP
    (fun n h x hx => horth n h x fun h' => hx ((htP x).2 h')) fun PP h hp j c hc => by rw [hb1 PP h hp]
  have hm := meas_upd hm₀ b
  have hc := GlobalTheory.Fam.commOf_is hD hH W u hPk _ hm hx
  have hbT' : a.bT ∈ GfC D.sp.X' := hbT ▸ Subgroup.one_mem _
  let v₁ : VCom (commOf (pk W) u (mkGeo m b)) :=
    { gP := gP, tP := tP, N := N, NT := a.LT, b := b, bT := a.bT, Ψ := 0, ΨT := fun _ _ => 0, τ := y.τ, JG := fun _ => ⊥,
      eG := 0, eGT := fun _ _ => 0, dG := 0, cG := 0, RamAd := o.Ram, Sad := fun _ => id, dT := dT,
      op := fun _ => ⟨0, Fin.elim0, Fin.elim0⟩ }
  obtain ⟨Ψ, ΨT, hΨ, hΨT, htie⟩ := GlobalTheory.T.local_component_places_characterized W u hPk a y m b v₁ hc rfl rfl hgP hTy (fun j => (hb j).1) hbT' hsd
    (fun P => by rw [hbT, hLT]; exact moves_one _ _ _) hN rfl rfl htP
  have hYG : ∀ PP : (pk W).Pg, LocY (l PP.1 (Or.inl PP.2)) y N (pk W).βY b fun j c hc => ((S PP).T (Fin D.R.t)).bas j c hc :=
    fun PP => hb2 PP ▸ (hY PP.1 (Or.inl PP.2)).some
  obtain ⟨JG, eG, eGT, dG, n, G, pl, hG, hat, hrd, hstd⟩ := GlobalTheory.LevPin.exists_levelData W u hPk a y m b { v₁ with Ψ := Ψ, ΨT := ΨT } hc rfl rfl hgP
    hTy _ S hS hYG fun PP => ⟨hlX _ _, hlT _ _⟩
  let v : VCom (commOf (pk W) u (mkGeo m b)) := { v₁ with Ψ := Ψ, ΨT := ΨT, JG := JG, eG := eG, eGT := eGT, dG := dG }
  choose Q hQ using fun PP (h : QAll W PP) => GlobalTheory.T.local_component_at_split_place W u hPk a y m b v hc rfl rfl PP h (l PP (Or.inr h))
    (hb1 PP (Or.inr h) (hQG PP h) ▸ (hY PP (Or.inr h)).some) (hlX _ _) (hlT _ _)
  have hv : v.Is :=
    ⟨hdisj, fun j hj => (hN j hj).1, hsd, fun j => (hb j).1, hbT', hΨ, hΨT, GlobalTheory.FixLev.fixLev_compact_open D _ v n G hG, hat,
      fun j => ⟨(hb j).2, fun i => i.elim0⟩, fun j φ hφ => ⟨hφ.1, hφ⟩⟩
  refine ⟨⟨mkGeo m b, jj, k, ι, v, { o with M := M, β₀ := β₀ }, n, G, pl, Q, ⟨Bt, b 0, 1, 1, 1⟩, c₀⟩,
    ⟨hm, hlast, hx, hv, shape_upd hsh b Ψ ΨT JG eG eGT dG, hG,
      fun row col => ⟨tie_upd (htie jj row col) JG eG eGT dG, hrd jj row col⟩, ?_, ?_, ?_, ?_, ⟨fun _ => hlev, rfl, had, hz⟩⟩,
    rfl, ?_, hfr, hR⟩
  · show TopReadAt W u jj a.bT
    rw [hbT]; exact hjj
  · show star o.ζ₀ ⬝ᵥ a.Lz.gram *ᵥ o.ζ₀ = _ ∧ ∀ j h, y.τ j h *ᵥ o.ζ₀ = _
    rw [hζ]; exact ⟨hn, fun j h => (hτ j h).2⟩
  · intro i
    refine ⟨(hstd i).1, (hstd i).2.1, (hstd i).2.2.trans ?_⟩
    rw [← hζ]
  · intro PP h
    refine ⟨(hQ PP h).1, (hQ PP h).2.1, (hQ PP h).2.2.trans ?_⟩
    rw [← hζ]
  · show (⟨a.x, a.vac, a.Lz, a.oT, o.ζ₀, a.bT, a.LT⟩ : XGeo D) = a
    rw [hζ]

end Gen

set_option maxHeartbeats 2000000 in

theorem exists_geoAll : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.StrongApproxSU → ∀ {B : GlobalTheory.Mem.Base} {X : GlobalTheory.Mem.PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {L : SizeData₂ (I.rec7 l Z)} {hT : GatTies (I.rec7 l Z)} {Gi : Formalism.MainNotions.G.Inst (I.rec7 l Z) L} {Gl : Formalism.MainNotions.G.LatInst (I.rec7 l Z)} {Kc : Formalism.MainNotions.G.Consts} {Yd : DivX (I.rec7 l Z)} {cX : ExtraC} {ex : Extra (I.rec7 l Z) L hT Gi Gl Kc Yd cX} (W : RealPack ex), AllTrue W → ∀ u : B.Word, ∃ a : GeoAll W u, a.Is ∧ a.True ∧ (∀ r s, (a.g.oT B.R.m rfl).iA r s = if r.val = s.val then 1 else 0) ∧ GlobalTheory.MiTop.Framed a.d.B := by
  intro hD hH hS B X I l Z L hT Gi Gl Kc Yd cX ex W hW u
  obtain ⟨a, c₀, hx, hpin, hbT, hiA, hLT, hline, hn, hemb, hz, horth, hloc⟩ := GlobalTheory.T.all_true_family_geometry hS W hW u
  obtain ⟨jj, hjj⟩ := hW.tq.top1 u
  have hPr := (base_fields_primes_ok B X).2.1
  obtain ⟨A, hA, rfl, rfl, hfr, hR⟩ := core (W := W) (u := u) hD hH hW.pk hW.lev.1 (hPr.T_prime u).ne_zero
    (fun PP hP => Formalism.L2.Col.T_notMem_vGs hPr u ⟨PP, (hW.lev.2.1 PP).1 hP⟩)
    (fun PP ⟨t, ht⟩ hP => TC.Q_notMem_of_ok hW.tr.ok _ PP ((hW.tq.Q t PP).1 ht) ((hW.lev.2.1 PP).1 hP))
    jj hjj a c₀ hx hbT hLT hline hn (fun n h x _ => horth n h x) hloc
    (fun k _ _ _ _ ι p β Q => GlobalTheory.AdForm.StdT I l Z u p β Q fun j => (a.x j).L)
    fun y m b v h1 h2 h3 h4 => GlobalTheory.T.all_true_family_geometry_column W hW u (mkGeo m b) c₀ v a.ζ₀ hpin h1 h2 hline hz hemb
      (fun x _ => let ⟨LZ, _, ho⟩ := horth _ rfl x; ⟨LZ, hLT ▸ ho⟩) (by rw [h3]; exact h4)
  exact ⟨A, hA, ⟨hpin, hR, hemb, hz⟩, hiA, hfr⟩

end GlobalTheory.GeoExists

end
