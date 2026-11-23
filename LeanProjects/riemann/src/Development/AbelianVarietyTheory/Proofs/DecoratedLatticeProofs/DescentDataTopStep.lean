import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaAtSeesawProductDatumEqVacuumCombinationsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixSupportedSplitPlaceOfIsHalfConjSum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLatticeVacuumOfCarriesLatticeCompletions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DescentTopStepVectorStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeesawCombinationsCompositeNeZeroOfVacuumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam

noncomputable section

namespace GlobalTheory.DatumTopAt

section Gen

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D}

theorem combAt_mono' {P Q : GlobalTheory.FinPl.Pl D → Prop} (h : ∀ x, P x → Q x) {c : WO S T →₀ ℂ}
    (hc : GlobalTheory.FinPl.CombAt P c) : GlobalTheory.FinPl.CombAt Q c := fun x hx => GlobalTheory.DisjComb.mxAt_mono h (hc x hx)

theorem vac_mono' {LS : GlobalTheory.FinPl.Lat S} {LT : GlobalTheory.FinPl.Lat T} (P : GlobalTheory.FinPl.Pl D → Prop) {f : WO S T → ℂ}
    (h : GlobalTheory.FinPl.Vac ψ S T LS LT (fun _ => True) f) : GlobalTheory.FinPl.Vac ψ S T LS LT P f := by
  have hle : latO S T (LS : Set _) (LT : Set _) P ≤ latO S T (LS : Set _) (LT : Set _) fun _ => True :=
    AddSubgroup.closure_mono fun w ⟨α, hα, _, hw⟩ => ⟨α, hα, fun _ h => absurd trivial h, hw⟩
  exact ⟨h.1, fun u hu => h.2.1 u (hle hu), fun e he u hu hh => h.2.2 e he u (hle hu) hh⟩

theorem locPl_combAt {M : GlobalTheory.FinPl.Lat S} {M' : GlobalTheory.FinPl.Lat T} (Lp : LocPl ψ S T M M') :
    GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.o ∧ GlobalTheory.FinPl.CombAt (· = Lp.q.v) Lp.e :=
  ⟨fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.o_at u hu),
    fun u hu => GlobalTheory.FinPl.SplitHalfSuppImp.mxAt_of_isHalf D Lp.k Lp.q u (Lp.e_is.1 u hu)⟩

theorem comm_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (pv : Fin n → GlobalTheory.FinPl.Pl D) (hv : Function.Injective pv)
    (a b : Fin n → (WO S T →₀ ℂ)) (ha : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (a i))
    (hb : ∀ i, GlobalTheory.FinPl.CombAt (· = pv i) (b i)) :
    ∀ l : List (Fin n), l.Nodup → ∀ g, l.foldr (fun i g' => comb ψ S T (b i) (comb ψ S T (a i) g')) g =
      l.foldr (fun i g' => comb ψ S T (b i) g') (l.foldr (fun i g' => comb ψ S T (a i) g') g) := by
  have pass : ∀ x (t : List (Fin n)), x ∉ t → ∀ Y, comb ψ S T (a x) (t.foldr (fun i g' => comb ψ S T (b i) g') Y) =
      t.foldr (fun i g' => comb ψ S T (b i) g') (comb ψ S T (a x) Y) := by
    intro x t
    induction t with
    | nil => intro _ Y; rfl
    | cons y t ih =>
      intro hx Y
      have hxy : x ≠ y := fun e => hx (e ▸ List.mem_cons_self)
      have hxt : x ∉ t := fun m => hx (List.mem_cons_of_mem _ m)
      have hd : ∀ p, (· = pv x) p → ¬ (· = pv y) p := fun p h1 h2 => hxy (hv (h1.symm.trans h2))
      simp only [List.foldr_cons]
      rw [(GlobalTheory.DisjComb.main D ψ hψ S T _ _ hd).1 (a x) (b y) (ha x) (hb y), ih hxt]
  intro l
  induction l with
  | nil => intro _ g; rfl
  | cons x t ih =>
    intro hnd g
    rw [List.nodup_cons] at hnd
    simp only [List.foldr_cons]
    rw [ih hnd.2, pass x t hnd.1]

theorem comp_list (hψ : IsStdChar D ψ (-1)) {n : ℕ} (Q : GlobalTheory.FinPl.Pl D → Prop) (a : Fin n → (WO S T →₀ ℂ))
    (ha : ∀ i, GlobalTheory.FinPl.CombAt Q (a i)) : ∀ l : List (Fin n), ∃ o, GlobalTheory.FinPl.CombAt Q o ∧
      ∀ g, comb ψ S T o g = l.foldr (fun i g' => comb ψ S T (a i) g') g := by
  intro l
  induction l with
  | nil =>
    refine ⟨Finsupp.single 0 1, fun u hu => ?_, fun g => ?_⟩
    · rw [Finsupp.mem_support_iff, Finsupp.single_apply] at hu
      split_ifs at hu with h0
      · subst h0; exact fun i j => Submodule.zero_mem _
      · exact absurd rfl hu
    · simp only [comb, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
        Finsupp.single_eq_same, one_smul, List.foldr_nil]
      exact GlobalTheory.MixPer.heisO_zero ψ S T g
  | cons x t ih =>
    obtain ⟨o, ho, hc⟩ := ih
    obtain ⟨e, he, hce⟩ := (GlobalTheory.DisjComb.main D ψ hψ S T Q (fun _ => False) (fun _ _ h => h)).2.2.2.1 (a x) o
      (combAt_mono' (fun p hp => Or.inl hp) (ha x)) (combAt_mono' (fun p hp => Or.inl hp) ho)
    refine ⟨e, combAt_mono' (fun p hp => hp.elim id False.elim) he, fun g => ?_⟩
    rw [hce, hc]
    rfl

theorem latV_eq_of_moves {V : HSp D} {g : GA D V} {Λ M N : GlobalTheory.FinPl.Lat V} {P : GlobalTheory.FinPl.Pl D → Prop}
    (hM : Submodule.IsLattice D.host.E M) (hN : Submodule.IsLattice D.host.E N)
    (h1 : GlobalTheory.FinPl.Moves V g Λ M P) (h2 : GlobalTheory.FinPl.Moves V g Λ N P) :
    GlobalTheory.FinPl.latV V M P = GlobalTheory.FinPl.latV V N P := by
  have key : ∀ (A B : GlobalTheory.FinPl.Lat V), Submodule.IsLattice D.host.E A → GlobalTheory.FinPl.Moves V g Λ A P →
      GlobalTheory.FinPl.Moves V g Λ B P → ∀ y, y ∈ GlobalTheory.FinPl.latV V A P → y ∈ GlobalTheory.FinPl.latV V B P := by
    intro A B hA hgA hgB y hy
    have hent : ∀ i, y i ∈ GlobalTheory.FinPl.idAt D P := ((((GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P).2 V).2.2.2 A y hA).1 hy).1
    have hz := GlobalTheory.VacMove.mem_ideal_mulVec _ (Formalism.L2.Theta.mt V g⁻¹) y hent
    have e : Formalism.L2.Theta.mt V g *ᵥ (Formalism.L2.Theta.mt V g⁻¹ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, GlobalTheory.VacMove.mt_mul_inv', Matrix.one_mulVec]
    have h3 := (hgA _ hz).2 (e.symm ▸ hy)
    have h4 := (hgB _ hz).1 h3
    rwa [e] at h4
  ext y
  exact ⟨key M N hM h1 h2 y, key N M hN h2 h1 y⟩

end Gen

end GlobalTheory.DatumTopAt

namespace GlobalTheory.DatumTopAt

theorem datum_top : ∀ (D : D7) (L : SizeData₂ D) (hT : GatTies D) (Gi : Formalism.MainNotions.G.Inst D L) (Gl : Formalism.MainNotions.G.LatInst D) (Kc : Formalism.MainNotions.G.Consts) (Yd : DivX D) (cX : ExtraC) (ex : Extra D L hT Gi Gl Kc Yd cX) (W : RealPack ex) (u : D.what₂.Word) (f : FamCh W u), PkHyp W → f.RowOK → ∀ v : VCom f.c, v.Is → VTie f v → ∀ (n : ℕ) (G : Fin n → GLoc v) (pl : Fin n ≃ (pk W).Pg), GPin G → GRead f G pl → ∀ j (h : j + 2 * 0 + 2 = D.R.m), ∀ d₀, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d₀ → ∃ (M : GlobalTheory.FinPl.Lat (Yc D (j + 1))) (M' : GlobalTheory.FinPl.Lat D.sp.X') (o' : WO (Yc D (j + 1)) D.sp.X' →₀ ℂ), IsSelfDualC (Yc D (j + 1)) M ∧ IsSelfDualC D.sp.X' M' ∧ GlobalTheory.FinPl.CombAt (· ∈ v.gP) o' ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ M M' (· ∈ v.gP) (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ∧ GlobalTheory.FinPl.Vac f.c.ψ _ _ (v.N (j + 1)) v.NT (· ∈ v.gP) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) ∧ ((omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0 → comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h)) ≠ 0) ∧ ∃ κ : ℂ, κ ≠ 0 ∧ ∀ d, IsDG W (j + 1) (pk W).MX (pk W).ΛX (pk W).βX (vacT (pk W) j h) d → omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (comb f.c.ψ _ _ d (vacT (pk W) j h)) = κ • comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' (omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h))) := by
  intro D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR j h d₀ hd₀
  have hψ : IsStdChar D (pk W).ψ (-1) := hd₀.2.1.1
  obtain ⟨hΛ, hΛX, M, hM, hMv, hg0⟩ := GlobalTheory.T.descent_top_self_dual D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT j h d₀ hd₀
  obtain ⟨Lp, κ, hκ, hq, hint, heGT, hdat⟩ := GlobalTheory.T.descent_top_step_vector D L hT Gi Gl Kc Yd cX ex W u f hPk hRow v hv hVT n G pl hGP hGR
    j h d₀ hd₀ hΛ hΛX M hM hMv
  have hNT : v.NT = f.g.LT := hVT.bT.2
  have hLT : IsSelfDualC D.sp.X' f.g.LT := hNT ▸ hv.sdT
  have hinj : Function.Injective fun i => (Lp i).q.v := fun i i' e => hGP.inj ((hq i).symm.trans (e.trans (hq i')))
  generalize hg : omT (pk W) W.P.A3.A.μ0 j h (f.g.b (j + 1), f.g.bT) (vacT (pk W) j h) = g₀ at hg0 hdat ⊢
  have hcomb : ∀ i, GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).o ∧ GlobalTheory.FinPl.CombAt (· = (Lp i).q.v) (Lp i).e :=
    fun i => locPl_combAt (Lp i)
  have hplace : ∀ i, (Lp i).q.v ∈ v.gP := fun i => (hGP.places _).2 ⟨i, hq i⟩
  have hoP : ∀ i, GlobalTheory.FinPl.CombAt (· ∈ v.gP) (Lp i).o := fun i =>
    combAt_mono' (fun p (hp : p = (Lp i).q.v) => hp ▸ hplace i) (hcomb i).1
  obtain ⟨o', ho', ho'eq⟩ := comp_list (ψ := f.c.ψ) (S := Yc D (j + 1)) (T := D.sp.X') hψ (· ∈ v.gP) (fun i => (Lp i).o) hoP
    (List.finRange n)
  obtain ⟨F₀, hF₀, hF₀t, -⟩ := hdat d₀ hd₀
  have hoff : ∀ p, (∀ i, p ≠ (Lp i).q.v) → GlobalTheory.FinPl.latV (Yc D (j + 1)) (v.N (j + 1)) (· = p) =
      GlobalTheory.FinPl.latV (Yc D (j + 1)) M (· = p) ∧ GlobalTheory.FinPl.latV D.sp.X' v.NT (· = p) = GlobalTheory.FinPl.latV D.sp.X' f.g.LT (· = p) := by
    intro p hp
    have hpg : p ∉ v.gP := fun hm => by
      obtain ⟨i, hi⟩ := (hGP.places p).1 hm
      exact hp i (hi.trans (hq i).symm)
    exact ⟨latV_eq_of_moves (hv.sd (j + 1) (by omega)).1 hM.1
      (hVT.moves (j + 1) (by omega) (· = p) fun p' (hp' : p' = p) => hp' ▸ hpg) (hMv _), by rw [hNT]⟩
  have hNvac := (GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ F₀ hg0 hF₀ hF₀t).2 (v.N (j + 1)) v.NT
    (hv.sd (j + 1) (by omega)) hv.sdT hint hoff
  have hre := comm_list hψ (fun i => (Lp i).q.v) hinj (fun i => (Lp i).o) (fun i => (Lp i).e) (fun i => (hcomb i).1)
    (fun i => (hcomb i).2) (List.finRange n) (List.nodup_finRange n)
  have hth : IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' (comb f.c.ψ _ _ o' g₀) := by
    rw [ho'eq]; exact hNvac.1
  have hkey : ∀ F, IsThetaAt f.c.ψ (symplO (Yc D (j + 1)) D.sp.X') (heisO f.c.ψ (Yc D (j + 1)) D.sp.X') (∑ i, (Lp i).q.e)
      (latO (Yc D (j + 1)) D.sp.X' (M : Set _) (f.g.LT : Set _) fun _ => True) 1 g₀ (prodDat Lp) F →
      IsThetaFunO f.c.ψ (Yc D (j + 1)) D.sp.X' F → F = comb f.c.ψ _ _ (v.eGT j h) (comb f.c.ψ _ _ o' g₀) := by
    intro F hF hFt
    rw [(GlobalTheory.T.thetaAt_seesawProductDatum_eq_vacuumCombinations D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ F hg0 hF hFt).1, hre, heGT _ hth, ho'eq]
  refine ⟨M, f.g.LT, o', hM, hLT, ho', vac_mono' _ hg0, ?_, ?_, κ, hκ, ?_⟩
  · rw [ho'eq]; exact vac_mono' _ hNvac
  · intro hne
    rw [ho'eq]
    exact GlobalTheory.T.seesawCombinations_composite_ne_zero_of_vacuum D f.c.ψ hψ _ _ M f.g.LT hM hLT n Lp hinj g₀ hg0 hne
  · intro d hd
    obtain ⟨F, hF, hFt, heq⟩ := hdat d hd
    rw [heq, hkey F hF hFt]

end GlobalTheory.DatumTopAt
