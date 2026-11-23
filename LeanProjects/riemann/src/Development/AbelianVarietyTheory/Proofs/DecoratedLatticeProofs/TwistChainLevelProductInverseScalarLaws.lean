import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LocK
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralIndicatorGivesLocalVacuumSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDatumLocalModelFormulaStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsDblClosed
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacuaStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemSupportAconvPair
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LambdaZeroEqProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HeisenbergCombinationDisjointPlacesCommuteVacua
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.QFinLaw

theorem combAt_aconv {D : D7} {S T : HSp D} (P : GlobalTheory.FinPl.Pl D → Prop) :
    ∀ l : List (WO S T →₀ ℂ), (∀ e ∈ l, GlobalTheory.FinPl.CombAt P e) → GlobalTheory.FinPl.CombAt P (aconv l) := by
  intro l
  induction l with
  | nil =>
    intro _ u hu i j
    have h0 : aconv ([] : List (WO S T →₀ ℂ)) = Finsupp.single 0 1 := rfl
    rw [h0, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton] at hu
    subst hu
    simpa using (GlobalTheory.FinPl.idAt D P).zero_mem
  | cons e l ih =>
    intro hl u hu
    have e1 : aconv (e :: l) = aconv [e, aconv l] := by
      apply AddMonoidAlgebra.ofCoeff_injective (R := ℂ) (M := WO S T)
      rw [GlobalTheory.QValOuter.aconv_cons, GlobalTheory.QValOuter.aconv_pair]
    rw [e1] at hu
    obtain ⟨a, ha, b, hb, rfl⟩ := GlobalTheory.QValOuter.mem_support_aconv_pair _ _ hu
    intro i j
    rw [Matrix.add_apply]
    exact Ideal.add_mem _ (hl e List.mem_cons_self a ha i j)
      (ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')) b hb i j)

theorem comb_aconv_cons {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : WO S T →₀ ℂ)
    (l : List (WO S T →₀ ℂ)) (h : ∀ x ∈ e.support, ∀ y ∈ (aconv l).support, symplO S T x y = 0) (f : WO S T → ℂ) :
    comb ψ S T (aconv (e :: l)) f = comb ψ S T e (comb ψ S T (aconv l) f) := by
  rw [GlobalTheory.HeisComb.comb_comb, GlobalTheory.HeisComb.comb_eq_sum]
  have hG0 : ∀ u, (0 : ℂ) • heisO ψ S T u f = 0 := fun u => zero_smul _ _
  have hGa : ∀ u (a b : ℂ), (a + b) • heisO ψ S T u f = a • heisO ψ S T u f + b • heisO ψ S T u f :=
    fun u a b => add_smul _ _ _
  show (e.sum fun g a => (aconv l).sum fun h b => Finsupp.single (g + h) (a * b)).sum
    (fun u a => a • heisO ψ S T u f) = _
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finsupp.sum_sum_index hG0 hGa, Finsupp.sum]
  refine Finset.sum_congr rfl fun y hy => ?_
  rw [Finsupp.sum_single_index (hG0 _), GlobalTheory.SplitScalar.heisO_add_of_orth ψ S T (h x hx y hy)]

theorem comb_aconv_map {D : D7} (ψ : AddChar (AF D.host.F) ℂ) {S T : HSp D} {r : ℕ} (p : Fin r → GlobalTheory.FinPl.Pl D)
    (hp : Function.Injective p) (E : Fin r → WO S T →₀ ℂ) (hE : ∀ a, GlobalTheory.FinPl.CombAt (· = p a) (E a))
    (f : WO S T → ℂ) :
    ∀ L : List (Fin r), L.Nodup → comb ψ S T (aconv (L.map E)) f = L.foldr (fun a g => comb ψ S T (E a) g) f := by
  intro L
  induction L with
  | nil => intro _; exact GlobalTheory.LevelComb.comb_single_zero ψ f
  | cons a L ih =>
    intro hL
    rw [List.map_cons, comb_aconv_cons, ih hL.of_cons, List.foldr_cons]
    intro x hx y hy
    refine GlobalTheory.DisjComb.symplO_disj (P := (· = p a)) (P' := fun v => ∃ b ∈ L, v = p b) ?_ (hE a x hx) ?_
    · rintro _ rfl ⟨b, hb, hab⟩
      exact (List.nodup_cons.1 hL).1 (hp hab ▸ hb)
    · exact combAt_aconv _ (L.map E) (fun e he => by
        obtain ⟨b, hb, rfl⟩ := List.mem_map.1 he
        exact fun u hu => GlobalTheory.DisjComb.mxAt_mono (fun v hv => ⟨b, hb, hv⟩) (hE b u hu)) y hy

theorem eQ_comb_at_place : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → v.Is → F.Pins w → ∀ j, j + 1 < D.R.m → ∀ Ψ, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ → ∀ i, ∃ f, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) f ∧ comb c.ψ _ _ (w.eQ j) Ψ = comb c.ψ _ _ ((F.Q i).eL j) f := by
  intro D c v t w F hc hv hP j hj Ψ hΨ i
  have hI := fun P P' hd => GlobalTheory.T.heisenbergCombination_disjoint_places_commute_vacua D c.ψ hc.std (c.V j) (c.V (j + 1)) P P' hd
  have hca : ∀ a, GlobalTheory.FinPl.CombAt (· = (F.Q a).q.v) ((F.Q a).eL j) := by
    intro a u hu r q'
    have := (F.Q a).hs
    exact (GlobalTheory.FinPl.FrameLat.idem_iff (F.Q a).q _).2 (((F.Q a).eL_at j ((F.Q a).s - j) (by omega)).1 u hu r q')
  have hdisj : ∀ a b : Fin F.r, a ≠ b → ∀ p, p = (F.Q a).q.v → ¬ p = (F.Q b).q.v := fun a b hab p ha hb =>
    hab (hP.inj (ha.symm.trans hb))
  let g : Fin F.r → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((F.Q a).eL j) f
  have hfold : comb c.ψ _ _ (w.eQ j) Ψ = (List.finRange F.r).foldr g Ψ := by
    rw [hP.eQ j hj, List.ofFn_eq_map]
    exact comb_aconv_map c.ψ (fun a => (F.Q a).q.v) hP.inj (fun a => (F.Q a).eL j) hca Ψ _ (List.nodup_finRange _)
  refine ⟨((List.finRange F.r).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) Ψ :=
      GlobalTheory.GSuppComb.vac_mono (fun p hp => by rw [hp]; exact (hP.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin F.r), (∀ a ∈ l, a ≠ i) →
        GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (F.Q i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a l ih =>
        intro hl
        exact ((hI (· = (F.Q a).q.v) (· = (F.Q i).q.v) (hdisj a i (hl a List.mem_cons_self))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange F.r).mem_erase_iff.1 ha).1
  · rw [hfold]
    exact GlobalTheory.GSuppComb.foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ
      (List.mem_finRange i)

theorem local_scalar_law : ∀ (D : D7) (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (q : GlobalTheory.FinPl.SplitPt D k), q.UnitAA → ∀ (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), IsStdChar D ψ (-1) → (ofSplit q).IsChar ψ ψk → HasConductor ψk 1 → ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (ω : Om S T), IsWeilDatumO ψ S T χS χT ω → ∀ (μS μT : kˣ →* ℂˣ), (ofSplit q).IsComp χS μS → (ofSplit q).IsComp χT μT → ∀ (Y Y' : Type) [Fintype Y] [DecidableEq Y] [Fintype Y'] [DecidableEq Y'] (FS : Frame k S.rank Y') (FT : Frame k T.rank Y) (LS : GlobalTheory.FinPl.Lat S) (LT : GlobalTheory.FinPl.Lat T), IsSelfDualC S LS → IsSelfDualC T LT → (∀ y : Y' → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FS.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV S LS (· = q.v)) → (∀ y : Y → k, (∀ i, y i ∈ 𝒪[k]) ↔ (fun i => q.sec ((FT.β *ᵥ y) i)) ∈ GlobalTheory.FinPl.latV T LT (· = q.v)) → ∀ (e : WO S T →₀ ℂ) (Φ : Matrix Y Y' k → ℂ), Φ ∈ SB (Matrix Y Y' k) → (ofSplit q).IsCombAt ψ FS FT e Φ → ∀ f, GlobalTheory.FinPl.Vac ψ S T LS LT (· = q.v) f → ∀ g gk h hk, (ofSplit q).IsLoc FS g gk → (ofSplit q).IsLoc FT h hk → ∀ z : ℂ, (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det gk) : ℂˣ) : ℂ) • om μS⁻¹ gk hk Φ = z • Φ → ω (g, h) (comb ψ S T e f) = z • comb ψ S T e f := by
  intro D k _ _ _ _ q hU ψ ψk hψ hch hcond S T χS χT ω hω μS μT cS cT Y Y' _ _ _ _ FS FT LS LT hLS hLT hFS hFT e Φ hΦ
    hcomb f hf g gk h hk hg hh z hz
  obtain ⟨Tm, hTm, hTO⟩ :=
    (GlobalTheory.T.integralIndicator_gives_localVacuum_splitPlace D k q hU Y Y' S T FS FT ψ ψk hψ hch hcond LS LT hLS hLT hFS hFT).2 f hf
  obtain ⟨O, hO, -⟩ := GlobalTheory.LocMod.PinModel.exists_isOne (k := k) (Y := Y) (Y' := Y')
  let Φs : SB (Matrix Y Y' k) := ⟨Φ, hΦ⟩
  have e1 : Tm Φs = comb ψ S T e f := by rw [hcomb.2 Tm hTm O Φs hO rfl, hTO O hO]
  have e2 := GlobalTheory.T.weilDatum_localModel_formula D k (ofSplit q) ψ S T χS χT ω hω μS μT cS cT Y Y' FS FT Tm hTm g gk h hk hg hh Φs (z • Φs)
    (by rw [Submodule.coe_smul]; exact hz.symm)
  rw [← e1, e2, map_smul]

theorem om_twist {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] (μ ζ : kˣ →* ℂˣ) (g : GL a k) (h : GL b k)
    (Φ : Matrix b a k → ℂ) :
    om (μ * ζ) g h Φ = ((ζ (Matrix.GeneralLinearGroup.det g) : ℂ) *
      (((ζ (Matrix.GeneralLinearGroup.det h))⁻¹ : ℂˣ) : ℂ)) • om μ g h Φ := by
  funext x
  simp only [om, Pi.smul_apply, smul_eq_mul, MonoidHom.mul_apply, Units.val_mul, mul_inv, Units.val_inv_eq_inv_val]
  ring

variable {D : D7}

theorem isComp_mul {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ χ' : (AE D)ˣ →* Circle} {μ μ' : kˣ →* ℂˣ} (h : p.IsComp χ μ) (h' : p.IsComp χ' μ') :
    p.IsComp (χ * χ') (μ * μ') := fun x a ha => by
  rw [MonoidHom.mul_apply, MonoidHom.mul_apply, Units.val_mul, Circle.coe_mul, h x a ha, h' x a ha]

theorem isComp_inv {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (p : Place D k) {χ : (AE D)ˣ →* Circle} {μ : kˣ →* ℂˣ} (h : p.IsComp χ μ) : p.IsComp χ⁻¹ μ⁻¹ := fun x a ha => by
  rw [MonoidHom.inv_apply, MonoidHom.inv_apply, Units.val_inv_eq_inv_val, Circle.coe_inv, h x a ha]

theorem place_law (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t)
    (hc : c.Is) (ht : t.Is) (hv : v.Is) (hP : F.Pins w) (j σ : ℕ) (h : j + 2 * (σ + 1) + 2 = D.R.m) (i : Fin F.r)
    (cc : ℕ) (hcc : j + 1 + cc = (F.Q i).s + 1) (x : GL ((F.Q i).X (j + 1) ⊕ Fin cc) (F.Q i).k)
    (hx : x ∈ ((F.Q i).T.lev (j + 1) cc hcc).J) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, (F.Q i).gl (j + 1) cc hcc x) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) ((F.Q i).gl (j + 1) cc hcc x, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) =
          a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  have hs := (F.Q i).hs
  obtain ⟨d, rfl⟩ : ∃ d, cc = d + 1 := ⟨cc - 1, by omega⟩
  have hjd : j + (d + 1) = (F.Q i).s := by omega
  have hjd' : j + 1 + d = (F.Q i).s := by omega
  obtain ⟨χz, hV, hW, hV', hW'⟩ := hP.mid j σ h
  obtain ⟨ζ, hζ⟩ := GlobalTheory.LocMod.Witness.exists_isComp (ofSplit (F.Q i).q) χz
  refine ⟨(((F.Q i).T.lev (j + 1) (d + 1) hcc).lam ⟨x, hx⟩ : ℂ) * (((ζ (Matrix.GeneralLinearGroup.det x))⁻¹ : ℂˣ) : ℂ),
    mul_ne_zero (Units.ne_zero _) (Units.ne_zero _), fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP j (by omega) Ψ₁ h₁ i
    rw [hfe]
    have hw := (t.sBF j (σ + 1) h).weil
    rw [(ht.sBF j (σ + 1) h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu j (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χV (((F.Q i).T.mu (j + 1))⁻¹ * ζ) := by
      rw [hV]; exact isComp_mul _ hmu hζ
    have cT : (ofSplit (F.Q i).q).IsComp (t.sBF j (σ + 1) h).χW ((F.Q i).T.mu (j + 1))⁻¹ := by
      rw [hW]; exact hmu
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY j (d + 1 + 1) (by omega)) 1 1 := by
      have := (F.Q i).gl_loc j (d + 1 + 1) (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om j) hw _ _ cS cT _ _
      ((F.Q i).FY j (d + 1 + 1) (by omega)) ((F.Q i).FY (j + 1) (d + 1) (by omega)) (v.N j) (v.N (j + 1))
      (hv.sd j (by omega)) (hv.sd (j + 1) (by omega)) ((F.Q i).latY j (d + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).eL j) ((F.Q i).T.Phi j (d + 1) hjd)
      ((F.Q i).reg.1 j (d + 1) hjd) ((F.Q i).eL_at j (d + 1) hjd) f hf 1 1 _ x h1 ((F.Q i).gl_loc _ _ _ x) _ ?_
    rw [map_one, map_one, Units.val_one, one_smul, mul_inv, inv_inv, om_twist, ((F.Q i).laws.1 j (d + 1) hjd).2 ⟨x, hx⟩,
      smul_smul]
    congr 1
    simp only [map_one, MonoidHom.inv_apply, inv_one, Units.val_one, one_mul, inv_inv, mul_inv, Units.val_inv_eq_inv_val]
    ring
  · obtain ⟨f, hf, hfe⟩ := eQ_comb_at_place D c v t w F hc hv hP (j + 1) (by omega) Ψ₂ h₂ i
    rw [hfe]
    have hw := (t.sFB j σ h).weil
    rw [(ht.sFB j σ h).1] at hw
    have hmu := isComp_inv _ ((F.Q i).mu (j + 1) (by omega)).1
    rw [inv_inv] at hmu
    have cS : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χV ((F.Q i).T.mu (j + 1 + 1))⁻¹ := by
      rw [hV']; exact hmu
    have cT : (ofSplit (F.Q i).q).IsComp (t.sFB j σ h).χW (((F.Q i).T.mu (j + 1 + 1))⁻¹ * ζ) := by
      rw [hW']; exact isComp_mul _ hmu hζ
    have h1 : (ofSplit (F.Q i).q).IsLoc ((F.Q i).FY (j + 1 + 1) d (by omega)) 1 1 := by
      have := (F.Q i).gl_loc (j + 1 + 1) d (by omega) 1
      rwa [map_one] at this
    refine local_scalar_law D (F.Q i).k (F.Q i).q (F.Q i).unit c.ψ (F.Q i).ψk hc.std (F.Q i).char (F.Q i).cond _ _ _ _ (t.om (j + 1)) hw _ _
      cS cT _ _ ((F.Q i).FY (j + 1) (d + 1) (by omega)) ((F.Q i).FY (j + 1 + 1) d (by omega)) (v.N (j + 1))
      (v.N (j + 1 + 1)) (hv.sd (j + 1) (by omega)) (hv.sd (j + 1 + 1) (by omega))
      ((F.Q i).latY (j + 1) (d + 1) (by omega)) ((F.Q i).latY (j + 1 + 1) d (by omega)) ((F.Q i).eL (j + 1))
      ((F.Q i).T.Phi (j + 1) d hjd') ((F.Q i).reg.1 (j + 1) d hjd') ((F.Q i).eL_at (j + 1) d hjd') f hf _ x 1 1
      ((F.Q i).gl_loc _ _ _ x) h1 _ ?_
    rw [inv_inv, ((F.Q i).laws.1 (j + 1) d hjd').1 ⟨x, hx⟩, smul_smul]
    congr 1
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv, inv_inv, Units.val_mul, Units.val_inv_eq_inv_val]
    field_simp

theorem inverse_laws : ∀ (D : D7) (c : Comm D) (v : VCom c) (t : Tup c) (w : VTup t) (F : QFam v t), c.Is → t.Is → v.Is → WeilOK (t := t) v → F.Pins w → ∀ j σ (h : j + 2 * (σ + 1) + 2 = D.R.m), ∀ k ∈ GlobalTheory.QuotientFiniteLevel.qK F j σ h, ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ → GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ → t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧ t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂ := by
  intro D c v t w F hc ht hv _ hP j σ h k hk
  refine Subgroup.iSup_induction (fun i => GlobalTheory.QuotientFiniteLevel.locK F j σ h i)
    (C := fun k => ∃ a : ℂ, a ≠ 0 ∧ ∀ Ψ₁ Ψ₂, GlobalTheory.FinPl.Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ w.Q) Ψ₁ →
      GlobalTheory.FinPl.Vac c.ψ _ _ (v.N (j + 1)) (v.N (j + 1 + 1)) (· ∈ w.Q) Ψ₂ →
      t.om j (1, k) (comb c.ψ _ _ (w.eQ j) Ψ₁) = a⁻¹ • comb c.ψ _ _ (w.eQ j) Ψ₁ ∧
        t.om (j + 1) (k, 1) (comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂) = a • comb c.ψ _ _ (w.eQ (j + 1)) Ψ₂)
    (show k ∈ ⨆ i, GlobalTheory.QuotientFiniteLevel.locK F j σ h i from hk) ?_ ?_ ?_
  · intro i k hk
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hk
    exact place_law D c v t w F hc ht hv hP j σ h i _ _ x hx
  · refine ⟨1, one_ne_zero, fun Ψ₁ Ψ₂ _ _ => ⟨?_, ?_⟩⟩
    · rw [show ((1 : GA D (c.V j)), (1 : GA D (c.V (j + 1)))) = 1 from rfl, map_one, inv_one, one_smul]; rfl
    · rw [show ((1 : GA D (c.V (j + 1))), (1 : GA D (c.V (j + 1 + 1)))) = 1 from rfl, map_one, one_smul]; rfl
  · rintro x y ⟨a, ha, hxa⟩ ⟨b, hb, hyb⟩
    refine ⟨a * b, mul_ne_zero ha hb, fun Ψ₁ Ψ₂ h₁ h₂ => ⟨?_, ?_⟩⟩
    · have e : ((1 : GA D (c.V j)), x * y) = (1, x) * (1, y) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).1, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).1, smul_smul, mul_inv,
        mul_comm b⁻¹]
    · have e : (x * y, (1 : GA D (c.V (j + 1 + 1)))) = (x, 1) * (y, 1) := by simp
      rw [e, map_mul, Module.End.mul_apply, (hyb Ψ₁ Ψ₂ h₁ h₂).2, map_smul, (hxa Ψ₁ Ψ₂ h₁ h₂).2, smul_smul, mul_comm b a]

end GlobalTheory.QFinLaw
end
