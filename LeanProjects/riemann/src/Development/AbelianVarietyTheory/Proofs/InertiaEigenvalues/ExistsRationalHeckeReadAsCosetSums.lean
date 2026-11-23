import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BaseEmbeddingReadingEvalAdelicFunction
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.RationalHeckeScalars
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SplitOffDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransport
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.DIV Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.HeckeReadRational

section SlopeTestRemainingChoices

open Formalism.IndefR.Arith Formalism.IndefR.Mult Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem hkC_eq_heckeScalar {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks)
    (i : Fin D.R.m) (P : Formalism.L2.DIV.Pl D.host.E) (k : ℕ) : hkC R i P k = heckeScalar R i P k := by
  rw [hkC, heckeScalar, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast]

theorem heckeOn_mem_wall_of_hkData {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks}
    {i : Fin D.R.m} (hβ' : IsSDFrame (Wc D i) (R.βW i) (R.ΛW i) 1) (hSb : R.fam_Sb) (hHW : R.models_HW)
    (σ : D.what₂.LL →+* ℂ) {P : Formalism.L2.DIV.Pl D.host.E} {k : ℕ} {α : GA D (Wc D i)} {Rc : Finset (GA D (Wc D i))}
    (hd : IsHkData R i P k α Rc) (z : (R.HW i σ).H) :
    heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) ∈ R.Wall i σ := by
  obtain ⟨hso, -, -, ⟨e, ϖ, he, -, -, hα⟩, hR⟩ := hd
  obtain ⟨c, hβ⟩ := hβ'
  have hN : ((1 ^ c : ℕ) : 𝓞 D.host.E) ∉ P.asIdeal := by
    rw [one_pow, Nat.cast_one]
    exact (Ideal.ne_top_iff_one _).1 P.isPrime.ne_top
  have hoff : ∀ PP, PP ∈ (R.datWp i R.triv).Pg ∨ PP ∈ (R.datWp i R.triv).Q → PP ≠ P ∧ ¬ Lev.IsConjPl PP P := by
    intro PP hPP
    have hPP' : PP ∈ R.Pg := hPP.elim id fun h => absurd h (Finset.notMem_empty _)
    have hS : PP ∈ (R.Sb : Set (Formalism.L2.DIV.Pl D.host.E)) := hSb hPP'
    refine ⟨fun h => hso.2.1 (h ▸ hS), fun h => hso.2.2 PP hS ?_⟩
    rw [Formalism.L2.Col.conjIdeal_asIdeal]
    refine PP.isMaximal.eq_of_le (Formalism.L2.Col.conjPrime₂ P).isPrime.ne_top fun a ha => ?_
    obtain ⟨a', ha', e⟩ := h a ha
    rw [Formalism.L2.Col.mem_conjP]
    have : Formalism.L2.Col.cO D.host.E a = a' := RingOfIntegers.ext e.symm
    rwa [this]
  have hp : IsPrimeIdem P e (e + cA D e) := Or.inl ⟨he, rfl⟩
  have hq := (GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).2.2.1 P e _ hp
  obtain ⟨large₂, hLg⟩ := ((GlobalTheory.T.supported_subgroup_split_commute_primeIdempotents (Wc D i)).1 _ hq.1 hq.2.1).1
  have hK : ∀ g, g ∈ levG (Wc D i) (R.βW i) (R.datWp i R.triv) ⊓ large₂ ↔ g ∈ locPart (Wc D i) (KsphC (Wc D i) ∅) e := by
    intro g
    have h1 := ((GlobalTheory.T.level_hyperspecial_trivialCharacter_splits_off_places (Wc D i) (R.βW i) _ _ (R.datWp i R.triv) hβ).2 P e _ hp hN hoff).1 g
    exact ⟨fun h => ⟨(h1 ((hLg g).1 h.2)).1 h.1, (hLg g).1 h.2⟩, fun h => ⟨(h1 h.2).2 h.1, (hLg g).2 h.2⟩⟩
  have hoL := GlobalTheory.HeckeModel.offAt_of_place hβ he hN hoff hLg hK
  have hαL : α ∈ large₂ := (hLg α).2 hα.2.1
  obtain ⟨A₀, hA₀⟩ := GlobalTheory.HeckeSup.exists_local_isDC hoL.splits hαL hR
  have key : heckeOn (R.MW i σ) Rc ((R.HW i σ).e z) = heckeOn (R.MW i σ) A₀ ((R.HW i σ).e z) := by
    ext v : 1
    show heckeLin (Wc D i) Rc ((R.HW i σ).e z v) = heckeLin (Wc D i) A₀ ((R.HW i σ).e z v)
    exact funext fun h => GlobalTheory.HeckeModel.sum_eq_of_isDC hR (hoL.splits.isDC hαL hA₀) ⟨1, 1, by simp⟩
      (GlobalTheory.HeckeSup.model_inv_cl hHW i σ z v) h
  rw [key]
  exact GlobalTheory.HeckeModel.heckeOn_mem_mult hoL (fun g hg => hq.2.2.1 g ((hLg g).1 hg)) hαL hA₀
    (show (R.HW i σ).e z ∈ R.Wall i σ from (hHW i σ).2.1 ▸ LinearMap.mem_range_self _ z)

end SlopeTestRemainingChoices

section Main

open Formalism.IndefR.Mult

set_option maxHeartbeats 1600000 in

theorem rationalHecke_of_readsCusp : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Formalism.L2.Pj.CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : Formalism.IndefR.FWT.FWTie T R κ v₀) (i : Fin D.R.m), GlobalTheory.IndefiniteRowSideFullHecke.SplitOffDetection.HeckeTransform → R.toLevCh.Is A.μ0 → R.IsFam → R.IsModels → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, Formalism.IndefR.FWT.JEvAt T R κ v₀ i (sg0 D A) hV) → Function.Injective ((R.FW i).j (sg0 D A)) → (∀ hV : T.V ((i : ℕ) + 1) (Formalism.IndefR.FWT.res T (sg0 D A)) = Wc D i, GlobalTheory.HeckeSup.ReadsCusp T R κ i (Formalism.IndefR.FWT.res T (sg0 D A)) hV) → GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.RationalHecke R i := by
  intro D G _ _ Pl0 T0 A T _ R κ v₀ fw i hT hlev hfam hmod hex _ hR P hP k hk
  have hHW : R.models_HW := hmod.HW
  have hV : T.V ((i : ℕ) + 1) (res T (sg0 D A)) = Wc D i :=
    fw.laws.spaceW _ (inR i) _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  obtain ⟨p, m, hp, hpP, -⟩ := GlobalTheory.HeckeSup.exists_prime_under P
  have hoff := GlobalTheory.HeckeSup.not_dvd_level fw.laws hpP hP.2
  have hsp := GlobalTheory.HeckeSup.split_of_ne (H := T.Q.H) hP.1.1
  have hn : (κ i).n = D.R.nV := (fw.kap i (D.eTau.symm 1)).2.2
  have htr : ∀ f : Cu T κ i, ∃ g ∈ T.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n,
      GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.GeoHecke T ((i : ℕ) + 1) P.asIdeal p k
        (hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV) f g := by
    intro f
    obtain ⟨g, hg, hfg⟩ := GlobalTheory.HeckeSup.exists_transform hT GlobalTheory.ThetaTransport.heckePointLaws fw.laws i
      ⟨P.isMaximal, hsp, hp, hpP, hoff⟩ hk ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) (dom_wtA (κ i)) f f.2
    rw [show hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k (κ i).n =
      hkScal T.Q.c ((Nat.card (kP P) : T.Q.c.F)⁻¹ ^ (k * D.R.nV / 2)) P.asIdeal k D.R.nV by rw [hn]] at hfg
    exact ⟨g, hg, hfg⟩
  choose g hg hfg using htr
  have hEI := GlobalTheory.EvalAtUnitVector.evInj T R v₀ hHW fw.hv₀ i _ (base_embedding_good T R fw.alg_eq fw.laws.pins.2.2.1)
  have hread : ∀ f : Cu T κ i, ∀ Rc, GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.IsCosetSys R i P k Rc →
      (R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK)) =
        GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc
          ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
    rintro f Rc ⟨α, hα, hRc⟩
    have hd : GlobalTheory.IndefiniteRowSideFullHecke.LatticesOverBalls.IsHkData R i P k α Rc := ⟨hP.1, hP.2, hk, hα, hRc⟩
    have h1 := hR hV P p k α Rc hd ⟨hP.1, hp, hpP, hoff, hk, hα, hRc⟩ f f.2 (g f) (hg f) (hfg f)
    rw [hkC_eq_heckeScalar] at h1
    obtain ⟨z', hz'⟩ : ∃ z', (R.HW i (sg0 D A)).e z' = heckeOn (R.MW i (sg0 D A)) Rc
        ((R.HW i (sg0 D A)).e ((R.FW i).j (sg0 D A) (fw.e i f : (R.FW i).WK))) := by
      rw [← LinearMap.mem_range, (hHW i _).2.1]
      exact heckeOn_mem_wall_of_hkData (hlev.βW i) hfam.Sb hHW _ hd _
    have e1 : (R.FW i).j (sg0 D A) (fw.e i ⟨g f, hg f⟩ : (R.FW i).WK) = GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • z' := by
      apply hEI
      refine (GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) ⟨g f, hg f⟩).trans ?_
      funext h
      rw [h1 h, ← GlobalTheory.HeckeSup.baseEmbedding_reading_eval_adelicFunction fw hV (hex hV) f]
      unfold evAt
      rw [map_smul, hz']
      simp [heckeOn, postOn, heckeLin]
      exact Or.inl rfl
    rw [e1, map_smul, hz']
  obtain ⟨n, b, hbK, -, hKspan, hLind, hLspan⟩ := fw.ks i
  let B : Module.Basis (Fin n) D.what₂.LL (Fin (R.nW i) → D.what₂.LL) := Module.Basis.mk hLind hLspan.ge
  have hB : ∀ l, B l = b l := fun l => Module.Basis.mk_apply hLind hLspan.ge l
  let f0 : Fin n → Cu T κ i := fun l => (fw.e i).symm ⟨b l, hbK l⟩
  let yv : Fin n → Fin (R.nW i) → D.what₂.LL := fun l => (fw.e i ⟨g (f0 l), hg (f0 l)⟩ : (R.FW i).WK)
  let hL := B.constr D.what₂.LL yv
  have hLb : ∀ l, hL (b l) = yv l := fun l => by rw [← hB l]; exact B.constr_basis _ _ _
  have hb0 : ∀ l, (fw.e i (f0 l) : Fin (R.nW i) → D.what₂.LL) = b l := fun l => by simp [f0]
  refine ⟨hL, fun Rc hRc => ?_, fun x hx => ?_⟩
  · have hext := B.ext (f₁ := ((R.HW i (sg0 D A)).e.comp ((R.FW i).j (sg0 D A))).comp hL)
      (f₂ := ((GlobalTheory.IndefiniteRowSideFullHecke.RationalHeckeScalars.heckeScalar R i P k • heckeOn (R.MW i (sg0 D A)) Rc).comp (R.HW i (sg0 D A)).e).comp
        ((R.FW i).j (sg0 D A))) fun l => by
      rw [hB l]
      simp only [LinearMap.comp_apply, LinearMap.smul_apply]
      rw [hLb l, ← hb0 l]
      exact hread (f0 l) Rc hRc
    intro x
    have := LinearMap.congr_fun hext x
    simpa only [LinearMap.comp_apply, LinearMap.smul_apply] using this
  · rw [← hKspan] at hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨l, rfl⟩ := hx
      rw [hLb]
      exact (fw.e i _).2
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | smul a x _ hx =>
      rw [← algebraMap_smul D.what₂.LL a x, map_smul, algebraMap_smul]
      exact Submodule.smul_mem _ a hx

end Main

end GlobalTheory.HeckeReadRational
