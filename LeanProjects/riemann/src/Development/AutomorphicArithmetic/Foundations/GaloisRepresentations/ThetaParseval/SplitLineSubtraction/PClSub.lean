import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.SubtractOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.PContLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLDirectSumPotSemistableStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AwayRepIsoLoc
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso tw)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open UpperTheory.Gal.TP.Sub

private theorem cont_sum {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [Field k]
    [TopologicalSpace k] [IsTopologicalRing k] {a b : ℕ} (r : Γ →* GL (Fin a) k) (s : Γ →* GL (Fin b) k)
    (hr : Continuous r) (hs : Continuous s) : Continuous (sumRep r s) := by
  have h : Continuous fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k) :=
    GlobalTheory.BCGal.cont_sumRep r s (Units.continuous_val.comp hr) (Units.continuous_val.comp hs)
  rw [Units.continuous_iff]
  refine ⟨h, ?_⟩
  have e : (fun g => (((sumRep r s g)⁻¹ : GL (Fin (a + b)) k) : Matrix (Fin (a + b)) (Fin (a + b)) k)) =
      (fun g => (sumRep r s g : Matrix (Fin (a + b)) (Fin (a + b)) k)) ∘ fun g => g⁻¹ := by
    funext g
    simp [map_inv]
  exact e ▸ h.comp continuous_inv

private theorem unrPol_add (S : Multiset ℂ) (c : ℂ) (m : ℤ) :
    unrPol (S + {c}) m = unrPol S m * unrPol {c} m := by
  simp only [unrPol, Multiset.map_add, Multiset.prod_add]

private theorem unrPol_single_ne (c : ℂ) (m : ℤ) : unrPol {c} m ≠ 0 := by
  simp only [unrPol, Multiset.map_singleton, Multiset.prod_singleton]
  exact X_sub_C_ne_zero _

theorem UpperTheory.Gal.TP.Sub.clSub_holds :
    FrobSub → SumDR → PstOfDR → WDFacts → ClSub := by
  intro hF hD hP hW E Ω _ _ _ _ _ l _ ι a s μ hs hμ w S c J m hc hsum
  refine ⟨fun hl => (hF E Ω l ι a w S c μ (hc.1 hl)).1 s (hsum.1 hl), ?_⟩
  intro P AI hT A h O _ _ _ Bw hj
  obtain ⟨-, d1, j1, p1⟩ := hc.2 P AI hT A h O Bw hj
  obtain ⟨c2, d2, j2, p2⟩ := hsum.2 P AI hT A h O Bw hj
  have ci : Continuous (Dec (F := E) A).subtype := continuous_subtype_val
  have cμ : Continuous (rk1 μ) := (contLeft_holds (G E Ω) (Qbar l) a 1).2.2.2 μ hμ
  have cS : Continuous ((sumRep s (rk1 μ)).comp (Dec (F := E) A).subtype) :=
    (cont_sum s (rk1 μ) hs cμ).comp ci
  have e : (sumRep s (rk1 μ)).comp (Dec (F := E) A).subtype =
      sumRep (s.comp (Dec (F := E) A).subtype) ((rk1 μ).comp (Dec (F := E) A).subtype) := by
    ext; rfl
  rw [e] at c2 d2 j2 p2 cS
  obtain ⟨dS, -, jS⟩ := hD l P AI hT E Ω A O Bw a 1 _ _ d2
  have pS : IsPstAt P Bw (s.comp (Dec (F := E) A).subtype) :=
    hP l P AI hT E Ω A O Bw a _ (hs.comp ci) dS
  have pM : IsPstAt P Bw ((rk1 μ).comp (Dec (F := E) A).subtype) :=
    hP l P AI hT E Ω A O Bw 1 _ (cμ.comp ci) d1
  have pT := hP l P AI hT E Ω A O Bw (a + 1) _ cS d2
  have hw := GlobalTheory.T.weilDeligneParamAboveL_directSum_potSemistable l P AI hT ι E Ω A w O Bw h hj a 1 _ _ pS pM pT
  have hu := (GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ pT).2 c2
  rw [hw] at hu p2
  refine ⟨(GlobalTheory.PstLaws.unr_wdAt_iff Bw h hj P ι _ pS).1 ((hW E Ω A w h _ _).1 hu), dS,
    fun τ LL' τ' hi => jS τ (J τ) {m τ} (j2 τ LL' τ' hi) (j1 τ LL' τ' hi), fun g => ?_⟩
  have q := p2 g
  rw [(hW E Ω A w h _ _).2.1 g, p1 g, unrPol_add] at q
  exact mul_right_cancel₀ (unrPol_single_ne c (deg g)) q
