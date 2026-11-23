import Formalism.LocalToGlobal.Columns.RecChainCUnfPol

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section XpL

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  (Λm : LevFam X.E X.K (R.N R.m) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

@[reducible] def topGSD (u : Pr.Word) : GSD X.K := formGSD (colVal W u R.m (Pr.vT u) Pr.vGs) Λm

def topEv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) : (topGSD W Λm u).Ev σ₀ :=
  roundEv σ₀ hσ (W.lamTrue u R.m) (fun d => d.1.Lsh) Λm

variable {W ΛM}

variable (ΛM) in

def LevExtL : Prop := ∀ h : ↥(ΛM.inv).grp, (extR R hSG ((1 : UF X.E (R.N R.m - 1)), h.1)).2 ∈ Λm.grp

variable {Λm}

def extFL (hL : LevExtL Λm hSG ΛM) (u : Pr.Word) : (ptGSD W ΛM).G →* (topGSD W Λm u).G where
  toFun a := ((extR R hSG (a.1, a.2.1)).1, ⟨(extR R hSG (a.1, a.2.1)).2, hL a.2⟩)
  map_one' := by
    apply Prod.ext
    · exact map_one (extUH (N_m_succ R))
    · apply Subtype.ext
      exact congrArg Prod.snd (map_one (extR R hSG))
  map_mul' a b := by
    apply Prod.ext
    · exact map_mul (extUH (N_m_succ R)) a.1 b.1
    · apply Subtype.ext
      exact congrArg Prod.snd (map_mul (extR R hSG) (a.1, a.2.1) (b.1, b.2.1))

theorem tilR_smulFL (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (a : (ptGSD W ΛM).G) (d : DecoSet X.E (R.N R.m - 1) ∅ SG') :
    tilR hSG u (a • d) = extFL hSG hL u a • tilR hSG u d := by
  show tilR hSG u (FormG.incl _ a • d) = FormG.incl _ (extFL hSG hL u a) • tilR hSG u d
  exact tilR_smul hSG hPr u hpi (a.1, a.2.1) d

variable (W Λm ΛM) in

def tilClL (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : (topGSD W Λm u).Cl :=
  (topGSD W Λm u).cls (tilR hSG u ((ptGSD W ΛM).outSec.rep c))

def stabMapRL (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →* MulAction.stabilizer (topGSD W Λm u).G ((topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c)) :=
  ((MulAut.conj ((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹).toMonoidHom.comp
    ((extFL hSG hL u).comp (Subgroup.subtype _))).codRestrict _ (fun s => by
      rw [MulAction.mem_stabilizer_iff]
      show (((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹ * extFL hSG hL u s.1 *
        ((topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))⁻¹⁻¹) •
          (topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c) = _
      rw [inv_inv, mul_smul, mul_smul]
      have h1 : (topGSD W Λm u).outSec.mv (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) •
          (topGSD W Λm u).outSec.rep (tilClL W Λm hSG ΛM u c) = tilR hSG u ((ptGSD W ΛM).outSec.rep c) :=
        (topGSD W Λm u).outSec.mv_smul _
      rw [h1, ← tilR_smulFL hSG hPr u hpi hL, s.2, inv_smul_eq_iff, h1])

theorem stabMapRL_injective (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtL Λm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) : Function.Injective (stabMapRL hSG hPr u hpi hL c) := by
  intro s s' h
  have h1 := congrArg Subtype.val h
  have h2 : extFL hSG hL u s.1 = extFL hSG hL u s'.1 := (MulAut.conj _).injective h1
  have h3 : s.1.1 = s'.1.1 := rec_extUH_injective (N_m_succ R) (congrArg Prod.fst h2)
  exact Subtype.ext (formGSD_stab_inj _ _ _ s.2 s'.2 h3)

variable (W Λm ΛM) in

def lowCL (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  (topEv W Λm σ₀ hσ u).extend ((ptEv W ΛM σ₀ hσ).ev.comp (brC W u))

theorem lowCL_ev (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (x : VV X.K (W.lamTrue u R.m)) :
    lowCL W Λm ΛM σ₀ hσ u ((topEv W Λm σ₀ hσ u).ev x) = (ptEv W ΛM σ₀ hσ).ev (brC W u x) :=
  (topEv W Λm σ₀ hσ u).extend_ev _ x

end XpL

section XpC

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (bm : Λ.β R.m)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG')
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem stepF_mem_top (u : Pr.Word) : (stepF W Λ u R.m).mem bm = topGSD W (Λ.lev R.m bm) u := rfl

def LevExtC : Prop := LevExtL (Λ.lev R.m bm) hSG ΛM

variable {W Λ bm ΛM}

def extFC (hL : LevExtC Λ bm hSG ΛM) (u : Pr.Word) : (ptGSD W ΛM).G →* (stepF W Λ u R.m).G bm :=
  extFL (W := W) hSG hL u

theorem tilR_smulFC (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (a : (ptGSD W ΛM).G) (d : DecoSet X.E (R.N R.m - 1) ∅ SG') :
    tilR hSG u (a • d) = (extFC hSG hL u a : (topGSD W (Λ.lev R.m bm) u).G) • tilR hSG u d :=
  tilR_smulFL hSG hPr u hpi hL a d

variable (W Λ bm ΛM) in

def tilClC (u : Pr.Word) (c : (ptGSD W ΛM).Cl) : StClC W Λ u R.m := ⟨bm, tilClL W (Λ.lev R.m bm) hSG ΛM u c⟩

def stabMapRC (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) :
    MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c) →* FamStab (stepF W Λ u R.m) (tilClC W Λ bm hSG ΛM u c) :=
  stabMapRL hSG hPr u hpi hL c

theorem stabMapRC_injective (hPr : Pr.Ok) (u : Pr.Word) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal) (hL : LevExtC Λ bm hSG ΛM)
    (c : (ptGSD W ΛM).Cl) : Function.Injective (stabMapRC (W := W) hSG hPr u hpi hL c) :=
  stabMapRL_injective hSG hPr u hpi hL c

variable (W Λ bm ΛM) in

def lowCC (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    (FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] (FrS X σ₀ (R.N R.m - 1) → ℂ) :=
  lowCL W (Λ.lev R.m bm) ΛM σ₀ hσ u

theorem lowCC_ev (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (x : VV X.K (W.lamTrue u R.m)) :
    lowCC W Λ bm ΛM σ₀ hσ u (evV X.emb 1 (W.lamTrue u R.m) σ₀ x) = (ptEv W ΛM σ₀ hσ).ev (brC W u x) :=
  lowCL_ev σ₀ hσ u x

variable (W Λ bm) in

def resTop (σ₀ : X.K →+* ℂ) (u : Pr.Word) :
    (StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ) →ₗ[ℂ] ((topGSD W (Λ.lev R.m bm) u).Cl → FrS X σ₀ (R.N R.m) → ℂ) :=
  LinearMap.funLeft ℂ (FrS X σ₀ (R.N R.m) → ℂ) fun c₀ : (topGSD W (Λ.lev R.m bm) u).Cl => (⟨bm, c₀⟩ : StClC W Λ u R.m)

theorem resTop_apply (σ₀ : X.K →+* ℂ) (u : Pr.Word) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c₀ : (topGSD W (Λ.lev R.m bm) u).Cl) : resTop W Λ bm σ₀ u F c₀ = F ⟨bm, c₀⟩ := rfl

variable (bm) in

def recPerC (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) : PeriodMap R (recChainC hX σ₀ G u A) where
  Mt := Fin ((rowGSD W ΛM).hDim hM) → ℂ
  Wz := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m) → ℂ
  evz := ((topEv W (Λ.lev R.m bm) σ₀ hσ u).evAt fun c => tilR hSG u ((ptGSD W ΛM).outSec.rep c)) ∘ₗ resTop W Λ bm σ₀ u
  Wrow := (ptGSD W ΛM).Cl → FrS X σ₀ (R.N R.m - 1) → ℂ
  lowerMap := LinearMap.pi fun c => lowCC W Λ bm ΛM σ₀ hσ u ∘ₗ LinearMap.proj c
  period := periodC W ΛM hX σ₀ hσ hM

structure ThArgC (W : Wts X Pr.Word R) (Λ : LevCh X Pr R) (u : Pr.Word) where

  beOn : X.Tau → ℝ
  beOn_nonneg : ∀ τ, 0 ≤ beOn τ

  thN : ∀ i, (X.K →+* ℂ) → StClC W Λ u i → StClC W Λ u (i + 1) → ℝ
  thN_nonneg : ∀ i s L L', 0 ≤ thN i s L L'

  thFree : ∀ i, (X.K →+* ℂ) → StClC W Λ u i → StClC W Λ u (i + 1) → ℝ
  thFree_nonneg : ∀ i s L L', 0 ≤ thFree i s L L'

theorem recPerC_evz (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).evz F c =
      (topEv W (Λ.lev R.m bm) σ₀ hσ u).trPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c)) (F (tilClC W Λ bm hSG ΛM u c)) := rfl

def recXpC (hX : X.Ok) (hPr : Pr.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (hpi : ∀ w : SG', Pr.piT u ∉ w.1.asIdeal)
    (hL : LevExtC Λ bm hSG ΛM) (Th : ThArgC W Λ u) : XpArg σ₀ (recChainC hX σ₀ G u A) (recPerC bm hSG hX σ₀ hσ u G A hM) where
  clsP := (ptGSD W ΛM).Cl
  clsPFin := (ptOk W ΛM hX).fintypeCl
  stabilizer₂ := fun c => MulAction.stabilizer (ptGSD W ΛM).G ((ptGSD W ΛM).outSec.rep c)
  stabPGrp := fun _ => inferInstance
  stabPFin := fun _ => (ptOk W ΛM hX).fin_stab _
  til := tilClC W Λ bm hSG ΛM u
  stabMap := stabMapRC hSG hPr u hpi hL
  stabMap_inj := stabMapRC_injective hSG hPr u hpi hL
  evz_til := fun φ ψ h => by
    funext c
    exact (recPerC_evz hSG hX σ₀ hσ u G A hM φ c).trans
      ((congrArg ((topEv W (Λ.lev R.m bm) σ₀ hσ u).trPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c))) (h c)).trans
        (recPerC_evz hSG hX σ₀ hσ u G A hM ψ c).symm)
  ptC := (ptEv W ΛM σ₀ hσ).Fi
  ipP := (ptEv W ΛM σ₀ hσ).ipCl (ptOk W ΛM hX)
  ptLat := ptH W ΛM hX
  ptLat_good := ptH_good W ΛM hX
  ptEmb := (ptEv W ΛM σ₀ hσ).emb
  ptEmb_basis := ⟨(ptEv W ΛM σ₀ hσ).emb_li (ptOk W ΛM hX) _ ((ptGSD W ΛM).hB (ptOk W ΛM hX)).linearIndependent,
    (ptEv W ΛM σ₀ hσ).span_basis _⟩
  ptEmb_norm := fun x => (ptEv W ΛM σ₀ hσ).norm_ipCl (ptOk W ΛM hX) (ptRat W ΛM hX) hσ x
  beOn := Th.beOn
  beOn_nonneg := Th.beOn_nonneg
  thN := Th.thN
  thN_nonneg := Th.thN_nonneg
  thFree := Th.thFree
  thFree_nonneg := Th.thFree_nonneg

theorem recPerC_lower_emb (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (F : StClC W Λ u R.m → FrS X σ₀ (R.N R.m) → ℂ)
    (φ : (topGSD W (Λ.lev R.m bm) u).EqFun) (hF : resTop W Λ bm σ₀ u F = (topEv W (Λ.lev R.m bm) σ₀ hσ u).emb φ) (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).lowerMap ((recPerC bm hSG hX σ₀ hσ u G A hM).evz F) c =
      (ptEv W ΛM σ₀ hσ).ev (brC W u ((φ : (topGSD W (Λ.lev R.m bm) u).D → (topGSD W (Λ.lev R.m bm) u).V)
        (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))) := by
  show lowCL W (Λ.lev R.m bm) ΛM σ₀ hσ u ((topEv W (Λ.lev R.m bm) σ₀ hσ u).atPt (tilR hSG u ((ptGSD W ΛM).outSec.rep c))
    (resTop W Λ bm σ₀ u F)) = _
  rw [hF, GSD.Ev.atPt_emb]
  exact lowCL_ev σ₀ hσ u _

theorem recPerC_lower_fam (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W Λ G u) (hM : (rowGSD W ΛM).Ok) (φ : (stepF W Λ u R.m).Forms) (c : (ptGSD W ΛM).Cl) :
    (recPerC bm hSG hX σ₀ hσ u G A hM).lowerMap ((recPerC bm hSG hX σ₀ hσ u G A hM).evz
        (fun c' : StClC W Λ u R.m => evV X.emb 1 (W.lamTrue u R.m) σ₀ ((φ c'.1).1 (repC c')))) c =
      (ptEv W ΛM σ₀ hσ).ev (brC W u ((φ bm).1 (tilR hSG u ((ptGSD W ΛM).outSec.rep c)))) :=
  recPerC_lower_emb hSG hX σ₀ hσ u G A hM _ (φ bm) rfl c

end XpC

section One

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ₀ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

theorem LevExtC_one : LevExtC (LevCh.one Λ₀) () hSG ΛM ↔ LevExt Λ₀ hSG ΛM := Iff.rfl

theorem tilClC_one (u : Pr.Word) (c : (ptGSD W ΛM).Cl) :
    tilClC W (LevCh.one Λ₀) () hSG ΛM u c = ⟨(), tilCl W Λ₀ hSG ΛM u c⟩ := rfl

theorem lowCC_one (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word) :
    lowCC W (LevCh.one Λ₀) () ΛM σ₀ hσ u = lowC W Λ₀ ΛM σ₀ hσ u := rfl

theorem recPerC_evz_one (hX : X.Ok) (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (u : Pr.Word)
    (G : ChainGlob W σ₀) (A : ChainArgC W (LevCh.one Λ₀) G u) (A₀ : ChainArg W Λ₀ G u) (hM : (rowGSD W ΛM).Ok)
    (F : StClC W (LevCh.one Λ₀) u R.m → FrS X σ₀ (R.N R.m) → ℂ) :
    (recPerC () hSG hX σ₀ hσ u G A hM).evz F = (recPer hSG hX σ₀ hσ u G A₀ hM).evz fun c₀ : StCl W Λ₀ u R.m => F ⟨(), c₀⟩ := rfl

end One

end Formalism.L2.Col
