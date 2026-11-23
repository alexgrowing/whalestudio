import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteOrderChartsMiddleSteps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsStepPointOfChartBasePoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ChartLevelCharacterRepsOnAdelicUnitaryPointsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsAdelicUnitaryLiftOfChartBasePointStatement
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemberRepresentativeMovedAtTwistEqTupleFrames
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.UG
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.AdForm
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdForm.Rebase

section Core
open Formalism.L2.Col Formalism.L2.DIV GlobalTheory.Mem.Col2.ZeroMove

theorem exists_move {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E]
    (hc : CMData F E) {n : ℕ} {ST SG Q SQ : Finset (HeightOneSpectrum (𝓞 E))}
    (W : Finset (HeightOneSpectrum (𝓞 F))) (p0 p1 : DecoF E n ST SG Q)
    (hdeco : p1.deco = p0.deco) (hQ1 : ∀ P ∈ Q, P.under (𝓞 F) ∈ W)
    (hoff : ∀ P, P ∈ ST ∨ P ∈ SG → P.under (𝓞 F) ∉ W) (k g1 : GL (Fin n) (AfE F E))
    (hpt : IsPtOf hc k (extTo SQ p0)) (hg1 : IsPtOf hc g1 (extTo SQ p1)) :
    ∃ κ : GL (Fin n) (AfE F E), (∀ v ∉ W, bc (prV (E := E) v) κ = 1) ∧ IsPtOf hc (k * κ) (extTo SQ p1) := by
  have hN : (extTo SQ p1).deco.1.N = (extTo SQ p0).deco.1.N := by
    show p1.deco.1.N = p0.deco.1.N
    rw [hdeco]
  have hxU : k⁻¹ * g1 ∈ UPts hc.sig 1 (FiniteAdeleRing (𝓞 F) F) := mul_mem (inv_mem hpt.uni) hg1.uni
  have hxC : Formalism.L2.Herm.Carries (k⁻¹ * g1) (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) := by
    intro z
    have e1 := hpt.lat (((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    have e2 := hg1.lat (((k : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) _) *ᵥ z)
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec] at e1
    rw [hN] at e2
    rw [_root_.mul_inv_rev, inv_inv, Units.val_mul, ← Matrix.mulVec_mulVec, ← e2, e1]
  obtain ⟨κ, hκU, hκin, hκout⟩ := exists_splice hc.sig 1 W (k⁻¹ * g1) hxU
  have hκC : Formalism.L2.Herm.Carries κ (Formalism.L2.Col.stdLat E n) (Formalism.L2.Col.stdLat E n) :=
    carries_of_local _ κ hxC fun v => if hv : v ∈ W then Or.inl (hκin v hv) else Or.inr (hκout v hv)
  have hof : ∀ P : HeightOneSpectrum (𝓞 E), (P ∈ ST ∨ P ∈ SG) → bc (prV (E := E) (P.under (𝓞 F))) κ = 1 :=
    fun P hP => hκout _ (hoff P hP)
  have hd' : (extTo SQ p1).deco = (extTo SQ p0).deco := hdeco
  refine ⟨κ, hκout, mul_mem hpt.uni hκU, ?_, fun P x hx i hi => ?_, fun w x hx i => ?_, fun P i j => ?_⟩
  · rw [hN]
    exact GlobalTheory.Mem.Col2.TC.ChTw.Match.LocForm.carries_mul hpt.lat hκC
  · rw [adAt_pullV_mul P.1 k (hof P.1 (Or.inl P.2)), hd']
    exact hpt.f P x (by rw [← hN]; exact hx) i hi
  · rw [adAt_pullV_mul w.1 k (hof w.1 (Or.inr w.2)), hd']
    exact hpt.be w x (by rw [← hN]; exact hx) i
  · by_cases hv : P.1.under (𝓞 F) ∈ W
    · rw [adAt_mul_congr P.1 k (hκin _ hv) i j, mul_inv_cancel_left]
      exact hg1.fr P i j
    · have hQa : P.1 ∉ Q := fun h => hv (hQ1 _ h)
      rw [adAt_mul_of_one P.1 k (hκout _ hv) i j, hpt.fr P i j, extTo_fr, extTo_fr,
        ptFr_eq p0 p1 hdeco.symm hQa hQa]

end Core

def reindex {D : D7} {T : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))} {i : ℕ} {hi : i ≤ D.R.m} {cl cl' : Type}
    {stab : cl → Type} [∀ c, Group (stab c)] {lat : cl → Submodule (𝓞 D.host.E) (Fin (D.R.N i) → D.host.E)}
    (K : LevelChart D T bad i hi stab lat) (e : cl' → cl) (he : Function.Bijective e) :
    LevelChart D T bad i hi (fun c => stab (e c)) (fun c => lat (e c)) where
  lev := K.lev
  y c := K.y (e c)
  y_bij := K.y_bij.comp he
  y_lat c := K.y_lat (e c)
  stabI c := K.stabI (e c)
  stabI_inj c := K.stabI_inj (e c)
  stabI_range c := K.stabI_range (e c)

theorem reads_rename {B : Base} {X : PreX B.toPre} {I : TC B X} {u : B.Word} {a : I.ι} {i : ℕ} {C C₀ : Type}
    {chOf₀ : (I.stp u a i).Cl → C₀} {Lb : C₀ → Submodule (𝓞 B.host.E) (Fin (B.R.N i) → B.host.E)}
    {U : C₀ → Subgroup (TC.GA B (B.R.N i))} {chi : ∀ β, U β →* ℂˣ} {y : (I.stp u a i).Cl → TC.GA B (B.R.N i)}
    {st : ∀ c, (I.stp u a i).Stab c → GL (Fin (B.R.N i)) B.host.E} {k : C₀ → TC.GA B (B.R.N i)}
    (h : I.Reads u a i chOf₀ Lb U chi y st k) (chOf : (I.stp u a i).Cl → C) (φ : C → C₀) (hφ : ∀ c, chOf₀ c = φ (chOf c))
    (hinj : Function.Injective φ) (hon : Function.Surjective chOf) :
    I.Reads u a i chOf (fun β => Lb (φ β)) (fun β => U (φ β)) (fun β => chi (φ β)) y st (fun β => k (φ β)) where
  key c c' := by rw [← h.key, hφ, hφ, hinj.eq_iff]
  onto := hon
  lb β := h.lb (φ β)
  k_std β := h.k_std (φ β)
  k_off β := h.k_off (φ β)
  k_T β := h.k_T (φ β)
  pt c := by
    have := h.pt c
    rwa [hφ] at this
  lev c x q := by
    have := h.lev c x q
    rwa [hφ] at this
  chr c := by
    have key : ∀ γ, chOf₀ c = γ → ∀ (x : U γ) (κ : (I.stp u a i).G c.1), (I.stp u a i).gam c.1 κ = 1 →
        TC.PtOf (y c * x.1 * k γ) ((I.stp u a i).act c.1 κ ((I.stp u a i).rep c)).1.1 →
        ((chi γ x : ℂˣ) : ℂ) = B.embLL (((I.stp u a i).chr c.1 κ : B.LLˣ) : B.LL) := by
      rintro _ rfl
      exact h.chr c
    exact key _ (hφ c)
  stab := h.stab

variable {B : Base} {X : PreX B.toPre}

set_option maxHeartbeats 2000000 in

theorem exists_charts (I : TC B X) (hI : I.Ok) (hP : TC.Pins B X) (l : I.Laws) (Z : TC.Later B (I.cols l)) (u : B.Word) (a : I.ι)
    (i : ℕ) (hi : i ≤ B.R.m) (h1 : 1 ≤ i) (h2 : i < B.R.m) {C : Type} (chOf : (I.stp u a i).Cl → C)
    (key : ∀ c c', chOf c = chOf c' ↔ c.1 = c'.1 ∧ cosetIn ((I.stp u a i).rep c) = cosetIn ((I.stp u a i).rep c'))
    (onto : Function.Surjective chOf) (k : C → TC.GA B (B.R.N i)) (hk : GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i k) :
    ∃ (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
      (K : ∀ β : C, LevelChart (I.rec7 l Z) (B.T u) bad i hi (fun c : {c // chOf c = β} => (I.chain l u a).stab i c.1)
        (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1))),
      I.Reads u a i chOf (fun β => (K β).lev.Lb) (fun β => (K β).lev.U) (fun β => (K β).lev.chi)
        (fun c => ((K (chOf c)).y ⟨c, rfl⟩).1) (fun c s => ((K (chOf c)).stabI ⟨c, rfl⟩ s).1) k ∧
      (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K β).lev.chi κ ^ n = 1) ∧
      ∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v := by
  let Q : Finset (HeightOneSpectrum (𝓞 (I.rec7 l Z).host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  have key₀ : ∀ c c', GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c' ↔ chOf c = chOf c' :=
    fun c c' => by
      rw [key]
      exact Subtype.ext_iff.trans Prod.ext_iff
  let φ : C → GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i := fun β => GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i (Function.surjInv onto β)
  let ψ : GlobalTheory.Mem.Col2.TC.ChTw.Chart I u a i → C := fun γ => chOf γ.2.choose
  have hφ : ∀ c, GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = φ (chOf c) := fun c =>
    (key₀ _ _).2 (Function.surjInv_eq onto _).symm
  have hψ : ∀ β, ψ (φ β) = β := fun β => by
    refine Eq.trans ((key₀ _ _).1 ?_) (Function.surjInv_eq onto β)
    exact Subtype.ext (φ β).2.choose_spec
  have hinj : Function.Injective φ := Function.LeftInverse.injective hψ
  obtain ⟨K, hK, hfin⟩ := GlobalTheory.Mem.Col2.ChExM.exists_charts I hI hP l Z u a Q i hi h1 h2 hQ (fun γ => k (ψ γ))
    ⟨fun γ => hk.std _, fun γ => hk.off _, fun γ => hk.T _⟩
  let e : ∀ β : C, {c // chOf c = β} → {c // GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = φ β} :=
    fun β c => ⟨c.1, (hφ c.1).trans (congrArg φ c.2)⟩
  have he : ∀ β, Function.Bijective (e β) := fun β =>
    ⟨fun c c' h => by
      have h' := congrArg Subtype.val h
      exact Subtype.ext h', fun c => ⟨⟨c.1, hinj ((hφ c.1).symm.trans c.2)⟩, rfl⟩⟩
  refine ⟨badQ (I.rec7 l Z) Q, fun β => reindex (K (φ β)) (e β) (he β), ?_, fun β => hfin (φ β), fun v hv => hv.imp id (hQ v).1⟩
  have h := reads_rename hK chOf φ hφ hinj onto
  have hy : ∀ c γ (hc : GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = γ),
      ((K γ).y ⟨c, hc⟩).1 = ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).y ⟨c, rfl⟩).1 := by
    rintro c _ rfl
    rfl
  have hs : ∀ c γ (hc : GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c = γ) s,
      ((K γ).stabI ⟨c, hc⟩ s).1 = ((K (GlobalTheory.Mem.Col2.TC.ChTw.chartOf I u a i c)).stabI ⟨c, rfl⟩ s).1 := by
    rintro c _ rfl s
    rfl
  have e1 : (fun β => k (ψ (φ β))) = k := funext fun β => congrArg k (hψ β)
  rw [e1, ← funext fun c => hy c _ (hφ c), ← funext fun c => funext fun s => hs c _ (hφ c) s] at h
  exact h

def StepOk {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (i : ℕ)
    (bad : Set (HeightOneSpectrum (𝓞 B.host.F)))
    (K : ∀ (hi : i ≤ B.R.m) (β : Ch i), LevelChart (I.rec7 l Z) (B.T u) bad i hi
      (fun c : {c // A.chOf i c = β} => (I.chain l u a).stab i c.1) (fun c => latCrd (I.rec7 l Z) i hi (I.latAt u a i c.1)))
    (k : Ch i → TC.GA B (B.R.N i)) (kA : Ch i → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) (xr : Ch i → (AE (I.rec7 l Z))ˣ)
    (p0 : Ch i → PtAt B.R I.sel (I.tup a) (I.cst a) u i) (U : Ch i → Subgroup (GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)))
    (chi : ∀ β, U β →* ℂˣ) (h : ∀ β : Ch i, {c // A.chOf i c = β} → GA (I.rec7 l Z) ((I.rec7 l Z).sp.X i)) : Prop :=
  ∀ hi : i ≤ B.R.m, I.Reads u a i (A.chOf i) (fun β => (K hi β).lev.Lb) (fun β => (K hi β).lev.U) (fun β => (K hi β).lev.chi)
      (fun c => ((K hi (A.chOf i c)).y ⟨c, rfl⟩).1) (fun c s => ((K hi (A.chOf i c)).stabI ⟨c, rfl⟩ s).1) k ∧
    (∀ β, kA β ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (kA β) = (k β).1 ∧ IsDetRoot _ (kA β) (xr β)) ∧
    (∀ β, TC.PtOf (k β) (extTo I.SQ (p0 β).1.1) ∧ (p0 β).1.1.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) ∧
    (∀ c, cosetIn ((I.stp u a i).rep c) = cosetIn (p0 (A.chOf i c))) ∧
    (∀ β g, g ∈ U β ↔ g ∈ GfC _ ∧ ∃ κ : (K hi β).lev.U, κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g) ∧
    (∀ β (g : U β) (κ : (K hi β).lev.U), κ.1.1 = finM _ (rankN (I.rec7 l Z) i hi) g.1 → chi β g = (K hi β).lev.chi κ) ∧
    (∀ β c, h β c ∈ GfC _ ∧ finM _ (rankN (I.rec7 l Z) i hi) (h β c) = ((K hi β).y c).1.1) ∧
    (∀ β, ∃ n : ℕ, 0 < n ∧ ∀ κ, (K hi β).lev.chi κ ^ n = 1) ∧ ∀ v ∈ bad, v ∈ Formalism.L2.Forms.badG (I.rec7 l Z) ∨ I.UnderQ a v

attribute [local instance] GlobalTheory.Mem.Col2.starE

set_option maxHeartbeats 2000000 in

theorem exists_step {I : TC B X} (hI : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is) (i : ℕ) (hm : i + 1 = B.R.m)
    (q : Ch i → Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : Ch i → TC.GA B (B.R.N i))
    (hoff : ∀ β v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (κ β) = 1)
    (hpt : ∀ β, TC.PtOf (A.kb i β * κ β) (extTo I.SQ (q β)))
    (hN : ∀ β, (q β).deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) :
    ∃ bad K kA xr p0 U chi h, StepOk A i bad K (fun β => A.kb i β * κ β) kA xr p0 U chi h ∧ ∀ β, (p0 β).1.1 = q β := by
  have hi : i ≤ B.R.m := by omega
  have h2m := B.R.two_le_m
  have hR₀ := hA.reads i hi
  have hd : Disjoint (B.primes X).vGs (I.Q a) := (LevTwist.levOk_twists B X I hI).2.1.mono_right (I.Q_subset_SQ a)
  have hk : GlobalTheory.Mem.Col2.TC.ChTw.AdmK I u a i (fun β => A.kb i β * κ β) := by
    refine ⟨fun β => ?_, fun β v h1 h2 h3 => ?_, fun β P r j hr => ?_⟩
    · obtain ⟨p, hp, hpN⟩ := hR₀.k_std β
      refine ⟨p, ⟨(hpt β).uni, ?_, fun P => absurd P.2 (Finset.notMem_empty _), fun P => absurd P.2 (Finset.notMem_empty _),
        fun P => absurd P.2 (Finset.notMem_empty _)⟩, hpN⟩
      have e := (hpt β).lat
      rw [extTo_deco, hN] at e
      rw [hpN]
      exact e
    · rw [map_mul, hR₀.k_off β v h1 h2 h3, hoff β v h2, mul_one]
    · have e : bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb i β * κ β)⁻¹ =
          bc (prV (E := B.host.E) (P.1.under (𝓞 B.host.F))) (A.kb i β)⁻¹ := by
        rw [map_inv, map_mul, hoff β _ (GlobalTheory.Mem.Col2.ZeroMove.not_underQ I hI u a (Or.inl P.2)), mul_one, map_inv]
      have e2 := GlobalTheory.Mem.Col2.ZeroMove.adAt_entry_of_bc (F := B.host.F) (E := B.host.E) P.1 e r j
      exact e2 ▸ hR₀.k_T β P r j hr
  obtain ⟨bad, K, hR, hfin, hbad⟩ := exists_charts I hI hP l Z u a i hi (by omega) (by omega) (A.chOf i) hR₀.key hR₀.onto _ hk
  have hq : ∀ β, TC.PtOf (A.kb i β * κ β) (q β) := fun β => IsPtOf.of_extTo (I.Q_subset_SQ a) hd (hpt β)
  have hone : ∀ β, ∀ P ∈ I.SQ, P ∉ I.Q a → (A.kb i β * κ β).1.map (adAt B.host.F P) = 1 := by
    intro β P hP' hPQ
    have hPG : P ∉ (B.primes X).vGs := Finset.disjoint_right.1 (LevTwist.levOk_twists B X I hI).2.1 hP'
    have hfr : ptFr (q β) P = 1 := by
      unfold ptFr
      rw [dif_neg hPG, dif_neg hPQ, hN]
      unfold GlobalTheory.Mem.Col2.latFr
      exact if_pos rfl
    refine Matrix.ext fun r s => ?_
    have e := (hpt β).fr ⟨P, hP'⟩ r s
    rw [extTo_fr, hfr] at e
    refine e.trans ?_
    show algebraMap _ _ ((Pi.single s 1 : Fin (B.R.N i) → B.host.E) r) = _
    rw [Matrix.one_apply, Pi.single_apply]
    split_ifs <;> simp
  choose kA hkA using fun β => GlobalTheory.T.exists_adelicUnitaryLift_of_chartBasePoint I hI hP l Z i hi _ (hR.k_std β)
  choose xr hxr using fun β => GlobalTheory.RecDict.exists_isDetRoot (I.rec7 l Z) _ (kA β)
  choose b0 p0 hp1 hp2 hp3 using fun β => GlobalTheory.KxPoint.pointOf_base I hI hP u a i hi _ _ _ _ _ _ _ hR β ⟨q β, hq β⟩ (hone β)
  choose U chi h hU hchi hh using fun β => GlobalTheory.T.chartLevelCharacterReps_on_adelicUnitaryPoints I l Z i hi (K β)
  refine ⟨bad, fun _ => K, kA, xr, p0, U, chi, h, fun _ => ⟨hR, fun β => ⟨(hkA β).1, (hkA β).2, hxr β⟩, fun β => ⟨hp1 β, hp2 β⟩,
    fun c => (hp3 _ c rfl).2, hU, hchi, hh, hfin, hbad⟩, fun β => ?_⟩
  exact GlobalTheory.Mem.Col2.PtUniq.isPtOf_unique _ _ _ _ (IsPtOf.of_extTo (I.Q_subset_SQ a) hd (hp1 β)) (hq β)

set_option maxHeartbeats 2000000 in

theorem exists_moved {I : TC B X} (hI : I.Ok) (hP : TC.Pins B X) {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι}
    {Ch : ℕ → Type} (A : TwDat I l Z u a Ch) (hA : A.Is)
    (q : ∀ i, Ch i → Formalism.L2.Col.ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : ∀ i, Ch i → TC.GA B (B.R.N i))
    (hoff : ∀ i, i + 1 = B.R.m → ∀ β v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) (κ i β) = 1)
    (hpt : ∀ i, i + 1 = B.R.m → ∀ β, TC.PtOf (A.kb i β * κ i β) (extTo I.SQ (q i β)))
    (hN : ∀ i, i + 1 = B.R.m → ∀ β, (q i β).deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i)) :
    ∃ A' : TwDat I l Z u a Ch, A'.Is ∧ A'.chr = A.chr ∧ A'.b0 = A.b0 ∧ (∀ i, i + 1 ≠ B.R.m → A'.kb i = A.kb i ∧ A'.p0 i = A.p0 i) ∧
      ∀ i, i + 1 = B.R.m → ∀ β, A'.kb i β = A.kb i β * κ i β ∧ (A'.p0 i β).1.1 = q i β ∧
        cosetIn (A'.p0 i β) = cosetIn (A.p0 i β) := by
  have H : ∀ i, ∃ bad K k kA xr p0 U chi h, StepOk A i bad K k kA xr p0 U chi h ∧ (i + 1 ≠ B.R.m → k = A.kb i ∧ p0 = A.p0 i) ∧
      (i + 1 = B.R.m → ∀ β, k β = A.kb i β * κ i β ∧ (p0 β).1.1 = q i β) := by
    intro i
    by_cases hm : i + 1 = B.R.m
    · obtain ⟨bad, K, kA, xr, p0, U, chi, h, h1, h2⟩ := exists_step hI hP A hA i hm (q i) (κ i) (hoff i hm) (hpt i hm) (hN i hm)
      exact ⟨bad, K, _, kA, xr, p0, U, chi, h, h1, fun h' => absurd hm h', fun _ β => ⟨rfl, h2 β⟩⟩
    · exact ⟨A.bad i, A.K i, A.kb i, A.kA i, A.xr i, A.p0 i, A.U i, A.chi i, A.h i,
        fun hi => ⟨hA.reads i hi, hA.kA i hi, hA.base i hi, fun c => (hA.rep i hi c).2, hA.U i hi, hA.chi i hi, hA.h i hi,
          hA.fin i hi, hA.bad_le i hi⟩, fun _ => ⟨rfl, rfl⟩, fun h' => absurd h' hm⟩
  choose bad K k kA xr p0 U chi h hS hne heq using H
  refine ⟨⟨bad, A.chOf, K, k, kA, xr, A.b0, p0, U, chi, h, A.chr, A.e⟩,
    ⟨fun i hi => (hS i hi).1, fun β => ?_, fun i hi => (hS i hi).2.1, fun i hi => (hS i hi).2.2.1,
      fun i hi c => ⟨(hA.rep i hi c).1, (hS i hi).2.2.2.1 c⟩, fun i hi => (hS i hi).2.2.2.2.1, fun i hi => (hS i hi).2.2.2.2.2.1,
      fun i hi => (hS i hi).2.2.2.2.2.2.1, hA.chr, hA.idem, fun i hi => (hS i hi).2.2.2.2.2.2.2.1,
      fun i hi => (hS i hi).2.2.2.2.2.2.2.2⟩, rfl, rfl, hne, fun i hm β => ⟨(heq i hm β).1, (heq i hm β).2, ?_⟩⟩
  · show I.TopPt l Z u a (k B.R.m β)
    rw [(hne B.R.m (by omega)).1]
    exact hA.top β
  · have hi : i ≤ B.R.m := by omega
    obtain ⟨c, rfl⟩ := (hA.reads i hi).onto β
    exact ((hS i hi).2.2.2.1 c).symm.trans (hA.rep i hi c).2

open Formalism.L2.Col in

theorem exists_frames {I : TC B X} (hI : I.Ok) {u : B.Word} {a : I.ι} {i : ℕ}
    (p : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (k : TC.GA B (B.R.N i)) (hk : TC.PtOf k (extTo I.SQ p))
    (hN : p.deco.1.N = Formalism.L2.Col.stdLat B.fields.E (B.R.N i))
    (r : I.Q a → (Sp B.fields.E (B.R.N i) ≃ₗ[B.fields.E] Sp B.fields.E (B.R.N i)))
    (hr : ∀ P, r P ∈ GLint B.fields.E (B.R.N i) P.1) :
    ∃ (q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i) (κ : TC.GA B (B.R.N i)), q.deco = p.deco ∧ (∀ P, q.fr P = r P) ∧
      (∀ v, ¬ I.UnderQ a v → bc (prV (E := B.host.E) v) κ = 1) ∧ TC.PtOf (k * κ) (extTo I.SQ q) := by
  let q : ChPt (Pr := B.primes X) (R := B.R) I.sel (I.tup a) u i := ⟨(p.deco, r), fun P x => by
    show r P x ∈ Formalism.HermitianLatticesTheory.localization₂ P.1.asIdeal p.deco.1.N ↔ _
    rw [hN]
    exact hr P x⟩
  let Q : Finset (HeightOneSpectrum (𝓞 B.host.F)) := (I.Q a).image (fun P => P.under (𝓞 B.host.F))
  have hQ : ∀ v, v ∈ Q ↔ I.UnderQ a v := fun v => Finset.mem_image
  obtain ⟨g1, hg1⟩ := PtTwist.exists_ptOf_twists I hI u _ (extTo I.SQ q)
  obtain ⟨κ, h1, h2⟩ := exists_move B.sp.cm Q p q rfl (fun P h => (hQ _).2 ⟨P, h, rfl⟩)
    (fun P hP hv => GlobalTheory.Mem.Col2.ZeroMove.not_underQ I hI u a hP ((hQ _).1 hv)) k g1 hk hg1
  exact ⟨q, κ, rfl, fun _ => rfl, fun v hv => h1 v fun h => hv ((hQ v).1 h), h2⟩

open Formalism.L2.Col in

theorem repY_cong {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
    {mu : Formalism.L2.DIV.Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ} (h : j + 1 = R.m)
    (p p' : PtAt R sel mu cst u j) (hc : cosetIn p' = cosetIn p) (P : rowSG Pr sel mu) :
    ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ •
      ((frsF sel mu p'.1.1 P).symm (repY p'.1.2) - (frsF sel mu p.1.1 P).symm (repY p.1.2)) ∈ stdAt X.E (R.N j) P.1 := by
  have h1 : (frsF sel mu p'.1.1 P).symm (repY p'.1.2) ∈ cosetIn p' P :=
    ⟨_, p'.repY_mem h, by rw [sub_self, smul_zero]; exact zero_mem _⟩
  rw [hc] at h1
  obtain ⟨y, hy, h2⟩ := h1
  obtain ⟨y₀, -, hY⟩ := p.mem_ybSet h
  have h3 := p.repY_mem h
  have hy' : y - y₀ ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    rw [hY] at hy
    exact hy
  have h3' : repY p.1.2 - y₀ ∈ locLat (rowSG Pr sel mu) p.1.1.deco.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ)) := by
    generalize repY p.1.2 = z at h3
    rw [hY] at h3
    exact h3
  have h4 := (mem_locLat _ _ _ _).1 (sub_mem hy' h3') P
  rw [sub_sub_sub_cancel_right] at h4
  have h5 : ((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then (0 : ℤ) else (cst.M : ℤ))) =
      (qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M) := by
    split_ifs <;> simp
  rw [h5] at h4
  have h6 : (frsF sel mu p.1.1 P).symm (((qOf P.1 : X.E) ^ (if P.1 ∈ Pr.vGs then 0 else cst.M))⁻¹ • (y - repY p.1.2)) ∈
      stdAt X.E (R.N j) P.1 := by
    refine (isFr_ptFr p.1.1 P.1 _).1 ?_
    rw [← frsF_eq_ptFr, LinearEquiv.apply_symm_apply]
    exact h4
  have h7 := add_mem h2 h6
  rwa [map_smul, map_sub, ← smul_add, sub_add_sub_cancel] at h7

end GlobalTheory.AdForm.Rebase

end
